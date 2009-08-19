#include "cld_intchk.hh"
#include "cl_decorator.hh"

#include <map>
#include <string>

class CldCbSeqChk: public ClDecoratorBase {
    public:
        CldCbSeqChk(ICodeListener *slave);

        virtual void file_open(
            const char              *file_name)
        {
            file_ = file_name;
            this->setState(S_FILE_LEVEL);
            ClDecoratorBase::file_open(file_name);
        }

        virtual void file_close() {
            this->setState(S_INIT);
            ClDecoratorBase::file_close();
        }

        virtual void fnc_open(
            const struct cl_location*loc,
            const char              *fnc_name,
            enum cl_scope_e         scope)
        {
            loc_ = *loc;
            this->setState(S_FNC_DECL);
            ClDecoratorBase::fnc_open(loc, fnc_name, scope);
        }

        virtual void fnc_arg_decl(
            int                     arg_id,
            const char              *arg_name)
        {
            this->chkArgDecl();
            ClDecoratorBase::fnc_arg_decl(arg_id, arg_name);
        }

        virtual void fnc_close() {
            this->setState(S_FILE_LEVEL);
            ClDecoratorBase::fnc_close();
        }

        virtual void bb_open(
            const char              *bb_name)
        {
            this->setState(S_BLOCK_LEVEL);
            ClDecoratorBase::bb_open(bb_name);
        }

        virtual void insn(
            const struct cl_insn    *cli)
        {
            loc_ = cli->loc;

            switch (cli->type) {
                case CL_INSN_JMP:
                    this->chkInsnJmp();
                    break;

                case CL_INSN_COND:
                    this->chkInsnCond();
                    break;

                case CL_INSN_RET:
                    this->chkInsnRet();
                    break;

                case CL_INSN_ABORT:
                    this->chkInsnAbort();
                    break;

                case CL_INSN_UNOP:
                    this->chkInsnUnop();
                    break;

                case CL_INSN_BINOP:
                    this->chkInsnBinop();
                    break;
            }

            ClDecoratorBase::insn(cli);
        }

        virtual void insn_call_open(
            const struct cl_location*loc,
            const struct cl_operand *dst,
            const struct cl_operand *fnc)
        {
            loc_ = *loc;
            this->setState(S_INSN_CALL);
            ClDecoratorBase::insn_call_open(loc, dst, fnc);
        }

        virtual void insn_call_arg(
            int                     arg_id,
            const struct cl_operand *arg_src)
        {
            this->chkInsnCallArg();
            ClDecoratorBase::insn_call_arg(arg_id, arg_src);
        }

        virtual void insn_call_close() {
            this->setCallClose();
            ClDecoratorBase::insn_call_close();
        }

    private:
        enum EState {
            S_INIT,
            S_FILE_LEVEL,
            S_FNC_DECL,
            S_FNC_BODY,
            S_BLOCK_LEVEL,
            S_INSN_CALL
        };

        EState                      state_;
        std::string                 file_;
        struct cl_location          loc_;


    private:
        static const char* toString(EState);
        void emitUnexpected(const char *);
        void emitUnexpected(EState);
        void setState(EState);
        void chkArgDecl();
        void chkInsnJmp();
        void chkInsnCond();
        void chkInsnRet();
        void chkInsnAbort();
        void chkInsnUnop();
        void chkInsnBinop();
        void chkInsnCallArg();
        void setCallClose();
};

class CldLabelChk: public ClDecoratorBase {
    public:
        CldLabelChk(ICodeListener *slave);

        virtual void file_open(
            const char              *file_name)
        {
            file_ = file_name;
            ClDecoratorBase::file_open(file_name);
        }

        virtual void fnc_open(
            const struct cl_location*loc,
            const char              *fnc_name,
            enum cl_scope_e         scope)
        {
            loc_ = *loc;
            this->reset();
            ClDecoratorBase::fnc_open(loc, fnc_name, scope);
        }

        virtual void fnc_close() {
            this->emitWarnings();
            ClDecoratorBase::fnc_close();
        }

        virtual void bb_open(
            const char              *bb_name)
        {
            this->defineLabel(bb_name);
            ClDecoratorBase::bb_open(bb_name);
        }

        virtual void insn(
            const struct cl_insn    *cli)
        {
            switch (cli->type) {
                case CL_INSN_JMP:
                    this->reqLabel(cli->data.insn_jmp.label);
                    break;

                case CL_INSN_COND:
                    this->reqLabel(cli->data.insn_cond.then_label);
                    this->reqLabel(cli->data.insn_cond.else_label);
                    break;

                default:
                    break;
            }

            ClDecoratorBase::insn(cli);
        }

    private:
        struct LabelState {
            bool                    defined;
            bool                    reachable;
            struct cl_location      loc;

            LabelState(): defined(false), reachable(false)
            {
                cl_set_location(&loc, -1);
            }
        };

        typedef std::map<std::string, LabelState> TMap;

        TMap                map_;
        std::string         file_;
        struct cl_location  loc_;

    private:
        void reset();
        void defineLabel(const char *);
        void reqLabel(const char *);
        void emitWarnings();
};

// TODO: go through CFG and report all unused/initialized?
class CldRegUsageChk: public ClDecoratorBase {
    public:
        CldRegUsageChk(ICodeListener *slave);

        virtual void file_open(
            const char              *file_name)
        {
            file_ = file_name;
            ClDecoratorBase::file_open(file_name);
        }

        virtual void fnc_open(
            const struct cl_location*loc,
            const char              *fnc_name,
            enum cl_scope_e         scope)
        {
            loc_ = *loc;
            this->reset();
            ClDecoratorBase::fnc_open(loc, fnc_name, scope);
        }

        virtual void fnc_close() {
            this->emitWarnings();
            ClDecoratorBase::fnc_close();
        }

        virtual void insn(
            const struct cl_insn    *cli)
        {
            loc_ = cli->loc;

            switch (cli->type) {
                case CL_INSN_COND:
                    this->handleSrc(cli->data.insn_cond.src);
                    break;

                case CL_INSN_RET:
                    this->handleSrc(cli->data.insn_ret.src);
                    break;

                case CL_INSN_UNOP:
                    this->handleDst(cli->data.insn_unop.dst);
                    this->handleSrc(cli->data.insn_unop.src);
                    break;

                case CL_INSN_BINOP:
                    this->handleDst(cli->data.insn_binop.dst);
                    this->handleSrc(cli->data.insn_binop.src1);
                    this->handleSrc(cli->data.insn_binop.src2);
                    break;

                default:
                    break;
            }

            ClDecoratorBase::insn(cli);
        }

        virtual void insn_call_open(
            const struct cl_location*loc,
            const struct cl_operand *dst,
            const struct cl_operand *fnc)
        {
            loc_ = *loc;
            this->handleDst(dst);
            this->handleSrc(fnc);
            ClDecoratorBase::insn_call_open(loc, dst, fnc);
        }

        virtual void insn_call_arg(
            int                     arg_id,
            const struct cl_operand *arg_src)
        {
            this->handleSrc(arg_src);
            ClDecoratorBase::insn_call_arg(arg_id, arg_src);
        }

    private:
        struct Usage {
            bool                    read;
            bool                    written;
            struct cl_location      loc;

            Usage(): read(false), written(false)
            {
                cl_set_location(&loc, -1);
            }
        };

        typedef std::map<int, Usage> TMap;

        TMap                map_;
        std::string         file_;
        struct cl_location  loc_;

    private:
        void reset();
        void handleDst(const struct cl_operand *);
        void handleSrc(const struct cl_operand *);
        void emitWarnings();
};

// /////////////////////////////////////////////////////////////////////////////
// CldCbSeqChk implementation
CldCbSeqChk::CldCbSeqChk(ICodeListener *slave):
    ClDecoratorBase(slave),
    state_(S_INIT)
{
    cl_set_location(&loc_, -1);
}

const char* CldCbSeqChk::toString(EState state) {
#define CASE_TO_STRING(state) case state: return #state;
    switch (state) {
        CASE_TO_STRING(S_INIT)
        CASE_TO_STRING(S_FILE_LEVEL)
        CASE_TO_STRING(S_FNC_DECL)
        CASE_TO_STRING(S_FNC_BODY)
        CASE_TO_STRING(S_BLOCK_LEVEL)
        CASE_TO_STRING(S_INSN_CALL)
        default:
            CL_DIE("CldCbSeqChk::toString");
            return NULL;
    }
}

void CldCbSeqChk::emitUnexpected(const char *what) {
    CL_MSG_STREAM(cl_error, file_ << ":" << loc_.line << ": error: "
            << "unexpected callback in state "
            << toString(state_) << " (" << what << ")");
}

void CldCbSeqChk::emitUnexpected(EState state) {
    this->emitUnexpected(toString(state));
}

void CldCbSeqChk::setState(EState newState) {
    switch (state_) {
        case S_INIT:
            if (S_FILE_LEVEL != newState)
                this->emitUnexpected(newState);
            break;

        case S_FILE_LEVEL:
            switch (newState) {
                case S_INIT:
                case S_FNC_DECL:
                    break;
                default:
                    this->emitUnexpected(newState);
            }
            break;

        case S_FNC_DECL:
            this->emitUnexpected(newState);
            break;

        case S_FNC_BODY:
            switch (newState) {
                case S_BLOCK_LEVEL:
                case S_FILE_LEVEL:
                    break;
                default:
                    this->emitUnexpected(newState);
            }
            break;

        case S_BLOCK_LEVEL:
            switch (newState) {
                case S_INSN_CALL:
                    break;
                default:
                    this->emitUnexpected(newState);
            }
            break;

        case S_INSN_CALL:
            this->emitUnexpected(newState);
            break;
    }

    state_ = newState;
}

void CldCbSeqChk::chkArgDecl() {
    if (S_FNC_DECL != state_)
        this->emitUnexpected("fnc_arg_decl");
}

void CldCbSeqChk::chkInsnJmp() {
    switch (state_) {
        case S_FNC_DECL:
        case S_BLOCK_LEVEL:
            break;

        default:
            this->emitUnexpected("CL_INSN_JMP");
    }

    state_ = S_FNC_BODY;
}

void CldCbSeqChk::chkInsnCond() {
    if (S_BLOCK_LEVEL != state_)
        this->emitUnexpected("CL_INSN_COND");

    state_ = S_FNC_BODY;
}

void CldCbSeqChk::chkInsnRet() {
    if (S_BLOCK_LEVEL != state_)
        this->emitUnexpected("CL_INSN_RET");

    state_ = S_FNC_BODY;
}

void CldCbSeqChk::chkInsnAbort() {
    if (S_BLOCK_LEVEL != state_)
        this->emitUnexpected("CL_INSN_ABORT");

    state_ = S_FNC_BODY;
}

void CldCbSeqChk::chkInsnUnop() {
    if (S_BLOCK_LEVEL != state_)
        this->emitUnexpected("CL_INSN_UNOP");
}

void CldCbSeqChk::chkInsnBinop() {
    if (S_BLOCK_LEVEL != state_)
        this->emitUnexpected("CL_INSN_BINOP");
}

void CldCbSeqChk::chkInsnCallArg() {
    if (S_INSN_CALL != state_)
        this->emitUnexpected("insn_call_arg");
}

void CldCbSeqChk::setCallClose() {
    if (S_INSN_CALL != state_)
        this->emitUnexpected("insn_call_close");

    state_ = S_BLOCK_LEVEL;
}


// /////////////////////////////////////////////////////////////////////////////
// CldLabelChk implementation
CldLabelChk::CldLabelChk(ICodeListener *slave):
    ClDecoratorBase(slave)
{
    cl_set_location(&loc_, -1);
}

void CldLabelChk::reset() {
    map_.clear();
}

void CldLabelChk::defineLabel(const char *label) {
    LabelState &ls = map_[label];
    ls.defined = true;
    if (ls.loc.line < 0)
        ls.loc = loc_;
}

void CldLabelChk::reqLabel(const char *label) {
    LabelState &ls = map_[label];
    ls.reachable = true;
    if (ls.loc.line < 0)
        ls.loc = loc_;
}

void CldLabelChk::emitWarnings() {
    TMap::iterator i;
    for (i = map_.begin(); i != map_.end(); ++i) {
        const std::string label = i->first;
        const LabelState &ls = i->second;

        if (!ls.defined) {
            CL_MSG_STREAM(cl_error, file_ << ":" << ls.loc.line << ": error: "
                    << "jump to undefined label '" << label << "'");
        }

        if (!ls.reachable) {
            CL_MSG_STREAM(cl_warn, file_ << ":" << ls.loc.line << ": warning: "
                    << "unreachable label '" << label << "'");
        }
    }
}


// /////////////////////////////////////////////////////////////////////////////
// CldRegUsageChk implementation
CldRegUsageChk::CldRegUsageChk(ICodeListener *slave):
    ClDecoratorBase(slave)
{
    cl_set_location(&loc_, -1);
}

void CldRegUsageChk::reset() {
    map_.clear();
}

void CldRegUsageChk::handleDst(const struct cl_operand *op) {
    if (CL_OPERAND_REG != op->type)
        return;

    Usage &u = map_[op->data.reg.id];
    u.written = true;
    if (u.loc.line < 0)
        u.loc = loc_;
}

void CldRegUsageChk::handleSrc(const struct cl_operand *op) {
    if (CL_OPERAND_REG != op->type)
        return;

    Usage &u = map_[op->data.reg.id];
    u.read = true;
    if (u.loc.line < 0)
        u.loc = loc_;
}

void CldRegUsageChk::emitWarnings() {
    TMap::iterator i;
    for (i = map_.begin(); i != map_.end(); ++i) {
        int reg = i->first;
        const Usage &u = i->second;

        if (!u.read) {
            CL_MSG_STREAM(cl_warn, file_ << ":" << u.loc.line << ": warning: "
                    << "unused register %r" << reg);
        }

        if (!u.written) {
            CL_MSG_STREAM(cl_error, file_ << ":" << u.loc.line << ": error: "
                    << "uninitialized register %r" << reg);
        }
    }
}


// /////////////////////////////////////////////////////////////////////////////
// public interface, see cld_unilabel.hh for more details
ICodeListener* createCldIntegrityChk(ICodeListener *slave) {
    return
        new CldRegUsageChk(
        new CldLabelChk(
        new CldCbSeqChk(slave)
        ));
}