#include "cl_typedot.hh"
#include "cl_private.hh"

#include <fstream>
#include <set>
#include <stack>
#include <vector>

class ClTypeDotGenerator: public AbstractCodeListener {
    public:
        ClTypeDotGenerator(const char *glDotFile);
        virtual ~ClTypeDotGenerator();

        virtual void file_open(const char *file_name) {
            loc_.currentFile = file_name;
        }

        virtual void file_close() {
            loc_.currentFile.clear();
        }

        virtual void fnc_open(
            const struct cl_location*loc,
            const char              *fnc_name,
            enum cl_scope_e         scope)
        {
            fnc_ = fnc_name;
        }

        virtual void fnc_arg_decl(
            int                     arg_id,
            const struct cl_operand *arg_src)
        {
            this->handleOperand(arg_src);
        }

        virtual void fnc_close() {
            fnc_.clear();
        }

        virtual void bb_open(const char *bb_name) { }

        virtual void insn(const struct cl_insn *cli) {
            switch (cli->code) {
                case CL_INSN_NOP:
                case CL_INSN_JMP:
                case CL_INSN_ABORT:
                    // no operand
                    break;

                case CL_INSN_COND:
                    this->handleOperand(cli->data.insn_cond.src);
                    break;

                case CL_INSN_RET:
                    this->handleOperand(cli->data.insn_ret.src);
                    break;

                case CL_INSN_UNOP:
                    this->handleOperand(cli->data.insn_unop.dst);
                    this->handleOperand(cli->data.insn_unop.src);
                    break;

                case CL_INSN_BINOP:
                    this->handleOperand(cli->data.insn_binop.dst);
                    this->handleOperand(cli->data.insn_binop.src1);
                    this->handleOperand(cli->data.insn_binop.src2);
                    break;
            }
        }

        virtual void insn_call_open(
            const struct cl_location*loc,
            const struct cl_operand *dst,
            const struct cl_operand *fnc)
        {
            this->handleOperand(dst);
            this->handleOperand(fnc);
        }

        virtual void insn_call_arg(
            int                     arg_id,
            const struct cl_operand *arg_src)
        {
            this->handleOperand(arg_src);
        }

        virtual void insn_call_close() { }

        virtual void insn_switch_open(
            const struct cl_location*loc,
            const struct cl_operand *src)
        {
            this->handleOperand(src);
        }

        virtual void insn_switch_case(
            const struct cl_location*loc,
            const struct cl_operand *val_lo,
            const struct cl_operand *val_hi,
            const char              *label)
        {
            this->handleOperand(val_lo);
            this->handleOperand(val_hi);
        }

        virtual void insn_switch_close() { }

    private:
        typedef std::stack<cl_type_uid_t>               TStack;

        std::ofstream           glOut_;
        Location                loc_;
        std::string             fnc_;

        std::set<cl_type_uid_t> typeSet_;

    private:
        struct Edge {
            cl_type_uid_t   src;
            cl_type_uid_t   dst;
            enum cl_type_e  code;
            std::string     label;

            Edge(cl_type_uid_t src_, cl_type_uid_t dst_, enum cl_type_e code_,
                    const std::string &label_):
                src(src_),
                dst(dst_),
                code(code_),
                label(label_)
            {
            }
        };
        typedef std::vector<Edge>                       TEdgeList;

        TEdgeList               pendingEdges_;
        static const char       *CltColors[];

    private:
        void printType(const struct cl_type *clt);
        void gobbleEdge(cl_type_uid_t src, cl_type_uid_t dst,
                        enum cl_type_e code, const char *label);
        void emitPendingEdges();
        void digOneType(const struct cl_type *, TStack &);
        void handleType(cl_type_uid_t uid);
        void handleOperand(const struct cl_operand *operand);
};

using std::ios;
using std::string;

enum {
    CNT_CL_TYPES = /* FIXME */ CL_TYPE_STRING + 1
};
const char *ClTypeDotGenerator::CltColors[CNT_CL_TYPES] = {
    "green",                        // CL_TYPE_VOID
    "red",                          // CL_TYPE_PTR
    "blue",                         // CL_TYPE_STRUCT
    "cyan",                         // CL_TYPE_UNION
    "yellow",                       // CL_TYPE_ARRAY
    "black",                        // CL_TYPE_FNC
    "green",                        // CL_TYPE_INT
    "green",                        // CL_TYPE_CHAR
    "green",                        // CL_TYPE_BOOL
    "green",                        // CL_TYPE_ENUM
    "purple",                       // CL_TYPE_STRING
};

// /////////////////////////////////////////////////////////////////////////////
// ClTypeDotGenerator implementation
ClTypeDotGenerator::ClTypeDotGenerator(const char *glDotFile)
{
    glOut_.open(glDotFile, ios::out);
    if (glOut_) {
        CL_DEBUG("ClTypeDotGenerator: created dot file '" << glDotFile << "'");
    } else {
        CL_MSG_STREAM_INTERNAL(cl_error, "error: "
                               "unable to create file '" << glDotFile << "'");
    }
    glOut_ << "digraph types" << " {" << std::endl
        << "\tlabel=<<FONT POINT-SIZE=\"18\">"
        << "\"data type graph\"" << "</FONT>>;" << std::endl
        << "\tlabelloc=t;" << std::endl;
}

ClTypeDotGenerator::~ClTypeDotGenerator() {
    glOut_ << "}" << std::endl;
    if (!glOut_) {
        CL_MSG_STREAM_INTERNAL(cl_warn, "warning: "
                "error detected while closing a file");
    }
    glOut_.close();
}

namespace {
    // FIXME: copy pasted from cl_pp.cc
    const char* typeName(const struct cl_type *clt) {
        if (!clt)
            TRAP;

        const char *name = clt->name;
        return (name)
            ? name
            : "<anon_type>";
    }
}

// FIXME: copy pasted from ClPrettyPrint::printVarType
void ClTypeDotGenerator::printType(const struct cl_type *clt) {
    string str;
    for (; clt; clt = this->getType(clt->items[0].type)) {
        enum cl_type_e code = clt->code;
        switch (code) {
            case CL_TYPE_PTR:
                str = string("*") + str;
                break;

            case CL_TYPE_ARRAY:
                str = string("[]") + str;
                break;

            default:
                goto deref_done;
        }
    }
deref_done:

    enum cl_type_e code = clt->code;
    switch (code) {
        case CL_TYPE_VOID:
            glOut_ << "void";
            break;

        case CL_TYPE_STRUCT:
            glOut_ << "struct" << " " << typeName(clt);
            break;

        case CL_TYPE_UNION:
            glOut_ << "union" << " " << typeName(clt);
            break;

        case CL_TYPE_FNC:
            glOut_ << "fnc";
            break;

        case CL_TYPE_INT:
            glOut_ << "int";
            break;

        case CL_TYPE_CHAR:
            glOut_ << "char";
            break;

        case CL_TYPE_BOOL:
            glOut_ << "bool";
            break;

        case CL_TYPE_ENUM:
            glOut_ << "enum" << " " << typeName(clt);
            break;

        default:
            TRAP;
    }

    if (!str.empty())
        str = string(" ") + str;
    glOut_ << str;
}

void ClTypeDotGenerator::gobbleEdge(cl_type_uid_t src, cl_type_uid_t dst,
                                    enum cl_type_e code, const char *label)
{
    string strLabel;
    if (label)
        strLabel = label;

    pendingEdges_.push_back(Edge(src, dst, code, strLabel));
}

void ClTypeDotGenerator::emitPendingEdges() {
    TEdgeList::iterator i;
    for (i = pendingEdges_.begin(); i != pendingEdges_.end(); ++i) {
        const Edge &e = *i;
        glOut_ << e.src << " -> " << e.dst
            << "[color=" << CltColors[e.code];
        if (!e.label.empty())
            glOut_ << ", label=\"" << e.label << "\"";
        glOut_ << "];" << std::endl;
    }
    pendingEdges_.clear();
}

void ClTypeDotGenerator::digOneType(const struct cl_type *type, TStack &st)
{
    if (!type)
        // TRAP;
        return;

    cl_type_uid_t uid = type->uid;
    enum cl_type_e code = type->code;

    glOut_ << uid << " [label=\"#" << uid << ": ";
    this->printType(type);
    glOut_ << "\", color=" << CltColors[code] << "];" << std::endl;

    switch (code) {
        case CL_TYPE_VOID:
            break;

        case CL_TYPE_PTR:
        case CL_TYPE_ARRAY:
        case CL_TYPE_STRUCT:
        case CL_TYPE_UNION: {
                int cnt = type->item_cnt;
                if (CL_TYPE_ARRAY == code)
                    cnt = 1;

                for (int i = 0; i < cnt; ++i) {
                    struct cl_type_item &item = type->items[i];
                    cl_type_uid_t dst = item.type;
                    st.push(dst);
                    this->gobbleEdge(uid, dst, code, item.name);
                }
            }
            break;

        case CL_TYPE_FNC:
        case CL_TYPE_INT:
        case CL_TYPE_CHAR:
        case CL_TYPE_BOOL:
        case CL_TYPE_ENUM:
        case CL_TYPE_STRING:
            break;
    }
}

void ClTypeDotGenerator::handleType(cl_type_uid_t uid) {
    TStack st;
    st.push(uid);

    while (!st.empty()) {
        cl_type_uid_t curr = st.top();
        st.pop();

        if (hasKey(typeSet_, curr))
            continue;

        typeSet_.insert(curr);
        this->digOneType(AbstractCodeListener::getType(curr), st);
    }

    this->emitPendingEdges();
}

void ClTypeDotGenerator::handleOperand(const struct cl_operand *op) {
    if (!op || op->code == CL_OPERAND_VOID)
        return;

    const struct cl_type *type = op->type;
    if (!type)
        return;

    this->handleType(type->uid);
}

// /////////////////////////////////////////////////////////////////////////////
// public interface, see cl_typedot.hh for more details
ICodeListener* createClTypeDotGenerator(const char *args) {
    return new ClTypeDotGenerator(args);
}