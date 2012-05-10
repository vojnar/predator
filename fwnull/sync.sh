#!/bin/sh

# check whether stdout is connected to a terminal
if tty 0>&1 >/dev/null; then
    # initialize coloring escape sequences
    export R="\033[1;31m"
    export G="\033[1;32m"
    export Y="\033[1;33m"
    export B="\033[1;34m"
    export N="\033[0m"
fi

printf "${R}ATTENTION:${N} This script is not intended to be run !!!
Please do not commit the generated files to prevent a disaster...\n"

do_sync() {
    ./probe.sh $1
    printf "\n${B}Processing the results...${N}\n" >&2
    for i in $1; do
        c="$(printf %s "$i" | sed 's|\.c$||')"
        raw="${i}-fwnull.err"
        err="${c}.err$2"
        grep '\[-fplugin=libfwnull\.so\]$' "$raw" \
            | grep -v 'note: .*\[internal location\]' \
            | sed 's| \[-fplugin=libfwnull\.so\]$||' \
            | sed 's|^[^:]*/||' \
            > "$err"

        rm -f "$raw" "${i}-bare-gcc.err"
    done
    printf "\n\n" >&2
}

printf "\n${G}Basic analysis...${N}\n" >&2
do_sync "$*"
