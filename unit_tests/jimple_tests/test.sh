#!/bin/bash
if [ -z "$TIMELIMIT" ]; then
  TIMELIMIT=5
fi
echo -n .
( $1/unit_tests/limit -w $TIMELIMIT -x "$1/bin/jstar $2.jimple" ) \
  > stdout 2> stderr
EC=$?
case $EC in
  4)
    echo
    echo "Time limit (${TIMELIMIT}s) exceeded. Try"
    echo "  TIMELIMIT=${TIMELIMIT}0 make test"
    echo "or, if you use a byte-code build,"
    echo "  TIMELIMIT=${TIMELIMIT}0 make test-byte"
    echo "(or some other number >$TIMELIMIT)."
    ;;
  0)
    ;;
  *)
    echo 
    echo "Failed $2 in $(pwd) (errorcode $EC)"
    ;;
esac

