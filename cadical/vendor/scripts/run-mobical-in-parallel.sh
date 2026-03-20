#!/bin/sh
name=`basename $0`
usage () {
cat <<EOF
usage: $name [ -h ] | ( <n> [ <arg> ... ] )

  -h     prints this command line option usage summary
  <n>    number of parallel mobical processes forked
  <arg>  arguments given to mobical

In addition the script forces '-q' as first option.
EOF
exit 0
}
die () {
  echo "$name: $error: $*" 1>&2
  exit 1
}
mobical=`dirname $0`/../build/mobical
test -f $mobical || die "could not find '$mobical'"
test $# = 0 && usage
case x"$1" in
  -h) usage;;
  x[1-9] | \
  x[1-9][0-9] | \
  x[1-9][0-9][0-9])
    n=$1;;
  *) die \
    "expected number of parallel processes in the range 1..999 as first argument"
    ;;
esac
shift
printf "running '$n' mobical processes"
if [ $# = 0 ]
then
  echo " (without any arguments)"
else
  echo " with argument '$*'"
fi
echo "using '$mobical'"
i=0
while [ $i -lt $n ]
do
  $mobical -q $* &
  i=`expr $i + 1`
done
wait
