#!/bin/bash

# $1 = timeout per run (seconds)
# $2 = path to alloy jar
# $3 = path to plingeling

# enumerate the bounds on memory_model_conpare_js_aarch64.als

timeout=$1
alloy=$2
plingeling=$3

# function gen_alloy_assert
# $1 = location bound
# $2 = event bound
function gen_alloy_assert {
  printf "open memory_model_compare_js_aarch64 as compare\n\nrun check_compilation_aligned_no_rmw for exactly 2 Exec, $2 E, $1 Natural\n"
}

# function run_one
# $1 = location bound
# $2 = event bound
# return
# 0 if no counter-example
# 1 if counter-example
# 2 if timeout
# 255 otherwise
function run_one {

  local name name_cnf output res

  name=`mktemp --tmpdir=. --suffix=.als`

  gen_alloy_assert $1 $2 > $name

  output=$(java -cp "$alloy:$alloy/alloy.jar" "OutCNF" $name)

  # When % is used in pattern ${variable%substring} it will return content of
  # variable with the shortest occurance of substring deleted from back of variable.
  name_cnf="${name%.*}.cnf"

  mv $output $name_cnf

  output=$(timeout --signal=KILL $timeout $plingeling -verb=0 -maxnbthreads=30 $name_cnf)

  if [ $? -eq 137 ]
  then
    # command was killed
    res=2
  elif [[ $output = *"s UNSATISFIABLE"* ]]
  then
    res=0
  elif [[ $output = *"s SATISFIABLE"* ]]
  then
    res=1
  else
    res=255
  fi

  rm $name
  rm $name_cnf
  return $res
}

# function find_event_bound
# $1 = location bound
# appends result to compare_js_aarch64_bounds.txt
function find_event_bound {

  local evts=2 ret res="UNSAT"

  while true
  do
    run_one $1 $evts
    ret=$?

    if [ $ret -eq 0 ]
    then
      # printf "unsat: $evts\n"
      let evts=evts+1
    elif [ $ret -eq 1 ]
    then
      # printf "sat: $evts\n"
      res="SAT"
      printf "$1 $evts $res\n" >> compare_js_aarch64_bounds.txt
      return $evts
    elif [ $ret -eq 2 ]
    then
      printf "$1 $(( $evts-1 )) $res\n" >> compare_js_aarch64_bounds.txt
      return $(( $evts-1 ))
    else
      return 255
    fi
  done

}

function top_level {

  local locs=2 ret

  while true
  do
    find_event_bound $locs
    ret=$?

    if [ $ret -eq 255 ]
    then
      echo "something went wrong!"
      exit 255
    fi

    if [ $locs -ge 20 ]
    then
      exit 0
    fi

    let locs=locs+1
  done
}

printf "results (timeout $1s)\n" > compare_js_aarch64_bounds.txt
printf "locs evts sat?\n" >> compare_js_aarch64_bounds.txt

top_level

