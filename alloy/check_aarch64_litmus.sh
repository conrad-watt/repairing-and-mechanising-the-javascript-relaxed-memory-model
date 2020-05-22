#!/bin/bash

# $1 = test name
# $2 = timeout per run (seconds)
# $3 = path to alloy jar
# $4 = path and flags to solver (filename assumed to follow)

# enumerate the bounds on memory_model_conpare_js_aarch64.als

name=$1
timeout=$2
alloy=$3
solver=$4

# function run_one
function run_one {

  local name_cnf name_txt output res

  output=$(java -cp "$alloy:$alloy/alloy.jar" "OutCNF" $name)

  # When % is used in pattern ${variable%substring} it will return content of
  # variable with the shortest occurance of substring deleted from back of variable.
  name_cnf="${name%.*}.cnf"
  name_txt="${name%.*}.txt"

  mv $output $name_cnf

  output=$(timeout --signal=KILL $timeout $solver $name_cnf)

  if [ $? -eq 137 ]
  then
    printf "TIMEOUT\n" > $name_txt
  elif [[ $output = *"s UNSATISFIABLE"* ]]
  then
    printf "UNSAT\n" > $name_txt
  elif [[ $output = *"s SATISFIABLE"* ]]
  then
    printf "SAT\n" > $name_txt
  else
    printf "ERROR\n$output\n" > $name_txt
  fi

  rm $name_cnf
  exit 0
}

run_one
