#!/bin/bash

#
# Copyright 2019 ISP RAS (http://www.ispras.ru)
# All Rights Reserved
#
# Licensed under the Apache License, Version 2.0 (the "License"); you may not use this file except
# in compliance with the License. You may obtain a copy of the License at
#
# http://www.apache.org/licenses/LICENSE-2.0
#
# Unless required by applicable law or agreed to in writing, software distributed under the License
# is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express
# or implied. See the License for the specific language governing permissions and limitations under
# the License.
#

# This script runs an argument binary on Spike simulator.

# Executes command with a timeout
# Params:
#   $1 timeout in seconds
#   $2 command
# Returns 1 if timed out 0 otherwise
timeout() {

  time=$1

  # start the command in a sub-shell to avoid problem with pipes
  # (spawn accepts one command)
  command="/bin/sh -c \"$2\""

  expect -c "set echo \"-noecho\"; set timeout $time; spawn -noecho $command; expect timeout { exit 1 } eof { exit 0 }"

  if [ $? = 1 ] ; then
    printf "\nTimeout after ${time} second(s)\n"
  fi
}

# Error message prefix
ERR_PREFIX="Simulation error:"

if [ $# -ne 3 ]; then
  echo "Usage: $0 BINARY-FILE SPIKE_TIMEOUT SPIKE_LOG" >&2
  exit 1
fi

# Get file name without ext from path
BINARY=$1
SPIKE_TIMEOUT=$2
SPIKE_LOG=$3

# Run Spike emulator on the argument binary.
# Output log is stored in file.
SPIKE=${RISCV_TCHAIN}/bin/spike

if [ ! -f "${SPIKE}" ] ; then

  SPIKE=spike

  if [ ! -f "${SPIKE}" ] ; then
    echo "$ERR_PREFIX can't find emulator neither in '${RISCV_TCHAIN}/bin' nor in '$PATH'" >&2
    exit 1
  fi
fi

timeout ${SPIKE_TIMEOUT} "$SPIKE -l --isa=rv64imafdcv -p1 $BINARY" &>${SPIKE_LOG}
