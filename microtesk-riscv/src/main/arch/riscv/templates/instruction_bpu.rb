#
# Copyright 2017 ISP RAS (http://www.ispras.ru)
#
# Licensed under the Apache License, Version 2.0 (the "License");
# you may not use this file except in compliance with the License.
# You may obtain a copy of the License at
#
#   http://www.apache.org/licenses/LICENSE-2.0
#
# Unless required by applicable law or agreed to in writing, software
# distributed under the License is distributed on an "AS IS" BASIS,
# WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
# See the License for the specific language governing permissions and
# limitations under the License.
#

require_relative 'riscv_base'

#
# Description:
#
# This small tests for BPU instructions.
#

class InstructionBPU < RISCVBaseTemplate

  def run
    trace "Run BPU instruction:"

    trace "\n\n"

    nop
#    trace "0"
#    b :branch1
#    label :branch2
#    trace "2"
#    nop
#    b :branch3
#    label :branch1
#    trace "1"
#    b :branch2
#    nop
#    label :branch3
#    trace "3"
#    nop

  end

end