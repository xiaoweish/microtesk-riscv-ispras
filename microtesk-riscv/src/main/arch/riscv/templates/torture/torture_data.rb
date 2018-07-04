#
# Copyright 2018 ISP RAS (http://www.ispras.ru)
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

require_relative '../riscv_base'
require_relative '../riscv_rand'

#
# Description:
#
#
module TortureData
  include RiscvRand

  def pre_testdata
    data {
label :hidden_data
      align 8
label :xreg_init_data
      (0..31).each { |i|
label :"reg_x#{i}_init"
      dword rand_biased
      }
    }

    data {
      align 8
label :freg_init_data
      (0..31).each { |i|
label :"reg_f#{i}_init"
      dword rand_biased
      }
    }

    RVTEST_DATA_BEGIN()

    data {
      align 8
label :xreg_output_data
      (0..31).each { |i|
label :"reg_x#{i}_output"
      dword rand_dword
      }
    }

    data {
      align 8
label :freg_output_data
      (0..31).each { |i|
label :"reg_f#{i}_output"
      dword rand_dword
      }
    }

    data {
      comment 'Memory Blocks'
      align 8
label :test_memory
      50.times { |i| dword rand_dword, rand_dword }
    }

    RVTEST_DATA_END()
  end

end
