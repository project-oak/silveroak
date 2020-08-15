#
# Copyright 2019 The Project Oak Authors
#
# Licensed under the Apache License, Version 2.0 (the "License");
# you may not use this file except in compliance with the License.
# You may obtain a copy of the License at
#
#     http://www.apache.org/licenses/LICENSE-2.0
#
# Unless required by applicable law or agreed to in writing, software
# distributed under the License is distributed on an "AS IS" BASIS,
# WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
# See the License for the specific language governing permissions and
# limitations under the License.
#

ZCU104=../../../../zcu104

install:
		cp pins_zcu104.xdc $(ZCU104)/opentitan/hw/top_earlgrey/data/
		cp clkgen_zcu104.sv $(ZCU104)/opentitan/hw/top_earlgrey/rtl/
		cp top_earlgrey_zcu104.sv $(ZCU104)/opentitan/hw/top_earlgrey/rtl/
		cp top_earlgrey_zcu104.core $(ZCU104)/opentitan/hw/top_earlgrey
		cp vivado_hook_opt_design_post.tcl $(ZCU104)/opentitan/hw/top_earlgrey/util/
		cp vivado_hook_write_bitstream_pre.tcl $(ZCU104)/opentitan/hw/top_earlgrey/util/
