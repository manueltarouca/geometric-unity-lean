import GU.Shiab.FormsEinstein

namespace GU.FormsW

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem ein_00_00 : checkKN (0, 0) (0, 0) = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem ein_00_01 : checkKN (0, 0) (0, 1) = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem ein_00_02 : checkKN (0, 0) (0, 2) = true := by decide +kernel

end GU.FormsW
