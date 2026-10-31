import GU.Shiab.FormsEinstein

namespace GU.FormsW

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem ein_01_33 : checkKN (0, 1) (3, 3) = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem ein_02_02 : checkKN (0, 2) (0, 2) = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem ein_02_03 : checkKN (0, 2) (0, 3) = true := by decide +kernel

end GU.FormsW
