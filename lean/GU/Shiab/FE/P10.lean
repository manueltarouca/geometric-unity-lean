import GU.Shiab.FormsEinstein

namespace GU.FormsW

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem ein_03_13 : checkKN (0, 3) (1, 3) = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem ein_03_22 : checkKN (0, 3) (2, 2) = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem ein_03_23 : checkKN (0, 3) (2, 3) = true := by decide +kernel

end GU.FormsW
