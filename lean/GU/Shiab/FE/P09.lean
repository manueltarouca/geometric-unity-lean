import GU.Shiab.FormsEinstein

namespace GU.FormsW

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem ein_03_03 : checkKN (0, 3) (0, 3) = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem ein_03_11 : checkKN (0, 3) (1, 1) = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem ein_03_12 : checkKN (0, 3) (1, 2) = true := by decide +kernel

end GU.FormsW
