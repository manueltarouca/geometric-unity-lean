import GU.Shiab.FormsEinstein

namespace GU.FormsW

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem ein_11_13 : checkKN (1, 1) (1, 3) = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem ein_11_22 : checkKN (1, 1) (2, 2) = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem ein_11_23 : checkKN (1, 1) (2, 3) = true := by decide +kernel

end GU.FormsW
