import GU.Shiab.FormsEinstein

namespace GU.FormsW

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem ein_02_22 : checkKN (0, 2) (2, 2) = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem ein_02_23 : checkKN (0, 2) (2, 3) = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem ein_02_33 : checkKN (0, 2) (3, 3) = true := by decide +kernel

end GU.FormsW
