/-
Copyright (c) 2026 Manuel Tarouca. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Manuel Tarouca
-/
import GU.Shiab.FormsEinstein

namespace GU.FormsW

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem ein_33_33 : checkKN (3, 3) (3, 3) = true := by decide +kernel

end GU.FormsW
