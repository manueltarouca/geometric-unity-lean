/-
Copyright (c) 2026 Manuel Tarouca. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Manuel Tarouca
-/
import GU.Shiab.FormsEinstein

namespace GU.FormsW

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem ein_00_33 : checkKN (0, 0) (3, 3) = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem ein_01_01 : checkKN (0, 1) (0, 1) = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem ein_01_02 : checkKN (0, 1) (0, 2) = true := by decide +kernel

end GU.FormsW
