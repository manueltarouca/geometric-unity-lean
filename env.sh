# Copyright (c) 2026 Manuel Tarouca
# SPDX-License-Identifier: Apache-2.0
# Source this to use the workspace-local Lean toolchain: `source env.sh`
GU_ROOT="$(cd "$(dirname "${BASH_SOURCE[0]:-${(%):-%x}}")" && pwd)"
export ELAN_HOME="$GU_ROOT/.toolchain/elan"
export XDG_CACHE_HOME="$GU_ROOT/.toolchain/cache"
export MATHLIB_CACHE_DIR="$GU_ROOT/.toolchain/cache/mathlib"
export PATH="$ELAN_HOME/bin:$PATH"
