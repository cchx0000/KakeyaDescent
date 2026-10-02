/-
Faithful hardening: re-exports `HardeningCore`.

The hardening machinery (P1-4/P1-5) lives in
`Theorems.Thm_FilteredDescent_HardeningCore` to break the import cycle:
`DescentInduction` needs `node_hardening_subpower` for the P1-4
integration, but the old `FaithfulHardening` (via `FaithfulTreeBridge` →
`EndToEnd`) transitively imported `DescentInduction`.

This file is kept as a compatibility shim; new code should import
`HardeningCore` directly.
-/

import Theorems.Thm_FilteredDescent_HardeningCore
