import Mathlib
import PEqualNP.Defs

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem PEqualNP.Outside.L_meta_9010 : ∀ x1 ∈ PEqualNP.HeptadCover.quadrangles PEqualNP.HeptadCover.singerLines3, ∀ x3 ∉ x1, ∃ x5 ∈ PEqualNP.HeptadCover.missLines PEqualNP.HeptadCover.singerLines3 x1, x3 ∈ PEqualNP.HeptadCover.singerLines3 x5 := by
  decide +kernel
