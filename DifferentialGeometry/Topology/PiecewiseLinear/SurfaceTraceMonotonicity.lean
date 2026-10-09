/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.Topology.PiecewiseLinear.CanonicalTowerSeams
import DifferentialGeometry.Topology.PiecewiseLinear.SphereInclusion

open Set

namespace DifferentialGeometry.Topology.PiecewiseLinear

local notation "E3" => EuclideanSpace ℝ (Fin 3)

theorem traceCircles_subset_of_inter_subset {L L' T : Set E3}
    (hcover : L ∩ T = ⋃ G ∈ traceCircles L T, G) (hsub : L' ∩ T ⊆ L ∩ T) :
    traceCircles L' T ⊆ traceCircles L T := by
  rintro G ⟨x, hx, hG, hGs⟩
  obtain ⟨J, hJ, hxJ⟩ := mem_iUnion₂.mp (hcover.subset (hsub hx))
  obtain ⟨y, -, hJ, hJs⟩ := hJ
  have hxJy : x ∈ connectedComponentIn (L ∩ T) y := hJ ▸ hxJ
  have hJx : connectedComponentIn (L ∩ T) x = J :=
    (connectedComponentIn_eq hxJy).symm.trans hJ.symm
  have hGsub : G ⊆ J := by
    rw [hG, ← hJx]
    exact connectedComponentIn_mono x hsub
  have hGJ : G = J := eq_of_subset_of_isPLSphere hGs hJs hGsub
  exact ⟨x, hsub hx, hGJ.trans hJx.symm, hGs⟩

theorem nullTraceCount_le_of_traceCircles_subset {L L' T : Set E3}
    (hfin : (traceCircles L T).Finite) (hsub : traceCircles L' T ⊆ traceCircles L T) :
    nullTraceCount L' T ≤ nullTraceCount L T := by
  unfold nullTraceCount
  exact Set.ncard_le_ncard (fun G hG => ⟨hsub hG.1, hG.2⟩)
    (hfin.subset fun _ hG => hG.1)

end DifferentialGeometry.Topology.PiecewiseLinear
