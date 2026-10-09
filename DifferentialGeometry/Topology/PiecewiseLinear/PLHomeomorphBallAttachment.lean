/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.Topology.PiecewiseLinear.BallReplacement

open Set

namespace DifferentialGeometry.Topology.PiecewiseLinear

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]

theorem IsPLHomeomorphOn.exists_extension_union_ball {n : ℕ}
    {P D : Set E} {Q D' : Set F} {f : E → F}
    (hf : IsPLHomeomorphOn f P Q) (hP : IsPolyhedron P)
    {r : (Fin (n + 2) → ℝ) → E} {s : (Fin (n + 2) → ℝ) → F}
    (hr : IsPLHomeomorphOn r (Convexity.StdSimplex.coordinateSet ℝ (Fin (n + 2))) D)
    (hs : IsPLHomeomorphOn s (Convexity.StdSimplex.coordinateSet ℝ (Fin (n + 2))) D')
    (hPD : P ∩ D = r '' stdSimplexBoundary (n + 1))
    (hQD : Q ∩ D' = s '' stdSimplexBoundary (n + 1))
    (hboundary : f '' (r '' stdSimplexBoundary (n + 1)) = s '' stdSimplexBoundary (n + 1)) :
    ∃ g : E → F, IsPLHomeomorphOn g (P ∪ D) (Q ∪ D') ∧ EqOn g f P := by
  have hb : IsPLHomeomorphOn f (r '' stdSimplexBoundary (n + 1))
      (s '' stdSimplexBoundary (n + 1)) := by
    rw [← hboundary]
    exact hf.restrict hr.isPLSphere_image_stdSimplexBoundary.isPolyhedron
      (hPD.symm.subset.trans inter_subset_left)
  obtain ⟨k, hk, hkf⟩ := exists_isPLHomeomorphOn_extension_of_stdSimplexBoundary hr hs hb
  obtain ⟨g, hg, hgf, -⟩ := exists_isPLHomeomorphOn_union hP
    (IsPLBall.isPolyhedron (⟨r, hr⟩ : IsPLBall (n + 1) D)) hf hk
    (by rw [hPD]; exact hkf.symm)
    (by rw [hPD, hQD]; exact hb.bijOn.surjOn)
  exact ⟨g, hg, hgf⟩

end DifferentialGeometry.Topology.PiecewiseLinear
