/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.Topology.PiecewiseLinear.DiskCrosscutMatching
import DifferentialGeometry.Topology.PiecewiseLinear.SphericalDiskExtension
import DifferentialGeometry.Topology.PiecewiseLinear.BallPairModel
import DifferentialGeometry.Topology.PiecewiseLinear.BallMarkedExtension

open Set

namespace DifferentialGeometry.Topology.PiecewiseLinear

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]

theorem exists_isPLHomeomorphOn_cone_disk_crosscut_pair
    {p : E} {q : F} {L : Geometry.SimplicialComplex ℝ E}
    {L' : Geometry.SimplicialComplex ℝ F} [Finite L.faces] [Finite L'.faces]
    (hL : IsConeBase p L) (hL' : IsConeBase q L')
    (hS : IsPLSphere 2 L.space) (hS' : IsPLSphere 2 L'.space)
    {D A : Set E} {D' A' : Set F} (hDL : D ⊆ L.space) (hDL' : D' ⊆ L'.space)
    {r : (Fin 3 → ℝ) → E} (hr : IsPLHomeomorphOn r (Convexity.StdSimplex.coordinateSet ℝ (Fin 3)) D)
    {η : ℝ → E} (hη : IsPLHomeomorphOn η (Icc 0 1) A) (hAD : A ⊆ D)
    (hmeet : A ∩ (r '' stdSimplexBoundary 2) = {η 0, η 1})
    {r' : (Fin 3 → ℝ) → F} (hr' : IsPLHomeomorphOn r' (Convexity.StdSimplex.coordinateSet ℝ (Fin 3)) D')
    {η' : ℝ → F} (hη' : IsPLHomeomorphOn η' (Icc 0 1) A') (hAD' : A' ⊆ D')
    (hmeet' : A' ∩ (r' '' stdSimplexBoundary 2) = {η' 0, η' 1}) :
    ∃ G : E → F, IsPLHomeomorphOn G (coneSet p L.space) (coneSet q L'.space) ∧
      G p = q ∧ G '' coneSet p D = coneSet q D' ∧
      G '' coneSet p (r '' stdSimplexBoundary 2) =
        coneSet q (r' '' stdSimplexBoundary 2) ∧
      G '' coneSet p A = coneSet q A' ∧
      G '' segment ℝ p (η 0) = segment ℝ q (η' 0) ∧
      G '' segment ℝ p (η 1) = segment ℝ q (η' 1) := by
  classical
  obtain ⟨f, hf, hfA, hfη⟩ :=
    exists_isPLHomeomorphOn_disk_eq_on_crosscut
      hr hη hAD hmeet hr' hη' hAD' hmeet'
  obtain ⟨g, hg, hgf⟩ :=
    exists_isPLHomeomorphOn_eqOn_disk_of_isPLSphere_two hS hS' ⟨r, hr⟩ hDL hf hDL'
  have hgD : g '' D = D' := hgf.image_eq.trans hf.image_eq
  have hbdD : r '' stdSimplexBoundary 2 ⊆ D :=
    image_subset_iff.mpr fun _ hz => hr.bijOn.mapsTo hz.1
  have hfbd : f '' (r '' stdSimplexBoundary 2) = r' '' stdSimplexBoundary 2 := by
    rw [← image_comp]
    exact (hr.trans hf).image_stdSimplexBoundary_congr hr'
  have hgbd : g '' (r '' stdSimplexBoundary 2) = r' '' stdSimplexBoundary 2 :=
    (hgf.mono hbdD).image_eq.trans hfbd
  have hgA : g '' A = A' := (hgf.mono hAD).image_eq.trans hfA
  have hη0 : η 0 ∈ D := hAD (hη.bijOn.mapsTo (by norm_num))
  have hη1 : η 1 ∈ D := hAD (hη.bijOn.mapsTo (by norm_num))
  have hg0 : g (η 0) = η' 0 := (hgf hη0).trans (hfη 0 (by norm_num))
  have hg1 : g (η 1) = η' 1 := (hgf hη1).trans (hfη 1 (by norm_num))
  obtain ⟨G, hG, -, hGp, -, hpair⟩ := exists_isPLHomeomorphOn_coneComplex_pair hL hL' hg
  rw [coneComplex_space_eq_coneSet hL, coneComplex_space_eq_coneSet hL'] at hG
  have hsegment (z : E) (hz : z ∈ L.space) :
      G '' segment ℝ p z = segment ℝ q (g z) := by
    have h := hpair {z} (singleton_subset_iff.mpr hz)
    rw [image_singleton, coneSet_eq_iUnion_segment (singleton_nonempty z),
      coneSet_eq_iUnion_segment (singleton_nonempty (g z)), biUnion_singleton,
      biUnion_singleton] at h
    exact h
  refine ⟨G, hG, hGp, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hpair D hDL, hgD]
  · rw [hpair _ (hbdD.trans hDL), hgbd]
  · rw [hpair A (hAD.trans hDL), hgA]
  · rw [hsegment (η 0) (hDL hη0), hg0]
  · rw [hsegment (η 1) (hDL hη1), hg1]

end DifferentialGeometry.Topology.PiecewiseLinear
