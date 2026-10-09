import DifferentialGeometry.Topology.SimplicialComplex.Refinement.CommonTriangulation
import Mathlib.Analysis.Normed.Affine.Convex

namespace DifferentialGeometry.Topology.Engulfing

set_option linter.unusedSectionVars false

open Set Metric _root_.Geometry
open scoped _root_.Topology Pointwise

variable {E : Type*} [DecidableEq E] [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E]

omit [DecidableEq E] in
theorem exists_bounded_subset_interior_simplex {S : Set E} (hS : Bornology.IsBounded S) :
    ∃ b : AffineBasis (Fin (Module.finrank ℝ E + 1)) ℝ E,
      S ⊆ interior (convexHull ℝ (range b)) := by
  classical
  obtain ⟨b, hb, -⟩ := exists_mem_interior_convexHull_affineBasis
    (show (univ : Set E) ∈ 𝓝 (0 : E) from Filter.univ_mem)
  obtain ⟨δ, hδ, hball⟩ := Metric.mem_nhds_iff.mp (isOpen_interior.mem_nhds hb)
  obtain ⟨R, hR⟩ := (Metric.isBounded_iff_subset_ball (0 : E)).mp hS
  let t : ℝ := (max R 1) / δ
  have ht : 0 < t := div_pos (lt_of_lt_of_le zero_lt_one (le_max_right _ _)) hδ
  let d : AffineBasis (Fin (Module.finrank ℝ E + 1)) ℝ E := Units.mk0 t ht.ne' • b
  have hscale : interior (convexHull ℝ (range d)) =
      t • interior (convexHull ℝ (range b)) := by
    simp [d, Pi.smul_def, range_smul, interior_smul₀, convexHull_smul, ht.ne']
  refine ⟨d, ?_⟩
  rw [hscale]
  calc
    S ⊆ ball (0 : E) (max R 1) := hR.trans (ball_subset_ball (le_max_left _ _))
    _ = t • ball (0 : E) δ := by
      rw [_root_.smul_ball ht.ne', smul_zero, Real.norm_eq_abs, abs_of_pos ht]
      congr 1
      dsimp [t]
      field_simp
    _ ⊆ t • interior (convexHull ℝ (range b)) := Set.smul_set_mono hball

omit [DecidableEq E] in
theorem exists_finite_convex_complex_containing (S : SimplicialComplex ℝ E)
    (hS : S.faces.Finite) :
    ∃ K J : SimplicialComplex ℝ E,
      K.faces.Finite ∧ Convex ℝ K.space ∧ S.space ⊆ interior K.space ∧
      (∀ s ∈ K.faces, s.card ≤ Module.finrank ℝ E + 1) ∧
      J.faces.Finite ∧ J.faces ⊆ K.faces ∧ J.space = S.space ∧ simplicialRefines J S := by
  classical
  have hcompact : IsCompact S.space :=
    hS.isCompact_biUnion (fun s _ => s.finite_toSet.isCompact_convexHull ℝ)
  obtain ⟨b, hb⟩ := exists_bounded_subset_interior_simplex hcompact.isBounded
  let K₀ : SimplicialComplex ℝ E := barycentricComplex b b.ind
  have hK₀ : K₀.faces.Finite := barycentricComplex_finite_faces b b.ind
  have hspace₀ : K₀.space = convexHull ℝ (range b) := barycentricComplex_space_eq b b.ind
  have hdim₀ : ∀ s ∈ K₀.faces, s.card ≤ Module.finrank ℝ E + 1 := by
    intro s hs
    simpa only [Fintype.card_coe] using (K₀.indep hs).card_le_finrank_succ.trans
      (Nat.add_le_add_right (Submodule.finrank_le _) 1)
  have hSK : S.space ⊆ K₀.space := by
    rw [hspace₀]
    exact hb.trans interior_subset
  obtain ⟨K, J, hK, hspace, -, hdim, hJ, hJK, hJspace, hJref⟩ :=
    exists_subdivision_containing_complex K₀ S hK₀ hS hSK hdim₀
  refine ⟨K, J, hK, ?_, ?_, hdim, hJ, hJK, hJspace, hJref⟩
  · rw [hspace, hspace₀]
    exact convex_convexHull ℝ _
  · rwa [hspace, hspace₀]

end DifferentialGeometry.Topology.Engulfing
