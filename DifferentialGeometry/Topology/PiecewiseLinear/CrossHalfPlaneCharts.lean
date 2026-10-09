/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.Topology.PiecewiseLinear.CrossHalfPlaneRectangle
import DifferentialGeometry.Topology.PiecewiseLinear.BallStarring

open Set Topology Metric

namespace DifferentialGeometry.Topology.PiecewiseLinear

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

open Classical in
theorem IsPLHomeomorphOn.exists_crossHalfPlane_disks
    {ψ : (ℝ × ℝ) × ℝ → E} {V : Set ((ℝ × ℝ) × ℝ)} {S Ω F Γ : Set E}
    (hψ : IsPLHomeomorphOn ψ V (S ∩ Ω)) (hV : IsOpen V) (hΩ : IsOpen Ω)
    (hF : ∀ p ∈ V, ψ p ∈ F ↔ p ∈ crossPlanes)
    (hΓ : ∀ p ∈ V, ψ p ∈ Γ ↔ p.1 = 0) {y : E} (hy : y ∈ S ∩ Ω) (hyΓ : y ∈ Γ) :
    ∃ (W : Set E) (P : Fin 4 → Set E) (q : Fin 4 → (Fin 3 → ℝ) → E),
      IsOpen W ∧ y ∈ W ∧ W ⊆ Ω ∧
      (∀ i, IsPLHomeomorphOn (q i) (Convexity.StdSimplex.coordinateSet ℝ (Fin 3)) (P i)) ∧
      (∀ i, P i ⊆ S ∩ F) ∧
      (∀ x ∈ S ∩ W, ∀ i, x ∈ P i ↔ Function.invFunOn ψ V x ∈ crossHalfPlane i) ∧
      ∀ x ∈ S ∩ W, ∀ i, x ∈ q i '' stdSimplexBoundary 2 ↔ x ∈ Γ := by
  obtain ⟨⟨w, z⟩, hpV, hpy⟩ := hψ.bijOn.surjOn hy
  have hw : w = 0 := (hΓ (w, z) hpV).mp (hpy.symm ▸ hyΓ)
  subst w
  obtain ⟨ε, hε, hεV⟩ := Metric.mem_nhds_iff.mp (hV.mem_nhds hpV)
  let r : ℝ := ε / 2
  have hr : 0 < r := half_pos hε
  have hclosed : closedBall ((0 : ℝ × ℝ), z) r ⊆ V :=
    (closedBall_subset_ball (half_lt_self hε)).trans hεV
  have hball : ball ((0 : ℝ × ℝ), z) r ⊆ V := ball_subset_closedBall.trans hclosed
  obtain ⟨Ω', hΩ', himg'⟩ := hψ.exists_image_eq_inter
    (O := ball ((0 : ℝ × ℝ), z) r) isOpen_ball
  have himg : ψ '' ball ((0 : ℝ × ℝ), z) r = S ∩ (Ω ∩ Ω') := by
    simpa only [inter_eq_right.mpr hball] using himg'
  have hyW : y ∈ Ω ∩ Ω' := by
    have hmem : y ∈ ψ '' ball ((0 : ℝ × ℝ), z) r :=
      ⟨((0 : ℝ × ℝ), z), mem_ball_self hr, hpy⟩
    rw [himg] at hmem
    exact hmem.2
  let B : Fin 4 → Set ((ℝ × ℝ) × ℝ) := crossHalfPlaneRectangle r z
  have hB : ∀ i, IsPLBall 2 (B i) := fun i => isPLBall_crossHalfPlaneRectangle i hr
  have hBV : ∀ i, B i ⊆ V := fun i =>
    (crossHalfPlaneRectangle_subset_closedBall i hr).trans hclosed
  choose q hq using (fun i => hB i)
  have hψB : ∀ i, IsPLHomeomorphOn ψ (B i) (ψ '' B i) :=
    fun i => hψ.restrict (hB i).isPolyhedron (hBV i)
  have hmem {A : Set ((ℝ × ℝ) × ℝ)} (hAV : A ⊆ V) {p : (ℝ × ℝ) × ℝ} (hp : p ∈ V) :
      ψ p ∈ ψ '' A ↔ p ∈ A := by
    constructor
    · rintro ⟨u, hu, heq⟩
      exact hψ.bijOn.injOn (hAV hu) hp heq ▸ hu
    · intro hpA
      exact mem_image_of_mem _ hpA
  refine ⟨Ω ∩ Ω', fun i => ψ '' B i, fun i => ψ ∘ q i,
    hΩ.inter hΩ', hyW, inter_subset_left, fun i => (hq i).trans (hψB i), ?_, ?_, ?_⟩
  · rintro i x ⟨p, hp, rfl⟩
    exact ⟨(hψ.bijOn.mapsTo (hBV i hp)).1,
      (hF p (hBV i hp)).mpr (crossHalfPlane_subset_crossPlanes i
        (crossHalfPlaneRectangle_subset_crossHalfPlane i hr hp))⟩
  · intro x hx i
    obtain ⟨p, hp, rfl⟩ := himg.symm ▸ hx
    rw [hψ.bijOn.invOn_invFunOn.1 (hball hp), hmem (hBV i) (hball hp)]
    exact mem_crossHalfPlaneRectangle_iff_of_mem_ball i hr hp
  · intro x hx i
    obtain ⟨p, hp, rfl⟩ := himg.symm ▸ hx
    obtain ⟨K, hKfin, hKspace⟩ := (hB i).isPolyhedron.exists_simplicialComplex
    let _ : Finite K.faces := hKfin.to_subtype
    have hqb := (hq i).image_stdSimplexBoundary_eq_boundaryComplex K hKspace
    have hbV : q i '' stdSimplexBoundary 2 ⊆ V := by
      rw [hqb]
      exact (boundaryComplex_space_subset 2 K).trans (hKspace.subset.trans (hBV i))
    rw [image_comp, hmem hbV (hball hp), hqb,
      mem_boundaryComplex_crossHalfPlaneRectangle_iff_of_mem_ball i hr K hKspace hp]
    exact (hΓ p (hball hp)).symm

end DifferentialGeometry.Topology.PiecewiseLinear
