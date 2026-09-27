/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.Topology.PiecewiseLinear.FourArcSphere
import DifferentialGeometry.Topology.PiecewiseLinear.PolygonalCircleCover

open Set Topology

namespace DifferentialGeometry.Topology.PiecewiseLinear

variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

theorem isPLSphere_one_range_of_piecewiseAffine_circle {f : loopCircle → E}
    (hinj : Function.Injective f)
    (hpl : IsPiecewiseAffineOn (fun t : ℝ => f (t : loopCircle)) univ) :
    IsPLSphere 1 (range f) := by
  let A : ℝ →ᵃ[ℝ] ℝ := AffineMap.lineMap 0 (1 / 2)
  let B : ℝ →ᵃ[ℝ] ℝ := AffineMap.lineMap 1 (1 / 2)
  have hA (t : ℝ) : A t = t / 2 := by
    simp [A, AffineMap.lineMap_apply_module, smul_eq_mul, div_eq_mul_inv]
  have hB (t : ℝ) : B t = 1 - t / 2 := by
    dsimp [B]
    rw [AffineMap.lineMap_apply_module]
    simp only [smul_eq_mul]
    ring
  let γ : ℝ → E := fun t => f (A t : loopCircle)
  let δ : ℝ → E := fun t => f (B t : loopCircle)
  have hγ : IsPiecewiseAffineOn γ (Icc (0 : ℝ) 1) := by
    have h := hpl.comp (isPiecewiseAffineOn_of_affine_of_isHPolytope
      A (isHPolytope_Icc (a := 0) (b := 1)))
    simpa [γ, Function.comp_def] using h
  have hδ : IsPiecewiseAffineOn δ (Icc (0 : ℝ) 1) := by
    have h := hpl.comp (isPiecewiseAffineOn_of_affine_of_isHPolytope
      B (isHPolytope_Icc (a := 0) (b := 1)))
    simpa [δ, Function.comp_def] using h
  have hγinj : InjOn γ (Icc (0 : ℝ) 1) := by
    intro s hs t ht hst
    have heq := hinj hst
    change (A s : loopCircle) = (A t : loopCircle) at heq
    have hAs : A s ∈ Ico (0 : ℝ) (0 + 1) := by rw [hA]; constructor <;> linarith [hs.1, hs.2]
    have hAt : A t ∈ Ico (0 : ℝ) (0 + 1) := by rw [hA]; constructor <;> linarith [ht.1, ht.2]
    have h := (AddCircle.coe_eq_coe_iff_of_mem_Ico hAs hAt).mp heq
    rw [hA, hA] at h
    linarith
  have hδinj : InjOn δ (Icc (0 : ℝ) 1) := by
    intro s hs t ht hst
    have heq := hinj hst
    change (B s : loopCircle) = (B t : loopCircle) at heq
    have hBs : B s ∈ Ioc (0 : ℝ) (0 + 1) := by rw [hB]; constructor <;> linarith [hs.1, hs.2]
    have hBt : B t ∈ Ioc (0 : ℝ) (0 + 1) := by rw [hB]; constructor <;> linarith [ht.1, ht.2]
    have h := (AddCircle.coe_eq_coe_iff_of_mem_Ioc hBs hBt).mp heq
    rw [hB, hB] at h
    linarith
  have hγpl := isPLHomeomorphOn_of_isPiecewiseAffineOn_of_bijOn
    isHPolytope_Icc.isPolyhedron hγ hγinj.bijOn_image
  have hδpl := isPLHomeomorphOn_of_isPiecewiseAffineOn_of_bijOn
    isHPolytope_Icc.isPolyhedron hδ hδinj.bijOn_image
  have hδ0 : δ 0 = γ 0 := by
    dsimp [δ, γ]
    rw [hB, hA]
    norm_num [AddCircle.coe_period, AddCircle.coe_zero]
  have hδ1 : δ 1 = γ 1 := by
    dsimp [δ, γ]
    rw [hB, hA]
    norm_num
  have hinter : γ '' Icc (0 : ℝ) 1 ∩ δ '' Icc (0 : ℝ) 1 = {γ 0, γ 1} := by
    apply Subset.antisymm
    · rintro y ⟨⟨s, hs, rfl⟩, t, ht, hts⟩
      by_cases ht0 : t = 0
      · subst t
        exact Or.inl (hts.symm.trans hδ0)
      · have heq := hinj hts
        change (B t : loopCircle) = (A s : loopCircle) at heq
        have hBt : B t ∈ Ico (0 : ℝ) (0 + 1) := by
          rw [hB]
          constructor <;> linarith [ht.1, ht.2, lt_of_le_of_ne ht.1 (Ne.symm ht0)]
        have hAs : A s ∈ Ico (0 : ℝ) (0 + 1) := by
          rw [hA]
          constructor <;> linarith [hs.1, hs.2]
        have h := (AddCircle.coe_eq_coe_iff_of_mem_Ico hBt hAs).mp heq
        rw [hB, hA] at h
        have hs1 : s = 1 := by linarith [hs.2, ht.2]
        exact Or.inr (congrArg γ hs1)
    · rintro y (rfl | rfl)
      · exact ⟨⟨0, by norm_num, rfl⟩, ⟨0, by norm_num, hδ0⟩⟩
      · exact ⟨⟨1, by norm_num, rfl⟩, ⟨1, by norm_num, hδ1⟩⟩
  have hcover : γ '' Icc (0 : ℝ) 1 ∪ δ '' Icc (0 : ℝ) 1 = range f := by
    apply Subset.antisymm
    · rintro y (⟨t, -, rfl⟩ | ⟨t, -, rfl⟩)
      · exact ⟨(A t : loopCircle), rfl⟩
      · exact ⟨(B t : loopCircle), rfl⟩
    · rintro y ⟨x, rfl⟩
      let t : ℝ := AddCircle.equivIco (1 : ℝ) 0 x
      have ht : t ∈ Ico (0 : ℝ) 1 := by
        simpa [t] using (AddCircle.equivIco (1 : ℝ) 0 x).2
      have htx : (t : loopCircle) = x := AddCircle.coe_equivIco
      by_cases ht2 : t ≤ 1 / 2
      · refine Or.inl ⟨2 * t, ⟨by linarith [ht.1], by linarith⟩, ?_⟩
        dsimp [γ]
        rw [hA, mul_div_cancel_left₀ _ (by norm_num : (2 : ℝ) ≠ 0), htx]
      · refine Or.inr ⟨2 * (1 - t), ⟨by linarith [ht.2], by linarith⟩, ?_⟩
        dsimp [δ]
        rw [hB, show 1 - 2 * (1 - t) / 2 = t by ring, htx]
  rw [← hcover]
  exact isPLSphere_one_union_of_isPLHomeomorphOn_Icc hγpl hδpl hδ0 hδ1 hinter

end DifferentialGeometry.Topology.PiecewiseLinear
