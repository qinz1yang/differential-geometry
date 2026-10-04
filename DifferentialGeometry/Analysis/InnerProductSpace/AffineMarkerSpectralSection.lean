import DifferentialGeometry.Analysis.InnerProductSpace.LocalizedNormalSpectralSection

/-! GAF03 (master207B, B:5871): affine marker locality of the weighted spectral section.

If every centre whose weight is nonzero somewhere on `U` has `K`-coordinate `c` and its plane lies
in `Kᗮ`, then the spectral displacement `Q z (z - μ z)` has `K`-coordinate `K z - c` on `U`.
This is the affine (`c ≠ 0`) version of the CFS24 locality kernel. -/

set_option autoImplicit false
noncomputable section
open scoped BigOperators
open Metric

namespace Submodule

open Classical in
theorem affine_marker_weighted_normal_spectral_section
    {H ι : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [FiniteDimensional ℝ H]
    (S : Finset ι) (U : Set H) (w : ι → H → ℝ) (hw : ∀ z ∈ U, ∑ i ∈ S, w i z = 1)
    (L : ι → Submodule ℝ H) (y : ι → H) (K : Submodule ℝ H) (c : H)
    (hcenter : ∀ i ∈ S, (∃ z ∈ U, w i z ≠ 0) → K.starProjection (y i) = c)
    (hplane : ∀ i ∈ S, (∃ z ∈ U, w i z ≠ 0) → L i ≤ Kᗮ) :
    let Q : H → H →L[ℝ] H := fun z =>
      (⨆ μ ∈ ball (1 : ℝ) (1 / 2), Module.End.eigenspace
        (∑ i ∈ S, w i z • (L i)ᗮ.starProjection).toLinearMap μ).starProjection
    ∀ z ∈ U, K.starProjection (Q z (z - ∑ i ∈ S, w i z • y i)) = K.starProjection z - c := by
  intro Q z hz
  -- some centre is active at `z`, so `c ∈ K`
  have hactive : ∃ i ∈ S, w i z ≠ 0 := by
    by_contra hnone
    have hsum : ∑ i ∈ S, w i z = 0 :=
      Finset.sum_eq_zero (fun i hi => by
        by_contra h
        exact hnone ⟨i, hi, h⟩)
    rw [hw z hz] at hsum
    exact one_ne_zero hsum
  obtain ⟨i₀, hi₀, hwi₀⟩ := hactive
  have hcK : c ∈ K := by
    rw [← hcenter i₀ hi₀ ⟨z, hz, hwi₀⟩]
    exact K.starProjection_apply_mem _
  have hKc : K.starProjection c = c := starProjection_eq_self_iff.mpr hcK
  obtain ⟨-, hloc⟩ := localized_weighted_normal_spectral_section S U w hw L y c
  set J : Finset ι := S.filter (fun i => ∃ y ∈ U, w i y ≠ 0) with hJ
  set V : Submodule ℝ H := J.sup (fun i => (ℝ ∙ (y i - c)) ⊔ L i) with hV
  have hVK : V ≤ Kᗮ := by
    apply Finset.sup_le
    intro i hi
    obtain ⟨hiS, hiU⟩ := Finset.mem_filter.mp hi
    apply sup_le
    · rw [span_singleton_le_iff_mem, ← starProjection_apply_eq_zero_iff, map_sub,
        hcenter i hiS hiU, hKc, sub_self]
    · exact hplane i hiS hiU
  have hKV : K ≤ Vᗮ := by
    intro v hv
    rw [mem_orthogonal]
    intro u hu
    have := (mem_orthogonal K u).mp (hVK hu) v hv
    rw [real_inner_comm]
    exact this
  have hcomp : K.starProjection.comp Vᗮ.starProjection = K.starProjection :=
    starProjection_comp_starProjection_of_le hKV
  have happ (v : H) : K.starProjection (Vᗮ.starProjection v) = K.starProjection v :=
    congrArg (fun A : H →L[ℝ] H => A v) hcomp
  have hsec := (hloc z hz).2
  calc K.starProjection (Q z (z - ∑ i ∈ S, w i z • y i))
      = K.starProjection (Vᗮ.starProjection (Q z (z - ∑ i ∈ S, w i z • y i))) :=
        (happ _).symm
    _ = K.starProjection (Vᗮ.starProjection (z - c)) := by rw [hsec]
    _ = K.starProjection z - c := by rw [happ, map_sub, hKc]

theorem affine_marker_of_spectral_section_eq_zero
    {H ι : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [FiniteDimensional ℝ H]
    (S : Finset ι) (U : Set H) (w : ι → H → ℝ) (hw : ∀ z ∈ U, ∑ i ∈ S, w i z = 1)
    (L : ι → Submodule ℝ H) (y : ι → H) (K : Submodule ℝ H) (c : H)
    (hcenter : ∀ i ∈ S, (∃ z ∈ U, w i z ≠ 0) → K.starProjection (y i) = c)
    (hplane : ∀ i ∈ S, (∃ z ∈ U, w i z ≠ 0) → L i ≤ Kᗮ) :
    let Q : H → H →L[ℝ] H := fun z =>
      (⨆ μ ∈ ball (1 : ℝ) (1 / 2), Module.End.eigenspace
        (∑ i ∈ S, w i z • (L i)ᗮ.starProjection).toLinearMap μ).starProjection
    ∀ z ∈ U, Q z (z - ∑ i ∈ S, w i z • y i) = 0 → K.starProjection z = c := by
  intro Q z hz hzero
  have h := affine_marker_weighted_normal_spectral_section S U w hw L y K c hcenter hplane z hz
  rw [hzero, map_zero] at h
  exact (sub_eq_zero.mp h.symm)

/-- Affine (`c`-) form of `starProjection_weighted_normal_section` (S192): fixed weights, displacement
averaged after the spectral projector, arbitrary spectral window `s ∋ 1`. -/
theorem starProjection_weighted_normal_section_affine
    {𝕜 H A : Type*} [RCLike 𝕜] [NormedAddCommGroup H] [InnerProductSpace 𝕜 H] [FiniteDimensional 𝕜 H]
    (V : Submodule 𝕜 H) (c : H) (S : Finset A)
    (L : A → Submodule 𝕜 H) (x : A → H) (w : A → 𝕜)
    (hw : ∑ i ∈ S, w i = 1)
    (hL : ∀ i ∈ S, w i ≠ 0 → L i ≤ Vᗮ)
    (hx : ∀ i ∈ S, w i ≠ 0 → V.starProjection (x i) = c)
    (s : Set 𝕜) (hs : 1 ∈ s) (z : H) :
    let O : H →L[𝕜] H := ∑ i ∈ S, w i • (L i)ᗮ.starProjection
    let Q := (⨆ a ∈ s, Module.End.eigenspace O.toLinearMap a).starProjection
    V.starProjection (∑ i ∈ S, w i • Q (z - x i)) = V.starProjection z - c := by
  classical
  let O : H →L[𝕜] H := ∑ i ∈ S, w i • (L i)ᗮ.starProjection
  let Q := (⨆ a ∈ s, Module.End.eigenspace O.toLinearMap a).starProjection
  have hfix (v : H) (hv : v ∈ V) : O v = v :=
    sum_smul_starProjection_orthogonal_apply_of_mem_orthogonal Vᗮ S L w hw hL
      (le_orthogonal_orthogonal V hv)
  have hQ := starProjection_eigenspace_iSup_of_fixed V O s hs hfix
  have hQv (v : H) : V.starProjection (Q v) = V.starProjection v :=
    congrArg (fun B : H →L[𝕜] H => B v) hQ
  change V.starProjection (∑ i ∈ S, w i • Q (z - x i)) = V.starProjection z - c
  rw [map_sum]
  calc
    ∑ i ∈ S, V.starProjection (w i • Q (z - x i)) =
        ∑ i ∈ S, w i • (V.starProjection z - c) := by
      apply Finset.sum_congr rfl
      intro i hi
      by_cases hwi : w i = 0
      · simp only [hwi, zero_smul, map_zero]
      · rw [map_smul, hQv, map_sub, hx i hi hwi]
    _ = V.starProjection z - c := by rw [← Finset.sum_smul, hw, one_smul]

theorem starProjection_eq_of_weighted_normal_section_eq_zero
    {𝕜 H A : Type*} [RCLike 𝕜] [NormedAddCommGroup H] [InnerProductSpace 𝕜 H] [FiniteDimensional 𝕜 H]
    (V : Submodule 𝕜 H) (c : H) (S : Finset A)
    (L : A → Submodule 𝕜 H) (x : A → H) (w : A → 𝕜)
    (hw : ∑ i ∈ S, w i = 1)
    (hL : ∀ i ∈ S, w i ≠ 0 → L i ≤ Vᗮ)
    (hx : ∀ i ∈ S, w i ≠ 0 → V.starProjection (x i) = c)
    (s : Set 𝕜) (hs : 1 ∈ s) (z : H) :
    let O : H →L[𝕜] H := ∑ i ∈ S, w i • (L i)ᗮ.starProjection
    let Q := (⨆ a ∈ s, Module.End.eigenspace O.toLinearMap a).starProjection
    ∑ i ∈ S, w i • Q (z - x i) = 0 → V.starProjection z = c := by
  intro O Q hzero
  have h := starProjection_weighted_normal_section_affine V c S L x w hw hL hx s hs z
  change V.starProjection (∑ i ∈ S, w i • Q (z - x i)) = V.starProjection z - c at h
  rw [hzero, map_zero] at h
  exact sub_eq_zero.mp h.symm

end Submodule

namespace ContinuousLinearMap

/-- GAF05/ZSP01 stage step: a blended adjustment `x + ψ (y - x)` keeps the coordinate `c`
when the projected point has it and either the cutoff is one or the input already has it. -/
theorem blend_apply_eq_of_projection_eq
    {H V : Type*} [NormedAddCommGroup H] [NormedSpace ℝ H] [NormedAddCommGroup V] [NormedSpace ℝ V]
    (J : H →L[ℝ] V) {x y : H} {ψ : ℝ} {c : V} (hy : J y = c) (hψ : ψ = 1 ∨ J x = c) :
    J (x + ψ • (y - x)) = c := by
  rcases hψ with h | h
  · rw [h, one_smul, add_sub_cancel, hy]
  · rw [map_add, map_smul, map_sub, hy, h, sub_self, smul_zero, add_zero]

end ContinuousLinearMap
