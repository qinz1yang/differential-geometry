import DifferentialGeometry.Analysis.Calculus.RadialReparametrization
import Mathlib.Analysis.Calculus.InverseFunctionTheorem.ContDiff
import Mathlib.LinearAlgebra.Complex.FiniteDimensional
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Lean.Elab.Tactic.Omega

set_option autoImplicit false

noncomputable section

open Set Filter Topology
open scoped ContDiff NNReal

namespace DifferentialGeometry.Analysis

private theorem bijective_prod_of_regular_kernel_vector
    (A B : ℂ →L[ℝ] ℝ) (hA : A ≠ 0) {v : ℂ}
    (hAv : A v = 0) (hBv : B v ≠ 0) :
    Function.Bijective (A.prod B) := by
  have hv : v ≠ 0 := by
    intro hv
    exact hBv (by simp only [hv, map_zero])
  have hAlinear : A.toLinearMap ≠ 0 := by
    intro hzero
    apply hA
    ext z
    exact LinearMap.congr_fun hzero z
  have hsurj : Function.Surjective A :=
    surjective_of_nonzero_of_finrank_eq_one (K := ℝ) (A := ℝ)
      (f := A.toLinearMap) (by simp) hAlinear
  have hrange : LinearMap.range A.toLinearMap = ⊤ :=
    LinearMap.range_eq_top.mpr hsurj
  have hdimC : Module.finrank ℝ ℂ = 2 := by
    rw [Module.finrank_eq_card_basis Complex.basisOneI, Fintype.card_fin]
  have hkerdim : Module.finrank ℝ (LinearMap.ker A.toLinearMap) = 1 := by
    have hdim := A.toLinearMap.finrank_range_add_finrank_ker
    rw [hrange, finrank_top, hdimC] at hdim
    norm_num at hdim
    omega
  have hspan : LinearMap.ker A.toLinearMap = Submodule.span ℝ ({v} : Set ℂ) :=
    eq_span_singleton_of_mem_of_finrank_eq_one hkerdim hAv hv
  have hinj : Function.Injective (A.prod B) := by
    intro x y hxy
    have hAx : A (x - y) = 0 := by
      simpa only [ContinuousLinearMap.prod_apply, map_sub] using
        sub_eq_zero.mpr (congrArg Prod.fst hxy)
    have hBx : B (x - y) = 0 := by
      simpa only [ContinuousLinearMap.prod_apply, map_sub] using
        sub_eq_zero.mpr (congrArg Prod.snd hxy)
    have hmem : x - y ∈ Submodule.span ℝ ({v} : Set ℂ) := by
      rw [← hspan]
      exact hAx
    obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.mp hmem
    have hcB : c * B v = 0 := by
      simpa only [← hc, map_smul, smul_eq_mul] using hBx
    have hc0 : c = 0 := (mul_eq_zero.mp hcB).resolve_right hBv
    apply sub_eq_zero.mp
    rw [← hc, hc0, zero_smul]
  refine ⟨hinj, ?_⟩
  apply (LinearMap.injective_iff_surjective_of_finrank_eq_finrank
    (f := (A.prod B).toLinearMap) ?_).mp hinj
  norm_num [hdimC, Module.finrank_prod]

/-- A continuous parametrization of a regular planar zero arc by its literal
ambient radius is smooth wherever a differentiable parametrization of the same
arc has nonzero radial derivative. No regularity at the arc's center is asserted. -/
theorem contDiffAt_radius_parametrization_of_regular_zero
    {f : ℂ → ℝ} {β α : ℝ → ℂ} {t r : ℝ}
    (hf : ContDiffAt ℝ ∞ f (β t))
    (hβ : DifferentiableAt ℝ β t) (hβne : β t ≠ 0)
    (hzero : ∀ᶠ s in 𝓝 t, f (β s) = 0)
    (hregular : fderiv ℝ f (β t) ≠ 0)
    (hradial : deriv (fun s => ‖β s‖) t ≠ 0)
    (hα : ContinuousAt α r) (hαr : α r = β t)
    (hαeq : ∀ᶠ s in 𝓝 r, f (α s) = 0 ∧ ‖α s‖ = s) :
    ContDiffAt ℝ ∞ α r := by
  let A : ℂ →L[ℝ] ℝ := fderiv ℝ f (β t)
  let B : ℂ →L[ℝ] ℝ := fderiv ℝ (fun z : ℂ => ‖z‖) (β t)
  let F : ℂ → ℝ × ℝ := fun z => (f z, ‖z‖)
  have hnorm : ContDiffAt ℝ ∞ (fun z : ℂ => ‖z‖) (β t) :=
    contDiffAt_norm ℝ hβne
  have hA : HasFDerivAt f A (β t) := (hf.differentiableAt (by simp)).hasFDerivAt
  have hB : HasFDerivAt (fun z : ℂ => ‖z‖) B (β t) :=
    (hnorm.differentiableAt (by simp)).hasFDerivAt
  have hAv : A (deriv β t) = 0 := by
    have hd := hA.comp_hasDerivAt t hβ.hasDerivAt
    have heq : (fun s => f (β s)) =ᶠ[𝓝 t] (fun _ => (0 : ℝ)) := hzero
    rw [← hd.deriv]
    change deriv (fun s => f (β s)) t = 0
    rw [heq.deriv_eq, deriv_const]
  have hBv : B (deriv β t) ≠ 0 := by
    have hd := hB.comp_hasDerivAt t hβ.hasDerivAt
    rw [← hd.deriv]
    exact hradial
  have hbij : Function.Bijective (A.prod B) :=
    bijective_prod_of_regular_kernel_vector A B hregular hAv hBv
  let L : ℂ ≃L[ℝ] (ℝ × ℝ) :=
    (LinearEquiv.ofBijective (A.prod B).toLinearMap hbij).toContinuousLinearEquiv
  have hF : ContDiffAt ℝ ∞ F (β t) := hf.prodMk hnorm
  have hDF : HasFDerivAt F (L : ℂ →L[ℝ] (ℝ × ℝ)) (β t) := hA.prodMk hB
  let e := hF.toOpenPartialHomeomorph F hDF (by simp : (∞ : ℕ∞ω) ≠ 0)
  have hecoe : (e : ℂ → ℝ × ℝ) = F :=
    hF.toOpenPartialHomeomorph_coe hDF (by simp)
  have hsource : β t ∈ e.source :=
    hF.mem_toOpenPartialHomeomorph_source hDF (by simp)
  have htarget : F (β t) ∈ e.target := e.map_source hsource
  have heback : e.symm (F (β t)) = β t := e.left_inv hsource
  have hinverse : ContDiffAt ℝ ∞ e.symm (F (β t)) := by
    apply e.contDiffAt_symm htarget (f₀' := L)
    · simpa only [heback, hecoe] using! hDF
    · simpa only [heback, hecoe] using hF
  have hpair : ∀ᶠ s in 𝓝 r, F (α s) = (0, s) := by
    filter_upwards [hαeq] with s hs
    exact Prod.ext hs.1 hs.2
  have hbase : F (β t) = (0, r) := by
    rw [← hαr]
    exact hpair.self_of_nhds
  have hsmooth : ContDiffAt ℝ ∞ (fun s : ℝ => e.symm (0, s)) r := by
    rw [hbase] at hinverse
    exact hinverse.comp r (contDiffAt_const.prodMk contDiffAt_id)
  have hnear : ∀ᶠ s in 𝓝 r, α s ∈ e.source :=
    hα (e.open_source.mem_nhds (hαr.symm ▸ hsource))
  have heq : α =ᶠ[𝓝 r] (fun s : ℝ => e.symm (0, s)) := by
    filter_upwards [hnear, hpair] with s hs hp
    have hleft : e.symm (F (α s)) = α s := e.left_inv hs
    rw [hp] at hleft
    exact hleft.symm
  exact hsmooth.congr_of_eventuallyEq heq

/-- A regular C¹ planar zero arc has a Lipschitz parametrization by its original
radius which is smooth at positive radius. The parametrization is the original
arc composed with the inverse of its original norm, without replacing the arc. -/
theorem exists_smooth_punctured_radial_reparametrization_of_zero_arc
    {f : ℂ → ℝ} {β : ℝ → ℂ} {v : ℂ} {tmax : ℝ}
    (htmax : 0 < tmax)
    (hβ : ContDiffOn ℝ 1 β (Ioo (-tmax) tmax)) (hβzero : β 0 = 0)
    (hd : HasDerivAt β v 0) (hv : v ≠ 0)
    (hzero : ∀ t ∈ Ico 0 tmax, f (β t) = 0)
    (hregular : ∀ t ∈ Ioo 0 tmax,
      ContDiffAt ℝ ∞ f (β t) ∧ fderiv ℝ f (β t) ≠ 0) :
    ∃ T : ℝ, 0 < T ∧ T < tmax ∧
      let R := ‖β T‖
      let τ := Function.invFunOn (fun t => ‖β t‖) (Icc 0 T)
      let α := β ∘ τ
      0 < R ∧ α 0 = 0 ∧
        (∀ r ∈ Icc 0 R, ‖α r‖ = r ∧ f (α r) = 0) ∧
        (∃ L : ℝ≥0, LipschitzOnWith L α (Icc 0 R)) ∧
        ContDiffOn ℝ ∞ α (Ioo 0 R) ∧
        ∀ r ∈ Ioc 0 R, fderiv ℝ f (α r) ≠ 0 := by
  have hβat : ContDiffAt ℝ 1 β 0 :=
    hβ.contDiffAt (isOpen_Ioo.mem_nhds ⟨neg_lt_zero.mpr htmax, htmax⟩)
  obtain ⟨T, hT, hTmax, hR, hτzero, hτmem, hright, hleft,
    ⟨K, L, hτLip, hαLip⟩, hderiv⟩ :=
    exists_radial_reparametrization_of_contDiffAt hβat hβzero hd hv htmax
  let R := ‖β T‖
  let τ := Function.invFunOn (fun t => ‖β t‖) (Icc 0 T)
  let α := β ∘ τ
  have hnorm (r : ℝ) (hr : r ∈ Icc 0 R) : ‖α r‖ = r := hright r hr
  have hparampos (r : ℝ) (hr : r ∈ Ioc 0 R) : 0 < τ r := by
    have hmem := hτmem ⟨hr.1.le, hr.2⟩
    apply lt_of_le_of_ne hmem.1
    intro hz
    have hn := hright r ⟨hr.1.le, hr.2⟩
    rw [← hz, hβzero, norm_zero] at hn
    exact hr.1.ne hn
  have hparamlt (r : ℝ) (hr : r ∈ Ioo 0 R) : τ r < T := by
    apply lt_of_le_of_ne (hτmem ⟨hr.1.le, hr.2.le⟩).2
    intro heq
    have hn := hright r ⟨hr.1.le, hr.2.le⟩
    rw [heq] at hn
    exact hr.2.ne hn.symm
  refine ⟨T, hT, hTmax, hR, ?_, ?_, ⟨L, hαLip⟩, ?_, ?_⟩
  · change β (τ 0) = 0
    simp only [τ, hτzero, hβzero]
  · intro r hr
    exact ⟨hnorm r hr, hzero (τ r) ⟨(hτmem hr).1, (hτmem hr).2.trans_lt hTmax⟩⟩
  · intro r hr
    have hτr : τ r ∈ Ioo 0 tmax :=
      ⟨hparampos r ⟨hr.1, hr.2.le⟩, (hparamlt r hr).trans hTmax⟩
    have hβr : DifferentiableAt ℝ β (τ r) :=
      (hβ.contDiffAt (isOpen_Ioo.mem_nhds
        ⟨(neg_lt_zero.mpr htmax).trans hτr.1, hτr.2⟩)).differentiableAt one_ne_zero
    have hβne : β (τ r) ≠ 0 := by
      apply norm_ne_zero_iff.mp
      rw [hright r ⟨hr.1.le, hr.2.le⟩]
      exact hr.1.ne'
    have hzeroNear : ∀ᶠ s in 𝓝 (τ r), f (β s) = 0 := by
      filter_upwards [isOpen_Ioo.mem_nhds hτr] with s hs
      exact hzero s ⟨hs.1.le, hs.2⟩
    have hradial : deriv (fun s => ‖β s‖) (τ r) ≠ 0 := by
      have hbound := (hderiv (τ r)
        ⟨hτr.1, (hτmem ⟨hr.1.le, hr.2.le⟩).2⟩).2
      exact ne_of_gt ((half_pos (norm_pos_iff.mpr hv)).trans_le hbound)
    have hαcontinuous : ContinuousAt α r :=
      hαLip.continuousOn.continuousAt (Icc_mem_nhds hr.1 hr.2)
    have heq : ∀ᶠ s in 𝓝 r, f (α s) = 0 ∧ ‖α s‖ = s := by
      filter_upwards [Icc_mem_nhds hr.1 hr.2] with s hs
      exact ⟨hzero (τ s) ⟨(hτmem hs).1, (hτmem hs).2.trans_lt hTmax⟩,
        hnorm s hs⟩
    exact (contDiffAt_radius_parametrization_of_regular_zero (hregular _ hτr).1
      hβr hβne hzeroNear (hregular _ hτr).2 hradial hαcontinuous rfl heq).contDiffWithinAt
  · intro r hr
    exact (hregular (τ r)
      ⟨hparampos r hr, (hτmem ⟨hr.1.le, hr.2⟩).2.trans_lt hTmax⟩).2

end DifferentialGeometry.Analysis
