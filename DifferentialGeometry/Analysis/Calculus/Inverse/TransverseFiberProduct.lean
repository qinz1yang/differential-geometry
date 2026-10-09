import DifferentialGeometry.Analysis.Calculus.Inverse.LocalSubmersion
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Analysis.Calculus.Deriv.Prod
import Mathlib.Analysis.Calculus.Deriv.Linear

set_option autoImplicit false
noncomputable section

open Set Filter
open scoped ContDiff Topology

namespace DifferentialGeometry.Analysis

variable {E F G : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
  [NormedAddCommGroup G] [NormedSpace ℝ G] [FiniteDimensional ℝ G]

omit [FiniteDimensional ℝ G] in
private theorem exists_open_injective_fderiv
    {f : E → G} {A : Set E} {a : E}
    (hA : IsOpen A) (ha : a ∈ A) (hf : ContDiffOn ℝ ∞ f A)
    (hi : Function.Injective (fderiv ℝ f a)) :
    ∃ V : Set E, IsOpen V ∧ a ∈ V ∧ V ⊆ A ∧
      ∀ x ∈ V, Function.Injective (fderiv ℝ f x) := by
  have hn : {x | Function.Injective (fderiv ℝ f x)} ∈ 𝓝 a :=
    ((hf.contDiffAt (hA.mem_nhds ha)).continuousAt_fderiv (by simp)).preimage_mem_nhds
      (ContinuousLinearMap.isOpen_injective.mem_nhds hi)
  obtain ⟨V, hV, hVo, haV⟩ := mem_nhds_iff.mp (Filter.inter_mem (hA.mem_nhds ha) hn)
  exact ⟨V, hVo, haV, fun x hx => (hV hx).1, fun x hx => (hV hx).2⟩

/-- A one-dimensional transverse fiber product has a smooth local interval
parametrization, and both projections of that parametrization are immersed. -/
theorem exists_local_transverse_fiber_curve
    {f : E → G} {g : F → G} {A : Set E} {B : Set F}
    {a : E} {b : F}
    (hA : IsOpen A) (hB : IsOpen B) (ha : a ∈ A) (hb : b ∈ B)
    (hf : ContDiffOn ℝ ∞ f A) (hg : ContDiffOn ℝ ∞ g B)
    (heq : f a = g b)
    (hfi : Function.Injective (fderiv ℝ f a))
    (hgi : Function.Injective (fderiv ℝ g b))
    (htrans : Function.Surjective
      ((fderiv ℝ f a).coprod (-(fderiv ℝ g b))))
    (hdim : Module.finrank ℝ E + Module.finrank ℝ F =
      Module.finrank ℝ G + 1) :
    ∃ (r : ℝ) (W : Set (E × F)) (c : ℝ → E × F),
      0 < r ∧ IsOpen W ∧ (a, b) ∈ W ∧ W ⊆ A ×ˢ B ∧
      ContDiffOn ℝ ∞ c (Set.Ioo (-r) r) ∧ c 0 = (a, b) ∧
      (∀ t ∈ Set.Ioo (-r) r,
        c t ∈ W ∧ f (c t).1 = g (c t).2) ∧
      (∀ z ∈ W,
        f z.1 = g z.2 ↔
          ∃! t : ℝ, t ∈ Set.Ioo (-r) r ∧ c t = z) ∧
      Set.InjOn c (Set.Ioo (-r) r) ∧
      (∀ t ∈ Set.Ioo (-r) r,
        deriv (fun s : ℝ => (c s).1) t ≠ 0 ∧
        deriv (fun s : ℝ => (c s).2) t ≠ 0) := by
  let : CompleteSpace E := FiniteDimensional.complete ℝ E
  let : CompleteSpace F := FiniteDimensional.complete ℝ F
  obtain ⟨A₀, hA₀, ha₀, hA₀A, hiA₀⟩ := exists_open_injective_fderiv hA ha hf hfi
  obtain ⟨B₀, hB₀, hb₀, hB₀B, hiB₀⟩ := exists_open_injective_fderiv hB hb hg hgi
  let H : E × F → G := fun z => f z.1 - g z.2
  let L : E × F →L[ℝ] G := (fderiv ℝ f a).coprod (-(fderiv ℝ g b))
  have hH : ContDiffOn ℝ ∞ H (A₀ ×ˢ B₀) :=
    ((hf.mono hA₀A).comp contDiffOn_fst (fun _ hz => hz.1)).sub
      ((hg.mono hB₀B).comp contDiffOn_snd (fun _ hz => hz.2))
  have hL : HasFDerivAt H L (a, b) := by
    have hLeq : L = (fderiv ℝ f a).comp (ContinuousLinearMap.fst ℝ E F) -
        (fderiv ℝ g b).comp (ContinuousLinearMap.snd ℝ E F) := by
      apply ContinuousLinearMap.ext
      intro z
      change fderiv ℝ f a z.1 + -(fderiv ℝ g b z.2) =
        fderiv ℝ f a z.1 - fderiv ℝ g b z.2
      exact (sub_eq_add_neg _ _).symm
    rw [hLeq]
    exact (((hf.contDiffAt (hA.mem_nhds ha)).differentiableAt (by simp)).hasFDerivAt.comp
      (a, b) hasFDerivAt_fst).sub
      (((hg.contDiffAt (hB.mem_nhds hb)).differentiableAt (by simp)).hasFDerivAt.comp
        (a, b) hasFDerivAt_snd)
  have hsplit : L.HasRightInverse :=
    ContinuousLinearMap.HasRightInverse.of_surjective_of_finiteDimensional htrans
  obtain ⟨e, heab, heAB, hesm, heism, hefst, heproj⟩ :=
    exists_localProjection_of_hasRightInverse hH (hA₀.prod hB₀) ⟨ha₀, hb₀⟩ hL hsplit
  let Q := ContinuousLinearEquiv.equivOfRightInverse L hsplit.rightInverse
    hsplit.rightInverse_rightInverse
  have hkdim : Module.finrank ℝ ℝ = Module.finrank ℝ L.ker := by
    have hQ := Q.toLinearEquiv.finrank_eq
    rw [Module.finrank_prod, Module.finrank_prod] at hQ
    rw [Module.finrank_self]
    omega
  let η : ℝ ≃L[ℝ] L.ker := ContinuousLinearEquiv.ofFinrankEq hkdim
  let k₀ : L.ker := (e (a, b)).2
  let φ : ℝ → G × L.ker := fun t => (0, k₀ + η t)
  let T : G × L.ker → ℝ := fun z => η.symm (z.2 - k₀)
  have hφ : ContDiff ℝ ∞ φ := contDiff_const.prodMk (contDiff_const.add η.contDiff)
  have hT : Continuous T := η.symm.continuous.comp (continuous_snd.sub continuous_const)
  have hfirst : (e (a, b)).1 = 0 := by
    rw [hefst]
    exact sub_eq_zero.mpr heq
  have hφzero : φ 0 = e (a, b) := by
    apply Prod.ext
    · exact hfirst.symm
    · simp [φ, k₀]
  have hpre : φ ⁻¹' e.target ∈ 𝓝 (0 : ℝ) :=
    hφ.continuous.continuousAt.preimage_mem_nhds
      (e.open_target.mem_nhds (hφzero.symm ▸ e.map_source heab))
  obtain ⟨r, hr, hrsub⟩ := Metric.mem_nhds_iff.mp hpre
  have hφmem (t : ℝ) (ht : t ∈ Ioo (-r) r) : φ t ∈ e.target := by
    apply hrsub
    simpa only [Metric.mem_ball, Real.dist_eq, sub_zero, abs_lt, Set.mem_Ioo] using ht
  have hTφ (t : ℝ) : T (φ t) = t := by simp [T, φ]
  have hφT (z : E × F) (hz : (e z).1 = 0) : φ (T (e z)) = e z := by
    apply Prod.ext
    · exact hz.symm
    · change k₀ + η (η.symm ((e z).2 - k₀)) = (e z).2
      rw [η.apply_symm_apply]
      abel
  let W : Set (E × F) := e.source ∩ e ⁻¹' (T ⁻¹' Ioo (-r) r)
  let c : ℝ → E × F := fun t => e.symm (φ t)
  have hWo : IsOpen W := e.isOpen_inter_preimage (isOpen_Ioo.preimage hT)
  have habW : (a, b) ∈ W := by
    refine ⟨heab, ?_⟩
    change T (e (a, b)) ∈ Ioo (-r) r
    rw [← hφzero, hTφ]
    exact ⟨neg_neg_of_pos hr, hr⟩
  have hWAB : W ⊆ A ×ˢ B := fun _ hz =>
    ⟨hA₀A (heAB hz.1).1, hB₀B (heAB hz.1).2⟩
  have hcsm : ContDiffOn ℝ ∞ c (Ioo (-r) r) :=
    heism.comp hφ.contDiffOn hφmem
  have hec (t : ℝ) (ht : t ∈ Ioo (-r) r) : e (c t) = φ t :=
    e.right_inv (hφmem t ht)
  have hcW (t : ℝ) (ht : t ∈ Ioo (-r) r) : c t ∈ W := by
    refine ⟨e.map_target (hφmem t ht), ?_⟩
    change T (e (c t)) ∈ Ioo (-r) r
    rwa [hec t ht, hTφ]
  have hcfiber (t : ℝ) (ht : t ∈ Ioo (-r) r) : f (c t).1 = g (c t).2 := by
    apply sub_eq_zero.mp
    exact heproj (φ t) (hφmem t ht)
  have hcT (t : ℝ) (ht : t ∈ Ioo (-r) r) : T (e (c t)) = t := by
    rw [hec t ht, hTφ]
  have hchar (z : E × F) (hz : z ∈ W) :
      f z.1 = g z.2 ↔ ∃! t : ℝ, t ∈ Ioo (-r) r ∧ c t = z := by
    constructor
    · intro hfg
      have hzfirst : (e z).1 = 0 := by
        rw [hefst]
        exact sub_eq_zero.mpr hfg
      refine ⟨T (e z), ⟨hz.2, ?_⟩, ?_⟩
      · change e.symm (φ (T (e z))) = z
        rw [hφT z hzfirst]
        exact e.left_inv hz.1
      · intro t ht
        exact (hcT t ht.1).symm.trans (congrArg (fun y => T (e y)) ht.2)
    · rintro ⟨t, ⟨ht, rfl⟩, _⟩
      exact hcfiber t ht
  have hcinj : InjOn c (Ioo (-r) r) := by
    intro s hs t ht hst
    exact (hcT s hs).symm.trans ((congrArg (fun z => T (e z)) hst).trans (hcT t ht))
  refine ⟨r, W, c, hr, hWo, habW, hWAB, hcsm, ?_,
    fun t ht => ⟨hcW t ht, hcfiber t ht⟩, hchar, hcinj, ?_⟩
  · change e.symm (φ 0) = (a, b)
    rw [hφzero]
    exact e.left_inv heab
  · intro t ht
    have hct : HasDerivAt c (deriv c t) t :=
      ((hcsm.contDiffAt (isOpen_Ioo.mem_nhds ht)).differentiableAt (by simp)).hasDerivAt
    have hedt := ((hesm.contDiffAt (e.open_source.mem_nhds (hcW t ht).1)).differentiableAt
      (by simp)).hasFDerivAt.comp_hasDerivAt t hct
    have heqnear : φ =ᶠ[𝓝 t] fun s => e (c s) := by
      filter_upwards [isOpen_Ioo.mem_nhds ht] with s hs
      exact (hec s hs).symm
    have hφdt : HasDerivAt φ ((0 : G), η 1) t := by
      simpa only [φ, Pi.add_apply, ContinuousLinearEquiv.coe_coe, zero_add] using
        (hasDerivAt_const t (0 : G)).prodMk
          ((hasDerivAt_const t k₀).add η.toContinuousLinearMap.hasDerivAt)
    have hcne : deriv c t ≠ 0 := by
      intro hzero
      have hh := (hedt.congr_of_eventuallyEq heqnear).unique hφdt
      rw [hzero, map_zero] at hh
      have hη : η 1 = 0 := (congrArg Prod.snd hh).symm
      exact one_ne_zero (η.injective (hη.trans (map_zero η).symm))
    have hα : HasDerivAt (fun s : ℝ => (c s).1) (deriv c t).1 t := by
      simpa only [ContinuousLinearMap.coe_fst', Function.comp_def] using
        (ContinuousLinearMap.fst ℝ E F).hasFDerivAt.comp_hasDerivAt t hct
    have hβ : HasDerivAt (fun s : ℝ => (c s).2) (deriv c t).2 t := by
      simpa only [ContinuousLinearMap.coe_snd', Function.comp_def] using
        (ContinuousLinearMap.snd ℝ E F).hasFDerivAt.comp_hasDerivAt t hct
    have hctp := heAB (hcW t ht).1
    have hfd := ((hf.contDiffAt (hA.mem_nhds (hA₀A hctp.1))).differentiableAt
      (by simp)).hasFDerivAt.comp_hasDerivAt t hα
    have hgd := ((hg.contDiffAt (hB.mem_nhds (hB₀B hctp.2))).differentiableAt
      (by simp)).hasFDerivAt.comp_hasDerivAt t hβ
    have hnear : (fun s => g (c s).2) =ᶠ[𝓝 t] fun s => f (c s).1 := by
      filter_upwards [isOpen_Ioo.mem_nhds ht] with s hs
      exact (hcfiber s hs).symm
    have hvel := (hfd.congr_of_eventuallyEq hnear).unique hgd
    constructor
    · rw [hα.deriv]
      intro hz
      have hz₂ : (deriv c t).2 = 0 := (hiB₀ _ hctp.2) (by
        simpa only [hz, map_zero] using hvel.symm)
      exact hcne (Prod.ext hz hz₂)
    · rw [hβ.deriv]
      intro hz
      have hz₁ : (deriv c t).1 = 0 := (hiA₀ _ hctp.1) (by
        simpa only [hz, map_zero] using hvel)
      exact hcne (Prod.ext hz₁ hz)

end DifferentialGeometry.Analysis
