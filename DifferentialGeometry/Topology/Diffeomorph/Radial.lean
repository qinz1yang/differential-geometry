import Mathlib.Analysis.SpecialFunctions.SmoothTransition
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.Calculus.ImplicitContDiff
import Mathlib.Topology.Order.IntermediateValue
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import DifferentialGeometry.Topology.Diffeomorph.Extension
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Topology.Order.Compact
import Mathlib.Analysis.Normed.Module.Ball.RadialEquiv
import Mathlib.Geometry.Manifold.Instances.Sphere
import Mathlib.Geometry.Manifold.Diffeomorph

open scoped ContDiff Manifold Topology

namespace Diffeomorph

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  {d : ℕ} [Fact (Module.finrank ℝ E = d + 1)]

noncomputable def unitSphereProd (n : ℕ∞ω) :
    let U : TopologicalSpace.Opens E := ⟨{0}ᶜ, isOpen_compl_singleton⟩
    let V : TopologicalSpace.Opens ℝ := ⟨Set.Ioi 0, isOpen_Ioi⟩
    Diffeomorph 𝓘(ℝ, E) ((𝓡 d).prod 𝓘(ℝ, ℝ)) U
      (Metric.sphere (0 : E) 1 × V) n := by
  let U : TopologicalSpace.Opens E := ⟨{0}ᶜ, isOpen_compl_singleton⟩
  let V : TopologicalSpace.Opens ℝ := ⟨Set.Ioi 0, isOpen_Ioi⟩
  let _ : ChartedSpace E ({0}ᶜ : Set E) := inferInstanceAs (ChartedSpace E U)
  let _ : ChartedSpace ℝ (Set.Ioi (0 : ℝ)) := inferInstanceAs (ChartedSpace ℝ V)
  let h : U ≃ₜ (Metric.sphere (0 : E) 1 × V) := homeomorphUnitSphereProd E
  have hv : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, E) n (Subtype.val : U → E) :=
    contMDiff_subtype_val
  have hn : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) n (fun x : U => ‖x.val‖) := by
    intro x
    apply contMDiffAt_subtype_iff.mpr
    exact (contDiffAt_norm ℝ (show x.val ≠ 0 from x.property)).contMDiffAt
  have hn0 : ∀ x : U, ‖x.val‖ ≠ 0 := fun x => norm_ne_zero_iff.mpr x.property
  refine { toEquiv := h.toEquiv, contMDiff_toFun := ?_, contMDiff_invFun := ?_ }
  · have hs : ContMDiff 𝓘(ℝ, E) (𝓡 d) n (fun x : U => (h x).1) := by
      have hs' : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, E) n
          (fun x : U => ((h x).1 : E)) := by
        apply ((hn.inv₀ hn0).smul hv).congr
        intro x
        exact homeomorphUnitSphereProd_apply_fst_coe E x
      exact hs'.codRestrict_sphere (fun x => (h x).1.property)
    have hr : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) n (fun x : U => (h x).2) := by
      have hr' : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) n (fun x : U => ((h x).2 : ℝ)) := by
        apply hn.congr
        intro x
        exact homeomorphUnitSphereProd_apply_snd_coe E x
      intro x
      exact (ChartedSpace.liftPropWithinAt_subtypeVal_comp_iff
        (P := ContDiffWithinAtProp 𝓘(ℝ, E) 𝓘(ℝ, ℝ) n) (U := V)
        (fun x : U => (h x).2) Set.univ x).mp (hr' x)
    exact hs.prodMk hr
  · have hi : ContMDiff ((𝓡 d).prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, E) n
        (fun p : Metric.sphere (0 : E) 1 × V => (h.symm p).val) :=
      (contMDiff_subtype_val.comp contMDiff_snd).smul
        (contMDiff_coe_sphere.comp contMDiff_fst)
    intro p
    exact (ChartedSpace.liftPropWithinAt_subtypeVal_comp_iff
      (P := ContDiffWithinAtProp ((𝓡 d).prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, E) n) (U := U)
      (h.symm : Metric.sphere (0 : E) 1 × V → U) Set.univ p).mp (hi p)

@[simp] theorem unitSphereProd_toHomeomorph (n : ℕ∞ω) :
    (unitSphereProd (E := E) (d := d) n).toHomeomorph = homeomorphUnitSphereProd E := rfl

@[simp] theorem unitSphereProd_apply_fst_val (n : ℕ∞ω) (x : ({0}ᶜ : Set E)) :
    ((unitSphereProd (E := E) (d := d) n x).1 : E) = ‖x.val‖⁻¹ • x.val := by
  exact homeomorphUnitSphereProd_apply_fst_coe E x

@[simp] theorem unitSphereProd_apply_snd_val (n : ℕ∞ω) (x : ({0}ᶜ : Set E)) :
    ((unitSphereProd (E := E) (d := d) n x).2 : ℝ) = ‖x.val‖ := by
  exact homeomorphUnitSphereProd_apply_snd_coe E x

@[simp] theorem unitSphereProd_symm_apply_val (n : ℕ∞ω)
    (p : Metric.sphere (0 : E) 1 × Set.Ioi (0 : ℝ)) :
    ((unitSphereProd (E := E) (d := d) n).symm p : E) = p.2.val • p.1.val := rfl

end Diffeomorph

namespace Real

private noncomputable def scalarRadial (c a r : ℝ) : ℝ :=
  c * r + (a - c) * smoothTransition (2 * r - 1 / 2)

private noncomputable def scalarRadialDeriv (c a r : ℝ) : ℝ :=
  c + (a - c) * (deriv smoothTransition (2 * r - 1 / 2) * 2)

private theorem scalarRadial_contDiff :
    ContDiff ℝ ∞ (fun z : (ℝ × ℝ) × ℝ => scalarRadial z.1.1 z.1.2 z.2) :=
  (contDiff_fst.fst.mul contDiff_snd).add
    ((contDiff_fst.snd.sub contDiff_fst.fst).mul
      (smoothTransition.contDiff.comp
        ((contDiff_const.mul contDiff_snd).sub contDiff_const)))

private theorem scalarRadial_contDiff_right (c a : ℝ) : ContDiff ℝ ∞ (scalarRadial c a) :=
  scalarRadial_contDiff.comp ((contDiff_const (c := (c, a))).prodMk contDiff_id)

private theorem scalarRadial_hasDerivAt (c a r : ℝ) :
    HasDerivAt (scalarRadial c a) (scalarRadialDeriv c a r) r := by
  have hσsmooth : ContDiff ℝ ∞ smoothTransition := smoothTransition.contDiff
  have hσ : HasDerivAt (fun r : ℝ => smoothTransition (2 * r - 1 / 2))
      (deriv smoothTransition (2 * r - 1 / 2) * 2) r := by
    simpa only [Function.comp_def, id_eq, mul_one] using
      (hσsmooth.differentiable (by simp) (2 * r - 1 / 2)).hasDerivAt.comp r
      (((hasDerivAt_id r).const_mul 2).sub_const (1 / 2))
  convert! ((hasDerivAt_id r).const_mul c).add (hσ.const_mul (a - c)) using 1
  simp only [scalarRadialDeriv, mul_one]

private theorem scalarRadialDeriv_le {c a : ℝ} (hca : c ≤ a) (r : ℝ) :
    c ≤ scalarRadialDeriv c a r := by
  have hσ : 0 ≤ deriv smoothTransition (2 * r - 1 / 2) :=
    smoothTransition.monotone.deriv_nonneg
  exact le_add_of_nonneg_right (mul_nonneg (sub_nonneg.mpr hca) (mul_nonneg hσ (by norm_num)))

private theorem scalarRadial_strictMono {c a : ℝ} (hc : 0 < c) (hca : c ≤ a) :
    StrictMono (scalarRadial c a) :=
  strictMono_of_hasDerivAt_pos (scalarRadial_hasDerivAt c a)
    (fun r => hc.trans_le (scalarRadialDeriv_le hca r))

private theorem scalarRadial_eq_mul_of_le (c a : ℝ) {r : ℝ} (hr : r ≤ 1 / 4) :
    scalarRadial c a r = c * r := by
  rw [scalarRadial, smoothTransition.zero_of_nonpos (by linarith), mul_zero, add_zero]

private theorem scalarRadial_eq_mul_add_of_le (c a : ℝ) {r : ℝ} (hr : 3 / 4 ≤ r) :
    scalarRadial c a r = c * r + a - c := by
  rw [scalarRadial, smoothTransition.one_of_one_le (by linarith), mul_one]
  ring

private theorem scalarRadial_zero (c a : ℝ) : scalarRadial c a 0 = 0 := by
  rw [scalarRadial_eq_mul_of_le c a (by norm_num), mul_zero]

private theorem scalarRadial_one (c a : ℝ) : scalarRadial c a 1 = a := by
  rw [scalarRadial_eq_mul_add_of_le c a (by norm_num)]
  ring

private theorem scalarRadial_surjective {c : ℝ} (hc : 0 < c) (a : ℝ) :
    Function.Surjective (scalarRadial c a) := by
  intro s
  let l : ℝ := min (s / c) (1 / 4)
  let u : ℝ := max ((s - a + c) / c) (3 / 4)
  have hl : scalarRadial c a l ≤ s := by
    rw [scalarRadial_eq_mul_of_le c a (min_le_right _ _)]
    calc
      c * l ≤ c * (s / c) := mul_le_mul_of_nonneg_left (min_le_left _ _) hc.le
      _ = s := by field_simp [hc.ne']
  have hu : s ≤ scalarRadial c a u := by
    rw [scalarRadial_eq_mul_add_of_le c a (le_max_right _ _)]
    have hmul : c * ((s - a + c) / c) ≤ c * u :=
      mul_le_mul_of_nonneg_left (le_max_left _ _) hc.le
    have heq : c * ((s - a + c) / c) = s - a + c := by field_simp [hc.ne']
    linarith
  obtain ⟨r, -, hr⟩ := (scalarRadial_contDiff_right c a).continuous.continuousOn.surjOn_Icc
    (s := Set.univ) (a := l) (b := u) (Set.mem_univ _) (Set.mem_univ _) ⟨hl, hu⟩
  exact ⟨r, hr⟩

private noncomputable def scalarRadialInverse (c a : ℝ) : ℝ → ℝ :=
  Function.invFun (scalarRadial c a)

private theorem scalarRadial_apply_inverse {c a : ℝ} (hc : 0 < c) (s : ℝ) :
    scalarRadial c a (scalarRadialInverse c a s) = s :=
  Function.rightInverse_invFun (scalarRadial_surjective hc a) s

private theorem scalarRadial_inverse_apply {c a : ℝ} (hc : 0 < c) (hca : c ≤ a) (r : ℝ) :
    scalarRadialInverse c a (scalarRadial c a r) = r :=
  Function.leftInverse_invFun (scalarRadial_strictMono hc hca).injective r

private theorem scalarRadialInverse_contDiffAt {z : (ℝ × ℝ) × ℝ}
    (hc : 0 < z.1.1) (hca : z.1.1 < z.1.2) :
    ContDiffAt ℝ ∞ (fun w : (ℝ × ℝ) × ℝ => scalarRadialInverse w.1.1 w.1.2 w.2) z := by
  let x : ℝ := scalarRadialInverse z.1.1 z.1.2 z.2
  let F : ((ℝ × ℝ) × ℝ) × ℝ → ℝ :=
    fun w => scalarRadial w.1.1.1 w.1.1.2 w.2 - w.1.2
  have hF : ContDiff ℝ ∞ F :=
    (scalarRadial_contDiff.comp (contDiff_fst.fst.prodMk contDiff_snd)).sub contDiff_fst.snd
  have hFx : F (z, x) = 0 := by
    exact sub_eq_zero.mpr (scalarRadial_apply_inverse hc z.2)
  let d : ℝ := scalarRadialDeriv z.1.1 z.1.2 x
  have hd : 0 < d := hc.trans_le (scalarRadialDeriv_le hca.le x)
  have hpartial : fderiv ℝ F (z, x) ∘L ContinuousLinearMap.inr ℝ ((ℝ × ℝ) × ℝ) ℝ =
      ContinuousLinearMap.toSpanSingleton ℝ d := by
    have hrestrict := ((hF.differentiable (by simp)) (z, x)).hasFDerivAt.comp x
      (hasFDerivAt_prodMk_right (𝕜 := ℝ) z x)
    exact hrestrict.unique
      ((scalarRadial_hasDerivAt z.1.1 z.1.2 x).sub_const z.2).hasFDerivAt
  have hi : (fderiv ℝ F (z, x) ∘L
      ContinuousLinearMap.inr ℝ ((ℝ × ℝ) × ℝ) ℝ).IsInvertible := by
    rw [hpartial]
    refine ⟨ContinuousLinearEquiv.unitsEquivAut ℝ (Units.mk0 d hd.ne'), ?_⟩
    ext
    simp
  let ψ : (ℝ × ℝ) × ℝ → ℝ := hF.contDiffAt.implicitFunction (by simp) hi
  have hψ : ContDiffAt ℝ ∞ ψ z := hF.contDiffAt.contDiffAt_implicitFunction (by simp) hi
  have hdom : {w : (ℝ × ℝ) × ℝ | 0 < w.1.1 ∧ w.1.1 < w.1.2} ∈ nhds z :=
    ((isOpen_lt continuous_const continuous_fst.fst).inter
      (isOpen_lt continuous_fst.fst continuous_fst.snd)).mem_nhds ⟨hc, hca⟩
  apply hψ.congr_of_eventuallyEq
  filter_upwards [hF.contDiffAt.eventually_apply_implicitFunction (by simp) hi, hdom]
    with w hw hwdom
  apply (scalarRadial_strictMono hwdom.1 hwdom.2.le).injective
  rw [scalarRadial_apply_inverse hwdom.1]
  exact (sub_eq_zero.mp (hw.trans hFx)).symm

private theorem scalarRadialInverse_pos_iff {c a s : ℝ} (hc : 0 < c) (hca : c ≤ a) :
    0 < scalarRadialInverse c a s ↔ 0 < s := by
  rw [← (scalarRadial_strictMono hc hca).lt_iff_lt,
    scalarRadial_zero, scalarRadial_apply_inverse hc]

end Real

namespace Diffeomorph

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  {d : ℕ} [Fact (Module.finrank ℝ E = d + 1)]

private noncomputable def radialSphereProdEquiv
    (R : Metric.sphere (0 : E) 1 → ℝ) (hR : ∀ θ, 1 < R θ) :
    (Metric.sphere (0 : E) 1 × Set.Ioi (0 : ℝ)) ≃
      (Metric.sphere (0 : E) 1 × Set.Ioi (0 : ℝ)) where
  toFun p := (p.1, ⟨Real.scalarRadial 1 (R p.1) p.2, by
    change 0 < Real.scalarRadial 1 (R p.1) p.2
    simpa only [Real.scalarRadial_zero] using
      Real.scalarRadial_strictMono zero_lt_one (hR p.1).le p.2.property⟩)
  invFun p := (p.1, ⟨Real.scalarRadialInverse 1 (R p.1) p.2,
    (Real.scalarRadialInverse_pos_iff zero_lt_one (hR p.1).le).mpr p.2.property⟩)
  left_inv p := by
    apply Prod.ext
    · rfl
    · apply Subtype.ext
      exact Real.scalarRadial_inverse_apply zero_lt_one (hR p.1).le p.2
  right_inv p := by
    apply Prod.ext
    · rfl
    · apply Subtype.ext
      exact Real.scalarRadial_apply_inverse zero_lt_one p.2

private noncomputable def radialSphereProd
    (R : Metric.sphere (0 : E) 1 → ℝ)
    (hR : ContMDiff (𝓡 d) 𝓘(ℝ, ℝ) ∞ R) (hR1 : ∀ θ, 1 < R θ) :
    let V : TopologicalSpace.Opens ℝ := ⟨Set.Ioi 0, isOpen_Ioi⟩
    Diffeomorph ((𝓡 d).prod 𝓘(ℝ, ℝ)) ((𝓡 d).prod 𝓘(ℝ, ℝ))
      (Metric.sphere (0 : E) 1 × V) (Metric.sphere (0 : E) 1 × V) ∞ := by
  let V : TopologicalSpace.Opens ℝ := ⟨Set.Ioi 0, isOpen_Ioi⟩
  let _ : ChartedSpace ℝ (Set.Ioi (0 : ℝ)) := inferInstanceAs (ChartedSpace ℝ V)
  let e := radialSphereProdEquiv R hR1
  have hdata : ContMDiff ((𝓡 d).prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, (ℝ × ℝ) × ℝ) ∞
      (fun p : Metric.sphere (0 : E) 1 × V => (((1 : ℝ), R p.1), (p.2 : ℝ))) := by
    refine (contMDiff_prod_module_iff _).mpr
      ⟨?_, contMDiff_subtype_val.comp contMDiff_snd⟩
    exact (contMDiff_prod_module_iff _).mpr ⟨contMDiff_const, hR.comp contMDiff_fst⟩
  refine { toEquiv := e, contMDiff_toFun := ?_, contMDiff_invFun := ?_ }
  · have hscalar : ContMDiff ((𝓡 d).prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, ℝ) ∞
        (fun p : Metric.sphere (0 : E) 1 × V => ((e p).2 : ℝ)) :=
      Real.scalarRadial_contDiff.comp_contMDiff hdata
    have htarget : ContMDiff ((𝓡 d).prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, ℝ) ∞
        (fun p : Metric.sphere (0 : E) 1 × V => (e p).2) := by
      intro p
      exact (ChartedSpace.liftPropWithinAt_subtypeVal_comp_iff
        (P := ContDiffWithinAtProp ((𝓡 d).prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, ℝ) ∞) (U := V)
        (fun p => (e p).2) Set.univ p).mp (hscalar p)
    exact contMDiff_fst.prodMk htarget
  · have hscalar : ContMDiff ((𝓡 d).prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, ℝ) ∞
        (fun p : Metric.sphere (0 : E) 1 × V => ((e.symm p).2 : ℝ)) := by
      intro p
      exact (Real.scalarRadialInverse_contDiffAt
        (z := ((1, R p.1), (p.2 : ℝ))) zero_lt_one (hR1 p.1)).comp_contMDiffAt
        (f := fun q : Metric.sphere (0 : E) 1 × V => (((1 : ℝ), R q.1), (q.2 : ℝ)))
        (x := p) (hdata p)
    have htarget : ContMDiff ((𝓡 d).prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, ℝ) ∞
        (fun p : Metric.sphere (0 : E) 1 × V => (e.symm p).2) := by
      intro p
      exact (ChartedSpace.liftPropWithinAt_subtypeVal_comp_iff
        (P := ContDiffWithinAtProp ((𝓡 d).prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, ℝ) ∞) (U := V)
        (fun p => (e.symm p).2) Set.univ p).mp (hscalar p)
    exact contMDiff_fst.prodMk htarget

private theorem radialSphereProd_apply_fst
    (R : Metric.sphere (0 : E) 1 → ℝ)
    (hR : ContMDiff (𝓡 d) 𝓘(ℝ, ℝ) ∞ R) (hR1 : ∀ θ, 1 < R θ)
    (p : Metric.sphere (0 : E) 1 × Set.Ioi (0 : ℝ)) :
    (radialSphereProd R hR hR1 p).1 = p.1 := rfl

private theorem radialSphereProd_apply_snd
    (R : Metric.sphere (0 : E) 1 → ℝ)
    (hR : ContMDiff (𝓡 d) 𝓘(ℝ, ℝ) ∞ R) (hR1 : ∀ θ, 1 < R θ)
    (p : Metric.sphere (0 : E) 1 × Set.Ioi (0 : ℝ)) :
    ((radialSphereProd R hR hR1 p).2 : ℝ) = Real.scalarRadial 1 (R p.1) p.2 := rfl

private noncomputable def puncturedRadial
    (R : Metric.sphere (0 : E) 1 → ℝ)
    (hR : ContMDiff (𝓡 d) 𝓘(ℝ, ℝ) ∞ R) (hR1 : ∀ θ, 1 < R θ) :
    let U : TopologicalSpace.Opens E := ⟨{0}ᶜ, isOpen_compl_singleton⟩
    Diffeomorph 𝓘(ℝ, E) 𝓘(ℝ, E) U U ∞ :=
  ((unitSphereProd (E := E) (d := d) ∞).trans (radialSphereProd R hR hR1)).trans
    (unitSphereProd (E := E) (d := d) ∞).symm

private theorem puncturedRadial_apply
    (R : Metric.sphere (0 : E) 1 → ℝ)
    (hR : ContMDiff (𝓡 d) 𝓘(ℝ, ℝ) ∞ R) (hR1 : ∀ θ, 1 < R θ)
    (x : ({0}ᶜ : Set E)) :
    (puncturedRadial R hR hR1 x : E) =
      Real.scalarRadial 1 (R ((unitSphereProd (E := E) (d := d) ∞ x).1)) ‖(x : E)‖ •
        (‖(x : E)‖⁻¹ • (x : E)) := by
  change (((unitSphereProd (E := E) (d := d) ∞).symm
    (radialSphereProd R hR hR1 (unitSphereProd (E := E) (d := d) ∞ x))) : E) = _
  simp only [unitSphereProd_symm_apply_val, radialSphereProd_apply_fst,
    radialSphereProd_apply_snd, unitSphereProd_apply_fst_val, unitSphereProd_apply_snd_val]

private theorem puncturedRadial_apply_of_norm_le
    (R : Metric.sphere (0 : E) 1 → ℝ)
    (hR : ContMDiff (𝓡 d) 𝓘(ℝ, ℝ) ∞ R) (hR1 : ∀ θ, 1 < R θ)
    (x : ({0}ᶜ : Set E)) (hx : ‖(x : E)‖ ≤ 1 / 4) :
    puncturedRadial R hR hR1 x = x := by
  apply Subtype.ext
  rw [puncturedRadial_apply, Real.scalarRadial_eq_mul_of_le 1 _ hx, one_mul]
  exact smul_inv_smul₀ (norm_ne_zero_iff.mpr x.property) (x : E)

end Diffeomorph

namespace Diffeomorph

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  {d : ℕ} [Fact (Module.finrank ℝ E = d + 1)]

omit [InnerProductSpace ℝ E] in
private theorem radial_support_subset :
    {x : E | 1 / 4 ≤ ‖x‖} ⊆ ({0}ᶜ : Set E) := by
  intro x hx
  change x ≠ 0
  intro h
  norm_num [h] at hx

private noncomputable def normalizedRadial
    (R : Metric.sphere (0 : E) 1 → ℝ)
    (hR : ContMDiff (𝓡 d) 𝓘(ℝ, ℝ) ∞ R) (hR1 : ∀ θ, 1 < R θ) :
    E ≃ₘ[ℝ] E :=
  (puncturedRadial R hR hR1).extend (C := {x : E | 1 / 4 ≤ ‖x‖})
    (isClosed_le continuous_const continuous_norm) radial_support_subset
    (fun x hx => puncturedRadial_apply_of_norm_le R hR hR1 x
      (le_of_lt (lt_of_not_ge hx)))

private theorem normalizedRadial_apply
    (R : Metric.sphere (0 : E) 1 → ℝ)
    (hR : ContMDiff (𝓡 d) 𝓘(ℝ, ℝ) ∞ R) (hR1 : ∀ θ, 1 < R θ)
    (x : ({0}ᶜ : Set E)) :
    normalizedRadial R hR hR1 x = (puncturedRadial R hR hR1 x : E) := by
  exact extend_apply (C := {y : E | 1 / 4 ≤ ‖y‖}) (puncturedRadial R hR hR1)
    (isClosed_le continuous_const continuous_norm) radial_support_subset
    (fun y hy => puncturedRadial_apply_of_norm_le R hR hR1 y
      (le_of_lt (lt_of_not_ge hy))) x

private theorem normalizedRadial_zero
    (R : Metric.sphere (0 : E) 1 → ℝ)
    (hR : ContMDiff (𝓡 d) 𝓘(ℝ, ℝ) ∞ R) (hR1 : ∀ θ, 1 < R θ) :
    normalizedRadial R hR hR1 0 = 0 := by
  exact extend_apply_of_notMem (C := {y : E | 1 / 4 ≤ ‖y‖})
    (puncturedRadial R hR hR1) (isClosed_le continuous_const continuous_norm)
    radial_support_subset (fun y hy => puncturedRadial_apply_of_norm_le R hR hR1 y
      (le_of_lt (lt_of_not_ge hy))) (by
        change ¬1 / 4 ≤ ‖(0 : E)‖
        norm_num)

private theorem normalizedRadial_apply_of_norm_le
    (R : Metric.sphere (0 : E) 1 → ℝ)
    (hR : ContMDiff (𝓡 d) 𝓘(ℝ, ℝ) ∞ R) (hR1 : ∀ θ, 1 < R θ)
    (x : E) (hx : ‖x‖ ≤ 1 / 4) : normalizedRadial R hR hR1 x = x := by
  by_cases hx0 : x = 0
  · simpa only [hx0] using normalizedRadial_zero R hR hR1
  · exact (normalizedRadial_apply R hR hR1 ⟨x, hx0⟩).trans
      (congrArg Subtype.val (puncturedRadial_apply_of_norm_le R hR hR1 ⟨x, hx0⟩ hx))

private noncomputable def ambientRadial
    (R : Metric.sphere (0 : E) 1 → ℝ)
    (hR : ContMDiff (𝓡 d) 𝓘(ℝ, ℝ) ∞ R)
    (c : ℝ) (hc : 0 < c) (hRc : ∀ θ, c < R θ) : E ≃ₘ[ℝ] E :=
  (normalizedRadial (fun θ => R θ / c) ((contDiff_id.div_const c).comp_contMDiff hR)
    (fun θ => (lt_div_iff₀ hc).mpr (by simpa only [one_mul] using hRc θ))).trans
    (ContinuousLinearEquiv.smulLeft (R₁ := ℝ) (M₁ := E) (Units.mk0 c hc.ne')).toDiffeomorph

private theorem ambientRadial_zero
    (R : Metric.sphere (0 : E) 1 → ℝ)
    (hR : ContMDiff (𝓡 d) 𝓘(ℝ, ℝ) ∞ R)
    (c : ℝ) (hc : 0 < c) (hRc : ∀ θ, c < R θ) :
    ambientRadial R hR c hc hRc 0 = 0 := by
  simp only [ambientRadial, coe_trans, Function.comp_apply, normalizedRadial_zero,
    ContinuousLinearEquiv.coe_toDiffeomorph, map_zero]

private theorem ambientRadial_symm_zero
    (R : Metric.sphere (0 : E) 1 → ℝ)
    (hR : ContMDiff (𝓡 d) 𝓘(ℝ, ℝ) ∞ R)
    (c : ℝ) (hc : 0 < c) (hRc : ∀ θ, c < R θ) :
    (ambientRadial R hR c hc hRc).symm 0 = 0 := by
  apply (ambientRadial R hR c hc hRc).injective
  change ambientRadial R hR c hc hRc ((ambientRadial R hR c hc hRc).symm 0) =
    ambientRadial R hR c hc hRc 0
  rw [apply_symm_apply, ambientRadial_zero]

private theorem ambientRadial_apply_of_norm_le
    (R : Metric.sphere (0 : E) 1 → ℝ)
    (hR : ContMDiff (𝓡 d) 𝓘(ℝ, ℝ) ∞ R)
    (c : ℝ) (hc : 0 < c) (hRc : ∀ θ, c < R θ)
    (x : E) (hx : ‖x‖ ≤ 1 / 4) : ambientRadial R hR c hc hRc x = c • x := by
  simp only [ambientRadial, coe_trans, Function.comp_apply,
    normalizedRadial_apply_of_norm_le _ _ _ x hx]
  rfl

private theorem scalar_radial_rescale {c : ℝ} (hc : c ≠ 0) (a r : ℝ) :
    c * Real.scalarRadial 1 (a / c) r = Real.scalarRadial c a r := by
  have hcancel : c * (a / c) = a := by field_simp [hc]
  change c * (1 * r + (a / c - 1) * Real.smoothTransition (2 * r - 1 / 2)) =
    c * r + (a - c) * Real.smoothTransition (2 * r - 1 / 2)
  calc
    _ = c * r + (c * (a / c) - c) * Real.smoothTransition (2 * r - 1 / 2) := by ring
    _ = _ := by rw [hcancel]

private theorem normalizedRadial_apply_ray
    (R : Metric.sphere (0 : E) 1 → ℝ)
    (hR : ContMDiff (𝓡 d) 𝓘(ℝ, ℝ) ∞ R) (hR1 : ∀ θ, 1 < R θ)
    (θ : Metric.sphere (0 : E) 1) (r : ℝ) (hr : 0 < r) :
    normalizedRadial R hR hR1 (r • (θ : E)) =
      Real.scalarRadial 1 (R θ) r • (θ : E) := by
  have hx : (((unitSphereProd (E := E) (d := d) ∞).symm (θ, ⟨r, hr⟩)) : E) =
      r • (θ : E) := rfl
  rw [← hx, normalizedRadial_apply]
  simp only [puncturedRadial, coe_trans, Function.comp_apply, apply_symm_apply,
    unitSphereProd_symm_apply_val, radialSphereProd_apply_fst, radialSphereProd_apply_snd]

private theorem ambientRadial_apply_ray
    (R : Metric.sphere (0 : E) 1 → ℝ)
    (hR : ContMDiff (𝓡 d) 𝓘(ℝ, ℝ) ∞ R)
    (c : ℝ) (hc : 0 < c) (hRc : ∀ θ, c < R θ)
    (θ : Metric.sphere (0 : E) 1) (r : ℝ) (hr : 0 ≤ r) :
    ambientRadial R hR c hc hRc (r • (θ : E)) =
      Real.scalarRadial c (R θ) r • (θ : E) := by
  rcases hr.eq_or_lt with rfl | hr
  · simp only [zero_smul, ambientRadial_zero, Real.scalarRadial_zero]
  · change c • normalizedRadial _ _ _ (r • (θ : E)) = _
    rw [normalizedRadial_apply_ray _ _ _ θ r hr, smul_smul, scalar_radial_rescale hc.ne']

private theorem ambientRadial_symm_apply_ray
    (R : Metric.sphere (0 : E) 1 → ℝ)
    (hR : ContMDiff (𝓡 d) 𝓘(ℝ, ℝ) ∞ R)
    (c : ℝ) (hc : 0 < c) (hRc : ∀ θ, c < R θ)
    (θ : Metric.sphere (0 : E) 1) (s : ℝ) (hs : 0 ≤ s) :
    (ambientRadial R hR c hc hRc).symm (s • (θ : E)) =
      Real.scalarRadialInverse c (R θ) s • (θ : E) := by
  have hψ : 0 ≤ Real.scalarRadialInverse c (R θ) s := by
    apply (Real.scalarRadial_strictMono hc (hRc θ).le).le_iff_le.mp
    simpa only [Real.scalarRadial_zero, Real.scalarRadial_apply_inverse hc] using hs
  apply (ambientRadial R hR c hc hRc).injective
  change ambientRadial R hR c hc hRc ((ambientRadial R hR c hc hRc).symm (s • (θ : E))) =
    ambientRadial R hR c hc hRc (Real.scalarRadialInverse c (R θ) s • (θ : E))
  rw [apply_symm_apply, ambientRadial_apply_ray R hR c hc hRc θ _ hψ,
    Real.scalarRadial_apply_inverse hc]

private theorem ambientRadial_symm_apply_of_norm_le
    (R : Metric.sphere (0 : E) 1 → ℝ)
    (hR : ContMDiff (𝓡 d) 𝓘(ℝ, ℝ) ∞ R)
    (c : ℝ) (hc : 0 < c) (hRc : ∀ θ, c < R θ)
    (x : E) (hx : ‖x‖ ≤ c / 4) :
    (ambientRadial R hR c hc hRc).symm x = c⁻¹ • x := by
  have hsmall : ‖c⁻¹ • x‖ ≤ 1 / 4 := by
    calc
      ‖c⁻¹ • x‖ = ‖x‖ / c := by
        rw [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hc), div_eq_inv_mul]
      _ ≤ 1 / 4 := (div_le_iff₀ hc).mpr (by linarith)
  apply (ambientRadial R hR c hc hRc).injective
  change ambientRadial R hR c hc hRc ((ambientRadial R hR c hc hRc).symm x) =
    ambientRadial R hR c hc hRc (c⁻¹ • x)
  rw [apply_symm_apply, ambientRadial_apply_of_norm_le R hR c hc hRc _ hsmall]
  exact (smul_inv_smul₀ hc.ne' x).symm

end Diffeomorph

namespace Diffeomorph

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  {d : ℕ} [Fact (Module.finrank ℝ E = d + 1)]

private theorem ambientRadial_image_sphere
    (R : Metric.sphere (0 : E) 1 → ℝ)
    (hR : ContMDiff (𝓡 d) 𝓘(ℝ, ℝ) ∞ R)
    (c : ℝ) (hc : 0 < c) (hRc : ∀ θ, c < R θ) :
    ambientRadial R hR c hc hRc '' Metric.sphere (0 : E) 1 =
      Set.range (fun θ : Metric.sphere (0 : E) 1 => R θ • (θ : E)) := by
  ext z
  constructor
  · rintro ⟨x, hx, rfl⟩
    refine ⟨⟨x, hx⟩, ?_⟩
    simpa only [one_smul, Real.scalarRadial_one] using
      (ambientRadial_apply_ray R hR c hc hRc ⟨x, hx⟩ 1 zero_le_one).symm
  · rintro ⟨θ, rfl⟩
    refine ⟨θ, θ.property, ?_⟩
    simpa only [one_smul, Real.scalarRadial_one] using
      ambientRadial_apply_ray R hR c hc hRc θ 1 zero_le_one

private theorem ambientRadial_image_closedBall
    (R : Metric.sphere (0 : E) 1 → ℝ)
    (hR : ContMDiff (𝓡 d) 𝓘(ℝ, ℝ) ∞ R)
    (c : ℝ) (hc : 0 < c) (hRc : ∀ θ, c < R θ) :
    ambientRadial R hR c hc hRc '' Metric.closedBall (0 : E) 1 =
      {z | z = 0 ∨ ∃ θ : Metric.sphere (0 : E) 1, ∃ s : ℝ,
        0 < s ∧ s ≤ R θ ∧ z = s • (θ : E)} := by
  ext z
  constructor
  · rintro ⟨x, hx, rfl⟩
    by_cases hx0 : x = 0
    · exact Or.inl (by simpa only [hx0] using ambientRadial_zero R hR c hc hRc)
    · let p := unitSphereProd (E := E) (d := d) ∞ (⟨x, hx0⟩ : ({0}ᶜ : Set E))
      have hp : (p.2 : ℝ) • (p.1 : E) = x :=
        congrArg Subtype.val ((unitSphereProd (E := E) (d := d) ∞).symm_apply_apply ⟨x, hx0⟩)
      have hbound : (p.2 : ℝ) ≤ 1 := by
        simpa only [p, unitSphereProd_apply_snd_val, mem_closedBall_zero_iff] using hx
      have hpos : 0 < Real.scalarRadial c (R p.1) p.2 := by
        simpa only [Real.scalarRadial_zero] using
          Real.scalarRadial_strictMono hc (hRc p.1).le p.2.property
      have htop : Real.scalarRadial c (R p.1) p.2 ≤ R p.1 := by
        simpa only [Real.scalarRadial_one] using
          (Real.scalarRadial_strictMono hc (hRc p.1).le).monotone hbound
      refine Or.inr ⟨p.1, Real.scalarRadial c (R p.1) p.2, hpos, htop, ?_⟩
      rw [← hp]
      exact ambientRadial_apply_ray R hR c hc hRc p.1 p.2 p.2.property.le
  · rintro (rfl | ⟨θ, s, hs, htop, rfl⟩)
    · exact ⟨0, by simp, ambientRadial_zero R hR c hc hRc⟩
    · let r := Real.scalarRadialInverse c (R θ) s
      have hr : 0 < r := (Real.scalarRadialInverse_pos_iff hc (hRc θ).le).mpr hs
      have hbound : r ≤ 1 := by
        apply (Real.scalarRadial_strictMono hc (hRc θ).le).le_iff_le.mp
        simpa only [r, Real.scalarRadial_apply_inverse hc, Real.scalarRadial_one] using htop
      refine ⟨r • (θ : E), ?_, ?_⟩
      · rw [mem_closedBall_zero_iff, norm_smul, Real.norm_eq_abs, abs_of_pos hr]
        simpa only [mem_sphere_zero_iff_norm.mp θ.property, mul_one] using hbound
      · rw [ambientRadial_apply_ray R hR c hc hRc θ r hr.le,
          Real.scalarRadial_apply_inverse hc]

private theorem ambientRadial_image_ball
    (R : Metric.sphere (0 : E) 1 → ℝ)
    (hR : ContMDiff (𝓡 d) 𝓘(ℝ, ℝ) ∞ R)
    (c : ℝ) (hc : 0 < c) (hRc : ∀ θ, c < R θ) :
    ambientRadial R hR c hc hRc '' Metric.ball (0 : E) 1 =
      {z | z = 0 ∨ ∃ θ : Metric.sphere (0 : E) 1, ∃ s : ℝ,
        0 < s ∧ s < R θ ∧ z = s • (θ : E)} := by
  ext z
  constructor
  · rintro ⟨x, hx, rfl⟩
    by_cases hx0 : x = 0
    · exact Or.inl (by simpa only [hx0] using ambientRadial_zero R hR c hc hRc)
    · let p := unitSphereProd (E := E) (d := d) ∞ (⟨x, hx0⟩ : ({0}ᶜ : Set E))
      have hp : (p.2 : ℝ) • (p.1 : E) = x :=
        congrArg Subtype.val ((unitSphereProd (E := E) (d := d) ∞).symm_apply_apply ⟨x, hx0⟩)
      have hbound : (p.2 : ℝ) < 1 := by
        simpa only [p, unitSphereProd_apply_snd_val, mem_ball_zero_iff] using hx
      have hpos : 0 < Real.scalarRadial c (R p.1) p.2 := by
        simpa only [Real.scalarRadial_zero] using
          Real.scalarRadial_strictMono hc (hRc p.1).le p.2.property
      have htop : Real.scalarRadial c (R p.1) p.2 < R p.1 := by
        simpa only [Real.scalarRadial_one] using
          Real.scalarRadial_strictMono hc (hRc p.1).le hbound
      refine Or.inr ⟨p.1, Real.scalarRadial c (R p.1) p.2, hpos, htop, ?_⟩
      rw [← hp]
      exact ambientRadial_apply_ray R hR c hc hRc p.1 p.2 p.2.property.le
  · rintro (rfl | ⟨θ, s, hs, htop, rfl⟩)
    · exact ⟨0, by simp, ambientRadial_zero R hR c hc hRc⟩
    · let r := Real.scalarRadialInverse c (R θ) s
      have hr : 0 < r := (Real.scalarRadialInverse_pos_iff hc (hRc θ).le).mpr hs
      have hbound : r < 1 := by
        apply (Real.scalarRadial_strictMono hc (hRc θ).le).lt_iff_lt.mp
        simpa only [r, Real.scalarRadial_apply_inverse hc, Real.scalarRadial_one] using htop
      refine ⟨r • (θ : E), ?_, ?_⟩
      · rw [mem_ball_zero_iff, norm_smul, Real.norm_eq_abs, abs_of_pos hr]
        simpa only [mem_sphere_zero_iff_norm.mp θ.property, mul_one] using hbound
      · rw [ambientRadial_apply_ray R hR c hc hRc θ r hr.le,
          Real.scalarRadial_apply_inverse hc]

private theorem exists_radial_diffeomorph
    (R : Metric.sphere (0 : E) 1 → ℝ)
    (hR : ContMDiff (𝓡 d) 𝓘(ℝ, ℝ) ∞ R)
    (c : ℝ) (hc : 0 < c) (hRc : ∀ θ, c < R θ) :
    ∃ F : E ≃ₘ[ℝ] E,
      F 0 = 0 ∧ F.symm 0 = 0 ∧
      (∀ x : E, ‖x‖ ≤ 1 / 4 → F x = c • x) ∧
      (∀ x : E, ‖x‖ ≤ c / 4 → F.symm x = c⁻¹ • x) ∧
      (∀ (θ : Metric.sphere (0 : E) 1) (r : ℝ), 0 ≤ r →
        F (r • (θ : E)) = Real.scalarRadial c (R θ) r • (θ : E)) ∧
      (∀ (θ : Metric.sphere (0 : E) 1) (s : ℝ), 0 ≤ s →
        F.symm (s • (θ : E)) = Real.scalarRadialInverse c (R θ) s • (θ : E)) ∧
      F '' Metric.closedBall (0 : E) 1 =
        {z | z = 0 ∨ ∃ θ : Metric.sphere (0 : E) 1, ∃ s : ℝ,
          0 < s ∧ s ≤ R θ ∧ z = s • (θ : E)} ∧
      F '' Metric.ball (0 : E) 1 =
        {z | z = 0 ∨ ∃ θ : Metric.sphere (0 : E) 1, ∃ s : ℝ,
          0 < s ∧ s < R θ ∧ z = s • (θ : E)} ∧
      F '' Metric.sphere (0 : E) 1 =
        Set.range (fun θ : Metric.sphere (0 : E) 1 => R θ • (θ : E)) :=
  ⟨ambientRadial R hR c hc hRc, ambientRadial_zero R hR c hc hRc,
    ambientRadial_symm_zero R hR c hc hRc, ambientRadial_apply_of_norm_le R hR c hc hRc,
    ambientRadial_symm_apply_of_norm_le R hR c hc hRc, ambientRadial_apply_ray R hR c hc hRc,
    ambientRadial_symm_apply_ray R hR c hc hRc, ambientRadial_image_closedBall R hR c hc hRc,
    ambientRadial_image_ball R hR c hc hRc, ambientRadial_image_sphere R hR c hc hRc⟩

end Diffeomorph

namespace Diffeomorph

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  {d : ℕ} [Fact (Module.finrank ℝ E = d + 1)]

theorem exists_diffeomorph_eq_smul_on_sphere
    (R : Metric.sphere (0 : E) 1 → ℝ)
    (hR : ContMDiff (𝓡 d) 𝓘(ℝ, ℝ) ∞ R) (hpos : ∀ θ, 0 < R θ) :
    ∃ F : E ≃ₘ[ℝ] E,
      F 0 = 0 ∧ F.symm 0 = 0 ∧
      (∀ θ : Metric.sphere (0 : E) 1, F θ = R θ • (θ : E)) ∧
      F '' Metric.closedBall (0 : E) 1 =
        {z | z = 0 ∨ ∃ θ : Metric.sphere (0 : E) 1, ∃ s : ℝ,
          0 < s ∧ s ≤ R θ ∧ z = s • (θ : E)} ∧
      F '' Metric.ball (0 : E) 1 =
        {z | z = 0 ∨ ∃ θ : Metric.sphere (0 : E) 1, ∃ s : ℝ,
          0 < s ∧ s < R θ ∧ z = s • (θ : E)} ∧
      F '' Metric.sphere (0 : E) 1 =
        Set.range (fun θ : Metric.sphere (0 : E) 1 => R θ • (θ : E)) := by
  let : FiniteDimensional ℝ E := Module.finite_of_finrank_eq_succ
    (Fact.out : Module.finrank ℝ E = d + 1)
  obtain ⟨a, ha, hRa⟩ := isCompact_univ.exists_forall_le' hR.continuous.continuousOn
    (fun θ _ => hpos θ)
  have hRc (θ : Metric.sphere (0 : E) 1) : a / 2 < R θ :=
    (half_lt_self ha).trans_le (hRa θ (Set.mem_univ θ))
  obtain ⟨F, hzero, hinvzero, _, _, hray, _, hclosed, hopen, hsphere⟩ :=
    exists_radial_diffeomorph R hR (a / 2) (half_pos ha) hRc
  refine ⟨F, hzero, hinvzero, ?_, hclosed, hopen, hsphere⟩
  intro θ
  simpa only [one_smul, Real.scalarRadial_one] using hray θ 1 zero_le_one

end Diffeomorph
