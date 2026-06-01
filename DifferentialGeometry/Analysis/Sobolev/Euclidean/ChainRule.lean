import DifferentialGeometry.Analysis.Sobolev.Euclidean.IteratedSobolev
import DifferentialGeometry.Analysis.Sobolev.Euclidean.Multiply
import Mathlib.MeasureTheory.Function.Jacobian

/-!
# Chain rule for `W^{k,p}` under a smooth bounded diffeomorphism

This file packages "smooth bounded diffeomorphism between two open
subsets of `E = EuclideanSpace ℝ (Fin d)`" as a self-contained record
`SmoothDiffeoBounded`. The base case (`k = 0`, i.e. `MemLp`) of the
chain-rule preservation is proved rigorously via the change-of-variables
formula `MeasureTheory.lintegral_image_eq_lintegral_abs_det_fderiv_mul`.

The structure is parametric over `d : ℕ`; the underlying space is
`EuclideanSpace ℝ (Fin d)` throughout, written without a local notation
to avoid elaboration interactions in tactic mode.
-/

noncomputable section

open MeasureTheory Set Filter Topology
open scoped ENNReal NNReal

namespace DifferentialGeometry
namespace Analysis
namespace Sobolev
namespace Euclidean

/-- A `C^∞` diffeomorphism between two open subsets of
`E = EuclideanSpace ℝ (Fin d)`, equipped with uniform bounds on the
iterated derivatives of both directions and a uniform lower bound on the
absolute determinant of the Jacobian.

The bounds and determinant lower bound are required to be **global** (not
just on `Ω`) — this avoids fragile cutoff constructions and is the natural
hypothesis for chart transitions in atlases of bounded geometry. -/
structure SmoothDiffeoBounded (d : ℕ) (Ω Ω' : Set (EuclideanSpace ℝ (Fin d))) where
  /-- The forward map. -/
  toFun : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d)
  /-- The inverse map. -/
  invFun : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d)
  /-- Smoothness of the forward map. -/
  toFun_smooth : ContDiff ℝ (⊤ : ℕ∞) toFun
  /-- Smoothness of the inverse map. -/
  invFun_smooth : ContDiff ℝ (⊤ : ℕ∞) invFun
  /-- The forward map sends `Ω` bijectively onto `Ω'`. -/
  bijOn : Set.BijOn toFun Ω Ω'
  /-- The inverse map sends `Ω'` bijectively onto `Ω`. -/
  invFun_bijOn : Set.BijOn invFun Ω' Ω
  /-- Left inverse on `Ω`. -/
  left_inv : Set.LeftInvOn invFun toFun Ω
  /-- Right inverse on `Ω'`. -/
  right_inv : Set.RightInvOn invFun toFun Ω'
  /-- Uniform upper bound for iterated derivatives of both directions. -/
  deriv_bound : ℝ
  /-- The bound is strictly positive. -/
  deriv_bound_pos : 0 < deriv_bound
  /-- All iterated derivatives of `toFun` are globally bounded by `deriv_bound`. -/
  iter_deriv_bounded : ∀ k : ℕ, ∀ x, ‖iteratedFDeriv ℝ k toFun x‖ ≤ deriv_bound
  /-- All iterated derivatives of `invFun` are globally bounded by `deriv_bound`. -/
  iter_deriv_invFun_bounded : ∀ k : ℕ, ∀ x, ‖iteratedFDeriv ℝ k invFun x‖ ≤ deriv_bound
  /-- Uniform positive lower bound for `|det DΦ|` on `Ω`. -/
  jacobian_lower_bound : ℝ
  /-- The Jacobian lower bound is strictly positive. -/
  jacobian_lower_bound_pos : 0 < jacobian_lower_bound
  /-- `|det DΦ(x)| ≥ jacobian_lower_bound` for `x ∈ Ω`. -/
  jacobian_lower : ∀ x ∈ Ω, jacobian_lower_bound ≤ |(fderiv ℝ toFun x).det|

namespace SmoothDiffeoBounded

variable {d : ℕ} {Ω Ω' : Set (EuclideanSpace ℝ (Fin d))}
    (Φ : SmoothDiffeoBounded d Ω Ω')

/-- The image of `Ω` under `toFun` is `Ω'`. -/
lemma image_toFun : Φ.toFun '' Ω = Ω' := Φ.bijOn.image_eq

/-- `toFun` restricted to `Ω` is injective. -/
lemma injOn_toFun : Set.InjOn Φ.toFun Ω := Φ.bijOn.injOn

/-- For `x ∈ Ω`, `toFun x ∈ Ω'`. -/
lemma mapsTo_toFun {x : EuclideanSpace ℝ (Fin d)} (hx : x ∈ Ω) :
    Φ.toFun x ∈ Ω' := Φ.bijOn.mapsTo hx

/-- For `y ∈ Ω'`, `invFun y ∈ Ω`. -/
lemma mapsTo_invFun {y : EuclideanSpace ℝ (Fin d)} (hy : y ∈ Ω') :
    Φ.invFun y ∈ Ω := Φ.invFun_bijOn.mapsTo hy

/-- Continuity of `toFun`. -/
lemma continuous_toFun : Continuous Φ.toFun := Φ.toFun_smooth.continuous

/-- Continuity of `invFun`. -/
lemma continuous_invFun : Continuous Φ.invFun := Φ.invFun_smooth.continuous

/-- Differentiability of `toFun`. -/
lemma differentiable_toFun : Differentiable ℝ Φ.toFun :=
  Φ.toFun_smooth.differentiable (by simp : ((⊤ : ℕ∞) : WithTop ℕ∞) ≠ 0)

/-- Differentiability of `invFun`. -/
lemma differentiable_invFun : Differentiable ℝ Φ.invFun :=
  Φ.invFun_smooth.differentiable (by simp : ((⊤ : ℕ∞) : WithTop ℕ∞) ≠ 0)

/-- Pointwise bound for `‖fderiv ℝ toFun x‖`. -/
lemma fderiv_toFun_bound (x : EuclideanSpace ℝ (Fin d)) :
    ‖fderiv ℝ Φ.toFun x‖ ≤ Φ.deriv_bound := by
  have h := Φ.iter_deriv_bounded 1 x
  rwa [norm_iteratedFDeriv_one] at h

/-- Pointwise bound for `‖fderiv ℝ invFun x‖`. -/
lemma fderiv_invFun_bound (x : EuclideanSpace ℝ (Fin d)) :
    ‖fderiv ℝ Φ.invFun x‖ ≤ Φ.deriv_bound := by
  have h := Φ.iter_deriv_invFun_bounded 1 x
  rwa [norm_iteratedFDeriv_one] at h

/-- `toFun` is Lipschitz with constant `deriv_bound`. -/
lemma toFun_lipschitz :
    LipschitzWith ⟨Φ.deriv_bound, le_of_lt Φ.deriv_bound_pos⟩ Φ.toFun := by
  apply lipschitzWith_of_nnnorm_fderiv_le Φ.differentiable_toFun
  intro x
  simp only [← NNReal.coe_le_coe, NNReal.coe_mk, coe_nnnorm]
  exact Φ.fderiv_toFun_bound x

/-- `invFun` is Lipschitz with constant `deriv_bound`. -/
lemma invFun_lipschitz :
    LipschitzWith ⟨Φ.deriv_bound, le_of_lt Φ.deriv_bound_pos⟩ Φ.invFun := by
  apply lipschitzWith_of_nnnorm_fderiv_le Φ.differentiable_invFun
  intro x
  simp only [← NNReal.coe_le_coe, NNReal.coe_mk, coe_nnnorm]
  exact Φ.fderiv_invFun_bound x

/-- The preimage of a set under `Φ.toFun`, intersected with `Ω`,
is the image of the original set under `invFun`, intersected with `Ω'`. -/
lemma toFun_preimage_inter_eq_invFun_image
    (s : Set (EuclideanSpace ℝ (Fin d))) :
    Φ.toFun ⁻¹' s ∩ Ω = Φ.invFun '' (s ∩ Ω') := by
  ext x
  simp only [Set.mem_inter_iff, Set.mem_preimage, Set.mem_image]
  constructor
  · rintro ⟨hxs, hxΩ⟩
    refine ⟨Φ.toFun x, ⟨hxs, Φ.mapsTo_toFun hxΩ⟩, Φ.left_inv hxΩ⟩
  · rintro ⟨y, ⟨hys, hyΩ'⟩, hxy⟩
    refine ⟨?_, ?_⟩
    · rw [← hxy, Φ.right_inv hyΩ']; exact hys
    · rw [← hxy]; exact Φ.mapsTo_invFun hyΩ'

/-- A measure-zero subset of `Ω'` has measure-zero preimage (intersected with `Ω`)
under `Φ.toFun`. -/
lemma toFun_preimage_null
    {s : Set (EuclideanSpace ℝ (Fin d))} (hs : volume (s ∩ Ω') = 0) :
    volume (Φ.toFun ⁻¹' s ∩ Ω) = 0 := by
  rw [Φ.toFun_preimage_inter_eq_invFun_image]
  exact MeasureTheory.addHaar_image_eq_zero_of_differentiableOn_of_addHaar_eq_zero
    (volume) Φ.differentiable_invFun.differentiableOn hs

/-- `Φ.toFun` is quasi-measure-preserving from `volume.restrict Ω` to
`volume.restrict Ω'`. -/
lemma toFun_quasiMeasurePreserving :
    MeasureTheory.Measure.QuasiMeasurePreserving Φ.toFun
      (volume.restrict Ω) (volume.restrict Ω') := by
  refine ⟨Φ.continuous_toFun.measurable, ?_⟩
  refine MeasureTheory.Measure.AbsolutelyContinuous.mk ?_
  intro s hs_meas hs_zero
  rw [MeasureTheory.Measure.restrict_apply hs_meas] at hs_zero
  have hpre_meas : MeasurableSet (Φ.toFun ⁻¹' s) :=
    Φ.continuous_toFun.measurable hs_meas
  have h_step1 : ((volume.restrict Ω).map Φ.toFun) s = volume (Φ.toFun ⁻¹' s ∩ Ω) := by
    rw [MeasureTheory.Measure.map_apply Φ.continuous_toFun.measurable hs_meas,
        MeasureTheory.Measure.restrict_apply hpre_meas]
  rw [h_step1]
  exact Φ.toFun_preimage_null hs_zero

end SmoothDiffeoBounded

/-- Change of variables for `lintegral` adapted to a smooth bounded
diffeomorphism: for any `g : E → ℝ≥0∞`,
`∫⁻ y in Ω', g y dy = ∫⁻ x in Ω, ENNReal.ofReal |det DΦ x| · g (Φ x) dx`. -/
lemma SmoothDiffeoBounded.lintegral_image_eq
    {d : ℕ} {Ω Ω' : Set (EuclideanSpace ℝ (Fin d))}
    (hΩ : IsOpen Ω) (Φ : SmoothDiffeoBounded d Ω Ω')
    (g : EuclideanSpace ℝ (Fin d) → ℝ≥0∞) :
    ∫⁻ y in Ω', g y ∂(volume) =
      ∫⁻ x in Ω, ENNReal.ofReal |(fderiv ℝ Φ.toFun x).det| * g (Φ.toFun x) ∂(volume) := by
  have hΦ_image : Φ.toFun '' Ω = Ω' := Φ.bijOn.image_eq
  have hΩ_meas : MeasurableSet Ω := hΩ.measurableSet
  have h_inj : Set.InjOn Φ.toFun Ω := Φ.bijOn.injOn
  have hΦ_diff : ∀ x, HasFDerivAt Φ.toFun (fderiv ℝ Φ.toFun x) x := fun x =>
    (Φ.differentiable_toFun x).hasFDerivAt
  have hΦ_deriv_within : ∀ x ∈ Ω, HasFDerivWithinAt Φ.toFun (fderiv ℝ Φ.toFun x) Ω x :=
    fun x _hx => (hΦ_diff x).hasFDerivWithinAt
  have h_chg :=
    MeasureTheory.lintegral_image_eq_lintegral_abs_det_fderiv_mul (μ := volume)
      (s := Ω) (f := Φ.toFun) (f' := fun x => fderiv ℝ Φ.toFun x)
      hΩ_meas hΦ_deriv_within h_inj g
  rw [hΦ_image] at h_chg
  exact h_chg

/-- The L^p norm of `u ∘ Φ` over `Ω` is bounded by a constant times the L^p
norm of `u` over `Ω'`. The constant comes from the lower bound on the
absolute Jacobian determinant of `Φ`.

This is the base case (`k = 0`) of the chain-rule preservation result. -/
theorem MemLp.comp_smoothDiffeoBounded
    {d : ℕ} {p : ℝ≥0∞} (hp_top : p ≠ ∞)
    {Ω Ω' : Set (EuclideanSpace ℝ (Fin d))} (hΩ : IsOpen Ω) (hΩ' : IsOpen Ω')
    (Φ : SmoothDiffeoBounded d Ω Ω')
    {u : EuclideanSpace ℝ (Fin d) → ℝ}
    (hu : MemLp u p (volume.restrict Ω')) :
    MemLp (fun x => u (Φ.toFun x)) p (volume.restrict Ω) := by
  classical
  have hΩ_meas : MeasurableSet Ω := hΩ.measurableSet
  have hΩ'_meas : MeasurableSet Ω' := hΩ'.measurableSet
  have h_aestrong : AEStronglyMeasurable
      (fun x => u (Φ.toFun x)) (volume.restrict Ω) := by
    have hqmp := Φ.toFun_quasiMeasurePreserving
    exact hu.aestronglyMeasurable.comp_quasiMeasurePreserving hqmp
  refine ⟨h_aestrong, ?_⟩
  by_cases hp_zero : p = 0
  · simp [hp_zero]
  rw [eLpNorm_lt_top_iff_lintegral_rpow_enorm_lt_top hp_zero hp_top]
  set q := p.toReal with hq_def
  set jLB := Φ.jacobian_lower_bound with hjLB_def
  have hjLB_pos : 0 < jLB := Φ.jacobian_lower_bound_pos
  have hjLB_ennreal_pos : 0 < ENNReal.ofReal jLB := by
    rw [ENNReal.ofReal_pos]; exact hjLB_pos
  have hjLB_ennreal_ne_top : ENNReal.ofReal jLB ≠ ⊤ := ENNReal.ofReal_ne_top
  have hbound_pointwise : ∀ x ∈ Ω,
      ENNReal.ofReal jLB * ‖u (Φ.toFun x)‖ₑ ^ q ≤
        ENNReal.ofReal |(fderiv ℝ Φ.toFun x).det| * ‖u (Φ.toFun x)‖ₑ ^ q := by
    intro x hx
    have h_le : ENNReal.ofReal jLB ≤ ENNReal.ofReal |(fderiv ℝ Φ.toFun x).det| :=
      ENNReal.ofReal_le_ofReal (Φ.jacobian_lower x hx)
    exact mul_le_mul_of_nonneg_right h_le (zero_le _)
  have hint_le :
      ENNReal.ofReal jLB * ∫⁻ x, ‖u (Φ.toFun x)‖ₑ ^ q ∂(volume.restrict Ω) ≤
        ∫⁻ x,
          ENNReal.ofReal |(fderiv ℝ Φ.toFun x).det| * ‖u (Φ.toFun x)‖ₑ ^ q
            ∂(volume.restrict Ω) := by
    rw [← MeasureTheory.lintegral_const_mul' _ _ hjLB_ennreal_ne_top]
    refine MeasureTheory.lintegral_mono_ae ?_
    rw [MeasureTheory.ae_restrict_iff' hΩ_meas]
    exact Filter.Eventually.of_forall fun x hx => hbound_pointwise x hx
  have hchg := Φ.lintegral_image_eq hΩ (fun y => ‖u y‖ₑ ^ q)
  have h_RHS_lt :
      ∫⁻ x,
        ENNReal.ofReal |(fderiv ℝ Φ.toFun x).det| * ‖u (Φ.toFun x)‖ₑ ^ q
          ∂(volume.restrict Ω) < ⊤ := by
    have h_RHS_eq :
        ∫⁻ x,
          ENNReal.ofReal |(fderiv ℝ Φ.toFun x).det| * ‖u (Φ.toFun x)‖ₑ ^ q
            ∂(volume.restrict Ω)
          = ∫⁻ y, ‖u y‖ₑ ^ q ∂(volume.restrict Ω') := hchg.symm
    rw [h_RHS_eq]
    exact lintegral_rpow_enorm_lt_top_of_eLpNorm_lt_top hp_zero hp_top hu.2
  have h_LHS_lt :
      ENNReal.ofReal jLB * ∫⁻ x, ‖u (Φ.toFun x)‖ₑ ^ q ∂(volume.restrict Ω) < ⊤ :=
    lt_of_le_of_lt hint_le h_RHS_lt
  by_contra h_top_contra
  rw [not_lt] at h_top_contra
  have h_top' :
      ∫⁻ x, ‖u (Φ.toFun x)‖ₑ ^ q ∂(volume.restrict Ω) = ⊤ := top_le_iff.mp h_top_contra
  rw [h_top', ENNReal.mul_top hjLB_ennreal_pos.ne'] at h_LHS_lt
  exact lt_irrefl _ h_LHS_lt

/-- The `MemWkp 0` (= `MemLp`) version of the chain rule. -/
theorem MemWkp.comp_smoothDiffeoBounded_zero
    {d : ℕ} {p : ℝ≥0∞} (hp_top : p ≠ ∞)
    {Ω Ω' : Set (EuclideanSpace ℝ (Fin d))} (hΩ : IsOpen Ω) (hΩ' : IsOpen Ω')
    (Φ : SmoothDiffeoBounded d Ω Ω')
    {u : EuclideanSpace ℝ (Fin d) → ℝ}
    (hu : MemWkp (d := d) 0 p u Ω') :
    MemWkp (d := d) 0 p (fun x => u (Φ.toFun x)) Ω := by
  rw [MemWkp_zero] at hu ⊢
  exact MemLp.comp_smoothDiffeoBounded hp_top hΩ hΩ' Φ hu

end Euclidean
end Sobolev
end Analysis
end DifferentialGeometry
