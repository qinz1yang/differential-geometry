import DifferentialGeometry.Analysis.Sobolev.Euclidean.IteratedSobolevSpace.IteratedSobolev
import DifferentialGeometry.Analysis.Sobolev.Euclidean.Multiplication.Multiply
import Mathlib.MeasureTheory.Function.Jacobian

noncomputable section

open MeasureTheory Set Filter Topology
open scoped ENNReal NNReal

namespace DifferentialGeometry
namespace Analysis
namespace Sobolev
namespace Euclidean

structure SmoothDiffeoBounded (d : ℕ) (Ω Ω' : Set (EuclideanSpace ℝ (Fin d))) where
  toFun : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d)
  invFun : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d)
  toFun_smooth : ContDiff ℝ (⊤ : ℕ∞) toFun
  invFun_smooth : ContDiff ℝ (⊤ : ℕ∞) invFun
  bijOn : Set.BijOn toFun Ω Ω'
  invFun_bijOn : Set.BijOn invFun Ω' Ω
  left_inv : Set.LeftInvOn invFun toFun Ω
  right_inv : Set.RightInvOn invFun toFun Ω'
  derivBound : ℝ
  deriv_bound_pos : 0 < derivBound
  iter_deriv_bounded : ∀ k : ℕ, ∀ x, ‖iteratedFDeriv ℝ k toFun x‖ ≤ derivBound
  iter_deriv_invFun_bounded : ∀ k : ℕ, ∀ x, ‖iteratedFDeriv ℝ k invFun x‖ ≤ derivBound
  jacobianLowerBound : ℝ
  jacobian_lower_bound_pos : 0 < jacobianLowerBound
  jacobian_lower : ∀ x ∈ Ω, jacobianLowerBound ≤ |(fderiv ℝ toFun x).det|


structure SmoothDiffeoBoundedAtOrder
    (d : ℕ) (Ω Ω' : Set (EuclideanSpace ℝ (Fin d))) (kmax : ℕ) where
  toFun : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d)
  invFun : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d)
  toFun_smooth : ContDiff ℝ (⊤ : ℕ∞) toFun
  invFun_smooth : ContDiff ℝ (⊤ : ℕ∞) invFun
  bijOn : Set.BijOn toFun Ω Ω'
  invFun_bijOn : Set.BijOn invFun Ω' Ω
  left_inv : Set.LeftInvOn invFun toFun Ω
  right_inv : Set.RightInvOn invFun toFun Ω'
  derivBound : ℝ
  deriv_bound_pos : 0 < derivBound
  iter_deriv_bounded_at : ∀ i ≤ kmax, ∀ x, ‖iteratedFDeriv ℝ i toFun x‖ ≤ derivBound
  iter_deriv_invFun_bounded_at :
    ∀ i ≤ kmax, ∀ x, ‖iteratedFDeriv ℝ i invFun x‖ ≤ derivBound
  jacobianLowerBound : ℝ
  jacobian_lower_bound_pos : 0 < jacobianLowerBound
  jacobian_lower : ∀ x ∈ Ω, jacobianLowerBound ≤ |(fderiv ℝ toFun x).det|

namespace SmoothDiffeoBoundedAtOrder

variable {d : ℕ} {kmax : ℕ} {Ω Ω' : Set (EuclideanSpace ℝ (Fin d))}
    (Φ : SmoothDiffeoBoundedAtOrder d Ω Ω' kmax)

lemma image_toFun : Φ.toFun '' Ω = Ω' := Φ.bijOn.image_eq

lemma injOn_toFun : Set.InjOn Φ.toFun Ω := Φ.bijOn.injOn

lemma mapsTo_toFun {x : EuclideanSpace ℝ (Fin d)} (hx : x ∈ Ω) :
    Φ.toFun x ∈ Ω' := Φ.bijOn.mapsTo hx

lemma mapsTo_invFun {y : EuclideanSpace ℝ (Fin d)} (hy : y ∈ Ω') :
    Φ.invFun y ∈ Ω := Φ.invFun_bijOn.mapsTo hy

lemma continuous_toFun : Continuous Φ.toFun := Φ.toFun_smooth.continuous

lemma continuous_invFun : Continuous Φ.invFun := Φ.invFun_smooth.continuous

lemma differentiable_toFun : Differentiable ℝ Φ.toFun :=
  Φ.toFun_smooth.differentiable (by simp : ((⊤ : ℕ∞) : WithTop ℕ∞) ≠ 0)

lemma differentiable_invFun : Differentiable ℝ Φ.invFun :=
  Φ.invFun_smooth.differentiable (by simp : ((⊤ : ℕ∞) : WithTop ℕ∞) ≠ 0)

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

lemma toFun_preimage_null
    {s : Set (EuclideanSpace ℝ (Fin d))} (hs : volume (s ∩ Ω') = 0) :
    volume (Φ.toFun ⁻¹' s ∩ Ω) = 0 := by
  rw [Φ.toFun_preimage_inter_eq_invFun_image]
  exact MeasureTheory.addHaar_image_eq_zero_of_differentiableOn_of_addHaar_eq_zero
    (volume) Φ.differentiable_invFun.differentiableOn hs

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

def weaken {kmax' : ℕ} (h : kmax' ≤ kmax) :
    SmoothDiffeoBoundedAtOrder d Ω Ω' kmax' where
  toFun := Φ.toFun
  invFun := Φ.invFun
  toFun_smooth := Φ.toFun_smooth
  invFun_smooth := Φ.invFun_smooth
  bijOn := Φ.bijOn
  invFun_bijOn := Φ.invFun_bijOn
  left_inv := Φ.left_inv
  right_inv := Φ.right_inv
  derivBound := Φ.derivBound
  deriv_bound_pos := Φ.deriv_bound_pos
  iter_deriv_bounded_at := fun i hi => Φ.iter_deriv_bounded_at i (hi.trans h)
  iter_deriv_invFun_bounded_at := fun i hi => Φ.iter_deriv_invFun_bounded_at i (hi.trans h)
  jacobianLowerBound := Φ.jacobianLowerBound
  jacobian_lower_bound_pos := Φ.jacobian_lower_bound_pos
  jacobian_lower := Φ.jacobian_lower

end SmoothDiffeoBoundedAtOrder

def SmoothDiffeoBounded.toAtOrder
    {d kmax : ℕ} {Ω Ω' : Set (EuclideanSpace ℝ (Fin d))}
    (Φ : SmoothDiffeoBounded d Ω Ω') :
    SmoothDiffeoBoundedAtOrder d Ω Ω' kmax where
  toFun := Φ.toFun
  invFun := Φ.invFun
  toFun_smooth := Φ.toFun_smooth
  invFun_smooth := Φ.invFun_smooth
  bijOn := Φ.bijOn
  invFun_bijOn := Φ.invFun_bijOn
  left_inv := Φ.left_inv
  right_inv := Φ.right_inv
  derivBound := Φ.derivBound
  deriv_bound_pos := Φ.deriv_bound_pos
  iter_deriv_bounded_at := fun i _ x => Φ.iter_deriv_bounded i x
  iter_deriv_invFun_bounded_at := fun i _ x => Φ.iter_deriv_invFun_bounded i x
  jacobianLowerBound := Φ.jacobianLowerBound
  jacobian_lower_bound_pos := Φ.jacobian_lower_bound_pos
  jacobian_lower := Φ.jacobian_lower

namespace SmoothDiffeoBoundedAtOrder

variable {d kmax : ℕ} {Ω Ω' : Set (EuclideanSpace ℝ (Fin d))}
    (Φ : SmoothDiffeoBoundedAtOrder d Ω Ω' kmax)

lemma fderiv_toFun_bound (hk : 1 ≤ kmax) (x : EuclideanSpace ℝ (Fin d)) :
    ‖fderiv ℝ Φ.toFun x‖ ≤ Φ.derivBound := by
  have h := Φ.iter_deriv_bounded_at 1 hk x
  rwa [norm_iteratedFDeriv_one] at h

lemma fderiv_invFun_bound (hk : 1 ≤ kmax) (x : EuclideanSpace ℝ (Fin d)) :
    ‖fderiv ℝ Φ.invFun x‖ ≤ Φ.derivBound := by
  have h := Φ.iter_deriv_invFun_bounded_at 1 hk x
  rwa [norm_iteratedFDeriv_one] at h

lemma toFun_lipschitz (hk : 1 ≤ kmax) :
    LipschitzWith ⟨Φ.derivBound, le_of_lt Φ.deriv_bound_pos⟩ Φ.toFun := by
  apply lipschitzWith_of_nnnorm_fderiv_le Φ.differentiable_toFun
  intro x
  change ‖fderiv ℝ Φ.toFun x‖ ≤ Φ.derivBound
  exact Φ.fderiv_toFun_bound hk x

lemma invFun_lipschitz (hk : 1 ≤ kmax) :
    LipschitzWith ⟨Φ.derivBound, le_of_lt Φ.deriv_bound_pos⟩ Φ.invFun := by
  apply lipschitzWith_of_nnnorm_fderiv_le Φ.differentiable_invFun
  intro x
  change ‖fderiv ℝ Φ.invFun x‖ ≤ Φ.derivBound
  exact Φ.fderiv_invFun_bound hk x

end SmoothDiffeoBoundedAtOrder

lemma SmoothDiffeoBoundedAtOrder.lintegral_image_eq
    {d kmax : ℕ} {Ω Ω' : Set (EuclideanSpace ℝ (Fin d))}
    (hΩ : IsOpen Ω) (Φ : SmoothDiffeoBoundedAtOrder d Ω Ω' kmax)
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

theorem MemLp.comp_smoothDiffeoBoundedAtOrder
    {d kmax : ℕ} {p : ℝ≥0∞} (hp_top : p ≠ ∞)
    {Ω Ω' : Set (EuclideanSpace ℝ (Fin d))} (hΩ : IsOpen Ω)
    (Φ : SmoothDiffeoBoundedAtOrder d Ω Ω' kmax)
    {u : EuclideanSpace ℝ (Fin d) → ℝ}
    (hu : MemLp u p (volume.restrict Ω')) :
    MemLp (fun x => u (Φ.toFun x)) p (volume.restrict Ω) := by
  classical
  have hΩ_meas : MeasurableSet Ω := hΩ.measurableSet
  have h_aestrong : AEStronglyMeasurable
      (fun x => u (Φ.toFun x)) (volume.restrict Ω) := by
    have hqmp := Φ.toFun_quasiMeasurePreserving
    exact hu.aestronglyMeasurable.comp_quasiMeasurePreserving hqmp
  rw [memLp_iff]
  by_cases hp_zero : p = 0
  · simp [hp_zero, h_aestrong]
  rw [eLpNorm_lt_top_iff_lintegral_rpow_enorm_lt_top hp_zero hp_top h_aestrong]
  set q := p.toReal with hq_def
  set jLB := Φ.jacobianLowerBound with hjLB_def
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
    exact mul_le_mul_of_nonneg_right h_le bot_le
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
    exact lintegral_rpow_enorm_lt_top_of_eLpNorm_lt_top hp_zero hp_top hu.eLpNorm_lt_top
  have h_LHS_lt :
      ENNReal.ofReal jLB * ∫⁻ x, ‖u (Φ.toFun x)‖ₑ ^ q ∂(volume.restrict Ω) < ⊤ :=
    lt_of_le_of_lt hint_le h_RHS_lt
  by_contra h_top_contra
  rw [not_lt] at h_top_contra
  have h_top' :
      ∫⁻ x, ‖u (Φ.toFun x)‖ₑ ^ q ∂(volume.restrict Ω) = ⊤ := top_le_iff.mp h_top_contra
  rw [h_top', ENNReal.mul_top hjLB_ennreal_pos.ne'] at h_LHS_lt
  exact lt_irrefl _ h_LHS_lt

theorem MemWkp.comp_smoothDiffeoBoundedAtOrder_zero
    {d kmax : ℕ} {p : ℝ≥0∞} (hp_top : p ≠ ∞)
    {Ω Ω' : Set (EuclideanSpace ℝ (Fin d))} (hΩ : IsOpen Ω)
    (Φ : SmoothDiffeoBoundedAtOrder d Ω Ω' kmax)
    {u : EuclideanSpace ℝ (Fin d) → ℝ}
    (hu : MemWkp (d := d) 0 p u Ω') :
    MemWkp (d := d) 0 p (fun x => u (Φ.toFun x)) Ω := by
  rw [MemWkp_zero] at hu ⊢
  exact MemLp.comp_smoothDiffeoBoundedAtOrder hp_top hΩ Φ hu

namespace SmoothDiffeoBounded

variable {d : ℕ} {Ω Ω' : Set (EuclideanSpace ℝ (Fin d))}
    (Φ : SmoothDiffeoBounded d Ω Ω')

lemma image_toFun : Φ.toFun '' Ω = Ω' := by
  exact (Φ.toAtOrder (kmax := 0)).image_toFun

lemma injOn_toFun : Set.InjOn Φ.toFun Ω := by
  exact (Φ.toAtOrder (kmax := 0)).injOn_toFun

lemma mapsTo_toFun {x : EuclideanSpace ℝ (Fin d)} (hx : x ∈ Ω) :
    Φ.toFun x ∈ Ω' := by
  exact (Φ.toAtOrder (kmax := 0)).mapsTo_toFun hx

lemma mapsTo_invFun {y : EuclideanSpace ℝ (Fin d)} (hy : y ∈ Ω') :
    Φ.invFun y ∈ Ω := by
  exact (Φ.toAtOrder (kmax := 0)).mapsTo_invFun hy

lemma continuous_toFun : Continuous Φ.toFun := by
  exact (Φ.toAtOrder (kmax := 0)).continuous_toFun

lemma continuous_invFun : Continuous Φ.invFun := by
  exact (Φ.toAtOrder (kmax := 0)).continuous_invFun

lemma differentiable_toFun : Differentiable ℝ Φ.toFun := by
  exact (Φ.toAtOrder (kmax := 0)).differentiable_toFun

lemma differentiable_invFun : Differentiable ℝ Φ.invFun := by
  exact (Φ.toAtOrder (kmax := 0)).differentiable_invFun

lemma fderiv_toFun_bound (x : EuclideanSpace ℝ (Fin d)) :
    ‖fderiv ℝ Φ.toFun x‖ ≤ Φ.derivBound := by
  exact (Φ.toAtOrder (kmax := 1)).fderiv_toFun_bound (le_refl 1) x

lemma fderiv_invFun_bound (x : EuclideanSpace ℝ (Fin d)) :
    ‖fderiv ℝ Φ.invFun x‖ ≤ Φ.derivBound := by
  exact (Φ.toAtOrder (kmax := 1)).fderiv_invFun_bound (le_refl 1) x

lemma toFun_lipschitz :
    LipschitzWith ⟨Φ.derivBound, le_of_lt Φ.deriv_bound_pos⟩ Φ.toFun := by
  exact (Φ.toAtOrder (kmax := 1)).toFun_lipschitz (le_refl 1)

lemma invFun_lipschitz :
    LipschitzWith ⟨Φ.derivBound, le_of_lt Φ.deriv_bound_pos⟩ Φ.invFun := by
  exact (Φ.toAtOrder (kmax := 1)).invFun_lipschitz (le_refl 1)

lemma toFun_preimage_inter_eq_invFun_image
    (s : Set (EuclideanSpace ℝ (Fin d))) :
    Φ.toFun ⁻¹' s ∩ Ω = Φ.invFun '' (s ∩ Ω') := by
  exact (Φ.toAtOrder (kmax := 0)).toFun_preimage_inter_eq_invFun_image s

lemma toFun_preimage_null
    {s : Set (EuclideanSpace ℝ (Fin d))} (hs : volume (s ∩ Ω') = 0) :
    volume (Φ.toFun ⁻¹' s ∩ Ω) = 0 := by
  exact (Φ.toAtOrder (kmax := 0)).toFun_preimage_null hs

lemma toFun_quasiMeasurePreserving :
    MeasureTheory.Measure.QuasiMeasurePreserving Φ.toFun
      (volume.restrict Ω) (volume.restrict Ω') := by
  exact (Φ.toAtOrder (kmax := 0)).toFun_quasiMeasurePreserving

end SmoothDiffeoBounded

lemma SmoothDiffeoBounded.lintegral_image_eq
    {d : ℕ} {Ω Ω' : Set (EuclideanSpace ℝ (Fin d))}
    (hΩ : IsOpen Ω) (Φ : SmoothDiffeoBounded d Ω Ω')
    (g : EuclideanSpace ℝ (Fin d) → ℝ≥0∞) :
    ∫⁻ y in Ω', g y ∂(volume) =
      ∫⁻ x in Ω, ENNReal.ofReal |(fderiv ℝ Φ.toFun x).det| * g (Φ.toFun x) ∂(volume) := by
  exact (Φ.toAtOrder (kmax := 0)).lintegral_image_eq hΩ g

theorem MemLp.comp_smoothDiffeoBounded
    {d : ℕ} {p : ℝ≥0∞} (hp_top : p ≠ ∞)
    {Ω Ω' : Set (EuclideanSpace ℝ (Fin d))} (hΩ : IsOpen Ω)
    (Φ : SmoothDiffeoBounded d Ω Ω')
    {u : EuclideanSpace ℝ (Fin d) → ℝ}
    (hu : MemLp u p (volume.restrict Ω')) :
    MemLp (fun x => u (Φ.toFun x)) p (volume.restrict Ω) := by
  exact MemLp.comp_smoothDiffeoBoundedAtOrder hp_top hΩ
    (Φ.toAtOrder (kmax := 0)) hu

theorem MemWkp.comp_smoothDiffeoBounded_zero
    {d : ℕ} {p : ℝ≥0∞} (hp_top : p ≠ ∞)
    {Ω Ω' : Set (EuclideanSpace ℝ (Fin d))} (hΩ : IsOpen Ω)
    (Φ : SmoothDiffeoBounded d Ω Ω')
    {u : EuclideanSpace ℝ (Fin d) → ℝ}
    (hu : MemWkp (d := d) 0 p u Ω') :
    MemWkp (d := d) 0 p (fun x => u (Φ.toFun x)) Ω := by
  exact MemWkp.comp_smoothDiffeoBoundedAtOrder_zero hp_top hΩ
    (Φ.toAtOrder (kmax := 0)) hu

variable {d : ℕ}

local notation "E" => EuclideanSpace ℝ (Fin d)

def SmoothDiffeoBoundedAtOrder.mkFromConcrete
    {kmax : ℕ} {Ω Ω' : Set E}
    (toFun invFun : E → E)
    (toFun_smooth : ContDiff ℝ (⊤ : ℕ∞) toFun)
    (invFun_smooth : ContDiff ℝ (⊤ : ℕ∞) invFun)
    (bijOn : Set.BijOn toFun Ω Ω')
    (invFun_bijOn : Set.BijOn invFun Ω' Ω)
    (left_inv : Set.LeftInvOn invFun toFun Ω)
    (right_inv : Set.RightInvOn invFun toFun Ω')
    (derivBound : ℝ) (deriv_bound_pos : 0 < derivBound)
    (iter_deriv_bounded_at :
      ∀ i ≤ kmax, ∀ x, ‖iteratedFDeriv ℝ i toFun x‖ ≤ derivBound)
    (iter_deriv_invFun_bounded_at :
      ∀ i ≤ kmax, ∀ x, ‖iteratedFDeriv ℝ i invFun x‖ ≤ derivBound)
    (jacobianLowerBound : ℝ) (jacobian_lower_bound_pos : 0 < jacobianLowerBound)
    (jacobian_lower : ∀ x ∈ Ω, jacobianLowerBound ≤ |(fderiv ℝ toFun x).det|) :
    SmoothDiffeoBoundedAtOrder d Ω Ω' kmax where
  toFun := toFun
  invFun := invFun
  toFun_smooth := toFun_smooth
  invFun_smooth := invFun_smooth
  bijOn := bijOn
  invFun_bijOn := invFun_bijOn
  left_inv := left_inv
  right_inv := right_inv
  derivBound := derivBound
  deriv_bound_pos := deriv_bound_pos
  iter_deriv_bounded_at := iter_deriv_bounded_at
  iter_deriv_invFun_bounded_at := iter_deriv_invFun_bounded_at
  jacobianLowerBound := jacobianLowerBound
  jacobian_lower_bound_pos := jacobian_lower_bound_pos
  jacobian_lower := jacobian_lower

theorem mk_smoothDiffeoBoundedAtOrder_of_per_order_bounds
    {kmax : ℕ} {Ω Ω' : Set E}
    {T Tinv : E → E}
    (hT_smooth : ContDiff ℝ (⊤ : ℕ∞) T)
    (hTinv_smooth : ContDiff ℝ (⊤ : ℕ∞) Tinv)
    (hbij : Set.BijOn T Ω Ω')
    (hbij_inv : Set.BijOn Tinv Ω' Ω)
    (hleft : Set.LeftInvOn Tinv T Ω)
    (hright : Set.RightInvOn Tinv T Ω')
    {derivBound : ℝ} (hbound_pos : 0 < derivBound)
    (hT_iter_bound : ∀ i ≤ kmax, ∀ x, ‖iteratedFDeriv ℝ i T x‖ ≤ derivBound)
    (hTinv_iter_bound : ∀ i ≤ kmax, ∀ x, ‖iteratedFDeriv ℝ i Tinv x‖ ≤ derivBound)
    {jacobianLowerBound : ℝ} (hj_pos : 0 < jacobianLowerBound)
    (hj_lower : ∀ x ∈ Ω, jacobianLowerBound ≤ |(fderiv ℝ T x).det|) :
    Nonempty (SmoothDiffeoBoundedAtOrder d Ω Ω' kmax) :=
  ⟨SmoothDiffeoBoundedAtOrder.mkFromConcrete
    (d := d) T Tinv hT_smooth hTinv_smooth hbij hbij_inv hleft hright
    derivBound hbound_pos hT_iter_bound hTinv_iter_bound
    jacobianLowerBound hj_pos hj_lower⟩

end Euclidean
end Sobolev
end Analysis
end DifferentialGeometry
