import DifferentialGeometry.Analysis.Complex.CauchyTransform.HolderRegularity
import Mathlib.Analysis.Distribution.AEEqOfIntegralContDiff
import Mathlib.Analysis.Calculus.LineDeriv.IntegrationByParts

set_option autoImplicit false

noncomputable section

open Set Filter Metric MeasureTheory
open scoped Topology ContDiff NNReal

namespace DifferentialGeometry.Analysis


section Density

variable {F : Type*} [NormedAddCommGroup F]

/-- Used only to express residual integrals on the ambient plane. -/
private def rawDensity {a : ℂ} {R : ℝ} (f : C(closedBall a R, F)) (z : ℂ) : F := by
  classical
  exact if hz : z ∈ closedBall a R then f ⟨z, hz⟩ else 0

private theorem rawDensity_coe {a : ℂ} {R : ℝ}
    (f : C(closedBall a R, F)) (w : closedBall a R) : rawDensity f w = f w := by
  simp only [rawDensity, dite_eq_left w.property]

private theorem rawDensity_zero {a : ℂ} {R : ℝ}
    (f : C(closedBall a R, F)) {z : ℂ} (hz : z ∉ closedBall a R) :
    rawDensity f z = 0 := by
  simp only [rawDensity, dite_eq_right hz]

private theorem continuousOn_rawDensity {a : ℂ} {R : ℝ}
    (f : C(closedBall a R, F)) : ContinuousOn (rawDensity f) (closedBall a R) := by
  apply continuousOn_iff_continuous_domRestrict.mpr
  change Continuous (fun w : closedBall a R => rawDensity f w)
  simpa only [rawDensity_coe] using f.continuous

end Density

private theorem integrable_realTest_smul
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    {φ : ℂ → ℝ} {g : ℂ → F} (hφ : Continuous φ) (hc : HasCompactSupport φ)
    (hg : ContinuousOn g (tsupport φ)) : Integrable (fun z => φ z • g z) := by
  apply (integrableOn_iff_integrable_of_support_subset
    ((Function.support_smul_subset_left φ g).trans (subset_tsupport φ))).mp
  exact (hφ.continuousOn.smul hg).integrableOn_compact hc

section Complex

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℂ F]

private theorem realTestDbar_smul (a b : ℝ) (x : F) :
    (((a : ℂ) + Complex.I * (b : ℂ)) / 2) • x =
      (1 / 2 : ℝ) • (a • x + Complex.I • (b • x)) := by
  rw [div_eq_mul_inv, mul_comm ((a : ℂ) + Complex.I * (b : ℂ)) (2 : ℂ)⁻¹,
    mul_smul, add_smul, mul_smul]
  rw [show (2 : ℂ)⁻¹ = ((1 / 2 : ℝ) : ℂ) by norm_num]
  have hcast (r : ℝ) (y : F) : (r : ℂ) • y = r • y := algebraMap_smul ℂ r y
  rw [hcast a x, hcast b x, hcast (1 / 2 : ℝ) _]

private theorem integral_subtype_realTest {a : ℂ} {R : ℝ}
    (f : C(closedBall a R, F)) (φ : ℂ → ℝ) :
    (∫ w : closedBall a R, (φ (w : ℂ) : ℂ) • f w
      ∂(volume.comap ((↑) : closedBall a R → ℂ))) =
        ∫ z : ℂ, φ z • rawDensity f z := by
  have hout : ∀ z ∉ closedBall a R, φ z • rawDensity f z = 0 := by
    intro z hz
    rw [rawDensity_zero f hz, smul_zero]
  rw [← setIntegral_eq_integral_of_forall_compl_eq_zero hout,
    ← integral_subtype_comap measurableSet_closedBall]
  apply integral_congr_ae
  exact Eventually.of_forall fun w => by
    change (φ (w : ℂ) : ℂ) • f w = φ (w : ℂ) • rawDensity f w
    rw [rawDensity_coe]
    exact algebraMap_smul ℂ (φ (w : ℂ)) (f w)

variable [CompleteSpace F]

omit [CompleteSpace F] in
/-- Compact test support supplies every L1 product in the two genuine
integration-by-parts identities. No global regularity of g is used. -/
private theorem integrable_and_integral_realTest_dbar
    {g : ℂ → F} {φ : ℂ → ℝ} (hφ : ContDiff ℝ 1 φ)
    (hc : HasCompactSupport φ) (hg : ∀ z ∈ tsupport φ, ContDiffAt ℝ 1 g z) :
    Integrable (fun z : ℂ => φ z • ((1 / 2 : ℝ) •
      (fderiv ℝ g z (1 : ℂ) + Complex.I • fderiv ℝ g z Complex.I))) ∧
    (∫ z : ℂ, φ z • ((1 / 2 : ℝ) •
      (fderiv ℝ g z (1 : ℂ) + Complex.I • fderiv ℝ g z Complex.I))) =
      -(∫ z : ℂ,
        (((fderiv ℝ φ z (1 : ℂ) : ℂ) +
          Complex.I * (fderiv ℝ φ z Complex.I : ℂ)) / 2) • g z) := by
  have hgc : ContinuousOn g (tsupport φ) :=
    fun z hz => (hg z hz).continuousAt.continuousWithinAt
  have hDc (v : ℂ) : ContinuousOn (fun z => fderiv ℝ g z v) (tsupport φ) := by
    intro z hz
    exact (((hg z hz).fderiv_right (m := 0) (by norm_num)).continuousAt.clm_apply
      continuousAt_const).continuousWithinAt
  have hφc (v : ℂ) : Continuous (fun z => fderiv ℝ φ z v) :=
    (hφ.continuous_fderiv (by norm_num)).clm_apply continuous_const
  have hiD (v : ℂ) : Integrable (fun z => φ z • fderiv ℝ g z v) :=
    integrable_realTest_smul hφ.continuous hc (hDc v)
  have hiφ (v : ℂ) : Integrable (fun z => fderiv ℝ φ z v • g z) :=
    integrable_realTest_smul (hφc v) (hc.fderiv_apply ℝ v)
      (hgc.mono (tsupport_fderiv_apply_subset ℝ v))
  have hparts (v : ℂ) : (∫ z : ℂ, φ z • fderiv ℝ g z v) =
      -(∫ z : ℂ, fderiv ℝ φ z v • g z) := by
    apply integral_smul_fderiv_eq_neg_fderiv_smul_of_integrable (hiφ v) (hiD v)
      (integrable_realTest_smul hφ.continuous hc hgc)
    · intro z _
      exact hφ.differentiable (by norm_num) z
    · intro z hz
      exact (hg z hz).differentiableAt (by norm_num)
  have hleft : (fun z : ℂ => φ z • ((1 / 2 : ℝ) •
      (fderiv ℝ g z (1 : ℂ) + Complex.I • fderiv ℝ g z Complex.I))) =
      fun z => (1 / 2 : ℝ) • (φ z • fderiv ℝ g z (1 : ℂ) +
        Complex.I • (φ z • fderiv ℝ g z Complex.I)) := by
    funext z
    rw [smul_comm (φ z) (1 / 2 : ℝ), smul_add, smul_comm (φ z) Complex.I]
  have hright : (fun z : ℂ =>
      (((fderiv ℝ φ z (1 : ℂ) : ℂ) +
        Complex.I * (fderiv ℝ φ z Complex.I : ℂ)) / 2) • g z) =
      fun z => (1 / 2 : ℝ) • (fderiv ℝ φ z (1 : ℂ) • g z +
        Complex.I • (fderiv ℝ φ z Complex.I • g z)) := by
    funext z
    exact realTestDbar_smul _ _ _
  have hiDI : Integrable (fun z : ℂ => Complex.I • (φ z • fderiv ℝ g z Complex.I)) :=
    (hiD Complex.I).smul Complex.I
  have hiφI : Integrable (fun z : ℂ => Complex.I • (fderiv ℝ φ z Complex.I • g z)) :=
    (hiφ Complex.I).smul Complex.I
  constructor
  · rw [hleft]
    exact ((hiD 1).add ((hiD Complex.I).smul Complex.I)).smul (1 / 2 : ℝ)
  · rw [hleft, hright, integral_smul,
      integral_add (hiD 1) hiDI, integral_smul,
      integral_smul, integral_add (hiφ 1) hiφI, integral_smul,
      hparts 1, hparts Complex.I]
    simp only [smul_add, smul_neg, neg_add]

/-- Local Hölder data derives C1 of the SAME ambient Cauchy integral, and
its proved weak equation then yields the pointwise dbar equation on the
actual open set. The original disk, density and comap measure are retained. -/
theorem contDiffOn_and_dbar_ambientCauchyIntegral_of_locally_holder
    {a : ℂ} {R : ℝ} {U : Set ℂ} (f : C(closedBall a R, F))
    (hU : IsOpen U) (hUD : U ⊆ ball a R)
    (hlocal : ∀ q ∈ U, ∃ ε : ℝ, 0 < ε ∧ ∃ α H : ℝ≥0,
      closedBall q ε ⊆ U ∧ 0 < α ∧ α ≤ 1 ∧
        HolderOnWith H α f {w : closedBall a R | (w : ℂ) ∈ closedBall q ε}) :
    ContDiffOn ℝ 1 (ambientCauchyIntegral f) U ∧
      ∀ q (hq : q ∈ U), (1 / 2 : ℝ) •
        (fderiv ℝ (ambientCauchyIntegral f) q (1 : ℂ) +
          Complex.I • fderiv ℝ (ambientCauchyIntegral f) q Complex.I) =
        f ⟨q, ball_subset_closedBall (hUD hq)⟩ := by
  have hT (q : ℂ) (hq : q ∈ U) : ContDiffAt ℝ 1 (ambientCauchyIntegral f) q := by
    obtain ⟨ε, hε, α, H, hball, hα, hα1, hf⟩ := hlocal q hq
    exact contDiffAt_ambientCauchyIntegral_of_holderOn f hε (hball.trans hUD) hf hα hα1
  have hTon : ContDiffOn ℝ 1 (ambientCauchyIntegral f) U :=
    fun q hq => (hT q hq).contDiffWithinAt
  let B (z : ℂ) : F := (1 / 2 : ℝ) •
    (fderiv ℝ (ambientCauchyIntegral f) z (1 : ℂ) +
      Complex.I • fderiv ℝ (ambientCauchyIntegral f) z Complex.I)
  have hD : ContinuousOn (fderiv ℝ (ambientCauchyIntegral f)) U :=
    hTon.continuousOn_fderiv_of_isOpen hU (by norm_num)
  have hBc : ContinuousOn B U :=
    ((hD.clm_apply continuousOn_const).add
      ((hD.clm_apply continuousOn_const).const_smul Complex.I)).const_smul (1 / 2 : ℝ)
  have hrc : ContinuousOn (rawDensity f) U :=
    (continuousOn_rawDensity f).mono (hUD.trans ball_subset_closedBall)
  let E (z : ℂ) : F := B z - rawDensity f z
  have hEc : ContinuousOn E U := hBc.sub hrc
  have hEA : ∀ᵐ z ∂volume, z ∈ U → E z = 0 := by
    apply hU.ae_eq_zero_of_integral_contDiff_smul_eq_zero
      (hEc.locallyIntegrableOn hU.measurableSet)
    intro φ hφ hc hs
    have hφ1 : ContDiff ℝ 1 φ := hφ.of_le (by simp)
    have hp := integrable_and_integral_realTest_dbar hφ1 hc (fun z hz => hT z (hs hz))
    have hw := integrable_and_weak_equation_ambientCauchyIntegral f hφ1 hc (hs.trans hUD)
    have hr : Integrable (fun z : ℂ => φ z • rawDensity f z) :=
      integrable_realTest_smul hφ.continuous hc (hrc.mono hs)
    have he : (∫ z : ℂ, φ z • B z) = ∫ z : ℂ, φ z • rawDensity f z := by
      calc
        _ = -(∫ z : ℂ,
          (((fderiv ℝ φ z (1 : ℂ) : ℂ) +
            Complex.I * (fderiv ℝ φ z Complex.I : ℂ)) / 2) •
              ambientCauchyIntegral f z) := hp.2
        _ = _ := by
          rw [hw.2, neg_neg]
          exact integral_subtype_realTest f φ
    change (∫ z : ℂ, φ z • (B z - rawDensity f z)) = 0
    simp only [smul_sub]
    rw [integral_sub hp.1 hr, he, sub_self]
  have hEzero : EqOn E 0 U := Measure.eqOn_open_of_ae_eq
    ((ae_restrict_iff' hU.measurableSet).mpr hEA) hU hEc continuousOn_const
  refine ⟨hTon, ?_⟩
  intro q hq
  have he := hEzero hq
  change B q - rawDensity f q = 0 at he
  have he' : B q = rawDensity f q := sub_eq_zero.mp he
  change B q = _
  rw [he', show rawDensity f q = f ⟨q, ball_subset_closedBall (hUD hq)⟩ from
    rawDensity_coe f ⟨q, ball_subset_closedBall (hUD hq)⟩]

/-- One genuine local Hölder ball gives the classical equation at its center.
The proof first derives C1 and the equation on an inner open neighborhood. -/
theorem contDiffAt_and_dbar_ambientCauchyIntegral_of_holderOn
    {a q : ℂ} {R ε : ℝ} (f : C(closedBall a R, F)) (hε : 0 < ε)
    (hinside : closedBall q ε ⊆ ball a R) {α H : ℝ≥0}
    (hf : HolderOnWith H α f {w : closedBall a R | (w : ℂ) ∈ closedBall q ε})
    (hα : 0 < α) (hα1 : α ≤ 1) :
    ContDiffAt ℝ 1 (ambientCauchyIntegral f) q ∧
      (1 / 2 : ℝ) • (fderiv ℝ (ambientCauchyIntegral f) q (1 : ℂ) +
        Complex.I • fderiv ℝ (ambientCauchyIntegral f) q Complex.I) =
      f ⟨q, ball_subset_closedBall (hinside (mem_closedBall_self hε.le))⟩ := by
  let U : Set ℂ := ball q (ε / 2)
  have hU : IsOpen U := isOpen_ball
  have hqU : q ∈ U := mem_ball_self (by positivity)
  have hUK : U ⊆ closedBall q ε :=
    ball_subset_closedBall.trans (closedBall_subset_closedBall (by linarith))
  obtain ⟨hT, he⟩ := contDiffOn_and_dbar_ambientCauchyIntegral_of_locally_holder
    f hU (hUK.trans hinside) (by
      intro y hy
      obtain ⟨δ, hδ, hδU⟩ := Metric.nhds_basis_closedBall.mem_iff.mp (hU.mem_nhds hy)
      refine ⟨δ, hδ, α, H, hδU, hα, hα1, hf.mono ?_⟩
      intro w hw
      exact hUK (hδU hw))
  exact ⟨hT.contDiffAt (hU.mem_nhds hqU), he q hqU⟩

end Complex

end DifferentialGeometry.Analysis
