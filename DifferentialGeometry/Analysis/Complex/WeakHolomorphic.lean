import DifferentialGeometry.External.DeGiorgi.WeakFormulation.SmoothTests
import DifferentialGeometry.Analysis.Sobolev.WeakDerivativeCommutation
import DifferentialGeometry.Analysis.Elliptic.Euclidean.Regularity.Harmonic
import DifferentialGeometry.Analysis.Sobolev.Euclidean.LocallyLipschitz.ChainRule
import Mathlib.Analysis.Complex.Conformal
import Mathlib.Analysis.Complex.RealDeriv
import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace

section

open MeasureTheory

namespace DifferentialGeometry.Analysis.Sobolev.Euclidean

local notation "E" => EuclideanSpace ℝ (Fin 2)

theorem integral_inner_weakGrad_smoothGradField_eq_zero_of_cauchy_riemann
    {p : ENNReal} (hp : 1 ≤ p) {Ω : Set E} {u v : E → ℝ}
    (hu : DeGiorgi.MemW1pWitness p u Ω) (hv : DeGiorgi.MemW1pWitness p v Ω)
    (hcr₀ : (fun x => hu.weakGrad x 0) =ᵐ[volume.restrict Ω]
      (fun x => hv.weakGrad x 1))
    (hcr₁ : (fun x => hu.weakGrad x 1) =ᵐ[volume.restrict Ω]
      (fun x => -hv.weakGrad x 0))
    {φ : E → ℝ} (hφ : DeGiorgi.IsSmoothTestOn Ω φ) :
    (∫ x in Ω, inner ℝ (hu.weakGrad x) (DeGiorgi.smoothGradField φ x)) = 0 := by
  have hcomm :
      (∫ x in Ω, hv.weakGrad x 1 * fderiv ℝ φ x (EuclideanSpace.single 0 1)) =
        ∫ x in Ω, hv.weakGrad x 0 * fderiv ℝ φ x (EuclideanSpace.single 1 1) :=
    DifferentialGeometry.Analysis.Sobolev.integral_weak_deriv_fderiv_comm
      (μ := volume.restrict Ω) (EuclideanSpace.single 1 1) (EuclideanSpace.single 0 1)
      (hv.isWeakGrad 1) (hv.isWeakGrad 0) hφ.1 hφ.2.1 hφ.2.2
  have hint (i j : Fin 2) :
      Integrable (fun x => hv.weakGrad x i *
        fderiv ℝ φ x (EuclideanSpace.single j 1)) (volume.restrict Ω) := by
    have hloc := (hv.weakGrad_component_memLp i).locallyIntegrable hp
    simpa only [smul_eq_mul] using
      hloc.integrable_smul_right_of_hasCompactSupport
        ((hφ.1.continuous_fderiv (by simp)).clm_apply continuous_const)
        (hφ.2.1.fderiv_apply (𝕜 := ℝ) (EuclideanSpace.single j 1))
  calc
    (∫ x in Ω, inner ℝ (hu.weakGrad x) (DeGiorgi.smoothGradField φ x)) =
        ∫ x in Ω, hv.weakGrad x 1 * fderiv ℝ φ x (EuclideanSpace.single 0 1) -
          hv.weakGrad x 0 * fderiv ℝ φ x (EuclideanSpace.single 1 1) := by
      apply integral_congr_ae
      filter_upwards [hcr₀, hcr₁] with x hx₀ hx₁
      simp only [PiLp.inner_apply, Real.inner_apply, Fin.sum_univ_two,
        DeGiorgi.smoothGradField]
      rw [hx₀, hx₁]
      ring
    _ = (∫ x in Ω, hv.weakGrad x 1 * fderiv ℝ φ x (EuclideanSpace.single 0 1)) -
        ∫ x in Ω, hv.weakGrad x 0 * fderiv ℝ φ x (EuclideanSpace.single 1 1) :=
      integral_sub (hint 1 0) (hint 0 1)
    _ = 0 := sub_eq_zero.mpr hcomm

end DifferentialGeometry.Analysis.Sobolev.Euclidean

end

section

noncomputable section

open Set Filter MeasureTheory
open scoped Topology ContDiff NNReal ENNReal

namespace DifferentialGeometry.Analysis

open Sobolev.Euclidean

local notation "V" => EuclideanSpace ℝ (Fin 2)

private def lipschitzBallWitness {f : V → ℝ} {L : ℝ≥0}
    (hf : LipschitzWith L f) (c : V) (R : ℝ) :
    DeGiorgi.MemW1pWitness 2 f (Metric.ball c R) := by
  let : IsFiniteMeasure (volume.restrict (Metric.ball c R)) :=
    isFiniteMeasure_restrict.mpr measure_ball_lt_top.ne
  exact {
    memLp := (hf.continuous.continuousOn.memLp_top_of_subset_isCompact
      (isCompact_closedBall c R) Metric.isOpen_ball.measurableSet
      Metric.ball_subset_closedBall).mono_exponent le_top
    weakGrad := fun x => WithLp.toLp 2 (fun i => fderiv ℝ f x (EuclideanSpace.single i 1))
    weakGrad_component_memLp := fun i =>
      (memLp_top_fderiv_of_lipschitzOnWith Metric.isOpen_ball
        hf.lipschitzOnWith i).mono_exponent le_top
    isWeakGrad := fun i =>
      hasWeakPartialDeriv_fderiv_of_lipschitzOnWith Metric.isOpen_ball hf.lipschitzOnWith i }

private theorem contDiffAt_of_lipschitz_of_ae_cauchy_riemann
    {F : V → ℂ} {L : ℝ≥0} (hF : LipschitzWith L F)
    {Ω : Set V} (hΩ : IsOpen Ω)
    (hCR : ∀ᵐ x ∂volume.restrict Ω,
      fderiv ℝ (fun y => (F y).re) x (EuclideanSpace.single 0 1) =
        fderiv ℝ (fun y => (F y).im) x (EuclideanSpace.single 1 1) ∧
      fderiv ℝ (fun y => (F y).re) x (EuclideanSpace.single 1 1) =
        -fderiv ℝ (fun y => (F y).im) x (EuclideanSpace.single 0 1))
    {x : V} (hx : x ∈ Ω) : ContDiffAt ℝ ∞ F x := by
  obtain ⟨R, hR, hRΩ⟩ := Metric.nhds_basis_closedBall.mem_iff.mp (hΩ.mem_nhds hx)
  let u : V → ℝ := fun y => (F y).re
  let v : V → ℝ := fun y => (F y).im
  have huLip : LipschitzWith (‖Complex.reCLM‖₊ * L) u := Complex.reCLM.lipschitzWith.comp hF
  have hvLip : LipschitzWith (‖Complex.imCLM‖₊ * L) v := Complex.imCLM.lipschitzWith.comp hF
  let wu := lipschitzBallWitness huLip x R
  let wv := lipschitzBallWitness hvLip x R
  have hCRball : ∀ᵐ y ∂volume.restrict (Metric.ball x R),
      fderiv ℝ u y (EuclideanSpace.single 0 1) = fderiv ℝ v y (EuclideanSpace.single 1 1) ∧
      fderiv ℝ u y (EuclideanSpace.single 1 1) = -fderiv ℝ v y
        (EuclideanSpace.single 0 1) := ae_mono (Measure.restrict_mono_set
        volume
    (Metric.ball_subset_closedBall.trans hRΩ)) hCR
  have hweakU (φ : V → ℝ) (hφ : DeGiorgi.IsSmoothTestOn (Metric.ball x R) φ)
    := integral_inner_weakGrad_smoothGradField_eq_zero_of_cauchy_riemann (by
    norm_num) wu wv
    (hCRball.mono fun _ h => h.1) (hCRball.mono fun _ h => h.2) hφ
  have hweakV (φ : V → ℝ) (hφ : DeGiorgi.IsSmoothTestOn (Metric.ball x R) φ)
    := integral_inner_weakGrad_smoothGradField_eq_zero_of_cauchy_riemann (by
    norm_num) wv (wu.smul (-1))
    (hCRball.mono fun y h => by
      change fderiv ℝ v y (EuclideanSpace.single 0 1) =
        (-1 : ℝ) * fderiv ℝ u y (EuclideanSpace.single 1 1)
      dsimp only [u, v]
      linarith [h.2])
    (hCRball.mono fun y h => by
      change fderiv ℝ v y (EuclideanSpace.single 1 1) =
        -((-1 : ℝ) * fderiv ℝ u y (EuclideanSpace.single 0 1))
      dsimp only [u, v]
      linarith [h.1]) hφ
  have hsmall : closure (Metric.ball x (R / 2)) ⊆ Metric.ball x R := by
    rw [closure_ball x (by positivity : R / 2 ≠ 0)]
    exact Metric.closedBall_subset_ball (by linarith)
  obtain ⟨u', hu', huu'⟩ := exists_contDiffOn_ae_eq_of_integral_inner_weakGrad_smoothGrad_eq_zero
    Metric.isOpen_ball Metric.isOpen_ball
    (by rw [closure_ball x (by positivity : R / 2 ≠ 0)]; exact isCompact_closedBall _ _)
    hsmall wu hweakU
  obtain ⟨v', hv', hvv'⟩ := exists_contDiffOn_ae_eq_of_integral_inner_weakGrad_smoothGrad_eq_zero
    Metric.isOpen_ball Metric.isOpen_ball
    (by rw [closure_ball x (by positivity : R / 2 ≠ 0)]; exact isCompact_closedBall _ _)
    hsmall wv hweakV
  have heu : EqOn u u' (Metric.ball x (R / 2)) :=
    Measure.eqOn_open_of_ae_eq huu' Metric.isOpen_ball
      huLip.continuous.continuousOn hu'.continuousOn
  have hev : EqOn v v' (Metric.ball x (R / 2)) :=
    Measure.eqOn_open_of_ae_eq hvv' Metric.isOpen_ball
      hvLip.continuous.continuousOn hv'.continuousOn
  have huC : ContDiffOn ℝ ∞ u (Metric.ball x (R / 2)) := hu'.congr heu
  have hvC : ContDiffOn ℝ ∞ v (Metric.ball x (R / 2)) := hv'.congr hev
  have hc : ContDiffOn ℝ ∞ (fun y => Complex.ofReal (u y) + Complex.ofReal (v y) * Complex.I)
      (Metric.ball x (R / 2)) :=
    (Complex.ofRealCLM.contDiff.comp_contDiffOn huC).add
      ((Complex.ofRealCLM.contDiff.comp_contDiffOn hvC).mul contDiffOn_const)
  have he : (fun y => Complex.ofReal (u y) + Complex.ofReal (v y) * Complex.I) = F := by
    funext y
    exact Complex.re_add_im (F y)
  rw [he] at hc
  exact hc.contDiffAt (Metric.ball_mem_nhds x (by positivity))

private theorem cauchy_riemann_repr {H : ℂ → ℂ} {x : V}
    (hH : DifferentiableAt ℂ H (Complex.orthonormalBasisOneI.repr.symm x)) :
    fderiv ℝ (fun y => (H (Complex.orthonormalBasisOneI.repr.symm y)).re) x
        (EuclideanSpace.single 0 1) =
      fderiv ℝ (fun y => (H (Complex.orthonormalBasisOneI.repr.symm y)).im) x
        (EuclideanSpace.single 1 1) ∧
    fderiv ℝ (fun y => (H (Complex.orthonormalBasisOneI.repr.symm y)).re) x
        (EuclideanSpace.single 1 1) =
      -fderiv ℝ (fun y => (H (Complex.orthonormalBasisOneI.repr.symm y)).im) x
        (EuclideanSpace.single 0 1) := by
  let e := Complex.orthonormalBasisOneI.repr.symm
  have hd := hH.hasDerivAt.complexToReal_fderiv.comp x e.hasFDerivAt
  have hr := Complex.reCLM.hasFDerivAt.comp x hd
  have hi := Complex.imCLM.hasFDerivAt.comp x hd
  have hreq := hr.fderiv
  have hieq := hi.fderiv
  change fderiv ℝ (fun y => (H (Complex.orthonormalBasisOneI.repr.symm y)).re) x = _ at hreq
  change fderiv ℝ (fun y => (H (Complex.orthonormalBasisOneI.repr.symm y)).im) x = _ at hieq
  rw [hreq, hieq]
  change (deriv H (e x) * e (EuclideanSpace.single 0 1)).re =
      (deriv H (e x) * e (EuclideanSpace.single 1 1)).im ∧
    (deriv H (e x) * e (EuclideanSpace.single 1 1)).re =
      -(deriv H (e x) * e (EuclideanSpace.single 0 1)).im
  simp only [e, Complex.orthonormalBasisOneI.repr_symm_single,
    Complex.coe_orthonormalBasisOneI, Matrix.cons_val_zero, Matrix.cons_val_one,
    mul_one, Complex.mul_I_re, Complex.mul_I_im]
  trivial

private theorem differentiableOn_of_lipschitzWith_of_ae_differentiableAt
    {H : ℂ → ℂ} {L : ℝ≥0} (hH : LipschitzWith L H)
    {Ω : Set ℂ} (hΩ : IsOpen Ω)
    (hae : ∀ᵐ z ∂volume.restrict Ω, DifferentiableAt ℂ H z) :
    DifferentiableOn ℂ H Ω := by
  let e := Complex.orthonormalBasisOneI.repr.symm
  let Ω' := e ⁻¹' Ω
  have hΩ' : IsOpen Ω' := hΩ.preimage e.continuous
  have hmp : MeasurePreserving e (volume.restrict Ω') (volume.restrict Ω) :=
    e.measurePreserving.restrict_preimage hΩ.measurableSet
  have hae' := hmp.quasiMeasurePreserving.ae hae
  have hCR := hae'.mono fun x hx => cauchy_riemann_repr hx
  have hFc : ∀ x ∈ Ω', ContDiffAt ℝ ∞ (H ∘ e) x :=
    fun x hx => contDiffAt_of_lipschitz_of_ae_cauchy_riemann
      (by simpa only [mul_one] using! hH.comp e.lipschitz) hΩ' hCR hx
  have hc : ContDiffOn ℝ ∞ H Ω := by
    intro z hz
    have hx : Complex.orthonormalBasisOneI.repr z ∈ Ω' := by
      simpa only [Ω', mem_preimage, e, LinearIsometryEquiv.symm_apply_apply] using hz
    have hh := (hFc _ hx).comp z Complex.orthonormalBasisOneI.repr.contDiff.contDiffAt
    have he : (H ∘ e) ∘ Complex.orthonormalBasisOneI.repr = H := by
      funext w
      simp only [Function.comp_apply, e, LinearIsometryEquiv.symm_apply_apply]
    rw [he] at hh
    exact hh.contDiffWithinAt
  have hder : ContinuousOn (fderiv ℝ H) Ω :=
    hc.continuousOn_fderiv_of_isOpen hΩ (by simp)
  have hcrcont : ContinuousOn (fun z => fderiv ℝ H z Complex.I -
      Complex.I * fderiv ℝ H z 1) Ω :=
    (hder.clm_apply continuousOn_const).sub
      (continuousOn_const.mul (hder.clm_apply continuousOn_const))
  have hcrzero : (fun z => fderiv ℝ H z Complex.I - Complex.I * fderiv ℝ H z 1)
      =ᵐ[volume.restrict Ω] 0 := hae.mono fun z hz => by
    have hh := (differentiableAt_complex_iff_differentiableAt_real.mp hz).2
    simpa only [smul_eq_mul, sub_eq_zero, Pi.zero_apply] using hh
  have hzero := Measure.eqOn_open_of_ae_eq hcrzero hΩ hcrcont continuousOn_const
  intro z hz
  apply DifferentiableAt.differentiableWithinAt
  apply differentiableAt_complex_iff_differentiableAt_real.mpr
  exact ⟨(hc.contDiffAt (hΩ.mem_nhds hz)).differentiableAt (by simp),
    by simpa only [Pi.zero_apply, sub_eq_zero, smul_eq_mul] using hzero hz⟩

theorem differentiableOn_of_lipschitzOnWith_of_ae_differentiableAt
    {Ω : Set ℂ} (hΩ : IsOpen Ω) {H : ℂ → ℂ} {L : ℝ≥0}
    (hH : LipschitzOnWith L H Ω)
    (hae : ∀ᵐ z ∂volume.restrict Ω, DifferentiableAt ℂ H z) :
    DifferentiableOn ℂ H Ω := by
  obtain ⟨G, hG, hHG⟩ := hH.extend_finite_dimension
  have haeG : ∀ᵐ z ∂volume.restrict Ω, DifferentiableAt ℂ G z := by
    filter_upwards [hae, ae_restrict_mem hΩ.measurableSet] with z hz hzΩ
    exact hz.congr_of_eventuallyEq
      (hHG.eventuallyEq_of_mem (hΩ.mem_nhds hzΩ)).symm
  have hdG := differentiableOn_of_lipschitzWith_of_ae_differentiableAt hG hΩ haeG
  exact hdG.congr hHG

end DifferentialGeometry.Analysis

end

end
