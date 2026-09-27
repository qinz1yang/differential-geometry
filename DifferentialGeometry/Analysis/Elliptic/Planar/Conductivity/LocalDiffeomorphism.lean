import DifferentialGeometry.Analysis.Elliptic.Planar.Conductivity.StreamFunction
import DifferentialGeometry.Analysis.Calculus.Inverse.LocalInverse
import Mathlib.LinearAlgebra.Determinant
import Mathlib.Analysis.Normed.Module.FiniteDimension

section

noncomputable section

open scoped ContDiff Topology

namespace DifferentialGeometry.Analysis

local notation "V" => EuclideanSpace ℝ (Fin 2)

theorem planarConductivity_eq_of_isSymm_det_eq_one
    {A : Matrix (Fin 2) (Fin 2) ℝ} (hA : A.IsSymm) (hdet : A.det = 1) :
    planarConductivity (A 1 1) (A 0 0) (-A 0 1) = A := by
  have hcross : A 1 0 = A 0 1 := hA.apply 0 1
  have hd : A 1 1 * A 0 0 - (-A 0 1) ^ 2 = 1 := by
    rw [Matrix.det_fin_two, hcross] at hdet
    nlinarith only [hdet]
  rw [planarConductivity, hd, Real.sqrt_one, inv_one, one_smul]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [hcross]

theorem det_fderiv_eq_gradient_dot_flux_of_stream
    {v s : V → ℝ} {F : V → V} {z : ℂ}
    (hv : DifferentiableAt ℝ v (Complex.orthonormalBasisOneI.repr z))
    (hs : HasFDerivAt s (planarFluxForm F (Complex.orthonormalBasisOneI.repr z))
      (Complex.orthonormalBasisOneI.repr z)) :
    (fderiv ℝ (fun w =>
      (v (Complex.orthonormalBasisOneI.repr w) : ℂ) +
        (s (Complex.orthonormalBasisOneI.repr w) : ℂ) * Complex.I) z).toLinearMap.det =
      dotProduct (DeGiorgi.smoothGradField v (Complex.orthonormalBasisOneI.repr z)).ofLp
        (F (Complex.orthonormalBasisOneI.repr z)).ofLp := by
  let e := Complex.orthonormalBasisOneI.repr
  have he := e.toContinuousLinearEquiv.hasFDerivAt (x := z)
  have hU := (Complex.ofRealCLM.hasFDerivAt.comp (e z) hv.hasFDerivAt).comp z he
  have hS := (Complex.ofRealCLM.hasFDerivAt.comp (e z) hs).comp z he
  have hW := (hU.add (hS.mul_const Complex.I)).fderiv
  change fderiv ℝ (fun w => (v (e w) : ℂ) + (s (e w) : ℂ) * Complex.I) z = _ at hW
  rw [← LinearMap.det_toMatrix Complex.basisOneI, Matrix.det_fin_two]
  simp only [LinearMap.toMatrix_apply, Complex.coe_basisOneI_repr, Complex.coe_basisOneI]
  rw [hW]
  have he0 : e 1 = EuclideanSpace.single 0 1 := by
    ext i
    fin_cases i <;> simp [e]
  have he1 : e Complex.I = EuclideanSpace.single 1 1 := by
    ext i
    fin_cases i <;> simp [e]
  simp [planarFluxForm, e, DeGiorgi.smoothGradField,
    dotProduct, Fin.sum_univ_two, Complex.real_smul, ← he0, ← he1]

theorem det_fderiv_eq_gradient_dot_conductivity_mulVec_of_stream
    {A : V → Matrix (Fin 2) (Fin 2) ℝ} {v s : V → ℝ} {z : ℂ}
    (hv : DifferentiableAt ℝ v (Complex.orthonormalBasisOneI.repr z))
    (hs : HasFDerivAt s
      (planarFluxForm (fun x => DeGiorgi.matMulE (A x) (DeGiorgi.smoothGradField v x))
        (Complex.orthonormalBasisOneI.repr z)) (Complex.orthonormalBasisOneI.repr z)) :
    (fderiv ℝ (fun w =>
      (v (Complex.orthonormalBasisOneI.repr w) : ℂ) +
        (s (Complex.orthonormalBasisOneI.repr w) : ℂ) * Complex.I) z).toLinearMap.det =
      dotProduct (DeGiorgi.smoothGradField v (Complex.orthonormalBasisOneI.repr z)).ofLp
        ((A (Complex.orthonormalBasisOneI.repr z)).mulVec
          (DeGiorgi.smoothGradField v (Complex.orthonormalBasisOneI.repr z)).ofLp) := by
  rw [det_fderiv_eq_gradient_dot_flux_of_stream hv hs, DeGiorgi.matMulE_ofLp]

theorem det_fderiv_pos_of_conductivity_stream
    {A : V → Matrix (Fin 2) (Fin 2) ℝ} {v s : V → ℝ} {z : ℂ}
    (hA : (A (Complex.orthonormalBasisOneI.repr z)).PosDef)
    (hv : DifferentiableAt ℝ v (Complex.orthonormalBasisOneI.repr z))
    (hs : HasFDerivAt s
      (planarFluxForm (fun x => DeGiorgi.matMulE (A x) (DeGiorgi.smoothGradField v x))
        (Complex.orthonormalBasisOneI.repr z)) (Complex.orthonormalBasisOneI.repr z))
    (hgrad : DeGiorgi.smoothGradField v (Complex.orthonormalBasisOneI.repr z) ≠ 0) :
    0 < (fderiv ℝ (fun w =>
      (v (Complex.orthonormalBasisOneI.repr w) : ℂ) +
        (s (Complex.orthonormalBasisOneI.repr w) : ℂ) * Complex.I) z).toLinearMap.det := by
  rw [det_fderiv_eq_gradient_dot_conductivity_mulVec_of_stream hv hs]
  have hne : (DeGiorgi.smoothGradField v (Complex.orthonormalBasisOneI.repr z)).ofLp ≠ 0 := by
    intro he
    apply hgrad
    ext i
    exact congrFun he i
  simpa only [star_trivial] using hA.dotProduct_mulVec_pos hne

theorem beltrami_fderiv_of_unit_determinant_conductivity_stream
    {A : V → Matrix (Fin 2) (Fin 2) ℝ} {v s : V → ℝ} {z : ℂ}
    (hA : (A (Complex.orthonormalBasisOneI.repr z)).PosDef)
    (hdet : (A (Complex.orthonormalBasisOneI.repr z)).det = 1)
    (hv : DifferentiableAt ℝ v (Complex.orthonormalBasisOneI.repr z))
    (hs : HasFDerivAt s
      (planarFluxForm (fun x => DeGiorgi.matMulE (A x) (DeGiorgi.smoothGradField v x))
        (Complex.orthonormalBasisOneI.repr z)) (Complex.orthonormalBasisOneI.repr z)) :
    complexAntilinearPart (fderiv ℝ (fun w =>
      (v (Complex.orthonormalBasisOneI.repr w) : ℂ) +
        (s (Complex.orthonormalBasisOneI.repr w) : ℂ) * Complex.I) z) =
      beltramiCoefficient (A (Complex.orthonormalBasisOneI.repr z) 1 1)
        (A (Complex.orthonormalBasisOneI.repr z) 0 0)
        (-A (Complex.orthonormalBasisOneI.repr z) 0 1) *
          complexLinearPart (fderiv ℝ (fun w =>
            (v (Complex.orthonormalBasisOneI.repr w) : ℂ) +
              (s (Complex.orthonormalBasisOneI.repr w) : ℂ) * Complex.I) z) := by
  let P := A (Complex.orthonormalBasisOneI.repr z)
  have hsym : P.IsSymm := Matrix.isHermitian_iff_isSymm.mp hA.isHermitian
  have hd : P 1 1 * P 0 0 - (-P 0 1) ^ 2 = 1 := by
    have hcross := hsym.apply 0 1
    change P.det = 1 at hdet
    rw [Matrix.det_fin_two, hcross] at hdet
    nlinarith only [hdet]
  apply beltrami_fderiv_of_conductivity_stream hA.diag_pos (by rw [hd]; norm_num) hv
  have hmat := planarConductivity_eq_of_isSymm_det_eq_one hsym hdet
  dsimp only [P] at hmat
  simpa only [planarFluxForm, hmat] using hs

theorem exists_localInverse_of_conductivity_stream
    {A : V → Matrix (Fin 2) (Fin 2) ℝ} {v s : V → ℝ}
    {Ω : Set V} {n : ℕ∞ω} (hn : n ≠ 0) (hΩ : IsOpen Ω)
    (hv : ContDiffOn ℝ n v Ω) (hs : ContDiffOn ℝ n s Ω)
    {z : ℂ} (hz : Complex.orthonormalBasisOneI.repr z ∈ Ω)
    (hA : (A (Complex.orthonormalBasisOneI.repr z)).PosDef)
    (hstream : HasFDerivAt s
      (planarFluxForm (fun x => DeGiorgi.matMulE (A x) (DeGiorgi.smoothGradField v x))
        (Complex.orthonormalBasisOneI.repr z)) (Complex.orthonormalBasisOneI.repr z))
    (hgrad : DeGiorgi.smoothGradField v (Complex.orthonormalBasisOneI.repr z) ≠ 0) :
    ∃ e : OpenPartialHomeomorph ℂ ℂ,
      z ∈ e.source ∧ e.source ⊆ Complex.orthonormalBasisOneI.repr ⁻¹' Ω ∧
      ContDiffOn ℝ n e e.source ∧ ContDiffOn ℝ n e.symm e.target ∧
      ∀ w, e w = (v (Complex.orthonormalBasisOneI.repr w) : ℂ) +
        (s (Complex.orthonormalBasisOneI.repr w) : ℂ) * Complex.I := by
  let w : ℂ → ℂ := fun t => (v (Complex.orthonormalBasisOneI.repr t) : ℂ) +
    (s (Complex.orthonormalBasisOneI.repr t) : ℂ) * Complex.I
  let U : Set ℂ := Complex.orthonormalBasisOneI.repr ⁻¹' Ω
  have hU : IsOpen U := hΩ.preimage Complex.orthonormalBasisOneI.repr.continuous
  have he : ContDiffOn ℝ n Complex.orthonormalBasisOneI.repr U :=
    Complex.orthonormalBasisOneI.repr.toContinuousLinearEquiv.contDiff.contDiffOn
  have hv' := hv.comp he (fun t ht => ht)
  have hs' := hs.comp he (fun t ht => ht)
  have hw : ContDiffOn ℝ n w U :=
    (Complex.ofRealCLM.contDiff.comp_contDiffOn hv').add
      ((Complex.ofRealCLM.contDiff.comp_contDiffOn hs').mul contDiffOn_const)
  have hvz := (hv.differentiableOn hn).differentiableAt (hΩ.mem_nhds hz)
  have hdet : (fderiv ℝ w z).toLinearMap.det ≠ 0 :=
    ne_of_gt (det_fderiv_pos_of_conductivity_stream hA hvz hstream hgrad)
  let L := (fderiv ℝ w z).toContinuousLinearEquivOfDetNeZero hdet
  have hL : (L : ℂ →L[ℝ] ℂ) = fderiv ℝ w z := by
    simp only [L, ContinuousLinearMap.coe_toContinuousLinearEquivOfDetNeZero]
  have hd : HasFDerivAt w (L : ℂ →L[ℝ] ℂ) z := by
    rw [hL]
    exact ((hw.differentiableOn hn).differentiableAt (hU.mem_nhds hz)).hasFDerivAt
  exact exists_localInverse_of_hasFDerivAt_equiv_of_ne_zero hn hw hU hz hd

end DifferentialGeometry.Analysis

end

end

section

noncomputable section
open Set Filter MeasureTheory
open scoped ContDiff Topology

namespace DifferentialGeometry.Analysis

local notation "V" => EuclideanSpace ℝ (Fin 2)

theorem fderiv_complex_stream_eq_zero_of_fderiv_eq_zero
    {A : V → Matrix (Fin 2) (Fin 2) ℝ} {v s : V → ℝ} {z : ℂ}
    (hv : DifferentiableAt ℝ v (Complex.orthonormalBasisOneI.repr z))
    (hs : HasFDerivAt s (planarFluxForm
      (fun x => DeGiorgi.matMulE (A x) (DeGiorgi.smoothGradField v x))
        (Complex.orthonormalBasisOneI.repr z)) (Complex.orthonormalBasisOneI.repr z))
    (hcrit : fderiv ℝ v (Complex.orthonormalBasisOneI.repr z) = 0) :
    fderiv ℝ (fun w => (v (Complex.orthonormalBasisOneI.repr w) : ℂ) +
      (s (Complex.orthonormalBasisOneI.repr w) : ℂ) * Complex.I) z = 0 := by
  let e := Complex.orthonormalBasisOneI.repr
  have hG : DeGiorgi.smoothGradField v (e z) = 0 := by
    ext i
    change fderiv ℝ v (e z) (EuclideanSpace.single i 1) = 0
    rw [hcrit, zero_apply]
  have hF : planarFluxForm (fun x => DeGiorgi.matMulE (A x)
      (DeGiorgi.smoothGradField v x)) (e z) = 0 := by
    simp only [planarFluxForm, hG, DeGiorgi.matMulE]
    ext x
    simp
  have hs0 : HasFDerivAt s (0 : V →L[ℝ] ℝ) (e z) := hF ▸ hs
  have hv0 : HasFDerivAt v (0 : V →L[ℝ] ℝ) (e z) := hcrit ▸ hv.hasFDerivAt
  have he := e.toContinuousLinearEquiv.hasFDerivAt (x := z)
  have hvC := (Complex.ofRealCLM.hasFDerivAt.comp (e z) hv0).comp z he
  have hsC := (Complex.ofRealCLM.hasFDerivAt.comp (e z) hs0).comp z he
  have hh := (hvC.add (hsC.mul_const Complex.I)).fderiv
  change fderiv ℝ (fun w => (v (e w) : ℂ) + (s (e w) : ℂ) * Complex.I) z = _ at hh
  simpa only [ContinuousLinearMap.comp_zero, ContinuousLinearMap.zero_comp,
    smul_zero, add_zero] using hh

theorem not_constant_complex_stream_of_coordinate_boundary
    {R : ℝ} (hR : 0 < R) {v s : V → ℝ}
    (hc : ContinuousOn v (Metric.closedBall (0 : V) R))
    (hbd : ∀ x ∈ Metric.sphere (0 : V) R, v x = x 0) :
    ¬ ∃ c : ℂ, EqOn (fun z => (v (Complex.orthonormalBasisOneI.repr z) : ℂ) +
      (s (Complex.orthonormalBasisOneI.repr z) : ℂ) * Complex.I)
        (fun _ => c) (Metric.ball (0 : ℂ) R) := by
  rintro ⟨c, heq⟩
  let e := Complex.orthonormalBasisOneI.repr
  have hvconst : EqOn v (fun _ => c.re) (Metric.ball (0 : V) R) := by
    intro y hy
    have heym : e.symm y ∈ Metric.ball (0 : ℂ) R := by simpa using hy
    have hh := congrArg Complex.re (heq heym)
    simpa only [← show e = Complex.orthonormalBasisOneI.repr from rfl,
      LinearIsometryEquiv.apply_symm_apply, Complex.add_re, Complex.mul_re,
      Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im, mul_zero,
      zero_mul, sub_self, add_zero] using hh
  have hvclosed : EqOn v (fun _ => c.re) (Metric.closedBall (0 : V) R) :=
    hvconst.of_subset_closure hc continuousOn_const Metric.ball_subset_closedBall
      (by rw [closure_ball (0 : V) hR.ne'])
  have hp : EuclideanSpace.single (0 : Fin 2) R ∈ Metric.sphere (0 : V) R := by
    simp [Real.norm_eq_abs, abs_of_pos hR]
  have hn : EuclideanSpace.single (0 : Fin 2) (-R) ∈ Metric.sphere (0 : V) R := by
    simp [Real.norm_eq_abs, abs_of_pos hR]
  have hp' := (hvclosed (Metric.sphere_subset_closedBall hp)).symm.trans (hbd _ hp)
  have hn' := (hvclosed (Metric.sphere_subset_closedBall hn)).symm.trans (hbd _ hn)
  simp only [PiLp.single_apply, if_true] at hp' hn'
  linarith

end DifferentialGeometry.Analysis

end

end
