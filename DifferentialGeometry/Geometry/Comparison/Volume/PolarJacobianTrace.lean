import DifferentialGeometry.Geometry.Comparison.Volume.PolarJacobianJets
import Mathlib.Analysis.Calculus.IteratedDeriv.FaaDiBruno

set_option autoImplicit false

noncomputable section

open Set Function Filter Bundle Manifold Matrix
open scoped Topology Manifold ContDiff BigOperators

namespace DifferentialGeometry.Geometry.Riemannian.VolumeComparison

open DifferentialGeometry
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Geometry.Riemannian
open DifferentialGeometry.Geometry.Riemannian.Exponential
open DifferentialGeometry.Geometry.Riemannian.NormalCoordinates

theorem iteratedDeriv_two_sqrt_det_of_first_zero
    {n : ℕ}
    (G B : ℝ → Matrix (Fin n) (Fin n) ℝ)
    (C : Matrix (Fin n) (Fin n) ℝ)
    (hG : ∀ i j, ContDiff ℝ ∞ (fun t ↦ G t i j))
    (hGB : ∀ t i j, HasDerivAt (fun s ↦ G s i j) (B t i j) t)
    (hBC : ∀ i j, HasDerivAt (fun t ↦ B t i j) (C i j) 0)
    (hG0 : G 0 = 1) (hB0 : B 0 = 0) :
    iteratedDeriv 2 (fun t ↦ Real.sqrt (G t).det) 0 =
      (1 / 2 : ℝ) * Matrix.trace C := by
  classical
  have hdet (t : ℝ) : HasDerivAt (fun s ↦ (G s).det)
      (Matrix.trace ((G t).adjugate * B t)) t :=
    DifferentialGeometry.Integral.Measure.hasDerivAt_det_eq_trace_adjugate_mul
      G (B t) t (hGB t)
  have hdet_deriv : deriv (fun t ↦ (G t).det) =
      fun t ↦ Matrix.trace ((G t).adjugate * B t) := by
    funext t
    exact (hdet t).deriv
  have hadj : ∀ i j, DifferentiableAt ℝ (fun t ↦ (G t).adjugate i j) 0 := by
    intro i j
    exact (DifferentialGeometry.Analysis.contDiff_adjugate_of_entries G hG i j).differentiable
      (by simp) 0
  have htrace : HasDerivAt
      (fun t ↦ Matrix.trace ((G t).adjugate * B t))
      (Matrix.trace C) 0 := by
    simp only [Matrix.trace, Matrix.mul_apply, Matrix.diag_apply]
    have houter : ∀ i ∈ (Finset.univ : Finset (Fin n)), HasDerivAt
        (fun t ↦ ∑ j, (G t).adjugate i j * B t j i) (C i i) 0 := by
      intro i _
      have hinner : ∀ j ∈ (Finset.univ : Finset (Fin n)), HasDerivAt
          (fun t ↦ (G t).adjugate i j * B t j i)
          ((1 : Matrix (Fin n) (Fin n) ℝ) i j * C j i) 0 := by
        intro j _
        have hmul := (hadj i j).hasDerivAt.mul (hBC j i)
        change HasDerivAt (fun t ↦ (G t).adjugate i j * B t j i) _ 0 at hmul
        rw [hG0, hB0] at hmul
        simpa only [Matrix.adjugate_one, Matrix.zero_apply, mul_zero,
          zero_add] using hmul
      have hsum := HasDerivAt.fun_sum hinner
      simpa [Matrix.one_apply] using hsum
    exact HasDerivAt.fun_sum houter
  have hdet_two : iteratedDeriv 2 (fun t ↦ (G t).det) 0 =
      Matrix.trace C := by
    rw [show 2 = 1 + 1 by omega, iteratedDeriv_succ, iteratedDeriv_one,
      hdet_deriv]
    exact htrace.deriv
  have hdet_one : deriv (fun t ↦ (G t).det) 0 = 0 := by
    rw [hdet_deriv]
    change Matrix.trace ((G 0).adjugate * B 0) = 0
    rw [hG0, hB0]
    simp
  have hdet_zero : (G 0).det = 1 := by rw [hG0, Matrix.det_one]
  have hdet_cont : ContDiff ℝ ∞ (fun t ↦ (G t).det) :=
    DifferentialGeometry.Analysis.contDiff_det_of_entries G hG
  have hsqrt : ContDiffAt ℝ 2 Real.sqrt ((G 0).det) := by
    rw [hdet_zero]
    exact Real.contDiffAt_sqrt one_ne_zero
  have hdet_cont_two : ContDiffAt ℝ 2 (fun t ↦ (G t).det) 0 :=
    hdet_cont.contDiffAt.of_le (by decide : (2 : WithTop ℕ∞) ≤ ∞)
  have hcomp := iteratedDeriv_comp_two (g := Real.sqrt)
    (f := fun t ↦ (G t).det) (x := (0 : ℝ)) hsqrt hdet_cont_two
  change iteratedDeriv 2 (Real.sqrt ∘ fun t ↦ (G t).det) 0 = _ at hcomp
  rw [hdet_zero, hdet_one, zero_pow (by norm_num : (2 : ℕ) ≠ 0),
    mul_zero, zero_add, hdet_two] at hcomp
  have hsqrt_deriv : deriv Real.sqrt 1 = (1 / 2 : ℝ) := by
    simpa using (Real.hasDerivAt_sqrt one_ne_zero).deriv
  rw [hsqrt_deriv] at hcomp
  have hfun : (fun t ↦ Real.sqrt (G t).det) =
      Real.sqrt ∘ fun t ↦ (G t).det := rfl
  rw [hfun]
  exact hcomp

variable {E : Type*} [NormedAddCommGroup E]
  [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [I.Boundaryless]
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M] [T2Space M] [T2Space (TangentBundle I M)]
  [SigmaCompactSpace M]
variable [RiemannianBundle (fun x : M ↦ TangentSpace I x)]

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
omit [T2Space (TangentBundle I M)] in
theorem intrinsicFrameGram_radial_hasDerivAt_zero
    [PseudoEMetricSpace M] [IsRiemannianManifold I M] [CompleteSpace M]
    [IsContinuousRiemannianBundle E (fun y : M ↦ TangentSpace I y)]
    (g : SmoothRiemannianMetric I M)
    (hEnorm : IsMetricNorm (I := I) (M := M) g) (p : M) (a : E)
    (i j : Fin (Module.finrank ℝ E)) :
    HasDerivAt
      (fun t : ℝ ↦ intrinsicFrameGram (I := I) g hEnorm p (t • a) i j) 0 0 := by
  have hmetric := intrinsicFrameMetric_contDiff (I := I) g hEnorm p
  have hline := DifferentialGeometry.iteratedDeriv_line
    hmetric.contDiffAt 1 (x := (0 : E)) (v := a)
  have happ := congrArg
    (fun Q : E →L[ℝ] E →L[ℝ] ℝ ↦
      Q ((stdOrthonormalBasis ℝ E) i) ((stdOrthonormalBasis ℝ E) j)) hline
  have hcurve : ContDiff ℝ ∞
      (fun t : ℝ ↦ intrinsicFrameMetric (I := I) g hEnorm p ((0 : E) + t • a)) :=
    hmetric.comp
      ((contDiff_const : ContDiff ℝ ∞ (fun _ : ℝ ↦ (0 : E))).add
        (contDiff_id.smul (contDiff_const : ContDiff ℝ ∞ (fun _ : ℝ ↦ a))))
  have happly := DifferentialGeometry.iteratedDeriv_apply₂
    (x := (0 : ℝ)) hcurve.contDiffAt 1 ((stdOrthonormalBasis ℝ E) i)
      ((stdOrthonormalBasis ℝ E) j)
  have hzero := intrinsicFrameMetric_first_jet_zero (I := I) g hEnorm p a
    ((stdOrthonormalBasis ℝ E) i) ((stdOrthonormalBasis ℝ E) j)
  have hderiv : deriv
      (fun t : ℝ ↦ intrinsicFrameGram (I := I) g hEnorm p (t • a) i j) 0 = 0 := by
    rw [← iteratedDeriv_one]
    simpa only [intrinsicFrameGram, zero_add] using happly.trans (happ.trans hzero)
  have hdiff : DifferentiableAt ℝ
      (fun t : ℝ ↦ intrinsicFrameGram (I := I) g hEnorm p (t • a) i j) 0 := by
    have hcoefficient := intrinsicFrameMetric_apply_contDiff (I := I) g hEnorm p
      ((stdOrthonormalBasis ℝ E) i) ((stdOrthonormalBasis ℝ E) j)
    exact (hcoefficient.comp
      (contDiff_id.smul
        (contDiff_const : ContDiff ℝ ∞ (fun _ : ℝ ↦ a)))).differentiable
          (by simp) 0
  simpa only [hderiv] using hdiff.hasDerivAt

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
omit [T2Space (TangentBundle I M)] in
theorem normalExpJacobian_radial_first_zero
    [PseudoEMetricSpace M] [IsRiemannianManifold I M] [CompleteSpace M]
    [IsContinuousRiemannianBundle E (fun y : M ↦ TangentSpace I y)]
    (g : SmoothRiemannianMetric I M)
    (hEnorm : IsMetricNorm (I := I) (M := M) g) (p : M) (a : E) :
    iteratedDeriv 1
        (fun t : ℝ ↦ normalExpJacobian (I := I) g hEnorm p (t • a)) 0 = 0 := by
  classical
  let G : ℝ → Matrix (Fin (Module.finrank ℝ E))
      (Fin (Module.finrank ℝ E)) ℝ := fun t ↦
    intrinsicFrameGram (I := I) g hEnorm p (t • a)
  have hG0 : G 0 = 1 := by
    simpa only [G, zero_smul] using intrinsicFrameGram_zero (I := I) g hEnorm p
  have hpos : 0 < (G 0).det := by rw [hG0, Matrix.det_one]; norm_num
  have hentries : ∀ i j, HasDerivAt (fun t ↦ G t i j)
      ((0 : Matrix (Fin (Module.finrank ℝ E))
        (Fin (Module.finrank ℝ E)) ℝ) i j) 0 := by
    intro i j
    simpa only [G, Matrix.zero_apply] using
      intrinsicFrameGram_radial_hasDerivAt_zero (I := I) g hEnorm p a i j
  have hJ :=
    DifferentialGeometry.Integral.Measure.hasDerivAt_sqrt_det_eq_half_trace_inv_mul
      G 0 0 hentries hpos
  have hJzero : HasDerivAt (fun t ↦ Real.sqrt (G t).det) 0 0 := by
    simpa only [Matrix.mul_zero, Matrix.trace_zero, mul_zero, zero_mul] using hJ
  have hfun : (fun t : ℝ ↦ normalExpJacobian (I := I) g hEnorm p (t • a)) =
      fun t ↦ Real.sqrt (G t).det := by
    funext t
    exact normalExpJacobian_eq_sqrt_det_intrFrameGram
      (I := I) g hEnorm p (t • a)
  rw [iteratedDeriv_one, hfun]
  exact hJzero.deriv

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
omit [T2Space (TangentBundle I M)] in
theorem normalExpJacobian_radial_two_of_metric_trace
    [PseudoEMetricSpace M] [IsRiemannianManifold I M] [CompleteSpace M]
    [IsContinuousRiemannianBundle E (fun y : M ↦ TangentSpace I y)]
    (g : SmoothRiemannianMetric I M)
    (hEnorm : IsMetricNorm (I := I) (M := M) g) (p : M) (a : E)
    (htrace :
      ∑ i : Fin (Module.finrank ℝ E),
          iteratedDeriv 2
            (fun t : ℝ ↦ intrinsicFrameMetric (I := I) g hEnorm p (t • a)
              ((stdOrthonormalBasis ℝ E) i) ((stdOrthonormalBasis ℝ E) i)) 0 =
        -(2 / 3 : ℝ) * ricciTensor (I := I) g p
          (normalFrame (I := I) g p a) (normalFrame (I := I) g p a)) :
    iteratedDeriv 2
        (fun t : ℝ ↦ normalExpJacobian (I := I) g hEnorm p (t • a)) 0 =
      -(1 / 3 : ℝ) * ricciTensor (I := I) g p
        (normalFrame (I := I) g p a) (normalFrame (I := I) g p a) := by
  classical
  let G : ℝ → Matrix (Fin (Module.finrank ℝ E))
      (Fin (Module.finrank ℝ E)) ℝ := fun t ↦
    intrinsicFrameGram (I := I) g hEnorm p (t • a)
  let B : ℝ → Matrix (Fin (Module.finrank ℝ E))
      (Fin (Module.finrank ℝ E)) ℝ := fun t i j ↦
    deriv (fun s ↦ G s i j) t
  let C : Matrix (Fin (Module.finrank ℝ E))
      (Fin (Module.finrank ℝ E)) ℝ := fun i j ↦
    iteratedDeriv 2 (fun t ↦ G t i j) 0
  have hG : ∀ i j, ContDiff ℝ ∞ (fun t ↦ G t i j) := by
    intro i j
    have hmetric := intrinsicFrameMetric_apply_contDiff (I := I) g hEnorm p
      ((stdOrthonormalBasis ℝ E) i) ((stdOrthonormalBasis ℝ E) j)
    have hcomp := hmetric.comp
      (contDiff_id.smul (contDiff_const : ContDiff ℝ ∞ (fun _ : ℝ ↦ a)))
    convert hcomp using 1 <;> rfl
  have hGB : ∀ t i j, HasDerivAt (fun s ↦ G s i j) (B t i j) t := by
    intro t i j
    exact ((hG i j).differentiable (by simp) t).hasDerivAt
  have hBC : ∀ i j, HasDerivAt (fun t ↦ B t i j) (C i j) 0 := by
    intro i j
    have hd : Differentiable ℝ (iteratedDeriv 1 (fun t ↦ G t i j)) :=
      (hG i j).differentiable_iteratedDeriv 1 (by simp)
    rw [iteratedDeriv_one] at hd
    have h := (hd 0).hasDerivAt
    change HasDerivAt (deriv (fun t ↦ G t i j))
      (iteratedDeriv 2 (fun t ↦ G t i j) 0) 0
    rw [show 2 = 1 + 1 by omega, iteratedDeriv_succ, iteratedDeriv_one]
    exact h
  have hG0 : G 0 = 1 := by
    simpa only [G, zero_smul] using intrinsicFrameGram_zero (I := I) g hEnorm p
  have hB0 : B 0 = 0 := by
    ext i j
    change deriv (fun s ↦ G s i j) 0 = 0
    simpa only [G] using
      (intrinsicFrameGram_radial_hasDerivAt_zero (I := I) g hEnorm p a i j).deriv
  have hmain := iteratedDeriv_two_sqrt_det_of_first_zero G B C hG hGB hBC hG0 hB0
  have hCtrace : Matrix.trace C =
      -(2 / 3 : ℝ) * ricciTensor (I := I) g p
        (normalFrame (I := I) g p a) (normalFrame (I := I) g p a) := by
    change (∑ i, C i i) = _
    simpa only [C, G, intrinsicFrameGram] using htrace
  have hJfun : (fun t : ℝ ↦ normalExpJacobian (I := I) g hEnorm p (t • a)) =
      fun t ↦ Real.sqrt (G t).det := by
    funext t
    exact normalExpJacobian_eq_sqrt_det_intrFrameGram
      (I := I) g hEnorm p (t • a)
  rw [hJfun, hmain, hCtrace]
  ring

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
omit [T2Space (TangentBundle I M)] in
theorem normalExpJacobian_radial_two_of_intrinsicMetricJet_trace
    [PseudoEMetricSpace M] [IsRiemannianManifold I M] [CompleteSpace M]
    [IsContinuousRiemannianBundle E (fun y : M ↦ TangentSpace I y)]
    (g : SmoothRiemannianMetric I M)
    (hEnorm : IsMetricNorm (I := I) (M := M) g) (p : M) (a : E)
    (htrace :
      ∑ i : Fin (Module.finrank ℝ E),
          intrinsicMetricJet (I := I) g hEnorm p
            (tangentSpaceModelContinuousLinearEquiv (I := I) p
              (normalFrame (I := I) g p 0))
            (tangentSpaceModelContinuousLinearEquiv (I := I) p
              (normalFrame (I := I) g p a))
            (tangentSpaceModelContinuousLinearEquiv (I := I) p
              (normalFrame (I := I) g p ((stdOrthonormalBasis ℝ E) i))) 2 0 =
        -(2 / 3 : ℝ) * ricciTensor (I := I) g p
          (normalFrame (I := I) g p a) (normalFrame (I := I) g p a)) :
    iteratedDeriv 2
        (fun t : ℝ ↦ normalExpJacobian (I := I) g hEnorm p (t • a)) 0 =
      -(1 / 3 : ℝ) * ricciTensor (I := I) g p
        (normalFrame (I := I) g p a) (normalFrame (I := I) g p a) := by
  apply normalExpJacobian_radial_two_of_metric_trace (I := I) g hEnorm p a
  rw [← htrace]
  apply Finset.sum_congr rfl
  intro i _
  let ei : E := (stdOrthonormalBasis ℝ E) i
  have hmetric := intrinsicFrameMetric_contDiff (I := I) g hEnorm p
  have hline := DifferentialGeometry.iteratedDeriv_line
    hmetric.contDiffAt 2 (x := (0 : E)) (v := a)
  have happ := congrArg (fun Q : E →L[ℝ] E →L[ℝ] ℝ ↦ Q ei ei) hline
  have hcurve : ContDiff ℝ ∞
      (fun t : ℝ ↦ intrinsicFrameMetric (I := I) g hEnorm p ((0 : E) + t • a)) :=
    hmetric.comp
      ((contDiff_const : ContDiff ℝ ∞ (fun _ : ℝ ↦ (0 : E))).add
        (contDiff_id.smul (contDiff_const : ContDiff ℝ ∞ (fun _ : ℝ ↦ a))))
  have happly := DifferentialGeometry.iteratedDeriv_apply₂
    (x := (0 : ℝ)) hcurve.contDiffAt 2 ei ei
  have hdiag := intrinsicFrameMetric_diag_jet (I := I) g hEnorm p 0 a ei 2
  simpa only [zero_add, ei] using happly.trans (happ.trans hdiag)

end DifferentialGeometry.Geometry.Riemannian.VolumeComparison
