import DifferentialGeometry.Geometry.Curvature.DimensionThree.HamiltonIveyRegion
import DifferentialGeometry.Geometry.Flow.RicciFlow.Evolution.RicciPinchingPreservation
import DifferentialGeometry.Geometry.Flow.RicciFlow.Evolution.UhlenbeckCurvatureOperatorHeatReaction
import Mathlib.Analysis.SpecialFunctions.Exp

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace DifferentialGeometry.PDE.RicciFlow

open Bundle Tensor0SBundle
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Geometry.Curvature.DimensionThree
open DifferentialGeometry.Geometry.Operator
open scoped Manifold ContDiff

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace Real E]
variable [FiniteDimensional Real E]
variable {H : Type*} [TopologicalSpace H]
variable {I : ModelWithCorners Real E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
variable [IsManifold I ∞ M] [SigmaCompactSpace M] [T2Space M]

def hamiltonIveySupportCoefficient (K a t0 t : Real) : Real :=
  K * Real.exp (a + 2) / (a * (1 + 2 * K * (t - t0)))

noncomputable def hamiltonIveySupportUpperSec
    {D : DifferentialGeometry.Geometry.Curvature.RealTimeInterval}
    (S : SolutionOn (I := I) (M := M) D) (K a t0 : Real) :
    TwoTensorSecFamily (I := I) (M := M) :=
  fun t =>
    hamiltonIveySupportCoefficient K a t0 t • metricTensorField (I := I) (S.base.metric t) -
      pinchSec (I := I) S ((1 + a) / (2 * a)) t

theorem hamiltonIveySupportUpperSec_at_point
    {D : DifferentialGeometry.Geometry.Curvature.RealTimeInterval}
    (S : SolutionOn (I := I) (M := M) D) (K a t0 t : Real) (x : M) :
    (hamiltonIveySupportUpperSec (I := I) (M := M) S K a t0) t x =
      hamiltonIveySupportCoefficient K a t0 t • metricTensorField (I := I) (S.base.metric t) x -
        pinchSec (I := I) S ((1 + a) / (2 * a)) t x := by
  rfl

noncomputable def hamiltonIveySupportUpperNablaModel
    {D : DifferentialGeometry.Geometry.Curvature.RealTimeInterval}
    [CompleteSpace E] [SigmaCompactSpace M] [T2Space M]
    (S : SolutionOn (I := I) (M := M) D) (a : Real) :
    TensorNabla1SecFamily (I := I) (M := M) :=
  fun t => -pinchNablaModel (I := I) S ((1 + a) / (2 * a)) t

noncomputable def hamiltonIveySupportUpperNab2ModelSec
    {D : DifferentialGeometry.Geometry.Curvature.RealTimeInterval}
    [CompleteSpace E] [SigmaCompactSpace M] [T2Space M]
    (S : SolutionOn (I := I) (M := M) D) (a : Real) :
    TensorNabla2SecFamily (I := I) (M := M) :=
  fun t => -pinchNab2ModelSec (I := I) S ((1 + a) / (2 * a)) t

theorem hamiltonIveySupportUpperSec_symm
    {D : DifferentialGeometry.Geometry.Curvature.RealTimeInterval}
    (S : SolutionOn (I := I) (M := M) D) (K a t0 : Real) (U : Set Real) :
    TwoTensorFamilySymmetricOn (I := I) (M := M)
      (twoTensorSecToFamily (I := I) (M := M)
        (hamiltonIveySupportUpperSec (I := I) (M := M) S K a t0)) U := by
  intro t _ht x v w
  have hpinch := pinchSec_symm (I := I) S ((1 + a) / (2 * a)) U t _ht x v w
  have hpinch_pt : ((pinchSec (I := I) S ((1 + a) / (2 * a)) t) x)
        (DifferentialGeometry.Geometry.Curvature.vec2 (I := I) v w) =
      ((pinchSec (I := I) S ((1 + a) / (2 * a)) t) x)
        (DifferentialGeometry.Geometry.Curvature.vec2 (I := I) w v) := by
    simpa [twoTensorSecToFamily_apply] using hpinch
  have hg := (S.base.metric t).symm x v w
  rw [twoTensorSecToFamily_apply (I := I) (M := M)
      (hamiltonIveySupportUpperSec (I := I) (M := M) S K a t0) t x v w,
    twoTensorSecToFamily_apply (I := I) (M := M)
      (hamiltonIveySupportUpperSec (I := I) (M := M) S K a t0) t x w v]
  unfold hamiltonIveySupportUpperSec hamiltonIveySupportCoefficient
  simp only [ContMDiffSection.coe_sub, Pi.sub_apply, ContMDiffSection.coe_smul,
    Pi.smul_apply]
  rw [Tensor0SSpace.sub_apply, Tensor0SSpace.sub_apply]
  rw [Tensor0SSpace.smul_apply, Tensor0SSpace.smul_apply]
  rw [hpinch_pt]
  simp only [metricTensorField_apply, Fin.isValue, smul_eq_mul]
  rw [show DifferentialGeometry.Geometry.Curvature.vec2 (I := I) v w 0 = v by rfl,
    show DifferentialGeometry.Geometry.Curvature.vec2 (I := I) v w 1 = w by rfl,
    show DifferentialGeometry.Geometry.Curvature.vec2 (I := I) w v 0 = w by rfl,
    show DifferentialGeometry.Geometry.Curvature.vec2 (I := I) w v 1 = v by rfl]
  rw [hg]

theorem hamiltonIveySupportCoefficient_pos
    {K a t0 t : Real} (hK : 0 < K) (ha : 0 < a) (ht : 0 ≤ t - t0) :
    0 < hamiltonIveySupportCoefficient K a t0 t := by
  unfold hamiltonIveySupportCoefficient
  have hden : 0 < 1 + 2 * K * (t - t0) := by
    nlinarith [mul_nonneg (mul_pos two_pos hK).le ht]
  positivity

def hamiltonIveySupportCoefficientDeriv (K a t0 t : Real) : Real :=
  -2 * K * hamiltonIveySupportCoefficient K a t0 t / (1 + 2 * K * (t - t0))

theorem hamiltonIveySupportCoefficient_hasDerivAt
    {K a t0 t : Real} (hK : 0 < K) (ha : 0 < a) (ht : 0 ≤ t - t0) :
    HasDerivAt (fun s : Real => hamiltonIveySupportCoefficient K a t0 s)
      (hamiltonIveySupportCoefficientDeriv K a t0 t) t := by
  have hid : HasDerivAt (fun s : Real => s) (1 : Real) t := hasDerivAt_id t
  have hconst : HasDerivAt (fun _s : Real => t0) (0 : Real) t :=
    (hasDerivAt_const (c := t0) (x := t))
  have hlin_raw : HasDerivAt ((fun s : Real => s) - fun _s : Real => t0) (1 - 0) t :=
    hid.sub hconst
  have hlin : HasDerivAt (fun s : Real => s - t0) (1 : Real) t := by
    exact hlin_raw.congr_deriv (by norm_num)
  have hD : HasDerivAt (fun s : Real => 1 + 2 * K * (s - t0)) (2 * K) t := by
    simpa [two_mul, mul_add, add_comm, add_left_comm, add_assoc] using
      (hlin.const_mul (2 * K)).const_add 1
  have hD_ne : 1 + 2 * K * (t - t0) ≠ 0 := by
    have hden : 0 < 1 + 2 * K * (t - t0) := by
      nlinarith [mul_nonneg (mul_pos two_pos hK).le ht]
    exact ne_of_gt hden
  have hquot_raw :
      HasDerivAt ((fun _s : Real => K * Real.exp (a + 2)) /
        fun s : Real => a * (1 + 2 * K * (s - t0)))
        (-((K * Real.exp (a + 2)) * (a * (2 * K))) /
          (a * (1 + 2 * K * (t - t0))) ^ 2) t := by
    have hnum : HasDerivAt (fun _s : Real => K * Real.exp (a + 2))
        (0 : Real) t := (hasDerivAt_const (c := K * Real.exp (a + 2)) (x := t))
    have hden : HasDerivAt (fun s : Real => a * (1 + 2 * K * (s - t0)))
        (a * (2 * K)) t := hD.const_mul a
    have hden_ne : a * (1 + 2 * K * (t - t0)) ≠ 0 := by
      exact mul_ne_zero ha.ne' hD_ne
    have hquot0 := hnum.div hden hden_ne
    have hderiv0 : (0 * (a * (1 + 2 * K * (t - t0))) -
        (K * Real.exp (a + 2)) * (a * (2 * K))) /
        (a * (1 + 2 * K * (t - t0))) ^ 2 =
        -((K * Real.exp (a + 2)) * (a * (2 * K))) /
          (a * (1 + 2 * K * (t - t0))) ^ 2 := by ring
    exact hquot0.congr_deriv hderiv0
  have hderiv :
      -((K * Real.exp (a + 2)) * (a * (2 * K))) /
          (a * (1 + 2 * K * (t - t0))) ^ 2 =
        hamiltonIveySupportCoefficientDeriv K a t0 t := by
    unfold hamiltonIveySupportCoefficientDeriv hamiltonIveySupportCoefficient
    field_simp [ha.ne', hD_ne]
  change HasDerivAt ((fun _s : Real => K * Real.exp (a + 2)) /
    fun s : Real => a * (1 + 2 * K * (s - t0)))
    (hamiltonIveySupportCoefficientDeriv K a t0 t) t
  exact hquot_raw.congr_deriv hderiv

def hamiltonIveySupportPinchDelta (a : Real) : Real :=
  (1 + a) / (2 * a)

def hamiltonIveySupportUpperMissingPlaneIndex (i : Fin 3) : Fin 3 :=
  if i = 0 then 2 else if i = 1 then 1 else 0

def hamiltonIveySupportUpperDiagNormal (a delta : Real) (i : Fin 3) :
    Matrix (Fin 3) (Fin 3) Real :=
  Matrix.diagonal (fun j : Fin 3 =>
    if j = hamiltonIveySupportUpperMissingPlaneIndex i then -a * (2 * delta)
    else a * (1 - 2 * delta))

private lemma sum_diag_eq
    (f : Fin 3 × Fin 3 → Real) :
    (∑ x : Fin 3 × Fin 3, if x.1 = x.2 then f x else 0) =
      ∑ i : Fin 3, f (i, i) := by
  classical
  let s : Finset (Fin 3 × Fin 3) := Finset.univ.filter (fun x => x.1 = x.2)
  have hfilter : (∑ x : Fin 3 × Fin 3, if x.1 = x.2 then f x else 0) =
      ∑ x ∈ s, f x := by
    rw [Finset.sum_filter]
  rw [hfilter]
  symm
  refine Finset.sum_bij (s := Finset.univ) (t := s)
    (fun i hi => (i, i))
    (by intro i hi; simp [s])
    (by intro i hi j hj h; exact congrArg Prod.fst h)
    (by
      intro x hx
      have hx' : x ∈ Finset.univ.filter (fun x => x.1 = x.2) := by simpa [s] using hx
      rw [Finset.mem_filter] at hx'
      refine ⟨x.1, by simp, ?_⟩
      exact Prod.ext rfl hx'.2)
    (by intro i hi; rfl)

theorem inner_hamiltonIveySupportUpperDiagNormal_full_eq_diag
    (a delta : Real) (i : Fin 3) (A : Matrix (Fin 3) (Fin 3) Real) :
    inner ℝ (matrixToEuclid (hamiltonIveySupportUpperDiagNormal a delta i))
      (matrixToEuclid A) =
    inner ℝ (matrixToEuclid (hamiltonIveySupportUpperDiagNormal a delta i))
      (matrixToEuclid (Matrix.diagonal (fun j => A j j))) := by
  classical
  rw [inner_matrixToEuclid, inner_matrixToEuclid]
  simp only [matrixToEuclid, hamiltonIveySupportUpperDiagNormal, Matrix.diagonal,
    Matrix.of_apply, WithLp.ofLp_toLp, ite_mul, mul_ite, mul_zero, zero_mul]
  rw [sum_diag_eq, sum_diag_eq]
  simp only [↓reduceIte]

theorem inner_hamiltonIveySupportUpperDiagNormal_diag
    (a delta : Real) (i : Fin 3) (d : Fin 3 → Real) :
    inner ℝ (matrixToEuclid (hamiltonIveySupportUpperDiagNormal a delta i))
      (matrixToEuclid (Matrix.diagonal d)) =
      a * ((1 - 2 * delta) *
            (∑ j : Fin 3, if j = hamiltonIveySupportUpperMissingPlaneIndex i then 0 else d j) -
          2 * delta * d (hamiltonIveySupportUpperMissingPlaneIndex i)) := by
  classical
  rw [inner_matrixToEuclid]
  simp only [matrixToEuclid, hamiltonIveySupportUpperDiagNormal, Matrix.diagonal,
    Matrix.of_apply, WithLp.ofLp_toLp, ite_mul, mul_ite, mul_zero, zero_mul]
  rw [sum_diag_eq]
  fin_cases i <;> simp only [Fin.sum_univ_three, hamiltonIveySupportUpperMissingPlaneIndex] <;>
    norm_num <;> simp only [Fin.reduceEq, ↓reduceIte] <;> ring

theorem hamiltonIveySupportPinchDelta_den_ne
    {a : Real} (ha : 0 < a) :
    1 - 3 * hamiltonIveySupportPinchDelta a ≠ 0 := by
  unfold hamiltonIveySupportPinchDelta
  have hcalc : 1 - 3 * ((1 + a) / (2 * a)) = -(a + 3) / (2 * a) := by
    field_simp [ha.ne']
    ring
  rw [hcalc]
  exact div_ne_zero (by nlinarith) (by positivity)

variable [IsManifold I 1 M] [IsManifold I 2 M]

omit [IsManifold I 2 M] in
theorem hamiltonIveySupportUpperSec_eval_ricciEigen
    {D : DifferentialGeometry.Geometry.Curvature.RealTimeInterval}
    (S : SolutionOn (I := I) (M := M) D)
    {K a t0 t : Real} {x : M}
    {basis : Module.Basis (Fin 3) Real (TangentSpace I x)}
    {l1 l2 l3 : Real} (ha : 0 < a)
    (horth : OrthonormalBasisAt (I := I) (S.base.metric t) x basis)
    (hdiag : RicciDiagAt (I := I) (S.ricci t x) (l1 + l2 + l3) l1 l2 l3 basis) :
    a * twoTensorSecToFamily (I := I) (M := M)
        (hamiltonIveySupportUpperSec (I := I) (M := M) S K a t0) t x
        (basis 0) (basis 0) =
      DifferentialGeometry.Geometry.Curvature.DimensionThree.hamiltonIveySupportEigenGap K (t - t0) a
        ((l1 + l2 + l3) / 2 - l1) ((l1 + l2 + l3) / 2) := by
  classical
  rw [twoTensorSecToFamily_apply]
  rw [hamiltonIveySupportUpperSec_at_point (I := I) S K a t0 t x]
  rcases hdiag with ⟨hscalar_diag, hric⟩
  have hric00 : (S.ricci t x) (vec2 (I := I) (basis 0) (basis 0)) = l1 := by
    have h00 := hric 0 0
    simpa [ricciCompAt_apply, ricciDiag3] using h00
  have hric11 : (S.ricci t x) (vec2 (I := I) (basis 1) (basis 1)) = l2 := by
    have h11 := hric 1 1
    simpa [ricciCompAt_apply, ricciDiag3] using h11
  have hric22 : (S.ricci t x) (vec2 (I := I) (basis 2) (basis 2)) = l3 := by
    have h22 := hric 2 2
    simpa [ricciCompAt_apply, ricciDiag3] using h22
  have hmetric00 :
      (S.base.metric t).inner x (basis 0) (basis 0) = 1 := by
    simpa [DifferentialGeometry.Geometry.Curvature.delta3] using horth 0 0
  have hscalar_trace :
      metricTracePair0SAt (I := I) (S.base.metric t) (S.ricci t x) = l1 + l2 + l3 := by
    rw [metricTrace_comp_orthonormal (I := I) (M := M) basis horth (S.ricci t x)]
    unfold ricciScal3
    simp only [Fin.sum_univ_three]
    rw [hric00, hric11, hric22]
  have hpinch_eval : (pinchSec (I := I) S ((1 + a) / (2 * a)) t x)
      (DifferentialGeometry.Geometry.Curvature.vec2 (I := I) (basis 0) (basis 0)) =
      l1 - (hamiltonIveySupportPinchDelta a) * (l1 + l2 + l3) := by
    rw [pinchSec_at_trace (I := I) (M := M) S ((1 + a) / (2 * a)) t x]
    rw [Tensor0SSpace.sub_apply]
    rw [Tensor0SSpace.smul_apply]
    simp only [metricTensorField_apply, Fin.isValue, smul_eq_mul]
    rw [show DifferentialGeometry.Geometry.Curvature.vec2 (I := I) (basis 0) (basis 0) 0 =
        basis 0 by rfl]
    rw [show DifferentialGeometry.Geometry.Curvature.vec2 (I := I) (basis 0) (basis 0) 1 =
        basis 0 by rfl]
    rw [hric00, hmetric00, hscalar_trace]
    unfold hamiltonIveySupportPinchDelta
    field_simp [ha.ne']
  have hmain_eval :
      ((hamiltonIveySupportCoefficient K a t0 t •
          metricTensorField (I := I) (S.base.metric t) x -
        pinchSec (I := I) S ((1 + a) / (2 * a)) t x)
        (DifferentialGeometry.Geometry.Curvature.vec2 (I := I) (basis 0) (basis 0))) =
        hamiltonIveySupportCoefficient K a t0 t -
          (l1 - (hamiltonIveySupportPinchDelta a) * (l1 + l2 + l3)) := by
    rw [Tensor0SSpace.sub_apply]
    rw [Tensor0SSpace.smul_apply]
    simp only [metricTensorField_apply, Fin.isValue, smul_eq_mul]
    rw [show DifferentialGeometry.Geometry.Curvature.vec2 (I := I) (basis 0) (basis 0) 0 =
        basis 0 by rfl]
    rw [show DifferentialGeometry.Geometry.Curvature.vec2 (I := I) (basis 0) (basis 0) 1 =
        basis 0 by rfl]
    rw [hmetric00, hpinch_eval]
    ring
  rw [hmain_eval]
  unfold DifferentialGeometry.Geometry.Curvature.DimensionThree.hamiltonIveySupportEigenGap
    hamiltonIveySupportCoefficient hamiltonIveySupportPinchDelta
  field_simp [ha.ne']
  ring

noncomputable def hamiltonIveySupportUpperReactAt
    (K a t0 t : Real) (g : SmoothRiemannianMetric I M) {x : M}
    (A : Tensor02At (I := I) (M := M) x) :
    Tensor02At (I := I) (M := M) x :=
  let c : Real := hamiltonIveySupportCoefficient K a t0 t
  let cder : Real := hamiltonIveySupportCoefficientDeriv K a t0 t
  let delta : Real := hamiltonIveySupportPinchDelta a
  let Q : Tensor02At (I := I) (M := M) x :=
    c • metricTensorField (I := I) g x - A
  let Ric : Tensor02At (I := I) (M := M) x :=
    shiftRic3At (I := I) (M := M) delta g Q
  cder • metricTensorField (I := I) g x - (2 * c) • Ric -
    shiftNAt (I := I) (M := M) delta t g x Q

noncomputable def hamiltonIveySupportUpperReact
    (K a t0 : Real) : TwoTensorReaction (I := I) (M := M) :=
  Tensor02ReactionAt.toRawSymm (I := I) (M := M)
    (fun t g _x A => hamiltonIveySupportUpperReactAt (I := I) K a t0 t g A)

omit [IsManifold I 2 M] in
private theorem hamiltonIveySupportUpperReactAt_of_solution
    {D : DifferentialGeometry.Geometry.Curvature.RealTimeInterval}
    (S : SolutionOn (I := I) (M := M) D)
    {K a t0 t : Real} {x : M} (ha : 0 < a)
    (hdim : Module.finrank Real (TangentSpace I x) = 3) :
    hamiltonIveySupportUpperReactAt (I := I) K a t0 t (S.base.metric t)
        ((hamiltonIveySupportUpperSec (I := I) (M := M) S K a t0) t x) =
      hamiltonIveySupportCoefficientDeriv K a t0 t •
          metricTensorField (I := I) (S.base.metric t) x -
        (2 * hamiltonIveySupportCoefficient K a t0 t) • S.ricci t x -
        shiftNAt (I := I) (M := M) (hamiltonIveySupportPinchDelta a) t
          (S.base.metric t) x (pinchSec (I := I) S (hamiltonIveySupportPinchDelta a) t x) := by
  unfold hamiltonIveySupportUpperReactAt
  simp only [hamiltonIveySupportUpperSec, ContMDiffSection.coe_sub, Pi.sub_apply,
    ContMDiffSection.coe_smul, Pi.smul_apply]
  change hamiltonIveySupportCoefficientDeriv K a t0 t •
        metricTensorField (I := I) (S.base.metric t) x -
      (2 * hamiltonIveySupportCoefficient K a t0 t) •
        shiftRic3At (I := I) (M := M) (hamiltonIveySupportPinchDelta a)
          (S.base.metric t)
          (hamiltonIveySupportCoefficient K a t0 t •
              metricTensorField (I := I) (S.base.metric t) x -
            (hamiltonIveySupportCoefficient K a t0 t •
                metricTensorField (I := I) (S.base.metric t) x -
              pinchSec (I := I) S ((1 + a) / (2 * a)) t x)) -
      shiftNAt (I := I) (M := M) (hamiltonIveySupportPinchDelta a) t
        (S.base.metric t) x
        (hamiltonIveySupportCoefficient K a t0 t •
            metricTensorField (I := I) (S.base.metric t) x -
          (hamiltonIveySupportCoefficient K a t0 t •
              metricTensorField (I := I) (S.base.metric t) x -
            pinchSec (I := I) S ((1 + a) / (2 * a)) t x)) =
    hamiltonIveySupportCoefficientDeriv K a t0 t •
        metricTensorField (I := I) (S.base.metric t) x -
      (2 * hamiltonIveySupportCoefficient K a t0 t) • S.ricci t x -
      shiftNAt (I := I) (M := M) (hamiltonIveySupportPinchDelta a) t
        (S.base.metric t) x (pinchSec (I := I) S (hamiltonIveySupportPinchDelta a) t x)
  have hQ : hamiltonIveySupportCoefficient K a t0 t •
        metricTensorField (I := I) (S.base.metric t) x -
      (hamiltonIveySupportCoefficient K a t0 t •
          metricTensorField (I := I) (S.base.metric t) x -
        pinchSec (I := I) S ((1 + a) / (2 * a)) t x) =
      pinchSec (I := I) S ((1 + a) / (2 * a)) t x := by
    abel
  simp only [hQ]
  have hden : 1 - 3 * hamiltonIveySupportPinchDelta a ≠ 0 :=
    hamiltonIveySupportPinchDelta_den_ne ha
  have hpinch := pinchSec_at_trace (I := I) (M := M) S ((1 + a) / (2 * a)) t x
  rw [hpinch]
  obtain ⟨basis, horth⟩ := exists_orthonormalBasisAt (I := I) (S.base.metric t) x hdim
  have hRic := shiftRic3At_pinch (I := I) (M := M) (δ := (1 + a) / (2 * a))
    (g := S.base.metric t) (x := x) basis horth (by
      have hcalc : 1 - 3 * ((1 + a) / (2 * a)) = -(a + 3) / (2 * a) := by
        field_simp [ha.ne']
        ring
      rw [hcalc]
      exact div_ne_zero (by nlinarith) (by positivity)) (S.ricci t x)
  simp only [hamiltonIveySupportPinchDelta, hRic]
  change hamiltonIveySupportCoefficientDeriv K a t0 t •
        metricTensorField (I := I) (S.base.metric t) x -
      (2 * hamiltonIveySupportCoefficient K a t0 t) • S.ricci t x -
      shiftNAt (I := I) (M := M) (hamiltonIveySupportPinchDelta a) t
        (S.base.metric t) x
        ((S.ricci t) x -
          ((1 + a) / (2 * a) *
              Geometry.Operator.metricTracePair0SAt (I := I) (S.base.metric t)
                (S.ricci t x)) •
            metricTensorField (I := I) (S.base.metric t) x) =
    hamiltonIveySupportCoefficientDeriv K a t0 t •
        metricTensorField (I := I) (S.base.metric t) x -
      (2 * hamiltonIveySupportCoefficient K a t0 t) • S.ricci t x -
      shiftNAt (I := I) (M := M) (hamiltonIveySupportPinchDelta a) t
        (S.base.metric t) x (pinchSec (I := I) S (hamiltonIveySupportPinchDelta a) t x)
  simp only [hamiltonIveySupportPinchDelta, hpinch]

omit [IsManifold I 2 M] in
private theorem hamiltonIveySupportUpperReact_eval
    {D : DifferentialGeometry.Geometry.Curvature.RealTimeInterval}
    (S : SolutionOn (I := I) (M := M) D)
    (K a t0 t : Real) (x : M) (v w : TangentSpace I x) :
    (hamiltonIveySupportUpperReact (I := I) (M := M) K a t0 t (S.base.metric t)
        (twoTensorSecToFamily (I := I) (M := M)
          (hamiltonIveySupportUpperSec (I := I) (M := M) S K a t0) t)) x v w =
      hamiltonIveySupportUpperReactAt (I := I) K a t0 t (S.base.metric t)
        ((hamiltonIveySupportUpperSec (I := I) (M := M) S K a t0) t x)
        (vec2 (I := I) v w) := by
  let Araw : RawTwoTensorField (I := I) (M := M) :=
    twoTensorSecToFamily (I := I) (M := M)
      (hamiltonIveySupportUpperSec (I := I) (M := M) S K a t0) t
  have hbilin : TwoTensorBilinearAt (I := I) (M := M) Araw x := by
    simpa [Araw] using
      twoTensorSecToFamily_bilin (I := I) (M := M)
        (hamiltonIveySupportUpperSec (I := I) (M := M) S K a t0) t x
  have hsym : TwoTensorSymmetricAt (I := I) (M := M) Araw x := by
    simpa [Araw] using
      (hamiltonIveySupportUpperSec_symm (I := I) S K a t0 Set.univ) t (by simp) x
  rw [show twoTensorSecToFamily (I := I) (M := M)
      (hamiltonIveySupportUpperSec (I := I) (M := M) S K a t0) t = Araw by rfl]
  rw [hamiltonIveySupportUpperReact, Tensor02ReactionAt.toRawSymm_eval_of_bilin
    (I := I) (M := M)
    (fun t g _x A => hamiltonIveySupportUpperReactAt (I := I) K a t0 t g A)
    t (S.base.metric t) Araw x hbilin]
  have hrealSec : Tensor02RealizesRawAt (I := I) (M := M)
      (rawSym2 (I := I) (M := M) Araw) x
      ((hamiltonIveySupportUpperSec (I := I) (M := M) S K a t0) t x) := by
    intro X Y
    rw [rawSym2_eq_of_symm (I := I) (M := M) hsym X Y]
    rfl
  have hrealBundled : Tensor02RealizesRawAt (I := I) (M := M)
      (rawSym2 (I := I) (M := M) Araw) x
      (tensor02OfRawAt (I := I) (M := M)
        (rawSym2 (I := I) (M := M) Araw) x
        (rawSym2_bilin (I := I) (M := M) hbilin)) :=
    tensor02OfRawAt_realizes (I := I) (M := M)
      (rawSym2 (I := I) (M := M) Araw) x
      (rawSym2_bilin (I := I) (M := M) hbilin)
  have hT : tensor02OfRawAt (I := I) (M := M)
      (rawSym2 (I := I) (M := M) Araw) x
      (rawSym2_bilin (I := I) (M := M) hbilin) =
      (hamiltonIveySupportUpperSec (I := I) (M := M) S K a t0) t x :=
    tensor02_realizes_ext (I := I) (M := M) hrealBundled hrealSec
  rw [hT]

omit [FiniteDimensional ℝ E] [IsManifold I ∞ M] [SigmaCompactSpace M] [T2Space M] [IsManifold I 2 M] in
private theorem real_smul0S_apply {s : ℕ} {x : M} (c : Real)
    (A : Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) s x)
    (v : Fin s → TangentSpace I x) :
    (c • A) v = c * A v := by
  rw [Tensor0SSpace.smul_apply, smul_eq_mul]

omit [FiniteDimensional ℝ E] [SigmaCompactSpace M] [T2Space M] [IsManifold I 1 M] [IsManifold I 2 M] in
private theorem tensor02_zero_apply {x : M}
    (A : Tensor02At (I := I) (M := M) x) :
    A (0 : Fin 2 → TangentSpace I x) = 0 := by
  with_unfolding_all exact A.map_coord_zero (0 : Fin 2) rfl

omit [IsManifold I 2 M] in
private theorem hamiltonIveySupportUpperShiftNAt_eq_pinchCoordReact
    {D : DifferentialGeometry.Geometry.Curvature.RealTimeInterval}
    (S : SolutionOn (I := I) (M := M) D)
    {a t : Real} {x : M} (ha : 0 < a)
    (hdim : Module.finrank Real (TangentSpace I x) = 3)
    (v : TangentSpace I x) :
    shiftNAt (I := I) (M := M) (hamiltonIveySupportPinchDelta a) t
        (S.base.metric t) x (pinchSec (I := I) S (hamiltonIveySupportPinchDelta a) t x)
        (vec2 (I := I) v v) =
      pinchCoordReact (I := I) S (hamiltonIveySupportPinchDelta a) t x v := by
  classical
  by_cases hv : v = 0
  · subst v
    have hvec0 : vec2 (I := I) (0 : TangentSpace I x) 0 =
        (0 : Fin 2 → TangentSpace I x) := by
      funext q
      fin_cases q <;> rfl
    have hric : ricciCoordReact (I := I) S t x 0 = 0 := by
      rw [ricciCoordReact_eq_actual (I := I) S t x 0]
      rw [hvec0]
      have hzero : ricciActualReactAt (I := I) S t x (0 : Fin 2 → TangentSpace I x) = 0 := by
        exact tensor02_zero_apply _
      rw [hzero]
    have hN : shiftNAt (I := I) (M := M) (hamiltonIveySupportPinchDelta a) t
        (S.base.metric t) x (pinchSec (I := I) S (hamiltonIveySupportPinchDelta a) t x)
        (vec2 (I := I) (0 : TangentSpace I x) 0) = 0 := by
      rw [hvec0]
      exact tensor02_zero_apply _
    rw [hN]
    unfold pinchCoordReact
    rw [hric]
    have hRicZero : S.ricciAt t x (vec2 (I := I) (0 : TangentSpace I x) 0) = 0 := by
      rw [hvec0]
      exact tensor02_zero_apply _
    rw [hRicZero]
    simp
  · obtain ⟨nb⟩ := exists_nullOrthonormalBasis3At (I := I) (M := M)
      (S.base.metric t) hdim hv
    have hpinch := pinchSec_at_trace (I := I) (M := M) S (hamiltonIveySupportPinchDelta a) t x
    have hden : 1 - 3 * hamiltonIveySupportPinchDelta a ≠ 0 :=
      hamiltonIveySupportPinchDelta_den_ne ha
    have hshift := shiftNAt_pinch (I := I) (M := M)
      (δ := hamiltonIveySupportPinchDelta a) (t := t) nb.basis nb.orthonormal hden (S.ricci t x)
    have hactual := ricciActualReactAt_eq_reaction3 (I := I) (M := M) S t x
      nb.basis nb.orthonormal
    have hcoord := ricciCoordReact_eq_actual (I := I) S t x v
    rw [hpinch, hshift, ← hactual]
    rw [Tensor0SSpace.sub_apply 2 x (ricciActualReactAt (I := I) S t x)
      ((2 * hamiltonIveySupportPinchDelta a) •
        (inner0S (I := I) (S.base.metric t) x 2 ((S.ricci t) x) ((S.ricci t) x) •
            metricTensorField (I := I) (S.base.metric t) x -
          metricTracePair0SAt (I := I) (S.base.metric t) ((S.ricci t) x) •
            (S.ricci t) x)) (vec2 (I := I) v v)]
    rw [Tensor0SSpace.smul_apply 2 x (2 * hamiltonIveySupportPinchDelta a)
      (inner0S (I := I) (S.base.metric t) x 2 ((S.ricci t) x) ((S.ricci t) x) •
          metricTensorField (I := I) (S.base.metric t) x -
        metricTracePair0SAt (I := I) (S.base.metric t) ((S.ricci t) x) •
          (S.ricci t) x) (vec2 (I := I) v v)]
    rw [← hcoord]
    simp [pinchCoordReact, metricTensorField_apply,
      SolutionOn.scalar_eq_metricTrace, vec2, DifferentialGeometry.Geometry.Curvature.vec2]
    ring

private def hamiltonIveySupportUpperCoordReact
    {D : DifferentialGeometry.Geometry.Curvature.RealTimeInterval}
    (S : SolutionOn (I := I) (M := M) D) (K a t0 t : Real)
    (x : M) (v : TangentSpace I x) : Real :=
  hamiltonIveySupportCoefficientDeriv K a t0 t * (S.base.metric t).inner x v v -
    2 * hamiltonIveySupportCoefficient K a t0 t *
      S.ricciAt t x (vec2 (I := I) v v) -
    pinchCoordReact (I := I) S (hamiltonIveySupportPinchDelta a) t x v

omit [IsManifold I 2 M] in
private theorem hamiltonIveySupportUpperReact_coord_eq
    {D : DifferentialGeometry.Geometry.Curvature.RealTimeInterval}
    (S : SolutionOn (I := I) (M := M) D)
    {K a t0 t : Real} {x : M} (ha : 0 < a)
    (hdim : Module.finrank Real (TangentSpace I x) = 3)
    (v : TangentSpace I x) :
    (hamiltonIveySupportUpperReact (I := I) (M := M) K a t0 t (S.base.metric t)
        (twoTensorSecToFamily (I := I) (M := M)
          (hamiltonIveySupportUpperSec (I := I) (M := M) S K a t0) t)) x v v =
      hamiltonIveySupportUpperCoordReact (I := I) S K a t0 t x v := by
  rw [hamiltonIveySupportUpperReact_eval (I := I) S K a t0 t x v v]
  rw [hamiltonIveySupportUpperReactAt_of_solution (I := I) S ha hdim]
  have hshift := hamiltonIveySupportUpperShiftNAt_eq_pinchCoordReact
    (I := I) S (t := t) ha hdim v
  unfold hamiltonIveySupportUpperCoordReact
  rw [Tensor0SSpace.sub_apply 2 x
      (hamiltonIveySupportCoefficientDeriv K a t0 t •
          metricTensorField (I := I) (S.base.metric t) x -
        (2 * hamiltonIveySupportCoefficient K a t0 t) • S.ricci t x)
      (shiftNAt (I := I) (M := M) (hamiltonIveySupportPinchDelta a) t
        (S.base.metric t) x (pinchSec (I := I) S (hamiltonIveySupportPinchDelta a) t x))
      (vec2 (I := I) v v)]
  rw [Tensor0SSpace.sub_apply 2 x
      (hamiltonIveySupportCoefficientDeriv K a t0 t •
        metricTensorField (I := I) (S.base.metric t) x)
      ((2 * hamiltonIveySupportCoefficient K a t0 t) • S.ricci t x)
      (vec2 (I := I) v v)]
  rw [Tensor0SSpace.smul_apply 2 x
      (hamiltonIveySupportCoefficientDeriv K a t0 t)
      (metricTensorField (I := I) (S.base.metric t) x) (vec2 (I := I) v v)]
  rw [Tensor0SSpace.smul_apply 2 x (2 * hamiltonIveySupportCoefficient K a t0 t)
      (S.ricci t x) (vec2 (I := I) v v)]
  rw [metricTensorField_apply]
  rw [show DifferentialGeometry.Geometry.Curvature.vec2 (I := I) v v 0 = v by rfl,
    show DifferentialGeometry.Geometry.Curvature.vec2 (I := I) v v 1 = v by rfl]
  rw [SolutionOn.ricciAt, SolutionFamily.ricciAt]
  rw [hshift]
  simp [SolutionOn.ricci, SolutionFamily.ricci]

private def hamiltonIveySupportUpperCoordTime
    {D : DifferentialGeometry.Geometry.Curvature.RealTimeInterval}
    (S : SolutionOn (I := I) (M := M) D) (K a t0 t : Real)
    (x : M) (v : TangentSpace I x) : Real :=
  hamiltonIveySupportCoefficientDeriv K a t0 t * (S.base.metric t).inner x v v -
    2 * hamiltonIveySupportCoefficient K a t0 t *
      S.ricciAt t x (vec2 (I := I) v v) -
    pinchCoordTime (I := I) S (hamiltonIveySupportPinchDelta a) t x v

omit [SigmaCompactSpace M] [T2Space M] [IsManifold I 1 M] [IsManifold I 2 M] in
private theorem hamiltonIveySupportUpperNab2ModelSec_neg
    {D : DifferentialGeometry.Geometry.Curvature.RealTimeInterval}
    [CompleteSpace E] [SigmaCompactSpace M] [T2Space M]
    (S : SolutionOn (I := I) (M := M) D) (a t : Real) (x : M) :
    (hamiltonIveySupportUpperNab2ModelSec (I := I) S a t) x =
      -pinchNab2Model (I := I) S (hamiltonIveySupportPinchDelta a) t x := by
  simp [hamiltonIveySupportUpperNab2ModelSec, pinchNab2ModelSec_apply,
    hamiltonIveySupportPinchDelta]

omit [SigmaCompactSpace M] [T2Space M] [IsManifold I 2 M] in
private theorem hamiltonIveySupportUpperHeat_coord
    {D : DifferentialGeometry.Geometry.Curvature.RealTimeInterval}
    [CompleteSpace E] [SigmaCompactSpace M] [T2Space M]
    (S : SolutionOn (I := I) (M := M) D) (a t : Real) (x : M)
    (v : TangentSpace I x) :
    tensorHeatWithDrift2QuadMetricAt (I := I) (S.base.metric t)
        (fun _y : M => 0)
        (hamiltonIveySupportUpperNab2ModelSec (I := I) S a t x)
        (hamiltonIveySupportUpperNablaModel (I := I) S a t x) v =
      -(ricciCoordRough (I := I) S t x v) +
        hamiltonIveySupportPinchDelta a *
          (DifferentialGeometry.Geometry.Curvature.laplacianAt (I := I) (flowG (I := I) S) t
              (S.scalar t) x * (S.base.metric t).inner x v v) := by
  classical
  rw [tensorHeatWithDrift2QuadMetricAt_zero_drift]
  rw [hamiltonIveySupportUpperNab2ModelSec_neg (I := I) S a t x]
  rw [metricTraceFirstTwo0SAt_neg (I := I) (S.base.metric t)
    (pinchNab2Model (I := I) S (hamiltonIveySupportPinchDelta a) t x)
    (vec2 (I := I) v v)]
  classical
  let basis := DifferentialGeometry.Tensor.Coordinates.coordinateFrameAt_toBasis (I := I) x
  let gInv : DifferentialGeometry.Tensor.Coordinates.CoordinateIdx (𝕜 := Real) E ->
      DifferentialGeometry.Tensor.Coordinates.CoordinateIdx (𝕜 := Real) E -> Real :=
    fun k l => DifferentialGeometry.Tensor.Coordinates.inverseMetricFlatModelInChart_component
      (I := I) (S.base.metric t) x k l (extChartAt I x x)
  have hinv : MetricInverseInBasis_gen (I := I) (S.base.metric t) x basis gInv := by
    simpa [basis, gInv] using
      Tensor.Coordinates.inverseMetricFlatModelInChart_metricInverseInBasis_center
        (I := I) (S.base.metric t) x
  rw [pinchNab2Model_trace (I := I) S (hamiltonIveySupportPinchDelta a) t basis gInv hinv v]
  rw [ricciRoughTrace_coord (I := I) S t x v]
  rw [scalarHessTrace_eq_lap (I := I) S t x]
  unfold ricciCoordRough
  ring

omit [SigmaCompactSpace M] [T2Space M] [IsManifold I 2 M] in
private theorem hamiltonIveySupportUpperQuadDeriv_coord
    [I.Boundaryless]
    {D : DifferentialGeometry.Geometry.Curvature.RealTimeInterval}
    [CompleteSpace E] [SigmaCompactSpace M] [T2Space M]
    (S : SolutionOn (I := I) (M := M) D)
    (hS : IsSmoothSolutionOn (I := I) (M := M) S)
    {K a t0 : Real} (hK : 0 < K) (ha : 0 < a)
    (t : DifferentialGeometry.Geometry.Curvature.RealTimeInterval.RegularTime D)
    (ht : 0 ≤ (t : Real) - t0) (x : M) (v : TangentSpace I x) :
    HasDerivWithinAt
      (fun s : Real =>
        twoTensorSecToFamily (I := I) (M := M)
          (hamiltonIveySupportUpperSec (I := I) (M := M) S K a t0) s x v v)
      (hamiltonIveySupportUpperCoordTime (I := I) S K a t0 (t : Real) x v)
      D.carrier (t : Real) := by
  have hpinch := pinchQuadDeriv_coord (I := I) (M := M) S hS
    (delta := hamiltonIveySupportPinchDelta a) t x v
  have hcoef : HasDerivWithinAt
      (fun s : Real => hamiltonIveySupportCoefficient K a t0 s)
      (hamiltonIveySupportCoefficientDeriv K a t0 (t : Real)) D.carrier (t : Real) := by
    exact (hamiltonIveySupportCoefficient_hasDerivAt hK ha ht).hasDerivWithinAt
  have hmetric : HasDerivWithinAt
      (fun s : Real => (S.family.metric s).inner x v v)
      ((-2 : Real) * S.ricciAt (t : Real) x (vec2 (I := I) v v))
      D.carrier (t : Real) := by
    have hg := metric_derivWithin_eq_neg_two_ricci (I := I) S hS.isSolution t x v v
    simpa [SolutionOn.family] using hg
  have hmul := hcoef.mul hmetric
  have hsub := hmul.sub hpinch
  have hfun : (fun s : Real =>
      twoTensorSecToFamily (I := I) (M := M)
        (hamiltonIveySupportUpperSec (I := I) (M := M) S K a t0) s x v v) =
      fun s : Real =>
        hamiltonIveySupportCoefficient K a t0 s * (S.base.metric s).inner x v v -
          twoTensorSecToFamily (I := I) (M := M)
            (pinchSec (I := I) S (hamiltonIveySupportPinchDelta a)) s x v v := by
    funext s
    rw [twoTensorSecToFamily_apply (I := I) (M := M)
      (hamiltonIveySupportUpperSec (I := I) (M := M) S K a t0) s x v v]
    rw [hamiltonIveySupportUpperSec_at_point (I := I) S K a t0 s x]
    rw [Tensor0SSpace.sub_apply 2 x
      (hamiltonIveySupportCoefficient K a t0 s •
        metricTensorField (I := I) (S.base.metric s) x)
      (pinchSec (I := I) S ((1 + a) / (2 * a)) s x)
      (vec2 (I := I) v v)]
    rw [Tensor0SSpace.smul_apply 2 x (hamiltonIveySupportCoefficient K a t0 s)
      (metricTensorField (I := I) (S.base.metric s) x) (vec2 (I := I) v v)]
    simp only [metricTensorField_apply, Fin.isValue, smul_eq_mul]
    rw [show DifferentialGeometry.Geometry.Curvature.vec2 (I := I) v v 0 = v by rfl,
      show DifferentialGeometry.Geometry.Curvature.vec2 (I := I) v v 1 = v by rfl]
    rw [twoTensorSecToFamily_apply (I := I) (M := M)
      (pinchSec (I := I) S (hamiltonIveySupportPinchDelta a)) s x v v]
    rfl
  have hpinchfun : (fun s : Real =>
      ((pinchSec (I := I) S (hamiltonIveySupportPinchDelta a) s) x)
        (vec2 (I := I) v v)) =
      fun s : Real =>
        twoTensorSecToFamily (I := I) (M := M)
          (pinchSec (I := I) S (hamiltonIveySupportPinchDelta a)) s x v v := by
    funext s
    rw [twoTensorSecToFamily_apply (I := I) (M := M)
      (pinchSec (I := I) S (hamiltonIveySupportPinchDelta a)) s x v v]
  have hderiv0 : HasDerivWithinAt
      (fun s : Real =>
        hamiltonIveySupportCoefficient K a t0 s * (S.base.metric s).inner x v v -
          twoTensorSecToFamily (I := I) (M := M)
            (pinchSec (I := I) S (hamiltonIveySupportPinchDelta a)) s x v v)
      (hamiltonIveySupportUpperCoordTime (I := I) S K a t0 (t : Real) x v)
      D.carrier (t : Real) := by
    have hcongr := hsub.congr (f₁ := fun s : Real =>
        hamiltonIveySupportCoefficient K a t0 s * (S.base.metric s).inner x v v -
          twoTensorSecToFamily (I := I) (M := M)
            (pinchSec (I := I) S (hamiltonIveySupportPinchDelta a)) s x v v)
        (by
          intro s _hs
          change hamiltonIveySupportCoefficient K a t0 s * (S.base.metric s).inner x v v -
              twoTensorSecToFamily (I := I) (M := M)
                (pinchSec (I := I) S (hamiltonIveySupportPinchDelta a)) s x v v =
            ((fun s : Real => hamiltonIveySupportCoefficient K a t0 s) *
                fun s : Real => (S.base.metric s).inner x v v) s -
              ((pinchSec (I := I) S (hamiltonIveySupportPinchDelta a) s) x)
                (vec2 (I := I) v v)
          simp only [Pi.mul_apply]
          rw [twoTensorSecToFamily_apply (I := I) (M := M)
            (pinchSec (I := I) S (hamiltonIveySupportPinchDelta a)) s x v v])
        (by
          change hamiltonIveySupportCoefficient K a t0 (t : Real) *
              (S.base.metric (t : Real)).inner x v v -
            twoTensorSecToFamily (I := I) (M := M)
              (pinchSec (I := I) S (hamiltonIveySupportPinchDelta a)) (t : Real) x v v =
            ((fun s : Real => hamiltonIveySupportCoefficient K a t0 s) *
                fun s : Real => (S.base.metric s).inner x v v) (t : Real) -
              ((pinchSec (I := I) S (hamiltonIveySupportPinchDelta a) (t : Real)) x)
                (vec2 (I := I) v v)
          simp only [Pi.mul_apply]
          rw [twoTensorSecToFamily_apply (I := I) (M := M)
            (pinchSec (I := I) S (hamiltonIveySupportPinchDelta a)) (t : Real) x v v])
    apply hcongr.congr_deriv
    simp [hamiltonIveySupportUpperCoordTime, pinchCoordTime, ricciCoordQuadRHS,
      SolutionOn.family, SolutionOn.ricci, SolutionFamily.ricci,
      SolutionOn.ricciAt, SolutionFamily.ricciAt]
    ring
  exact hderiv0.congr (by
    intro s _hs
    exact congrFun hfun s) (congrFun hfun (t : Real))

omit [SigmaCompactSpace M] [T2Space M] [IsManifold I 2 M] in
private theorem hamiltonIveySupportUpperParabolic_of_react
    [I.Boundaryless]
    {D : DifferentialGeometry.Geometry.Curvature.RealTimeInterval}
    [CompleteSpace E] [SigmaCompactSpace M] [T2Space M]
    (S : SolutionOn (I := I) (M := M) D)
    (hS : IsSmoothSolutionOn (I := I) (M := M) S)
    {K a t0 T : Real} (hK : 0 < K) (ha : 0 < a) (ht0 : t0 ≤ 0)
    (hTsub : Set.Icc 0 T ⊆ D.carrier)
    (hTreg : Set.Ioc 0 T ⊆ D.regular)
    (hreact : ∀ t, t ∈ Set.Ioc 0 T -> ∀ x, ∀ v : TangentSpace I x,
      (hamiltonIveySupportUpperReact (I := I) (M := M) K a t0 t (S.base.metric t)
        (twoTensorSecToFamily (I := I) (M := M)
          (hamiltonIveySupportUpperSec (I := I) (M := M) S K a t0) t)) x v v =
        hamiltonIveySupportUpperCoordReact (I := I) S K a t0 t x v) :
    TensorParabolicSupersolutionWithDriftOn (I := I) (M := M)
      (fun t : Real => S.base.metric t)
      (twoTensorSecToFamily (I := I) (M := M)
        (hamiltonIveySupportUpperSec (I := I) (M := M) S K a t0))
      (fun _t x => (0 : TangentSpace I x))
      (hamiltonIveySupportUpperReact (I := I) (M := M) K a t0)
      (fun t x => hamiltonIveySupportUpperNab2ModelSec (I := I) S a t x)
      (fun t x => hamiltonIveySupportUpperNablaModel (I := I) S a t x) T := by
  refine ⟨?_⟩
  refine ⟨fun t x v => hamiltonIveySupportUpperCoordTime (I := I) S K a t0 t x v, ?_, ?_⟩
  · intro t ht x v
    have htreg : t ∈ D.regular := hTreg ht
    have ht_nonneg : 0 ≤ t - t0 := by linarith [le_of_lt ht.1, ht0]
    have hderiv := hamiltonIveySupportUpperQuadDeriv_coord (I := I) (M := M)
      S hS hK ha ⟨t, htreg⟩ ht_nonneg x v
    simpa [hamiltonIveySupportUpperCoordTime] using hderiv.mono hTsub
  · intro t ht x v
    have hheat := hamiltonIveySupportUpperHeat_coord (I := I) S a t x v
    have hN := hreact t ht x v
    apply le_of_eq
    calc
      tensorHeatWithDrift2QuadMetricAt (I := I) (S.base.metric t)
            (fun x => (0 : TangentSpace I x))
            (hamiltonIveySupportUpperNab2ModelSec (I := I) S a t x)
            (hamiltonIveySupportUpperNablaModel (I := I) S a t x) v +
          (hamiltonIveySupportUpperReact (I := I) (M := M) K a t0 t (S.base.metric t)
            (twoTensorSecToFamily (I := I) (M := M)
              (hamiltonIveySupportUpperSec (I := I) (M := M) S K a t0) t)) x v v =
        -(ricciCoordRough (I := I) S t x v) +
            hamiltonIveySupportPinchDelta a *
              (DifferentialGeometry.Geometry.Curvature.laplacianAt (I := I) (flowG (I := I) S) t
                  (S.scalar t) x * (S.base.metric t).inner x v v) +
          hamiltonIveySupportUpperCoordReact (I := I) S K a t0 t x v := by
            rw [hheat, hN]
      _ = hamiltonIveySupportUpperCoordTime (I := I) S K a t0 t x v := by
            unfold hamiltonIveySupportUpperCoordReact hamiltonIveySupportUpperCoordTime
            simp [pinchCoordTime, pinchCoordReact, ricciCoordReact, ricciCoordQuadRHS,
              ricciCoordRough, SolutionOn.family]
            ring

theorem shiftReactBlock3_eq_of_ne {delta a b c : Real}
    (hden : 1 - 3 * delta ≠ 0) :
    shiftReactBlock3 delta a b c =
      delta ^ 2 * (1 - 3 * delta) * shiftScal3 delta a b ^ 2 +
        (1 - delta) * ((a - b) ^ 2 + 4 * c ^ 2) := by
  have hden' : 1 - delta * 3 ≠ 0 := by
    intro h
    apply hden
    nlinarith
  have hden2 : 1 - delta * 6 + delta ^ 2 * 9 ≠ 0 := by
    have hsq : (1 - delta * 3) ^ 2 ≠ 0 := pow_ne_zero 2 hden'
    convert hsq using 1
    ring
  unfold shiftReactBlock3 pinchReact ricciPresReact ricciSq3 ricciNorm3
    stdRmOfRic3 shiftRicBlock3 shiftBlockS3 shiftScal3
    DifferentialGeometry.Geometry.Curvature.delta3
  simp [Fin.sum_univ_three, ricciScal3]
  field_simp [hden, hden', hden2]
  ring_nf

def hamiltonIveySupportUpperReactBlock (A c q p r s : Real) : Real :=
  let delta : Real := hamiltonIveySupportPinchDelta A
  let den : Real := 1 - 3 * delta
  let b11 : Real := -p
  let b22 : Real := -r
  let b12 : Real := -s
  let ricB : Fin 3 → Fin 3 → Real := shiftRicBlock3 delta b11 b22 b12
  let trB : Real := ricciScal3 ricB
  let shiftB : Real := delta ^ 2 * (1 - 3 * delta) * shiftScal3 delta b11 b22 ^ 2 +
    (1 - delta) * ((b11 - b22) ^ 2 + 4 * b12 ^ 2)
  let ric00 : Real := ricB 0 0 + c / den
  let shiftQ : Real := shiftB + (c / den) * (2 * delta - 1) * (3 * (ricB 0 0) - trB)
  (-q * c - 2 * c * ric00 - shiftQ)

def hamiltonIveySupportUpperReactBlockPoly
    (A c q p r s : Real) : Real :=
  ((A + 3) * (4 * A ^ 2 * c ^ 2 - 2 * A ^ 2 * c * p - A ^ 2 * c * q -
      2 * A ^ 2 * c * r + 2 * A ^ 2 * p * r - 2 * A ^ 2 * s ^ 2 -
      3 * A * c * q + 4 * A * p * r - 4 * A * s ^ 2 +
      2 * p ^ 2 - 2 * p * r + 2 * r ^ 2 + 6 * s ^ 2)) /
    (A * (A + 3) ^ 2)

omit [SigmaCompactSpace M] [T2Space M] [IsManifold I 2 M] in
theorem hamiltonIveySupportUpperReactBlock_eq_poly
    {A c q p r s : Real} (hA : A ≠ 0) (hA3 : A + 3 ≠ 0) :
    hamiltonIveySupportUpperReactBlock A c q p r s =
      hamiltonIveySupportUpperReactBlockPoly A c q p r s := by
  unfold hamiltonIveySupportUpperReactBlock hamiltonIveySupportUpperReactBlockPoly
    hamiltonIveySupportPinchDelta
  unfold shiftRicBlock3 shiftBlockS3 shiftScal3
  unfold ricciScal3
  unfold DifferentialGeometry.Geometry.Curvature.delta3
  simp only [Fin.sum_univ_three, Fin.isValue, Fin.reduceEq, ↓reduceIte]
  have hden1 : 1 - 3 * ((1 + A) / (2 * A)) ≠ 0 := by
    have hcalc : 1 - 3 * ((1 + A) / (2 * A)) = -(A + 3) / (2 * A) := by
      field_simp [hA]
      ring
    rw [hcalc]
    have hnum : -(A + 3) ≠ 0 := by
      rw [neg_ne_zero]
      exact hA3
    exact div_ne_zero hnum (mul_ne_zero two_ne_zero hA)
  have hm : -3 - A ≠ 0 := by
    intro h
    have : A + 3 = 0 := by nlinarith
    exact hA3 this
  have hquad : 9 + A * 6 + A ^ 2 ≠ 0 := by
    have hsq : (A + 3) ^ 2 = 9 + A * 6 + A ^ 2 := by ring
    rw [← hsq]
    exact pow_ne_zero 2 hA3
  field_simp [hA, hA3, hm, hden1, hquad]
  rw [show 2 * A - (1 + A) * 3 = -(A + 3) by ring]
  have hneg : -(A + 3) ≠ 0 := by rw [neg_ne_zero]; exact hA3
  field_simp [hA, hA3, hneg]
  ring_nf

omit [SigmaCompactSpace M] [T2Space M] [IsManifold I 2 M] in
theorem hamiltonIveySupportUpperReact_eq_block
    {K a t0 t : Real} {g : SmoothRiemannianMetric I M} {x : M}
    {Araw : RawTwoTensorField (I := I) (M := M)}
    {basis : Module.Basis (Fin 3) Real (TangentSpace I x)}
    {p r s : Real}
    (ha : 0 < a)
    (hsym : TwoTensorSymmetricAt (I := I) (M := M) Araw x)
    (hbilin : TwoTensorBilinearAt (I := I) (M := M) Araw x)
    (hblock : ShiftBlockAt (I := I) (M := M) g Araw x basis p r s) :
    (hamiltonIveySupportUpperReact (I := I) (M := M) K a t0 t g Araw) x (basis 0) (basis 0) =
      hamiltonIveySupportUpperReactBlock a (hamiltonIveySupportCoefficient K a t0 t)
        (2 * K / (1 + 2 * K * (t - t0))) p r s := by
  rw [hamiltonIveySupportUpperReact]
  rw [Tensor02ReactionAt.toRawSymm_eval_of_bilin
    (I := I) (M := M)
    (fun t g _x A => hamiltonIveySupportUpperReactAt (I := I) K a t0 t g A)
    t g Araw x hbilin (basis 0) (basis 0)]
  let T : Tensor02At (I := I) (M := M) x :=
    tensor02OfRawAt (I := I) (M := M)
      (rawSym2 (I := I) (M := M) Araw) x
      (rawSym2_bilin (I := I) (M := M) hbilin)
  have hreal : Tensor02RealizesRawAt (I := I) (M := M) Araw x T := by
    intro v w
    rw [tensor02OfRawAt_realizes (I := I) (M := M)]
    exact rawSym2_eq_of_symm (I := I) (M := M) hsym v w
  let negAraw : RawTwoTensorField (I := I) (M := M) :=
    fun y v w => - Araw y v w
  have hreal_neg : Tensor02RealizesRawAt (I := I) (M := M) negAraw x (-T) := by
    intro v w
    rw [Tensor0SSpace.neg_apply]
    rw [hreal v w]
  have hblock_neg : ShiftBlockAt (I := I) (M := M) g negAraw x basis (-p) (-r) (-s) := by
    refine ⟨hblock.orthonormal, ?_⟩
    intro i j
    dsimp [negAraw]
    rw [hblock.components i j]
    fin_cases i <;> fin_cases j <;> simp [shiftBlockS3]
  change hamiltonIveySupportUpperReactAt (I := I) K a t0 t g T (vec2 (I := I) (basis 0) (basis 0)) =
      hamiltonIveySupportUpperReactBlock a (hamiltonIveySupportCoefficient K a t0 t)
        (2 * K / (1 + 2 * K * (t - t0))) p r s
  dsimp [hamiltonIveySupportUpperReactAt]
  let C : Real := hamiltonIveySupportCoefficient K a t0 t
  let Cder : Real := hamiltonIveySupportCoefficientDeriv K a t0 t
  let delta : Real := hamiltonIveySupportPinchDelta a
  have hden : 1 - 3 * delta ≠ 0 := by
    dsimp [delta]
    exact hamiltonIveySupportPinchDelta_den_ne ha
  have hmetric00 : (metricTensorField (I := I) g x) (vec2 (I := I) (basis 0) (basis 0)) = 1 := by
    simp [metricTensorField_apply, hblock.orthonormal 0 0, vec2,
      DifferentialGeometry.Geometry.Curvature.vec2,
      DifferentialGeometry.Geometry.Curvature.delta3]
  have hQ' : C • (metricTensorField (I := I) g x) - T =
      (-T) + C • (metricTensorField (I := I) g x) := by
    abel
  have hRicNeg_comp : ∀ i j : Fin 3,
      shiftRic3At (I := I) (M := M) delta g (-T)
          (vec2 (I := I) (basis i) (basis j)) =
        shiftRicBlock3 delta (-p) (-r) (-s) i j := by
    intro i j
    exact shiftRic3At_comp_of_shiftBlock (I := I) (M := M) hreal_neg hblock_neg i j
  have hRicQ00 :
      (shiftRic3At (I := I) (M := M) delta g (C • (metricTensorField (I := I) g x) - T))
          (vec2 (I := I) (basis 0) (basis 0)) =
        shiftRicBlock3 delta (-p) (-r) (-s) 0 0 + C / (1 - 3 * delta) := by
    rw [hQ']
    rw [shiftRic_add_g (I := I) (M := M) (δ := delta) (c := C)
      basis hblock.orthonormal hden (-T)]
    simp only [Tensor0SBundle.Tensor0SSpace.add_apply, Tensor0SBundle.Tensor0SSpace.smul_apply,
      hmetric00, smul_eq_mul]
    rw [hRicNeg_comp 0 0]
    ring
  have hshift_base :
      (shiftNAt (I := I) (M := M) delta t g x (-T))
          (vec2 (I := I) (basis 0) (basis 0)) =
        shiftReactBlock3 delta (-p) (-r) (-s) := by
    exact shiftNAt_comp_shiftBlock (I := I) (M := M) hreal_neg hblock_neg
  have hshiftQ :
      (shiftNAt (I := I) (M := M) delta t g x
          (C • (metricTensorField (I := I) g x) - T))
          (vec2 (I := I) (basis 0) (basis 0)) =
        shiftReactBlock3 delta (-p) (-r) (-s) +
          (C / (1 - 3 * delta)) * (2 * delta - 1) *
            (3 * (shiftRic3At (I := I) (M := M) delta g (-T))
                (vec2 (I := I) (basis 0) (basis 0)) -
              metricTracePair0SAt (I := I) g
                (shiftRic3At (I := I) (M := M) delta g (-T))) := by
    rw [hQ']
    have hdiff := shiftNAt_add_g_comp (I := I) (M := M)
      (delta := delta) (c := C) (t := t) basis hblock.orthonormal hden (-T)
    have hdiff' := congrArg (fun X : Real => X + (shiftNAt (I := I) (M := M) delta t g x (-T))
        (vec2 (I := I) (basis 0) (basis 0))) hdiff
    have hQeq :
        (shiftNAt (I := I) (M := M) delta t g x
          ((-T) + C • (metricTensorField (I := I) g x)))
          (vec2 (I := I) (basis 0) (basis 0)) =
          (shiftNAt (I := I) (M := M) delta t g x (-T))
            (vec2 (I := I) (basis 0) (basis 0)) +
          (C / (1 - 3 * delta)) * (2 * delta - 1) *
            (3 * (shiftRic3At (I := I) (M := M) delta g (-T))
                (vec2 (I := I) (basis 0) (basis 0)) -
              metricTracePair0SAt (I := I) g
                (shiftRic3At (I := I) (M := M) delta g (-T))) := by
      linarith
    rw [hQeq, hshift_base]
  have hTrace :
      metricTracePair0SAt (I := I) g
          (shiftRic3At (I := I) (M := M) delta g (-T)) =
        ricciScal3 (shiftRicBlock3 delta (-p) (-r) (-s)) := by
    rw [metricTrace_comp_orthonormal (I := I) (M := M) basis hblock.orthonormal
      (shiftRic3At (I := I) (M := M) delta g (-T))]
    simp [hRicNeg_comp]
  have hmain :
      (Cder • (metricTensorField (I := I) g x) -
          (2 * C) • shiftRic3At (I := I) (M := M) delta g
            (C • (metricTensorField (I := I) g x) - T) -
        shiftNAt (I := I) (M := M) delta t g x
          (C • (metricTensorField (I := I) g x) - T))
        (vec2 (I := I) (basis 0) (basis 0)) =
      Cder - 2 * C * (shiftRicBlock3 delta (-p) (-r) (-s) 0 0 + C / (1 - 3 * delta)) -
        (shiftReactBlock3 delta (-p) (-r) (-s) +
          (C / (1 - 3 * delta)) * (2 * delta - 1) *
            (3 * shiftRicBlock3 delta (-p) (-r) (-s) 0 0 -
              ricciScal3 (shiftRicBlock3 delta (-p) (-r) (-s)))) := by
    simp only [Tensor0SBundle.Tensor0SSpace.sub_apply, Tensor0SBundle.Tensor0SSpace.smul_apply,
      hmetric00, hRicQ00, hshiftQ, hTrace, hRicNeg_comp 0 0, smul_eq_mul]
    ring
  rw [hmain]
  have hCder : Cder = -(2 * K / (1 + 2 * K * (t - t0))) * C := by
    dsimp [Cder, C, hamiltonIveySupportCoefficientDeriv, hamiltonIveySupportCoefficient]
    field_simp
  rw [hCder]
  unfold hamiltonIveySupportUpperReactBlock
  rw [shiftReactBlock3_eq_of_ne (delta := delta) (a := -p) (b := -r) (c := -s) hden]

omit [SigmaCompactSpace M] [T2Space M] [IsManifold I 2 M] in
theorem hamiltonIveySupportUpperReactBlockPoly_not_nonneg :
    ¬ (∀ a c q p r s : Real, 0 < a -> 0 < c -> 0 ≤ p -> 0 ≤ r ->
      p * r - s ^ 2 ≥ 0 ->
      0 ≤ hamiltonIveySupportUpperReactBlockPoly a c q p r s) := by
  intro h
  have hle := h 25 54 0.000000005 133 4 6 (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num)
  norm_num [hamiltonIveySupportUpperReactBlockPoly] at hle

omit [SigmaCompactSpace M] [T2Space M] [IsManifold I 2 M] in
theorem hamiltonIveySupportUpperReactBlockPoly_not_nonneg_of_q_relation :
    ¬ (∀ a c q p r s : Real, 0 < a -> 0 < c ->
      q = 2 * a * c / Real.exp (a + 2) -> 0 ≤ p -> 0 ≤ r -> p * r - s ^ 2 ≥ 0 ->
      0 ≤ hamiltonIveySupportUpperReactBlockPoly a c q p r s) := by
  intro h
  let a : Real := Real.log 1000 - 2
  have hExp2 : Real.exp 2 < 1000 := by
    have h1 : Real.exp 1 < 3 := Real.exp_one_lt_three
    have hpos : 0 < Real.exp 1 := Real.exp_pos 1
    have h2 : Real.exp 2 = (Real.exp 1) ^ 2 := by
      rw [show (2:ℝ) = 1 + 1 by norm_num, Real.exp_add]
      ring
    rw [h2]
    have h3 : (Real.exp 1) ^ 2 < 9 := by nlinarith [sq_nonneg (Real.exp 1 - 3), h1, hpos]
    nlinarith
  have hlog2 : 2 < Real.log 1000 := by
    rw [Real.lt_log_iff_exp_lt (by norm_num : (0:ℝ) < 1000)]
    exact hExp2
  have ha : 0 < a := by
    dsimp [a]
    linarith
  have hExp69 : Real.exp 6.9 < 1000 := by
    have h1 : Real.exp 1 < 2.7182818286 := Real.exp_one_lt_d9
    have h7 : Real.exp 7 = (Real.exp 1) ^ 7 := by
      rw [← Real.exp_nat_mul 1 7]
      norm_num
    have h7lt : Real.exp 7 < 1100 := by
      rw [h7]
      have hpow : (Real.exp 1) ^ 7 < (2.7182818286 : ℝ) ^ 7 := by
        exact pow_lt_pow_left₀ h1 (Real.exp_pos 1).le (by norm_num : (7:ℕ) ≠ 0)
      have hnum : (2.7182818286 : ℝ) ^ 7 < 1100 := by norm_num
      linarith
    have h01 : 1.1 < Real.exp 0.1 := by
      have := Real.add_one_lt_exp (show (0.1:ℝ) ≠ 0 by norm_num)
      norm_num at this ⊢
      linarith
    have h69 : Real.exp 6.9 = Real.exp 7 / Real.exp 0.1 := by
      rw [show (6.9:ℝ) = 7 - 0.1 by norm_num, Real.exp_sub]
    rw [h69]
    have hden : 0 < Real.exp 0.1 := Real.exp_pos _
    rw [div_lt_iff₀ hden]
    have h1100 : 1100 < 1000 * Real.exp 0.1 := by nlinarith [h01]
    linarith
  have h69log : 6.9 < Real.log 1000 := by
    rw [Real.lt_log_iff_exp_lt (by norm_num : (0:ℝ) < 1000)]
    exact hExp69
  have ha49 : 4.9 < a := by
    dsimp [a]
    linarith
  have hexp : Real.exp (a + 2) = 1000 := by
    dsimp [a]
    rw [show Real.log 1000 - 2 + 2 = Real.log 1000 by ring]
    rw [Real.exp_log (by norm_num : (0:ℝ) < 1000)]
  let q : Real := 2 * a * 1000 / Real.exp (a + 2)
  have hq : q = 2 * a := by
    dsimp [q]
    rw [hexp]
    field_simp
  have hle := h a 1000 q 100 2101 457 ha (by norm_num) rfl (by norm_num) (by norm_num) (by norm_num)
  have hpoly_lt : hamiltonIveySupportUpperReactBlockPoly a 1000 q 100 2101 457 < 0 := by
    dsimp [q] at hle ⊢
    rw [hexp] at hle ⊢
    have ha_ne : a ≠ 0 := ne_of_gt ha
    have ha3 : a + 3 ≠ 0 := by nlinarith [ha]
    unfold hamiltonIveySupportUpperReactBlockPoly
    field_simp [ha_ne, ha3] at hle ⊢
    ring_nf at hle ⊢
    nlinarith [ha49]
  exact (not_le_of_gt hpoly_lt) hle

omit [SigmaCompactSpace M] [T2Space M] [IsManifold I 2 M] in
theorem hamiltonIveySupportUpperReactBlockPoly_tangent_eq
    {a X c q l1 : Real} (ha : a ≠ 0) (ha3 : a + 3 ≠ 0) (hc : c = X / a) :
    hamiltonIveySupportUpperReactBlockPoly a c q
        (c + X * (a - 1) / a + l1)
        (c + X * (a - 1) / a + (a * X - l1)) 0 =
      (DifferentialGeometry.Geometry.Curvature.DimensionThree.reactionSectionalSum3
          l1 (a * X - l1) (-X) -
        a * DifferentialGeometry.Geometry.Curvature.DimensionThree.reactionPinchHeight3
          l1 (a * X - l1) (-X) +
        a * (-(q * c))) / a := by
  rw [hamiltonIveySupportUpperReactBlockPoly]
  rw [hc]
  unfold DifferentialGeometry.Geometry.Curvature.DimensionThree.reactionSectionalSum3
    DifferentialGeometry.Geometry.Curvature.DimensionThree.reactionPinchHeight3
    DifferentialGeometry.Dim3Reaction.sectionalReaction12
    DifferentialGeometry.Dim3Reaction.sectionalReaction13
    DifferentialGeometry.Dim3Reaction.sectionalReaction23
  field_simp [ha, ha3]
  ring_nf

theorem hamiltonIveySupportUpperReactBlockPoly_pos_of_barrier_boundary
    {K τ a l1 l2 l3 : Real}
    (ha : a = Real.log ((-l3) / K) + Real.log (1 + 2 * K * τ) - 2)
    (ha_pos : 0 < a)
    (h21 : l2 ≤ l1) (h32 : l3 ≤ l2) (hl3 : l3 < 0)
    (hK : 0 < K) (hden : 0 < 1 + 2 * K * τ)
    (hboundary : DifferentialGeometry.Geometry.Curvature.DimensionThree.hamiltonIveyBarrier K τ (-l3) = DifferentialGeometry.Geometry.Curvature.DimensionThree.sectionalSum3 l1 l2 l3) :
    let c : Real := K * Real.exp (a + 2) / (a * (1 + 2 * K * τ))
    let q : Real := 2 * K / (1 + 2 * K * τ)
    let p : Real := c + DifferentialGeometry.Geometry.Curvature.DimensionThree.sectionalSum3 l1 l2 l3 / a + l1
    let r : Real := c + DifferentialGeometry.Geometry.Curvature.DimensionThree.sectionalSum3 l1 l2 l3 / a + l2
    0 < hamiltonIveySupportUpperReactBlockPoly a c q p r 0 := by
  intro c q p r
  let X : Real := -l3
  have hXdef : X = -l3 := rfl
  have hXpos : 0 < X := by dsimp [X]; exact neg_pos.mpr hl3
  have hXlog : Real.log (X / K) = Real.log ((-l3) / K) := by
    rw [hXdef]
  have harg1 : 0 < X / K := div_pos hXpos hK
  have hsumlog : Real.log (X / K) + Real.log (1 + 2 * K * τ) =
      Real.log ((X / K) * (1 + 2 * K * τ)) :=
    (Real.log_mul harg1.ne' hden.ne').symm
  have hlogarg : 0 < (X / K) * (1 + 2 * K * τ) := mul_pos harg1 hden
  have hexp : Real.exp (Real.log (X / K) + Real.log (1 + 2 * K * τ)) =
      (X / K) * (1 + 2 * K * τ) := by
    rw [hsumlog, Real.exp_log hlogarg]
  have ha2 : a + 2 = Real.log (X / K) + Real.log (1 + 2 * K * τ) := by
    rw [hXlog, ha]
    ring
  have hXexp : X = K * Real.exp (a + 2) / (1 + 2 * K * τ) := by
    calc
      X = (X / K) * (1 + 2 * K * τ) * (K / (1 + 2 * K * τ)) := by
            rw [show (X / K) * (1 + 2 * K * τ) * (K / (1 + 2 * K * τ)) =
                X * ((1 + 2 * K * τ) / (1 + 2 * K * τ)) by field_simp [hK.ne']]
            rw [div_self hden.ne']
            ring
      _ = K * Real.exp (a + 2) / (1 + 2 * K * τ) := by
            rw [ha2, hexp]
            field_simp [hK.ne', hden.ne']
  have hS_eq : DifferentialGeometry.Geometry.Curvature.DimensionThree.sectionalSum3 l1 l2 l3 = X * (a - 1) := by
    rw [← hboundary]
    unfold DifferentialGeometry.Geometry.Curvature.DimensionThree.hamiltonIveyBarrier
    rw [hXdef]
    rw [ha]
    ring_nf
  have hl1l2 : l1 + l2 = a * X := by
    have hS' := hS_eq
    unfold DifferentialGeometry.Geometry.Curvature.DimensionThree.sectionalSum3 at hS'
    rw [hXdef] at hS'
    nlinarith
  have hmain := DifferentialGeometry.Geometry.Curvature.DimensionThree.hamiltonIveyBarrier_reaction_derivative_pos_on_boundary
    (l1 := l1) (l2 := l2) (l3 := l3) (K := K) (τ := τ)
    h21 h32 hl3 hK hden hboundary
  have hc : c = X / a := by
    dsimp [c]
    rw [hXexp]
    field_simp [ha_pos.ne', hK.ne', hden.ne']
  have htime_eq : a * (-(q * c)) = - X * (2 * K / (1 + 2 * K * τ)) := by
    dsimp [q]
    rw [hc]
    field_simp [ha_pos.ne']
  have hblock_eq :
      hamiltonIveySupportUpperReactBlockPoly a c q p r 0 =
        (DifferentialGeometry.Geometry.Curvature.DimensionThree.reactionSectionalSum3 l1 l2 l3 -
          a * DifferentialGeometry.Geometry.Curvature.DimensionThree.reactionPinchHeight3 l1 l2 l3 +
          a * (-(q * c))) / a := by
    have hl2 : l2 = a * X - l1 := by linarith [hl1l2]
    have hl3X : l3 = -X := by linarith
    dsimp [p, r]
    rw [hS_eq, hl2, hl3X]
    simpa [hc] using
      (hamiltonIveySupportUpperReactBlockPoly_tangent_eq
        (a := a) (X := X) (c := c) (q := q) (l1 := l1)
        ha_pos.ne' (by nlinarith : a + 3 ≠ 0) hc)
  rw [hblock_eq]
  have hmain' : 0 < DifferentialGeometry.Geometry.Curvature.DimensionThree.reactionSectionalSum3 l1 l2 l3 -
      a * DifferentialGeometry.Geometry.Curvature.DimensionThree.reactionPinchHeight3 l1 l2 l3 -
      X * (2 * K / (1 + 2 * K * τ)) := by
    simpa [hXdef, ha] using hmain
  have hdiv : 0 < (DifferentialGeometry.Geometry.Curvature.DimensionThree.reactionSectionalSum3 l1 l2 l3 -
      a * DifferentialGeometry.Geometry.Curvature.DimensionThree.reactionPinchHeight3 l1 l2 l3 +
      a * (-(q * c))) / a := by
    have hnum_pos : 0 < DifferentialGeometry.Geometry.Curvature.DimensionThree.reactionSectionalSum3 l1 l2 l3 -
        a * DifferentialGeometry.Geometry.Curvature.DimensionThree.reactionPinchHeight3 l1 l2 l3 + a * (-(q * c)) := by
      rw [htime_eq]
      simpa using hmain'
    exact div_pos hnum_pos ha_pos
  exact hdiv

omit [SigmaCompactSpace M] [T2Space M] [IsManifold I 2 M] in
theorem hamiltonIveySupportUpperParabolic
    [I.Boundaryless]
    {D : DifferentialGeometry.Geometry.Curvature.RealTimeInterval}
    [CompleteSpace E] [SigmaCompactSpace M] [T2Space M]
    (S : SolutionOn (I := I) (M := M) D)
    (hS : IsSmoothSolutionOn (I := I) (M := M) S)
    {K a t0 T : Real} (hK : 0 < K) (ha : 0 < a) (ht0 : t0 ≤ 0)
    (hdim : ∀ x : M, Module.finrank Real (TangentSpace I x) = 3)
    (hTsub : Set.Icc 0 T ⊆ D.carrier)
    (hTreg : Set.Ioc 0 T ⊆ D.regular) :
    TensorParabolicSupersolutionWithDriftOn (I := I) (M := M)
      (fun t : Real => S.base.metric t)
      (twoTensorSecToFamily (I := I) (M := M)
        (hamiltonIveySupportUpperSec (I := I) (M := M) S K a t0))
      (fun _t x => (0 : TangentSpace I x))
      (hamiltonIveySupportUpperReact (I := I) (M := M) K a t0)
      (fun t x => hamiltonIveySupportUpperNab2ModelSec (I := I) S a t x)
      (fun t x => hamiltonIveySupportUpperNablaModel (I := I) S a t x) T := by
  exact hamiltonIveySupportUpperParabolic_of_react (I := I) (M := M) S hS hK ha ht0
    hTsub hTreg (fun t ht x v =>
      hamiltonIveySupportUpperReact_coord_eq (I := I) S ha (hdim x) v)

end DifferentialGeometry.PDE.RicciFlow
