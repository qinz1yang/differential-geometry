import DifferentialGeometry.Geometry.Curvature.DimensionThree.CurvatureOperatorLeastEigenvalue
import DifferentialGeometry.Geometry.Flow.RicciFlow.DimensionThree.HamiltonIvey
import DifferentialGeometry.Geometry.Flow.RicciFlow.DimensionThree.HamiltonIveySupportUpper
import DifferentialGeometry.Tensor.RSTensor.QuadraticBounds.Unit
import DifferentialGeometry.Geometry.Flow.RicciFlow.MaximumPrinciple.TensorWeak.Basic
import DifferentialGeometry.Geometry.Flow.RicciFlow.Evolution.ShiftedReaction

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace DifferentialGeometry.PDE.RicciFlow

open Bundle Tensor0SBundle
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Geometry.Curvature.DimensionThree
open DifferentialGeometry.Geometry.Operator
open scoped Manifold ContDiff BigOperators

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace Real E]
variable [FiniteDimensional Real E] [CompleteSpace E]
variable {H : Type*} [TopologicalSpace H]
variable {I : ModelWithCorners Real E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
variable [IsManifold I ∞ M] [IsManifold I 1 M] [IsManifold I 2 M]
variable [SigmaCompactSpace M] [T2Space M]

theorem orderedSectionalCurvaturesAt_ricciEigen_min
    {D : DifferentialGeometry.Geometry.Curvature.RealTimeInterval}
    (S : SolutionOn (I := I) (M := M) D)
    {t : Real} {x : M}
    {basis : Module.Basis (Fin 3) Real (TangentSpace I x)}
    {l1 l2 l3 : Real}
    (horth : OrthonormalBasisAt (I := I) (S.base.metric t) x basis)
    (h21 : l2 ≤ l1) (h32 : l3 ≤ l2)
    (hdiag : RicciDiagAt (I := I) (S.ricci t x) (l1 + l2 + l3) l1 l2 l3 basis) :
    orderedSectionalCurvaturesAt (I := I) x basis
        ⟨S.base.rm04 t x, metricRm04At_mem_algebraicCurvatureTensorSubmodule
          (I := I) (S.base.metric t) x⟩ 2 =
      (l1 + l2 + l3) / 2 - l1 := by
  classical
  have hval : ∀ i j : Fin 3,
      (S.ricci t x) (vec2 (I := I) (basis i) (basis j)) = ricciDiag3 l1 l2 l3 i j := by
    intro i j
    simpa [ricciCompAt_apply] using hdiag.2 i j
  have hscalar_trace :
      metricTracePair0SAt (I := I) (S.base.metric t) (S.ricci t x) = l1 + l2 + l3 := by
    calc
      metricTracePair0SAt (I := I) (S.base.metric t) (S.ricci t x)
          = ricciScal3 (fun a b : Fin 3 =>
              (S.ricci t x) (vec2 (I := I) (basis a) (basis b))) := by
            exact metricTrace_comp_orthonormal (I := I) (M := M) basis horth (S.ricci t x)
      _ = l1 + l2 + l3 := by
            unfold ricciScal3
            simp only [Fin.sum_univ_three]
            rw [hval 0 0, hval 1 1, hval 2 2]
            simp [ricciDiag3]
  have htrace := traceData_metricTrace (I := I) (M := M) S horth
  have htrace' :
      DifferentialGeometry.Geometry.Curvature.RiemannFromRicci3DTraceDataAt
        (I := I) (S.base.metric t) (-(S.ricci t x)) (-(l1 + l2 + l3))
        (S.base.rm04 t x) basis := by
    rcases htrace with ⟨horth_t, hcurv_t, hric_t, hscalar_t⟩
    refine ⟨horth_t, hcurv_t, hric_t, ?_⟩
    rw [← hscalar_t, hscalar_trace]
  have hdiagNeg : RicciDiagAt (I := I) (-(S.ricci t x))
      (-(l1 + l2 + l3)) (-l1) (-l2) (-l3) basis := by
    constructor
    · unfold ricciEigenScalar3
      ring
    · intro i j
      simp only [ricciCompAt, component0S_apply]
      rw [show (fun a : Fin 2 => basis (slots2 i j a)) =
          vec2 (I := I) (basis i) (basis j) by
        funext a
        fin_cases a <;> rfl]
      rw [show (-(S.ricci t) x) (vec2 (I := I) (basis i) (basis j)) =
          -((S.ricci t x) (vec2 (I := I) (basis i) (basis j))) by rfl]
      rw [hval i j]
      fin_cases i <;> fin_cases j <;> simp [ricciDiag3]
  have hcomp := stdRmComp_eq_diag (I := I) htrace' hdiagNeg
  let d : Fin 3 → Real := fun i =>
    if i = 0 then sec12Ric3 l1 l2 l3 else if i = 1 then sec13Ric3 l1 l2 l3 else sec23Ric3 l1 l2 l3
  have hmatrix : curvatureOperatorMatrixAt (I := I) x basis
      ⟨S.base.rm04 t x, metricRm04At_mem_algebraicCurvatureTensorSubmodule
        (I := I) (S.base.metric t) x⟩ = Matrix.diagonal d := by
    ext i j
    unfold curvatureOperatorMatrixAt Matrix.diagonal d
    change (S.base.rm04 t x) (vec4 (I := I) (basis (bivectorIndex3 i).1)
        (basis (bivectorIndex3 i).2) (basis (bivectorIndex3 j).2)
        (basis (bivectorIndex3 j).1)) =
      if i = j then d i else 0
    rw [← rm04CompAt_apply]
    change standardRmCompAt (I := I) basis (S.base.rm04 t x)
        (bivectorIndex3 i).1 (bivectorIndex3 i).2
        (bivectorIndex3 j).2 (bivectorIndex3 j).1 =
      if i = j then d i else 0
    rw [hcomp (bivectorIndex3 i).1 (bivectorIndex3 i).2
      (bivectorIndex3 j).2 (bivectorIndex3 j).1]
    dsimp [d]
    fin_cases i <;> fin_cases j <;>
      simp [bivectorIndex3, stdRmDiag3, ricciDiag3, ricciEigenScalar3,
        sec12Ric3, sec13Ric3, sec23Ric3, delta3] <;> ring_nf
  have hd : Antitone d := by
    intro i j hij
    fin_cases i <;> fin_cases j <;> simp [d, sec12Ric3, sec13Ric3, sec23Ric3] at hij ⊢ <;>
      nlinarith
  have heig := diagonal_eigenvalues₀_eq_of_antitone d hd
  have h2 : d 2 = (l1 + l2 + l3) / 2 - l1 := by
    simp [d, sec23Ric3]
    ring
  have hmain : orderedSectionalCurvaturesAt (I := I) x basis
      ⟨S.base.rm04 t x, metricRm04At_mem_algebraicCurvatureTensorSubmodule
        (I := I) (S.base.metric t) x⟩ = d := by
    unfold orderedSectionalCurvaturesAt
    let hA : (curvatureOperatorMatrixAt (I := I) x basis
        ⟨S.base.rm04 t x, metricRm04At_mem_algebraicCurvatureTensorSubmodule
          (I := I) (S.base.metric t) x⟩).IsHermitian :=
      curvatureOperatorMatrixAt_isHermitian (I := I) x basis
        ⟨S.base.rm04 t x, metricRm04At_mem_algebraicCurvatureTensorSubmodule
          (I := I) (S.base.metric t) x⟩
    let hB : (Matrix.diagonal d).IsHermitian := Matrix.isHermitian_diagonal d
    have heig0 : hA.eigenvalues₀ = hB.eigenvalues₀ := by
      have hchar : (curvatureOperatorMatrixAt (I := I) x basis
          ⟨S.base.rm04 t x, metricRm04At_mem_algebraicCurvatureTensorSubmodule
            (I := I) (S.base.metric t) x⟩).charpoly = (Matrix.diagonal d).charpoly := by
        rw [hmatrix]
      have hsA := hA.sort_roots_charpoly_eq_eigenvalues₀
      have hsB := hB.sort_roots_charpoly_eq_eigenvalues₀
      rw [← hchar] at hsB
      exact List.ofFn_inj.mp (hsA.symm.trans hsB)
    change hA.eigenvalues₀ = d
    rw [heig0]
    exact heig
  rw [hmain, h2]

omit [IsManifold I 2 M] in
theorem hamiltonIveySupportUpperSec_lowerBound_ricciEigen
    {D : DifferentialGeometry.Geometry.Curvature.RealTimeInterval}
    (S : SolutionOn (I := I) (M := M) D)
    {K a t0 t : Real} {x : M}
    {basis : Module.Basis (Fin 3) Real (TangentSpace I x)}
    {l1 l2 l3 : Real} (ha : 0 < a)
    (horth : OrthonormalBasisAt (I := I) (S.base.metric t) x basis)
    (h21 : l2 ≤ l1) (h32 : l3 ≤ l2)
    (hdiag : RicciDiagAt (I := I) (S.ricci t x) (l1 + l2 + l3) l1 l2 l3 basis)
    {v : TangentSpace I x} (hunit : (S.base.metric t).inner x v v = 1) :
    DifferentialGeometry.Geometry.Curvature.DimensionThree.hamiltonIveySupportEigenGap
        K (t - t0) a ((l1 + l2 + l3) / 2 - l1) ((l1 + l2 + l3) / 2) / a ≤
      twoTensorSecToFamily (I := I) (M := M)
        (hamiltonIveySupportUpperSec (I := I) (M := M) S K a t0) t x v v := by
  classical
  let c : Fin 3 → Real := basis.repr v
  let l : Fin 3 → Real := fun i => if i = 0 then l1 else if i = 1 then l2 else l3
  have hsum0 : ∑ i : Fin 3, basis.repr v i ^ 2 = 1 := by
    have h := inner_eq_sum_repr3 (I := I) horth v v
    rw [h] at hunit
    simpa [pow_two] using hunit
  have hsum : ∑ i : Fin 3, c i ^ 2 = 1 := by
    simpa [c] using hsum0
  have hval : ∀ i j : Fin 3,
      (S.ricci t x) (vec2 (I := I) (basis i) (basis j)) = ricciDiag3 l1 l2 l3 i j := by
    intro i j
    simpa [ricciCompAt_apply] using hdiag.2 i j
  have hEnd : ricciEndAt (I := I) (S.base.metric t) (S.ricci t x) v =
      ∑ i : Fin 3, c i • ricciEndAt (I := I) (S.base.metric t) (S.ricci t x) (basis i) := by
    dsimp [c]
    conv_lhs => rw [← basis.sum_repr v]
    rw [map_sum]
    apply Finset.sum_congr rfl
    intro i _
    rw [map_smul]
  have hRicSum : (S.ricci t x) (vec2 (I := I) v v) = ∑ i : Fin 3, l i * c i ^ 2 := by
    have hRicEval : (S.ricci t x) (vec2 (I := I) v v) =
        (S.base.metric t).inner x
          (ricciEndAt (I := I) (S.base.metric t) (S.ricci t x) v) v := by
      exact (ricciEnd_inner (I := I) (S.base.metric t) (S.ricci t x) v v).symm
    rw [hRicEval]
    have hreprEnd : ∀ i : Fin 3,
        basis.repr (ricciEndAt (I := I) (S.base.metric t) (S.ricci t x) v) i =
          ∑ j : Fin 3, c j * (S.ricci t x) (vec2 (I := I) (basis j) (basis i)) := by
      intro i
      rw [hEnd]
      rw [map_sum]
      simp only [Finsupp.coe_finset_sum, Finset.sum_apply]
      apply Finset.sum_congr rfl
      intro j _
      rw [LinearEquiv.map_smul basis.repr]
      rw [Finsupp.smul_apply]
      dsimp [c]
      rw [ricciEnd_repr_orthonormal (I := I) (M := M) basis horth (S.ricci t x) j i]
    have hinner := inner_eq_sum_repr3 (I := I) horth
      (ricciEndAt (I := I) (S.base.metric t) (S.ricci t x) v) v
    rw [hinner]
    have hstep : (∑ i : Fin 3,
        basis.repr (ricciEndAt (I := I) (S.base.metric t) (S.ricci t x) v) i *
          basis.repr v i) =
        ∑ i : Fin 3, l i * c i ^ 2 := by
      simp_rw [hreprEnd]
      dsimp [c]
      rw [show (∑ i : Fin 3, (∑ j : Fin 3,
          basis.repr v j * (S.ricci t x) (vec2 (I := I) (basis j) (basis i))) *
            basis.repr v i) =
          ∑ i : Fin 3, (∑ j : Fin 3,
            basis.repr v j * ricciDiag3 l1 l2 l3 j i) * basis.repr v i by
        apply Finset.sum_congr rfl
        intro i _
        apply congrArg (fun z : Real => z * basis.repr v i)
        apply Finset.sum_congr rfl
        intro j _
        rw [hval j i]]
      rw [show (∑ i : Fin 3, (∑ j : Fin 3,
          basis.repr v j * ricciDiag3 l1 l2 l3 j i) * basis.repr v i) =
          ∑ i : Fin 3, l i * basis.repr v i ^ 2 by
        simp only [ricciDiag3, Fin.sum_univ_three, Fin.isValue, Fin.reduceEq,
          ↓reduceIte, pow_two]
        simp [l]
        ring_nf]
    exact hstep
  have hscalar_trace :
      metricTracePair0SAt (I := I) (S.base.metric t) (S.ricci t x) = l1 + l2 + l3 := by
    rw [metricTrace_comp_orthonormal (I := I) (M := M) basis horth (S.ricci t x)]
    unfold ricciScal3
    simp only [Fin.sum_univ_three]
    rw [hval 0 0, hval 1 1, hval 2 2]
    simp [ricciDiag3]
  have hB : twoTensorSecToFamily (I := I) (M := M)
      (hamiltonIveySupportUpperSec (I := I) (M := M) S K a t0) t x v v =
      hamiltonIveySupportCoefficient K a t0 t -
        (S.ricci t x) (vec2 (I := I) v v) +
          hamiltonIveySupportPinchDelta a * (l1 + l2 + l3) := by
    rw [twoTensorSecToFamily_apply]
    rw [hamiltonIveySupportUpperSec_at_point (I := I) S K a t0 t x]
    rw [pinchSec_at_trace (I := I) (M := M) S ((1 + a) / (2 * a)) t x]
    rw [Tensor0SSpace.sub_apply, Tensor0SSpace.sub_apply]
    rw [Tensor0SSpace.smul_apply, Tensor0SSpace.smul_apply]
    simp only [metricTensorField_apply, Fin.isValue, smul_eq_mul]
    rw [show DifferentialGeometry.Geometry.Curvature.vec2 (I := I) v v 0 = v by rfl]
    rw [show DifferentialGeometry.Geometry.Curvature.vec2 (I := I) v v 1 = v by rfl]
    rw [hunit, mul_one, hscalar_trace]
    unfold hamiltonIveySupportPinchDelta
    field_simp [ha.ne']
    ring
  rw [hB, hRicSum]
  unfold DifferentialGeometry.Geometry.Curvature.DimensionThree.hamiltonIveySupportEigenGap
    hamiltonIveySupportCoefficient hamiltonIveySupportPinchDelta
  have hcoef_min : ∀ i : Fin 3,
      (l1 + l2 + l3) / 2 - l1 ≤ (l1 + l2 + l3) / 2 - l i := by
    intro i
    fin_cases i <;> simp [l] <;> nlinarith
  have hle : ∀ i : Fin 3,
      ((l1 + l2 + l3) / 2 - l1) * c i ^ 2 ≤
        ((l1 + l2 + l3) / 2 - l i) * c i ^ 2 := by
    intro i
    exact mul_le_mul_of_nonneg_right (hcoef_min i) (sq_nonneg (c i))
  have hmain : (l1 + l2 + l3) / 2 - l1 ≤
      ∑ i : Fin 3, ((l1 + l2 + l3) / 2 - l i) * c i ^ 2 := by
    calc
      (l1 + l2 + l3) / 2 - l1 =
          ((l1 + l2 + l3) / 2 - l1) * ∑ i : Fin 3, c i ^ 2 := by
            rw [hsum, mul_one]
      _ = ∑ i : Fin 3, ((l1 + l2 + l3) / 2 - l1) * c i ^ 2 := by
            rw [Finset.mul_sum]
      _ ≤ ∑ i : Fin 3, ((l1 + l2 + l3) / 2 - l i) * c i ^ 2 :=
            Finset.sum_le_sum (fun i _ => hle i)
  have hexp : ∑ i : Fin 3, ((l1 + l2 + l3) / 2 - l i) * c i ^ 2 =
      ((l1 + l2 + l3) / 2) * ∑ i : Fin 3, c i ^ 2 - ∑ i : Fin 3, l i * c i ^ 2 := by
    simp_rw [sub_mul]
    rw [Finset.sum_sub_distrib]
    rw [← Finset.mul_sum]
  have hsum_upper : ∑ i : Fin 3, l i * c i ^ 2 ≤ l1 := by
    rw [hexp, hsum] at hmain
    nlinarith
  field_simp [ha.ne']
  ring_nf
  nlinarith [hsum_upper]


theorem hamiltonIveySupportUpperSec_quad_ge_leastEigen_gap
    {D : DifferentialGeometry.Geometry.Curvature.RealTimeInterval}
    (S : SolutionOn (I := I) (M := M) D)
    {K a t0 t : Real} {x : M} (hK : 0 < K) (ha : 0 < a)
    (hτ : 0 ≤ t - t0) (hdim : Module.finrank Real (TangentSpace I x) = 3)
    {v : TangentSpace I x} (hunit : (S.base.metric t).inner x v v = 1) :
    S.scalar t x / 2 -
        hamiltonIveyBarrier K (t - t0)
          (pinchHeight3 (leastCurvatureOperatorEigenvalueAt (I := I)
            (S.base.metric t) x
            ⟨S.base.rm04 t x, metricRm04At_mem_algebraicCurvatureTensorSubmodule
              (I := I) (S.base.metric t) x⟩)) ≤
      a * twoTensorSecToFamily (I := I) (M := M)
        (hamiltonIveySupportUpperSec (I := I) (M := M) S K a t0) t x v v := by
  classical
  obtain ⟨basis, l1, l2, l3, horth, h21, h32, hdiag⟩ :=
    ricciEigen3_ordered (I := I) (S.base.metric t) (S.ricci t x) hdim
      (ricciAt_symm (I := I) (M := M) S t x)
  have hdiag_sum : RicciDiagAt (I := I) (S.ricci t x) (l1 + l2 + l3) l1 l2 l3 basis := by
    simpa [ricciEigenScalar3] using hdiag
  have hscalar_trace :
      metricTracePair0SAt (I := I) (S.base.metric t) (S.ricci t x) = l1 + l2 + l3 := by
    calc
      metricTracePair0SAt (I := I) (S.base.metric t) (S.ricci t x)
          = ricciScal3 (fun a b : Fin 3 =>
              (S.ricci t x) (vec2 (I := I) (basis a) (basis b))) := by
            exact metricTrace_comp_orthonormal (I := I) (M := M) basis horth (S.ricci t x)
      _ = l1 + l2 + l3 := by
            unfold ricciScal3
            simp only [Fin.sum_univ_three]
            have hval : ∀ i j : Fin 3,
                (S.ricci t x) (vec2 (I := I) (basis i) (basis j)) =
                  ricciDiag3 l1 l2 l3 i j := by
              intro i j
              simpa [ricciCompAt_apply] using hdiag_sum.2 i j
            rw [hval 0 0, hval 1 1, hval 2 2]
            simp [ricciDiag3]
  have hscalar_flow : S.scalar t x = l1 + l2 + l3 := by
    rw [SolutionOn.scalar_eq_metricTrace]
    exact hscalar_trace
  have hmin := orderedSectionalCurvaturesAt_ricciEigen_min
    (I := I) (M := M) S horth h21 h32 hdiag_sum
  have hleast := leastCurvatureOperatorEigenvalueAt_eq_sectionalMin
    (I := I) (S.base.metric t) x basis horth
    ⟨S.base.rm04 t x, metricRm04At_mem_algebraicCurvatureTensorSubmodule
      (I := I) (S.base.metric t) x⟩
  have hgap := hamiltonIveyBarrier_sub_le_supportEigenGap
    (K := K) (τ := t - t0) (a := a) (l3 := (l1 + l2 + l3) / 2 - l1)
    (S := (l1 + l2 + l3) / 2) hK hτ ha.le
  have hb := hamiltonIveySupportUpperSec_lowerBound_ricciEigen
    (I := I) (M := M) S (K := K) (a := a) (t0 := t0) ha horth h21 h32 hdiag_sum hunit
  have hb_mul : DifferentialGeometry.Geometry.Curvature.DimensionThree.hamiltonIveySupportEigenGap
      K (t - t0) a ((l1 + l2 + l3) / 2 - l1) ((l1 + l2 + l3) / 2) ≤
      a * twoTensorSecToFamily (I := I) (M := M)
        (hamiltonIveySupportUpperSec (I := I) (M := M) S K a t0) t x v v := by
    have hmul := mul_le_mul_of_nonneg_left hb ha.le
    field_simp [ha.ne'] at hmul
    ring_nf at hmul ⊢
    exact hmul
  have hmain : (l1 + l2 + l3) / 2 -
      hamiltonIveyBarrier K (t - t0)
        (pinchHeight3 (leastCurvatureOperatorEigenvalueAt (I := I)
          (S.base.metric t) x
          ⟨S.base.rm04 t x, metricRm04At_mem_algebraicCurvatureTensorSubmodule
            (I := I) (S.base.metric t) x⟩)) ≤
      a * twoTensorSecToFamily (I := I) (M := M)
        (hamiltonIveySupportUpperSec (I := I) (M := M) S K a t0) t x v v := by
    have hpinch : pinchHeight3 (leastCurvatureOperatorEigenvalueAt (I := I)
        (S.base.metric t) x
        ⟨S.base.rm04 t x, metricRm04At_mem_algebraicCurvatureTensorSubmodule
          (I := I) (S.base.metric t) x⟩) =
        pinchHeight3 ((l1 + l2 + l3) / 2 - l1) := by
      rw [hleast, hmin]
    rw [hpinch]
    exact hgap.trans hb_mul
  rw [SolutionOn.scalar_eq_metricTrace]
  change metricTracePair0SAt (I := I) (S.base.metric t) (S.base.ricciAt t x) / 2 -
      hamiltonIveyBarrier K (t - t0)
        (pinchHeight3 (leastCurvatureOperatorEigenvalueAt (I := I)
          (S.base.metric t) x
          ⟨S.base.rm04 t x, metricRm04At_mem_algebraicCurvatureTensorSubmodule
            (I := I) (S.base.metric t) x⟩)) ≤
    a * twoTensorSecToFamily (I := I) (M := M)
      (hamiltonIveySupportUpperSec (I := I) (M := M) S K a t0) t x v v
  rw [show S.base.ricciAt t x = S.ricci t x from rfl]
  rw [hscalar_trace]
  exact hmain

theorem exists_hamiltonIveySupportUpperSec_eigenGap
    {D : DifferentialGeometry.Geometry.Curvature.RealTimeInterval}
    (S : SolutionOn (I := I) (M := M) D)
    {K a t0 t : Real} {x : M} (ha : 0 < a)
    (hdim : Module.finrank Real (TangentSpace I x) = 3) :
    ∃ basis : Module.Basis (Fin 3) Real (TangentSpace I x),
      ∃ l1 l2 l3 : Real,
        OrthonormalBasisAt (I := I) (S.base.metric t) x basis ∧
        l2 ≤ l1 ∧ l3 ≤ l2 ∧
        RicciDiagAt (I := I) (S.ricci t x) (l1 + l2 + l3) l1 l2 l3 basis ∧
        orderedSectionalCurvaturesAt (I := I) x basis
            ⟨S.base.rm04 t x, metricRm04At_mem_algebraicCurvatureTensorSubmodule
              (I := I) (S.base.metric t) x⟩ 2 =
          (l1 + l2 + l3) / 2 - l1 ∧
        a * twoTensorSecToFamily (I := I) (M := M)
            (hamiltonIveySupportUpperSec (I := I) (M := M) S K a t0) t x
            (basis 0) (basis 0) =
          DifferentialGeometry.Geometry.Curvature.DimensionThree.hamiltonIveySupportEigenGap
            K (t - t0) a
            (orderedSectionalCurvaturesAt (I := I) x basis
              ⟨S.base.rm04 t x, metricRm04At_mem_algebraicCurvatureTensorSubmodule
                (I := I) (S.base.metric t) x⟩ 2)
            (S.scalar t x / 2) := by
  classical
  obtain ⟨basis, l1, l2, l3, horth, h21, h32, hdiag⟩ :=
    ricciEigen3_ordered (I := I) (S.base.metric t) (S.ricci t x) hdim
      (ricciAt_symm (I := I) (M := M) S t x)
  have hdiag_sum : RicciDiagAt (I := I) (S.ricci t x) (l1 + l2 + l3) l1 l2 l3 basis := by
    simpa [ricciEigenScalar3] using hdiag
  have hval : ∀ i j : Fin 3,
      (S.ricci t x) (vec2 (I := I) (basis i) (basis j)) = ricciDiag3 l1 l2 l3 i j := by
    intro i j
    simpa [ricciCompAt_apply] using hdiag_sum.2 i j
  have hscalar_trace :
      metricTracePair0SAt (I := I) (S.base.metric t) (S.ricci t x) = l1 + l2 + l3 := by
    calc
      metricTracePair0SAt (I := I) (S.base.metric t) (S.ricci t x)
          = ricciScal3 (fun a b : Fin 3 =>
              (S.ricci t x) (vec2 (I := I) (basis a) (basis b))) := by
            exact metricTrace_comp_orthonormal (I := I) (M := M) basis horth (S.ricci t x)
      _ = l1 + l2 + l3 := by
            unfold ricciScal3
            simp only [Fin.sum_univ_three]
            rw [hval 0 0, hval 1 1, hval 2 2]
            simp [ricciDiag3]
  have hscalar_flow : S.scalar t x = l1 + l2 + l3 := by
    rw [SolutionOn.scalar_eq_metricTrace]
    exact hscalar_trace
  have hmin := orderedSectionalCurvaturesAt_ricciEigen_min
    (I := I) (M := M) S horth h21 h32 hdiag_sum
  have heval := hamiltonIveySupportUpperSec_eval_ricciEigen
    (I := I) (M := M) S (K := K) (t0 := t0) ha horth hdiag_sum
  refine ⟨basis, l1, l2, l3, horth, h21, h32, hdiag_sum, hmin, ?_⟩
  rw [heval]
  rw [← hmin]
  have hsumhalf : (l1 + l2 + l3) / 2 = S.scalar t x / 2 := by
    rw [hscalar_flow]
  rw [hsumhalf]

theorem hamiltonIveySupportUpperSec_quad_eq_leastEigen_gap_at_failure
    {D : DifferentialGeometry.Geometry.Curvature.RealTimeInterval}
    (S : SolutionOn (I := I) (M := M) D)
    {K t0 t : Real} {x : M} (hK : 0 < K) (hτ : 0 ≤ t - t0)
    (hdim : Module.finrank Real (TangentSpace I x) = 3)
    (hscalar : scalarSectionalLowerBarrier3 K (t - t0) ≤ S.scalar t x / 2)
    (hfail : S.scalar t x / 2 <
      hamiltonIveyConvexBarrier K (t - t0)
        (pinchHeight3 (leastCurvatureOperatorEigenvalueAt (I := I)
          (S.base.metric t) x
          ⟨S.base.rm04 t x, metricRm04At_mem_algebraicCurvatureTensorSubmodule
            (I := I) (S.base.metric t) x⟩))) :
    ∃ a : Real, 0 < a ∧
      ∃ v : TangentSpace I x,
        (S.base.metric t).inner x v v = 1 ∧
        a * twoTensorSecToFamily (I := I) (M := M)
            (hamiltonIveySupportUpperSec (I := I) (M := M) S K a t0) t x v v =
          S.scalar t x / 2 -
            hamiltonIveyBarrier K (t - t0)
              (pinchHeight3 (leastCurvatureOperatorEigenvalueAt (I := I)
                (S.base.metric t) x
                ⟨S.base.rm04 t x, metricRm04At_mem_algebraicCurvatureTensorSubmodule
                  (I := I) (S.base.metric t) x⟩)) := by
  classical
  obtain ⟨basis, l1, l2, l3, horth, h21, h32, hdiag⟩ :=
    ricciEigen3_ordered (I := I) (S.base.metric t) (S.ricci t x) hdim
      (ricciAt_symm (I := I) (M := M) S t x)
  have hdiag_sum : RicciDiagAt (I := I) (S.ricci t x) (l1 + l2 + l3) l1 l2 l3 basis := by
    simpa [ricciEigenScalar3] using hdiag
  have hmin := orderedSectionalCurvaturesAt_ricciEigen_min
    (I := I) (M := M) S horth h21 h32 hdiag_sum
  have hleast := leastCurvatureOperatorEigenvalueAt_eq_sectionalMin
    (I := I) (S.base.metric t) x basis horth
    ⟨S.base.rm04 t x, metricRm04At_mem_algebraicCurvatureTensorSubmodule
      (I := I) (S.base.metric t) x⟩
  let ν : Real := leastCurvatureOperatorEigenvalueAt (I := I)
    (S.base.metric t) x
    ⟨S.base.rm04 t x, metricRm04At_mem_algebraicCurvatureTensorSubmodule
      (I := I) (S.base.metric t) x⟩
  let νbasis : Real := orderedSectionalCurvaturesAt (I := I) x basis
    ⟨S.base.rm04 t x, metricRm04At_mem_algebraicCurvatureTensorSubmodule
      (I := I) (S.base.metric t) x⟩ 2
  have hνbasis : νbasis = ν := by
    dsimp [νbasis, ν]
    rw [← hleast]
  have h21o := orderedSectionalCurvaturesAt_one_le_zero (I := I) x basis
    ⟨S.base.rm04 t x, metricRm04At_mem_algebraicCurvatureTensorSubmodule
      (I := I) (S.base.metric t) x⟩
  have h32o := orderedSectionalCurvaturesAt_two_le_one (I := I) x basis
    ⟨S.base.rm04 t x, metricRm04At_mem_algebraicCurvatureTensorSubmodule
      (I := I) (S.base.metric t) x⟩
  have hsum_scalar := scalar_eq_two_mul_sum_orderedSectionalCurvaturesAt
    (I := I) (M := M) S basis horth
  have hsum_os : S.scalar t x / 2 =
      ∑ i : Fin 3, orderedSectionalCurvaturesAt (I := I) x basis
        ⟨S.base.rm04 t x, metricRm04At_mem_algebraicCurvatureTensorSubmodule
          (I := I) (S.base.metric t) x⟩ i := by
    nlinarith
  have hS3 : -3 * pinchHeight3 ν ≤ S.scalar t x / 2 := by
    by_cases hν0 : νbasis < 0
    · have hpinch : pinchHeight3 ν = -νbasis := by
        change pinchHeight3 ν = -νbasis
        rw [← hνbasis]
        unfold pinchHeight3
        exact max_eq_left (neg_nonneg.mpr hν0.le)
      rw [hpinch]
      have hle : ∀ i : Fin 3, νbasis ≤
          orderedSectionalCurvaturesAt (I := I) x basis
            ⟨S.base.rm04 t x, metricRm04At_mem_algebraicCurvatureTensorSubmodule
              (I := I) (S.base.metric t) x⟩ i := by
        intro i
        have hanti := orderedSectionalCurvaturesAt_antitone (I := I) x basis
          ⟨S.base.rm04 t x, metricRm04At_mem_algebraicCurvatureTensorSubmodule
            (I := I) (S.base.metric t) x⟩
        exact hanti (show i ≤ (2 : Fin 3) from Nat.le_of_lt_succ i.2)
      have hsumle : 3 * νbasis ≤
          ∑ i : Fin 3, orderedSectionalCurvaturesAt (I := I) x basis
            ⟨S.base.rm04 t x, metricRm04At_mem_algebraicCurvatureTensorSubmodule
              (I := I) (S.base.metric t) x⟩ i := by
        have hraw := Finset.sum_le_sum (s := Finset.univ) (fun i _ => hle i)
        simpa [Fin.sum_univ_three, mul_assoc, mul_comm, mul_left_comm] using hraw
      rw [hsum_os]
      nlinarith
    · have hpinch : pinchHeight3 ν = 0 := by
        change pinchHeight3 ν = 0
        rw [← hνbasis]
        unfold pinchHeight3
        exact max_eq_right (neg_nonpos.mpr (not_lt.mp hν0))
      rw [hpinch, hsum_os]
      have hnonneg : ∀ i : Fin 3, 0 ≤
          orderedSectionalCurvaturesAt (I := I) x basis
            ⟨S.base.rm04 t x, metricRm04At_mem_algebraicCurvatureTensorSubmodule
              (I := I) (S.base.metric t) x⟩ i := by
        intro i
        have hanti := orderedSectionalCurvaturesAt_antitone (I := I) x basis
          ⟨S.base.rm04 t x, metricRm04At_mem_algebraicCurvatureTensorSubmodule
            (I := I) (S.base.metric t) x⟩
        exact (not_lt.mp hν0).trans (hanti (show i ≤ (2 : Fin 3) from Nat.le_of_lt_succ i.2))
      simpa using (Finset.sum_nonneg (fun i _ => hnonneg i))
  have hfail' : S.scalar t x / 2 <
      hamiltonIveyConvexBarrier K (t - t0) (pinchHeight3 ν) := by
    simpa [ν] using hfail
  have hpos := hamiltonIveyConvexBarrier_failure_pinch_pos
    (K := K) (τ := t - t0) (X := pinchHeight3 ν) (S := S.scalar t x / 2)
    hK hτ (le_max_right _ _) hS3 hscalar hfail'
  have hXpos : 0 < pinchHeight3 ν := hpos.1
  have hbar_fail : S.scalar t x / 2 < hamiltonIveyBarrier K (t - t0) (pinchHeight3 ν) := hpos.2
  let a : Real := Real.log (pinchHeight3 ν / K) + Real.log (1 + 2 * K * (t - t0)) - 2
  have ha : 0 < a := hamiltonIveyBarrier_slope_pos_of_scalarLower_of_lt
    (K := K) (τ := t - t0) (X := pinchHeight3 ν) (S := S.scalar t x / 2)
    hK hτ hXpos hS3 hscalar hbar_fail
  have hνneg : νbasis < 0 := by
    by_contra hnot
    have hzero : pinchHeight3 ν = 0 := by
      change pinchHeight3 ν = 0
      rw [← hνbasis]
      unfold pinchHeight3
      exact max_eq_right (neg_nonpos.mpr (not_lt.mp hnot))
    linarith
  have hXeq : pinchHeight3 ν = -νbasis := by
    change pinchHeight3 ν = -νbasis
    rw [← hνbasis]
    unfold pinchHeight3
    exact max_eq_left (neg_nonneg.mpr hνneg.le)
  obtain ⟨basis2, l1', l2', l3', horth2, _h21', _h32', _hdiag', hmin2, heval⟩ :=
    exists_hamiltonIveySupportUpperSec_eigenGap
      (I := I) (M := M) S (K := K) (a := a) (t0 := t0) ha hdim
  have hleast2 := leastCurvatureOperatorEigenvalueAt_eq_sectionalMin
    (I := I) (S.base.metric t) x basis2 horth2
    ⟨S.base.rm04 t x, metricRm04At_mem_algebraicCurvatureTensorSubmodule
      (I := I) (S.base.metric t) x⟩
  have hord2 : orderedSectionalCurvaturesAt (I := I) x basis2
      ⟨S.base.rm04 t x, metricRm04At_mem_algebraicCurvatureTensorSubmodule
        (I := I) (S.base.metric t) x⟩ 2 = ν := by
    dsimp [ν]
    rw [hleast2]
  have hevalν : a * twoTensorSecToFamily (I := I) (M := M)
      (hamiltonIveySupportUpperSec (I := I) (M := M) S K a t0) t x
      (basis2 0) (basis2 0) =
      hamiltonIveySupportEigenGap K (t - t0) a ν (S.scalar t x / 2) := by
    simpa [hord2] using heval
  have hgap_eq : hamiltonIveySupportEigenGap K (t - t0) a ν (S.scalar t x / 2) =
      hamiltonIveySupportGap K (t - t0) a (pinchHeight3 ν) (S.scalar t x / 2) := by
    have hrel := hamiltonIveySupportGap_eq_of_pinch_eq
      (K := K) (τ := t - t0) (a := a) (X := pinchHeight3 ν) (l3 := ν)
      (S := S.scalar t x / 2) rfl
    have hνbasis_eq : ν = νbasis := by
      simpa [ν, νbasis] using hleast
    rw [hXeq, hνbasis_eq] at hrel ⊢
    simpa using hrel
  have hgap_barrier : hamiltonIveySupportGap K (t - t0) a (pinchHeight3 ν) (S.scalar t x / 2) =
      S.scalar t x / 2 - hamiltonIveyBarrier K (t - t0) (pinchHeight3 ν) := by
    dsimp [a]
    exact hamiltonIveySupportGap_eq_barrier_sub_of_slope
      (K := K) (τ := t - t0) (X := pinchHeight3 ν) (S := S.scalar t x / 2)
      hK hτ hXpos
  have hunit : (S.base.metric t).inner x (basis2 0) (basis2 0) = 1 := by
    simpa [DifferentialGeometry.Geometry.Curvature.delta3] using horth2 0 0
  refine ⟨a, ha, basis2 0, hunit, ?_⟩
  rw [hevalν, hgap_eq, hgap_barrier]

theorem curvatureOperatorRegionPropagationOn_of_supportUpper_nonneg
    {D : DifferentialGeometry.Geometry.Curvature.RealTimeInterval}
    (S : SolutionOn (I := I) (M := M) D)
    {t0 T K : Real} (hK : 0 < K)
    (hdim : ∀ x : M, Module.finrank Real (TangentSpace I x) = 3)
    (hscalar : ∀ t : Real, t ∈ Set.Icc t0 (t0 + T) → ∀ x : M,
      scalarSectionalLowerBarrier3 K (t - t0) ≤ S.scalar t x / 2)
    (hnonneg : ∀ a : Real, 0 < a → ∀ t : Real, t ∈ Set.Icc t0 (t0 + T) →
      ∀ x : M, ∀ v : TangentSpace I x,
        0 ≤ a * twoTensorSecToFamily (I := I) (M := M)
          (hamiltonIveySupportUpperSec (I := I) (M := M) S K a t0) t x v v) :
    CurvatureOperatorRegionPropagationOn (I := I) (M := M) S K t0 T := by
  intro t ht x
  by_contra hnot
  obtain ⟨basis, horth⟩ := exists_orthonormalBasisAt (I := I) (S.base.metric t) x (hdim x)
  let A : algebraicCurvatureTensorSubmodule (I := I) (M := M) x :=
    ⟨S.base.rm04 t x, metricRm04At_mem_algebraicCurvatureTensorSubmodule
      (I := I) (S.base.metric t) x⟩
  let Mtx : Matrix (Fin 3) (Fin 3) Real := curvatureOperatorMatrixAt (I := I) x basis A
  have hnot_basis : Mtx ∉ hamiltonIveyConvexMatrixRegion K (t - t0) := by
    intro hmem
    exact hnot ⟨basis, horth, hmem⟩
  have hherm : Mtx.IsHermitian := by
    dsimp [Mtx]
    exact curvatureOperatorMatrixAt_isHermitian (I := I) x basis A
  have hfirst : 0 ≤ max (-(curvatureOperatorMatrixAt_isHermitian (I := I) x basis A).eigenvalues₀ 2) 0 :=
    le_max_right _ _
  have hbar_lt : Mtx.trace < hamiltonIveyConvexBarrier K (t - t0)
      (max (-(curvatureOperatorMatrixAt_isHermitian (I := I) x basis A).eigenvalues₀ 2) 0) := by
    have hnot_viol : ¬ hamiltonIveyConvexMatrixRegionViolation K (t - t0) Mtx := by
      intro hv
      apply hnot_basis
      rw [hamiltonIveyConvexMatrixRegion_eq_violation]
      exact hv
    have hfirst' : 0 ≤ max (-DifferentialGeometry.Analysis.Convex.sectionalRayleighMin3 Mtx) 0 :=
      le_max_right _ _
    have hle : hamiltonIveyConvexBarrier K (t - t0)
        (max (-(curvatureOperatorMatrixAt_isHermitian (I := I) x basis A).eigenvalues₀ 2) 0) ≤
        Mtx.trace → False := by
      intro hle
      have hle' : hamiltonIveyConvexBarrier K (t - t0)
          (max (-DifferentialGeometry.Analysis.Convex.sectionalRayleighMin3 Mtx) 0) ≤
          Mtx.trace := by
        simpa [DifferentialGeometry.Analysis.Convex.sectionalRayleighMin3_eq_eigenvalue_min hherm] using hle
      exact hnot_viol ⟨hherm, hfirst', hle'⟩
    exact lt_of_not_ge hle
  have hleast : leastCurvatureOperatorEigenvalueAt (I := I) (S.base.metric t) x A =
      orderedSectionalCurvaturesAt (I := I) x basis A 2 :=
    leastCurvatureOperatorEigenvalueAt_eq_sectionalMin
      (I := I) (S.base.metric t) x basis horth A
  have hord2 : (curvatureOperatorMatrixAt_isHermitian (I := I) x basis A).eigenvalues₀ 2 =
      orderedSectionalCurvaturesAt (I := I) x basis A 2 := rfl
  have hpinch : max (-(curvatureOperatorMatrixAt_isHermitian (I := I) x basis A).eigenvalues₀ 2) 0 =
      pinchHeight3 (leastCurvatureOperatorEigenvalueAt (I := I) (S.base.metric t) x A) := by
    rw [hord2, ← hleast]
    rfl
  have hbar_lt' : Mtx.trace < hamiltonIveyConvexBarrier K (t - t0)
      (pinchHeight3 (leastCurvatureOperatorEigenvalueAt (I := I) (S.base.metric t) x A)) := by
    simpa [hpinch] using hbar_lt
  have htrace := curvatureOperatorMatrixAt_trace_eq_sum_orderedSectionalCurvaturesAt
    (I := I) x basis A
  have hscalar_eq := scalar_eq_two_mul_sum_orderedSectionalCurvaturesAt
    (I := I) (M := M) S basis horth
  have hsum : Mtx.trace = S.scalar t x / 2 := by
    dsimp [Mtx]
    rw [htrace]
    nlinarith [hscalar_eq]
  have hfail : S.scalar t x / 2 < hamiltonIveyConvexBarrier K (t - t0)
      (pinchHeight3 (leastCurvatureOperatorEigenvalueAt (I := I) (S.base.metric t) x A)) := by
    rwa [hsum] at hbar_lt'
  obtain ⟨a, ha, v, hunit, heq⟩ := hamiltonIveySupportUpperSec_quad_eq_leastEigen_gap_at_failure
    (I := I) (M := M) S (K := K) (t0 := t0) (t := t) (x := x)
    hK (by linarith [ht.1]) (hdim x) (hscalar t ht x) hfail
  have hbar_gt : S.scalar t x / 2 < hamiltonIveyBarrier K (t - t0)
      (pinchHeight3 (leastCurvatureOperatorEigenvalueAt (I := I) (S.base.metric t) x A)) := by
    have hmax := hfail
    unfold hamiltonIveyConvexBarrier at hmax
    by_cases hle : hamiltonIveyBarrier K (t - t0)
        (pinchHeight3 (leastCurvatureOperatorEigenvalueAt (I := I) (S.base.metric t) x A)) ≤
        scalarSectionalLowerBarrier3 K (t - t0)
    · rw [max_eq_left hle] at hmax
      linarith [hscalar t ht x]
    · have hnotle : scalarSectionalLowerBarrier3 K (t - t0) <
          hamiltonIveyBarrier K (t - t0)
            (pinchHeight3 (leastCurvatureOperatorEigenvalueAt (I := I) (S.base.metric t) x A)) :=
        lt_of_not_ge hle
      rw [max_eq_right (le_of_lt hnotle)] at hmax
      exact hmax
  have hnon := hnonneg a ha t ht x v
  have hneg : a * twoTensorSecToFamily (I := I) (M := M)
      (hamiltonIveySupportUpperSec (I := I) (M := M) S K a t0) t x v v < 0 := by
    rw [heq]
    linarith
  exact (not_lt_of_ge hnon) hneg



theorem hamiltonIveySupportUpperSec_initial_nonneg_unit
    {D : DifferentialGeometry.Geometry.Curvature.RealTimeInterval}
    (S : SolutionOn (I := I) (M := M) D)
    {K t0 a : Real} {x : M} (hK : 0 < K) (ha : 0 < a)
    (hdim : Module.finrank Real (TangentSpace I x) = 3)
    (hinit : CurvatureOperatorLowerBoundAt (I := I) (S.base.metric t0) x
      ⟨S.base.rm04 t0 x, metricRm04At_mem_algebraicCurvatureTensorSubmodule
        (I := I) (S.base.metric t0) x⟩ K)
    {v : TangentSpace I x} (hunit : (S.base.metric t0).inner x v v = 1) :
    0 ≤ a * twoTensorSecToFamily (I := I) (M := M)
      (hamiltonIveySupportUpperSec (I := I) (M := M) S K a t0) t0 x v v := by
  let A : algebraicCurvatureTensorSubmodule (I := I) (M := M) x :=
    ⟨S.base.rm04 t0 x, metricRm04At_mem_algebraicCurvatureTensorSubmodule
      (I := I) (S.base.metric t0) x⟩
  have hgap := hamiltonIveySupportUpperSec_quad_ge_leastEigen_gap
    (I := I) (M := M) S (K := K) (a := a) (t0 := t0) (t := t0) (x := x)
    hK ha (by simp) hdim hunit
  have hle0 : hamiltonIveyBarrier K 0
      (pinchHeight3 (leastCurvatureOperatorEigenvalueAt (I := I) (S.base.metric t0) x A)) ≤
      S.scalar t0 x / 2 := by
    obtain ⟨basis, horth⟩ := exists_orthonormalBasisAt (I := I) (S.base.metric t0) x hdim
    have hmem := curvatureOperatorMatrixAt_initial_mem_hamiltonIveyConvexMatrixRegion
      (I := I) (M := M) S hK basis horth hinit
    have htrace := curvatureOperatorMatrixAt_trace_eq_sum_orderedSectionalCurvaturesAt
      (I := I) x basis A
    have hscalar_eq := scalar_eq_two_mul_sum_orderedSectionalCurvaturesAt
      (I := I) (M := M) S basis horth
    have hsum : (curvatureOperatorMatrixAt (I := I) x basis A).trace = S.scalar t0 x / 2 := by
      rw [htrace]
      nlinarith [hscalar_eq]
    rcases hmem with ⟨_hM, _hX, hbar⟩
    have hbar' : hamiltonIveyConvexBarrier K 0
        (pinchHeight3 (orderedSectionalCurvaturesAt (I := I) x basis A 2)) ≤
        S.scalar t0 x / 2 := by
      rw [← hsum]
      simpa [A, pinchHeight3] using hbar
    have hbar_le : hamiltonIveyBarrier K 0
        (pinchHeight3 (orderedSectionalCurvaturesAt (I := I) x basis A 2)) ≤
        S.scalar t0 x / 2 :=
      (hamiltonIveyBarrier_le_hamiltonIveyConvexBarrier K 0 _).trans hbar'
    have hleast : leastCurvatureOperatorEigenvalueAt (I := I) (S.base.metric t0) x A =
        orderedSectionalCurvaturesAt (I := I) x basis A 2 :=
      leastCurvatureOperatorEigenvalueAt_eq_sectionalMin
        (I := I) (S.base.metric t0) x basis horth A
    simpa [hleast] using hbar_le
  have hnon : 0 ≤ S.scalar t0 x / 2 -
      hamiltonIveyBarrier K 0
        (pinchHeight3 (leastCurvatureOperatorEigenvalueAt (I := I) (S.base.metric t0) x A)) :=
    sub_nonneg.mpr hle0
  have hB : S.scalar t0 x / 2 -
      hamiltonIveyBarrier K 0
        (pinchHeight3 (leastCurvatureOperatorEigenvalueAt (I := I) (S.base.metric t0) x A)) ≤
      a * twoTensorSecToFamily (I := I) (M := M)
        (hamiltonIveySupportUpperSec (I := I) (M := M) S K a t0) t0 x v v := by
    simpa [A] using hgap
  linarith



theorem hamiltonIveySupportUpperSec_initial_nonneg
    {D : DifferentialGeometry.Geometry.Curvature.RealTimeInterval}
    (S : SolutionOn (I := I) (M := M) D)
    {K t0 a : Real} {x : M} (hK : 0 < K) (ha : 0 < a)
    (hdim : Module.finrank Real (TangentSpace I x) = 3)
    (hinit : CurvatureOperatorLowerBoundAt (I := I) (S.base.metric t0) x
      ⟨S.base.rm04 t0 x, metricRm04At_mem_algebraicCurvatureTensorSubmodule
        (I := I) (S.base.metric t0) x⟩ K)
    (v : TangentSpace I x) :
    0 ≤ a * twoTensorSecToFamily (I := I) (M := M)
      (hamiltonIveySupportUpperSec (I := I) (M := M) S K a t0) t0 x v v := by
  by_cases hv : v = 0
  · subst v
    have hzero : twoTensorSecToFamily (I := I) (M := M)
        (hamiltonIveySupportUpperSec (I := I) (M := M) S K a t0) t0 x 0 0 = 0 := by
      let A : Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) 2 x :=
        hamiltonIveySupportUpperSec (I := I) (M := M) S K a t0 t0 x
      change A (vec2 (0 : TangentSpace I x) (0 : TangentSpace I x)) = 0
      have hvec : vec2 (0 : TangentSpace I x) (0 : TangentSpace I x) =
          (0 : Fin 2 → TangentSpace I x) := by
        funext i
        fin_cases i <;> rfl
      rw [hvec]
      exact A.map_coord_zero (0 : Fin 2) rfl
    rw [hzero]
    simp
  · obtain ⟨nb⟩ := exists_nullOrthonormalBasis3At (I := I) (S.base.metric t0) hdim hv
    rcases nb.scale with ⟨r, hr, hscale⟩
    have hunit : (S.base.metric t0).inner x (nb.basis 0) (nb.basis 0) = 1 := by
      simpa [DifferentialGeometry.Geometry.Curvature.delta3] using nb.orthonormal 0 0
    have hnon := hamiltonIveySupportUpperSec_initial_nonneg_unit
      (I := I) (M := M) S hK ha hdim hinit (v := nb.basis 0) hunit
    let A : Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) 2 x :=
      hamiltonIveySupportUpperSec (I := I) (M := M) S K a t0 t0 x
    have hquad := tensor02_smul2 (I := I) (M := M) A r (nb.basis 0)
    have hB : twoTensorSecToFamily (I := I) (M := M)
        (hamiltonIveySupportUpperSec (I := I) (M := M) S K a t0) t0 x v v =
        r * r * twoTensorSecToFamily (I := I) (M := M)
          (hamiltonIveySupportUpperSec (I := I) (M := M) S K a t0) t0 x
            (nb.basis 0) (nb.basis 0) := by
      conv_lhs => rw [hscale]
      have hq : quad02 (I := I) (M := M) A (r • nb.basis 0) =
          twoTensorSecToFamily (I := I) (M := M)
            (hamiltonIveySupportUpperSec (I := I) (M := M) S K a t0) t0 x
              (r • nb.basis 0) (r • nb.basis 0) :=
        quad02_sec_eq (S := hamiltonIveySupportUpperSec (I := I) (M := M) S K a t0)
          t0 x (r • nb.basis 0)
      rw [← hq]
      have hquad' : quad02 (I := I) (M := M) A (r • nb.basis 0) =
          r * r * quad02 (I := I) (M := M) A (nb.basis 0) := by
        simpa [quad02, vec2_self_eq_const, pow_two] using hquad (nb.basis 0)
      rw [hquad']
      rw [quad02_sec_eq (S := hamiltonIveySupportUpperSec (I := I) (M := M) S K a t0)
        t0 x (nb.basis 0)]
    rw [hB]
    have hle : 0 ≤ a * (r * r * twoTensorSecToFamily (I := I) (M := M)
        (hamiltonIveySupportUpperSec (I := I) (M := M) S K a t0) t0 x
          (nb.basis 0) (nb.basis 0)) := by
      have hnon' : 0 ≤ (r * r) * (a * twoTensorSecToFamily (I := I) (M := M)
          (hamiltonIveySupportUpperSec (I := I) (M := M) S K a t0) t0 x
            (nb.basis 0) (nb.basis 0)) :=
        mul_nonneg (by simpa [pow_two] using (sq_nonneg r)) hnon
      convert hnon' using 1
      ring
    simpa [mul_assoc, mul_comm, mul_left_comm] using hle


theorem hamilton_ivey_pinching_of_supportUpper_nonneg
    {D : DifferentialGeometry.Geometry.Curvature.RealTimeInterval}
    (S : SolutionOn (I := I) (M := M) D)
    {t0 T K : Real} (hK : 0 < K)
    (hslab : Set.Icc t0 (t0 + T) ⊆ D.carrier)
    (hdim : ∀ x : M, Module.finrank Real (TangentSpace I x) = 3)
    (hscalar : ∀ t : Real, t ∈ Set.Icc t0 (t0 + T) → ∀ x : M,
      scalarSectionalLowerBarrier3 K (t - t0) ≤ S.scalar t x / 2)
    (hnonneg : ∀ a : Real, 0 < a → ∀ t : Real, t ∈ Set.Icc t0 (t0 + T) →
      ∀ x : M, ∀ v : TangentSpace I x,
        0 ≤ a * twoTensorSecToFamily (I := I) (M := M)
          (hamiltonIveySupportUpperSec (I := I) (M := M) S K a t0) t x v v) :
    (∀ t : Real, t ∈ Set.Icc t0 (t0 + T) → ∀ x : M,
      -6 * K / (1 + 4 * K * (t - t0)) ≤ S.scalar t x) ∧
    (∀ t : Real, t ∈ Set.Icc t0 (t0 + T) → ∀ x : M,
      ∀ basis : Module.Basis (Fin 3) Real (TangentSpace I x),
        OrthonormalBasisAt (I := I) (S.base.metric t) x basis →
        orderedSectionalCurvaturesAt (I := I) x basis
            ⟨S.base.rm04 t x, metricRm04At_mem_algebraicCurvatureTensorSubmodule
              (I := I) (S.base.metric t) x⟩ 2 < 0 →
          S.scalar t x ≥
            2 * (-orderedSectionalCurvaturesAt (I := I) x basis
              ⟨S.base.rm04 t x, metricRm04At_mem_algebraicCurvatureTensorSubmodule
                (I := I) (S.base.metric t) x⟩ 2) *
              (Real.log ((-orderedSectionalCurvaturesAt (I := I) x basis
                ⟨S.base.rm04 t x, metricRm04At_mem_algebraicCurvatureTensorSubmodule
                  (I := I) (S.base.metric t) x⟩ 2) / K) +
                Real.log (1 + 2 * K * (t - t0)) - 3)) := by
  have hprop := curvatureOperatorRegionPropagationOn_of_supportUpper_nonneg
    (I := I) (M := M) S hK hdim hscalar hnonneg
  exact hamilton_ivey_pinching_of_curvatureOperatorRegionPropagation
    (I := I) (M := M) S hK hslab hprop


theorem ricciAt_basis_eq_curvatureOperatorMatrix_trace_sub_missing
    {D : DifferentialGeometry.Geometry.Curvature.RealTimeInterval}
    (S : SolutionOn (I := I) (M := M) D)
    {t : Real} {x : M}
    (basis : Module.Basis (Fin 3) Real (TangentSpace I x))
    (horth : OrthonormalBasisAt (I := I) (S.base.metric t) x basis)
    (i : Fin 3) :
    S.ricciAt t x (vec2 (I := I) (basis i) (basis i)) =
      (curvatureOperatorMatrixAt (I := I) x basis
        ⟨S.base.rm04 t x, metricRm04At_mem_algebraicCurvatureTensorSubmodule
          (I := I) (S.base.metric t) x⟩).trace -
        (curvatureOperatorMatrixAt (I := I) x basis
          ⟨S.base.rm04 t x, metricRm04At_mem_algebraicCurvatureTensorSubmodule
            (I := I) (S.base.metric t) x⟩)
          (hamiltonIveySupportUpperMissingPlaneIndex i)
          (hamiltonIveySupportUpperMissingPlaneIndex i) := by
  classical
  let A : algebraicCurvatureTensorSubmodule (I := I) (M := M) x :=
    ⟨S.base.rm04 t x, metricRm04At_mem_algebraicCurvatureTensorSubmodule
      (I := I) (S.base.metric t) x⟩
  have htr := traceData_metricTrace (I := I) (M := M) S horth
  have hric := htr.ricci_trace i i
  have hleft : ricciCompAt (I := I) basis (-(S.ricci t x)) i i =
      - S.ricciAt t x (vec2 (I := I) (basis i) (basis i)) := by
    rw [ricciCompAt_apply]
    simp [SolutionOn.ricciAt, SolutionFamily.ricciAt]
  have hstd : stdRicci3 (standardRmCompAt (I := I) basis (S.base.rm04 t x)) i i =
      -((curvatureOperatorMatrixAt (I := I) x basis A).trace -
        (curvatureOperatorMatrixAt (I := I) x basis A)
          (hamiltonIveySupportUpperMissingPlaneIndex i)
          (hamiltonIveySupportUpperMissingPlaneIndex i)) := by
    fin_cases i
    · have hsym := htr.curvature_symmetries
      have h00 : standardRmCompAt (I := I) basis (S.base.rm04 t x) 0 0 0 0 = 0 := by
        have h := hsym.anti_first 0 0 0 0
        linarith
      have h10 : standardRmCompAt (I := I) basis (S.base.rm04 t x) 1 0 1 0 =
          -curvatureOperatorMatrixAt (I := I) x basis A 0 0 := by
        change standardRmCompAt (I := I) basis (S.base.rm04 t x) 1 0 1 0 =
          - standardRmCompAt (I := I) basis (S.base.rm04 t x) 0 1 1 0
        rw [hsym.anti_first 0 1 1 0]
      have h20 : standardRmCompAt (I := I) basis (S.base.rm04 t x) 2 0 2 0 =
          -curvatureOperatorMatrixAt (I := I) x basis A 1 1 := by
        change standardRmCompAt (I := I) basis (S.base.rm04 t x) 2 0 2 0 =
          - standardRmCompAt (I := I) basis (S.base.rm04 t x) 0 2 2 0
        rw [hsym.anti_first 0 2 2 0]
      change standardRmCompAt (I := I) basis (S.base.rm04 t x) 0 0 0 0 +
          standardRmCompAt (I := I) basis (S.base.rm04 t x) 1 0 1 0 +
          standardRmCompAt (I := I) basis (S.base.rm04 t x) 2 0 2 0 =
        -((curvatureOperatorMatrixAt (I := I) x basis A).trace -
          (curvatureOperatorMatrixAt (I := I) x basis A)
            (hamiltonIveySupportUpperMissingPlaneIndex 0)
            (hamiltonIveySupportUpperMissingPlaneIndex 0))
      rw [h00, h10, h20]
      simp [hamiltonIveySupportUpperMissingPlaneIndex, Matrix.trace, Fin.sum_univ_three]
      ring
    · have hsym := htr.curvature_symmetries
      have h11 : standardRmCompAt (I := I) basis (S.base.rm04 t x) 1 1 1 1 = 0 := by
        have h := hsym.anti_first 1 1 1 1
        linarith
      have h01 : standardRmCompAt (I := I) basis (S.base.rm04 t x) 0 1 0 1 =
          -curvatureOperatorMatrixAt (I := I) x basis A 0 0 := by
        change standardRmCompAt (I := I) basis (S.base.rm04 t x) 0 1 0 1 =
          - standardRmCompAt (I := I) basis (S.base.rm04 t x) 0 1 1 0
        rw [← hsym.anti_last 0 1 1 0]
      have h21 : standardRmCompAt (I := I) basis (S.base.rm04 t x) 2 1 2 1 =
          -curvatureOperatorMatrixAt (I := I) x basis A 2 2 := by
        change standardRmCompAt (I := I) basis (S.base.rm04 t x) 2 1 2 1 =
          - standardRmCompAt (I := I) basis (S.base.rm04 t x) 1 2 2 1
        rw [hsym.anti_first 1 2 2 1]
      change standardRmCompAt (I := I) basis (S.base.rm04 t x) 0 1 0 1 +
          standardRmCompAt (I := I) basis (S.base.rm04 t x) 1 1 1 1 +
          standardRmCompAt (I := I) basis (S.base.rm04 t x) 2 1 2 1 =
        -((curvatureOperatorMatrixAt (I := I) x basis A).trace -
          (curvatureOperatorMatrixAt (I := I) x basis A)
            (hamiltonIveySupportUpperMissingPlaneIndex 1)
            (hamiltonIveySupportUpperMissingPlaneIndex 1))
      rw [h11, h01, h21]
      simp [hamiltonIveySupportUpperMissingPlaneIndex, Matrix.trace, Fin.sum_univ_three]
      ring
    · have hsym := htr.curvature_symmetries
      have h22 : standardRmCompAt (I := I) basis (S.base.rm04 t x) 2 2 2 2 = 0 := by
        have h := hsym.anti_first 2 2 2 2
        linarith
      have h02 : standardRmCompAt (I := I) basis (S.base.rm04 t x) 0 2 0 2 =
          -curvatureOperatorMatrixAt (I := I) x basis A 1 1 := by
        change standardRmCompAt (I := I) basis (S.base.rm04 t x) 0 2 0 2 =
          - standardRmCompAt (I := I) basis (S.base.rm04 t x) 0 2 2 0
        rw [← hsym.anti_last 0 2 2 0]
      have h12 : standardRmCompAt (I := I) basis (S.base.rm04 t x) 1 2 1 2 =
          -curvatureOperatorMatrixAt (I := I) x basis A 2 2 := by
        change standardRmCompAt (I := I) basis (S.base.rm04 t x) 1 2 1 2 =
          - standardRmCompAt (I := I) basis (S.base.rm04 t x) 1 2 2 1
        rw [← hsym.anti_last 1 2 2 1]
      change standardRmCompAt (I := I) basis (S.base.rm04 t x) 0 2 0 2 +
          standardRmCompAt (I := I) basis (S.base.rm04 t x) 1 2 1 2 +
          standardRmCompAt (I := I) basis (S.base.rm04 t x) 2 2 2 2 =
        -((curvatureOperatorMatrixAt (I := I) x basis A).trace -
          (curvatureOperatorMatrixAt (I := I) x basis A)
            (hamiltonIveySupportUpperMissingPlaneIndex 2)
            (hamiltonIveySupportUpperMissingPlaneIndex 2))
      rw [h22, h02, h12]
      simp [hamiltonIveySupportUpperMissingPlaneIndex, Matrix.trace, Fin.sum_univ_three]
      ring
  rw [hleft] at hric
  rw [hstd] at hric
  linarith



theorem supportUpperDiag_eq_coe_sub_inner
    {D : DifferentialGeometry.Geometry.Curvature.RealTimeInterval}
    (S : SolutionOn (I := I) (M := M) D)
    {K a t0 t : Real}
    {x : M} (basis : Module.Basis (Fin 3) Real (TangentSpace I x))
    (horth : OrthonormalBasisAt (I := I) (S.base.metric t) x basis)
    (i : Fin 3) :
    a * twoTensorSecToFamily (I := I) (M := M)
        (hamiltonIveySupportUpperSec (I := I) (M := M) S K a t0) t x
        (basis i) (basis i) =
      a * hamiltonIveySupportCoefficient K a t0 t -
        inner ℝ (matrixToEuclid (hamiltonIveySupportUpperDiagNormal a
          (hamiltonIveySupportPinchDelta a) i))
          (matrixToEuclid (curvatureOperatorMatrixAt (I := I) x basis
            ⟨S.base.rm04 t x, metricRm04At_mem_algebraicCurvatureTensorSubmodule
              (I := I) (S.base.metric t) x⟩)) := by
  classical
  let A : algebraicCurvatureTensorSubmodule (I := I) (M := M) x :=
    ⟨S.base.rm04 t x, metricRm04At_mem_algebraicCurvatureTensorSubmodule
      (I := I) (S.base.metric t) x⟩
  let Mtx : Matrix (Fin 3) (Fin 3) Real := curvatureOperatorMatrixAt (I := I) x basis A
  let δ : Real := hamiltonIveySupportPinchDelta a
  let C : Real := hamiltonIveySupportCoefficient K a t0 t
  have hric := ricciAt_basis_eq_curvatureOperatorMatrix_trace_sub_missing
    (I := I) (M := M) S basis horth i
  have hscalar : S.scalar t x = 2 * Mtx.trace := by
    have hsum := scalar_eq_two_mul_sum_orderedSectionalCurvaturesAt
      (I := I) (M := M) S basis horth
    have htrace := curvatureOperatorMatrixAt_trace_eq_sum_orderedSectionalCurvaturesAt
      (I := I) x basis A
    dsimp [Mtx, A] at htrace
    nlinarith
  have hQ : twoTensorSecToFamily (I := I) (M := M)
        (hamiltonIveySupportUpperSec (I := I) (M := M) S K a t0) t x
        (basis i) (basis i) =
      C + δ * S.scalar t x - S.ricciAt t x (vec2 (I := I) (basis i) (basis i)) := by
    rw [twoTensorSecToFamily_apply]
    rw [hamiltonIveySupportUpperSec_at_point (I := I) S K a t0 t x]
    rw [Tensor0SSpace.sub_apply]
    rw [Tensor0SSpace.smul_apply]
    simp only [metricTensorField_apply, Fin.isValue, smul_eq_mul]
    rw [show vec2 (I := I) (basis i) (basis i) 0 = basis i by rfl]
    rw [show vec2 (I := I) (basis i) (basis i) 1 = basis i by rfl]
    rw [horth i i]
    have hdii : DifferentialGeometry.Geometry.Curvature.delta3 i i = 1 := by
      norm_num [DifferentialGeometry.Geometry.Curvature.delta3]
    rw [hdii]
    have hpinch := pinchSec_at_trace (I := I) (M := M) S ((1 + a) / (2 * a)) t x
    have hpinch_eval :
        (pinchSec (I := I) S ((1 + a) / (2 * a)) t x)
            (vec2 (I := I) (basis i) (basis i)) =
          S.ricciAt t x (vec2 (I := I) (basis i) (basis i)) -
            hamiltonIveySupportPinchDelta a * S.scalar t x := by
      rw [hpinch]
      rw [Tensor0SSpace.sub_apply]
      rw [Tensor0SSpace.smul_apply]
      simp only [metricTensorField_apply, Fin.isValue, smul_eq_mul]
      rw [show vec2 (I := I) (basis i) (basis i) 0 = basis i by rfl]
      rw [show vec2 (I := I) (basis i) (basis i) 1 = basis i by rfl]
      rw [horth i i]
      have hdii' : DifferentialGeometry.Geometry.Curvature.delta3 i i = 1 := by
        norm_num [DifferentialGeometry.Geometry.Curvature.delta3]
      rw [hdii']
      rw [SolutionOn.scalar_eq_metricTrace]
      rw [SolutionOn.ricciAt, SolutionFamily.ricciAt, SolutionOn.family_metric]
      simp only [mul_one]
      rfl
    rw [hpinch_eval]
    ring
  have hdiag := inner_hamiltonIveySupportUpperDiagNormal_diag
    (a := a) (delta := δ) (i := i)
    (d := fun j => Mtx j j)
  have hfull := inner_hamiltonIveySupportUpperDiagNormal_full_eq_diag
    (a := a) (delta := δ) (i := i) (A := Mtx)
  have hpair : inner ℝ (matrixToEuclid (hamiltonIveySupportUpperDiagNormal a δ i))
      (matrixToEuclid Mtx) =
      a * ((1 - 2 * δ) *
            (∑ j : Fin 3, if j = hamiltonIveySupportUpperMissingPlaneIndex i then 0 else Mtx j j) -
          2 * δ * Mtx (hamiltonIveySupportUpperMissingPlaneIndex i)
            (hamiltonIveySupportUpperMissingPlaneIndex i)) := by
    rw [hfull]
    exact hdiag
  have hmain : a * (C + δ * S.scalar t x - S.ricciAt t x (vec2 (I := I) (basis i) (basis i))) =
      a * C - inner ℝ (matrixToEuclid (hamiltonIveySupportUpperDiagNormal a δ i))
          (matrixToEuclid Mtx) := by
    rw [hpair]
    rw [hscalar, hric]
    dsimp [Mtx]
    fin_cases i <;>
      simp [hamiltonIveySupportUpperMissingPlaneIndex, Matrix.trace, Fin.sum_univ_three] <;> ring
  calc
    a * twoTensorSecToFamily (I := I) (M := M)
        (hamiltonIveySupportUpperSec (I := I) (M := M) S K a t0) t x
        (basis i) (basis i)
        = a * (C + δ * S.scalar t x - S.ricciAt t x (vec2 (I := I) (basis i) (basis i))) := by rw [hQ]
    _ = a * C - inner ℝ (matrixToEuclid (hamiltonIveySupportUpperDiagNormal a δ i))
          (matrixToEuclid Mtx) := hmain
    _ = a * hamiltonIveySupportCoefficient K a t0 t -
        inner ℝ (matrixToEuclid (hamiltonIveySupportUpperDiagNormal a
          (hamiltonIveySupportPinchDelta a) i))
          (matrixToEuclid (curvatureOperatorMatrixAt (I := I) x basis
            ⟨S.base.rm04 t x, metricRm04At_mem_algebraicCurvatureTensorSubmodule
              (I := I) (S.base.metric t) x⟩)) := by
          simp [C, δ, Mtx, A]



theorem supportUpperDiag_initial_inner_le
    {D : DifferentialGeometry.Geometry.Curvature.RealTimeInterval}
    (S : SolutionOn (I := I) (M := M) D)
    {K t0 a : Real} {x : M} (hK : 0 < K) (ha : 0 < a)
    (hdim : Module.finrank Real (TangentSpace I x) = 3)
    (hinit : CurvatureOperatorLowerBoundAt (I := I) (S.base.metric t0) x
      ⟨S.base.rm04 t0 x, metricRm04At_mem_algebraicCurvatureTensorSubmodule
        (I := I) (S.base.metric t0) x⟩ K)
    (basis : Module.Basis (Fin 3) Real (TangentSpace I x))
    (horth : OrthonormalBasisAt (I := I) (S.base.metric t0) x basis)
    (i : Fin 3) :
    inner ℝ (matrixToEuclid (hamiltonIveySupportUpperDiagNormal a
        (hamiltonIveySupportPinchDelta a) i))
      (matrixToEuclid (curvatureOperatorMatrixAt (I := I) x basis
        ⟨S.base.rm04 t0 x, metricRm04At_mem_algebraicCurvatureTensorSubmodule
          (I := I) (S.base.metric t0) x⟩)) ≤
      a * hamiltonIveySupportCoefficient K a t0 t0 := by
  have hnon := hamiltonIveySupportUpperSec_initial_nonneg
    (I := I) (M := M) S hK ha hdim hinit (basis i)
  have hrepr := supportUpperDiag_eq_coe_sub_inner
    (I := I) (M := M) S (K := K) (a := a) (t0 := t0) (t := t0)
    basis horth i
  -- hrepr : a * Q = a*C - inner ν A
  have hle : 0 ≤ a * hamiltonIveySupportCoefficient K a t0 t0 -
      inner ℝ (matrixToEuclid (hamiltonIveySupportUpperDiagNormal a
        (hamiltonIveySupportPinchDelta a) i))
      (matrixToEuclid (curvatureOperatorMatrixAt (I := I) x basis
        ⟨S.base.rm04 t0 x, metricRm04At_mem_algebraicCurvatureTensorSubmodule
          (I := I) (S.base.metric t0) x⟩)) := by
    rw [← hrepr]
    exact hnon
  linarith



theorem supportUpperDiag_nonneg_iff_inner_le
    {D : DifferentialGeometry.Geometry.Curvature.RealTimeInterval}
    (S : SolutionOn (I := I) (M := M) D)
    {K a t0 t : Real} {x : M}
    (basis : Module.Basis (Fin 3) Real (TangentSpace I x))
    (horth : OrthonormalBasisAt (I := I) (S.base.metric t) x basis)
    (i : Fin 3) :
    0 ≤ a * twoTensorSecToFamily (I := I) (M := M)
        (hamiltonIveySupportUpperSec (I := I) (M := M) S K a t0) t x
        (basis i) (basis i) ↔
      inner ℝ (matrixToEuclid (hamiltonIveySupportUpperDiagNormal a
          (hamiltonIveySupportPinchDelta a) i))
        (matrixToEuclid (curvatureOperatorMatrixAt (I := I) x basis
          ⟨S.base.rm04 t x, metricRm04At_mem_algebraicCurvatureTensorSubmodule
            (I := I) (S.base.metric t) x⟩)) ≤
        a * hamiltonIveySupportCoefficient K a t0 t := by
  have hrepr := supportUpperDiag_eq_coe_sub_inner
    (I := I) (M := M) S (K := K) (a := a) (t0 := t0) (t := t)
    basis horth i
  constructor <;> intro h <;> nlinarith



theorem supportUpperDiag_nonneg_of_inner_le
    {D : DifferentialGeometry.Geometry.Curvature.RealTimeInterval}
    (S : SolutionOn (I := I) (M := M) D)
    {K a t0 t : Real} {x : M}
    (basis : Module.Basis (Fin 3) Real (TangentSpace I x))
    (horth : OrthonormalBasisAt (I := I) (S.base.metric t) x basis)
    (i : Fin 3)
    (hle : inner ℝ (matrixToEuclid (hamiltonIveySupportUpperDiagNormal a
          (hamiltonIveySupportPinchDelta a) i))
        (matrixToEuclid (curvatureOperatorMatrixAt (I := I) x basis
          ⟨S.base.rm04 t x, metricRm04At_mem_algebraicCurvatureTensorSubmodule
            (I := I) (S.base.metric t) x⟩)) ≤
        a * hamiltonIveySupportCoefficient K a t0 t) :
    0 ≤ a * twoTensorSecToFamily (I := I) (M := M)
        (hamiltonIveySupportUpperSec (I := I) (M := M) S K a t0) t x
        (basis i) (basis i) :=
  (supportUpperDiag_nonneg_iff_inner_le (I := I) (M := M) S basis horth i).2 hle



theorem supportUpperDiag_eq_coe_sub_inner_uhlenbeck
    {D : DifferentialGeometry.Geometry.Curvature.RealTimeInterval}
    (S : SolutionOn (I := I) (M := M) D)
    {K a t0 t : Real} {x : M}
    (basis : Module.Basis (Fin 3) Real (TangentSpace I x))
    (horth : OrthonormalBasisAt (I := I) (S.base.metric t) x basis)
    (i : Fin 3)
    (pulledRm : FourComp M (Fin 3))
    (hpull : ∀ a b c d : Fin 3,
      pulledRm t x a b c d =
        tensor04StdAt (I := I) (M := M) (S.base.rm04 t x)
          (basis a) (basis b) (basis c) (basis d)) :
    a * twoTensorSecToFamily (I := I) (M := M)
        (hamiltonIveySupportUpperSec (I := I) (M := M) S K a t0) t x
        (basis i) (basis i) =
      a * hamiltonIveySupportCoefficient K a t0 t -
        inner ℝ (matrixToEuclid (hamiltonIveySupportUpperDiagNormal a
          (hamiltonIveySupportPinchDelta a) i))
          (uhlenbeckCurvatureOperatorMatrix pulledRm t x) := by
  have hrepr := supportUpperDiag_eq_coe_sub_inner
    (I := I) (M := M) S (K := K) (a := a) (t0 := t0) (t := t)
    basis horth i
  have hmat := uhlenbeckCurvatureOperatorMatrixAsMatrix_eq_curvatureOperatorMatrixAt
    (I := I) (M := M) (x := x) (basis := basis)
    (A := ⟨S.base.rm04 t x, metricRm04At_mem_algebraicCurvatureTensorSubmodule
      (I := I) (S.base.metric t) x⟩)
    (pulledRm := pulledRm) (t := t) hpull
  have hmat2 := uhlenbeckCurvatureOperatorMatrix_eq_matrixToEuclid
    (pulledRm := pulledRm) (t := t) (x := x)
  rw [hrepr]
  rw [hmat2, hmat]



theorem supportUpperDiag_nonneg_of_uhlenbeck_inner_le
    {D : DifferentialGeometry.Geometry.Curvature.RealTimeInterval}
    (S : SolutionOn (I := I) (M := M) D)
    {K a t0 t : Real} {x : M}
    (basis : Module.Basis (Fin 3) Real (TangentSpace I x))
    (horth : OrthonormalBasisAt (I := I) (S.base.metric t) x basis)
    (i : Fin 3)
    (pulledRm : FourComp M (Fin 3))
    (hpull : ∀ a b c d : Fin 3,
      pulledRm t x a b c d =
        tensor04StdAt (I := I) (M := M) (S.base.rm04 t x)
          (basis a) (basis b) (basis c) (basis d))
    (hle : inner ℝ (matrixToEuclid (hamiltonIveySupportUpperDiagNormal a
          (hamiltonIveySupportPinchDelta a) i))
        (uhlenbeckCurvatureOperatorMatrix pulledRm t x) ≤
        a * hamiltonIveySupportCoefficient K a t0 t) :
    0 ≤ a * twoTensorSecToFamily (I := I) (M := M)
        (hamiltonIveySupportUpperSec (I := I) (M := M) S K a t0) t x
        (basis i) (basis i) := by
  have hrepr := supportUpperDiag_eq_coe_sub_inner_uhlenbeck
    (I := I) (M := M) S (K := K) (a := a) (t0 := t0) (t := t)
    basis horth i pulledRm hpull
  nlinarith [hrepr, hle]



theorem supportUpperDiag_initial_uhlenbeck_inner_le
    {D : DifferentialGeometry.Geometry.Curvature.RealTimeInterval}
    (S : SolutionOn (I := I) (M := M) D)
    {K t0 a : Real} {x : M} (hK : 0 < K) (ha : 0 < a)
    (hdim : Module.finrank Real (TangentSpace I x) = 3)
    (hinit : CurvatureOperatorLowerBoundAt (I := I) (S.base.metric t0) x
      ⟨S.base.rm04 t0 x, metricRm04At_mem_algebraicCurvatureTensorSubmodule
        (I := I) (S.base.metric t0) x⟩ K)
    (basis : Module.Basis (Fin 3) Real (TangentSpace I x))
    (horth : OrthonormalBasisAt (I := I) (S.base.metric t0) x basis)
    (i : Fin 3)
    (pulledRm : FourComp M (Fin 3))
    (hpull : ∀ a b c d : Fin 3,
      pulledRm t0 x a b c d =
        tensor04StdAt (I := I) (M := M) (S.base.rm04 t0 x)
          (basis a) (basis b) (basis c) (basis d)) :
    inner ℝ (matrixToEuclid (hamiltonIveySupportUpperDiagNormal a
        (hamiltonIveySupportPinchDelta a) i))
      (uhlenbeckCurvatureOperatorMatrix pulledRm t0 x) ≤
      a * hamiltonIveySupportCoefficient K a t0 t0 := by
  have hmat := uhlenbeckCurvatureOperatorMatrixAsMatrix_eq_curvatureOperatorMatrixAt
    (I := I) (M := M) (x := x) (basis := basis)
    (A := ⟨S.base.rm04 t0 x, metricRm04At_mem_algebraicCurvatureTensorSubmodule
      (I := I) (S.base.metric t0) x⟩)
    (pulledRm := pulledRm) (t := t0) hpull
  have hmat2 := uhlenbeckCurvatureOperatorMatrix_eq_matrixToEuclid
    (pulledRm := pulledRm) (t := t0) (x := x)
  have hle := supportUpperDiag_initial_inner_le
    (I := I) (M := M) S hK ha hdim hinit basis horth i
  rw [hmat2, hmat]
  exact hle



theorem supportUpperDiag_uhlenbeck_nonneg_iff_inner_le
    {D : DifferentialGeometry.Geometry.Curvature.RealTimeInterval}
    (S : SolutionOn (I := I) (M := M) D)
    {K a t0 t : Real} {x : M}
    (basis : Module.Basis (Fin 3) Real (TangentSpace I x))
    (horth : OrthonormalBasisAt (I := I) (S.base.metric t) x basis)
    (i : Fin 3)
    (pulledRm : FourComp M (Fin 3))
    (hpull : ∀ a b c d : Fin 3,
      pulledRm t x a b c d =
        tensor04StdAt (I := I) (M := M) (S.base.rm04 t x)
          (basis a) (basis b) (basis c) (basis d)) :
    0 ≤ a * twoTensorSecToFamily (I := I) (M := M)
        (hamiltonIveySupportUpperSec (I := I) (M := M) S K a t0) t x
        (basis i) (basis i) ↔
      inner ℝ (matrixToEuclid (hamiltonIveySupportUpperDiagNormal a
          (hamiltonIveySupportPinchDelta a) i))
        (uhlenbeckCurvatureOperatorMatrix pulledRm t x) ≤
        a * hamiltonIveySupportCoefficient K a t0 t := by
  have hrepr := supportUpperDiag_eq_coe_sub_inner_uhlenbeck
    (I := I) (M := M) S (K := K) (a := a) (t0 := t0) (t := t)
    basis horth i pulledRm hpull
  constructor <;> intro h <;> nlinarith



theorem supportUpperDiag_initial_uhlenbeck_nonneg
    {D : DifferentialGeometry.Geometry.Curvature.RealTimeInterval}
    (S : SolutionOn (I := I) (M := M) D)
    {K t0 a : Real} {x : M} (hK : 0 < K) (ha : 0 < a)
    (hdim : Module.finrank Real (TangentSpace I x) = 3)
    (hinit : CurvatureOperatorLowerBoundAt (I := I) (S.base.metric t0) x
      ⟨S.base.rm04 t0 x, metricRm04At_mem_algebraicCurvatureTensorSubmodule
        (I := I) (S.base.metric t0) x⟩ K)
    (basis : Module.Basis (Fin 3) Real (TangentSpace I x))
    (horth : OrthonormalBasisAt (I := I) (S.base.metric t0) x basis)
    (i : Fin 3)
    (pulledRm : FourComp M (Fin 3))
    (hpull : ∀ a b c d : Fin 3,
      pulledRm t0 x a b c d =
        tensor04StdAt (I := I) (M := M) (S.base.rm04 t0 x)
          (basis a) (basis b) (basis c) (basis d)) :
    0 ≤ a * twoTensorSecToFamily (I := I) (M := M)
        (hamiltonIveySupportUpperSec (I := I) (M := M) S K a t0) t0 x
        (basis i) (basis i) :=
  supportUpperDiag_nonneg_of_uhlenbeck_inner_le
    (I := I) (M := M) S basis horth i pulledRm hpull
    (supportUpperDiag_initial_uhlenbeck_inner_le
      (I := I) (M := M) S hK ha hdim hinit basis horth i pulledRm hpull)



theorem supportUpperDiag_nonneg_of_uhlenbeck_halfspaces
    {D : DifferentialGeometry.Geometry.Curvature.RealTimeInterval}
    (S : SolutionOn (I := I) (M := M) D)
    {K a t0 t : Real} {x : M}
    (basis : Module.Basis (Fin 3) Real (TangentSpace I x))
    (horth : OrthonormalBasisAt (I := I) (S.base.metric t) x basis)
    (pulledRm : FourComp M (Fin 3))
    (hpull : ∀ a b c d : Fin 3,
      pulledRm t x a b c d =
        tensor04StdAt (I := I) (M := M) (S.base.rm04 t x)
          (basis a) (basis b) (basis c) (basis d))
    (hle : ∀ i : Fin 3,
      inner ℝ (matrixToEuclid (hamiltonIveySupportUpperDiagNormal a
          (hamiltonIveySupportPinchDelta a) i))
        (uhlenbeckCurvatureOperatorMatrix pulledRm t x) ≤
        a * hamiltonIveySupportCoefficient K a t0 t) :
    ∀ i : Fin 3,
      0 ≤ a * twoTensorSecToFamily (I := I) (M := M)
        (hamiltonIveySupportUpperSec (I := I) (M := M) S K a t0) t x
        (basis i) (basis i) :=
  fun i => supportUpperDiag_nonneg_of_uhlenbeck_inner_le
    (I := I) (M := M) S basis horth i pulledRm hpull (hle i)



omit [CompleteSpace E] [IsManifold I 2 M] [SigmaCompactSpace M] [T2Space M] in
theorem supportUpperDiag_parabolic_ineq
    [I.Boundaryless]
    {D : DifferentialGeometry.Geometry.Curvature.RealTimeInterval}
    [CompleteSpace E] [SigmaCompactSpace M] [T2Space M]
    (S : SolutionOn (I := I) (M := M) D)
    (hS : IsSmoothSolutionOn (I := I) (M := M) S)
    {K a t0 T : Real} (hK : 0 < K) (ha : 0 < a) (ht0 : t0 ≤ 0)
    (hdim : ∀ x : M, Module.finrank Real (TangentSpace I x) = 3)
    (hTsub : Set.Icc 0 T ⊆ D.carrier)
    (hTreg : Set.Ioc 0 T ⊆ D.regular)
    {x : M} (basis : Module.Basis (Fin 3) Real (TangentSpace I x))
    (i : Fin 3) :
    ∀ t : Real, t ∈ Set.Ioc 0 T →
      ∃ timeDeriv : Real,
        HasDerivWithinAt
          (fun s : Real =>
            twoTensorSecToFamily (I := I) (M := M)
              (hamiltonIveySupportUpperSec (I := I) (M := M) S K a t0) s x
              (basis i) (basis i))
          timeDeriv (Set.Icc 0 T) t ∧
        tensorHeatWithDrift2QuadMetricAt (I := I) (S.base.metric t)
            (fun _y : M => (0 : TangentSpace I _y))
            (hamiltonIveySupportUpperNab2ModelSec (I := I) S a t x)
            (hamiltonIveySupportUpperNablaModel (I := I) S a t x) (basis i) +
          (hamiltonIveySupportUpperReact (I := I) (M := M) K a t0 t (S.base.metric t)
            (twoTensorSecToFamily (I := I) (M := M)
              (hamiltonIveySupportUpperSec (I := I) (M := M) S K a t0) t))
            x (basis i) (basis i) ≤ timeDeriv := by
  intro t ht
  have hpar := hamiltonIveySupportUpperParabolic
    (I := I) (M := M) S hS hK ha ht0 hdim hTsub hTreg
  rcases hpar.evaluatedInequality with ⟨timeDeriv, htime, hineq⟩
  exact ⟨timeDeriv t x (basis i), htime t ht x (basis i), hineq t ht x (basis i)⟩



end DifferentialGeometry.PDE.RicciFlow
