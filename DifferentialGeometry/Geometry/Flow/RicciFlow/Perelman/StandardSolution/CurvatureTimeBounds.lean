import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.StandardSolution.CovariantTimeNorm
import DifferentialGeometry.Geometry.Flow.RicciFlow.Evolution.Curvature.Derivatives.Evolution.SolutionHeatEquation
import DifferentialGeometry.Geometry.Connection.MetricTrace.NormBound

set_option autoImplicit false
noncomputable section
open Set Bundle Manifold DifferentialGeometry DifferentialGeometry.Tensor0SBundle
open DifferentialGeometry.Geometry.Curvature DifferentialGeometry.Geometry.Operator
open DifferentialGeometry.Geometry.Connection
open DifferentialGeometry.PDE.RicciFlow
open scoped Manifold ContDiff BigOperators
namespace DifferentialGeometry.PDE.RicciFlow

def curvatureTimeBound (d k : ℕ) (C : ℝ) : ℝ :=
  Real.sqrt ((d : ℝ) ^ (4 + k)) * ((d : ℝ) * C +
    rmResidualCost d k * ((k + 1 : ℕ) : ℝ) * C ^ 2 +
      ((4 + k : ℕ) : ℝ) * (d : ℝ) ^ 2 * C ^ 2)

theorem curvatureTimeBound_nonneg (d k : ℕ) (C : ℝ) (hC : 0 ≤ C) :
    0 ≤ curvatureTimeBound d k C := by
  have hr := rmResidualCost_nonneg d k
  unfold curvatureTimeBound
  positivity

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

private theorem tensor_deriv_of_basis {ι : Type*} [Finite ι] {s : ℕ} {x : M}
    (basis : Module.Basis ι ℝ (TangentSpace I x))
    (T : ℝ → Tensor0SSpace s I x) (Tdot : Tensor0SSpace s I x) (J : Set ℝ) (t : ℝ)
    (h : ∀ m : Fin s → ι, HasDerivWithinAt (fun r => component0S basis (T r) m)
      (component0S basis Tdot m) J t) : HasDerivWithinAt T Tdot J t := by
  classical
  let _ := Fintype.ofFinite ι
  let b := tensor0SBasis (I := I) basis s
  have hh := HasDerivWithinAt.sum (u := Finset.univ) (fun m _ => (h m).smul_const (b m))
  have he : (∑ m, fun r => component0S basis (T r) m • b m) = T := by
    funext r
    rw [Finset.sum_apply]
    simpa only [b, ← tensor0SBasis_repr] using (tensor0SBasis (I := I) basis s).sum_repr (T r)
  have he' : (∑ m, component0S basis Tdot m • b m) = Tdot := by
    simpa only [b, ← tensor0SBasis_repr] using (tensor0SBasis (I := I) basis s).sum_repr Tdot
  rw [he, he'] at hh
  exact hh

omit [FiniteDimensional ℝ E] in
private theorem trace_component_bound {ι : Type*} [Fintype ι] [DecidableEq ι]
    {s : ℕ} {x : M} (basis : Module.Basis ι ℝ (TangentSpace I x))
    (T : Tensor0SSpace (s + 2) I x) (C : ℝ)
    (hC : ∀ m : Fin (s + 2) → ι, |component0S basis T m| ≤ C) (m : Fin s → ι) :
    |component0S basis (metricTrace0S2TensorInBasis basis identityInvMetric T) m| ≤
      (Fintype.card ι : ℝ) * C := by
  have he : component0S basis (metricTrace0S2TensorInBasis basis identityInvMetric T) m =
      ∑ i : ι, component0S basis T (Fin.cons i (Fin.cons i m)) := by
    rw [component0S_apply, metricTrace0S2TensorInBasis_apply]
    simp only [metricTrace0S2InBasis, identityInvMetric, diagonalInvMetric, ite_mul, one_mul, zero_mul]
    apply Finset.sum_congr rfl
    intro i _
    rw [Finset.sum_eq_single i]
    · rw [ite_eq_left rfl, component0S_apply]
      congr 1
      funext a
      refine Fin.cases ?_ (fun a1 => ?_) a
      · rfl
      · refine Fin.cases ?_ (fun _ => ?_) a1 <;> rfl
    · intro j _ hji
      simp only [ite_eq_right (Ne.symm hji)]
    · intro hni
      exact absurd (Finset.mem_univ i) hni
  rw [he]
  calc |∑ i : ι, component0S basis T (Fin.cons i (Fin.cons i m))|
      ≤ ∑ i : ι, |component0S basis T (Fin.cons i (Fin.cons i m))| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _i : ι, C := Finset.sum_le_sum fun i _ => hC (Fin.cons i (Fin.cons i m))
    _ = (Fintype.card ι : ℝ) * C := by simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]

variable [CompleteSpace E] [NeZero (Module.finrank ℝ E)] [I.Boundaryless]
  [T2Space M] [BoundarylessManifold I M]

theorem curvature_time_derivative_bound {D : RealTimeInterval}
    (S : SolutionOn (I := I) (M := M) D) (hS : IsSolutionOn S)
    (k : ℕ) (t : RealTimeInterval.RegularTime D) (x : M) (C : ℝ) (hC : 0 ≤ C)
    (hbound : ∀ j ≤ k + 2, Real.sqrt (nablaKRm04NormSqIntrinsic S j (t : ℝ) x) ≤ C) :
    Real.sqrt (normSq0S (S.base.metric (t : ℝ)) x (4 + k)
      (covariantTimeDerivWithin S.base.metric (fun r => nablaKRm04Field S r k x) D.carrier (t : ℝ))) ≤
        curvatureTimeBound (Module.finrank ℝ E) k C := by
  classical
  let d := Module.finrank ℝ E
  let Idx := Fin d
  let g := S.base.metric (t : ℝ)
  let T := fun r => nablaKRm04Field S r k x
  obtain ⟨R, hRcost, hpoint⟩ := rmResidual_cost S hS k t
  obtain ⟨basis, horth, hdt⟩ := hpoint x
  have hinv := metricInverseInBasis_identity_of_orthonormal g basis horth
  let L := metricTrace0S2TensorInBasis basis (identityInvMetric (Idx := Idx))
    (nablaKRm04Field S (t : ℝ) (k + 2) x)
  let U := covariantTimeDerivWithin S.base.metric T D.carrier (t : ℝ)
  have hderiv := tensor_deriv_of_basis basis T (L + R x) D.carrier (t : ℝ) hdt
  have hJ : UniqueDiffWithinAt ℝ D.carrier (t : ℝ) := uniqueDiffWithinAt_of_mem_nhds (D.regular_mem_nhds t.2)
  have hU : U = (L + R x) + ricciTimeCorrection g (T (t : ℝ)) := by
    have he : derivWithin T D.carrier (t : ℝ) = L + R x := hderiv.derivWithin hJ
    exact congrArg (fun V : Tensor0SSpace (4 + k) I x => V + ricciTimeCorrection g (T (t : ℝ))) he
  have hcomp (j : ℕ) (hj : j ≤ k + 2) (m : Fin (4 + j) → Idx) :
      |component0S basis (nablaKRm04Field S (t : ℝ) j x) m| ≤ C :=
    (component_le_sqrt g basis hinv _ m).trans (hbound j hj)
  have hLap (m : Fin (4 + k) → Idx) : |component0S basis L m| ≤ (d : ℝ) * C := by
    simpa only [Fintype.card_fin] using trace_component_bound basis
      (nablaKRm04Field S (t : ℝ) (k + 2) x) C (hcomp (k + 2) le_rfl) m
  have hst (j : ℕ) : stNormSq S (t : ℝ) j x basis = nablaKRm04NormSqIntrinsic S j (t : ℝ) x := by
    simpa only [stNormSq, nablaKRm04NormSqIntrinsic] using
      (compNormSqMulti_orthoBasis_eq_normSq0S g basis horth (nablaKRm04Field S (t : ℝ) j x))
  have hRc := rmResidualCost_nonneg d k
  have hR (m : Fin (4 + k) → Idx) : |component0S basis (R x) m| ≤
      rmResidualCost d k * ((k + 1 : ℕ) : ℝ) * C ^ 2 := by
    have hh := hRcost.bound x basis (by simpa only [SolutionOn.family_metric] using horth) m
    simp only [hst] at hh
    apply hh.trans
    calc rmResidualCost d k * (∑ j ∈ Finset.range (k + 1),
        Real.sqrt (nablaKRm04NormSqIntrinsic S j (t : ℝ) x) *
          Real.sqrt (nablaKRm04NormSqIntrinsic S (k - j) (t : ℝ) x))
        ≤ rmResidualCost d k * ∑ _j ∈ Finset.range (k + 1), C * C :=
          mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun j hj =>
            mul_le_mul (hbound j (by simp only [Finset.mem_range] at hj; omega))
              (hbound (k - j) (by omega)) (Real.sqrt_nonneg _) hC) hRc
      _ = _ := by simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul]; ring
  have hRic (i j : Idx) : |ricciTensor g x (basis i) (basis j)| ≤ (d : ℝ) * C := by
    have hh := metricRicciComp_le g basis horth i j
    rw [metricRicciAt_apply_eq_ricciTensor] at hh
    have h0 : Real.sqrt (normSq0S g x 4 (metricRm04At g x)) ≤ C := hbound 0 (by omega)
    apply hh.trans
    simpa only [Fintype.card_fin] using mul_le_mul_of_nonneg_left h0 (Nat.cast_nonneg d)
  have hCorrection (m : Fin (4 + k) → Idx) :
      |component0S basis (ricciTimeCorrection g (T (t : ℝ))) m| ≤
        ((4 + k : ℕ) : ℝ) * (d : ℝ) ^ 2 * C ^ 2 := by
    have hh := abs_covariantEndomorphismActionArray_le
      (fun i j => ricciTensor g x (basis i) (basis j))
      (fun n => tensor0SComponent (T (t : ℝ)) (fun i => basis i) n)
      ((d : ℝ) * C) (mul_nonneg (Nat.cast_nonneg d) hC) hRic m
    have hcN : compNormSqMulti (fun n => tensor0SComponent (T (t : ℝ)) (fun i => basis i) n) =
        nablaKRm04NormSqIntrinsic S k (t : ℝ) x := by
      simpa only [tensor0SComponent_apply, nablaKRm04NormSqIntrinsic] using
        (compNormSqMulti_orthoBasis_eq_normSq0S g basis horth (T (t : ℝ)))
    rw [hcN] at hh
    rw [show component0S basis (ricciTimeCorrection g (T (t : ℝ))) m =
      tensor0SComponent (ricciTimeCorrection g (T (t : ℝ))) (fun i => basis i) m from rfl,
      ricciTimeCorrection_component g (T (t : ℝ)) basis horth]
    apply hh.trans
    have he := mul_le_mul_of_nonneg_left (hbound k (by omega))
      (show 0 ≤ ((4 + k : ℕ) : ℝ) * (Fintype.card Idx : ℝ) * ((d : ℝ) * C) by positivity)
    calc _ ≤ ((4 + k : ℕ) : ℝ) * (Fintype.card Idx : ℝ) * ((d : ℝ) * C) * C := he
      _ = ((4 + k : ℕ) : ℝ) * (d : ℝ) ^ 2 * C ^ 2 := by
        simp only [Idx, Fintype.card_fin]
        ring
  let B := (d : ℝ) * C + rmResidualCost d k * ((k + 1 : ℕ) : ℝ) * C ^ 2 +
    ((4 + k : ℕ) : ℝ) * (d : ℝ) ^ 2 * C ^ 2
  have hB : 0 ≤ B := by dsimp only [B]; positivity
  have hUb (m : Fin (4 + k) → Idx) : |component0S basis U m| ≤ B := by
    rw [hU]
    change |component0S basis L m + component0S basis (R x) m +
      component0S basis (ricciTimeCorrection g (T (t : ℝ))) m| ≤ B
    exact (abs_add_le _ _).trans (add_le_add ((abs_add_le _ _).trans
      (add_le_add (hLap m) (hR m))) (hCorrection m))
  have hb := normSq0S_le_card g basis horth U B hUb
  have hc : (Fintype.card (Fin (4 + k) → Idx) : ℝ) = (d : ℝ) ^ (4 + k) := by simp [Idx]
  rw [hc] at hb
  have hs := Real.sqrt_le_sqrt hb
  rw [Real.sqrt_mul (by positivity : 0 ≤ (d : ℝ) ^ (4 + k)), Real.sqrt_sq hB] at hs
  exact hs
end DifferentialGeometry.PDE.RicciFlow
