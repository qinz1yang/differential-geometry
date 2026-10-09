import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.StandardSolution.CovariantTimeNorm
import DifferentialGeometry.Geometry.Operator.Laplacian.Rough
import DifferentialGeometry.Tensor.RSTensor.Coordinates.Components
import DifferentialGeometry.Geometry.Metric.TensorInner.Cotangent.Riemannian

set_option autoImplicit false
noncomputable section
open Set Bundle Manifold DifferentialGeometry DifferentialGeometry.Tensor0SBundle
open DifferentialGeometry.Geometry.Curvature DifferentialGeometry.Geometry.Operator
open DifferentialGeometry.Geometry.Metric
open scoped Manifold ContDiff BigOperators
namespace DifferentialGeometry.PDE.RicciFlow

private theorem trace_ricStar {ι : Type*} [Fintype ι] {s : ℕ}
    (R : ι → ι → ℝ) (hR : ∀ i j, R i j = R j i)
    (A : (Fin (s + 2) → ι) → ℝ) (m : Fin s → ι) :
    (∑ i : ι, covariantEndomorphismActionArray R A (Fin.cons i (Fin.cons i m))) =
      covariantEndomorphismActionArray R (fun n => ∑ i : ι, A (Fin.cons i (Fin.cons i n))) m +
        2 * ∑ i : ι, ∑ j : ι, R i j * A (Fin.cons i (Fin.cons j m)) := by
  classical
  have he (i : ι) : covariantEndomorphismActionArray R A (Fin.cons i (Fin.cons i m)) =
      (∑ j : ι, R i j * A (Fin.cons j (Fin.cons i m))) +
        ((∑ j : ι, R i j * A (Fin.cons i (Fin.cons j m))) +
          ∑ q : Fin s, ∑ j : ι, R (m q) j * A (Fin.cons i (Fin.cons i (Function.update m q j)))) := by
    simp only [covariantEndomorphismActionArray, Fin.sum_univ_succ, Fin.cons_zero, Fin.cons_succ,
      Fin.update_cons_zero, ← Fin.cons_update]
  have hswap : (∑ i : ι, ∑ j : ι, R i j * A (Fin.cons j (Fin.cons i m))) =
      ∑ i : ι, ∑ j : ι, R i j * A (Fin.cons i (Fin.cons j m)) := by
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    rw [hR j i]
  have htail : (∑ i : ι, ∑ q : Fin s, ∑ j : ι,
      R (m q) j * A (Fin.cons i (Fin.cons i (Function.update m q j)))) =
        covariantEndomorphismActionArray R (fun n => ∑ i : ι, A (Fin.cons i (Fin.cons i n))) m := by
    rw [Finset.sum_comm]
    unfold covariantEndomorphismActionArray
    apply Finset.sum_congr rfl
    intro q _
    rw [Finset.sum_comm]
    simp only [Finset.mul_sum]
  simp only [he, Finset.sum_add_distrib]
  rw [hswap, htail]
  ring

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

private theorem trace_eq_basis {ι : Type*} [Fintype ι] [DecidableEq ι] {s : ℕ} {x : M}
    (g : SmoothRiemannianMetric I M) (basis : Module.Basis ι ℝ (TangentSpace I x))
    (B : ι → ι → ℝ) (hB : MetricInverseInBasis g x basis B) (T : Tensor0SSpace (s + 2) I x) :
    metricTraceFirstTwo0STensor g T = metricTrace0S2TensorInBasis basis B T := by
  apply tensor0SSpace_ext s x
  intro v
  rw [metricTraceFirstTwo0STensor_apply, metricTrace0S2TensorInBasis_apply]
  exact metricTraceFirstTwo0SAt_eq_sum_basis g basis B hB T v

omit [FiniteDimensional ℝ E] in
private theorem trace_basis_component {ι : Type*} [Fintype ι] {s : ℕ} {x : M}
    (basis : Module.Basis ι ℝ (TangentSpace I x)) (B : ι → ι → ℝ)
    (T : Tensor0SSpace (s + 2) I x) (m : Fin s → ι) :
    component0S basis (metricTrace0S2TensorInBasis basis B T) m =
      ∑ i : ι, ∑ j : ι, B i j * component0S basis T (Fin.cons i (Fin.cons j m)) := by
  rw [component0S_apply, metricTrace0S2TensorInBasis_apply]
  unfold metricTrace0S2InBasis
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  congr 1
  rw [component0S_apply]
  apply congrArg T
  funext q
  refine Fin.cases ?_ (fun q1 => ?_) q
  · rfl
  · refine Fin.cases ?_ (fun _ => ?_) q1 <;> rfl

private theorem trace_component_orthonormal {ι : Type*} [Fintype ι] [DecidableEq ι]
    {s : ℕ} {x : M} (g : SmoothRiemannianMetric I M)
    (basis : Module.Basis ι ℝ (TangentSpace I x))
    (horth : ∀ i j, g.inner x (basis i) (basis j) = if i = j then (1 : ℝ) else 0)
    (T : Tensor0SSpace (s + 2) I x) (m : Fin s → ι) :
    component0S basis (metricTraceFirstTwo0STensor g T) m =
      ∑ i : ι, component0S basis T (Fin.cons i (Fin.cons i m)) := by
  rw [trace_eq_basis g basis identityInvMetric
    (metricInverseInBasis_identity_of_orthonormal g basis horth), trace_basis_component]
  simp only [identityInvMetric, diagonalInvMetric, ite_mul, one_mul, zero_mul]
  apply Finset.sum_congr rfl
  intro i _
  simp

variable [T2Space M] [BoundarylessManifold I M]

theorem ricciTimeCorrection_metricTrace {ι : Type*} [Fintype ι] [DecidableEq ι]
    {s : ℕ} {x : M} (g : SmoothRiemannianMetric I M) (T : Tensor0SSpace (s + 2) I x)
    (basis : Module.Basis ι ℝ (TangentSpace I x))
    (horth : ∀ i j, g.inner x (basis i) (basis j) = if i = j then (1 : ℝ) else 0) :
    metricTraceFirstTwo0STensor g (ricciTimeCorrection g T) =
      ricciTimeCorrection g (metricTraceFirstTwo0STensor g T) +
        (2 : ℝ) • metricTrace0S2TensorInBasis basis
          (fun i j => ricciTensor g x (basis i) (basis j)) T := by
  apply ext0S_basis basis
  intro m
  rw [component0S_add, component0S_smul, trace_basis_component,
    trace_component_orthonormal g basis horth]
  have hc (r : ℕ) (V : Tensor0SSpace r I x) (n : Fin r → ι) :
      component0S basis (ricciTimeCorrection g V) n =
        covariantEndomorphismActionArray (fun i j => ricciTensor g x (basis i) (basis j))
          (fun v => component0S basis V v) n :=
    ricciTimeCorrection_component g V basis horth n
  simp only [hc]
  have he : (fun n => component0S basis (metricTraceFirstTwo0STensor g T) n) =
      (fun n => ∑ i : ι, component0S basis T (Fin.cons i (Fin.cons i n))) :=
    funext (trace_component_orthonormal g basis horth T)
  rw [he]
  exact trace_ricStar (fun i j => ricciTensor g x (basis i) (basis j))
    (fun i j => ricciTensor_symm g x (basis i) (basis j)) (component0S basis T) m

omit [T2Space M] [BoundarylessManifold I M] in
private theorem basis_inverse_orthonormal {ι : Type*} [Finite ι] [DecidableEq ι]
    {x : M} (g : SmoothRiemannianMetric I M) (basis : Module.Basis ι ℝ (TangentSpace I x))
    (horth : ∀ i j, g.inner x (basis i) (basis j) = if i = j then (1 : ℝ) else 0) (i j : ι) :
    basisInvMetric g x basis i j = if i = j then (1 : ℝ) else 0 := by
  let _ := Fintype.ofFinite ι
  have hh := (basisInvMetric_isInverse g x basis i j).1
  simpa only [horth, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, ite_true] using hh

theorem hasDerivWithinAt_metricTrace {ι : Type*} [Fintype ι] [DecidableEq ι]
    {s : ℕ} {x : M} (g : ℝ → SmoothRiemannianMetric I M)
    (T : ℝ → Tensor0SSpace (s + 2) I x) (Tdot : Tensor0SSpace (s + 2) I x)
    (J : Set ℝ) (t : ℝ) (basis : Module.Basis ι ℝ (TangentSpace I x))
    (horth : ∀ i j, (g t).inner x (basis i) (basis j) = if i = j then (1 : ℝ) else 0)
    (hRF : ∀ v w : TangentSpace I x,
      HasDerivWithinAt (fun r => (g r).inner x v w) (-2 * ricciTensor (g t) x v w) J t)
    (hT : ∀ v : Fin (s + 2) → TangentSpace I x,
      HasDerivWithinAt (fun r => T r v) (Tdot v) J t) :
    HasDerivWithinAt (fun r => metricTraceFirstTwo0STensor (g r) (T r))
      (metricTraceFirstTwo0STensor (g t) Tdot + (2 : ℝ) • metricTrace0S2TensorInBasis basis
        (fun i j => ricciTensor (g t) x (basis i) (basis j)) (T t)) J t := by
  classical
  have hB (i j : ι) := basis_inverse_orthonormal (g t) basis horth i j
  have hInv (i j : ι) : HasDerivWithinAt (fun r => basisInvMetric (g r) x basis i j)
      (2 * ricciTensor (g t) x (basis i) (basis j)) J t := by
    have hh := basisInvMetric_hasDerivWithinAt_ricciFlow g x basis J t hRF i j
    simpa only [hB, ite_mul, one_mul, zero_mul, mul_ite, mul_one, mul_zero,
      Finset.sum_ite_eq, Finset.mem_univ, ite_true] using hh
  apply hasDerivWithinAt_tensor0S_of_eval
  intro v
  have hh := HasDerivWithinAt.fun_sum (u := Finset.univ) (fun (i : ι) _ =>
    HasDerivWithinAt.fun_sum (u := Finset.univ) (fun (j : ι) _ =>
      (hInv i j).mul (hT (metricTraceInput (basis i) (basis j) v))))
  have he : (fun r => ∑ i : ι, ∑ j : ι,
      basisInvMetric (g r) x basis i j * T r (metricTraceInput (basis i) (basis j) v)) =
        (fun r => metricTraceFirstTwo0STensor (g r) (T r) v) := by
    funext r
    rw [metricTraceFirstTwo0STensor_apply,
      metricTraceFirstTwo0SAt_eq_sum_basis (g r) basis _ (basisInvMetric_isInverse (g r) x basis)]
    rfl
  change HasDerivWithinAt (fun r => ∑ i : ι, ∑ j : ι,
    basisInvMetric (g r) x basis i j * T r (metricTraceInput (basis i) (basis j) v)) _ J t at hh
  rw [he] at hh
  apply hh.congr_deriv
  change (∑ i : ι, ∑ j : ι,
    ((2 * ricciTensor (g t) x (basis i) (basis j)) * T t (metricTraceInput (basis i) (basis j) v) +
      basisInvMetric (g t) x basis i j * Tdot (metricTraceInput (basis i) (basis j) v))) =
        metricTraceFirstTwo0STensor (g t) Tdot v +
          2 * metricTrace0S2TensorInBasis basis (fun i j => ricciTensor (g t) x (basis i) (basis j)) (T t) v
  rw [metricTraceFirstTwo0STensor_apply,
    metricTraceFirstTwo0SAt_eq_sum_basis (g t) basis _ (basisInvMetric_isInverse (g t) x basis),
    metricTrace0S2TensorInBasis_apply]
  simp only [metricTrace0S2InBasis, Finset.sum_add_distrib, mul_assoc, Finset.mul_sum]
  ring

theorem covariantTimeDerivWithin_metricTrace {ι : Type*} [Finite ι] [DecidableEq ι]
    {s : ℕ} {x : M} (g : ℝ → SmoothRiemannianMetric I M)
    (T : ℝ → Tensor0SSpace (s + 2) I x) (Tdot : Tensor0SSpace (s + 2) I x)
    (J : Set ℝ) (t : ℝ) (hJ : UniqueDiffWithinAt ℝ J t)
    (basis : Module.Basis ι ℝ (TangentSpace I x))
    (horth : ∀ i j, (g t).inner x (basis i) (basis j) = if i = j then (1 : ℝ) else 0)
    (hRF : ∀ v w : TangentSpace I x,
      HasDerivWithinAt (fun r => (g r).inner x v w) (-2 * ricciTensor (g t) x v w) J t)
    (hT : ∀ v : Fin (s + 2) → TangentSpace I x,
      HasDerivWithinAt (fun r => T r v) (Tdot v) J t) :
    covariantTimeDerivWithin g (fun r => metricTraceFirstTwo0STensor (g r) (T r)) J t =
      metricTraceFirstTwo0STensor (g t) (covariantTimeDerivWithin g T J t) := by
  let _ := Fintype.ofFinite ι
  have hd : derivWithin T J t = Tdot := (hasDerivWithinAt_tensor0S_of_eval T Tdot J t hT).derivWithin hJ
  let R := metricTrace0S2TensorInBasis basis (fun i j => ricciTensor (g t) x (basis i) (basis j)) (T t)
  have htr : derivWithin (fun r => metricTraceFirstTwo0STensor (g r) (T r)) J t =
      metricTraceFirstTwo0STensor (g t) Tdot + (2 : ℝ) • R :=
    (hasDerivWithinAt_metricTrace g T Tdot J t basis horth hRF hT).derivWithin hJ
  have ha (A B : Tensor0SSpace (s + 2) I x) :
      metricTraceFirstTwo0STensor (g t) (A + B) =
        metricTraceFirstTwo0STensor (g t) A + metricTraceFirstTwo0STensor (g t) B := by
    apply tensor0SSpace_ext s x
    intro v
    rw [Tensor0SSpace.add_apply, metricTraceFirstTwo0STensor_apply,
      metricTraceFirstTwo0STensor_apply, metricTraceFirstTwo0STensor_apply]
    exact metricTraceFirstTwo0SAt_add (g t) A B v
  change derivWithin (fun r => metricTraceFirstTwo0STensor (g r) (T r)) J t +
    ricciTimeCorrection (g t) (metricTraceFirstTwo0STensor (g t) (T t)) = _
  calc _ = (metricTraceFirstTwo0STensor (g t) Tdot + (2 : ℝ) • R) +
      ricciTimeCorrection (g t) (metricTraceFirstTwo0STensor (g t) (T t)) :=
        congrArg (fun V : Tensor0SSpace s I x => V +
          ricciTimeCorrection (g t) (metricTraceFirstTwo0STensor (g t) (T t))) htr
    _ = metricTraceFirstTwo0STensor (g t) Tdot +
        (ricciTimeCorrection (g t) (metricTraceFirstTwo0STensor (g t) (T t)) + (2 : ℝ) • R) := by module
    _ = metricTraceFirstTwo0STensor (g t) Tdot +
        metricTraceFirstTwo0STensor (g t) (ricciTimeCorrection (g t) (T t)) := by
          rw [ricciTimeCorrection_metricTrace (g t) (T t) basis horth]
    _ = metricTraceFirstTwo0STensor (g t) (Tdot + ricciTimeCorrection (g t) (T t)) := (ha _ _).symm
    _ = _ := congrArg (fun V : Tensor0SSpace (s + 2) I x =>
      metricTraceFirstTwo0STensor (g t) (V + ricciTimeCorrection (g t) (T t))) hd.symm
end DifferentialGeometry.PDE.RicciFlow
