import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.StandardSolution.MetricCompatibleTimeDerivative
import DifferentialGeometry.Geometry.Metric.InverseTimeDerivative
import DifferentialGeometry.Geometry.Metric.QuadraticBounds.FiniteArrayNorm
import DifferentialGeometry.Geometry.Metric.TensorInner.Cotangent.Riemannian

set_option autoImplicit false
noncomputable section
open Set Bundle Manifold DifferentialGeometry DifferentialGeometry.Tensor0SBundle
open DifferentialGeometry.Geometry.Curvature
open scoped Manifold ContDiff BigOperators
namespace DifferentialGeometry.PDE.RicciFlow
variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [T2Space M] [BoundarylessManifold I M]

theorem ricciTimeCorrection_component {ι : Type*} [Fintype ι] [DecidableEq ι]
    {s : ℕ} {x : M} (g : SmoothRiemannianMetric I M) (T : Tensor0SSpace s I x)
    (basis : Module.Basis ι ℝ (TangentSpace I x))
    (horth : ∀ i j, g.inner x (basis i) (basis j) = if i = j then (1 : ℝ) else 0)
    (m : Fin s → ι) :
    tensor0SComponent (ricciTimeCorrection g T) (fun i => basis i) m =
      covariantEndomorphismActionArray (fun i j => ricciTensor g x (basis i) (basis j))
        (fun n => tensor0SComponent T (fun i => basis i) n) m := by
  have hinv := metricInverseInBasis_identity_of_orthonormal g basis horth
  have hrepr (k i : ι) : basis.repr (ricciSharp g x (basis k)) i =
      ricciTensor g x (basis k) (basis i) := by
    rw [basis_repr_eq_sum_inv_inner g x basis identityInvMetric hinv]
    simp only [inner_ricciSharp, identityInvMetric, diagonalInvMetric]
    simp
  have hexp (k : ι) : ricciSharp g x (basis k) =
      ∑ j : ι, ricciTensor g x (basis k) (basis j) • basis j := by
    conv_lhs => rw [← basis.sum_repr (ricciSharp g x (basis k))]
    simp only [hrepr]
  rw [tensor0SComponent_apply, ricciTimeCorrection_apply]
  unfold covariantEndomorphismActionArray
  apply Finset.sum_congr rfl
  intro q _
  rw [hexp (m q)]
  have hs := T.toModel.toMultilinearMap.map_update_sum Finset.univ q
    (fun j => ricciTensor g x (basis (m q)) (basis j) • basis j) (fun a => basis (m a))
  change T (Function.update (fun a => basis (m a)) q
    (∑ j : ι, ricciTensor g x (basis (m q)) (basis j) • basis j)) =
      ∑ j : ι, T (Function.update (fun a => basis (m a)) q
        (ricciTensor g x (basis (m q)) (basis j) • basis j)) at hs
  rw [hs]
  apply Finset.sum_congr rfl
  intro j _
  rw [T.map_update_smul, smul_eq_mul]
  congr 1
  apply congrArg T
  funext a
  by_cases ha : a = q
  · subst a
    simp only [Function.update_self]
  · simp only [Function.update_of_ne ha]

theorem ricciReaction_eq_two_inner_timeCorrection {ι : Type*} [Fintype ι] [DecidableEq ι]
    {s : ℕ} {x : M} (g : SmoothRiemannianMetric I M) (T : Tensor0SSpace s I x)
    (basis : Module.Basis ι ℝ (TangentSpace I x))
    (horth : ∀ i j, g.inner x (basis i) (basis j) = if i = j then (1 : ℝ) else 0) :
    metricVariationContract identityInvMetric (fun i j => ricciTensor g x (basis i) (basis j))
      (fun m => tensor0SComponent T (fun i => basis i) m)
      (fun m => tensor0SComponent T (fun i => basis i) m) =
        2 * inner0S g x s (ricciTimeCorrection g T) T := by
  rw [metricVariationContract_identityInvMetric]
  rw [inner0S_eq_coord g x s basis identityInvMetric
    (metricInverseInBasis_identity_of_orthonormal g basis horth)]
  rw [coordInner0S_identity_eq_sum]
  congr 1
  apply Finset.sum_congr rfl
  intro m _
  rw [ricciTimeCorrection_component g T basis horth m]
  exact mul_comm _ _

theorem hasDerivWithinAt_normSq0S_covariantTime {ι : Type*} [Finite ι] [DecidableEq ι]
    {s : ℕ} {x : M} (g : ℝ → SmoothRiemannianMetric I M)
    (T : ℝ → Tensor0SSpace s I x) (Tdot : Tensor0SSpace s I x)
    (J : Set ℝ) (t : ℝ) (hJ : UniqueDiffWithinAt ℝ J t)
    (basis : Module.Basis ι ℝ (TangentSpace I x))
    (horth : ∀ i j, (g t).inner x (basis i) (basis j) = if i = j then (1 : ℝ) else 0)
    (hflow : ∀ v w : TangentSpace I x,
      HasDerivWithinAt (fun r => (g r).inner x v w) (-2 * ricciTensor (g t) x v w) J t)
    (hT : ∀ v : Fin s → TangentSpace I x,
      HasDerivWithinAt (fun r => T r v) (Tdot v) J t) :
    HasDerivWithinAt (fun r => normSq0S (g r) x s (T r))
      (2 * inner0S (g t) x s (covariantTimeDerivWithin g T J t) (T t)) J t := by
  let _ := Fintype.ofFinite ι
  let B := fun r => basisInvMetric (g r) x basis
  let ric := fun i j => ricciTensor (g t) x (basis i) (basis j)
  have hinv (r : ℝ) : MetricInverseInBasis (g r) x basis (B r) := basisInvMetric_isInverse (g r) x basis
  have hB : B t = identityInvMetric := MetricInverseInBasis.unique (g t) x basis _ _ (hinv t)
    (metricInverseInBasis_identity_of_orthonormal (g t) basis horth)
  have hd := hasDerivWithinAt_normSq0S_of_metric_variation (fun r => g r) B
    (fun i j => 2 * ∑ a : ι, ∑ b : ι, B t i a * B t j b * ric a b) ric T
    (fun m => tensor0SComponent Tdot (fun i => basis i) m) Tdot basis hinv
    (fun i j => DifferentialGeometry.Geometry.Metric.basisInvMetric_hasDerivWithinAt_ricciFlow g x basis J t hflow i j)
    (fun m => hT (fun a => basis (m a))) (fun _ => rfl) (fun _ _ => rfl)
  have he : covariantTimeDerivWithin g T J t = Tdot + ricciTimeCorrection (g t) (T t) := by
    have hh : derivWithin T J t = Tdot := (hasDerivWithinAt_tensor0S_of_eval T Tdot J t hT).derivWithin hJ
    exact congrArg (fun U : Tensor0SSpace s I x => U + ricciTimeCorrection (g t) (T t)) hh
  apply hd.congr_deriv
  rw [hB]
  change metricVariationContract identityInvMetric
    (fun i j => ricciTensor (g t) x (basis i) (basis j))
    (fun m => tensor0SComponent (T t) (fun i => basis i) m)
    (fun m => tensor0SComponent (T t) (fun i => basis i) m) + 2 * inner0S (g t) x s Tdot (T t) = _
  rw [ricciReaction_eq_two_inner_timeCorrection (g t) (T t) basis horth, he, inner0S_add_left]
  ring
end DifferentialGeometry.PDE.RicciFlow
