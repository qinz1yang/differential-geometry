import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.StandardSolution.RicciActionExpression
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.StandardSolution.CovariantTimeAlgebra
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.StandardSolution.CovariantTimeProduct
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.StandardSolution.CovariantTimeTrace
import DifferentialGeometry.Geometry.Flow.RicciFlow.Evolution.Curvature.Derivatives.Commutator.SecondTermBound

set_option autoImplicit false
noncomputable section
open Set Filter Bundle Manifold DifferentialGeometry DifferentialGeometry.Tensor0SBundle
open DifferentialGeometry.Geometry.Curvature DifferentialGeometry.Geometry.Operator
open DifferentialGeometry.PDE.RicciFlow Bundle.continuousMultilinearMap
open scoped Manifold ContDiff Topology
namespace DifferentialGeometry.PDE.RicciFlow

def CurvatureExpression.timeDerivative : {s : ℕ} → CurvatureExpression s → CurvatureExpression s
  | _, .curvature k => timeLeaf k
  | _, .zero s => .zero s
  | _, .add A B => .add A.timeDerivative B.timeDerivative
  | _, .smul c A => .smul c A.timeDerivative
  | _, .product A B => .add (.product A.timeDerivative B) (.product A B.timeDerivative)
  | _, .perm e A => .perm e A.timeDerivative
  | _, .trace A => .trace A.timeDerivative

def CurvatureExpression.timeIter {s : ℕ} (A : CurvatureExpression s) : ℕ → CurvatureExpression s
  | 0 => A
  | b + 1 => (A.timeIter b).timeDerivative

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [T2Space M]
  [CompleteSpace E] [BoundarylessManifold I M] [NeZero (Module.finrank ℝ E)] [I.Boundaryless]

theorem CurvatureExpression.eval_differentiableWithinAt {D : RealTimeInterval}
    (S : SolutionOn (I := I) (M := M) D) (hS : IsSolutionOn S)
    (t : RealTimeInterval.RegularTime D) {s : ℕ} (A : CurvatureExpression s) (x : M) :
    DifferentiableWithinAt ℝ (fun r => A.eval S r x) D.carrier (t : ℝ) := by
  have jet {q : ℕ} (F : ℝ → Tensor0SSpace q I x)
      (hF : DifferentiableWithinAt ℝ F D.carrier (t : ℝ)) (v : Fin q → TangentSpace I x) :
      HasDerivWithinAt (fun r => F r v) (derivWithin F D.carrier (t : ℝ) v) D.carrier (t : ℝ) :=
    (tensor0SEvalCLM (I := I) v).hasFDerivAt.comp_hasDerivWithinAt (f := F) (t : ℝ)
      hF.hasDerivWithinAt
  have hRF (v w : TangentSpace I x) :
      HasDerivWithinAt (fun r => (S.base.metric r).inner x v w)
        (-2 * ricciTensor (S.base.metric (t : ℝ)) x v w) D.carrier (t : ℝ) := by
    have h := metric_derivWithin_eq_neg_two_ricci S hS t x v w
    change HasDerivWithinAt (fun r => (S.base.metric r).inner x v w)
      (-2 * metricRicciAt (S.base.metric (t : ℝ)) x (vec2 v w)) D.carrier (t : ℝ) at h
    rw [metricRicciAt_apply_eq_ricciTensor] at h
    exact h
  obtain ⟨n, frame, basis, _, horth⟩ := exists_orthoBasisFrameAt S (t : ℝ) x
  induction A with
  | curvature k => exact (hasDerivWithinAt_curvature_canonical_residual S hS k t x).differentiableWithinAt
  | zero s => exact (hasDerivWithinAt_const (t : ℝ) D.carrier (0 : Tensor0SSpace s I x)).differentiableWithinAt
  | add A B ihA ihB => exact ihA.add ihB
  | smul c A ih => exact ih.const_smul c
  | product A B ihA ihB =>
      exact (hasDerivWithinAt_tensor0S_product (fun r => A.eval S r x) (fun r => B.eval S r x)
        (derivWithin (fun r => A.eval S r x) D.carrier (t : ℝ))
        (derivWithin (fun r => B.eval S r x) D.carrier (t : ℝ)) D.carrier (t : ℝ)
        (jet _ ihA) (jet _ ihB)).differentiableWithinAt
  | perm e A ih =>
      exact (hasDerivWithinAt_tensor0S_domDomCongr (fun r => A.eval S r x)
        (derivWithin (fun r => A.eval S r x) D.carrier (t : ℝ)) e D.carrier (t : ℝ)
        (jet _ ih)).differentiableWithinAt
  | trace A ih =>
      exact (hasDerivWithinAt_metricTrace S.base.metric (fun r => A.eval S r x)
        (derivWithin (fun r => A.eval S r x) D.carrier (t : ℝ)) D.carrier (t : ℝ)
        basis horth hRF (jet _ ih)).differentiableWithinAt

theorem CurvatureExpression.eval_timeDerivative {D : RealTimeInterval}
    (S : SolutionOn (I := I) (M := M) D) (hS : IsSolutionOn S)
    (t : RealTimeInterval.RegularTime D) {s : ℕ} (A : CurvatureExpression s) (x : M) :
    covariantTimeDerivWithin S.base.metric (fun r => A.eval S r x) D.carrier (t : ℝ) =
      A.timeDerivative.eval S (t : ℝ) x := by
  have hJ : UniqueDiffWithinAt ℝ D.carrier (t : ℝ) :=
    uniqueDiffWithinAt_of_mem_nhds (D.regular_mem_nhds t.2)
  have jet {q : ℕ} (B : CurvatureExpression q) (v : Fin q → TangentSpace I x) :
      HasDerivWithinAt (fun r => B.eval S r x v)
        (derivWithin (fun r => B.eval S r x) D.carrier (t : ℝ) v) D.carrier (t : ℝ) :=
    (tensor0SEvalCLM (I := I) v).hasFDerivAt.comp_hasDerivWithinAt
      (f := fun r => B.eval S r x) (t : ℝ) (B.eval_differentiableWithinAt S hS t x).hasDerivWithinAt
  have hRF (v w : TangentSpace I x) :
      HasDerivWithinAt (fun r => (S.base.metric r).inner x v w)
        (-2 * ricciTensor (S.base.metric (t : ℝ)) x v w) D.carrier (t : ℝ) := by
    have h := metric_derivWithin_eq_neg_two_ricci S hS t x v w
    change HasDerivWithinAt (fun r => (S.base.metric r).inner x v w)
      (-2 * metricRicciAt (S.base.metric (t : ℝ)) x (vec2 v w)) D.carrier (t : ℝ) at h
    rw [metricRicciAt_apply_eq_ricciTensor] at h
    exact h
  obtain ⟨n, frame, basis, _, horth⟩ := exists_orthoBasisFrameAt S (t : ℝ) x
  induction A with
  | curvature k => exact covariantTimeDerivWithin_curvature_timeLeaf S hS k t x
  | zero s => exact covariantTimeDerivWithin_zero S.base.metric D.carrier (t : ℝ)
  | @add s A B ihA ihB =>
      exact (covariantTimeDerivWithin_add S.base.metric (fun r => A.eval S r x)
        (fun r => B.eval S r x) D.carrier (t : ℝ) hJ
        (A.eval_differentiableWithinAt S hS t x) (B.eval_differentiableWithinAt S hS t x)).trans
          (congrArg₂ (fun U V : Tensor0SSpace s I x => U + V) ihA ihB)
  | @smul s c A ih =>
      exact (covariantTimeDerivWithin_const_smul S.base.metric (fun r => A.eval S r x) c
        D.carrier (t : ℝ) hJ (A.eval_differentiableWithinAt S hS t x)).trans
          (congrArg (fun U : Tensor0SSpace s I x => c • U) ih)
  | @product s q A B ihA ihB =>
      exact (covariantTimeDerivWithin_product S.base.metric
        (fun r => A.eval S r x) (fun r => B.eval S r x)
        (derivWithin (fun r => A.eval S r x) D.carrier (t : ℝ))
        (derivWithin (fun r => B.eval S r x) D.carrier (t : ℝ)) D.carrier (t : ℝ) hJ
        (jet A) (jet B)).trans
          (congrArg₂ (fun (U : Tensor0SSpace s I x) (V : Tensor0SSpace q I x) =>
            (productFun (F := E) (E := TangentSpace I) U (B.eval S (t : ℝ) x) : Tensor0SSpace (s + q) I x) +
              productFun (F := E) (E := TangentSpace I) (A.eval S (t : ℝ) x) V) ihA ihB)
  | @perm s s' e A ih =>
      exact (covariantTimeDerivWithin_domDomCongr S.base.metric (fun r => A.eval S r x)
        (derivWithin (fun r => A.eval S r x) D.carrier (t : ℝ)) e D.carrier (t : ℝ) hJ (jet A)).trans
          (congrArg (fun U : Tensor0SSpace s I x => U.domDomCongr e) ih)
  | @trace s A ih =>
      exact (covariantTimeDerivWithin_metricTrace S.base.metric (fun r => A.eval S r x)
        (derivWithin (fun r => A.eval S r x) D.carrier (t : ℝ)) D.carrier (t : ℝ) hJ
        basis horth hRF (jet A)).trans
          (congrArg (fun U : Tensor0SSpace (s + 2) I x => metricTraceFirstTwo0STensor (S.base.metric (t : ℝ)) U) ih)

theorem CurvatureExpression.eval_timeIter {D : RealTimeInterval}
    (S : SolutionOn (I := I) (M := M) D) (hS : IsSolutionOn S)
    {s : ℕ} (A : CurvatureExpression s) (b : ℕ) (t : RealTimeInterval.RegularTime D) (x : M) :
    iteratedCovariantTimeDerivWithin S.base.metric (fun r => A.eval S r x) D.carrier b (t : ℝ) =
      (A.timeIter b).eval S (t : ℝ) x := by
  induction b generalizing t with
  | zero => rfl
  | succ b ih =>
      let U := iteratedCovariantTimeDerivWithin S.base.metric (fun r => A.eval S r x) D.carrier b
      let V := fun r => (A.timeIter b).eval S r x
      have he : U =ᶠ[𝓝 (t : ℝ)] V := by
        filter_upwards [D.regular_isOpen.mem_nhds t.2] with r hr
        exact ih ⟨r, hr⟩
      have hd : derivWithin U D.carrier (t : ℝ) = derivWithin V D.carrier (t : ℝ) :=
        he.derivWithin_eq_of_nhds
      have hc : covariantTimeDerivWithin S.base.metric U D.carrier (t : ℝ) =
          covariantTimeDerivWithin S.base.metric V D.carrier (t : ℝ) :=
        congrArg₂ (fun W Z : Tensor0SSpace s I x => W + ricciTimeCorrection (S.base.metric (t : ℝ)) Z)
          hd (ih t)
      exact hc.trans ((A.timeIter b).eval_timeDerivative S hS t x)
end DifferentialGeometry.PDE.RicciFlow
