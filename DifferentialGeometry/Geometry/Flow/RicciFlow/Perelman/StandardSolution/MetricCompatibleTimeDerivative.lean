import DifferentialGeometry.Geometry.Curvature.CurvatureOperator.Identities.Ricci
import DifferentialGeometry.Geometry.Curvature.Metric.LeviCivita
import DifferentialGeometry.Geometry.Connection.MetricCompatibility.Tensor.Metric
import DifferentialGeometry.Tensor.RSTensor.Functoriality.Pullback
import DifferentialGeometry.Tensor.RSTensor.Coordinates.Expansion

set_option autoImplicit false
noncomputable section
open Set Bundle Manifold DifferentialGeometry DifferentialGeometry.Tensor0SBundle
open DifferentialGeometry.Geometry.Curvature
open scoped Manifold ContDiff BigOperators
namespace DifferentialGeometry.PDE.RicciFlow
variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

theorem hasDerivWithinAt_tensor0S_of_eval {s : ℕ} {x : M}
    (T : ℝ → Tensor0SSpace s I x) (Tdot : Tensor0SSpace s I x) (J : Set ℝ) (t : ℝ)
    (h : ∀ v : Fin s → TangentSpace I x,
      HasDerivWithinAt (fun r => T r v) (Tdot v) J t) :
    HasDerivWithinAt T Tdot J t := by
  classical
  let basis := Module.finBasis ℝ (TangentSpace I x)
  let b := tensor0SBasis (I := I) basis s
  have hc (m : Fin s → Fin (Module.finrank ℝ (TangentSpace I x))) :
      HasDerivWithinAt (fun r => b.repr (T r) m) (b.repr Tdot m) J t := by
    simpa only [b, tensor0SBasis_repr, component0S_apply] using h (fun a => basis (m a))
  have hh := HasDerivWithinAt.sum (u := Finset.univ) (fun m _ => (hc m).smul_const (b m))
  have he : (∑ m, fun r => b.repr (T r) m • b m) = T := by
    funext r
    rw [Finset.sum_apply]
    exact b.sum_repr (T r)
  rw [he, b.sum_repr] at hh
  exact hh

private def insertEndomorphism {s : ℕ} {x : M}
    (T : Tensor0SSpace s I x) (L : TangentSpace I x →L[ℝ] TangentSpace I x) (q : Fin s) :
    Tensor0SSpace s I x :=
  Tensor0SSpace.ofModel (I := I) (x := x)
    ((Tensor0SSpace.toModel T).compContinuousLinearMap
      (Function.update (fun _ : Fin s => ContinuousLinearMap.id ℝ (TangentSpace I x)) q L))

omit [FiniteDimensional ℝ E] in
private theorem insertEndomorphism_apply {s : ℕ} {x : M}
    (T : Tensor0SSpace s I x) (L : TangentSpace I x →L[ℝ] TangentSpace I x)
    (q : Fin s) (v : Fin s → TangentSpace I x) :
    insertEndomorphism T L q v = T (Function.update v q (L (v q))) := by
  change T (fun i => Function.update (fun _ : Fin s => ContinuousLinearMap.id ℝ (TangentSpace I x)) q L i (v i)) = _
  congr 1
  funext i
  by_cases hi : i = q
  · subst i
    simp only [Function.update_self]
  · simp only [Function.update_of_ne hi]
    rfl

variable [T2Space M] [BoundarylessManifold I M]

def ricciTimeCorrection {s : ℕ} {x : M} (g : SmoothRiemannianMetric I M)
    (T : Tensor0SSpace s I x) : Tensor0SSpace s I x :=
  ∑ q : Fin s, insertEndomorphism T (ricciSharp g x) q

theorem ricciTimeCorrection_apply {s : ℕ} {x : M} (g : SmoothRiemannianMetric I M)
    (T : Tensor0SSpace s I x) (v : Fin s → TangentSpace I x) :
    ricciTimeCorrection g T v = ∑ q : Fin s, T (Function.update v q (ricciSharp g x (v q))) := by
  rw [ricciTimeCorrection, tensor0S_sum_apply]
  exact Finset.sum_congr rfl fun q _ => insertEndomorphism_apply T (ricciSharp g x) q v

theorem ricciTimeCorrection_smul {s : ℕ} {x : M} (g : SmoothRiemannianMetric I M)
    (c : ℝ) (T : Tensor0SSpace s I x) :
    ricciTimeCorrection g (c • T) = c • ricciTimeCorrection g T := by
  apply tensor0SSpace_ext s x
  intro v
  simp only [ricciTimeCorrection_apply, Tensor0SSpace.smul_apply, smul_eq_mul, Finset.mul_sum]

def covariantTimeDerivWithin {s : ℕ} {x : M}
    (g : ℝ → SmoothRiemannianMetric I M) (T : ℝ → Tensor0SSpace s I x)
    (J : Set ℝ) (t : ℝ) : Tensor0SSpace s I x :=
  derivWithin T J t + ricciTimeCorrection (g t) (T t)

theorem covariantTimeDerivWithin_apply {s : ℕ} {x : M}
    (g : ℝ → SmoothRiemannianMetric I M) (T : ℝ → Tensor0SSpace s I x)
    (Tdot : Tensor0SSpace s I x) (J : Set ℝ) (t : ℝ) (hJ : UniqueDiffWithinAt ℝ J t)
    (h : ∀ v : Fin s → TangentSpace I x, HasDerivWithinAt (fun r => T r v) (Tdot v) J t)
    (v : Fin s → TangentSpace I x) :
    covariantTimeDerivWithin g T J t v = Tdot v +
      ∑ q : Fin s, T t (Function.update v q (ricciSharp (g t) x (v q))) := by
  have he : derivWithin T J t = Tdot :=
    (hasDerivWithinAt_tensor0S_of_eval T Tdot J t h).derivWithin hJ
  change (derivWithin T J t + ricciTimeCorrection (g t) (T t)) v = _
  calc (derivWithin T J t + ricciTimeCorrection (g t) (T t)) v
      = (Tdot + ricciTimeCorrection (g t) (T t)) v := congrArg (fun U : Tensor0SSpace s I x => (U + ricciTimeCorrection (g t) (T t)) v) he
    _ = _ := congrArg (fun z => Tdot v + z) (ricciTimeCorrection_apply (g t) (T t) v)

theorem covariantTimeDerivWithin_smul {s : ℕ} {x : M}
    (g : ℝ → SmoothRiemannianMetric I M) (T : ℝ → Tensor0SSpace s I x)
    (Tdot : Tensor0SSpace s I x) (f : ℝ → ℝ) (f' : ℝ)
    (J : Set ℝ) (t : ℝ) (hJ : UniqueDiffWithinAt ℝ J t)
    (hT : HasDerivWithinAt T Tdot J t) (hf : HasDerivWithinAt f f' J t) :
    covariantTimeDerivWithin g (fun r => f r • T r) J t =
      f' • T t + f t • covariantTimeDerivWithin g T J t := by
  have hd : derivWithin (fun r => f r • T r) J t = f' • T t + f t • Tdot :=
    ((hf.smul hT).derivWithin hJ).trans (add_comm _ _)
  have he : derivWithin T J t = Tdot := hT.derivWithin hJ
  change derivWithin (fun r => f r • T r) J t + ricciTimeCorrection (g t) (f t • T t) = _
  calc derivWithin (fun r => f r • T r) J t + ricciTimeCorrection (g t) (f t • T t)
      = (f' • T t + f t • Tdot) + ricciTimeCorrection (g t) (f t • T t) :=
        congrArg (fun U : Tensor0SSpace s I x => U + ricciTimeCorrection (g t) (f t • T t)) hd
    _ = f' • T t + f t • (Tdot + ricciTimeCorrection (g t) (T t)) := by
      rw [ricciTimeCorrection_smul]
      module
    _ = _ := congrArg (fun U : Tensor0SSpace s I x => f' • T t + f t • (U + ricciTimeCorrection (g t) (T t))) he.symm

theorem ricciTimeCorrection_metric (g : SmoothRiemannianMetric I M) (x : M) :
    ricciTimeCorrection g (metricTensorField g x) = (2 : ℝ) • metricRicciAt g x := by
  apply tensor0SSpace_ext 2 x
  intro v
  rw [ricciTimeCorrection_apply]
  simp only [Fin.sum_univ_two, metricTensorField_apply, Function.update_self,
    Function.update_of_ne (by decide : (1 : Fin 2) ≠ 0),
    Function.update_of_ne (by decide : (0 : Fin 2) ≠ 1), Tensor0SSpace.smul_apply, smul_eq_mul]
  rw [inner_ricciSharp, inner_ricciSharp_right, ricciTensor_symm g x (v 1) (v 0)]
  have hv : v = vec2 (v 0) (v 1) := by ext i; fin_cases i <;> rfl
  have he : metricRicciAt g x v = ricciTensor g x (v 0) (v 1) :=
    (congrArg (metricRicciAt g x) hv).trans (metricRicciAt_apply_eq_ricciTensor g x (v 0) (v 1))
  rw [he]
  ring

theorem hasDerivWithinAt_metric_of_ricciFlow (g : ℝ → SmoothRiemannianMetric I M)
    (J : Set ℝ) (t : ℝ) (x : M)
    (hflow : ∀ v w : TangentSpace I x,
      HasDerivWithinAt (fun r => (g r).inner x v w)
        (-2 * ricciTensor (g t) x v w) J t) :
    HasDerivWithinAt (fun r => metricTensorField (g r) x)
      ((-2 : ℝ) • metricRicciAt (g t) x) J t := by
  apply hasDerivWithinAt_tensor0S_of_eval
  intro v
  have hv : v = vec2 (v 0) (v 1) := by ext i; fin_cases i <;> rfl
  have he : metricRicciAt (g t) x v = ricciTensor (g t) x (v 0) (v 1) :=
    (congrArg (metricRicciAt (g t) x) hv).trans (metricRicciAt_apply_eq_ricciTensor (g t) x (v 0) (v 1))
  simpa only [metricTensorField_apply, Tensor0SSpace.smul_apply, smul_eq_mul, he] using hflow (v 0) (v 1)

theorem covariantTimeDerivWithin_metric (g : ℝ → SmoothRiemannianMetric I M)
    (J : Set ℝ) (t : ℝ) (hJ : UniqueDiffWithinAt ℝ J t) (x : M)
    (hflow : ∀ v w : TangentSpace I x,
      HasDerivWithinAt (fun r => (g r).inner x v w)
        (-2 * ricciTensor (g t) x v w) J t) :
    covariantTimeDerivWithin g (fun r => metricTensorField (g r) x) J t = 0 := by
  have hd := hasDerivWithinAt_metric_of_ricciFlow g J t x hflow
  have he : derivWithin (fun r => metricTensorField (g r) x) J t = (-2 : ℝ) • metricRicciAt (g t) x :=
    hd.derivWithin hJ
  change derivWithin (fun r => metricTensorField (g r) x) J t + ricciTimeCorrection (g t) (metricTensorField (g t) x) = 0
  exact (congrArg (fun U : Tensor0SSpace 2 I x => U + ricciTimeCorrection (g t) (metricTensorField (g t) x)) he).trans (by
    rw [ricciTimeCorrection_metric]
    module)
end DifferentialGeometry.PDE.RicciFlow
