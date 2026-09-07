import DifferentialGeometry.Geometry.Curvature.Metric
import DifferentialGeometry.Tensor.RSTensor.NablaOnTensors.TotalNabla0SLinear
import DifferentialGeometry.Tensor.RSTensor.NablaOnTensors.Regularity.TotalNabla0S
import DifferentialGeometry.Tensor.RSTensor.MetricTrace.NablaTraceGen

noncomputable section

namespace DifferentialGeometry.PDE.RicciFlow

open Bundle DifferentialGeometry.Tensor0SBundle
open DifferentialGeometry.Integral.Connection
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Geometry.Operator
open DifferentialGeometry.Tensor.RSTensor
open scoped Manifold ContDiff BigOperators

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace Real E]
variable [FiniteDimensional Real E]
variable {H : Type*} [TopologicalSpace H]
variable {I : ModelWithCorners Real E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

variable [SigmaCompactSpace M] [T2Space M]

private theorem sub_of_add_smul {A B : Type*}
    [AddCommGroup A] [Module Real A] [AddCommGroup B] [Module Real B]
    (f : A -> B) (hadd : ∀ a b : A, f (a + b) = f a + f b)
    (hsmul : ∀ (c : Real) (a : A), f (c • a) = c • f a) (a b : A) :
    f (a - b) = f a - f b := by
  have hab : a - b = a + (-1 : Real) • b := by
    rw [neg_one_smul, ← sub_eq_add_neg]
  rw [hab, hadd, hsmul, neg_one_smul, ← sub_eq_add_neg]

section Operators

variable {s : ℕ}

def metricNabla0S (g : SmoothRiemannianMetric I M)
    (T : Tensor0SField (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      (n := (∞ : WithTop ℕ∞)) s) :
    Tensor0SField (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      (n := (∞ : WithTop ℕ∞)) (s + 1) :=
  totalNabla0S (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) s
    (metricCov (I := I) g) T
    (totalNabla0S_reg (E := E) (H := H) (I := I) (M := M) s
      (metricCov (I := I) g) (metricCov_smooth (I := I) g) T)

omit [SigmaCompactSpace M] in
@[simp] theorem metricNabla0S_apply (g : SmoothRiemannianMetric I M)
    (T : Tensor0SField (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      (n := (∞ : WithTop ℕ∞)) s) (x : M) :
    metricNabla0S (I := I) g T x =
      totalNabla0SFun (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) s
        (metricCov (I := I) g) T x := rfl

omit [SigmaCompactSpace M] in
theorem metricNabla0S_add (g : SmoothRiemannianMetric I M)
    (T U : Tensor0SField (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      (n := (∞ : WithTop ℕ∞)) s) :
    metricNabla0S (I := I) g (T + U) =
      metricNabla0S (I := I) g T + metricNabla0S (I := I) g U := by
  refine DFunLike.ext _ _ fun x => ?_
  have hsplit :
      (metricNabla0S (I := I) g T + metricNabla0S (I := I) g U) x
        = metricNabla0S (I := I) g T x + metricNabla0S (I := I) g U x := rfl
  rw [hsplit]
  exact totalNabla0SFun_add (I := I) (M := M) (metricCov (I := I) g) T U x

omit [SigmaCompactSpace M] in
theorem metricNabla0S_smul (g : SmoothRiemannianMetric I M) (c : Real)
    (T : Tensor0SField (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      (n := (∞ : WithTop ℕ∞)) s) :
    metricNabla0S (I := I) g (c • T) = c • metricNabla0S (I := I) g T := by
  refine DFunLike.ext _ _ fun x => ?_
  have hsplit :
      (c • metricNabla0S (I := I) g T) x = c • (metricNabla0S (I := I) g T x) := rfl
  rw [hsplit]
  exact totalNabla0SFun_smul (I := I) (M := M) (metricCov (I := I) g) c T x

omit [SigmaCompactSpace M] in
theorem metricNabla0S_sub (g : SmoothRiemannianMetric I M)
    (T U : Tensor0SField (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      (n := (∞ : WithTop ℕ∞)) s) :
    metricNabla0S (I := I) g (T - U) =
      metricNabla0S (I := I) g T - metricNabla0S (I := I) g U :=
  sub_of_add_smul (metricNabla0S (I := I) g) (metricNabla0S_add (I := I) g)
    (fun c a => metricNabla0S_smul (I := I) g c a) T U

omit [SigmaCompactSpace M] [T2Space M] in
theorem traceFirstTwo_sub (g : SmoothRiemannianMetric I M)
    (A B : Tensor0SField (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      (n := (∞ : WithTop ℕ∞)) (s + 2)) :
    metricTraceFirstTwoField (I := I) (M := M) g (A - B) =
      metricTraceFirstTwoField (I := I) (M := M) g A -
        metricTraceFirstTwoField (I := I) (M := M) g B :=
  sub_of_add_smul (metricTraceFirstTwoField (I := I) (M := M) (s := s) g)
    (metricTraceFirstTwoField_add (I := I) (M := M) g)
    (fun c a => metricTraceFirstTwoField_smul (I := I) (M := M) g c a) A B

omit [SigmaCompactSpace M] [T2Space M] in
theorem traceFirstTwo_zero (g : SmoothRiemannianMetric I M) :
    metricTraceFirstTwoField (I := I) (M := M) g
        (0 : Tensor0SField (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
          (n := (∞ : WithTop ℕ∞)) (s + 2)) = 0 := by
  simpa using traceFirstTwo_sub (I := I) (M := M) (s := s) g 0 0

def covDiv0SField (g : SmoothRiemannianMetric I M)
    (V : Tensor0SField (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      (n := (∞ : WithTop ℕ∞)) (s + 1)) :
    Tensor0SField (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      (n := (∞ : WithTop ℕ∞)) s :=
  metricTraceFirstTwoField (I := I) (M := M) g (metricNabla0S (I := I) g V)

def roughLap0SField (g : SmoothRiemannianMetric I M)
    (T : Tensor0SField (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      (n := (∞ : WithTop ℕ∞)) s) :
    Tensor0SField (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      (n := (∞ : WithTop ℕ∞)) s :=
  covDiv0SField (I := I) g (metricNabla0S (I := I) g T)

omit [SigmaCompactSpace M] in
theorem roughLap0SField_apply (g : SmoothRiemannianMetric I M)
    (T : Tensor0SField (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      (n := (∞ : WithTop ℕ∞)) s) (x : M) :
    roughLap0SField (I := I) g T x =
      roughLap0STensor (I := I) g
        (metricNabla0S (I := I) g (metricNabla0S (I := I) g T) x) := rfl

omit [SigmaCompactSpace M] in
theorem covDiv0SField_sub (g : SmoothRiemannianMetric I M)
    (V W : Tensor0SField (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      (n := (∞ : WithTop ℕ∞)) (s + 1)) :
    covDiv0SField (I := I) g (V - W) =
      covDiv0SField (I := I) g V - covDiv0SField (I := I) g W := by
  rw [covDiv0SField, covDiv0SField, covDiv0SField, metricNabla0S_sub,
    traceFirstTwo_sub]

end Operators

end DifferentialGeometry.PDE.RicciFlow
