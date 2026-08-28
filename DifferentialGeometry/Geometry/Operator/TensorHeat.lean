import DifferentialGeometry.Geometry.Operator.RoughLaplacian
import DifferentialGeometry.Geometry.Metric.Family.Basic
import DifferentialGeometry.Geometry.Operator.Operators
open DifferentialGeometry.Geometry.Curvature

set_option autoImplicit false

namespace DifferentialGeometry.Geometry.Operator

noncomputable section

open Bundle DifferentialGeometry.Tensor0SBundle
open scoped Manifold ContDiff

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace Real E]
variable [FiniteDimensional Real E]
variable {H : Type*} [TopologicalSpace H]
variable {I : ModelWithCorners Real E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
variable {Time : Type*}

private theorem metricTraceFirstTwo0SAt_zero
    (g : SmoothRiemannianMetric I M)
    {x : M} {s : ℕ}
    (tail : Fin s -> TangentSpace I x) :
    metricTraceFirstTwo0SAt (I := I) g
        (0 : Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
          (s + 2) x)
        tail = 0 := by
  rw [metricTraceFirstTwo0SAt_eq_sum_basis (I := I) g
    (DifferentialGeometry.Tensor.Coordinates.coordinateFrameAt_toBasis (I := I) x)
    (fun k l : DifferentialGeometry.Tensor.Coordinates.CoordinateIdx (𝕜 := Real) E =>
      DifferentialGeometry.Tensor.Coordinates.inverseMetricFlatModelInChart_component (I := I) g x k
        l
        (extChartAt I x x))
    (Tensor.Coordinates.inverseMetricFlatModelInChart_metricInverseInBasis_center
      (I := I) g x)
    (0 : Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      (s + 2) x)
    tail]
  simp [metricTrace0S2InBasis]

def tensorHeat0SMetricAt
    (g : SmoothRiemannianMetric I M)
    {x : M} {s : ℕ}
    (nabla2A : Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      (s + 2) x) :
    Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) s x :=
  roughLap0STensor (I := I) g nabla2A

@[simp]
theorem tensorHeat0SMetricAt_apply
    (g : SmoothRiemannianMetric I M)
    {x : M} {s : ℕ}
    (nabla2A : Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      (s + 2) x)
    (tail : Fin s -> TangentSpace I x) :
    tensorHeat0SMetricAt (I := I) g nabla2A tail =
      metricTraceFirstTwo0SAt (I := I) g nabla2A tail := by
  exact roughLap0STensor_apply (I := I) g nabla2A tail

def tensorHeat0SAt
    (G : MetricConnectionFamily (I := I) (M := M) Time)
    (t : Time) {x : M} {s : ℕ}
    (nabla2A : Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      (s + 2) x) :
    Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) s x :=
  tensorHeat0SMetricAt (I := I) (G.metric t) nabla2A

@[simp]
theorem tensorHeat0SAt_apply
    (G : MetricConnectionFamily (I := I) (M := M) Time)
    (t : Time) {x : M} {s : ℕ}
    (nabla2A : Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      (s + 2) x)
    (tail : Fin s -> TangentSpace I x) :
    tensorHeat0SAt (I := I) G t nabla2A tail =
      metricTraceFirstTwo0SAt (I := I) (G.metric t) nabla2A tail := by
  exact tensorHeat0SMetricAt_apply (I := I) (G.metric t) nabla2A tail

def tensorDrift0SAt
    (X : (x : M) -> TangentSpace I x)
    {x : M} {s : ℕ}
    (nablaA : Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      (s + 1) x) :
    Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) s x :=
  tensor0S_curry (I := I) (𝕜 := Real) (M := M) s x nablaA (X x)

omit [FiniteDimensional ℝ E] in
@[simp]
theorem tensorDrift0SAt_apply
    (X : (x : M) -> TangentSpace I x)
    {x : M} {s : ℕ}
    (nablaA : Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      (s + 1) x)
    (tail : Fin s -> TangentSpace I x) :
    tensorDrift0SAt (I := I) X nablaA tail =
      nablaA (Fin.cons (X x) tail) := by
  exact Tensor0SBundle.tensor0S_curry_apply_cons (I := I) s nablaA (X x) tail

def tensorHeatWithDrift0SMetricAt
    (g : SmoothRiemannianMetric I M)
    (X : (x : M) -> TangentSpace I x)
    {x : M} {s : ℕ}
    (nabla2A : Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      (s + 2) x)
    (nablaA : Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      (s + 1) x) :
    Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) s x :=
  tensorHeat0SMetricAt (I := I) g nabla2A + tensorDrift0SAt (I := I) X nablaA

@[simp]
theorem tensorHeatWithDrift0SMetricAt_apply
    (g : SmoothRiemannianMetric I M)
    (X : (x : M) -> TangentSpace I x)
    {x : M} {s : ℕ}
    (nabla2A : Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      (s + 2) x)
    (nablaA : Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      (s + 1) x)
    (tail : Fin s -> TangentSpace I x) :
    tensorHeatWithDrift0SMetricAt (I := I) g X nabla2A nablaA tail =
      metricTraceFirstTwo0SAt (I := I) g nabla2A tail +
        nablaA (Fin.cons (X x) tail) := by
  simp [tensorHeatWithDrift0SMetricAt]

def tensorHeatWithDrift0SAt
    (G : MetricConnectionFamily (I := I) (M := M) Time)
    (t : Time) (X : (x : M) -> TangentSpace I x)
    {x : M} {s : ℕ}
    (nabla2A : Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      (s + 2) x)
    (nablaA : Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      (s + 1) x) :
    Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) s x :=
  tensorHeatWithDrift0SMetricAt (I := I) (G.metric t) X nabla2A nablaA

@[simp]
theorem tensorHeatWithDrift0SAt_apply
    (G : MetricConnectionFamily (I := I) (M := M) Time)
    (t : Time) (X : (x : M) -> TangentSpace I x)
    {x : M} {s : ℕ}
    (nabla2A : Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      (s + 2) x)
    (nablaA : Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      (s + 1) x)
    (tail : Fin s -> TangentSpace I x) :
    tensorHeatWithDrift0SAt (I := I) G t X nabla2A nablaA tail =
      metricTraceFirstTwo0SAt (I := I) (G.metric t) nabla2A tail +
        nablaA (Fin.cons (X x) tail) := by
  exact tensorHeatWithDrift0SMetricAt_apply (I := I) (G.metric t) X nabla2A nablaA tail

def tensorHeatWithDrift2MetricAt
    (g : SmoothRiemannianMetric I M)
    (X : (x : M) -> TangentSpace I x)
    {x : M}
    (nabla2A : Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      4 x)
    (nablaA : Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      3 x) :
    Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) 2 x :=
  tensorHeatWithDrift0SMetricAt (I := I) (s := 2) g X nabla2A nablaA

@[simp]
theorem tensorHeatWithDrift2MetricAt_apply
    (g : SmoothRiemannianMetric I M)
    (X : (x : M) -> TangentSpace I x)
    {x : M}
    (nabla2A : Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      4 x)
    (nablaA : Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      3 x)
    (v : Fin 2 -> TangentSpace I x) :
    tensorHeatWithDrift2MetricAt (I := I) g X nabla2A nablaA v =
      metricTraceFirstTwo0SAt (I := I) g nabla2A v +
        nablaA (Fin.cons (X x) v) := by
  simp [tensorHeatWithDrift2MetricAt]

def tensorHeatWithDrift2At
    (G : MetricConnectionFamily (I := I) (M := M) Time)
    (t : Time) (X : (x : M) -> TangentSpace I x)
    {x : M}
    (nabla2A : Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      4 x)
    (nablaA : Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      3 x) :
    Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) 2 x :=
  tensorHeatWithDrift2MetricAt (I := I) (G.metric t) X nabla2A nablaA

@[simp]
theorem tensorHeatWithDrift2At_apply
    (G : MetricConnectionFamily (I := I) (M := M) Time)
    (t : Time) (X : (x : M) -> TangentSpace I x)
    {x : M}
    (nabla2A : Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      4 x)
    (nablaA : Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      3 x)
    (v : Fin 2 -> TangentSpace I x) :
    tensorHeatWithDrift2At (I := I) G t X nabla2A nablaA v =
      metricTraceFirstTwo0SAt (I := I) (G.metric t) nabla2A v +
        nablaA (Fin.cons (X x) v) := by
  exact tensorHeatWithDrift2MetricAt_apply (I := I) (G.metric t) X nabla2A nablaA v

def tensorHeatWithDrift2QuadMetricAt
    (g : SmoothRiemannianMetric I M)
    (X : (x : M) -> TangentSpace I x)
    {x : M}
    (nabla2A : Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      4 x)
    (nablaA : Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      3 x)
    (v : TangentSpace I x) : Real :=
  tensorHeatWithDrift2MetricAt (I := I) g X nabla2A nablaA (vec2 v v)

@[simp]
theorem tensorHeatWithDrift2QuadMetricAt_eq
    (g : SmoothRiemannianMetric I M)
    (X : (x : M) -> TangentSpace I x)
    {x : M}
    (nabla2A : Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      4 x)
    (nablaA : Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      3 x)
    (v : TangentSpace I x) :
    tensorHeatWithDrift2QuadMetricAt (I := I) g X nabla2A nablaA v =
      metricTraceFirstTwo0SAt (I := I) g nabla2A (vec2 v v) +
        nablaA (Fin.cons (X x) (vec2 v v)) := by
  simp [tensorHeatWithDrift2QuadMetricAt]

theorem tensorHeatWithDrift2QuadMetricAt_zero_drift
    (g : SmoothRiemannianMetric I M)
    {x : M}
    (nabla2A : Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      4 x)
    (nablaA : Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      3 x)
    (v : TangentSpace I x) :
    tensorHeatWithDrift2QuadMetricAt (I := I) g
        (fun _y : M => 0) nabla2A nablaA v =
      metricTraceFirstTwo0SAt (I := I) g nabla2A (vec2 v v) := by
  rw [tensorHeatWithDrift2QuadMetricAt_eq]
  have hzero :
      nablaA (Fin.cons (n := 2)
          (α := fun _ : Fin 3 => TangentSpace I x)
          (0 : TangentSpace I x) (vec2 (I := I) v v)) = 0 := by
    simpa using
      Tensor0SSpace.map_update_smul nablaA
        (Fin.cons (n := 2) (α := fun _ : Fin 3 => TangentSpace I x)
          (0 : TangentSpace I x) (vec2 (I := I) v v))
        (0 : Fin 3) (0 : Real) (0 : TangentSpace I x)
  simpa using hzero

theorem heatQuad_eq_parts
    (g : SmoothRiemannianMetric I M)
    (X : (x : M) -> TangentSpace I x)
    {x : M}
    (nabla2A : Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      4 x)
    (nablaA : Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      3 x)
    (v : TangentSpace I x)
    (laplacian drift : Real)
    (hlap :
      metricTraceFirstTwo0SAt (I := I) g nabla2A (vec2 v v) = laplacian)
    (hdrift : nablaA (Fin.cons (X x) (vec2 v v)) = drift) :
    tensorHeatWithDrift2QuadMetricAt (I := I) g X nabla2A nablaA v =
      laplacian + drift := by
  rw [tensorHeatWithDrift2QuadMetricAt_eq, hlap, hdrift]

theorem tensorHeatWithDrift2QuadMetricAt_zero
    (g : SmoothRiemannianMetric I M)
    (X : (x : M) -> TangentSpace I x)
    {x : M} (v : TangentSpace I x) :
    tensorHeatWithDrift2QuadMetricAt (I := I) g X
        (0 : Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
          4 x)
        (0 : Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
          3 x)
        v = 0 := by
  rw [tensorHeatWithDrift2QuadMetricAt_eq]
  rw [metricTraceFirstTwo0SAt_zero]
  simp

def tensorHeatWithDrift2QuadAt
    (G : MetricConnectionFamily (I := I) (M := M) Time)
    (t : Time) (X : (x : M) -> TangentSpace I x)
    {x : M}
    (nabla2A : Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      4 x)
    (nablaA : Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      3 x)
    (v : TangentSpace I x) : Real :=
  tensorHeatWithDrift2QuadMetricAt (I := I) (G.metric t) X nabla2A nablaA v

@[simp]
theorem tensorHeatWithDrift2QuadAt_eq
    (G : MetricConnectionFamily (I := I) (M := M) Time)
    (t : Time) (X : (x : M) -> TangentSpace I x)
    {x : M}
    (nabla2A : Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      4 x)
    (nablaA : Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      3 x)
    (v : TangentSpace I x) :
    tensorHeatWithDrift2QuadAt (I := I) G t X nabla2A nablaA v =
      metricTraceFirstTwo0SAt (I := I) (G.metric t) nabla2A (vec2 v v) +
        nablaA (Fin.cons (X x) (vec2 v v)) := by
  exact tensorHeatWithDrift2QuadMetricAt_eq (I := I) (G.metric t) X nabla2A nablaA v

theorem tensorHeatWithDrift2QuadAt_zero
    (G : MetricConnectionFamily (I := I) (M := M) Time)
    (t : Time) (X : (x : M) -> TangentSpace I x)
    {x : M} (v : TangentSpace I x) :
    tensorHeatWithDrift2QuadAt (I := I) G t X
        (0 : Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
          4 x)
        (0 : Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
          3 x)
        v = 0 := by
  rw [tensorHeatWithDrift2QuadAt_eq]
  rw [metricTraceFirstTwo0SAt_zero]
  simp

end

end DifferentialGeometry.Geometry.Operator
