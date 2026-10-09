import DifferentialGeometry.Geometry.Exponential.Flat.TorusType
import DifferentialGeometry.Geometry.Curvature.Coordinates.RiemannTensorBridge
import DifferentialGeometry.Geometry.Metric.Completeness

/-!
# A closed orientable surface with a flat smooth metric is the torus

SF4(c) (`Riemannian.Exponential.nonempty_diffeomorph_addCircle_prod_of_flat`) is stated inside
the radial-flat instance block (a Riemannian bundle, the Riemannian extended metric, completeness).
Here it is bound to a plain smooth metric on a compact connected oriented surface modelled on
`𝓡 2` whose curvature tensor vanishes (the flat branch of SF2): the instances are built from the
metric itself, as in `GC.Endpoint.exists_isCoveringMap_of_euclidean`, and the vanishing of
`metricRm04StandardAt` gives the vanishing of the Riemann operator through `rm04_eq_inner_riem`.
-/

set_option autoImplicit false

noncomputable section

open Bundle Manifold
open scoped Manifold ContDiff Topology
open DifferentialGeometry DifferentialGeometry.Geometry DifferentialGeometry.Geometry.Riemannian
  DifferentialGeometry.Geometry.Riemannian.Exponential
  DifferentialGeometry.Geometry.Curvature DifferentialGeometry.Geometry.Connection

namespace DifferentialGeometry.Geometry.ClosedSurface

local notation "E2" => EuclideanSpace ℝ (Fin 2)

variable {Z : Type*} [TopologicalSpace Z] [ChartedSpace E2 Z] [IsManifold (𝓡 2) ∞ Z]
  [T2Space Z] [CompactSpace Z] [ConnectedSpace Z]

omit [CompactSpace Z] [ConnectedSpace Z] in
/-- The Riemann operator of the Levi-Civita connection vanishes when the `(0,4)` curvature
tensor does. -/
theorem riemannOp_eq_zero_of_rm04_eq_zero (h : SmoothRiemannianMetric (𝓡 2) Z)
    (hflat : ∀ x (v w z u : TangentSpace (𝓡 2) x), metricRm04StandardAt h x v w z u = 0)
    (x : Z) (X Y W : TangentSpace (𝓡 2) x) :
    riemannOp (LeviCivita (I := 𝓡 2) h) x X Y W = 0 := by
  by_contra hne
  have hpos := h.pos x _ hne
  rw [← rm04_eq_inner_riem h x X Y W, hflat] at hpos
  exact lt_irrefl 0 hpos

private instance finrankTwoNeZero : NeZero (Module.finrank ℝ E2) := ⟨by simp⟩

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
/-- **SF4(c) for a plain smooth metric.** A compact connected oriented surface modelled on `𝓡 2`
with a smooth metric of vanishing curvature tensor is diffeomorphic to `ℝ²/ℤ²`. -/
theorem nonempty_diffeomorph_torus_of_rm04_eq_zero (o : ManifoldOrientation (𝓡 2) Z 2)
    (h : SmoothRiemannianMetric (𝓡 2) Z)
    (hflat : ∀ x (v w z u : TangentSpace (𝓡 2) x), metricRm04StandardAt h x v w z u = 0) :
    Nonempty (Z ≃ₘ⟮𝓡 2, 𝓘(ℝ, ℝ).prod 𝓘(ℝ, ℝ)⟯ (AddCircle (1 : ℝ) × AddCircle (1 : ℝ))) := by
  let : IsManifold (𝓡 2) 1 Z :=
    IsManifold.of_le (I := 𝓡 2) (M := Z) (n := (∞ : WithTop ℕ∞)) (by decide)
  let : TopologicalSpace.MetrizableSpace Z := Manifold.metrizableSpace (𝓡 2) Z
  let : T3Space Z := inferInstance
  let : RiemannianBundle (fun x : Z => TangentSpace (𝓡 2) x) := ⟨h.toRiemannianMetric⟩
  let : IsContinuousRiemannianBundle E2 (fun x : Z => TangentSpace (𝓡 2) x) :=
    ⟨⟨h.inner, h.contMDiff.continuous, by intro x v w; rfl⟩⟩
  let : EMetricSpace Z := EMetricSpace.ofRiemannianMetric (𝓡 2) Z
  let : CompleteSpace Z := (RiemannianMetricComplete.of_compact h).complete
  have hEg : IsMetricNorm (I := 𝓡 2) (M := Z) h := fun z v =>
    tensor0SBundle_enorm_eq_riemannianBundle_enorm (I := 𝓡 2) h z v
  exact nonempty_diffeomorph_addCircle_prod_of_flat (I := 𝓡 2) (by simp) o h hEg
    (riemannOp_eq_zero_of_rm04_eq_zero h hflat)

end DifferentialGeometry.Geometry.ClosedSurface
