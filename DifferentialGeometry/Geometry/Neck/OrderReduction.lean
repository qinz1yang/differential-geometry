import DifferentialGeometry.Geometry.Neck.InsertionOrientation

set_option autoImplicit false
noncomputable section
open Set Function Bundle Manifold TopologicalSpace DifferentialGeometry
open DifferentialGeometry.Geometry.Metric
open scoped Manifold ContDiff
namespace DifferentialGeometry.Geometry.Neck.normalizedDatum
variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [Fact (Module.finrank ℝ E = 3)]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [T2Space M]
  {g : SmoothRiemannianMetric I M} {x₀ : M} {δ : ℝ} {k j : ℕ}

def lowerOrder (d : normalizedDatum g x₀ δ k) (hjk : j ≤ k) : normalizedDatum g x₀ δ j where
  precision_pos := d.precision_pos
  precision_lt_one := d.precision_lt_one
  map := d.map
  smooth := d.smooth
  injective := d.injective
  immersion := d.immersion
  center_eq := d.center_eq
  scalar_pos := d.scalar_pos
  retainedSide := d.retainedSide
  error_lt := (metricDerivENormSupOn_mono (subset_refl _) hjk _ _ _).trans_lt d.error_lt

theorem lowerOrder_map (d : normalizedDatum g x₀ δ k) (hjk : j ≤ k) :
    (d.lowerOrder hjk).map = d.map := rfl

theorem lowerOrder_retainedSide (d : normalizedDatum g x₀ δ k) (hjk : j ≤ k) :
    (d.lowerOrder hjk).retainedSide = d.retainedSide := rfl

theorem lowerOrder_normalizedMetric (d : normalizedDatum g x₀ δ k) (hjk : j ≤ k) :
    (d.lowerOrder hjk).normalizedMetric = d.normalizedMetric := rfl

theorem lowerOrder_controlledMap (d : normalizedDatum g x₀ δ k) (hjk : j ≤ k) :
    (d.lowerOrder hjk).controlledMap = d.controlledMap := rfl

theorem lowerOrder_controlledImage (d : normalizedDatum g x₀ δ k) (hjk : j ≤ k) :
    (d.lowerOrder hjk).controlledImage = d.controlledImage := rfl

theorem lowerOrder_oriented (d : normalizedDatum g x₀ δ k) (hjk : j ≤ k) :
    (d.lowerOrder hjk).oriented = d.oriented.lowerOrder hjk := rfl

theorem lowerOrder_rescaled (d : normalizedDatum g x₀ δ k) (hjk : j ≤ k) (c : ℝ) (hc : 0 < c) :
    (d.lowerOrder hjk).rescaled c hc = (d.rescaled c hc).lowerOrder hjk := rfl
end DifferentialGeometry.Geometry.Neck.normalizedDatum
