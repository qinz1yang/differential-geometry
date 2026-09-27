import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Contract.HornComponents
import DifferentialGeometry.Geometry.Neck.ScalarDistanceBarrier

set_option autoImplicit false
noncomputable section

open Set Filter
open scoped Manifold ContDiff Topology ENNReal

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.TerminalCorePresentation

open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn

universe u

theorem eventually_scaled_distance_to_horn_base_gt_of_base_necks
    (D : ℕ → OneStepIncoming.{u}) {eps Lambda : ℝ}
    (P : ∀ i, TerminalCorePresentation (D i) eps Lambda)
    (c : ∀ i, ConnectedComponents (D i).slab.terminalRegularOpen)
    (e : ∀ i, (P i).hornIndex (c i))
    (x p : ∀ i, (D i).slab.terminalRegularOpen)
    (N : ∀ i, SpatialNeck (D i).terminal.metric (1 / 156000) (p i))
    (level : ℕ → ℝ) (hlevel : ∀ i, |level i| ≤ 3)
    (hbase : ∀ i y, (P i).horn (c i) (e i) (y, 0) = (N i).map (y, level i))
    {B : ℝ} (hB : 0 < B)
    (hscalar : ∀ i, metricScalarAt (D i).terminal.metric (p i) ≤ B)
    (Q : ℕ → ℝ) (hQ : ∀ i, 0 < Q i)
    (hQeq : ∀ i, Q i = metricScalarAt (D i).terminal.metric (x i))
    (hQlim : Tendsto Q atTop atTop) (R : ℝ) :
    ∀ᶠ i in atTop, ∀ y : Sphere 2,
      ENNReal.ofReal R < riemannianEDistOf
        (scaleMetric (Q i) (hQ i) (D i).terminal.metric) (x i)
        ((P i).horn (c i) (e i) (y, 0)) := by
  have h := eventually_scaled_ball_disjoint_spatial_neck_sphere
    (fun i => (D i).terminal.metric) p x le_rfl hB N level
    (fun i => (hlevel i).trans (by norm_num)) hscalar Q hQ hQeq hQlim R
  filter_upwards [h] with i hi y
  apply lt_of_not_ge
  intro hnear
  exact disjoint_left.mp hi hnear ⟨y, (hbase i y).symm⟩

theorem eventually_scaled_closedBall_subset_positive_horn_of_base_necks
    (D : ℕ → OneStepIncoming.{u}) {eps Lambda : ℝ}
    (P : ∀ i, TerminalCorePresentation (D i) eps Lambda)
    (c : ∀ i, ConnectedComponents (D i).slab.terminalRegularOpen)
    (e : ∀ i, (P i).hornIndex (c i))
    (x p : ∀ i, (D i).slab.terminalRegularOpen)
    (hx : ∀ i, x i ∈ (P i).horn (c i) (e i) '' (univ ×ˢ Ioi (0 : ℝ)))
    (N : ∀ i, SpatialNeck (D i).terminal.metric (1 / 156000) (p i))
    (level : ℕ → ℝ) (hlevel : ∀ i, |level i| ≤ 3)
    (hbase : ∀ i y, (P i).horn (c i) (e i) (y, 0) = (N i).map (y, level i))
    {B : ℝ} (hB : 0 < B)
    (hscalar : ∀ i, metricScalarAt (D i).terminal.metric (p i) ≤ B)
    (Q : ℕ → ℝ) (hQ : ∀ i, 0 < Q i)
    (hQeq : ∀ i, Q i = metricScalarAt (D i).terminal.metric (x i))
    (hQlim : Tendsto Q atTop atTop) (R : ℝ) :
    ∀ᶠ i in atTop,
      riemannianClosedBallOf (scaleMetric (Q i) (hQ i) (D i).terminal.metric) (x i) R ⊆
        (P i).horn (c i) (e i) '' (univ ×ˢ Ioi (0 : ℝ)) := by
  have hfront (i : ℕ) : frontier ((P i).horn (c i) (e i) '' (univ ×ˢ Ioi (0 : ℝ))) =
      range (fun y : Sphere 2 => (N i).map (y, level i)) := by
    rw [(P i).frontier_positive_horn_eq_base]
    exact congrArg range (funext (hbase i))
  have h := eventually_scaled_closedBall_subset_of_spatial_neck_frontier
    (fun i => (D i).terminal.metric) p x le_rfl hB N level
    (fun i => (hlevel i).trans (by norm_num)) hscalar
    (fun i => (P i).horn (c i) (e i) '' (univ ×ˢ Ioi (0 : ℝ)))
    (fun i => (P i).isOpen_positive_horn (c i) (e i) |>.interior_eq |>.symm ▸ hx i)
    hfront Q hQ hQeq hQlim R
  exact h.mono fun i hi => by rwa [(P i).isOpen_positive_horn (c i) (e i) |>.interior_eq] at hi

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.TerminalCorePresentation
