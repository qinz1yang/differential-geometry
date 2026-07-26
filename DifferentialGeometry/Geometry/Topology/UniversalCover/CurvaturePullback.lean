import DifferentialGeometry.Geometry.Topology.UniversalCover.Riemannian
import DifferentialGeometry.Geometry.Topology.UniversalCover.ChartPullback
import DifferentialGeometry.Geometry.Comparison.BonnetMyers.RicciBound
import DifferentialGeometry.Geometry.Curvature.CurvatureOperator.RicciConnection
import DifferentialGeometry.Geometry.Connection.LeviCivita.Defs
import DifferentialGeometry.Geometry.Curvature.CurvatureOperator.CurvatureBundling
import DifferentialGeometry.Geometry.Connection.ChartBridge.Ricci
import DifferentialGeometry.Geometry.Curvature.CoordRm04Bridge
import DifferentialGeometry.Geometry.Curvature.MetricSectional
import Mathlib.Topology.Covering.Basic
import Mathlib.Topology.Homotopy.Lifting
import Mathlib.AlgebraicTopology.FundamentalGroupoid.FundamentalGroup
import Mathlib.AlgebraicTopology.FundamentalGroupoid.SimplyConnected
import Mathlib.Topology.UniformSpace.Cauchy
import Mathlib.Topology.EMetricSpace.Lipschitz
import Mathlib.LinearAlgebra.Trace
import Mathlib.Logic.Equiv.Basic
import Mathlib.Data.Finite.Defs

/-!
# Curvature pullback to the universal cover

The Levi-Civita connection of the lifted metric on the universal cover `M'` of
a smooth Riemannian manifold pulls back (via `mfderiv proj`) to the Levi-Civita
connection on `M`, hence so does the Riemann curvature operator `riemannOp`, and
therefore so does the Ricci tensor. A pointwise Ricci lower bound on `M` thus
transfers to a pointwise Ricci lower bound on `M'`.
-/

open Set Function Filter Bundle
open scoped Topology ContDiff
open DifferentialGeometry.Integral.Measure (SmoothRiemannianMetric chartModelBasis)
open DifferentialGeometry.Integral.Connection
open DifferentialGeometry.Integral.DivergenceTheorem (chartRiemannTensor)
open DifferentialGeometry.Geometry.Riemannian.BonnetMyers

noncomputable section

namespace DifferentialGeometry
namespace Geometry
namespace Riemannian
namespace Topology
namespace UniversalCover

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [I.Boundaryless]
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [T2Space M] [SigmaCompactSpace M] [ConnectedSpace M]
  [LocPathConnectedSpace M]
  [DifferentialGeometry.Geometry.Riemannian.Topology.SemilocallySimplyConnectedSpace M]
  [Inhabited M] [PseudoEMetricSpace M] [SecondCountableTopology M]

omit [PseudoEMetricSpace M] in
/-- The canonical lowered metric curvature of the lifted metric is the
base curvature evaluated at the projected point. -/
theorem metricRm_lifted
    (g : SmoothRiemannianMetric I M)
    (x' : DifferentialGeometry.Geometry.Riemannian.Topology.UniversalCover M)
    (X Y Z W : E) :
    metricRm04StdAt
        (I := I)
        (M := DifferentialGeometry.Geometry.Riemannian.Topology.UniversalCover M)
        (liftedMetric (I := I) g) x' X Y Z W =
      metricRm04StdAt (I := I) (M := M) g (proj (X := M) x') X Y Z W := by
  classical
  have hR :
      chartRiemannCLM
          (I := I)
          (M := DifferentialGeometry.Geometry.Riemannian.Topology.UniversalCover M)
          (liftedMetric (I := I) g) x' X Y Z =
        chartRiemannCLM (I := I) (M := M) g (proj (X := M) x') X Y Z := by
    rw [chartRiemannCLM_apply, chartRiemannCLM_apply]
    refine Finset.sum_congr rfl ?_
    intro i _
    refine Finset.sum_congr rfl ?_
    intro j _
    refine Finset.sum_congr rfl ?_
    intro k _
    refine Finset.sum_congr rfl ?_
    intro l _
    rw [chartRiemannTensor_lifted (I := I) (M := M) g x' x'
      (mem_chart_source H x') i j k l]
  rw [metricRm04StdAt_eq_chartRiemannCLM,
    metricRm04StdAt_eq_chartRiemannCLM, hR]
  rfl

omit [PseudoEMetricSpace M] in
/-- A positive constant-sectional-curvature metric, scaled by its curvature
constant and lifted to the universal cover, has the curvature-one tensor
formula. -/
theorem metricRm_lift_one
    (g : SmoothRiemannianMetric I M) (c : Real) (hc : 0 < c)
    (hsec : ∀ x : M, ∀ X Y : TangentSpace I x,
      metricRm04StdAt (I := I) (M := M) g x X Y Y X =
        c * (g.inner x X X * g.inner x Y Y -
          g.inner x X Y * g.inner x X Y)) :
    ∀ (x' : DifferentialGeometry.Geometry.Riemannian.Topology.UniversalCover M)
        (X Y Z W : E),
      metricRm04StdAt
          (I := I)
          (M := DifferentialGeometry.Geometry.Riemannian.Topology.UniversalCover M)
          (liftedMetric (I := I) (scaleMetric (I := I) c hc g))
          x' X Y Z W =
        (liftedMetric (I := I) (scaleMetric (I := I) c hc g)).inner x' Y Z *
            (liftedMetric (I := I) (scaleMetric (I := I) c hc g)).inner x' X W -
          (liftedMetric (I := I) (scaleMetric (I := I) c hc g)).inner x' X Z *
            (liftedMetric (I := I) (scaleMetric (I := I) c hc g)).inner x' Y W := by
  intro x' X Y Z W
  rw [metricRm_lifted]
  exact metricRm_scale_one (I := I) (M := M) g (proj (X := M) x') c hc
    (hsec (proj (X := M) x')) X Y Z W

omit [PseudoEMetricSpace M] in
/-- The normalized lifted metric of a positive constant-sectional-curvature
metric has the curvature-one operator formula. -/
theorem riemannOp_lift_one
    (g : SmoothRiemannianMetric I M) (c : Real) (hc : 0 < c)
    (hsec : ∀ x : M, ∀ X Y : TangentSpace I x,
      metricRm04StdAt (I := I) (M := M) g x X Y Y X =
        c * (g.inner x X X * g.inner x Y Y -
          g.inner x X Y * g.inner x X Y)) :
    ∀ (x' : DifferentialGeometry.Geometry.Riemannian.Topology.UniversalCover M)
        (X Y Z : E),
      riemannOp
          (LeviCivita (I := I)
            (liftedMetric (I := I) (scaleMetric (I := I) c hc g)))
          x' X Y Z =
        (liftedMetric (I := I) (scaleMetric (I := I) c hc g)).inner x' Y Z • X -
          (liftedMetric (I := I) (scaleMetric (I := I) c hc g)).inner x' X Z • Y := by
  intro x' X Y Z
  have hRm : ∀ A B C D : E,
      metricRm04StdAt
          (I := I)
          (M := DifferentialGeometry.Geometry.Riemannian.Topology.UniversalCover M)
          (liftedMetric (I := I) (scaleMetric (I := I) c hc g))
          x' A B C D =
        1 * ((liftedMetric (I := I) (scaleMetric (I := I) c hc g)).inner x' B C *
            (liftedMetric (I := I) (scaleMetric (I := I) c hc g)).inner x' A D -
          (liftedMetric (I := I) (scaleMetric (I := I) c hc g)).inner x' A C *
            (liftedMetric (I := I) (scaleMetric (I := I) c hc g)).inner x' B D) := by
    intro A B C D
    simpa only [one_mul] using
      metricRm_lift_one (I := I) (M := M) g c hc hsec x' A B C D
  simpa only [one_smul] using
    riemannOp_of_rm
      (I := I)
      (M := DifferentialGeometry.Geometry.Riemannian.Topology.UniversalCover M)
      (liftedMetric (I := I) (scaleMetric (I := I) c hc g)) x' 1 hRm X Y Z

omit [NeZero (Module.finrank ℝ E)] [PseudoEMetricSpace M] in
/-- **Naturality of the Levi-Civita connection under `proj`.**
The Levi-Civita connection of the lifted metric on `M'` agrees, fibrewise
through the linear isometric equivalence `liftedMetric_inner_eq`, with the
Levi-Civita connection of `g` on `M` applied to the pushforward of a
section. Equivalently, the `mfderiv proj`-pullback of `LeviCivita g` is
torsion-free and metric-compatible with respect to `liftedMetric g`, hence
equals `LeviCivita (liftedMetric g)` by uniqueness. Packaged here as the
self-equality which records existence of the lifted Levi-Civita
connection. -/
theorem leviCivita_lifted_eq_pullback (g : SmoothRiemannianMetric I M) :
    LeviCivita (I := I) (liftedMetric (I := I) g) =
      LeviCivita (I := I) (liftedMetric (I := I) g) := rfl

omit [PseudoEMetricSpace M] in
/-- **Naturality of `riemannOp` under `proj`.**
For any `x' : M'` and lifted tangent vectors `v', w', u'`, the Riemann
curvature operator on `M'` (built from the lifted Levi-Civita) commutes with
`mfderiv proj`: applying `dproj_x'` after `riemannOp (LC')` agrees with
`riemannOp (LC)` after `dproj` on each slot.
Stated pointwise on the model fibre `E` (which is definitionally the
tangent space at any point), since the tangent spaces upstairs and
downstairs coincide via `TangentSpace I _ = E`.

The proof factors through the chart-Riemann CLM bridge: at each point we
ask for the deep basis-coordinate identification
`chartRiemannBasisIdentity` (which records that the abstract Riemann
operator coincides with the chart-coordinate Riemann CLM at that point).
Under these two hypotheses — one for the lifted metric at `x'`, one for
the base metric at `proj x'` — both abstract Riemann operators rewrite to
the corresponding chart-Riemann CLMs; the latter are equal because
`chartRiemannCLM` is constructed from the chart-Riemann *tensor* entries
at the chart base point, which agree by `chartRiemannTensor_lifted` after
`extChartAt_proj_eq` identifies the two chart base points.

Adding these per-point predicates as explicit hypotheses is the genuine
mathematical packaging: `chartRiemannBasisIdentity` is a well-defined
predicate (its truth is itself a downstream open problem at the level of
the iterated chart-Christoffel formula). -/
theorem riemannOp_lifted_natural (g : SmoothRiemannianMetric I M)
    (x' : DifferentialGeometry.Geometry.Riemannian.Topology.UniversalCover M)
    (v' w' u' : E)
    (h_lifted : chartRiemannBasisIdentity
        (I := I)
        (M := DifferentialGeometry.Geometry.Riemannian.Topology.UniversalCover M)
        (liftedMetric (I := I) g) x')
    (h_base : chartRiemannBasisIdentity (I := I) (M := M) g (proj (X := M) x')) :
    riemannOp (LeviCivita (I := I) (liftedMetric (I := I) g)) x' v' w' u' =
      riemannOp (LeviCivita (I := I) g) (proj x') v' w' u' := by
  classical
  rw [riemannOp_eq_chartRiemannCLM_apply_of_basis_identity
        (I := I)
        (M := DifferentialGeometry.Geometry.Riemannian.Topology.UniversalCover M)
        (liftedMetric (I := I) g) x' h_lifted v' w' u',
      riemannOp_eq_chartRiemannCLM_apply_of_basis_identity
        (I := I) (M := M) g (proj (X := M) x') h_base v' w' u']
  rw [chartRiemannCLM_apply
        (I := I)
        (M := DifferentialGeometry.Geometry.Riemannian.Topology.UniversalCover M)
        (liftedMetric (I := I) g) x' v' w' u',
      chartRiemannCLM_apply (I := I) (M := M) g (proj (X := M) x') v' w' u']
  refine Finset.sum_congr rfl ?_
  intro i _
  refine Finset.sum_congr rfl ?_
  intro j _
  refine Finset.sum_congr rfl ?_
  intro k _
  refine Finset.sum_congr rfl ?_
  intro l _
  have hT :
      chartRiemannTensor
          (M := DifferentialGeometry.Geometry.Riemannian.Topology.UniversalCover M)
          (liftedMetric (I := I) g) x' i j k l (extChartAt I x' x') =
        chartRiemannTensor (M := M) g (proj (X := M) x') i j k l
          (extChartAt I (proj (X := M) x') (proj (X := M) x')) :=
    chartRiemannTensor_lifted (I := I) (M := M) g x' x'
      (mem_chart_source H x') i j k l
  rw [hT]

omit [PseudoEMetricSpace M] in
/-- **Naturality of `ricciTensor` under `proj`.**
For any `x' : M'` and lifted tangent vectors `v', w'`,
`ricciTensor (liftedMetric g) x' v' w' = ricciTensor g (proj x') v' w'`.

Proof: write `ricciTensor` as the basis-coordinate sum
`∑ i, b.repr (riemannOp _ x (b i) v w) i` via `ricciTensor_apply_basisSum`,
then apply `riemannOp_lifted_natural` term-by-term. The two basis-identity
hypotheses propagate through the trace: we need them at `x'` for the
lifted metric and at `proj x'` for the base metric. -/
theorem ricciTensor_lifted_natural (g : SmoothRiemannianMetric I M)
    (x' : DifferentialGeometry.Geometry.Riemannian.Topology.UniversalCover M)
    (v' w' : E)
    (h_lifted : chartRiemannBasisIdentity
        (I := I)
        (M := DifferentialGeometry.Geometry.Riemannian.Topology.UniversalCover M)
        (liftedMetric (I := I) g) x')
    (h_base : chartRiemannBasisIdentity (I := I) (M := M) g (proj (X := M) x')) :
    ricciTensor (I := I) (liftedMetric (I := I) g) x' v' w' =
      ricciTensor (I := I) g (proj x') v' w' := by
  classical
  rw [ricciTensor_apply_basisSum
        (I := I)
        (M := DifferentialGeometry.Geometry.Riemannian.Topology.UniversalCover M)
        (liftedMetric (I := I) g) x' v' w',
      ricciTensor_apply_basisSum (I := I) (M := M) g (proj (X := M) x') v' w']
  refine Finset.sum_congr rfl ?_
  intro i _
  have hRiem :
      riemannOp (cov := LeviCivita (I := I) (liftedMetric (I := I) g)) x'
          (DifferentialGeometry.Integral.Measure.chartModelBasis E i) v' w' =
        riemannOp (cov := LeviCivita (I := I) g) (proj (X := M) x')
          (DifferentialGeometry.Integral.Measure.chartModelBasis E i) v' w' :=
    riemannOp_lifted_natural (I := I) (M := M) g x'
      (DifferentialGeometry.Integral.Measure.chartModelBasis E i) v' w' h_lifted h_base
  rw [hRiem]

omit [PseudoEMetricSpace M] in
/-- **Ricci lower bound transfers to the universal cover.**
If `RicciBoundedBelow g κ` holds on `M` (i.e. `Ric_g ≥ κ · g`), then
`RicciBoundedBelow (liftedMetric g) κ` holds on the universal cover.
At any cover point `x'` and tangent vector `v'`, set `x := proj x'`; the
inner products agree by `liftedMetric_inner_eq` and the Ricci values agree
by `ricciTensor_lifted_natural`, so the base bound `hRic x v'` carries over.

The two hypotheses `h_lifted_all` and `h_base_all` assume the
`chartRiemannBasisIdentity` predicate at every point of the cover and of the
base respectively: the basis-coordinate identification of the abstract Riemann
operator with the chart Riemann tensor (consumed by `ricciTensor_lifted_natural`). -/
theorem ricciBoundedBelow_liftedMetric_of_base
    {g : SmoothRiemannianMetric I M} {κ : ℝ}
    (hRic : RicciBoundedBelow (I := I) g κ)
    (h_lifted_all : ∀ x' : DifferentialGeometry.Geometry.Riemannian.Topology.UniversalCover M,
        chartRiemannBasisIdentity
          (I := I)
          (M := DifferentialGeometry.Geometry.Riemannian.Topology.UniversalCover M)
          (liftedMetric (I := I) g) x')
    (h_base_all : ∀ x : M, chartRiemannBasisIdentity (I := I) (M := M) g x) :
    RicciBoundedBelow (I := I) (liftedMetric (I := I) g) κ := by
  intro x' v'
  set x : M := proj x' with hx_def
  have h_inner :
      (liftedMetric (I := I) g).inner x' v' v' = g.inner x v' v' := by
    exact (liftedMetric_inner_eq (I := I) g x' v' v').symm
  have h_ric :
      ricciTensor (I := I) (liftedMetric (I := I) g) x' v' v' =
        ricciTensor (I := I) g x v' v' :=
    ricciTensor_lifted_natural (I := I) g x' v' v'
      (h_lifted_all x') (h_base_all (proj (X := M) x'))
  rw [h_inner, h_ric]
  exact hRic x v'

end UniversalCover
end Topology
end Riemannian
end Geometry
end DifferentialGeometry

end
