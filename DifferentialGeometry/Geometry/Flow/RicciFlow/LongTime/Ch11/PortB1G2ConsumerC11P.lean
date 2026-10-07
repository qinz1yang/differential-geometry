import DifferentialGeometry.Analysis.Calculus.Cutoff.SingularBarrier
import DifferentialGeometry.Geometry.Comparison.Variation.Field.FiniteJointFrames
import DifferentialGeometry.Geometry.Flow.RicciFlow.Estimates.Distance.FixedEndpoints
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.LGeometry.Action.Regularized.FiniteJointAction
import DifferentialGeometry.Topology.Manifold.InverseFunctionTheorem.FiniteParameterGraph
import DifferentialGeometry.Topology.MetricSpace.TruncatedDistanceLevel

set_option autoImplicit false

/-!
# S-CH11-PORT-B1 G2 consumer (`_C11P`)

Type-checks the main theorems of the verbatim-ported astra B1 modules of group G2
(analysis / variation / Perelman `LGeometry` base).  Own file, no new declarations.
-/

open scoped ENNReal NNReal

/-- Consumer: the truncated distance level is continuous. -/
example {X : Type*} [PseudoEMetricSpace X] (p : X) (N : ℝ≥0) :
    Continuous (fun x => (min (edist x p) (N : ℝ≥0∞)).toReal) :=
  (EMetric.lipschitzWith_truncated_edist_level p N).continuous

/-- Consumer: the singular-barrier constant exists for every `D ≥ 0`. -/
example (D : ℝ) (hD : 0 ≤ D) :
    type_of% (DifferentialGeometry.Analysis.SingularBarrier.exists_constant D hD) :=
  DifferentialGeometry.Analysis.SingularBarrier.exists_constant D hD

open DifferentialGeometry.PDE.RicciFlow DifferentialGeometry.PDE.RicciFlow.Perelman
  DifferentialGeometry.Geometry.Riemannian.Variation DifferentialGeometry.Coordinates

example : type_of% @contDiffOn_finiteJointAction := @contDiffOn_finiteJointAction

example : type_of% @exists_finiteJointAction_endpoint_branch :=
  @exists_finiteJointAction_endpoint_branch

example : type_of% @exists_compatible_joint_variation_of_fields :=
  @exists_compatible_joint_variation_of_fields

example : type_of% @riemannianEDistOf_le_add_of_endpoint_ricci_on_interval :=
  @riemannianEDistOf_le_add_of_endpoint_ricci_on_interval

example : type_of% @isLocalDiffeomorphAt_parameter_graph_of_slice_bijective_two :=
  @isLocalDiffeomorphAt_parameter_graph_of_slice_bijective_two
