import DifferentialGeometry.Geometry.Geodesic.Naturality.OpenSubtype
import DifferentialGeometry.Geometry.Connection.ParallelTransport.Derivative.CovariantDerivativeAlong









open Bundle Manifold DifferentialGeometry Set Filter
open DifferentialGeometry.Geometry.Riemannian
open AlongCurve CovariantDerivativeAlong Geodesic
open scoped Bundle Manifold ContDiff Topology

namespace DifferentialGeometry.Geometry

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

omit [FiniteDimensional ℝ E] [I.Boundaryless] in
private theorem tangent_trivialization_open
    (U : TopologicalSpace.Opens M) (a x : U)
    (hx : (x : M) ∈ (chartAt H (a : M)).source) :
    (trivializationAt E (TangentSpace I (M := U)) a).continuousLinearMapAt ℝ x =
      (trivializationAt E (TangentSpace I (M := M)) (a : M)).continuousLinearMapAt
        ℝ (x : M) := by
  have hxU : x ∈ (chartAt H a).source := by
    rw [TopologicalSpace.Opens.chartAt_eq, OpenPartialHomeomorph.subtypeRestr_source]
    exact hx
  rw [TangentBundle.continuousLinearMapAt_trivializationAt_eq_core hxU,
    TangentBundle.continuousLinearMapAt_trivializationAt_eq_core hx,
    tangentCoordChange_opens x a x (mem_chart_source H (x : M))]

omit [FiniteDimensional ℝ E] [I.Boundaryless] in
private theorem tangent_symm_trivialization_open
    (U : TopologicalSpace.Opens M) (a : U) :
    (trivializationAt E (TangentSpace I (M := U)) a).symmL ℝ a =
      (trivializationAt E (TangentSpace I (M := M)) (a : M)).symmL ℝ (a : M) := by
  rw [TangentBundle.symmL_trivializationAt_eq_core (mem_chart_source H a),
    TangentBundle.symmL_trivializationAt_eq_core (mem_chart_source H (a : M)),
    tangentCoordChange_opens a a a (mem_chart_source H (a : M))]




theorem covDerivAlong_restrictOpen
    (g : SmoothRiemannianMetric I M) (U : TopologicalSpace.Opens M) [T2Space U]
    (γ : ℝ → U) (V : ∀ t, TangentSpace I (γ t)) (t : ℝ)
    (hγ : ContinuousAt γ t) :
    covDerivAlong (g.restrictOpen U) γ V t =
      covDerivAlong g (Subtype.val ∘ γ) (fun s => V s) t := by
  have heq : chartRepAt (I := I) γ V t =ᶠ[𝓝 t]
      chartRepAt (I := I) (Subtype.val ∘ γ) (fun s => V s) t := by
    have hn : ∀ᶠ s in 𝓝 t, (γ s : M) ∈ (chartAt H (γ t : M)).source :=
      (continuous_subtype_val.continuousAt.comp hγ).eventually
        ((chartAt H (γ t : M)).open_source.mem_nhds (mem_chart_source H (γ t : M)))
    filter_upwards [hn] with s hs
    exact congrArg (fun L => L (V s)) (tangent_trivialization_open U (γ t) (γ s) hs)
  unfold covDerivAlong
  erw [tangent_symm_trivialization_open]
  congr 1
  unfold chartCovDerivAlong
  erw [heq.deriv_eq, heq.eq_of_nhds]
  exact congrArg (fun v => _ + v)
    (contr_open g U (γ t) (deriv (chartCurve (I := I) (γ t) γ) t)
      (chartRepAt (I := I) (Subtype.val ∘ γ) (fun s => V s) t t))

end DifferentialGeometry.Geometry
