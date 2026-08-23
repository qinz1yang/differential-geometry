import DifferentialGeometry.Analysis.Parabolic.MaximumPrinciple.ScalarStrong
import DifferentialGeometry.Geometry.Operator.MetricFamilyRegularity

set_option autoImplicit false

namespace DifferentialGeometry.Analysis.Parabolic

noncomputable section

open Bundle Set
open DifferentialGeometry.Geometry.Connection
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Geometry.Operator
open scoped Manifold ContDiff Topology

universe u uE uH

variable {E : Type uE} [NormedAddCommGroup E] [NormedSpace Real E]
variable [FiniteDimensional Real E]
variable {H : Type uH} [TopologicalSpace H]
variable {I : ModelWithCorners Real E H}
variable {M : Type u} [TopologicalSpace M] [ChartedSpace H M]
variable [IsManifold I ∞ M]

theorem scalar_strong_maximum_principle_time_dependent_metric_of_metricFamilySmoothOn
    [I.Boundaryless] [CompleteSpace E] [SigmaCompactSpace M]
    [T2Space M] [CompactSpace M] [ConnectedSpace M]
    [VectorBundle Real E (TangentSpace I : M → Type _)]
    (G : MetricConnectionFamily (I := I) (M := M) Real)
    {T : Real} (hT : 0 < T)
    {D : RealTimeInterval}
    (hG : MetricFamilySmoothOn (I := I) (M := M) D G.metric)
    (hslab : Set.Icc 0 T ⊆ D.regular)
    (hconn : ∀ t ∈ Set.Icc 0 T,
      G.connection t = LeviCivita (I := I) (G.metric t))
    (u : Real → M → Real)
    (hu_cont : ContinuousOn (fun p : Real × M => u p.1 p.2)
      (spacetimeSlab (M := M) T))
    (hu_nonneg : ∀ t ∈ Set.Icc 0 T, ∀ x : M, 0 ≤ u t x)
    (hu_time : ∀ t ∈ Set.Icc 0 T, 0 < t → ∀ x : M,
      DifferentiableWithinAt Real (fun s => u s x) (Set.Icc 0 T) t)
    (hu_mdiff : ∀ t ∈ Set.Icc 0 T, 0 < t → ∀ x : M,
      MDifferentiableAt I (modelWithCornersSelf Real Real) (u t) x)
    (hu_grad : ∀ t ∈ Set.Icc 0 T, 0 < t → ∀ x : M,
      MDiffAt (T% fun y : M =>
        gradientFun (I := I) (G.metric t) (u t) y) x)
    (hu_super : ∀ t ∈ Set.Icc 0 T, 0 < t → ∀ x : M,
      0 ≤ derivWithin (fun s => u s x) (Set.Icc 0 T) t -
        laplacianAt (I := I) G t (u t) x)
    {y : M} (hy : u T y = 0) :
    ∀ t ∈ Set.Icc 0 T, ∀ x : M, u t x = 0 := by
  exact scalar_strong_maximum_principle_time_dependent_metric (I := I)
    G hT
    (fun rho hrho => G.gradient_norm_sq_continuousOn hG hslab hrho)
    (fun rho hrho => G.laplacianAt_continuousOn
      hG hslab (uniqueDiffOn_Icc hT) hconn hrho)
    u hu_cont hu_nonneg hu_time hu_mdiff hu_grad hu_super hy

theorem scalar_strong_maximum_principle_time_dependent_metric_positive_of_metricFamilySmoothOn
    [I.Boundaryless] [CompleteSpace E] [SigmaCompactSpace M]
    [T2Space M] [CompactSpace M] [ConnectedSpace M]
    [VectorBundle Real E (TangentSpace I : M → Type _)]
    (G : MetricConnectionFamily (I := I) (M := M) Real)
    {T : Real} (hT : 0 < T)
    {D : RealTimeInterval}
    (hG : MetricFamilySmoothOn (I := I) (M := M) D G.metric)
    (hslab : Set.Icc 0 T ⊆ D.regular)
    (hconn : ∀ t ∈ Set.Icc 0 T,
      G.connection t = LeviCivita (I := I) (G.metric t))
    (u : Real → M → Real)
    (hu_cont : ContinuousOn (fun p : Real × M => u p.1 p.2)
      (spacetimeSlab (M := M) T))
    (hu_nonneg : ∀ t ∈ Set.Icc 0 T, ∀ x : M, 0 ≤ u t x)
    (hu_time : ∀ t ∈ Set.Icc 0 T, 0 < t → ∀ x : M,
      DifferentiableWithinAt Real (fun s => u s x) (Set.Icc 0 T) t)
    (hu_mdiff : ∀ t ∈ Set.Icc 0 T, 0 < t → ∀ x : M,
      MDifferentiableAt I (modelWithCornersSelf Real Real) (u t) x)
    (hu_grad : ∀ t ∈ Set.Icc 0 T, 0 < t → ∀ x : M,
      MDiffAt (T% fun y : M =>
        gradientFun (I := I) (G.metric t) (u t) y) x)
    (hu_super : ∀ t ∈ Set.Icc 0 T, 0 < t → ∀ x : M,
      0 ≤ derivWithin (fun s => u s x) (Set.Icc 0 T) t -
        laplacianAt (I := I) G t (u t) x)
    {t : Real} (ht : t ∈ Set.Icc 0 T) {x : M} (hx : 0 < u t x)
    (y : M) :
    0 < u T y := by
  exact scalar_strong_maximum_principle_time_dependent_metric_positive (I := I)
    G hT
    (fun rho hrho => G.gradient_norm_sq_continuousOn hG hslab hrho)
    (fun rho hrho => G.laplacianAt_continuousOn
      hG hslab (uniqueDiffOn_Icc hT) hconn hrho)
    u hu_cont hu_nonneg hu_time hu_mdiff hu_grad hu_super ht hx y

theorem scalar_strong_maximum_principle_time_dependent_metric_with_potential_of_metricFamilySmoothOn
    [I.Boundaryless] [CompleteSpace E] [SigmaCompactSpace M]
    [T2Space M] [CompactSpace M] [ConnectedSpace M]
    [VectorBundle Real E (TangentSpace I : M → Type _)]
    (G : MetricConnectionFamily (I := I) (M := M) Real)
    {T : Real} (hT : 0 < T)
    {D : RealTimeInterval}
    (hG : MetricFamilySmoothOn (I := I) (M := M) D G.metric)
    (hslab : Set.Icc 0 T ⊆ D.regular)
    (hconn : ∀ t ∈ Set.Icc 0 T,
      G.connection t = LeviCivita (I := I) (G.metric t))
    (V : Real → M → Real) (L : Real)
    (u : Real → M → Real)
    (hu_cont : ContinuousOn (fun p : Real × M => u p.1 p.2)
      (spacetimeSlab (M := M) T))
    (hu_nonneg : ∀ t ∈ Set.Icc 0 T, ∀ x : M, 0 ≤ u t x)
    (hu_time : ∀ t ∈ Set.Icc 0 T, 0 < t → ∀ x : M,
      DifferentiableWithinAt Real (fun s => u s x) (Set.Icc 0 T) t)
    (hu_mdiff : ∀ t ∈ Set.Icc 0 T, 0 < t → ∀ x : M,
      MDifferentiableAt I (modelWithCornersSelf Real Real) (u t) x)
    (hu_grad : ∀ t ∈ Set.Icc 0 T, 0 < t → ∀ x : M,
      MDiffAt (T% fun y : M =>
        gradientFun (I := I) (G.metric t) (u t) y) x)
    (hu_super : ∀ t ∈ Set.Icc 0 T, 0 < t → ∀ x : M,
      0 ≤ derivWithin (fun s => u s x) (Set.Icc 0 T) t -
        laplacianAt (I := I) G t (u t) x - V t x * u t x)
    (hV : ∀ t ∈ Set.Icc 0 T, ∀ x : M, L ≤ V t x)
    {y : M} (hy : u T y = 0) :
    ∀ t ∈ Set.Icc 0 T, ∀ x : M, u t x = 0 := by
  exact scalar_strong_maximum_principle_time_dependent_metric_with_potential
    (I := I) G hT
    (fun rho hrho => G.gradient_norm_sq_continuousOn hG hslab hrho)
    (fun rho hrho => G.laplacianAt_continuousOn
      hG hslab (uniqueDiffOn_Icc hT) hconn hrho)
    V L u hu_cont hu_nonneg hu_time hu_mdiff hu_grad hu_super hV hy

theorem scalar_strong_maximum_principle_time_dependent_metric_with_potential_positive_of_metricFamilySmoothOn
    [I.Boundaryless] [CompleteSpace E] [SigmaCompactSpace M]
    [T2Space M] [CompactSpace M] [ConnectedSpace M]
    [VectorBundle Real E (TangentSpace I : M → Type _)]
    (G : MetricConnectionFamily (I := I) (M := M) Real)
    {T : Real} (hT : 0 < T)
    {D : RealTimeInterval}
    (hG : MetricFamilySmoothOn (I := I) (M := M) D G.metric)
    (hslab : Set.Icc 0 T ⊆ D.regular)
    (hconn : ∀ t ∈ Set.Icc 0 T,
      G.connection t = LeviCivita (I := I) (G.metric t))
    (V : Real → M → Real) (L : Real)
    (u : Real → M → Real)
    (hu_cont : ContinuousOn (fun p : Real × M => u p.1 p.2)
      (spacetimeSlab (M := M) T))
    (hu_nonneg : ∀ t ∈ Set.Icc 0 T, ∀ x : M, 0 ≤ u t x)
    (hu_time : ∀ t ∈ Set.Icc 0 T, 0 < t → ∀ x : M,
      DifferentiableWithinAt Real (fun s => u s x) (Set.Icc 0 T) t)
    (hu_mdiff : ∀ t ∈ Set.Icc 0 T, 0 < t → ∀ x : M,
      MDifferentiableAt I (modelWithCornersSelf Real Real) (u t) x)
    (hu_grad : ∀ t ∈ Set.Icc 0 T, 0 < t → ∀ x : M,
      MDiffAt (T% fun y : M =>
        gradientFun (I := I) (G.metric t) (u t) y) x)
    (hu_super : ∀ t ∈ Set.Icc 0 T, 0 < t → ∀ x : M,
      0 ≤ derivWithin (fun s => u s x) (Set.Icc 0 T) t -
        laplacianAt (I := I) G t (u t) x - V t x * u t x)
    (hV : ∀ t ∈ Set.Icc 0 T, ∀ x : M, L ≤ V t x)
    {t : Real} (ht : t ∈ Set.Icc 0 T) {x : M} (hx : 0 < u t x)
    (y : M) :
    0 < u T y := by
  exact scalar_strong_maximum_principle_time_dependent_metric_with_potential_positive
    (I := I) G hT
    (fun rho hrho => G.gradient_norm_sq_continuousOn hG hslab hrho)
    (fun rho hrho => G.laplacianAt_continuousOn
      hG hslab (uniqueDiffOn_Icc hT) hconn hrho)
    V L u hu_cont hu_nonneg hu_time hu_mdiff hu_grad hu_super hV ht hx y

theorem scalar_strong_maximum_principle_time_dependent_metric_with_drift_and_potential_of_metricFamilySmoothOn
    [I.Boundaryless] [CompleteSpace E] [SigmaCompactSpace M]
    [T2Space M] [CompactSpace M] [ConnectedSpace M]
    [VectorBundle Real E (TangentSpace I : M → Type _)]
    (G : MetricConnectionFamily (I := I) (M := M) Real)
    {T : Real} (hT : 0 < T)
    {D : RealTimeInterval}
    (hG : MetricFamilySmoothOn (I := I) (M := M) D G.metric)
    (hslab : Set.Icc 0 T ⊆ D.regular)
    (hconn : ∀ t ∈ Set.Icc 0 T,
      G.connection t = LeviCivita (I := I) (G.metric t))
    (X : Real → (x : M) → TangentSpace I x)
    (hdrift : ∀ (rho : M → Real),
      ContMDiff I 𝓘(Real, Real) ∞ rho →
      ContinuousOn (fun p : Real × M =>
        driftTerm (I := I) G p.1 (X p.1) rho p.2)
        (spacetimeSlab (M := M) T))
    (V : Real → M → Real) (L : Real)
    (u : Real → M → Real)
    (hu_cont : ContinuousOn (fun p : Real × M => u p.1 p.2)
      (spacetimeSlab (M := M) T))
    (hu_nonneg : ∀ t ∈ Set.Icc 0 T, ∀ x : M, 0 ≤ u t x)
    (hu_time : ∀ t ∈ Set.Icc 0 T, 0 < t → ∀ x : M,
      DifferentiableWithinAt Real (fun s => u s x) (Set.Icc 0 T) t)
    (hu_mdiff : ∀ t ∈ Set.Icc 0 T, 0 < t → ∀ x : M,
      MDifferentiableAt I 𝓘(Real, Real) (u t) x)
    (hu_grad : ∀ t ∈ Set.Icc 0 T, 0 < t → ∀ x : M,
      MDiffAt (T% fun y : M =>
        gradientFun (I := I) (G.metric t) (u t) y) x)
    (hu_super : ∀ t ∈ Set.Icc 0 T, 0 < t → ∀ x : M,
      0 ≤ parabolicOperatorWithDrift (I := I) G T X u t x -
        V t x * u t x)
    (hV : ∀ t ∈ Set.Icc 0 T, ∀ x : M, L ≤ V t x)
    {y : M} (hy : u T y = 0) :
    ∀ t ∈ Set.Icc 0 T, ∀ x : M, u t x = 0 := by
  exact
    scalar_strong_maximum_principle_time_dependent_metric_with_drift_and_potential
      (I := I) G hT X
        (fun rho hrho => G.gradient_norm_sq_continuousOn hG hslab hrho)
        (fun rho hrho => G.heatOperatorWithDrift_continuousOn
          hG hslab (uniqueDiffOn_Icc hT) hconn X hrho (hdrift rho hrho))
        V L u hu_cont hu_nonneg hu_time hu_mdiff hu_grad hu_super hV hy

theorem scalar_strong_maximum_principle_time_dependent_metric_with_drift_and_potential_positive_of_metricFamilySmoothOn
    [I.Boundaryless] [CompleteSpace E] [SigmaCompactSpace M]
    [T2Space M] [CompactSpace M] [ConnectedSpace M]
    [VectorBundle Real E (TangentSpace I : M → Type _)]
    (G : MetricConnectionFamily (I := I) (M := M) Real)
    {T : Real} (hT : 0 < T)
    {D : RealTimeInterval}
    (hG : MetricFamilySmoothOn (I := I) (M := M) D G.metric)
    (hslab : Set.Icc 0 T ⊆ D.regular)
    (hconn : ∀ t ∈ Set.Icc 0 T,
      G.connection t = LeviCivita (I := I) (G.metric t))
    (X : Real → (x : M) → TangentSpace I x)
    (hdrift : ∀ (rho : M → Real),
      ContMDiff I 𝓘(Real, Real) ∞ rho →
      ContinuousOn (fun p : Real × M =>
        driftTerm (I := I) G p.1 (X p.1) rho p.2)
        (spacetimeSlab (M := M) T))
    (V : Real → M → Real) (L : Real)
    (u : Real → M → Real)
    (hu_cont : ContinuousOn (fun p : Real × M => u p.1 p.2)
      (spacetimeSlab (M := M) T))
    (hu_nonneg : ∀ t ∈ Set.Icc 0 T, ∀ x : M, 0 ≤ u t x)
    (hu_time : ∀ t ∈ Set.Icc 0 T, 0 < t → ∀ x : M,
      DifferentiableWithinAt Real (fun s => u s x) (Set.Icc 0 T) t)
    (hu_mdiff : ∀ t ∈ Set.Icc 0 T, 0 < t → ∀ x : M,
      MDifferentiableAt I 𝓘(Real, Real) (u t) x)
    (hu_grad : ∀ t ∈ Set.Icc 0 T, 0 < t → ∀ x : M,
      MDiffAt (T% fun y : M =>
        gradientFun (I := I) (G.metric t) (u t) y) x)
    (hu_super : ∀ t ∈ Set.Icc 0 T, 0 < t → ∀ x : M,
      0 ≤ parabolicOperatorWithDrift (I := I) G T X u t x -
        V t x * u t x)
    (hV : ∀ t ∈ Set.Icc 0 T, ∀ x : M, L ≤ V t x)
    {t : Real} (ht : t ∈ Set.Icc 0 T) {x : M} (hx : 0 < u t x)
    (y : M) :
    0 < u T y := by
  exact
    scalar_strong_maximum_principle_time_dependent_metric_with_drift_and_potential_positive
      (I := I) G hT X
        (fun rho hrho => G.gradient_norm_sq_continuousOn hG hslab hrho)
        (fun rho hrho => G.heatOperatorWithDrift_continuousOn
          hG hslab (uniqueDiffOn_Icc hT) hconn X hrho (hdrift rho hrho))
        V L u hu_cont hu_nonneg hu_time hu_mdiff hu_grad hu_super hV ht hx y

theorem scalar_strong_maximum_principle_time_dependent_metric_with_drift_of_metricFamilySmoothOn
    [I.Boundaryless] [CompleteSpace E] [SigmaCompactSpace M]
    [T2Space M] [CompactSpace M] [ConnectedSpace M]
    [VectorBundle Real E (TangentSpace I : M → Type _)]
    (G : MetricConnectionFamily (I := I) (M := M) Real)
    {T : Real} (hT : 0 < T)
    {D : RealTimeInterval}
    (hG : MetricFamilySmoothOn (I := I) (M := M) D G.metric)
    (hslab : Set.Icc 0 T ⊆ D.regular)
    (hconn : ∀ t ∈ Set.Icc 0 T,
      G.connection t = LeviCivita (I := I) (G.metric t))
    (X : Real → (x : M) → TangentSpace I x)
    (hdrift : ∀ (rho : M → Real),
      ContMDiff I 𝓘(Real, Real) ∞ rho →
      ContinuousOn (fun p : Real × M =>
        driftTerm (I := I) G p.1 (X p.1) rho p.2)
        (spacetimeSlab (M := M) T))
    (u : Real → M → Real)
    (hu_cont : ContinuousOn (fun p : Real × M => u p.1 p.2)
      (spacetimeSlab (M := M) T))
    (hu_nonneg : ∀ t ∈ Set.Icc 0 T, ∀ x : M, 0 ≤ u t x)
    (hu_time : ∀ t ∈ Set.Icc 0 T, 0 < t → ∀ x : M,
      DifferentiableWithinAt Real (fun s => u s x) (Set.Icc 0 T) t)
    (hu_mdiff : ∀ t ∈ Set.Icc 0 T, 0 < t → ∀ x : M,
      MDifferentiableAt I 𝓘(Real, Real) (u t) x)
    (hu_grad : ∀ t ∈ Set.Icc 0 T, 0 < t → ∀ x : M,
      MDiffAt (T% fun y : M =>
        gradientFun (I := I) (G.metric t) (u t) y) x)
    (hu_super : ∀ t ∈ Set.Icc 0 T, 0 < t → ∀ x : M,
      0 ≤ parabolicOperatorWithDrift (I := I) G T X u t x)
    {y : M} (hy : u T y = 0) :
    ∀ t ∈ Set.Icc 0 T, ∀ x : M, u t x = 0 := by
  apply
    scalar_strong_maximum_principle_time_dependent_metric_with_drift_and_potential_of_metricFamilySmoothOn
      (I := I) G hT hG hslab hconn X hdrift (fun _ _ => 0) 0 u
        hu_cont hu_nonneg hu_time hu_mdiff hu_grad
  · simpa using hu_super
  · intro t ht x
    exact le_rfl
  · exact hy

theorem scalar_strong_maximum_principle_time_dependent_metric_with_drift_positive_of_metricFamilySmoothOn
    [I.Boundaryless] [CompleteSpace E] [SigmaCompactSpace M]
    [T2Space M] [CompactSpace M] [ConnectedSpace M]
    [VectorBundle Real E (TangentSpace I : M → Type _)]
    (G : MetricConnectionFamily (I := I) (M := M) Real)
    {T : Real} (hT : 0 < T)
    {D : RealTimeInterval}
    (hG : MetricFamilySmoothOn (I := I) (M := M) D G.metric)
    (hslab : Set.Icc 0 T ⊆ D.regular)
    (hconn : ∀ t ∈ Set.Icc 0 T,
      G.connection t = LeviCivita (I := I) (G.metric t))
    (X : Real → (x : M) → TangentSpace I x)
    (hdrift : ∀ (rho : M → Real),
      ContMDiff I 𝓘(Real, Real) ∞ rho →
      ContinuousOn (fun p : Real × M =>
        driftTerm (I := I) G p.1 (X p.1) rho p.2)
        (spacetimeSlab (M := M) T))
    (u : Real → M → Real)
    (hu_cont : ContinuousOn (fun p : Real × M => u p.1 p.2)
      (spacetimeSlab (M := M) T))
    (hu_nonneg : ∀ t ∈ Set.Icc 0 T, ∀ x : M, 0 ≤ u t x)
    (hu_time : ∀ t ∈ Set.Icc 0 T, 0 < t → ∀ x : M,
      DifferentiableWithinAt Real (fun s => u s x) (Set.Icc 0 T) t)
    (hu_mdiff : ∀ t ∈ Set.Icc 0 T, 0 < t → ∀ x : M,
      MDifferentiableAt I 𝓘(Real, Real) (u t) x)
    (hu_grad : ∀ t ∈ Set.Icc 0 T, 0 < t → ∀ x : M,
      MDiffAt (T% fun y : M =>
        gradientFun (I := I) (G.metric t) (u t) y) x)
    (hu_super : ∀ t ∈ Set.Icc 0 T, 0 < t → ∀ x : M,
      0 ≤ parabolicOperatorWithDrift (I := I) G T X u t x)
    {t : Real} (ht : t ∈ Set.Icc 0 T) {x : M} (hx : 0 < u t x)
    (y : M) :
    0 < u T y := by
  apply
    scalar_strong_maximum_principle_time_dependent_metric_with_drift_and_potential_positive_of_metricFamilySmoothOn
      (I := I) G hT hG hslab hconn X hdrift (fun _ _ => 0) 0 u
        hu_cont hu_nonneg hu_time hu_mdiff hu_grad
  · simpa using hu_super
  · intro t ht x
    exact le_rfl
  · exact ht
  · exact hx

end

end DifferentialGeometry.Analysis.Parabolic
