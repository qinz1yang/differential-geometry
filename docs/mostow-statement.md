# Native three-dimensional Mostow statement

This is a compiler-checked statement interface, not a proved theorem.
The given homotopy equivalence, common negative normalization, actual Riemannian
volume and original homotopy class are retained. No compactness or orientability
assumption occurs.

The native volume and completeness constructors require sigma compactness.
Hausdorffness prevents pseudo-distance collapse. The metric instances below
come from the supplied smooth metrics; native checks identify their extended
distances with `riemannianEDistOf` definitionally and obtain completeness from
the supplied `RiemannianMetricComplete` hypotheses.

Required imports:

```lean
import DifferentialGeometry.Geometry.Metric.Completeness
import DifferentialGeometry.Geometry.Metric.Distance.Topology
import DifferentialGeometry.Geometry.Curvature.Metric.Defs
import DifferentialGeometry.Analysis.Integration.Measure.Riemannian.Invariance
import Mathlib.Topology.Homotopy.Equiv
import Mathlib.Topology.MetricSpace.Basic
```

With universes `u v`, namespace `DifferentialGeometry`, and the `Manifold`,
`ContDiff` and `ENNReal` notation scopes, the exact target proposition is:

```lean
∀ (M : Type u) (N : Type v)
    [TopologicalSpace M] [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
    [IsManifold (𝓡 3) ∞ M] [T2Space M] [SigmaCompactSpace M] [ConnectedSpace M]
    [TopologicalSpace N] [ChartedSpace (EuclideanSpace ℝ (Fin 3)) N]
    [IsManifold (𝓡 3) ∞ N] [T2Space N] [SigmaCompactSpace N] [ConnectedSpace N],
    ∀ (g : SmoothRiemannianMetric (𝓡 3) M)
      (h : SmoothRiemannianMetric (𝓡 3) N) (κ : ℝ)
      (u : ContinuousMap.HomotopyEquiv M N),
      κ < 0 →
      RiemannianMetricComplete g → RiemannianMetricComplete h →
      Integral.Measure.riemannianVolumeMeasure (𝓡 3) M g Set.univ < (⊤ : ℝ≥0∞) →
      Integral.Measure.riemannianVolumeMeasure (𝓡 3) N h Set.univ < (⊤ : ℝ≥0∞) →
      (∀ (p : M) (v w : TangentSpace (𝓡 3) p),
        Geometry.Curvature.metricRm04StandardAt g p v w w v =
          κ * (g.inner p v v * g.inner p w w - g.inner p v w * g.inner p v w)) →
      (∀ (p : N) (v w : TangentSpace (𝓡 3) p),
        Geometry.Curvature.metricRm04StandardAt h p v w w v =
          κ * (h.inner p v v * h.inner p w w - h.inner p v w * h.inner p v w)) →
      letI : TopologicalSpace.MetrizableSpace M := Manifold.metrizableSpace (𝓡 3) M
      letI : TopologicalSpace.MetrizableSpace N := Manifold.metrizableSpace (𝓡 3) N
      letI : PseudoMetricSpace M := g.toPseudoMetricSpace
      letI : MetricSpace M := MetricSpace.ofT0PseudoMetricSpace M
      letI : PseudoMetricSpace N := h.toPseudoMetricSpace
      letI : MetricSpace N := MetricSpace.ofT0PseudoMetricSpace N
      ∃! a : M ≃ᵢ N, ContinuousMap.Homotopic u.toFun (a : C(M, N)) : Prop
```

The audited native volume, curvature, distance, completeness and scaling APIs
have transitive axiom closures contained in `propext`, `Classical.choice` and
`Quot.sound`. This checks the vocabulary and metric compatibility only.
The proof of the displayed proposition remains open.
