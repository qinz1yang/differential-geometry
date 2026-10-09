import DifferentialGeometry.Geometry.Hyperbolic.Isometry
import DifferentialGeometry.Geometry.Metric.Distance.Differential

noncomputable section
open scoped Manifold ContDiff Topology

namespace DifferentialGeometry.Geometry.Hyperbolic

universe u v

variable {M : Type u} {N : Type v}
  [TopologicalSpace M] [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
  [IsManifold (𝓡 3) ∞ M] [T2Space M] [SigmaCompactSpace M] [ConnectedSpace M]
  [TopologicalSpace N] [ChartedSpace (EuclideanSpace ℝ (Fin 3)) N]
  [IsManifold (𝓡 3) ∞ N] [T2Space N] [SigmaCompactSpace N] [ConnectedSpace N]

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
theorem contMDiff_isometryEquiv_of_constant_negative_curvature
    (g : SmoothRiemannianMetric (𝓡 3) M) (h : SmoothRiemannianMetric (𝓡 3) N)
    (κ : ℝ) (hκ : κ < 0) (hg : RiemannianMetricComplete g)
    (hh : RiemannianMetricComplete h)
    (hsecg : ∀ (p : M) (v w : TangentSpace (𝓡 3) p),
      Curvature.metricRm04StandardAt g p v w w v =
        κ * (g.inner p v v * g.inner p w w - g.inner p v w * g.inner p v w))
    (hsech : ∀ (p : N) (v w : TangentSpace (𝓡 3) p),
      Curvature.metricRm04StandardAt h p v w w v =
        κ * (h.inner p v v * h.inner p w w - h.inner p v w * h.inner p v w)) :
    letI : TopologicalSpace.MetrizableSpace M := Manifold.metrizableSpace (𝓡 3) M
    letI : TopologicalSpace.MetrizableSpace N := Manifold.metrizableSpace (𝓡 3) N
    letI : PseudoMetricSpace M := g.toPseudoMetricSpace
    letI : MetricSpace M := MetricSpace.ofT0PseudoMetricSpace M
    letI : PseudoMetricSpace N := h.toPseudoMetricSpace
    letI : MetricSpace N := MetricSpace.ofT0PseudoMetricSpace N
    ∀ a : M ≃ᵢ N, ContMDiff (𝓡 3) (𝓡 3) ∞ a := by
  exact contMDiff_isometryEquiv g h κ hκ hg hh hsecg hsech

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
theorem exists_diffeomorph_eq_isometryEquiv_of_constant_negative_curvature
    (g : SmoothRiemannianMetric (𝓡 3) M) (h : SmoothRiemannianMetric (𝓡 3) N)
    (κ : ℝ) (hκ : κ < 0) (hg : RiemannianMetricComplete g)
    (hh : RiemannianMetricComplete h)
    (hsecg : ∀ (p : M) (v w : TangentSpace (𝓡 3) p),
      Curvature.metricRm04StandardAt g p v w w v =
        κ * (g.inner p v v * g.inner p w w - g.inner p v w * g.inner p v w))
    (hsech : ∀ (p : N) (v w : TangentSpace (𝓡 3) p),
      Curvature.metricRm04StandardAt h p v w w v =
        κ * (h.inner p v v * h.inner p w w - h.inner p v w * h.inner p v w)) :
    letI : TopologicalSpace.MetrizableSpace M := Manifold.metrizableSpace (𝓡 3) M
    letI : TopologicalSpace.MetrizableSpace N := Manifold.metrizableSpace (𝓡 3) N
    letI : PseudoMetricSpace M := g.toPseudoMetricSpace
    letI : MetricSpace M := MetricSpace.ofT0PseudoMetricSpace M
    letI : PseudoMetricSpace N := h.toPseudoMetricSpace
    letI : MetricSpace N := MetricSpace.ofT0PseudoMetricSpace N
    ∀ a : M ≃ᵢ N, ∃ f : M ≃ₘ⟮𝓡 3, 𝓡 3⟯ N,
      (∀ x, f x = a x) ∧
      ∀ (p : M) (v w : TangentSpace (𝓡 3) p),
        h.inner (f p) (mfderiv (𝓡 3) (𝓡 3) f p v) (mfderiv (𝓡 3) (𝓡 3) f p w) =
          g.inner p v w := by
  let _ : TopologicalSpace.MetrizableSpace M := Manifold.metrizableSpace (𝓡 3) M
  let _ : TopologicalSpace.MetrizableSpace N := Manifold.metrizableSpace (𝓡 3) N
  let _ : PseudoMetricSpace M := g.toPseudoMetricSpace
  let _ : MetricSpace M := MetricSpace.ofT0PseudoMetricSpace M
  let _ : PseudoMetricSpace N := h.toPseudoMetricSpace
  let _ : MetricSpace N := MetricSpace.ofT0PseudoMetricSpace N
  intro a
  let f : M ≃ₘ⟮𝓡 3, 𝓡 3⟯ N := {
    toEquiv := a.toEquiv
    contMDiff_toFun :=
      contMDiff_isometryEquiv_of_constant_negative_curvature g h κ hκ hg hh hsecg hsech a
    contMDiff_invFun :=
      contMDiff_isometryEquiv_of_constant_negative_curvature h g κ hκ hh hg hsech hsecg a.symm }
  refine ⟨f, fun _ => rfl, ?_⟩
  intro p v w
  have hd : ∀ᶠ x in 𝓝 p, (riemannianEDistOf h (f x) (f p)).toReal =
      1 * (riemannianEDistOf g x p).toReal := by
    apply Filter.Eventually.of_forall
    intro x
    rw [one_mul]
    exact congrArg ENNReal.toReal (a.edist_eq x p)
  simpa only [one_pow, one_mul] using
    Riemannian.inner_mfderiv_eq_mul_of_eventually_riemannian_distance_eq g h f p 1
      (f.contMDiff.mdifferentiable (by decide) p) hd v w

end DifferentialGeometry.Geometry.Hyperbolic
