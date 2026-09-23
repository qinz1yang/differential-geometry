import DifferentialGeometry.Geometry.Flow.RicciFlow.Estimates.LocalDistanceComparison
import DifferentialGeometry.Geometry.Metric.LocalPullDistance

noncomputable section

open Set Manifold
open DifferentialGeometry.Geometry.Curvature DifferentialGeometry.Tensor0SBundle
open scoped Manifold ContDiff Topology ENNReal NNReal

namespace DifferentialGeometry.PDE.RicciFlow

variable {E F H H' M N : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
  [TopologicalSpace H] [TopologicalSpace H']
  {I : ModelWithCorners ℝ E H} [I.Boundaryless] {J : ModelWithCorners ℝ F H'}
  [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [T2Space M]
  [TopologicalSpace N] [ChartedSpace H' N] [IsManifold J ∞ N] [T2Space N]
  {D : RealTimeInterval}

omit [FiniteDimensional ℝ F] [T2Space N] in
theorem isCompact_intrinsic_closedBall_of_localPullMetric_terminal
    (g : SmoothRiemannianMetric J N) (f : M → N)
    (hf : IsLocalDiffeomorph I J ∞ f) (hinj : Function.Injective f)
    (S : SolutionOn (I := I) (M := M) D) (hS : IsSolutionOn S)
    {a b C t : ℝ} (hcarrier : Icc a b ⊆ D.carrier)
    (hregular : Ioo a b ⊆ D.regular)
    (hRm : ∀ u ∈ Icc a b, ∀ x : M,
      normSq0S (I := I) (S.base.metric u) x 4 (S.base.rm04 u x) ≤ C)
    (ht : t ∈ Icc a b) (hterminal : S.base.metric b = localPullMetric g f hf)
    (p : M) {r R : ℝ≥0}
    (hcompact : IsCompact {x : N | riemannianEDistOf g (f p) x ≤ R})
    (hball : {x : N | riemannianEDistOf g (f p) x ≤ R} ⊆ range f)
    (hfit : ENNReal.ofReal (Real.exp
      ((Module.finrank ℝ E : ℝ) ^ 2 * Real.sqrt C * |t - b|)) * (r : ℝ≥0∞) ≤ R) :
    IsCompact {x : M | riemannianEDistOf (S.base.metric t) p x ≤ r} := by
  have hemb : _root_.Topology.IsOpenEmbedding f :=
    .of_continuous_injective_isOpenMap hf.contMDiff.continuous hinj hf.isOpenMap
  have hK : IsCompact {x : M | riemannianEDistOf g (f p) (f x) ≤ R} :=
    hemb.isEmbedding.isInducing.isCompact_preimage' hcompact hball
  have hclosed : IsClosed {x : M | riemannianEDistOf (S.base.metric t) p x ≤ r} := by
    apply isClosed_le ?_ continuous_const
    unfold riemannianEDistOf
    exact Geometry.Riemannian.continuous_riemannianEDist (S.base.metric t) p
  apply hK.of_isClosed_subset hclosed
  intro x hx
  have hbound := (riemannianEDistOf_exp_bounds_of_curvature_bound S hS hcarrier hregular hRm
    (show b ∈ Icc a b from ⟨ht.1.trans ht.2, le_rfl⟩) ht p x).2
  rw [hterminal, abs_sub_comm b t] at hbound
  have hambient : riemannianEDistOf g (f p) (f x) ≤
      riemannianEDistOf (localPullMetric g f hf) p x := by
    have h := Geometry.Metric.edistOf_le_of_quad_of_localDiffeomorph
      (localPullMetric g f hf) g f hf (c := 1) zero_lt_one
      (fun z v => by rw [localPullMetric_inner, one_mul]) p x
    simpa only [Real.sqrt_one, ENNReal.ofReal_one, one_mul] using h
  have hmul : ENNReal.ofReal (Real.exp
      ((Module.finrank ℝ E : ℝ) ^ 2 * Real.sqrt C * |t - b|)) *
      riemannianEDistOf (S.base.metric t) p x ≤
      ENNReal.ofReal (Real.exp
        ((Module.finrank ℝ E : ℝ) ^ 2 * Real.sqrt C * |t - b|)) * (r : ℝ≥0∞) :=
    mul_le_mul_right hx _
  exact hambient.trans (hbound.trans (hmul.trans hfit))


theorem riemannianEDistOf_exp_bounds_on_localPullMetric_terminal_ball
    (g : SmoothRiemannianMetric J N) (f : M → N)
    (hf : IsLocalDiffeomorph I J ∞ f) (hinj : Function.Injective f)
    (S : SolutionOn (I := I) (M := M) D) (hS : IsSolutionOn S)
    {a b C t : ℝ} (hcarrier : Icc a b ⊆ D.carrier)
    (hregular : Ioo a b ⊆ D.regular)
    (hRm : ∀ r ∈ Icc a b, ∀ x : M,
      normSq0S (I := I) (S.base.metric r) x 4 (S.base.rm04 r x) ≤ C)
    (ht : t ∈ Icc a b) (hterminal : S.base.metric b = localPullMetric g f hf)
    (p : M) {R : ℝ≥0} (hR : 0 < R)
    (hball : {x : N | riemannianEDistOf g (f p) x < R} ⊆ range f)
    (x : M) (hx : riemannianEDistOf g (f p) (f x) < (R / 3 : ℝ≥0)) :
    ENNReal.ofReal (Real.exp
        (-((Module.finrank ℝ E : ℝ) ^ 2 * Real.sqrt C * |t - b|))) *
        riemannianEDistOf g (f p) (f x) ≤ riemannianEDistOf (S.base.metric t) p x ∧
      riemannianEDistOf (S.base.metric t) p x ≤
        ENNReal.ofReal (Real.exp
          ((Module.finrank ℝ E : ℝ) ^ 2 * Real.sqrt C * |t - b|)) *
          riemannianEDistOf g (f p) (f x) := by
  have heq := Geometry.Metric.riemannianEDistOf_localPullMetric_eq_of_ball_subset
    g f hf hinj p hR hball x hx
  have hd := riemannianEDistOf_exp_bounds_of_curvature_bound S hS hcarrier hregular hRm
    ht ⟨ht.1.trans ht.2, le_rfl⟩ p x
  rwa [hterminal, heq] at hd

end DifferentialGeometry.PDE.RicciFlow
