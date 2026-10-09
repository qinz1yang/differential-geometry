import DifferentialGeometry.Geometry.Hyperbolic.IsometrySmooth
import DifferentialGeometry.Geometry.Hyperbolic.UniversalCoverMetric
import DifferentialGeometry.Geometry.Metric.Distance.Topology
import DifferentialGeometry.Geometry.Metric.Comparison.DistanceScaling
import DifferentialGeometry.Geometry.Measure.Isometry

noncomputable section

open scoped Manifold ContDiff Bundle Topology

namespace DifferentialGeometry.Geometry.Hyperbolic

open Riemannian.Topology (UniversalCover SemilocallySimplyConnectedSpace
  manifold_semilocallySimplyConnectedSpace)

local notation "E3" => EuclideanSpace ℝ (Fin 3)
local notation "H3" => Hyperboloid E3

variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E3 H} [I.Boundaryless]
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [T2Space M] [SigmaCompactSpace M] [ConnectedSpace M]

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
private theorem exists_normalized_smooth_covering
    (g : SmoothRiemannianMetric I M) (hg : RiemannianMetricComplete g)
    (κ : ℝ) (hκ : κ < 0)
    (hsec : ∀ (x : M) (v w : TangentSpace I x),
      Curvature.metricRm04StandardAt g x v w w v =
        κ * (g.inner x v v * g.inner x w w - g.inner x v w * g.inner x v w)) :
    ∃ q : H3 → M, IsCoveringMap q ∧ Function.Surjective q ∧
      IsLocalDiffeomorph 𝓘(ℝ, E3) I ∞ q ∧
      ∀ x r, q '' Metric.ball x r = riemannianBallOf (scaleMetric (-κ) (neg_pos.mpr hκ) g) (q x) r := by
  let x₀ : M := Classical.choice inferInstance
  let _ : Inhabited M := ⟨x₀⟩
  let _ : LocallyPathConnectedSpace H := I.toHomeomorph.isOpenEmbedding.locallyPathConnectedSpace
  let _ : LocallyPathConnectedSpace M := ChartedSpace.locallyPathConnectedSpace H M
  let _ : PathConnectedSpace M := PathConnectedSpace.of_locallyPathConnectedSpace
  let _ : SemilocallySimplyConnectedSpace M := manifold_semilocallySimplyConnectedSpace (I := I)
  let _ : SecondCountableTopology H := ModelWithCorners.secondCountableTopology I
  let _ : SecondCountableTopology M := ChartedSpace.secondCountable_of_sigmaCompact H M
  let gN := scaleMetric (-κ) (neg_pos.mpr hκ) g
  let ĝ := UniversalCover.liftedMetric (I := I) gN
  let hĝ : RiemannianMetricComplete ĝ := UniversalCover.liftedMetric_complete gN (hg.scaleMetric _ _)
  let _ : IsManifold I 1 (UniversalCover M) :=
    IsManifold.of_le (I := I) (M := UniversalCover M) (n := ∞) (by decide)
  let _ : TopologicalSpace.MetrizableSpace (UniversalCover M) := Manifold.metrizableSpace I (UniversalCover M)
  let _ : T3Space (UniversalCover M) := inferInstance
  let _ : Bundle.RiemannianBundle (TangentSpace I : UniversalCover M → Type _) := ⟨ĝ.toRiemannianMetric⟩
  let _ : IsContinuousRiemannianBundle E3 (TangentSpace I : UniversalCover M → Type _) :=
    ⟨⟨ĝ.inner, ĝ.contMDiff.continuous, by intro x v w; rfl⟩⟩
  let _ : EMetricSpace (UniversalCover M) := EMetricSpace.ofRiemannianMetric I (UniversalCover M)
  let _ : PseudoEMetricSpace (UniversalCover M) :=
    (EMetricSpace.ofRiemannianMetric I (UniversalCover M)).toPseudoEMetricSpace
  let _ : CompleteSpace (UniversalCover M) := hĝ.complete
  let _ : NeZero (Module.finrank ℝ E3) := ⟨by simp⟩
  let b : OrthonormalBasis (Fin 3) ℝ (TangentSpace I (UniversalCover.basePoint (X := M))) :=
    (stdOrthonormalBasis ℝ (TangentSpace I (UniversalCover.basePoint (X := M)))).reindex
      (finCongr (show Module.finrank ℝ (TangentSpace I (UniversalCover.basePoint (X := M))) = 3 from
        finrank_euclideanSpace_fin))
  let i := b.repr.symm
  let e := normalizedUniversalCoverIsometryEquiv g hg κ hκ x₀ hsec i
  let q : H3 → M := fun x => UniversalCover.proj (e x)
  have heq : (e : H3 → UniversalCover M) =
      Riemannian.Exponential.hyperbolicComparison ĝ hĝ UniversalCover.basePoint i :=
    funext (normalizedUniversalCoverIsometryEquiv_apply g hg κ hκ x₀ hsec i)
  have he : IsLocalDiffeomorph 𝓘(ℝ, E3) I ∞ e := by
    rw [heq]
    exact Riemannian.Exponential.isLocalDiffeomorph_hyperbolicComparison
      ĝ hĝ UniversalCover.basePoint (normalized_lifted_riemannOp g κ hκ hsec) i
  refine ⟨q, isCoveringMap_proj_normalizedUniversalCoverIsometryEquiv g hg κ hκ x₀ hsec i, ?_, ?_, ?_⟩
  · intro x
    let x' : UniversalCover M := ⟨x, ⟦PathConnectedSpace.somePath x₀ x⟧⟩
    refine ⟨e.symm x', ?_⟩
    change UniversalCover.proj (e (e.symm x')) = x
    rw [e.apply_symm_apply]
    rfl
  · intro x
    exact (he x).comp I M (UniversalCover.proj_localDiffeo (I := I) (e x))
  · exact image_ball_proj_normalizedUniversalCoverIsometryEquiv g hg κ hκ x₀ hsec i

variable {H' : Type*} [TopologicalSpace H'] {J : ModelWithCorners ℝ E3 H'} [J.Boundaryless]
  {N : Type*} [TopologicalSpace N] [ChartedSpace H' N] [IsManifold J ∞ N]
  [T2Space N] [SigmaCompactSpace N] [ConnectedSpace N]

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
theorem contMDiff_isometryEquiv
    (g : SmoothRiemannianMetric I M) (h : SmoothRiemannianMetric J N)
    (κ : ℝ) (hκ : κ < 0) (hg : RiemannianMetricComplete g) (hh : RiemannianMetricComplete h)
    (hsecg : ∀ (x : M) (v w : TangentSpace I x),
      Curvature.metricRm04StandardAt g x v w w v =
        κ * (g.inner x v v * g.inner x w w - g.inner x v w * g.inner x v w))
    (hsech : ∀ (x : N) (v w : TangentSpace J x),
      Curvature.metricRm04StandardAt h x v w w v =
        κ * (h.inner x v v * h.inner x w w - h.inner x v w * h.inner x v w)) :
    letI : TopologicalSpace.MetrizableSpace M := Manifold.metrizableSpace I M
    letI : TopologicalSpace.MetrizableSpace N := Manifold.metrizableSpace J N
    letI : PseudoMetricSpace M := g.toPseudoMetricSpace
    letI : MetricSpace M := MetricSpace.ofT0PseudoMetricSpace M
    letI : PseudoMetricSpace N := h.toPseudoMetricSpace
    letI : MetricSpace N := MetricSpace.ofT0PseudoMetricSpace N
    ∀ a : M ≃ᵢ N, ContMDiff I J ∞ a := by
  let _ : TopologicalSpace.MetrizableSpace M := Manifold.metrizableSpace I M
  let _ : TopologicalSpace.MetrizableSpace N := Manifold.metrizableSpace J N
  let _ : PseudoMetricSpace M := g.toPseudoMetricSpace
  let _ : MetricSpace M := MetricSpace.ofT0PseudoMetricSpace M
  let _ : PseudoMetricSpace N := h.toPseudoMetricSpace
  let _ : MetricSpace N := MetricSpace.ofT0PseudoMetricSpace N
  intro a
  let ae : M ≃ N := a.toEquiv
  change ContMDiff I J ∞ ae
  have ha (x y : M) : riemannianEDistOf h (ae x) (ae y) = riemannianEDistOf g x y := a.edist_eq x y
  obtain ⟨q, hq, hqs, hqd, hqball⟩ := exists_normalized_smooth_covering g hg κ hκ hsecg
  obtain ⟨p, hp, hps, hpd, hpball⟩ := exists_normalized_smooth_covering h hh κ hκ hsech
  let gN := scaleMetric (-κ) (neg_pos.mpr hκ) g
  let hN := scaleMetric (-κ) (neg_pos.mpr hκ) h
  let _ : PseudoMetricSpace M := gN.toPseudoMetricSpace
  let _ : MetricSpace M := MetricSpace.ofT0PseudoMetricSpace M
  let _ : PseudoMetricSpace N := hN.toPseudoMetricSpace
  let _ : MetricSpace N := MetricSpace.ofT0PseudoMetricSpace N
  let aN : M ≃ᵢ N :=
    { toEquiv := ae
      isometry_toFun := fun x y => by
        change riemannianEDistOf hN (ae x) (ae y) = riemannianEDistOf gN x y
        rw [edistOf_scale, edistOf_scale, ha] }
  have hqball' (x : H3) (r : ℝ) (_ : 0 < r) :
      q '' Metric.ball x r = Metric.eball (q x) (ENNReal.ofReal r) := by
    rw [hqball]
    ext y
    change riemannianEDistOf gN (q x) y < ENNReal.ofReal r ↔ edist y (q x) < ENNReal.ofReal r
    rw [edist_comm]
    rfl
  have hpball' (x : H3) (r : ℝ) (_ : 0 < r) :
      p '' Metric.ball x r = Metric.eball (p x) (ENNReal.ofReal r) := by
    rw [hpball]
    ext y
    change riemannianEDistOf hN (p x) y < ENNReal.ofReal r ↔ edist y (p x) < ENNReal.ofReal r
    rw [edist_comm]
    rfl
  exact contMDiff_isometryEquiv_of_covering q p hq hp hqs hps hqball' hpball' hqd hpd.contMDiff aN


private local instance : MeasurableSpace M := borel M
private local instance : BorelSpace M := ⟨rfl⟩
private local instance : MeasurableSpace N := borel N
private local instance : BorelSpace N := ⟨rfl⟩

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
theorem measurePreserving_isometryEquiv
    (g : SmoothRiemannianMetric I M) (h : SmoothRiemannianMetric J N)
    (κ : ℝ) (hκ : κ < 0) (hg : RiemannianMetricComplete g) (hh : RiemannianMetricComplete h)
    (hsecg : ∀ (x : M) (v w : TangentSpace I x),
      Curvature.metricRm04StandardAt g x v w w v =
        κ * (g.inner x v v * g.inner x w w - g.inner x v w * g.inner x v w))
    (hsech : ∀ (x : N) (v w : TangentSpace J x),
      Curvature.metricRm04StandardAt h x v w w v =
        κ * (h.inner x v v * h.inner x w w - h.inner x v w * h.inner x v w)) :
    letI : TopologicalSpace.MetrizableSpace M := Manifold.metrizableSpace I M
    letI : TopologicalSpace.MetrizableSpace N := Manifold.metrizableSpace J N
    letI : PseudoMetricSpace M := g.toPseudoMetricSpace
    letI : MetricSpace M := MetricSpace.ofT0PseudoMetricSpace M
    letI : PseudoMetricSpace N := h.toPseudoMetricSpace
    letI : MetricSpace N := MetricSpace.ofT0PseudoMetricSpace N
    ∀ a : M ≃ᵢ N, MeasureTheory.MeasurePreserving a
      (Integral.Measure.riemannianVolumeMeasure I M g) (Integral.Measure.riemannianVolumeMeasure J N h) := by
  let _ : TopologicalSpace.MetrizableSpace M := Manifold.metrizableSpace I M
  let _ : TopologicalSpace.MetrizableSpace N := Manifold.metrizableSpace J N
  let _ : PseudoMetricSpace M := g.toPseudoMetricSpace
  let _ : MetricSpace M := MetricSpace.ofT0PseudoMetricSpace M
  let _ : PseudoMetricSpace N := h.toPseudoMetricSpace
  let _ : MetricSpace N := MetricSpace.ofT0PseudoMetricSpace N
  intro a
  let Φ : M ≃ₘ⟮I, J⟯ N :=
    { toEquiv := a.toEquiv
      contMDiff_toFun := contMDiff_isometryEquiv g h κ hκ hg hh hsecg hsech a
      contMDiff_invFun := contMDiff_isometryEquiv h g κ hκ hh hg hsech hsecg a.symm }
  exact Measure.measurePreserving_diffeomorph_of_riemannian_distance_eq g h Φ
    (fun x y => a.edist_eq x y)

end DifferentialGeometry.Geometry.Hyperbolic
