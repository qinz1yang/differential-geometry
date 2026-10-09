import DifferentialGeometry.Geometry.Hyperbolic.TopologicalStability
import DifferentialGeometry.Geometry.Hyperbolic.Approximation
import DifferentialGeometry.Geometry.Metric.Approximation.Maps
import DifferentialGeometry.Geometry.Metric.Distance.Topology
import DifferentialGeometry.Geometry.Comparison.HopfRinow.Proper
import DifferentialGeometry.Topology.FiberBundle.Separation
import Mathlib.Topology.Order.Compact


noncomputable section

open Set
open scoped Manifold ContDiff

namespace DifferentialGeometry.Geometry.Hyperbolic

private theorem image_eq_of_subtype_eqOn
    {X Y Z : Type*} {Ω K : Set X} (hK : K ⊆ Ω) (Φ : X → Y) (f : Ω → Y)
    (heq : EqOn (fun p : Ω => Φ p) f (Subtype.val ⁻¹' K)) (d : X → Y → Z) :
    (fun p : X => d p (Φ p)) '' K =
      (fun p : Ω => d p (f p)) '' (Subtype.val ⁻¹' K) := by
  ext z
  constructor
  · rintro ⟨p, hp, rfl⟩
    refine ⟨⟨p, hK hp⟩, hp, ?_⟩
    exact congrArg (d p) (heq hp).symm
  · rintro ⟨p, hp, rfl⟩
    exact ⟨p.val, hp, congrArg (d p.val) (heq hp)⟩

private theorem sSup_dist_subtype_lt_of_compact
    {X Y : Type*} [TopologicalSpace X] [PseudoMetricSpace Y]
    {Ω K U : Set X} (hK : IsCompact K) (hKΩ : K ⊆ Ω)
    (hUK : U ⊆ K) (hU : U.Nonempty)
    (e Φ : X → Y) (he : ContinuousOn e K) (hΦ : ContinuousOn Φ K) (f : Ω → Y)
    (heq : EqOn (fun p : Ω => Φ p) f (Subtype.val ⁻¹' K)) {ζ : ℝ}
    (hclose : sSup ((fun p : X => dist (e p) (Φ p)) '' K) < ζ) :
    ((fun p : X => dist (e p) (Φ p)) '' K =
      (fun p : Ω => dist (e p) (f p)) '' (Subtype.val ⁻¹' K)) ∧
    BddAbove ((fun p : Ω => dist (e p) (f p)) '' (Subtype.val ⁻¹' K)) ∧
    sSup ((fun p : Ω => dist (e p) (f p)) '' (Subtype.val ⁻¹' K)) < ζ ∧
    sSup ((fun p : Ω => dist (e p) (f p)) '' (Subtype.val ⁻¹' U)) < ζ := by
  have himage := image_eq_of_subtype_eqOn hKΩ Φ f heq (fun p y => dist (e p) y)
  have hbdd : BddAbove ((fun p : X => dist (e p) (Φ p)) '' K) :=
    hK.bddAbove_image (continuous_dist.comp_continuousOn (he.prodMk hΦ))
  have hbdd' : BddAbove ((fun p : Ω => dist (e p) (f p)) '' (Subtype.val ⁻¹' K)) :=
    himage ▸ hbdd
  have hclosed : sSup ((fun p : Ω => dist (e p) (f p)) '' (Subtype.val ⁻¹' K)) < ζ :=
    himage ▸ hclose
  refine ⟨himage, hbdd', hclosed, ?_⟩
  have hne : ((fun p : Ω => dist (e p) (f p)) '' (Subtype.val ⁻¹' U)).Nonempty := by
    obtain ⟨p, hp⟩ := hU
    exact ⟨_, ⟨p, hKΩ (hUK hp)⟩, hp, rfl⟩
  exact (csSup_le_csSup hbdd' hne (image_mono (preimage_mono hUK))).trans_lt hclosed

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [T2Space M] [SigmaCompactSpace M] [PreconnectedSpace M]
  {N : Type*} [TopologicalSpace N] [ChartedSpace H N] [IsManifold I ∞ N]
  [T2Space N] [SigmaCompactSpace N] [PreconnectedSpace N]

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
private theorem metric_approximation_closeness_transfer
    {Ω : Set M} (f : Ω → N) (g : SmoothRiemannianMetric I M)
    (hg : RiemannianMetricComplete g) (h : SmoothRiemannianMetric I N)
    (o : M) {R r ζ ε : ℝ} {p : ℕ}
    (hf : isMetricApproximationOnBall f g h o R p ε)
    (Φ : PartialDiffeomorph I I M N ∞)
    (hΦ : DifferentialGeometry.PartialDiffeomorph.isMetricApproximationOn Φ
      (riemannianClosedBallOf g o R) p ε g h)
    (heq : EqOn (fun y : Ω => Φ y) f (Subtype.val ⁻¹' riemannianClosedBallOf g o R))
    (hr : 0 < r) (hrR : r ≤ R) :
    letI : TopologicalSpace.MetrizableSpace M := Manifold.metrizableSpace I M
    letI : PseudoMetricSpace M := g.toPseudoMetricSpace
    letI : MetricSpace M := MetricSpace.ofT0PseudoMetricSpace M
    letI : TopologicalSpace.MetrizableSpace N := Manifold.metrizableSpace I N
    letI : PseudoMetricSpace N := h.toPseudoMetricSpace
    letI : MetricSpace N := MetricSpace.ofT0PseudoMetricSpace N
    ∀ e : M ≃ᵢ N,
      sSup ((fun q => dist (e q) (Φ q)) '' Metric.closedBall o r) < ζ →
      ((fun q => dist (e q) (Φ q)) '' Metric.closedBall o r =
        (fun q : Ω => dist (e q) (f q)) '' (Subtype.val ⁻¹' Metric.closedBall o r)) ∧
      BddAbove ((fun q : Ω => dist (e q) (f q)) '' (Subtype.val ⁻¹' Metric.closedBall o r)) ∧
      sSup ((fun q : Ω => dist (e q) (f q)) '' (Subtype.val ⁻¹' Metric.closedBall o r)) < ζ ∧
      sSup ((fun q : Ω => dist (e q) (f q)) '' (Subtype.val ⁻¹' Metric.ball o r)) < ζ := by
  let _ : TopologicalSpace.MetrizableSpace M := Manifold.metrizableSpace I M
  let _ : PseudoMetricSpace M := g.toPseudoMetricSpace
  let _ : MetricSpace M := MetricSpace.ofT0PseudoMetricSpace M
  let _ : TopologicalSpace.MetrizableSpace N := Manifold.metrizableSpace I N
  let _ : PseudoMetricSpace N := h.toPseudoMetricSpace
  let _ : MetricSpace N := MetricSpace.ofT0PseudoMetricSpace N
  intro e hclose
  have hclosed : riemannianClosedBallOf g o r = Metric.closedBall o r := by
    ext y
    change edist o y ≤ ENNReal.ofReal r ↔ dist y o ≤ r
    rw [edist_dist, dist_comm, ENNReal.ofReal_le_ofReal_iff hr.le]
  have hsmall : Metric.closedBall o r ⊆ riemannianClosedBallOf g o R := by
    rw [← hclosed]
    exact riemannianClosedBallOf_mono g o hrR
  have hcompact : IsCompact (Metric.closedBall o r) := by
    rw [← hclosed]
    exact hg.closedEBall_isCompact o r
  have hcont : ContinuousOn (Φ : M → N) (Metric.closedBall o r) :=
    Φ.contMDiffOn_toFun.continuousOn.mono (hsmall.trans hΦ.1)
  exact sSup_dist_subtype_lt_of_compact hcompact (hsmall.trans hf.2.1)
    Metric.ball_subset_closedBall ⟨o, Metric.mem_ball_self hr⟩ e Φ
    e.continuous.continuousOn hcont f (heq.mono (preimage_mono hsmall)) hclose

end DifferentialGeometry.Geometry.Hyperbolic


open scoped Manifold ContDiff ENNReal

namespace DifferentialGeometry.Geometry.Hyperbolic

universe u v

local notation "E3" => EuclideanSpace ℝ (Fin 3)

variable {M : Type u} [TopologicalSpace M] [ChartedSpace E3 M]
  [IsManifold (𝓡 3) ∞ M] [T2Space M] [SigmaCompactSpace M] [ConnectedSpace M]

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
private theorem exists_isometry_close_of_cusp_count_le
    (g : SmoothRiemannianMetric (𝓡 3) M) (hg : RiemannianMetricComplete g)
    (hvolg : Integral.Measure.riemannianVolumeMeasure (𝓡 3) M g Set.univ < ⊤)
    (hsecg : ∀ (x : M) (v w : TangentSpace (𝓡 3) x),
      Curvature.metricRm04StandardAt g x v w w v =
        (-1 / 4 : ℝ) * (g.inner x v v * g.inner x w w - g.inner x v w * g.inner x v w))
    (o : M) {ζ : ℝ} (hζ : 0 < ζ) :
    letI : TopologicalSpace.MetrizableSpace M := Manifold.metrizableSpace (𝓡 3) M
    letI : PseudoMetricSpace M := g.toPseudoMetricSpace
    letI : MetricSpace M := MetricSpace.ofT0PseudoMetricSpace M
    ∃ n : ℕ, 1 ≤ n ∧ ζ⁻¹ < (n : ℝ) + 1 ∧
      ∀ (N : Type v) [TopologicalSpace N] [ChartedSpace E3 N]
        [IsManifold (𝓡 3) ∞ N] [T2Space N] [SigmaCompactSpace N] [ConnectedSpace N]
        (h : SmoothRiemannianMetric (𝓡 3) N),
        RiemannianMetricComplete h →
        Integral.Measure.riemannianVolumeMeasure (𝓡 3) N h Set.univ < ⊤ →
        (∀ (y : N) (v w : TangentSpace (𝓡 3) y),
          Curvature.metricRm04StandardAt h y v w w v =
            (-1 / 4 : ℝ) * (h.inner y v v * h.inner y w w - h.inner y v w * h.inner y v w)) →
        Geometry.Topology.endCount M ≤ Geometry.Topology.endCount N →
        ∀ Φ : PartialDiffeomorph (𝓡 3) (𝓡 3) M N ∞,
          PartialDiffeomorph.isMetricApproximationOn Φ
            (riemannianClosedBallOf g o (n + 1 : ℝ)) (n + 1) (1 / (n + 1 : ℝ)) g h →
          letI : TopologicalSpace.MetrizableSpace N := Manifold.metrizableSpace (𝓡 3) N
          letI : PseudoMetricSpace N := h.toPseudoMetricSpace
          letI : MetricSpace N := MetricSpace.ofT0PseudoMetricSpace N
          ∃ e : M ≃ᵢ N,
            sSup ((fun p => dist (e p) (Φ p)) '' Metric.closedBall o ζ⁻¹) < ζ := by
  let _ : TopologicalSpace.MetrizableSpace M := Manifold.metrizableSpace (𝓡 3) M
  let _ : PseudoMetricSpace M := g.toPseudoMetricSpace
  let _ : MetricSpace M := MetricSpace.ofT0PseudoMetricSpace M
  obtain ⟨s, hs, hsr, hclose⟩ :=
    exists_isometry_close_of_homeomorph_of_metric_approximation
      g hg hvolg (-1 / 4) (by norm_num) hsecg o hζ
  obtain ⟨n, hsn, htop⟩ :=
    hyperbolic_topological_stability_of_cusp_count_le g hg hvolg hsecg o s
  have hsnR : (s : ℝ) + 1 ≤ (n : ℝ) + 1 := by exact_mod_cast Nat.add_le_add_right hsn 1
  refine ⟨n, hs.trans hsn, hsr.trans_le hsnR, ?_⟩
  intro N _ _ _ _ _ _ h hh hvolh hsech hcount Φ hΦ
  obtain ⟨F⟩ := htop N h hh hvolh hsech hcount Φ hΦ
  have hsmall : PartialDiffeomorph.isMetricApproximationOn Φ
      (riemannianClosedBallOf g o (s + 1 : ℝ)) (s + 1) (1 / (s + 1 : ℝ)) g h := by
    apply hΦ.mono
    · intro p hp
      exact hp.trans (ENNReal.ofReal_le_ofReal hsnR)
    · omega
    · exact one_div_le_one_div_of_le (by positivity) hsnR
  exact hclose N h hh hvolh hsech F Φ hsmall

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
private theorem exists_isometry_close_to_original_map_of_cusp_count_le
    (g : SmoothRiemannianMetric (𝓡 3) M) (hg : RiemannianMetricComplete g)
    (hvolg : Integral.Measure.riemannianVolumeMeasure (𝓡 3) M g Set.univ < ⊤)
    (hsecg : ∀ (x : M) (v w : TangentSpace (𝓡 3) x),
      Curvature.metricRm04StandardAt g x v w w v =
        (-1 / 4 : ℝ) * (g.inner x v v * g.inner x w w - g.inner x v w * g.inner x v w))
    (o : M) {ζ : ℝ} (hζ : 0 < ζ) :
    letI : TopologicalSpace.MetrizableSpace M := Manifold.metrizableSpace (𝓡 3) M
    letI : PseudoMetricSpace M := g.toPseudoMetricSpace
    letI : MetricSpace M := MetricSpace.ofT0PseudoMetricSpace M
    ∃ ξ : ℝ, 0 < ξ ∧ ∃ n : ℕ, ξ = 1 / ((n : ℝ) + 1) ∧ ζ⁻¹ < ξ⁻¹ ∧
      ∀ (N : Type v) [TopologicalSpace N] [ChartedSpace E3 N]
        [IsManifold (𝓡 3) ∞ N] [T2Space N] [SigmaCompactSpace N] [ConnectedSpace N]
        (h : SmoothRiemannianMetric (𝓡 3) N),
        RiemannianMetricComplete h →
        Integral.Measure.riemannianVolumeMeasure (𝓡 3) N h Set.univ < ⊤ →
        (∀ (y : N) (v w : TangentSpace (𝓡 3) y),
          Curvature.metricRm04StandardAt h y v w w v =
            (-1 / 4 : ℝ) * (h.inner y v v * h.inner y w w - h.inner y v w * h.inner y v w)) →
        Geometry.Topology.endCount M ≤ Geometry.Topology.endCount N →
        ∀ (Ω : Set M) (f : Ω → N),
          isMetricApproximationOnBall f g h o ξ⁻¹ (n + 1) ξ →
          letI : TopologicalSpace.MetrizableSpace N := Manifold.metrizableSpace (𝓡 3) N
          letI : PseudoMetricSpace N := h.toPseudoMetricSpace
          letI : MetricSpace N := MetricSpace.ofT0PseudoMetricSpace N
          ∃ e : M ≃ᵢ N,
            sSup ((fun p : Ω => dist (e p) (f p)) ''
              (Subtype.val ⁻¹' Metric.closedBall o ζ⁻¹)) < ζ ∧
            sSup ((fun p : Ω => dist (e p) (f p)) ''
              (Subtype.val ⁻¹' Metric.ball o ζ⁻¹)) < ζ := by
  let _ : TopologicalSpace.MetrizableSpace M := Manifold.metrizableSpace (𝓡 3) M
  let _ : PseudoMetricSpace M := g.toPseudoMetricSpace
  let _ : MetricSpace M := MetricSpace.ofT0PseudoMetricSpace M
  let _ : NeZero (Module.finrank ℝ E3) := ⟨by simp⟩
  obtain ⟨n, hn, hr, hclose⟩ :=
    exists_isometry_close_of_cusp_count_le g hg hvolg hsecg o hζ
  refine ⟨1 / ((n : ℝ) + 1), by positivity, n, rfl, ?_, ?_⟩
  · simpa only [one_div, inv_inv] using hr
  intro N _ _ _ _ _ _ h hh hvolh hsech hcount Ω f hf
  let _ : TopologicalSpace.MetrizableSpace N := Manifold.metrizableSpace (𝓡 3) N
  let _ : PseudoMetricSpace N := h.toPseudoMetricSpace
  let _ : MetricSpace N := MetricSpace.ofT0PseudoMetricSpace N
  have hf' : isMetricApproximationOnBall f g h o ((n : ℝ) + 1)
      (n + 1) (1 / ((n : ℝ) + 1)) := by
    simpa only [one_div, inv_inv] using hf
  obtain ⟨Φ, hΦ, heq⟩ := hf'.2.2
  obtain ⟨e, he⟩ := hclose N h hh hvolh hsech hcount Φ hΦ
  exact ⟨e, (metric_approximation_closeness_transfer f g hg h o hf' Φ hΦ heq
    (inv_pos.mpr hζ) hr.le e he).2.2⟩

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
theorem hyperbolic_stability_of_cusp_count_le
    (g : SmoothRiemannianMetric (𝓡 3) M) (hg : RiemannianMetricComplete g)
    (hvolg : Integral.Measure.riemannianVolumeMeasure (𝓡 3) M g Set.univ < ⊤)
    (hsecg : ∀ (x : M) (v w : TangentSpace (𝓡 3) x),
      Curvature.metricRm04StandardAt g x v w w v =
        (-1 / 4 : ℝ) * (g.inner x v v * g.inner x w w - g.inner x v w * g.inner x v w))
    (o : M) {ζ : ℝ} (hζ : 0 < ζ) :
    letI : TopologicalSpace.MetrizableSpace M := Manifold.metrizableSpace (𝓡 3) M
    letI : PseudoMetricSpace M := g.toPseudoMetricSpace
    letI : MetricSpace M := MetricSpace.ofT0PseudoMetricSpace M
    ∃ ξ : ℝ, 0 < ξ ∧ ∃ n : ℕ, ξ = 1 / ((n : ℝ) + 1) ∧ ζ⁻¹ < ξ⁻¹ ∧
      ∀ (N : Type v) [TopologicalSpace N] [ChartedSpace E3 N]
        [IsManifold (𝓡 3) ∞ N] [T2Space N] [SigmaCompactSpace N] [ConnectedSpace N]
        (h : SmoothRiemannianMetric (𝓡 3) N),
        RiemannianMetricComplete h →
        Integral.Measure.riemannianVolumeMeasure (𝓡 3) N h Set.univ < ⊤ →
        (∀ (y : N) (v w : TangentSpace (𝓡 3) y),
          Curvature.metricRm04StandardAt h y v w w v =
            (-1 / 4 : ℝ) * (h.inner y v v * h.inner y w w - h.inner y v w * h.inner y v w)) →
        Geometry.Topology.endCount M ≤ Geometry.Topology.endCount N →
        ∀ (Ω : Set M) (f : Ω → N),
          isMetricApproximationOnBall f g h o ξ⁻¹ (n + 1) ξ →
          letI : TopologicalSpace.MetrizableSpace N := Manifold.metrizableSpace (𝓡 3) N
          letI : PseudoMetricSpace N := h.toPseudoMetricSpace
          letI : MetricSpace N := MetricSpace.ofT0PseudoMetricSpace N
          ∃ e : M ≃ᵢ N,
            sSup ((fun p : Ω => dist (e p) (f p)) ''
              (Subtype.val ⁻¹' Metric.closedBall o ζ⁻¹)) < ζ := by
  obtain ⟨ξ, hξ, n, hn, hr, hclose⟩ :=
    exists_isometry_close_to_original_map_of_cusp_count_le g hg hvolg hsecg o hζ
  refine ⟨ξ, hξ, n, hn, hr, ?_⟩
  intro N _ _ _ _ _ _ h hh hvolh hsech hcount Ω f hf
  obtain ⟨e, hclosed, hopen⟩ := hclose N h hh hvolh hsech hcount Ω f hf
  exact ⟨e, hclosed⟩

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
theorem hyperbolic_stability_on_ball_of_cusp_count_le
    (g : SmoothRiemannianMetric (𝓡 3) M) (hg : RiemannianMetricComplete g)
    (hvolg : Integral.Measure.riemannianVolumeMeasure (𝓡 3) M g Set.univ < ⊤)
    (hsecg : ∀ (x : M) (v w : TangentSpace (𝓡 3) x),
      Curvature.metricRm04StandardAt g x v w w v =
        (-1 / 4 : ℝ) * (g.inner x v v * g.inner x w w - g.inner x v w * g.inner x v w))
    (o : M) {ζ : ℝ} (hζ : 0 < ζ) :
    letI : TopologicalSpace.MetrizableSpace M := Manifold.metrizableSpace (𝓡 3) M
    letI : PseudoMetricSpace M := g.toPseudoMetricSpace
    letI : MetricSpace M := MetricSpace.ofT0PseudoMetricSpace M
    ∃ ξ : ℝ, 0 < ξ ∧ ∃ n : ℕ, ξ = 1 / ((n : ℝ) + 1) ∧ ζ⁻¹ < ξ⁻¹ ∧
      ∀ (N : Type v) [TopologicalSpace N] [ChartedSpace E3 N]
        [IsManifold (𝓡 3) ∞ N] [T2Space N] [SigmaCompactSpace N] [ConnectedSpace N]
        (h : SmoothRiemannianMetric (𝓡 3) N),
        RiemannianMetricComplete h →
        Integral.Measure.riemannianVolumeMeasure (𝓡 3) N h Set.univ < ⊤ →
        (∀ (y : N) (v w : TangentSpace (𝓡 3) y),
          Curvature.metricRm04StandardAt h y v w w v =
            (-1 / 4 : ℝ) * (h.inner y v v * h.inner y w w - h.inner y v w * h.inner y v w)) →
        Geometry.Topology.endCount M ≤ Geometry.Topology.endCount N →
        ∀ (Ω : Set M) (f : Ω → N),
          isMetricApproximationOnBall f g h o ξ⁻¹ (n + 1) ξ →
          letI : TopologicalSpace.MetrizableSpace N := Manifold.metrizableSpace (𝓡 3) N
          letI : PseudoMetricSpace N := h.toPseudoMetricSpace
          letI : MetricSpace N := MetricSpace.ofT0PseudoMetricSpace N
          ∃ e : M ≃ᵢ N,
            sSup ((fun p : Ω => dist (e p) (f p)) ''
              (Subtype.val ⁻¹' Metric.ball o ζ⁻¹)) < ζ := by
  obtain ⟨ξ, hξ, n, hn, hr, hclose⟩ :=
    exists_isometry_close_to_original_map_of_cusp_count_le g hg hvolg hsecg o hζ
  refine ⟨ξ, hξ, n, hn, hr, ?_⟩
  intro N _ _ _ _ _ _ h hh hvolh hsech hcount Ω f hf
  obtain ⟨e, hclosed, hopen⟩ := hclose N h hh hvolh hsech hcount Ω f hf
  exact ⟨e, hopen⟩

end DifferentialGeometry.Geometry.Hyperbolic
