import DifferentialGeometry.Geometry.Measure.HyperbolicUniversalCover
import DifferentialGeometry.Geometry.Hyperbolic.Hyperboloid.Volume
import DifferentialGeometry.Analysis.Integration.Measure.BallPacking
import DifferentialGeometry.Analysis.Integration.Measure.Riemannian.Scaling
import DifferentialGeometry.Geometry.Comparison.HopfRinow.Proper
import DifferentialGeometry.Geometry.Metric.Distance.Topology
import DifferentialGeometry.Geometry.Metric.GroupAction.Displacement

open scoped Manifold ContDiff ENNReal Bundle
open DifferentialGeometry.Integral.Measure (riemannianVolumeMeasure)

namespace DifferentialGeometry.Geometry.Hyperbolic

open Riemannian.Topology (UniversalCover SemilocallySimplyConnectedSpace
  manifold_semilocallySimplyConnectedSpace)

local notation "E₃" => EuclideanSpace ℝ (Fin 3)

private instance : NeZero (Module.finrank ℝ E₃) := ⟨by simp⟩

variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E₃ H} [I.Boundaryless]
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [T2Space M] [SigmaCompactSpace M] [ConnectedSpace M]

private local instance : MeasurableSpace M := borel M
private local instance : BorelSpace M := ⟨rfl⟩

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
omit [I.Boundaryless] [SigmaCompactSpace M] in
private theorem isClosed_image_setOf_le_deck_displacement
    [Inhabited M] [LocallyPathConnectedSpace M] [SemilocallySimplyConnectedSpace M]
    (g : SmoothRiemannianMetric I M) (δ : ℝ≥0∞) :
    IsClosed ((UniversalCover.proj : UniversalCover M → M) ''
      {x | ∀ γ : FundamentalGroup M (default : M), γ ≠ 1 →
        δ ≤ riemannianEDistOf (UniversalCover.liftedMetric (I := I) g) x (γ • x)}) := by
  let ĝ := UniversalCover.liftedMetric (I := I) g
  let _ : Bundle.RiemannianBundle (TangentSpace I : UniversalCover M → Type _) := ⟨ĝ.toRiemannianMetric⟩
  let _ : IsContinuousRiemannianBundle E₃ (TangentSpace I : UniversalCover M → Type _) :=
    ⟨ĝ.inner, ĝ.contMDiff.continuous, fun _ _ _ => rfl⟩
  let _ : RegularSpace (UniversalCover M) := UniversalCover.uc_regularSpace I
  let _ : PseudoEMetricSpace (UniversalCover M) := PseudoEMetricSpace.ofRiemannianMetric I _
  let _ : IsIsometricSMul (FundamentalGroup M (default : M)) (UniversalCover M) :=
    ⟨fun γ => UniversalCover.universalCover_deck_isometry_of_liftedMetric g γ⟩
  let S : Set (UniversalCover M) := {x | ∀ γ : FundamentalGroup M (default : M), γ ≠ 1 →
    δ ≤ riemannianEDistOf ĝ x (γ • x)}
  let q := Quotient.mk (MulAction.orbitRel (FundamentalGroup M (default : M)) (UniversalCover M))
  have hq : IsClosed (q '' S) :=
    MulAction.isClosed_image_setOf_forall_le_edist_smul (FundamentalGroup M (default : M)) δ
  have hfiber (x y : UniversalCover M) : UniversalCover.proj x = UniversalCover.proj y ↔ q x = q y := by
    constructor
    · intro h
      obtain ⟨γ, hγ⟩ := (UniversalCover.proj_eq_iff_smul y x).mp h.symm
      exact Quotient.sound ⟨γ, hγ⟩
    · intro h
      obtain ⟨γ, hγ⟩ := Quotient.exact h
      exact (congrArg UniversalCover.proj hγ.symm).trans (UniversalCover.proj_deckAct γ y)
  have hpre : UniversalCover.proj ⁻¹' (UniversalCover.proj '' S) = q ⁻¹' (q '' S) := by
    ext x
    constructor
    · rintro ⟨y, hy, hxy⟩
      exact ⟨y, hy, (hfiber y x).mp hxy⟩
    · rintro ⟨y, hy, hxy⟩
      exact ⟨y, hy, (hfiber y x).mpr hxy⟩
  let _ : PathConnectedSpace M := PathConnectedSpace.of_locallyPathConnectedSpace
  have hsurj : Function.Surjective (UniversalCover.proj : UniversalCover M → M) := by
    intro y
    exact ⟨⟨y, ⟦PathConnectedSpace.somePath default y⟧⟩, rfl⟩
  apply (UniversalCover.proj_isCoveringMap.isQuotientMap hsurj).isCoinducing.isClosed_preimage.mp
  rw [hpre]
  exact hq.preimage continuous_quot_mk

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
theorem isCompact_image_setOf_le_normalized_deck_displacement
    (g : SmoothRiemannianMetric I M) (hg : RiemannianMetricComplete (I := I) g)
    (κ : ℝ) (hκ : κ < 0) (x₀ : M)
    (hsec : ∀ (p : M) (X Y : TangentSpace I p),
      Curvature.metricRm04StandardAt g p X Y Y X =
        κ * (g.inner p X X * g.inner p Y Y - g.inner p X Y * g.inner p X Y))
    (hvol : riemannianVolumeMeasure I M g Set.univ < ⊤) (δ : ℝ) (hδ : 0 < δ) :
    letI : Inhabited M := ⟨x₀⟩
    letI : LocallyPathConnectedSpace H := I.toHomeomorph.isOpenEmbedding.locallyPathConnectedSpace
    letI : LocallyPathConnectedSpace M := ChartedSpace.locallyPathConnectedSpace H M
    letI : SemilocallySimplyConnectedSpace M := manifold_semilocallySimplyConnectedSpace (I := I)
    let gN := scaleMetric (-κ) (neg_pos.mpr hκ) g
    let ĝ := UniversalCover.liftedMetric (I := I) gN
    IsCompact ((UniversalCover.proj : UniversalCover M → M) ''
      {x | ∀ γ : FundamentalGroup M (default : M), γ ≠ 1 →
        ENNReal.ofReal δ ≤ riemannianEDistOf ĝ x (γ • x)}) := by
  let _ : Inhabited M := ⟨x₀⟩
  let _ : LocallyPathConnectedSpace H := I.toHomeomorph.isOpenEmbedding.locallyPathConnectedSpace
  let _ : LocallyPathConnectedSpace M := ChartedSpace.locallyPathConnectedSpace H M
  let _ : SemilocallySimplyConnectedSpace M := manifold_semilocallySimplyConnectedSpace (I := I)
  let gN := scaleMetric (-κ) (neg_pos.mpr hκ) g
  let ĝ := UniversalCover.liftedMetric (I := I) gN
  let S : Set (UniversalCover M) := {x | ∀ γ : FundamentalGroup M (default : M), γ ≠ 1 →
    ENNReal.ofReal δ ≤ riemannianEDistOf ĝ x (γ • x)}
  let T : Set M := UniversalCover.proj '' S
  change IsCompact T
  have hclosed : IsClosed T := isClosed_image_setOf_le_deck_displacement gN (ENNReal.ofReal δ)
  let _ : TopologicalSpace.MetrizableSpace M := Manifold.metrizableSpace I M
  let _ : T3Space M := inferInstance
  let _ : PseudoMetricSpace M := gN.toPseudoMetricSpace
  let μ := riemannianVolumeMeasure I M gN
  have hμ : μ Set.univ < ⊤ := by
    rw [show μ = riemannianVolumeMeasure I M (scaleMetric (-κ) (neg_pos.mpr hκ) g) from rfl,
      Integral.Measure.volume_scale_apply]
    exact ENNReal.mul_lt_top (ENNReal.pow_lt_top ENNReal.ofReal_lt_top) hvol
  let _ : MeasureTheory.IsFiniteMeasure μ := ⟨hμ⟩
  let r := δ / 2
  have hr : 0 < r := half_pos hδ
  let v := riemannianVolumeMeasure 𝓘(ℝ, E₃) (Hyperboloid E₃) Hyperboloid.riemannianMetric
    (Metric.ball Hyperboloid.origin r)
  have hv : 0 < v := Hyperboloid.riemannianVolumeMeasure_ball_pos Hyperboloid.origin hr
  have hball (p : M) : riemannianBallOf gN p r = Metric.ball p r := by
    ext z
    change riemannianEDistOf gN p z < ENNReal.ofReal r ↔ dist z p < r
    rw [← SmoothRiemannianMetric.toPseudoMetricSpace_edist gN, edist_lt_ofReal, dist_comm]
  have hmass (p : M) (hp : p ∈ T) : v ≤ μ (Metric.ball p r) := by
    obtain ⟨x, hx, rfl⟩ := hp
    have hx' : ∀ γ : FundamentalGroup M (default : M), γ ≠ 1 →
        ENNReal.ofReal (2 * r) ≤ riemannianEDistOf ĝ x (γ • x) := by
      have he : 2 * r = δ := by dsimp [r]; ring
      rw [he]
      exact hx
    have h := riemannianVolumeMeasure_normalized_ball_eq_of_le_deck_displacement
      g hg κ hκ x₀ hsec x r hx'
    change μ (riemannianBallOf gN (UniversalCover.proj x) r) = v at h
    rw [hball] at h
    exact h.ge
  have hb : Bornology.IsBounded T :=
    MeasureTheory.isBounded_of_uniform_ball_measure_lower_bound μ hr hv hmass
  obtain ⟨R, hR, hTR⟩ := hb.subset_closedBall_lt 0 x₀
  have hc := (hg.scaleMetric (-κ) (neg_pos.mpr hκ)).closedEBall_isCompact x₀ R
  apply hc.of_isClosed_subset hclosed
  intro p hp
  have hd : dist x₀ p ≤ R := Metric.mem_closedBall'.mp (hTR hp)
  change riemannianEDistOf gN x₀ p ≤ ENNReal.ofReal R
  rw [← SmoothRiemannianMetric.toPseudoMetricSpace_edist gN, edist_le_ofReal hR.le]
  exact hd

end DifferentialGeometry.Geometry.Hyperbolic
