import DifferentialGeometry.Geometry.Measure.BallComparison
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.StandardCap.FullMetricWindowCapture
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.StandardCap.FullMetricWindowCover
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.StandardCap.FullPreparedGluing
import DifferentialGeometry.Geometry.Measure.LocalIsometry
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.StandardCap.StaticWindowVolume
import DifferentialGeometry.Topology.ThreeManifold.Surgery.FiniteCap.FiniteCapQuotient

import DifferentialGeometry.Geometry.Flow.RicciFlow.Estimates.BallVolumeComparison

set_option autoImplicit false
noncomputable section
open Set Function TopologicalSpace Manifold DifferentialGeometry
open DifferentialGeometry.Geometry.Neck DifferentialGeometry.Geometry.Metric DifferentialGeometry.Topology.ThreeManifold.Surgery DifferentialGeometry.Topology.Manifold.Attachment
open DifferentialGeometry.Topology.Manifold
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Integral.Measure MeasureTheory
open scoped Manifold ContDiff Topology ENNReal
namespace DifferentialGeometry.PDE.RicciFlow.StandardCap
private abbrev CurvGE3 := EuclideanSpace ℝ (Fin 3)
private abbrev CurvGIC := (𝓡 2).prod 𝓘(ℝ)
private local instance {B : ℝ} {hB : 0 < B} : ChartedSpace CurvGE3 (InsertionQuotient hB) :=
  radialCapAttachmentChartedSpace transitionEnd_pos hB
private local instance {B : ℝ} {hB : 0 < B} : IsManifold (𝓡 3) ∞ (InsertionQuotient hB) :=
  radialCapAttachment_isManifold transitionEnd_pos hB
private local instance : NeZero (Module.finrank ℝ CurvGE3) := ⟨by simp⟩
private local instance {B : ℝ} {hB : 0 < B} : T2Space (InsertionQuotient hB) :=
  radialCapAttachment_t2Space transitionEnd_pos hB
private local instance {B : ℝ} {hB : 0 < B} : SigmaCompactSpace (InsertionQuotient hB) := by
  let : SecondCountableTopology (InsertionQuotient hB) := radialCapAttachment_secondCountableTopology transitionEnd_pos hB
  let : LocallyCompactSpace (InsertionQuotient hB) := ChartedSpace.locallyCompactSpace CurvGE3 (InsertionQuotient hB)
  infer_instance
variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
variable [Fact (Module.finrank ℝ E = 3)] [TopologicalSpace H] (I : ModelWithCorners ℝ E H) [I.Boundaryless]
variable [TopologicalSpace M] [ChartedSpace H M] [T2Space M] [IsManifold I ∞ M]
variable {ι : Type*} [Finite ι] {precision : ι → ℝ}
variable (hδ : ∀ i, 0 < precision i) (f : ∀ i : ι, bufferedCylinder (precision i) → M)
variable (hf : ∀ i, _root_.Topology.IsOpenEmbedding (f i))
variable (hdisj : Pairwise (fun i j => Disjoint (range (f i)) (range (f j))))
variable (hs : ∀ i, IsLocalDiffeomorph CurvGIC I ∞ (f i))
local notation "CurvGQ" => FiniteCapQuotient transitionEnd_pos hδ f (fun i => _root_.Topology.IsEmbedding.injective (_root_.Topology.IsOpenEmbedding.toIsEmbedding (hf i))) hdisj
variable (U : Opens M) (g : SmoothRiemannianMetric I U)
variable (R : Set (ConnectedComponents (cutCore f)))
variable (hRet : MapsTo (Subtype.val : cutCore f → M) (retainedCore f R) U)
variable (c : ℝ) (hc : 4 ≤ c)
local notation "CurvGRet" => finiteCapRetained transitionEnd_pos hδ f hf hdisj R
local notation "CurvGB" => {b : ι × Bool // cuttingSphereComponent hδ f hf hdisj b ∈ R}
variable (x₀ : ι → U) (order : ι → ℕ)
variable (d₀ : ∀ i, normalizedDatum g (x₀ i) (precision i) (order i))
variable (hOriginal : ∀ i, f i = neckAmbientMap U (d₀ i))
variable {k' : {b : ι × Bool // cuttingSphereComponent hδ f hf hdisj b ∈ R} → ℕ}
variable (hrec : ∀ b : {b : ι × Bool // cuttingSphereComponent hδ f hf hdisj b ∈ R}, (c * precision b.val.1)⁻¹ + 1 ≤ (precision b.val.1)⁻¹)
variable (d : ∀ b : {b : ι × Bool // cuttingSphereComponent hδ f hf hdisj b ∈ R}, normalizedDatum g
  ((d₀ b.val.1).offsetPoint (cuttingSign_sq b.val.2)) (c * precision b.val.1) (k' b))
variable (hmap : ∀ b : {b : ι × Bool // cuttingSphereComponent hδ f hf hdisj b ∈ R}, (d b).map = (d₀ b.val.1).recenteringMap (cuttingSign_sq b.val.2) (hrec b))
variable (hside : ∀ b : {b : ι × Bool // cuttingSphereComponent hδ f hf hdisj b ∈ R}, (d b).retainedSide = true)
variable {A D ε : ℝ} {hA : 0 < A} {m : ℕ}
variable (w : ∀ b : {b : ι × Bool // cuttingSphereComponent hδ f hf hdisj b ∈ R}, CanonicalStaticInsertionWitness (d b) A hA D m ε)

private local instance {B : ℝ} {hB : 0 < B} :
    MeasurableSpace (InsertionQuotient hB) := borel (InsertionQuotient hB)
private local instance {B : ℝ} {hB : 0 < B} : BorelSpace (InsertionQuotient hB) := ⟨rfl⟩

theorem finiteFullPreparedMetric_normalized_tip_ball_volume_ge [SigmaCompactSpace M]
    (b : CurvGB) (heps : ε ≤ 1 / 2) {ρ : ℝ} (hρ : 0 < ρ) (hρD : ρ < D) :
    let : LocallyPathConnectedSpace M := originalModel_locallyPathConnected I Fact.out
    let : ChartedSpace CurvGE3 CurvGQ := finiteCapChartedSpace I Fact.out transitionEnd_pos hδ f hf hdisj
    let : IsManifold (𝓡 3) ∞ CurvGQ := finiteCapQuotient_isManifold Fact.out transitionEnd_pos hδ f hf hdisj hs
    let : T2Space CurvGQ := finiteCapQuotient_t2Space transitionEnd_pos hδ f hf hdisj
    let : SigmaCompactSpace CurvGQ := finiteCapQuotient_sigmaCompactSpace transitionEnd_pos hδ f hf hdisj
    let : SigmaCompactSpace CurvGRet := isSigmaCompact_iff_sigmaCompactSpace.mp
      (DifferentialGeometry.Geometry.isSigmaCompact_of_isOpen (𝓡 3) (CurvGRet).isOpen)
    let gRet := finiteFullPreparedMetric I hδ f hf hdisj hs U g R hRet c hc x₀ order d₀ hOriginal hrec d hmap hside w
    let F := finiteFullWitnessMap I Fact.out transitionEnd_pos hδ f hf hdisj hs R c hc b
    let Q := metricScalarAt g ((d₀ b.val.1).offsetPoint (cuttingSign_sq b.val.2))
    ENNReal.ofReal (1 / 4 : ℝ) *
      riemannianVolumeMeasure (𝓡 3) CurvGE3 metric (Metric.closedBall (0 : CurvGE3) (ρ / 4)) ≤
      riemannianVolumeMeasure (𝓡 3) CurvGRet (scaleMetric Q (d b).scalar_pos gRet)
        (riemannianBallOf (scaleMetric Q (d b).scalar_pos gRet) (F ((w b).data.tip)) ρ) := by
  let : LocallyPathConnectedSpace M := originalModel_locallyPathConnected I Fact.out
  let : ChartedSpace CurvGE3 CurvGQ := finiteCapChartedSpace I Fact.out transitionEnd_pos hδ f hf hdisj
  let : IsManifold (𝓡 3) ∞ CurvGQ := finiteCapQuotient_isManifold Fact.out transitionEnd_pos hδ f hf hdisj hs
  let : T2Space CurvGQ := finiteCapQuotient_t2Space transitionEnd_pos hδ f hf hdisj
  let : SigmaCompactSpace CurvGQ := finiteCapQuotient_sigmaCompactSpace transitionEnd_pos hδ f hf hdisj
  let : SigmaCompactSpace CurvGRet := isSigmaCompact_iff_sigmaCompactSpace.mp
    (DifferentialGeometry.Geometry.isSigmaCompact_of_isOpen (𝓡 3) (CurvGRet).isOpen)
  dsimp only
  let gRet := finiteFullPreparedMetric I hδ f hf hdisj hs U g R hRet c hc x₀ order d₀ hOriginal hrec d hmap hside w
  let F := finiteFullWitnessMap I Fact.out transitionEnd_pos hδ f hf hdisj hs R c hc b
  let Q := metricScalarAt g ((d₀ b.val.1).offsetPoint (cuttingSign_sq b.val.2))
  apply ((w b).normalized_tip_ball_volume_ge heps hρ hρD).trans
  apply DifferentialGeometry.Geometry.Measure.riemannianVolumeMeasure_ball_le_of_injective_local_isometry
    (scaleMetric Q (d b).scalar_pos (w b).data.outMetric)
    (scaleMetric Q (d b).scalar_pos gRet) F
    (isLocalDiffeomorph_finiteFullWitnessMap I Fact.out transitionEnd_pos hδ f hf hdisj hs R c hc b)
    (injective_finiteFullWitnessMap I Fact.out transitionEnd_pos hδ f hf hdisj hs R c hc b)
  intro p v z
  rw [scaleMetric_inner, scaleMetric_inner]
  exact congrArg (fun a => Q * a)
    (finiteFullPreparedMetric_witness_inner I hδ f hf hdisj hs U g R hRet c hc
      x₀ order d₀ hOriginal hrec d hmap hside w b p v z).symm

theorem finiteFullPreparedMetric_tip_ball_volume_ge_on_curvature_controlled_flow [SigmaCompactSpace M]
    (b : CurvGB) (heps : ε ≤ 1 / 2) {ρ : ℝ} (hρ : 0 < ρ) (hρD : ρ < D)
    (T K : ℝ) (hT : 0 ≤ T) (hK : 0 ≤ K) :
    let : LocallyPathConnectedSpace M := originalModel_locallyPathConnected I Fact.out
    let : ChartedSpace CurvGE3 CurvGQ := finiteCapChartedSpace I Fact.out transitionEnd_pos hδ f hf hdisj
    let : IsManifold (𝓡 3) ∞ CurvGQ := finiteCapQuotient_isManifold Fact.out transitionEnd_pos hδ f hf hdisj hs
    let : T2Space CurvGQ := finiteCapQuotient_t2Space transitionEnd_pos hδ f hf hdisj
    let : SigmaCompactSpace CurvGQ := finiteCapQuotient_sigmaCompactSpace transitionEnd_pos hδ f hf hdisj
    let : SigmaCompactSpace CurvGRet := isSigmaCompact_iff_sigmaCompactSpace.mp
      (DifferentialGeometry.Geometry.isSigmaCompact_of_isOpen (𝓡 3) (CurvGRet).isOpen)
    let gRet := finiteFullPreparedMetric I hδ f hf hdisj hs U g R hRet c hc x₀ order d₀ hOriginal hrec d hmap hside w
    let F := finiteFullWitnessMap I Fact.out transitionEnd_pos hδ f hf hdisj hs R c hc b
    let Q := metricScalarAt g ((d₀ b.val.1).offsetPoint (cuttingSign_sq b.val.2))
    ∀ (Δ : RealTimeInterval) (S : SolutionOn (I := 𝓡 3) (M := CurvGRet) Δ),
      IsSolutionOn S → S.base.metric 0 = scaleMetric Q (d b).scalar_pos gRet →
      Icc 0 T ⊆ Δ.carrier → Ioo 0 T ⊆ Δ.regular →
      (∀ t ∈ Icc 0 T, ∀ x : CurvGRet,
        Real.sqrt (Tensor0SBundle.normSq0S (S.base.metric t) x 4 (S.base.rm04 t x)) ≤ K) →
      ∀ t ∈ Icc 0 T,
        ENNReal.ofReal (Real.exp (-(27 * K * T))) * (ENNReal.ofReal (1 / 4 : ℝ) *
          riemannianVolumeMeasure (𝓡 3) CurvGE3 metric
            (Metric.closedBall (0 : CurvGE3) (Real.exp (-(9 * K * T)) * ρ / 4))) ≤
        riemannianVolumeMeasure (𝓡 3) CurvGRet (S.base.metric t)
          (riemannianBallOf (S.base.metric t) (F ((w b).data.tip)) ρ) := by
  let : LocallyPathConnectedSpace M := originalModel_locallyPathConnected I Fact.out
  let : ChartedSpace CurvGE3 CurvGQ := finiteCapChartedSpace I Fact.out transitionEnd_pos hδ f hf hdisj
  let : IsManifold (𝓡 3) ∞ CurvGQ := finiteCapQuotient_isManifold Fact.out transitionEnd_pos hδ f hf hdisj hs
  let : T2Space CurvGQ := finiteCapQuotient_t2Space transitionEnd_pos hδ f hf hdisj
  let : SigmaCompactSpace CurvGQ := finiteCapQuotient_sigmaCompactSpace transitionEnd_pos hδ f hf hdisj
  let : SigmaCompactSpace CurvGRet := isSigmaCompact_iff_sigmaCompactSpace.mp
    (DifferentialGeometry.Geometry.isSigmaCompact_of_isOpen (𝓡 3) (CurvGRet).isOpen)
  let gRet := finiteFullPreparedMetric I hδ f hf hdisj hs U g R hRet c hc x₀ order d₀ hOriginal hrec d hmap hside w
  let F := finiteFullWitnessMap I Fact.out transitionEnd_pos hδ f hf hdisj hs R c hc b
  let Q := metricScalarAt g ((d₀ b.val.1).offsetPoint (cuttingSign_sq b.val.2))
  dsimp only
  intro Δ S hS hstart hcarrier hregular hRm t ht
  have hsmall : Real.exp (-(9 * K * T)) * ρ < D := by
    apply lt_of_le_of_lt _ hρD
    have he : Real.exp (-(9 * K * T)) ≤ 1 :=
      Real.exp_le_one_iff.mpr (neg_nonpos.mpr (mul_nonneg (mul_nonneg (by norm_num) hK) hT))
    simpa only [one_mul] using mul_le_mul_of_nonneg_right he hρ.le
  have hv := finiteFullPreparedMetric_normalized_tip_ball_volume_ge I hδ f hf hdisj hs
    U g R hRet c hc x₀ order d₀ hOriginal hrec d hmap hside w b heps
      (mul_pos (Real.exp_pos _) hρ) hsmall
  have hinit : ENNReal.ofReal (1 / 4 : ℝ) *
      riemannianVolumeMeasure (𝓡 3) CurvGE3 metric
        (Metric.closedBall (0 : CurvGE3) (Real.exp (-(9 * K * T)) * ρ / 4)) ≤
      riemannianVolumeMeasure (𝓡 3) CurvGRet (S.base.metric 0)
        (riemannianBallOf (S.base.metric 0) (F ((w b).data.tip))
          (Real.exp (-(9 * K * T)) * ρ)) := by
    rw [hstart]
    exact hv
  have h := riemannianVolumeMeasure_ball_ge_of_initial_volume_and_curvature_bound S hS
    hT hK hcarrier hregular hRm ht (F ((w b).data.tip)) hρ.le (by
      simpa only [show Module.finrank ℝ CurvGE3 = 3 by simp [CurvGE3], Nat.cast_ofNat,
        show (3 : ℝ) ^ 2 = 9 by norm_num] using hinit)
  simpa only [show Module.finrank ℝ CurvGE3 = 3 by simp [CurvGE3], Nat.cast_ofNat,
    show (3 : ℝ) ^ 2 = 9 by norm_num, show (3 : ℝ) ^ 3 = 27 by norm_num] using h

private theorem captured_ball_volume_lower_bound
    {F H' N : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    [FiniteDimensional ℝ F] [TopologicalSpace H'] {J : ModelWithCorners ℝ F H'}
    [TopologicalSpace N] [ChartedSpace H' N] [IsManifold J ∞ N] [T2Space N] [SigmaCompactSpace N]
    (gN : SmoothRiemannianMetric J N) (p q : N) {ρ r : ℝ}
    {v : ℝ≥0∞}
    (hcapture : riemannianEDistOf gN q p + ENNReal.ofReal ρ ≤ ENNReal.ofReal r)
    (hvol : v ≤ riemannianVolumeMeasure J N gN (riemannianBallOf gN p ρ)) :
    v ≤ riemannianVolumeMeasure J N gN (riemannianBallOf gN q r) := by
  apply hvol.trans (measure_mono ?_)
  intro y hy
  have hdist : riemannianEDistOf gN q p ≠ ⊤ :=
    ne_top_of_le_ne_top ENNReal.ofReal_ne_top
      ((le_add_right le_rfl).trans hcapture)
  exact (riemannianEDistOf_triangle gN q p y).trans_lt
    ((ENNReal.add_lt_add_left hdist hy).trans_le hcapture)



private theorem standard_cap_ball_volume_pos {ρ : ℝ} (hρ : 0 < ρ) :
    0 < (riemannianVolumeMeasure (𝓡 3) CurvGE3 metric
      (Metric.closedBall (0 : CurvGE3) ρ)).toReal := by
  let μ := riemannianVolumeMeasure (𝓡 3) CurvGE3 metric
  let _ : μ.IsOpenPosMeasure := riemannianVolumeMeasure_isOpenPosMeasure metric
  let _ : IsFiniteMeasureOnCompacts μ := riemannianVolumeMeasure_isFiniteMeasureOnCompacts metric
  apply ENNReal.toReal_pos
  · apply ne_of_gt
    exact (Metric.isOpen_ball.measure_pos μ ⟨0, Metric.mem_ball_self hρ⟩).trans_le
      (measure_mono Metric.ball_subset_closedBall)
  · exact (isCompact_closedBall (0 : CurvGE3) ρ).measure_ne_top

private theorem cubic_volume_bound_of_le_reserve
    {r R v : ℝ} (hr : 0 ≤ r) (hR : 0 < R) (hrR : r ≤ R) (hv : 0 ≤ v)
    {V : ℝ≥0∞} (hvol : ENNReal.ofReal v ≤ V) :
    ENNReal.ofReal (v / R ^ 3) * ENNReal.ofReal r ^ 3 ≤ V := by
  rw [← ENNReal.ofReal_pow hr, ← ENNReal.ofReal_mul (div_nonneg hv (pow_nonneg hR.le _))]
  apply (ENNReal.ofReal_le_ofReal ?_).trans hvol
  have hpow : r ^ 3 ≤ R ^ 3 := pow_le_pow_left₀ hr hrR 3
  calc
    v / R ^ 3 * r ^ 3 ≤ v / R ^ 3 * R ^ 3 :=
      mul_le_mul_of_nonneg_left hpow (by positivity)
    _ = v := div_mul_cancel₀ _ (pow_ne_zero _ hR.ne')



theorem finiteFullPreparedMetric_captured_tip_ball_volume_ratio_ge [SigmaCompactSpace M]
    (b : CurvGB) (heps : ε ≤ 1 / 2) {ρ Rmax : ℝ}
    (hρ : 0 < ρ) (hρD : ρ < D) (hRmax : 0 < Rmax)
    (T K : ℝ) (hT : 0 ≤ T) (hK : 0 ≤ K) :
    let : LocallyPathConnectedSpace M := originalModel_locallyPathConnected I Fact.out
    let : ChartedSpace CurvGE3 CurvGQ := finiteCapChartedSpace I Fact.out transitionEnd_pos hδ f hf hdisj
    let : IsManifold (𝓡 3) ∞ CurvGQ := finiteCapQuotient_isManifold Fact.out transitionEnd_pos hδ f hf hdisj hs
    let : T2Space CurvGQ := finiteCapQuotient_t2Space transitionEnd_pos hδ f hf hdisj
    let : SigmaCompactSpace CurvGQ := finiteCapQuotient_sigmaCompactSpace transitionEnd_pos hδ f hf hdisj
    let : SigmaCompactSpace CurvGRet := isSigmaCompact_iff_sigmaCompactSpace.mp
      (DifferentialGeometry.Geometry.isSigmaCompact_of_isOpen (𝓡 3) (CurvGRet).isOpen)
    let gRet := finiteFullPreparedMetric I hδ f hf hdisj hs U g R hRet c hc x₀ order d₀ hOriginal hrec d hmap hside w
    let F := finiteFullWitnessMap I Fact.out transitionEnd_pos hδ f hf hdisj hs R c hc b
    let Q := metricScalarAt g ((d₀ b.val.1).offsetPoint (cuttingSign_sq b.val.2))
    let ν := Real.exp (-(27 * K * T)) / 4 *
      (riemannianVolumeMeasure (𝓡 3) CurvGE3 metric
        (Metric.closedBall (0 : CurvGE3) (Real.exp (-(9 * K * T)) * ρ / 4))).toReal / Rmax ^ 3
    0 < ν ∧
    ∀ (Δ : RealTimeInterval) (S : SolutionOn (I := 𝓡 3) (M := CurvGRet) Δ),
      IsSolutionOn S → S.base.metric 0 = scaleMetric Q (d b).scalar_pos gRet →
      Icc 0 T ⊆ Δ.carrier → Ioo 0 T ⊆ Δ.regular →
      (∀ t ∈ Icc 0 T, ∀ x : CurvGRet,
        Real.sqrt (Tensor0SBundle.normSq0S (S.base.metric t) x 4 (S.base.rm04 t x)) ≤ K) →
      ∀ t ∈ Icc 0 T, ∀ q : CurvGRet, ∀ r : ℝ, 0 < r → r ≤ Rmax →
        riemannianEDistOf (S.base.metric t) q (F ((w b).data.tip)) + ENNReal.ofReal ρ ≤
          ENNReal.ofReal r →
        ENNReal.ofReal ν * ENNReal.ofReal r ^ 3 ≤
          riemannianVolumeMeasure (𝓡 3) CurvGRet (S.base.metric t)
            (riemannianBallOf (S.base.metric t) q r) := by
  let : LocallyPathConnectedSpace M := originalModel_locallyPathConnected I Fact.out
  let : ChartedSpace CurvGE3 CurvGQ := finiteCapChartedSpace I Fact.out transitionEnd_pos hδ f hf hdisj
  let : IsManifold (𝓡 3) ∞ CurvGQ := finiteCapQuotient_isManifold Fact.out transitionEnd_pos hδ f hf hdisj hs
  let : T2Space CurvGQ := finiteCapQuotient_t2Space transitionEnd_pos hδ f hf hdisj
  let : SigmaCompactSpace CurvGQ := finiteCapQuotient_sigmaCompactSpace transitionEnd_pos hδ f hf hdisj
  let : SigmaCompactSpace CurvGRet := isSigmaCompact_iff_sigmaCompactSpace.mp
    (DifferentialGeometry.Geometry.isSigmaCompact_of_isOpen (𝓡 3) (CurvGRet).isOpen)
  dsimp only
  let V := riemannianVolumeMeasure (𝓡 3) CurvGE3 metric
    (Metric.closedBall (0 : CurvGE3) (Real.exp (-(9 * K * T)) * ρ / 4))
  have hV : 0 < V.toReal := standard_cap_ball_volume_pos (by positivity)
  have hv : 0 < Real.exp (-(27 * K * T)) / 4 * V.toReal := mul_pos (by positivity) hV
  refine ⟨div_pos hv (pow_pos hRmax 3), ?_⟩
  intro Δ S hS hstart hcarrier hregular hRm t ht q r hr hrR hcapture
  have htip := finiteFullPreparedMetric_tip_ball_volume_ge_on_curvature_controlled_flow
    I hδ f hf hdisj hs U g R hRet c hc x₀ order d₀ hOriginal hrec d hmap hside w
    b heps hρ hρD T K hT hK Δ S hS hstart hcarrier hregular hRm t ht
  have htip' : ENNReal.ofReal (Real.exp (-(27 * K * T)) / 4 * V.toReal) ≤
      riemannianVolumeMeasure (𝓡 3) CurvGRet (S.base.metric t)
        (riemannianBallOf (S.base.metric t)
          ((finiteFullWitnessMap I Fact.out transitionEnd_pos hδ f hf hdisj hs R c hc b)
            ((w b).data.tip)) ρ) := by
    apply le_trans _ htip
    rw [ENNReal.ofReal_mul (by positivity : 0 ≤ Real.exp (-(27 * K * T)) / 4)]
    calc
      _ ≤ ENNReal.ofReal (Real.exp (-(27 * K * T)) / 4) * V :=
        mul_le_mul' le_rfl ENNReal.ofReal_toReal_le
      _ = _ := by
        rw [div_eq_mul_inv, ENNReal.ofReal_mul (Real.exp_pos _).le]
        rw [show (4 : ℝ)⁻¹ = 1 / 4 by norm_num]
        exact mul_assoc _ _ _
  exact cubic_volume_bound_of_le_reserve hr.le hRmax hrR hv.le
    (captured_ball_volume_lower_bound (S.base.metric t) _ q hcapture htip')


section

open DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

theorem finiteFullPreparedMetric_normalized_window_ball_volume_ge
 [SigmaCompactSpace M]
    (b : CurvGB) (heps : ε ≤ 1 / 2) (p : standardCapWindow D)
    {ρ : ℝ} (hρ : 0 < ρ) (hmargin : ‖p.val‖ + ρ < D) :
    let : LocallyPathConnectedSpace M := originalModel_locallyPathConnected I Fact.out
    let : ChartedSpace CurvGE3 CurvGQ := finiteCapChartedSpace I Fact.out transitionEnd_pos hδ f hf hdisj
    let : IsManifold (𝓡 3) ∞ CurvGQ := finiteCapQuotient_isManifold Fact.out transitionEnd_pos hδ f hf hdisj hs
    let : T2Space CurvGQ := finiteCapQuotient_t2Space transitionEnd_pos hδ f hf hdisj
    let : SigmaCompactSpace CurvGQ := finiteCapQuotient_sigmaCompactSpace transitionEnd_pos hδ f hf hdisj
    let : SigmaCompactSpace CurvGRet := isSigmaCompact_iff_sigmaCompactSpace.mp
      (DifferentialGeometry.Geometry.isSigmaCompact_of_isOpen (𝓡 3) (CurvGRet).isOpen)
    let gRet := finiteFullPreparedMetric I hδ f hf hdisj hs U g R hRet c hc x₀ order d₀ hOriginal hrec d hmap hside w
    let F := finiteFullWitnessMap I Fact.out transitionEnd_pos hδ f hf hdisj hs R c hc b
    let Q := metricScalarAt g ((d₀ b.val.1).offsetPoint (cuttingSign_sq b.val.2))
    ENNReal.ofReal (1 / 4 : ℝ) *
      riemannianVolumeMeasure (𝓡 3) CurvGE3 metric (Metric.closedBall p.val (ρ / 4)) ≤
      riemannianVolumeMeasure (𝓡 3) CurvGRet (scaleMetric Q (d b).scalar_pos gRet)
        (riemannianBallOf (scaleMetric Q (d b).scalar_pos gRet) (F ((w b).window p)) ρ) := by
  let : LocallyPathConnectedSpace M := originalModel_locallyPathConnected I Fact.out
  let : ChartedSpace CurvGE3 CurvGQ := finiteCapChartedSpace I Fact.out transitionEnd_pos hδ f hf hdisj
  let : IsManifold (𝓡 3) ∞ CurvGQ := finiteCapQuotient_isManifold Fact.out transitionEnd_pos hδ f hf hdisj hs
  let : T2Space CurvGQ := finiteCapQuotient_t2Space transitionEnd_pos hδ f hf hdisj
  let : SigmaCompactSpace CurvGQ := finiteCapQuotient_sigmaCompactSpace transitionEnd_pos hδ f hf hdisj
  let : SigmaCompactSpace CurvGRet := isSigmaCompact_iff_sigmaCompactSpace.mp
    (DifferentialGeometry.Geometry.isSigmaCompact_of_isOpen (𝓡 3) (CurvGRet).isOpen)
  dsimp only
  let gRet := finiteFullPreparedMetric I hδ f hf hdisj hs U g R hRet c hc x₀ order d₀ hOriginal hrec d hmap hside w
  let F := finiteFullWitnessMap I Fact.out transitionEnd_pos hδ f hf hdisj hs R c hc b
  let Q := metricScalarAt g ((d₀ b.val.1).offsetPoint (cuttingSign_sq b.val.2))
  apply (CanonicalStaticInsertionWitness.normalized_window_ball_volume_ge (w b) heps p hρ hmargin).trans
  apply DifferentialGeometry.Geometry.Measure.riemannianVolumeMeasure_ball_le_of_injective_local_isometry
    (scaleMetric Q (d b).scalar_pos (w b).data.outMetric)
    (scaleMetric Q (d b).scalar_pos gRet) F
    (isLocalDiffeomorph_finiteFullWitnessMap I Fact.out transitionEnd_pos hδ f hf hdisj hs R c hc b)
    (injective_finiteFullWitnessMap I Fact.out transitionEnd_pos hδ f hf hdisj hs R c hc b)
  intro p v z
  rw [scaleMetric_inner, scaleMetric_inner]
  exact congrArg (fun a => Q * a)
    (finiteFullPreparedMetric_witness_inner I hδ f hf hdisj hs U g R hRet c hc
      x₀ order d₀ hOriginal hrec d hmap hside w b p v z).symm



theorem exists_uniform_finiteFullPreparedMetric_window_ball_volume_lower (R₀ : ℝ) :
    ∃ ν : ℝ, 0 < ν ∧
      ∀ {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E],
      ∀ [Fact (Module.finrank ℝ E = 3)] [TopologicalSpace H] (I : ModelWithCorners ℝ E H) [I.Boundaryless],
      ∀ [TopologicalSpace M] [ChartedSpace H M] [T2Space M] [IsManifold I ∞ M] [SigmaCompactSpace M],
      ∀ {ι : Type*} [Finite ι] {precision : ι → ℝ},
      ∀ (hδ : ∀ i, 0 < precision i) (f : ∀ i : ι, bufferedCylinder (precision i) → M),
      ∀ (hf : ∀ i, _root_.Topology.IsOpenEmbedding (f i)),
      ∀ (hdisj : Pairwise (fun i j => Disjoint (range (f i)) (range (f j)))),
      ∀ (hs : ∀ i, IsLocalDiffeomorph CurvGIC I ∞ (f i)),
      ∀ (U : Opens M) (g : SmoothRiemannianMetric I U),
      ∀ (R : Set (ConnectedComponents (cutCore f))),
      ∀ (hRet : MapsTo (Subtype.val : cutCore f → M) (retainedCore f R) U),
      ∀ (c : ℝ) (hc : 4 ≤ c),
      ∀ (x₀ : ι → U) (order : ι → ℕ),
      ∀ (d₀ : ∀ i, normalizedDatum g (x₀ i) (precision i) (order i)),
      ∀ (hOriginal : ∀ i, f i = neckAmbientMap U (d₀ i)),
      ∀ {k' : {b : ι × Bool // cuttingSphereComponent hδ f hf hdisj b ∈ R} → ℕ},
      ∀ (hrec : ∀ b : {b : ι × Bool // cuttingSphereComponent hδ f hf hdisj b ∈ R}, (c * precision b.val.1)⁻¹ + 1 ≤ (precision b.val.1)⁻¹),
      ∀ (d : ∀ b : {b : ι × Bool // cuttingSphereComponent hδ f hf hdisj b ∈ R}, normalizedDatum g
    ((d₀ b.val.1).offsetPoint (cuttingSign_sq b.val.2)) (c * precision b.val.1) (k' b)),
      ∀ (hmap : ∀ b : {b : ι × Bool // cuttingSphereComponent hδ f hf hdisj b ∈ R}, (d b).map = (d₀ b.val.1).recenteringMap (cuttingSign_sq b.val.2) (hrec b)),
      ∀ (hside : ∀ b : {b : ι × Bool // cuttingSphereComponent hδ f hf hdisj b ∈ R}, (d b).retainedSide = true),
      ∀ {A D ε : ℝ} {hA : 0 < A} {m : ℕ},
      ∀ (w : ∀ b : {b : ι × Bool // cuttingSphereComponent hδ f hf hdisj b ∈ R}, CanonicalStaticInsertionWitness (d b) A hA D m ε),
      ∀ b : {b : ι × Bool // cuttingSphereComponent hδ f hf hdisj b ∈ R}, ε ≤ 1 / 2 →
      let : LocallyPathConnectedSpace M := originalModel_locallyPathConnected I Fact.out
      let : ChartedSpace CurvGE3 (FiniteCapQuotient transitionEnd_pos hδ f (fun i => (hf i).injective) hdisj) := finiteCapChartedSpace I Fact.out transitionEnd_pos hδ f hf hdisj
      let : IsManifold (𝓡 3) ∞ (FiniteCapQuotient transitionEnd_pos hδ f (fun i => (hf i).injective) hdisj) := finiteCapQuotient_isManifold Fact.out transitionEnd_pos hδ f hf hdisj hs
      let : T2Space (FiniteCapQuotient transitionEnd_pos hδ f (fun i => (hf i).injective) hdisj) := finiteCapQuotient_t2Space transitionEnd_pos hδ f hf hdisj
      let : SigmaCompactSpace (FiniteCapQuotient transitionEnd_pos hδ f (fun i => (hf i).injective) hdisj) := finiteCapQuotient_sigmaCompactSpace transitionEnd_pos hδ f hf hdisj
      let : SigmaCompactSpace (finiteCapRetained transitionEnd_pos hδ f hf hdisj R) := isSigmaCompact_iff_sigmaCompactSpace.mp
        (DifferentialGeometry.Geometry.isSigmaCompact_of_isOpen (𝓡 3) ((finiteCapRetained transitionEnd_pos hδ f hf hdisj R)).isOpen)
      let gRet := finiteFullPreparedMetric I hδ f hf hdisj hs U g R hRet c hc x₀ order d₀ hOriginal hrec d hmap hside w
      let F := finiteFullWitnessMap I Fact.out transitionEnd_pos hδ f hf hdisj hs R c hc b
      let Q := metricScalarAt g ((d₀ b.val.1).offsetPoint (cuttingSign_sq b.val.2))
      ∀ p : standardCapWindow D, ‖p.val‖ ≤ R₀ → ∀ r : ℝ, 0 < r → r ≤ 1 → ‖p.val‖ + r < D →
        ENNReal.ofReal ν * ENNReal.ofReal r ^ 3 ≤
          riemannianVolumeMeasure (𝓡 3) (finiteCapRetained transitionEnd_pos hδ f hf hdisj R) (scaleMetric Q (d b).scalar_pos gRet)
            (riemannianBallOf (scaleMetric Q (d b).scalar_pos gRet) (F ((w b).window p)) r) := by
  obtain ⟨ν, hν, hνbound⟩ := exists_uniform_normalized_window_ball_volume_lower R₀
  refine ⟨ν, hν, ?_⟩
  intro E H M _ _ _ _ _ I _ _ _ _ _ _ ι _ precision hδ f hf hdisj hs U g R hRet c hc x₀ order d₀ hOriginal k' hrec d hmap hside A D ε hA m w b heps
  let : LocallyPathConnectedSpace M := originalModel_locallyPathConnected I Fact.out
  let : ChartedSpace CurvGE3 (FiniteCapQuotient transitionEnd_pos hδ f (fun i => (hf i).injective) hdisj) := finiteCapChartedSpace I Fact.out transitionEnd_pos hδ f hf hdisj
  let : IsManifold (𝓡 3) ∞ (FiniteCapQuotient transitionEnd_pos hδ f (fun i => (hf i).injective) hdisj) := finiteCapQuotient_isManifold Fact.out transitionEnd_pos hδ f hf hdisj hs
  let : T2Space (FiniteCapQuotient transitionEnd_pos hδ f (fun i => (hf i).injective) hdisj) := finiteCapQuotient_t2Space transitionEnd_pos hδ f hf hdisj
  let : SigmaCompactSpace (FiniteCapQuotient transitionEnd_pos hδ f (fun i => (hf i).injective) hdisj) := finiteCapQuotient_sigmaCompactSpace transitionEnd_pos hδ f hf hdisj
  let : SigmaCompactSpace (finiteCapRetained transitionEnd_pos hδ f hf hdisj R) := isSigmaCompact_iff_sigmaCompactSpace.mp
    (DifferentialGeometry.Geometry.isSigmaCompact_of_isOpen (𝓡 3) ((finiteCapRetained transitionEnd_pos hδ f hf hdisj R)).isOpen)
  dsimp only
  intro p hp r hr hr1 hmargin
  let gRet := finiteFullPreparedMetric I hδ f hf hdisj hs U g R hRet c hc x₀ order d₀ hOriginal hrec d hmap hside w
  let F := finiteFullWitnessMap I Fact.out transitionEnd_pos hδ f hf hdisj hs R c hc b
  let Q := metricScalarAt g ((d₀ b.val.1).offsetPoint (cuttingSign_sq b.val.2))
  apply (hνbound (w b) heps p hp r hr hr1 hmargin).trans
  apply DifferentialGeometry.Geometry.Measure.riemannianVolumeMeasure_ball_le_of_injective_local_isometry
    (scaleMetric Q (d b).scalar_pos (w b).data.outMetric)
    (scaleMetric Q (d b).scalar_pos gRet) F
    (isLocalDiffeomorph_finiteFullWitnessMap I Fact.out transitionEnd_pos hδ f hf hdisj hs R c hc b)
    (injective_finiteFullWitnessMap I Fact.out transitionEnd_pos hδ f hf hdisj hs R c hc b)
  intro p v z
  rw [scaleMetric_inner, scaleMetric_inner]
  exact congrArg (fun a => Q * a)
    (finiteFullPreparedMetric_witness_inner I hδ f hf hdisj hs U g R hRet c hc
      x₀ order d₀ hOriginal hrec d hmap hside w b p v z).symm


end

section

open DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

theorem exists_uniform_finiteFullPreparedMetric_window_ball_volume_lower_on_flow (R₀ : ℝ) :
    ∃ ν : ℝ, 0 < ν ∧
      ∀ {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E],
      ∀ [Fact (Module.finrank ℝ E = 3)] [TopologicalSpace H] (I : ModelWithCorners ℝ E H) [I.Boundaryless],
      ∀ [TopologicalSpace M] [ChartedSpace H M] [T2Space M] [IsManifold I ∞ M] [SigmaCompactSpace M],
      ∀ {ι : Type*} [Finite ι] {precision : ι → ℝ},
      ∀ (hδ : ∀ i, 0 < precision i) (f : ∀ i : ι, bufferedCylinder (precision i) → M),
      ∀ (hf : ∀ i, _root_.Topology.IsOpenEmbedding (f i)),
      ∀ (hdisj : Pairwise (fun i j => Disjoint (range (f i)) (range (f j)))),
      ∀ (hs : ∀ i, IsLocalDiffeomorph CurvGIC I ∞ (f i)),
      ∀ (U : Opens M) (g : SmoothRiemannianMetric I U),
      ∀ (R : Set (ConnectedComponents (cutCore f))),
      ∀ (hRet : MapsTo (Subtype.val : cutCore f → M) (retainedCore f R) U),
      ∀ (c : ℝ) (hc : 4 ≤ c),
      ∀ (x₀ : ι → U) (order : ι → ℕ),
      ∀ (d₀ : ∀ i, normalizedDatum g (x₀ i) (precision i) (order i)),
      ∀ (hOriginal : ∀ i, f i = neckAmbientMap U (d₀ i)),
      ∀ {k' : {b : ι × Bool // cuttingSphereComponent hδ f hf hdisj b ∈ R} → ℕ},
      ∀ (hrec : ∀ b : {b : ι × Bool // cuttingSphereComponent hδ f hf hdisj b ∈ R}, (c * precision b.val.1)⁻¹ + 1 ≤ (precision b.val.1)⁻¹),
      ∀ (d : ∀ b : {b : ι × Bool // cuttingSphereComponent hδ f hf hdisj b ∈ R}, normalizedDatum g
    ((d₀ b.val.1).offsetPoint (cuttingSign_sq b.val.2)) (c * precision b.val.1) (k' b)),
      ∀ (hmap : ∀ b : {b : ι × Bool // cuttingSphereComponent hδ f hf hdisj b ∈ R}, (d b).map = (d₀ b.val.1).recenteringMap (cuttingSign_sq b.val.2) (hrec b)),
      ∀ (hside : ∀ b : {b : ι × Bool // cuttingSphereComponent hδ f hf hdisj b ∈ R}, (d b).retainedSide = true),
      ∀ {A D ε : ℝ} {hA : 0 < A} {m : ℕ},
      ∀ (w : ∀ b : {b : ι × Bool // cuttingSphereComponent hδ f hf hdisj b ∈ R}, CanonicalStaticInsertionWitness (d b) A hA D m ε),
      ∀ b : {b : ι × Bool // cuttingSphereComponent hδ f hf hdisj b ∈ R}, ε ≤ 1 / 2 →
      let : LocallyPathConnectedSpace M := originalModel_locallyPathConnected I Fact.out
      let : ChartedSpace CurvGE3 (FiniteCapQuotient transitionEnd_pos hδ f (fun i => (hf i).injective) hdisj) := finiteCapChartedSpace I Fact.out transitionEnd_pos hδ f hf hdisj
      let : IsManifold (𝓡 3) ∞ (FiniteCapQuotient transitionEnd_pos hδ f (fun i => (hf i).injective) hdisj) := finiteCapQuotient_isManifold Fact.out transitionEnd_pos hδ f hf hdisj hs
      let : T2Space (FiniteCapQuotient transitionEnd_pos hδ f (fun i => (hf i).injective) hdisj) := finiteCapQuotient_t2Space transitionEnd_pos hδ f hf hdisj
      let : SigmaCompactSpace (FiniteCapQuotient transitionEnd_pos hδ f (fun i => (hf i).injective) hdisj) := finiteCapQuotient_sigmaCompactSpace transitionEnd_pos hδ f hf hdisj
      let : SigmaCompactSpace (finiteCapRetained transitionEnd_pos hδ f hf hdisj R) := isSigmaCompact_iff_sigmaCompactSpace.mp
        (DifferentialGeometry.Geometry.isSigmaCompact_of_isOpen (𝓡 3) ((finiteCapRetained transitionEnd_pos hδ f hf hdisj R)).isOpen)
      let gRet := finiteFullPreparedMetric I hδ f hf hdisj hs U g R hRet c hc x₀ order d₀ hOriginal hrec d hmap hside w
      let F := finiteFullWitnessMap I Fact.out transitionEnd_pos hδ f hf hdisj hs R c hc b
      let Q := metricScalarAt g ((d₀ b.val.1).offsetPoint (cuttingSign_sq b.val.2))
      ∀ (Δ : RealTimeInterval) (S : SolutionOn (I := 𝓡 3)
        (M := finiteCapRetained transitionEnd_pos hδ f hf hdisj R) Δ),
        IsSolutionOn S → S.base.metric 0 = scaleMetric Q (d b).scalar_pos gRet →
      ∀ T K : ℝ, 0 ≤ T → 0 ≤ K → Icc 0 T ⊆ Δ.carrier → Ioo 0 T ⊆ Δ.regular →
        (∀ t ∈ Icc 0 T, ∀ x : finiteCapRetained transitionEnd_pos hδ f hf hdisj R,
          Real.sqrt (Tensor0SBundle.normSq0S (S.base.metric t) x 4 (S.base.rm04 t x)) ≤ K) →
      ∀ t ∈ Icc 0 T, ∀ p : standardCapWindow D, ‖p.val‖ ≤ R₀ →
      ∀ r : ℝ, 0 < r → r ≤ 1 → ‖p.val‖ + r < D →
        ENNReal.ofReal (Real.exp (-(54 * K * T)) * ν) * ENNReal.ofReal r ^ 3 ≤
          riemannianVolumeMeasure (𝓡 3) (finiteCapRetained transitionEnd_pos hδ f hf hdisj R)
            (S.base.metric t) (riemannianBallOf (S.base.metric t) (F ((w b).window p)) r) := by
  obtain ⟨ν, hν, hνbound⟩ := exists_uniform_finiteFullPreparedMetric_window_ball_volume_lower R₀
  refine ⟨ν, hν, ?_⟩
  intro E H M _ _ _ _ _ I _ _ _ _ _ _ ι _ precision hδ f hf hdisj hs U g R hRet c hc x₀ order d₀ hOriginal k' hrec d hmap hside A D ε hA m w b heps
  let : LocallyPathConnectedSpace M := originalModel_locallyPathConnected I Fact.out
  let : ChartedSpace CurvGE3 (FiniteCapQuotient transitionEnd_pos hδ f (fun i => (hf i).injective) hdisj) :=
    finiteCapChartedSpace I Fact.out transitionEnd_pos hδ f hf hdisj
  let : IsManifold (𝓡 3) ∞ (FiniteCapQuotient transitionEnd_pos hδ f (fun i => (hf i).injective) hdisj) :=
    finiteCapQuotient_isManifold Fact.out transitionEnd_pos hδ f hf hdisj hs
  let : T2Space (FiniteCapQuotient transitionEnd_pos hδ f (fun i => (hf i).injective) hdisj) :=
    finiteCapQuotient_t2Space transitionEnd_pos hδ f hf hdisj
  let : SigmaCompactSpace (FiniteCapQuotient transitionEnd_pos hδ f (fun i => (hf i).injective) hdisj) :=
    finiteCapQuotient_sigmaCompactSpace transitionEnd_pos hδ f hf hdisj
  let : SigmaCompactSpace (finiteCapRetained transitionEnd_pos hδ f hf hdisj R) := isSigmaCompact_iff_sigmaCompactSpace.mp
    (DifferentialGeometry.Geometry.isSigmaCompact_of_isOpen (𝓡 3) (finiteCapRetained transitionEnd_pos hδ f hf hdisj R).isOpen)
  dsimp only
  intro Δ S hS hstart T K hT hK hcarrier hregular hRm t ht p hp r hr hr1 hmargin
  let F := finiteFullWitnessMap I Fact.out transitionEnd_pos hδ f hf hdisj hs R c hc b
  have hinitial : ∀ ρ : ℝ, 0 < ρ → ρ ≤ r →
      ENNReal.ofReal ν * ENNReal.ofReal ρ ^ Module.finrank ℝ CurvGE3 ≤
        riemannianVolumeMeasure (𝓡 3) (finiteCapRetained transitionEnd_pos hδ f hf hdisj R)
          (S.base.metric 0) (riemannianBallOf (S.base.metric 0) (F ((w b).window p)) ρ) := by
    intro ρ hρ hρr
    rw [hstart]
    have hmargin' : ‖p.val‖ + ρ < D := (add_le_add_right hρr _).trans_lt hmargin
    simpa only [show Module.finrank ℝ CurvGE3 = 3 by simp [CurvGE3]] using
      hνbound I hδ f hf hdisj hs U g R hRet c hc x₀ order d₀ hOriginal hrec d hmap hside w b heps
        p hp ρ hρ (hρr.trans hr1) hmargin'
  have hv := riemannianVolumeMeasure_ball_ge_of_initial_volume_ratio_and_curvature_bound
    S hS hT hK hcarrier hregular hRm ht (F ((w b).window p)) hinitial hr le_rfl
  simpa only [show Module.finrank ℝ CurvGE3 = 3 by simp [CurvGE3], Nat.cast_ofNat,
    show 2 * (3 : ℝ)^3 = 54 by norm_num] using hv

theorem exists_uniform_finiteFullPreparedMetric_cap_ball_volume_lower :
    ∃ ν : ℝ, 0 < ν ∧
      ∀ {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E],
      ∀ [Fact (Module.finrank ℝ E = 3)] [TopologicalSpace H] (I : ModelWithCorners ℝ E H) [I.Boundaryless],
      ∀ [TopologicalSpace M] [ChartedSpace H M] [T2Space M] [IsManifold I ∞ M] [SigmaCompactSpace M],
      ∀ {ι : Type*} [Finite ι] {precision : ι → ℝ},
      ∀ (hδ : ∀ i, 0 < precision i) (f : ∀ i : ι, bufferedCylinder (precision i) → M),
      ∀ (hf : ∀ i, _root_.Topology.IsOpenEmbedding (f i)),
      ∀ (hdisj : Pairwise (fun i j => Disjoint (range (f i)) (range (f j)))),
      ∀ (hs : ∀ i, IsLocalDiffeomorph CurvGIC I ∞ (f i)),
      ∀ (U : Opens M) (g : SmoothRiemannianMetric I U),
      ∀ (R : Set (ConnectedComponents (cutCore f))),
      ∀ (hRet : MapsTo (Subtype.val : cutCore f → M) (retainedCore f R) U),
      ∀ (c : ℝ) (hc : 4 ≤ c),
      ∀ (x₀ : ι → U) (order : ι → ℕ),
      ∀ (d₀ : ∀ i, normalizedDatum g (x₀ i) (precision i) (order i)),
      ∀ (hOriginal : ∀ i, f i = neckAmbientMap U (d₀ i)),
      ∀ {k' : {b : ι × Bool // cuttingSphereComponent hδ f hf hdisj b ∈ R} → ℕ},
      ∀ (hrec : ∀ b : {b : ι × Bool // cuttingSphereComponent hδ f hf hdisj b ∈ R}, (c * precision b.val.1)⁻¹ + 1 ≤ (precision b.val.1)⁻¹),
      ∀ (d : ∀ b : {b : ι × Bool // cuttingSphereComponent hδ f hf hdisj b ∈ R}, normalizedDatum g
    ((d₀ b.val.1).offsetPoint (cuttingSign_sq b.val.2)) (c * precision b.val.1) (k' b)),
      ∀ (hmap : ∀ b : {b : ι × Bool // cuttingSphereComponent hδ f hf hdisj b ∈ R}, (d b).map = (d₀ b.val.1).recenteringMap (cuttingSign_sq b.val.2) (hrec b)),
      ∀ (hside : ∀ b : {b : ι × Bool // cuttingSphereComponent hδ f hf hdisj b ∈ R}, (d b).retainedSide = true),
      ∀ {A D ε : ℝ} {hA : 0 < A} {m : ℕ},
      ∀ (w : ∀ b : {b : ι × Bool // cuttingSphereComponent hδ f hf hdisj b ∈ R}, CanonicalStaticInsertionWitness (d b) A hA D m ε),
      ε ≤ 1 / 2 → transitionEnd < D →
      let : LocallyPathConnectedSpace M := originalModel_locallyPathConnected I Fact.out
      let : ChartedSpace CurvGE3 (FiniteCapQuotient transitionEnd_pos hδ f (fun i => (hf i).injective) hdisj) := finiteCapChartedSpace I Fact.out transitionEnd_pos hδ f hf hdisj
      let : IsManifold (𝓡 3) ∞ (FiniteCapQuotient transitionEnd_pos hδ f (fun i => (hf i).injective) hdisj) := finiteCapQuotient_isManifold Fact.out transitionEnd_pos hδ f hf hdisj hs
      let : T2Space (FiniteCapQuotient transitionEnd_pos hδ f (fun i => (hf i).injective) hdisj) := finiteCapQuotient_t2Space transitionEnd_pos hδ f hf hdisj
      let : SigmaCompactSpace (FiniteCapQuotient transitionEnd_pos hδ f (fun i => (hf i).injective) hdisj) := finiteCapQuotient_sigmaCompactSpace transitionEnd_pos hδ f hf hdisj
      let : SigmaCompactSpace (finiteCapRetained transitionEnd_pos hδ f hf hdisj R) := isSigmaCompact_iff_sigmaCompactSpace.mp
        (DifferentialGeometry.Geometry.isSigmaCompact_of_isOpen (𝓡 3) (finiteCapRetained transitionEnd_pos hδ f hf hdisj R).isOpen)
      let gRet := finiteFullPreparedMetric I hδ f hf hdisj hs U g R hRet c hc x₀ order d₀ hOriginal hrec d hmap hside w
      ∀ q : finiteCapRetained transitionEnd_pos hδ f hf hdisj R,
        q ∉ interior (range (finiteRetainedCoreInclusion transitionEnd_pos hδ f hf hdisj R)) →
      ∃ b : {b : ι × Bool // cuttingSphereComponent hδ f hf hdisj b ∈ R},
        ∃ x : standardCapWindow D, ‖x.val‖ ≤ transitionEnd ∧
          finiteFullWitnessMap I Fact.out transitionEnd_pos hδ f hf hdisj hs R c hc b
            ((w b).window x) = q ∧
          let Q := metricScalarAt g ((d₀ b.val.1).offsetPoint (cuttingSign_sq b.val.2))
          ∀ r : ℝ, 0 < r → r ≤ 1 → r < D - transitionEnd →
            ENNReal.ofReal ν * ENNReal.ofReal r ^ 3 ≤
              riemannianVolumeMeasure (𝓡 3) (finiteCapRetained transitionEnd_pos hδ f hf hdisj R)
                (scaleMetric Q (d b).scalar_pos gRet)
                (riemannianBallOf (scaleMetric Q (d b).scalar_pos gRet) q r) := by
  obtain ⟨ν, hν, hvolume⟩ := exists_uniform_finiteFullPreparedMetric_window_ball_volume_lower transitionEnd
  refine ⟨ν, hν, ?_⟩
  intro E H M _ _ _ _ _ I _ _ _ _ _ _ ι _ precision hδ f hf hdisj hs U g R hRet c hc x₀ order d₀ hOriginal k' hrec d hmap hside A D ε hA m w heps hD
  let : LocallyPathConnectedSpace M := originalModel_locallyPathConnected I Fact.out
  let : ChartedSpace CurvGE3 (FiniteCapQuotient transitionEnd_pos hδ f (fun i => (hf i).injective) hdisj) :=
    finiteCapChartedSpace I Fact.out transitionEnd_pos hδ f hf hdisj
  let : IsManifold (𝓡 3) ∞ (FiniteCapQuotient transitionEnd_pos hδ f (fun i => (hf i).injective) hdisj) :=
    finiteCapQuotient_isManifold Fact.out transitionEnd_pos hδ f hf hdisj hs
  let : T2Space (FiniteCapQuotient transitionEnd_pos hδ f (fun i => (hf i).injective) hdisj) :=
    finiteCapQuotient_t2Space transitionEnd_pos hδ f hf hdisj
  let : SigmaCompactSpace (FiniteCapQuotient transitionEnd_pos hδ f (fun i => (hf i).injective) hdisj) :=
    finiteCapQuotient_sigmaCompactSpace transitionEnd_pos hδ f hf hdisj
  let : SigmaCompactSpace (finiteCapRetained transitionEnd_pos hδ f hf hdisj R) := isSigmaCompact_iff_sigmaCompactSpace.mp
    (DifferentialGeometry.Geometry.isSigmaCompact_of_isOpen (𝓡 3) (finiteCapRetained transitionEnd_pos hδ f hf hdisj R).isOpen)
  dsimp only
  intro q hq
  obtain ⟨b, x, hx, himage⟩ := finiteFullWitnessMap_exists_window_preimage_of_notMem_retainedInterior
    I hδ f hf hdisj hs R c hc U g (fun b => (d₀ b.val.1).offsetPoint (cuttingSign_sq b.val.2))
      k' d w (by linarith) q hq
  refine ⟨b, x, hx, himage, ?_⟩
  intro r hr hr1 hrD
  have hm : ‖x.val‖ + r < D := by linarith
  rw [← himage]
  exact hvolume I hδ f hf hdisj hs U g R hRet c hc x₀ order d₀ hOriginal hrec d hmap hside w
    b heps x hx r hr hr1 hm

end

section

open DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

theorem exists_uniform_finiteFullPreparedMetric_window_ball_volume_lower_unscaled (R₀ : ℝ) :
    ∃ ν : ℝ, 0 < ν ∧
      ∀ {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E],
      ∀ [Fact (Module.finrank ℝ E = 3)] [TopologicalSpace H] (I : ModelWithCorners ℝ E H) [I.Boundaryless],
      ∀ [TopologicalSpace M] [ChartedSpace H M] [T2Space M] [IsManifold I ∞ M] [SigmaCompactSpace M],
      ∀ {ι : Type*} [Finite ι] {precision : ι → ℝ},
      ∀ (hδ : ∀ i, 0 < precision i) (f : ∀ i : ι, bufferedCylinder (precision i) → M),
      ∀ (hf : ∀ i, _root_.Topology.IsOpenEmbedding (f i)),
      ∀ (hdisj : Pairwise (fun i j => Disjoint (range (f i)) (range (f j)))),
      ∀ (hs : ∀ i, IsLocalDiffeomorph CurvGIC I ∞ (f i)),
      ∀ (U : Opens M) (g : SmoothRiemannianMetric I U),
      ∀ (R : Set (ConnectedComponents (cutCore f))),
      ∀ (hRet : MapsTo (Subtype.val : cutCore f → M) (retainedCore f R) U),
      ∀ (c : ℝ) (hc : 4 ≤ c),
      ∀ (x₀ : ι → U) (order : ι → ℕ),
      ∀ (d₀ : ∀ i, normalizedDatum g (x₀ i) (precision i) (order i)),
      ∀ (hOriginal : ∀ i, f i = neckAmbientMap U (d₀ i)),
      ∀ {k' : {b : ι × Bool // cuttingSphereComponent hδ f hf hdisj b ∈ R} → ℕ},
      ∀ (hrec : ∀ b : {b : ι × Bool // cuttingSphereComponent hδ f hf hdisj b ∈ R}, (c * precision b.val.1)⁻¹ + 1 ≤ (precision b.val.1)⁻¹),
      ∀ (d : ∀ b : {b : ι × Bool // cuttingSphereComponent hδ f hf hdisj b ∈ R}, normalizedDatum g
    ((d₀ b.val.1).offsetPoint (cuttingSign_sq b.val.2)) (c * precision b.val.1) (k' b)),
      ∀ (hmap : ∀ b : {b : ι × Bool // cuttingSphereComponent hδ f hf hdisj b ∈ R}, (d b).map = (d₀ b.val.1).recenteringMap (cuttingSign_sq b.val.2) (hrec b)),
      ∀ (hside : ∀ b : {b : ι × Bool // cuttingSphereComponent hδ f hf hdisj b ∈ R}, (d b).retainedSide = true),
      ∀ {A D ε : ℝ} {hA : 0 < A} {m : ℕ},
      ∀ (w : ∀ b : {b : ι × Bool // cuttingSphereComponent hδ f hf hdisj b ∈ R}, CanonicalStaticInsertionWitness (d b) A hA D m ε),
      ∀ b : {b : ι × Bool // cuttingSphereComponent hδ f hf hdisj b ∈ R}, ε ≤ 1 / 2 →
      let : LocallyPathConnectedSpace M := originalModel_locallyPathConnected I Fact.out
      let : ChartedSpace CurvGE3 (FiniteCapQuotient transitionEnd_pos hδ f (fun i => (hf i).injective) hdisj) := finiteCapChartedSpace I Fact.out transitionEnd_pos hδ f hf hdisj
      let : IsManifold (𝓡 3) ∞ (FiniteCapQuotient transitionEnd_pos hδ f (fun i => (hf i).injective) hdisj) := finiteCapQuotient_isManifold Fact.out transitionEnd_pos hδ f hf hdisj hs
      let : T2Space (FiniteCapQuotient transitionEnd_pos hδ f (fun i => (hf i).injective) hdisj) := finiteCapQuotient_t2Space transitionEnd_pos hδ f hf hdisj
      let : SigmaCompactSpace (FiniteCapQuotient transitionEnd_pos hδ f (fun i => (hf i).injective) hdisj) := finiteCapQuotient_sigmaCompactSpace transitionEnd_pos hδ f hf hdisj
      let : SigmaCompactSpace (finiteCapRetained transitionEnd_pos hδ f hf hdisj R) := isSigmaCompact_iff_sigmaCompactSpace.mp
        (DifferentialGeometry.Geometry.isSigmaCompact_of_isOpen (𝓡 3) ((finiteCapRetained transitionEnd_pos hδ f hf hdisj R)).isOpen)
      let gRet := finiteFullPreparedMetric I hδ f hf hdisj hs U g R hRet c hc x₀ order d₀ hOriginal hrec d hmap hside w
      let F := finiteFullWitnessMap I Fact.out transitionEnd_pos hδ f hf hdisj hs R c hc b
      let Q := metricScalarAt g ((d₀ b.val.1).offsetPoint (cuttingSign_sq b.val.2))
      ∀ p : standardCapWindow D, ‖p.val‖ ≤ R₀ → ∀ r : ℝ, 0 < r → Real.sqrt Q * r ≤ 1 → ‖p.val‖ + Real.sqrt Q * r < D →
        ENNReal.ofReal ν * ENNReal.ofReal r ^ 3 ≤
          riemannianVolumeMeasure (𝓡 3) (finiteCapRetained transitionEnd_pos hδ f hf hdisj R) gRet
            (riemannianBallOf gRet (F ((w b).window p)) r) := by
  obtain ⟨ν, hν, hvolume⟩ := exists_uniform_finiteFullPreparedMetric_window_ball_volume_lower R₀
  refine ⟨ν, hν, ?_⟩
  intro E H M _ _ _ _ _ I _ _ _ _ _ _ ι _ precision hδ f hf hdisj hs U g R hRet c hc x₀ order d₀ hOriginal k' hrec d hmap hside A D ε hA m w b heps
  let : LocallyPathConnectedSpace M := originalModel_locallyPathConnected I Fact.out
  let : ChartedSpace CurvGE3 (FiniteCapQuotient transitionEnd_pos hδ f (fun i => (hf i).injective) hdisj) :=
    finiteCapChartedSpace I Fact.out transitionEnd_pos hδ f hf hdisj
  let : IsManifold (𝓡 3) ∞ (FiniteCapQuotient transitionEnd_pos hδ f (fun i => (hf i).injective) hdisj) :=
    finiteCapQuotient_isManifold Fact.out transitionEnd_pos hδ f hf hdisj hs
  let : T2Space (FiniteCapQuotient transitionEnd_pos hδ f (fun i => (hf i).injective) hdisj) :=
    finiteCapQuotient_t2Space transitionEnd_pos hδ f hf hdisj
  let : SigmaCompactSpace (FiniteCapQuotient transitionEnd_pos hδ f (fun i => (hf i).injective) hdisj) :=
    finiteCapQuotient_sigmaCompactSpace transitionEnd_pos hδ f hf hdisj
  let : SigmaCompactSpace (finiteCapRetained transitionEnd_pos hδ f hf hdisj R) := isSigmaCompact_iff_sigmaCompactSpace.mp
    (DifferentialGeometry.Geometry.isSigmaCompact_of_isOpen (𝓡 3) (finiteCapRetained transitionEnd_pos hδ f hf hdisj R).isOpen)
  dsimp only
  intro p hp r hr hr1 hmargin
  let gRet := finiteFullPreparedMetric I hδ f hf hdisj hs U g R hRet c hc x₀ order d₀ hOriginal hrec d hmap hside w
  let F := finiteFullWitnessMap I Fact.out transitionEnd_pos hδ f hf hdisj hs R c hc b
  let Q := metricScalarAt g ((d₀ b.val.1).offsetPoint (cuttingSign_sq b.val.2))
  have hsqrt : 0 < Real.sqrt Q := Real.sqrt_pos.mpr (d b).scalar_pos
  have hv := hvolume I hδ f hf hdisj hs U g R hRet c hc x₀ order d₀ hOriginal hrec d hmap hside w b heps
    p hp (Real.sqrt Q * r) (mul_pos hsqrt hr) hr1 hmargin
  have hdim : Module.finrank ℝ CurvGE3 = 3 := by simp [CurvGE3]
  simpa only [hdim] using (DifferentialGeometry.Geometry.Measure.riemannianVolumeMeasure_ball_ge_scaleMetric_iff
    gRet Q (d b).scalar_pos (F ((w b).window p)) r (ENNReal.ofReal ν)).mp (by simpa only [hdim] using hv)


theorem exists_uniform_finiteFullPreparedMetric_ball_volume_lower_or_retained_ball :
    ∃ δ ν : ℝ, 0 < δ ∧ 0 < ν ∧
      ∀ {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E],
      ∀ [Fact (Module.finrank ℝ E = 3)] [TopologicalSpace H] (I : ModelWithCorners ℝ E H) [I.Boundaryless],
      ∀ [TopologicalSpace M] [ChartedSpace H M] [T2Space M] [IsManifold I ∞ M] [SigmaCompactSpace M],
      ∀ {ι : Type*} [Finite ι] {precision : ι → ℝ},
      ∀ (hδ : ∀ i, 0 < precision i) (f : ∀ i : ι, bufferedCylinder (precision i) → M),
      ∀ (hf : ∀ i, _root_.Topology.IsOpenEmbedding (f i)),
      ∀ (hdisj : Pairwise (fun i j => Disjoint (range (f i)) (range (f j)))),
      ∀ (hs : ∀ i, IsLocalDiffeomorph CurvGIC I ∞ (f i)),
      ∀ (U : Opens M) (g : SmoothRiemannianMetric I U),
      ∀ (R : Set (ConnectedComponents (cutCore f))),
      ∀ (hRet : MapsTo (Subtype.val : cutCore f → M) (retainedCore f R) U),
      ∀ (c : ℝ) (hc : 4 ≤ c),
      ∀ (x₀ : ι → U) (order : ι → ℕ),
      ∀ (d₀ : ∀ i, normalizedDatum g (x₀ i) (precision i) (order i)),
      ∀ (hOriginal : ∀ i, f i = neckAmbientMap U (d₀ i)),
      ∀ {k' : {b : ι × Bool // cuttingSphereComponent hδ f hf hdisj b ∈ R} → ℕ},
      ∀ (hrec : ∀ b : {b : ι × Bool // cuttingSphereComponent hδ f hf hdisj b ∈ R}, (c * precision b.val.1)⁻¹ + 1 ≤ (precision b.val.1)⁻¹),
      ∀ (d : ∀ b : {b : ι × Bool // cuttingSphereComponent hδ f hf hdisj b ∈ R}, normalizedDatum g
    ((d₀ b.val.1).offsetPoint (cuttingSign_sq b.val.2)) (c * precision b.val.1) (k' b)),
      ∀ (hmap : ∀ b : {b : ι × Bool // cuttingSphereComponent hδ f hf hdisj b ∈ R}, (d b).map = (d₀ b.val.1).recenteringMap (cuttingSign_sq b.val.2) (hrec b)),
      ∀ (hside : ∀ b : {b : ι × Bool // cuttingSphereComponent hδ f hf hdisj b ∈ R}, (d b).retainedSide = true),
      ∀ {A D ε : ℝ} {hA : 0 < A} {m : ℕ},
      ∀ (w : ∀ b : {b : ι × Bool // cuttingSphereComponent hδ f hf hdisj b ∈ R}, CanonicalStaticInsertionWitness (d b) A hA D m ε),
      ε ≤ 1 / 2 → transitionEnd + 2 < D →
      let : LocallyPathConnectedSpace M := originalModel_locallyPathConnected I Fact.out
      let Qcap := FiniteCapQuotient transitionEnd_pos hδ f (fun i => (hf i).injective) hdisj
      let : ChartedSpace CurvGE3 Qcap := finiteCapChartedSpace I Fact.out transitionEnd_pos hδ f hf hdisj
      let : IsManifold (𝓡 3) ∞ Qcap := finiteCapQuotient_isManifold Fact.out transitionEnd_pos hδ f hf hdisj hs
      let : T2Space Qcap := finiteCapQuotient_t2Space transitionEnd_pos hδ f hf hdisj
      let : SigmaCompactSpace Qcap := finiteCapQuotient_sigmaCompactSpace transitionEnd_pos hδ f hf hdisj
      let : SigmaCompactSpace (finiteCapRetained transitionEnd_pos hδ f hf hdisj R) := isSigmaCompact_iff_sigmaCompactSpace.mp
        (DifferentialGeometry.Geometry.isSigmaCompact_of_isOpen (𝓡 3) (finiteCapRetained transitionEnd_pos hδ f hf hdisj R).isOpen)
      let gRet := finiteFullPreparedMetric I hδ f hf hdisj hs U g R hRet c hc x₀ order d₀ hOriginal hrec d hmap hside w
      ∀ (q : finiteCapRetained transitionEnd_pos hδ f hf hdisj R) (r : ℝ), 0 < r →
        (∀ b : {b : ι × Bool // cuttingSphereComponent hδ f hf hdisj b ∈ R},
          Real.sqrt (metricScalarAt g ((d₀ b.val.1).offsetPoint (cuttingSign_sq b.val.2))) * r ≤ δ) →
        (ENNReal.ofReal ν * ENNReal.ofReal r ^ 3 ≤
          riemannianVolumeMeasure (𝓡 3) (finiteCapRetained transitionEnd_pos hδ f hf hdisj R) gRet
            (riemannianBallOf gRet q r)) ∨
          riemannianBallOf gRet q (2 * r) ⊆
            interior (range (finiteRetainedCoreInclusion transitionEnd_pos hδ f hf hdisj R)) := by
  obtain ⟨δ₀, hδ₀, hcover⟩ := exists_uniform_finiteFullPreparedMetric_window_or_retained_ball
  obtain ⟨ν, hν, hvolume⟩ := exists_uniform_finiteFullPreparedMetric_window_ball_volume_lower_unscaled
    (transitionEnd + 1)
  let δ := min (δ₀ / 2) 1
  have hδpos : 0 < δ := lt_min (half_pos hδ₀) zero_lt_one
  refine ⟨δ, ν, hδpos, hν, ?_⟩
  intro E H M _ _ _ _ _ I _ _ _ _ _ _ ι _ precision hδ f hf hdisj hs U g R hRet
    c hc x₀ order d₀ hOriginal k' hrec d hmap hside A D ε hA m w heps hD
  let : LocallyPathConnectedSpace M := originalModel_locallyPathConnected I Fact.out
  let Qcap := FiniteCapQuotient transitionEnd_pos hδ f (fun i => (hf i).injective) hdisj
  let : ChartedSpace CurvGE3 Qcap := finiteCapChartedSpace I Fact.out transitionEnd_pos hδ f hf hdisj
  let : IsManifold (𝓡 3) ∞ Qcap := finiteCapQuotient_isManifold Fact.out transitionEnd_pos hδ f hf hdisj hs
  let : T2Space Qcap := finiteCapQuotient_t2Space transitionEnd_pos hδ f hf hdisj
  let : SigmaCompactSpace Qcap := finiteCapQuotient_sigmaCompactSpace transitionEnd_pos hδ f hf hdisj
  let : SigmaCompactSpace (finiteCapRetained transitionEnd_pos hδ f hf hdisj R) := isSigmaCompact_iff_sigmaCompactSpace.mp
    (DifferentialGeometry.Geometry.isSigmaCompact_of_isOpen (𝓡 3) (finiteCapRetained transitionEnd_pos hδ f hf hdisj R).isOpen)
  dsimp only
  intro q r hr hscale
  have hscale2 (b : {b : ι × Bool // cuttingSphereComponent hδ f hf hdisj b ∈ R}) :
      Real.sqrt (metricScalarAt g ((d₀ b.val.1).offsetPoint (cuttingSign_sq b.val.2))) * (2 * r) ≤ δ₀ := by
    have h := (hscale b).trans (min_le_left (δ₀ / 2) 1)
    nlinarith
  rcases hcover I hδ f hf hdisj hs U g R hRet c hc x₀ order d₀ hOriginal hrec d hmap hside w
      heps (by linarith) q (2 * r) hscale2 with ⟨b, x, hx, hxq⟩ | hold
  · left
    have hscale1 := (hscale b).trans (min_le_right (δ₀ / 2) 1)
    rw [← hxq]
    exact hvolume I hδ f hf hdisj hs U g R hRet c hc x₀ order d₀ hOriginal hrec d hmap hside w
      b heps x hx r hr hscale1 (by linarith)
  · exact Or.inr hold


theorem exists_uniform_finiteFullPreparedMetric_small_ball_volume_lower_or_retained_neighborhood :
    ∃ ν : ℝ, 0 < ν ∧
      ∀ {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E],
      ∀ [Fact (Module.finrank ℝ E = 3)] [TopologicalSpace H] (I : ModelWithCorners ℝ E H) [I.Boundaryless],
      ∀ [TopologicalSpace M] [ChartedSpace H M] [T2Space M] [IsManifold I ∞ M] [SigmaCompactSpace M],
      ∀ {ι : Type*} [Finite ι] {precision : ι → ℝ},
      ∀ (hδ : ∀ i, 0 < precision i) (f : ∀ i : ι, bufferedCylinder (precision i) → M),
      ∀ (hf : ∀ i, _root_.Topology.IsOpenEmbedding (f i)),
      ∀ (hdisj : Pairwise (fun i j => Disjoint (range (f i)) (range (f j)))),
      ∀ (hs : ∀ i, IsLocalDiffeomorph CurvGIC I ∞ (f i)),
      ∀ (U : Opens M) (g : SmoothRiemannianMetric I U),
      ∀ (R : Set (ConnectedComponents (cutCore f))),
      ∀ (hRet : MapsTo (Subtype.val : cutCore f → M) (retainedCore f R) U),
      ∀ (c : ℝ) (hc : 4 ≤ c),
      ∀ (x₀ : ι → U) (order : ι → ℕ),
      ∀ (d₀ : ∀ i, normalizedDatum g (x₀ i) (precision i) (order i)),
      ∀ (hOriginal : ∀ i, f i = neckAmbientMap U (d₀ i)),
      ∀ {k' : {b : ι × Bool // cuttingSphereComponent hδ f hf hdisj b ∈ R} → ℕ},
      ∀ (hrec : ∀ b : {b : ι × Bool // cuttingSphereComponent hδ f hf hdisj b ∈ R}, (c * precision b.val.1)⁻¹ + 1 ≤ (precision b.val.1)⁻¹),
      ∀ (d : ∀ b : {b : ι × Bool // cuttingSphereComponent hδ f hf hdisj b ∈ R}, normalizedDatum g
    ((d₀ b.val.1).offsetPoint (cuttingSign_sq b.val.2)) (c * precision b.val.1) (k' b)),
      ∀ (hmap : ∀ b : {b : ι × Bool // cuttingSphereComponent hδ f hf hdisj b ∈ R}, (d b).map = (d₀ b.val.1).recenteringMap (cuttingSign_sq b.val.2) (hrec b)),
      ∀ (hside : ∀ b : {b : ι × Bool // cuttingSphereComponent hδ f hf hdisj b ∈ R}, (d b).retainedSide = true),
      ∀ {A D ε : ℝ} {hA : 0 < A} {m : ℕ},
      ∀ (w : ∀ b : {b : ι × Bool // cuttingSphereComponent hδ f hf hdisj b ∈ R}, CanonicalStaticInsertionWitness (d b) A hA D m ε),
      ε ≤ 1 / 2 → transitionEnd + 2 < D →
      let : LocallyPathConnectedSpace M := originalModel_locallyPathConnected I Fact.out
      let Qcap := FiniteCapQuotient transitionEnd_pos hδ f (fun i => (hf i).injective) hdisj
      let : ChartedSpace CurvGE3 Qcap := finiteCapChartedSpace I Fact.out transitionEnd_pos hδ f hf hdisj
      let : IsManifold (𝓡 3) ∞ Qcap := finiteCapQuotient_isManifold Fact.out transitionEnd_pos hδ f hf hdisj hs
      let : T2Space Qcap := finiteCapQuotient_t2Space transitionEnd_pos hδ f hf hdisj
      let : SigmaCompactSpace Qcap := finiteCapQuotient_sigmaCompactSpace transitionEnd_pos hδ f hf hdisj
      let : SigmaCompactSpace (finiteCapRetained transitionEnd_pos hδ f hf hdisj R) := isSigmaCompact_iff_sigmaCompactSpace.mp
        (DifferentialGeometry.Geometry.isSigmaCompact_of_isOpen (𝓡 3) (finiteCapRetained transitionEnd_pos hδ f hf hdisj R).isOpen)
      let gRet := finiteFullPreparedMetric I hδ f hf hdisj hs U g R hRet c hc x₀ order d₀ hOriginal hrec d hmap hside w
      ∃ r₀ : ℝ, 0 < r₀ ∧ ∀ q : finiteCapRetained transitionEnd_pos hδ f hf hdisj R,
        (∀ r : ℝ, 0 < r → r ≤ r₀ → ENNReal.ofReal ν * ENNReal.ofReal r ^ 3 ≤
          riemannianVolumeMeasure (𝓡 3) (finiteCapRetained transitionEnd_pos hδ f hf hdisj R) gRet
            (riemannianBallOf gRet q r)) ∨
          riemannianBallOf gRet q (2 * r₀) ⊆
            interior (range (finiteRetainedCoreInclusion transitionEnd_pos hδ f hf hdisj R)) := by
  obtain ⟨δ₀, hδ₀, hcover⟩ := exists_uniform_finiteFullPreparedMetric_window_or_retained_ball
  obtain ⟨ν, hν, hvolume⟩ := exists_uniform_finiteFullPreparedMetric_window_ball_volume_lower_unscaled
    (transitionEnd + 1)
  let δ := min (δ₀ / 2) 1
  have hδpos : 0 < δ := lt_min (half_pos hδ₀) zero_lt_one
  refine ⟨ν, hν, ?_⟩
  intro E H M _ _ _ _ _ I _ _ _ _ _ _ ι _ precision hδ f hf hdisj hs U g R hRet
    c hc x₀ order d₀ hOriginal k' hrec d hmap hside A D ε hA m w heps hD
  let : LocallyPathConnectedSpace M := originalModel_locallyPathConnected I Fact.out
  let Qcap := FiniteCapQuotient transitionEnd_pos hδ f (fun i => (hf i).injective) hdisj
  let : ChartedSpace CurvGE3 Qcap := finiteCapChartedSpace I Fact.out transitionEnd_pos hδ f hf hdisj
  let : IsManifold (𝓡 3) ∞ Qcap := finiteCapQuotient_isManifold Fact.out transitionEnd_pos hδ f hf hdisj hs
  let : T2Space Qcap := finiteCapQuotient_t2Space transitionEnd_pos hδ f hf hdisj
  let : SigmaCompactSpace Qcap := finiteCapQuotient_sigmaCompactSpace transitionEnd_pos hδ f hf hdisj
  let : SigmaCompactSpace (finiteCapRetained transitionEnd_pos hδ f hf hdisj R) := isSigmaCompact_iff_sigmaCompactSpace.mp
    (DifferentialGeometry.Geometry.isSigmaCompact_of_isOpen (𝓡 3) (finiteCapRetained transitionEnd_pos hδ f hf hdisj R).isOpen)
  dsimp only
  let scales : {b : ι × Bool // cuttingSphereComponent hδ f hf hdisj b ∈ R} → ℝ :=
    fun b => Real.sqrt (metricScalarAt g ((d₀ b.val.1).offsetPoint (cuttingSign_sq b.val.2)))
  obtain ⟨C, hC⟩ := (Set.finite_range scales).bddAbove
  have hCpos : 0 < max C 1 := zero_lt_one.trans_le (le_max_right C 1)
  let r₀ := δ / max C 1
  have hr₀ : 0 < r₀ := div_pos hδpos hCpos
  have hscale (b : {b : ι × Bool // cuttingSphereComponent hδ f hf hdisj b ∈ R}) :
      scales b * r₀ ≤ δ := by
    have hb : scales b ≤ max C 1 := (hC ⟨b, rfl⟩).trans (le_max_left C 1)
    have hmul : max C 1 * r₀ = δ := by dsimp only [r₀]; field_simp
    exact (mul_le_mul_of_nonneg_right hb hr₀.le).trans hmul.le
  have hscale2 (b : {b : ι × Bool // cuttingSphereComponent hδ f hf hdisj b ∈ R}) :
      scales b * (2 * r₀) ≤ δ₀ := by
    have h := (hscale b).trans (min_le_left (δ₀ / 2) 1)
    nlinarith
  refine ⟨r₀, hr₀, ?_⟩
  intro q
  rcases hcover I hδ f hf hdisj hs U g R hRet c hc x₀ order d₀ hOriginal hrec d hmap hside w
      heps (by linarith) q (2 * r₀) hscale2 with ⟨b, x, hx, hxq⟩ | hbuffer
  · left
    intro r hr hrr
    have hscale1 : scales b * r ≤ 1 :=
      ((mul_le_mul_of_nonneg_left hrr (Real.sqrt_nonneg _)).trans (hscale b)).trans
        (min_le_right (δ₀ / 2) 1)
    rw [← hxq]
    exact hvolume I hδ f hf hdisj hs U g R hRet c hc x₀ order d₀ hOriginal
      hrec d hmap hside w b heps x hx r hr hscale1 (by linarith)
  · exact Or.inr hbuffer


theorem exists_uniform_finiteFullPreparedMetric_small_ball_volume_lower_or_retained_ball :
    ∃ ν : ℝ, 0 < ν ∧
      ∀ {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E],
      ∀ [Fact (Module.finrank ℝ E = 3)] [TopologicalSpace H] (I : ModelWithCorners ℝ E H) [I.Boundaryless],
      ∀ [TopologicalSpace M] [ChartedSpace H M] [T2Space M] [IsManifold I ∞ M] [SigmaCompactSpace M],
      ∀ {ι : Type*} [Finite ι] {precision : ι → ℝ},
      ∀ (hδ : ∀ i, 0 < precision i) (f : ∀ i : ι, bufferedCylinder (precision i) → M),
      ∀ (hf : ∀ i, _root_.Topology.IsOpenEmbedding (f i)),
      ∀ (hdisj : Pairwise (fun i j => Disjoint (range (f i)) (range (f j)))),
      ∀ (hs : ∀ i, IsLocalDiffeomorph CurvGIC I ∞ (f i)),
      ∀ (U : Opens M) (g : SmoothRiemannianMetric I U),
      ∀ (R : Set (ConnectedComponents (cutCore f))),
      ∀ (hRet : MapsTo (Subtype.val : cutCore f → M) (retainedCore f R) U),
      ∀ (c : ℝ) (hc : 4 ≤ c),
      ∀ (x₀ : ι → U) (order : ι → ℕ),
      ∀ (d₀ : ∀ i, normalizedDatum g (x₀ i) (precision i) (order i)),
      ∀ (hOriginal : ∀ i, f i = neckAmbientMap U (d₀ i)),
      ∀ {k' : {b : ι × Bool // cuttingSphereComponent hδ f hf hdisj b ∈ R} → ℕ},
      ∀ (hrec : ∀ b : {b : ι × Bool // cuttingSphereComponent hδ f hf hdisj b ∈ R}, (c * precision b.val.1)⁻¹ + 1 ≤ (precision b.val.1)⁻¹),
      ∀ (d : ∀ b : {b : ι × Bool // cuttingSphereComponent hδ f hf hdisj b ∈ R}, normalizedDatum g
    ((d₀ b.val.1).offsetPoint (cuttingSign_sq b.val.2)) (c * precision b.val.1) (k' b)),
      ∀ (hmap : ∀ b : {b : ι × Bool // cuttingSphereComponent hδ f hf hdisj b ∈ R}, (d b).map = (d₀ b.val.1).recenteringMap (cuttingSign_sq b.val.2) (hrec b)),
      ∀ (hside : ∀ b : {b : ι × Bool // cuttingSphereComponent hδ f hf hdisj b ∈ R}, (d b).retainedSide = true),
      ∀ {A D ε : ℝ} {hA : 0 < A} {m : ℕ},
      ∀ (w : ∀ b : {b : ι × Bool // cuttingSphereComponent hδ f hf hdisj b ∈ R}, CanonicalStaticInsertionWitness (d b) A hA D m ε),
      ε ≤ 1 / 2 → transitionEnd + 2 < D →
      let : LocallyPathConnectedSpace M := originalModel_locallyPathConnected I Fact.out
      let Qcap := FiniteCapQuotient transitionEnd_pos hδ f (fun i => (hf i).injective) hdisj
      let : ChartedSpace CurvGE3 Qcap := finiteCapChartedSpace I Fact.out transitionEnd_pos hδ f hf hdisj
      let : IsManifold (𝓡 3) ∞ Qcap := finiteCapQuotient_isManifold Fact.out transitionEnd_pos hδ f hf hdisj hs
      let : T2Space Qcap := finiteCapQuotient_t2Space transitionEnd_pos hδ f hf hdisj
      let : SigmaCompactSpace Qcap := finiteCapQuotient_sigmaCompactSpace transitionEnd_pos hδ f hf hdisj
      let : SigmaCompactSpace (finiteCapRetained transitionEnd_pos hδ f hf hdisj R) := isSigmaCompact_iff_sigmaCompactSpace.mp
        (DifferentialGeometry.Geometry.isSigmaCompact_of_isOpen (𝓡 3) (finiteCapRetained transitionEnd_pos hδ f hf hdisj R).isOpen)
      let gRet := finiteFullPreparedMetric I hδ f hf hdisj hs U g R hRet c hc x₀ order d₀ hOriginal hrec d hmap hside w
      ∃ r₀ : ℝ, 0 < r₀ ∧
        ∀ (q : finiteCapRetained transitionEnd_pos hδ f hf hdisj R) (r : ℝ), 0 < r → r ≤ r₀ →
        (ENNReal.ofReal ν * ENNReal.ofReal r ^ 3 ≤
          riemannianVolumeMeasure (𝓡 3) (finiteCapRetained transitionEnd_pos hδ f hf hdisj R) gRet
            (riemannianBallOf gRet q r)) ∨
          riemannianBallOf gRet q (2 * r) ⊆
            interior (range (finiteRetainedCoreInclusion transitionEnd_pos hδ f hf hdisj R)) := by
  obtain ⟨ν, hν, hbound⟩ := exists_uniform_finiteFullPreparedMetric_small_ball_volume_lower_or_retained_neighborhood
  refine ⟨ν, hν, ?_⟩
  intro E H M _ _ _ _ _ I _ _ _ _ _ _ ι _ precision hδ f hf hdisj hs U g R hRet
    c hc x₀ order d₀ hOriginal k' hrec d hmap hside A D ε hA m w heps hD
  let : LocallyPathConnectedSpace M := originalModel_locallyPathConnected I Fact.out
  let Qcap := FiniteCapQuotient transitionEnd_pos hδ f (fun i => (hf i).injective) hdisj
  let : ChartedSpace CurvGE3 Qcap := finiteCapChartedSpace I Fact.out transitionEnd_pos hδ f hf hdisj
  let : IsManifold (𝓡 3) ∞ Qcap := finiteCapQuotient_isManifold Fact.out transitionEnd_pos hδ f hf hdisj hs
  let : T2Space Qcap := finiteCapQuotient_t2Space transitionEnd_pos hδ f hf hdisj
  let : SigmaCompactSpace Qcap := finiteCapQuotient_sigmaCompactSpace transitionEnd_pos hδ f hf hdisj
  let : SigmaCompactSpace (finiteCapRetained transitionEnd_pos hδ f hf hdisj R) := isSigmaCompact_iff_sigmaCompactSpace.mp
    (DifferentialGeometry.Geometry.isSigmaCompact_of_isOpen (𝓡 3) (finiteCapRetained transitionEnd_pos hδ f hf hdisj R).isOpen)
  dsimp only
  obtain ⟨r₀, hr₀, hballs⟩ := hbound I hδ f hf hdisj hs U g R hRet c hc x₀ order d₀ hOriginal
    hrec d hmap hside w heps hD
  refine ⟨r₀, hr₀, ?_⟩
  intro q r hr hrr
  rcases hballs q with hvolume | hbuffer
  · exact Or.inl (hvolume r hr hrr)
  · exact Or.inr ((riemannianBallOf_mono _ _ (mul_le_mul_of_nonneg_left hrr (by norm_num))).trans hbuffer)


end

end DifferentialGeometry.PDE.RicciFlow.StandardCap
