import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.StandardCap.FullMetricWindowCover
import DifferentialGeometry.Geometry.Metric.DistancePullback
import DifferentialGeometry.Geometry.Curvature.EmbeddingCurvatureJets
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.StandardCap.FullMetricModels
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.StandardCap.StaticWindowVolume
import DifferentialGeometry.Geometry.Comparison.OpenEmbeddingBallCapture

set_option autoImplicit false
noncomputable section
open Set Function TopologicalSpace Manifold DifferentialGeometry
open DifferentialGeometry.Geometry.Neck DifferentialGeometry.Geometry.Metric DifferentialGeometry.Topology.ThreeManifold.Surgery DifferentialGeometry.Topology.Manifold.Attachment
open DifferentialGeometry.Tensor0SBundle DifferentialGeometry.CheegerGromovCompactness
open DifferentialGeometry.Topology.Manifold
open DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
open DifferentialGeometry.Geometry.Riemannian
open DifferentialGeometry.Geometry.Curvature
open scoped Manifold ContDiff Topology ENNReal
namespace DifferentialGeometry.PDE.RicciFlow.StandardCap
private abbrev ModelGE3 := EuclideanSpace ℝ (Fin 3)
private abbrev ModelGIC := (𝓡 2).prod 𝓘(ℝ)
private local instance {B : ℝ} {hB : 0 < B} : ChartedSpace ModelGE3 (InsertionQuotient hB) :=
  radialCapAttachmentChartedSpace transitionEnd_pos hB
private local instance {B : ℝ} {hB : 0 < B} : IsManifold (𝓡 3) ∞ (InsertionQuotient hB) :=
  radialCapAttachment_isManifold transitionEnd_pos hB
private local instance : NeZero (Module.finrank ℝ ModelGE3) := ⟨by simp⟩
private local instance {B : ℝ} {hB : 0 < B} : T2Space (InsertionQuotient hB) :=
  radialCapAttachment_t2Space transitionEnd_pos hB
private local instance {B : ℝ} {hB : 0 < B} : SigmaCompactSpace (InsertionQuotient hB) := by
  let : SecondCountableTopology (InsertionQuotient hB) := radialCapAttachment_secondCountableTopology transitionEnd_pos hB
  let : LocallyCompactSpace (InsertionQuotient hB) := ChartedSpace.locallyCompactSpace ModelGE3 (InsertionQuotient hB)
  infer_instance
variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
variable [Fact (Module.finrank ℝ E = 3)] [TopologicalSpace H] (I : ModelWithCorners ℝ E H) [I.Boundaryless]
variable [TopologicalSpace M] [ChartedSpace H M] [T2Space M] [IsManifold I ∞ M]
variable {ι : Type*} [Finite ι] {precision : ι → ℝ}
variable (hδ : ∀ i, 0 < precision i) (f : ∀ i : ι, bufferedCylinder (precision i) → M)
variable (hf : ∀ i, _root_.Topology.IsOpenEmbedding (f i))
variable (hdisj : Pairwise (fun i j => Disjoint (range (f i)) (range (f j))))
variable (hs : ∀ i, IsLocalDiffeomorph ModelGIC I ∞ (f i))
local notation "ModelGQ" => FiniteCapQuotient transitionEnd_pos hδ f (fun i => _root_.Topology.IsEmbedding.injective (_root_.Topology.IsOpenEmbedding.toIsEmbedding (hf i))) hdisj
variable (U : Opens M) (g : SmoothRiemannianMetric I U)
variable (R : Set (ConnectedComponents (cutCore f)))
variable (hRet : MapsTo (Subtype.val : cutCore f → M) (retainedCore f R) U)
variable (c : ℝ) (hc : 4 ≤ c)
local notation "ModelGRet" => finiteCapRetained transitionEnd_pos hδ f hf hdisj R
local notation "ModelGOld" => finiteRetainedInteriorOpens transitionEnd_pos hδ f hf hdisj R
local notation "ModelGB" => {b : ι × Bool // cuttingSphereComponent hδ f hf hdisj b ∈ R}
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


theorem finiteFullPreparedMetric_normalized_tip_ball_subset_window_image
    (b : ModelGB) (heps : ε ≤ 1 / 2) {ρ : ℝ} (hρ : 0 < ρ) (hρD : ρ < D) :
    let : LocallyPathConnectedSpace M := originalModel_locallyPathConnected I Fact.out
    let : ChartedSpace ModelGE3 ModelGQ := finiteCapChartedSpace I Fact.out transitionEnd_pos hδ f hf hdisj
    let : IsManifold (𝓡 3) ∞ ModelGQ := finiteCapQuotient_isManifold Fact.out transitionEnd_pos hδ f hf hdisj hs
    let : T2Space ModelGQ := finiteCapQuotient_t2Space transitionEnd_pos hδ f hf hdisj
    let gRet := finiteFullPreparedMetric I hδ f hf hdisj hs U g R hRet c hc x₀ order d₀ hOriginal hrec d hmap hside w
    let F := finiteFullWitnessMap I Fact.out transitionEnd_pos hδ f hf hdisj hs R c hc b
    let Φ := F ∘ (w b).window
    let Q := metricScalarAt g ((d₀ b.val.1).offsetPoint (cuttingSign_sq b.val.2))
    riemannianBallOf (scaleMetric Q (d b).scalar_pos gRet) (F ((w b).data.tip)) (ρ / 2) ⊆
      Φ '' {x : standardCapWindow D | ‖x.val‖ ≤ ρ} := by
  let : LocallyPathConnectedSpace M := originalModel_locallyPathConnected I Fact.out
  let : ChartedSpace ModelGE3 ModelGQ := finiteCapChartedSpace I Fact.out transitionEnd_pos hδ f hf hdisj
  let : IsManifold (𝓡 3) ∞ ModelGQ := finiteCapQuotient_isManifold Fact.out transitionEnd_pos hδ f hf hdisj hs
  let : T2Space ModelGQ := finiteCapQuotient_t2Space transitionEnd_pos hδ f hf hdisj
  let gRet := finiteFullPreparedMetric I hδ f hf hdisj hs U g R hRet c hc x₀ order d₀ hOriginal hrec d hmap hside w
  let F := finiteFullWitnessMap I Fact.out transitionEnd_pos hδ f hf hdisj hs R c hc b
  let Φ := F ∘ (w b).window
  let Q := metricScalarAt g ((d₀ b.val.1).offsetPoint (cuttingSign_sq b.val.2))
  dsimp only
  have hzero : (0 : ThreeSpace) ∈ standardCapWindow D := by
    change ‖(0 : ThreeSpace)‖ < D + 1
    simp only [norm_zero]
    linarith
  let p : standardCapWindow D := ⟨0, hzero⟩
  have hF := isLocalDiffeomorph_finiteFullWitnessMap I Fact.out transitionEnd_pos hδ f hf hdisj hs R c hc b
  have hΦ : IsLocalDiffeomorph (𝓡 3) (𝓡 3) ∞ Φ :=
    fun q => ((w b).properties.window_local q).comp (𝓡 3) ModelGRet (hF ((w b).window q))
  have hiΦ : Injective Φ :=
    (injective_finiteFullWitnessMap I Fact.out transitionEnd_pos hδ f hf hdisj hs R c hc b).comp
      (w b).window_smooth.isEmbedding.injective
  have hnorm : ∀ z ∈ riemannianClosedBallOf metric (0 : ThreeSpace) ρ, ‖z‖ ≤ ρ := by
    intro z hz
    change riemannianEDistOf metric 0 z ≤ ENNReal.ofReal ρ at hz
    rwa [edist_zero, ENNReal.ofReal_le_ofReal_iff hρ.le] at hz
  have hsub : riemannianClosedBallOf metric (0 : ThreeSpace) ρ ⊆ standardCapWindow D := by
    intro z hz
    change ‖z‖ < D + 1
    linarith [hnorm z hz]
  have he : riemannianClosedBallOf metric (0 : ThreeSpace) ρ = Metric.closedBall 0 ρ := by
    ext z
    change riemannianEDistOf metric 0 z ≤ ENNReal.ofReal ρ ↔ dist z 0 ≤ ρ
    rw [edist_zero, ENNReal.ofReal_le_ofReal_iff hρ.le, dist_zero_right]
  have hcpt : IsCompact (riemannianClosedBallOf metric (0 : ThreeSpace) ρ) :=
    he ▸ isCompact_closedBall _ _
  have hlow (x : standardCapWindow D) (hx : x.val ∈ riemannianClosedBallOf metric p.val ρ)
      (v : TangentSpace ThreeModel x) : metric.inner x.val v v ≤ (2 : ℝ)^2 *
        (scaleMetric Q (d b).scalar_pos gRet).inner (Φ x)
          (mfderiv ThreeModel ThreeModel Φ x v) (mfderiv ThreeModel ThreeModel Φ x v) := by
    have hin : (scaleMetric Q (d b).scalar_pos gRet).inner (Φ x)
        (mfderiv ThreeModel ThreeModel Φ x v) (mfderiv ThreeModel ThreeModel Φ x v) =
        (w b).windowMetric.inner x v v := by
      rw [scaleMetric_inner, (w b).window_inner]
      apply congrArg (fun z => Q*z)
      exact metric_inner_comp_of_isometry (w b).data.outMetric gRet F
        (contMDiff_finiteFullWitnessMap I Fact.out transitionEnd_pos hδ f hf hdisj hs R c hc b)
        (finiteFullPreparedMetric_witness_inner I hδ f hf hdisj hs U g R hRet c hc
          x₀ order d₀ hOriginal hrec d hmap hside w b)
        (w b).window (w b).window_smooth.contMDiff x v v
    rw [hin]
    have hb := ((w b).window_inner_bounds heps ((hnorm x.val hx).trans_lt hρD) v).1
    rw [standardCapMetric_eq_metric, SmoothRiemannianMetric.restrictOpen_inner, one_div] at hb
    have hb' := (inv_mul_le_iff₀ (by norm_num : (0 : ℝ) < 2)).mp hb
    exact hb'.trans (mul_le_mul_of_nonneg_right (by norm_num : (2 : ℝ) ≤ 2^2)
      (metric_inner_self_nonneg (w b).windowMetric x v))
  have hcap := Geometry.Metric.ball_subset_image_of_metric_lower_on_opens
    (scaleMetric Q (d b).scalar_pos gRet) metric (standardCapWindow D) Φ hΦ hiΦ p
    hρ (by norm_num : (0 : ℝ) < 2) hcpt hsub hlow
  have hpoint : Φ p = F ((w b).data.tip) := congrArg F ((w b).window_tip hzero)
  rw [hpoint] at hcap
  apply hcap.trans
  apply image_mono
  intro x hx
  exact hnorm x.val hx

theorem finiteFullPreparedMetric_curvature_derivative_bound_on_normalized_tip_ball
    (b : ModelGB) (heps : ε ≤ 1 / 2) {ρ : ℝ} (hρ : 0 < ρ) (hρD : ρ < D)
    (j : ℕ) (C : ℝ)
    (hC : ∀ x : standardCapWindow D, ‖x.val‖ < D →
      Real.sqrt (normSq0S (w b).windowMetric x (4+j)
        (iterCov (w b).windowMetric 4 (metricRm04 (w b).windowMetric) j x)) ≤ C) :
    let : LocallyPathConnectedSpace M := originalModel_locallyPathConnected I Fact.out
    let : ChartedSpace ModelGE3 ModelGQ := finiteCapChartedSpace I Fact.out transitionEnd_pos hδ f hf hdisj
    let : IsManifold (𝓡 3) ∞ ModelGQ := finiteCapQuotient_isManifold Fact.out transitionEnd_pos hδ f hf hdisj hs
    let : T2Space ModelGQ := finiteCapQuotient_t2Space transitionEnd_pos hδ f hf hdisj
    let gRet := finiteFullPreparedMetric I hδ f hf hdisj hs U g R hRet c hc x₀ order d₀ hOriginal hrec d hmap hside w
    let F := finiteFullWitnessMap I Fact.out transitionEnd_pos hδ f hf hdisj hs R c hc b
    let Q := metricScalarAt g ((d₀ b.val.1).offsetPoint (cuttingSign_sq b.val.2))
    let gQ := scaleMetric Q (d b).scalar_pos gRet
    ∀ x ∈ riemannianClosedBallOf gQ (F ((w b).data.tip)) (ρ / 4),
      Real.sqrt (normSq0S gQ x (4+j) (iterCov gQ 4 (metricRm04 gQ) j x)) ≤ C := by
  let : LocallyPathConnectedSpace M := originalModel_locallyPathConnected I Fact.out
  let : ChartedSpace ModelGE3 ModelGQ := finiteCapChartedSpace I Fact.out transitionEnd_pos hδ f hf hdisj
  let : IsManifold (𝓡 3) ∞ ModelGQ := finiteCapQuotient_isManifold Fact.out transitionEnd_pos hδ f hf hdisj hs
  let : T2Space ModelGQ := finiteCapQuotient_t2Space transitionEnd_pos hδ f hf hdisj
  let gRet := finiteFullPreparedMetric I hδ f hf hdisj hs U g R hRet c hc x₀ order d₀ hOriginal hrec d hmap hside w
  let F := finiteFullWitnessMap I Fact.out transitionEnd_pos hδ f hf hdisj hs R c hc b
  let Φ := F ∘ (w b).window
  let Q := metricScalarAt g ((d₀ b.val.1).offsetPoint (cuttingSign_sq b.val.2))
  let gQ := scaleMetric Q (d b).scalar_pos gRet
  dsimp only
  intro x hx
  have hsmall : x ∈ riemannianBallOf gQ (F ((w b).data.tip)) (ρ / 2) :=
    hx.trans_lt ((ENNReal.ofReal_lt_ofReal_iff (half_pos hρ)).mpr (by linarith))
  obtain ⟨z, hz, hΦz⟩ := finiteFullPreparedMetric_normalized_tip_ball_subset_window_image
    I hδ f hf hdisj hs U g R hRet c hc x₀ order d₀ hOriginal hrec d hmap hside w b heps hρ hρD hsmall
  let : SigmaCompactSpace (standardCapWindow D) := isSigmaCompact_iff_sigmaCompactSpace.mp
    (DifferentialGeometry.Geometry.isSigmaCompact_of_isOpen (𝓡 3) (standardCapWindow D).isOpen)
  have hF := isLocalDiffeomorph_finiteFullWitnessMap I Fact.out transitionEnd_pos hδ f hf hdisj hs R c hc b
  have hΦ : IsLocalDiffeomorph (𝓡 3) (𝓡 3) ∞ Φ :=
    fun q => ((w b).properties.window_local q).comp (𝓡 3) ModelGRet (hF ((w b).window q))
  have hiΦ : Injective Φ :=
    (injective_finiteFullWitnessMap I Fact.out transitionEnd_pos hδ f hf hdisj hs R c hc b).comp
      (w b).window_smooth.isEmbedding.injective
  have hmetric (y : standardCapWindow D) (v u : TangentSpace ThreeModel y) :
      (w b).windowMetric.inner y v u = gQ.inner (Φ y)
        (mfderiv ThreeModel ThreeModel Φ y v) (mfderiv ThreeModel ThreeModel Φ y u) := by
    rw [(w b).window_inner, scaleMetric_inner]
    apply congrArg (fun z => Q*z)
    exact (metric_inner_comp_of_isometry (w b).data.outMetric gRet F
      (contMDiff_finiteFullWitnessMap I Fact.out transitionEnd_pos hδ f hf hdisj hs R c hc b)
      (finiteFullPreparedMetric_witness_inner I hδ f hf hdisj hs U g R hRet c hc
        x₀ order d₀ hOriginal hrec d hmap hside w b)
      (w b).window (w b).window_smooth.contMDiff y v u).symm
  have heq := curvature_jets_of_injective_local_isometry (w b).windowMetric gQ Φ hΦ hiΦ hmetric j z
  change Φ z = x at hΦz
  rw [hΦz] at heq
  exact heq.symm.trans_le (hC z (hz.trans_lt hρD))

theorem finiteFullPreparedMetric_window_image_subset_normalized_tip_ball
    (b : ModelGB) (heps : ε ≤ 1 / 2) {ρ : ℝ} (hρ : 0 < ρ) (hρD : ρ < D) :
    let : LocallyPathConnectedSpace M := originalModel_locallyPathConnected I Fact.out
    let : ChartedSpace ModelGE3 ModelGQ := finiteCapChartedSpace I Fact.out transitionEnd_pos hδ f hf hdisj
    let : IsManifold (𝓡 3) ∞ ModelGQ := finiteCapQuotient_isManifold Fact.out transitionEnd_pos hδ f hf hdisj hs
    let : T2Space ModelGQ := finiteCapQuotient_t2Space transitionEnd_pos hδ f hf hdisj
    let gRet := finiteFullPreparedMetric I hδ f hf hdisj hs U g R hRet c hc x₀ order d₀ hOriginal hrec d hmap hside w
    let F := finiteFullWitnessMap I Fact.out transitionEnd_pos hδ f hf hdisj hs R c hc b
    let Φ := F ∘ (w b).window
    let Q := metricScalarAt g ((d₀ b.val.1).offsetPoint (cuttingSign_sq b.val.2))
    Φ '' {x : standardCapWindow D | ‖x.val‖ ≤ ρ / 4} ⊆
      riemannianBallOf (scaleMetric Q (d b).scalar_pos gRet) (F ((w b).data.tip)) ρ := by
  let : LocallyPathConnectedSpace M := originalModel_locallyPathConnected I Fact.out
  let : ChartedSpace ModelGE3 ModelGQ := finiteCapChartedSpace I Fact.out transitionEnd_pos hδ f hf hdisj
  let : IsManifold (𝓡 3) ∞ ModelGQ := finiteCapQuotient_isManifold Fact.out transitionEnd_pos hδ f hf hdisj hs
  let : T2Space ModelGQ := finiteCapQuotient_t2Space transitionEnd_pos hδ f hf hdisj
  let gRet := finiteFullPreparedMetric I hδ f hf hdisj hs U g R hRet c hc x₀ order d₀ hOriginal hrec d hmap hside w
  let F := finiteFullWitnessMap I Fact.out transitionEnd_pos hδ f hf hdisj hs R c hc b
  let Q := metricScalarAt g ((d₀ b.val.1).offsetPoint (cuttingSign_sq b.val.2))
  dsimp only
  rintro _ ⟨x, hx, rfl⟩
  have hsrc := (w b).window_image_subset_normalized_tip_ball heps hρ hρD ⟨x, hx, rfl⟩
  have hd := edistOf_le_of_quad_of_localDiffeomorph
    (scaleMetric Q (d b).scalar_pos (w b).data.outMetric)
    (scaleMetric Q (d b).scalar_pos gRet) F
    (isLocalDiffeomorph_finiteFullWitnessMap I Fact.out transitionEnd_pos hδ f hf hdisj hs R c hc b)
    zero_lt_one (fun y v => ?_) ((w b).data.tip) ((w b).window x)
  · simp only [Real.sqrt_one, ENNReal.ofReal_one, one_mul] at hd
    exact hd.trans_lt hsrc
  · rw [scaleMetric_inner, scaleMetric_inner, one_mul]
    exact le_of_eq (congrArg (fun z => Q*z)
      (finiteFullPreparedMetric_witness_inner I hδ f hf hdisj hs U g R hRet c hc
        x₀ order d₀ hOriginal hrec d hmap hside w b y v v))

section

theorem exists_uniform_finiteFullPreparedMetric_window_ball_capture (R₀ : ℝ) :
    ∃ δ : ℝ, 0 < δ ∧
      ∀ {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
[Fact (Module.finrank ℝ E = 3)] [TopologicalSpace H] (I : ModelWithCorners ℝ E H) [I.Boundaryless]
[TopologicalSpace M] [ChartedSpace H M] [T2Space M] [IsManifold I ∞ M]
{ι : Type*} [Finite ι] {precision : ι → ℝ}
(hδ : ∀ i, 0 < precision i) (f : ∀ i : ι, bufferedCylinder (precision i) → M)
(hf : ∀ i, _root_.Topology.IsOpenEmbedding (f i))
(hdisj : Pairwise (fun i j => Disjoint (range (f i)) (range (f j))))
(hs : ∀ i, IsLocalDiffeomorph ((𝓡 2).prod 𝓘(ℝ)) I ∞ (f i))
(U : Opens M) (g : SmoothRiemannianMetric I U)
(R : Set (ConnectedComponents (cutCore f)))
(hRet : MapsTo (Subtype.val : cutCore f → M) (retainedCore f R) U)
(c : ℝ) (hc : 4 ≤ c)
(x₀ : ι → U) (order : ι → ℕ)
(d₀ : ∀ i, normalizedDatum g (x₀ i) (precision i) (order i))
(hOriginal : ∀ i, f i = neckAmbientMap U (d₀ i))
{k' : {b : ι × Bool // cuttingSphereComponent hδ f hf hdisj b ∈ R} → ℕ}
(hrec : ∀ b : {b : ι × Bool // cuttingSphereComponent hδ f hf hdisj b ∈ R}, (c * precision b.val.1)⁻¹ + 1 ≤ (precision b.val.1)⁻¹)
(d : ∀ b : {b : ι × Bool // cuttingSphereComponent hδ f hf hdisj b ∈ R}, normalizedDatum g
  ((d₀ b.val.1).offsetPoint (cuttingSign_sq b.val.2)) (c * precision b.val.1) (k' b))
(hmap : ∀ b : {b : ι × Bool // cuttingSphereComponent hδ f hf hdisj b ∈ R}, (d b).map = (d₀ b.val.1).recenteringMap (cuttingSign_sq b.val.2) (hrec b))
(hside : ∀ b : {b : ι × Bool // cuttingSphereComponent hδ f hf hdisj b ∈ R}, (d b).retainedSide = true)
{A D ε : ℝ} {hA : 0 < A} {m : ℕ}
(w : ∀ b : {b : ι × Bool // cuttingSphereComponent hδ f hf hdisj b ∈ R}, CanonicalStaticInsertionWitness (d b) A hA D m ε),
      ε ≤ 1 / 2 → R₀ + 1 < D →
      ∀ b : {b : ι × Bool // cuttingSphereComponent hδ f hf hdisj b ∈ R},
      ∀ p : standardCapWindow D, ‖p.val‖ ≤ R₀ →
      let : LocallyPathConnectedSpace M := originalModel_locallyPathConnected I Fact.out
      let Qcap := FiniteCapQuotient transitionEnd_pos hδ f (fun i => (hf i).injective) hdisj
      let : ChartedSpace ThreeSpace Qcap := finiteCapChartedSpace I Fact.out transitionEnd_pos hδ f hf hdisj
      let : IsManifold (𝓡 3) ∞ Qcap := finiteCapQuotient_isManifold Fact.out transitionEnd_pos hδ f hf hdisj hs
      let : T2Space Qcap := finiteCapQuotient_t2Space transitionEnd_pos hδ f hf hdisj
      let gRet := finiteFullPreparedMetric I hδ f hf hdisj hs U g R hRet c hc x₀ order d₀ hOriginal hrec d hmap hside w
      let F := finiteFullWitnessMap I Fact.out transitionEnd_pos hδ f hf hdisj hs R c hc b
      let Φ := F ∘ (w b).window
      let Q := metricScalarAt g ((d₀ b.val.1).offsetPoint (cuttingSign_sq b.val.2))
      riemannianBallOf (scaleMetric Q (d b).scalar_pos gRet) (Φ p) δ ⊆
        Φ '' {x : standardCapWindow D | dist x.val p.val ≤ 1} := by
  obtain ⟨δ, hδ, hcapture⟩ := exists_uniform_window_isometric_ball_capture R₀
  refine ⟨δ, hδ, ?_⟩
  intro E H M _ _ _ _ _ I _ _ _ _ _ ι _ precision hprecision f hf hdisj hs U g R hRet
    c hc x₀ order d₀ hOriginal k' hrec d hmap hside A D ε hA m w heps hRD b p hp
  let : LocallyPathConnectedSpace M := originalModel_locallyPathConnected I Fact.out
  let Qcap := FiniteCapQuotient transitionEnd_pos hprecision f (fun i => (hf i).injective) hdisj
  let : ChartedSpace ThreeSpace Qcap := finiteCapChartedSpace I Fact.out transitionEnd_pos hprecision f hf hdisj
  let : IsManifold (𝓡 3) ∞ Qcap := finiteCapQuotient_isManifold Fact.out transitionEnd_pos hprecision f hf hdisj hs
  let : T2Space Qcap := finiteCapQuotient_t2Space transitionEnd_pos hprecision f hf hdisj
  dsimp only
  exact hcapture (w b) heps hRD
    (finiteFullPreparedMetric I hprecision f hf hdisj hs U g R hRet c hc x₀ order d₀ hOriginal hrec d hmap hside w)
    (finiteFullWitnessMap I Fact.out transitionEnd_pos hprecision f hf hdisj hs R c hc b)
    (isLocalDiffeomorph_finiteFullWitnessMap I Fact.out transitionEnd_pos hprecision f hf hdisj hs R c hc b)
    (injective_finiteFullWitnessMap I Fact.out transitionEnd_pos hprecision f hf hdisj hs R c hc b)
    (finiteFullPreparedMetric_witness_inner I hprecision f hf hdisj hs U g R hRet c hc
      x₀ order d₀ hOriginal hrec d hmap hside w b) p hp


theorem exists_uniform_finiteFullPreparedMetric_window_or_retained_ball :
    ∃ δ : ℝ, 0 < δ ∧
      ∀ {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
[Fact (Module.finrank ℝ E = 3)] [TopologicalSpace H] (I : ModelWithCorners ℝ E H) [I.Boundaryless]
[TopologicalSpace M] [ChartedSpace H M] [T2Space M] [IsManifold I ∞ M]
{ι : Type*} [Finite ι] {precision : ι → ℝ}
(hδ : ∀ i, 0 < precision i) (f : ∀ i : ι, bufferedCylinder (precision i) → M)
(hf : ∀ i, _root_.Topology.IsOpenEmbedding (f i))
(hdisj : Pairwise (fun i j => Disjoint (range (f i)) (range (f j))))
(hs : ∀ i, IsLocalDiffeomorph ((𝓡 2).prod 𝓘(ℝ)) I ∞ (f i))
(U : Opens M) (g : SmoothRiemannianMetric I U)
(R : Set (ConnectedComponents (cutCore f)))
(hRet : MapsTo (Subtype.val : cutCore f → M) (retainedCore f R) U)
(c : ℝ) (hc : 4 ≤ c)
(x₀ : ι → U) (order : ι → ℕ)
(d₀ : ∀ i, normalizedDatum g (x₀ i) (precision i) (order i))
(hOriginal : ∀ i, f i = neckAmbientMap U (d₀ i))
{k' : {b : ι × Bool // cuttingSphereComponent hδ f hf hdisj b ∈ R} → ℕ}
(hrec : ∀ b : {b : ι × Bool // cuttingSphereComponent hδ f hf hdisj b ∈ R}, (c * precision b.val.1)⁻¹ + 1 ≤ (precision b.val.1)⁻¹)
(d : ∀ b : {b : ι × Bool // cuttingSphereComponent hδ f hf hdisj b ∈ R}, normalizedDatum g
  ((d₀ b.val.1).offsetPoint (cuttingSign_sq b.val.2)) (c * precision b.val.1) (k' b))
(hmap : ∀ b : {b : ι × Bool // cuttingSphereComponent hδ f hf hdisj b ∈ R}, (d b).map = (d₀ b.val.1).recenteringMap (cuttingSign_sq b.val.2) (hrec b))
(hside : ∀ b : {b : ι × Bool // cuttingSphereComponent hδ f hf hdisj b ∈ R}, (d b).retainedSide = true)
{A D ε : ℝ} {hA : 0 < A} {m : ℕ}
(w : ∀ b : {b : ι × Bool // cuttingSphereComponent hδ f hf hdisj b ∈ R}, CanonicalStaticInsertionWitness (d b) A hA D m ε),
      ε ≤ 1 / 2 → transitionEnd + 1 < D →
      let : LocallyPathConnectedSpace M := originalModel_locallyPathConnected I Fact.out
      let Qcap := FiniteCapQuotient transitionEnd_pos hδ f (fun i => (hf i).injective) hdisj
      let : ChartedSpace ModelGE3 Qcap := finiteCapChartedSpace I Fact.out transitionEnd_pos hδ f hf hdisj
      let : IsManifold (𝓡 3) ∞ Qcap := finiteCapQuotient_isManifold Fact.out transitionEnd_pos hδ f hf hdisj hs
      let : T2Space Qcap := finiteCapQuotient_t2Space transitionEnd_pos hδ f hf hdisj
      let gRet := finiteFullPreparedMetric I hδ f hf hdisj hs U g R hRet c hc x₀ order d₀ hOriginal hrec d hmap hside w
      ∀ (q : finiteCapRetained transitionEnd_pos hδ f hf hdisj R) (r : ℝ),
        (∀ b : {b : ι × Bool // cuttingSphereComponent hδ f hf hdisj b ∈ R},
          Real.sqrt (metricScalarAt g ((d₀ b.val.1).offsetPoint (cuttingSign_sq b.val.2))) * r ≤ δ) →
        (∃ b : {b : ι × Bool // cuttingSphereComponent hδ f hf hdisj b ∈ R},
          ∃ x : standardCapWindow D, ‖x.val‖ ≤ transitionEnd + 1 ∧
            finiteFullWitnessMap I Fact.out transitionEnd_pos hδ f hf hdisj hs R c hc b
              ((w b).window x) = q) ∨
          riemannianBallOf gRet q r ⊆
            interior (range (finiteRetainedCoreInclusion transitionEnd_pos hδ f hf hdisj R)) := by
  obtain ⟨δ, hδpos, hcapture⟩ := exists_uniform_finiteFullPreparedMetric_window_ball_capture transitionEnd
  refine ⟨δ, hδpos, ?_⟩
  intro E H M _ _ _ _ _ I _ _ _ _ _ ι _ precision hδ f hf hdisj hs U g R hRet
    c hc x₀ order d₀ hOriginal k' hrec d hmap hside A D ε hA m w heps hD
  let : LocallyPathConnectedSpace M := originalModel_locallyPathConnected I Fact.out
  let Qcap := FiniteCapQuotient transitionEnd_pos hδ f (fun i => (hf i).injective) hdisj
  let : ChartedSpace ModelGE3 Qcap := finiteCapChartedSpace I Fact.out transitionEnd_pos hδ f hf hdisj
  let : IsManifold (𝓡 3) ∞ Qcap := finiteCapQuotient_isManifold Fact.out transitionEnd_pos hδ f hf hdisj hs
  let : T2Space Qcap := finiteCapQuotient_t2Space transitionEnd_pos hδ f hf hdisj
  let gRet := finiteFullPreparedMetric I hδ f hf hdisj hs U g R hRet c hc x₀ order d₀ hOriginal hrec d hmap hside w
  dsimp only
  intro q r hscale
  classical
  by_cases hq : ∃ b : {b : ι × Bool // cuttingSphereComponent hδ f hf hdisj b ∈ R},
      ∃ x : standardCapWindow D, ‖x.val‖ ≤ transitionEnd + 1 ∧
        finiteFullWitnessMap I Fact.out transitionEnd_pos hδ f hf hdisj hs R c hc b
          ((w b).window x) = q
  · exact Or.inl hq
  right
  intro y hy
  by_contra hyold
  obtain ⟨b, p, hp, himage⟩ := finiteFullWitnessMap_exists_window_preimage_of_notMem_retainedInterior
    I hδ f hf hdisj hs R c hc U g (fun b => (d₀ b.val.1).offsetPoint (cuttingSign_sq b.val.2))
    k' d w (by linarith) y hyold
  let F := finiteFullWitnessMap I Fact.out transitionEnd_pos hδ f hf hdisj hs R c hc b
  let Q := metricScalarAt g ((d₀ b.val.1).offsetPoint (cuttingSign_sq b.val.2))
  have hback : q ∈ riemannianBallOf gRet (F ((w b).window p)) r := by
    change riemannianEDistOf gRet (F ((w b).window p)) q < ENNReal.ofReal r
    rw [show F ((w b).window p) = y from himage, riemannianEDistOf_comm]
    exact hy
  have hnormalized : q ∈ riemannianBallOf (scaleMetric Q (d b).scalar_pos gRet)
      (F ((w b).window p)) δ := by
    apply riemannianBallOf_mono _ _ (hscale b)
    rwa [riemannianBallOf_scaleMetric]
  obtain ⟨x, hx, hxq⟩ := hcapture I hδ f hf hdisj hs U g R hRet c hc x₀ order d₀ hOriginal
    hrec d hmap hside w heps hD b p hp hnormalized
  apply hq
  refine ⟨b, x, ?_, hxq⟩
  change dist x.val p.val ≤ 1 at hx
  have hn := norm_le_norm_sub_add x.val p.val
  rw [← dist_eq_norm] at hn
  linarith

end

end DifferentialGeometry.PDE.RicciFlow.StandardCap
