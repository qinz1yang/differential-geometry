import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.StandardCap.FullMetricWindowCover
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.StandardCap.FullMetricWindowCapture
import DifferentialGeometry.Geometry.Comparison.Distance.Calabi
import DifferentialGeometry.Topology.FirstExit
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
private theorem first_exit_distance_lower
    {X : Type*} [TopologicalSpace X] [ChartedSpace ThreeSpace X]
    [IsManifold ThreeModel ∞ X]
    (gX : SmoothRiemannianMetric ThreeModel X) {K : Set X} (hK : IsClosed K)
    (pole : X) {R T : ℝ} (hR : 0 < R) (hT : 0 < T)
    (hball : riemannianBallOf gX pole R ⊆ interior K)
    (γ : ℝ → X) (hγ : ContMDiffOn 𝓘(ℝ, ℝ) ThreeModel 1 γ (Icc 0 T))
    (hstart : γ 0 ∈ riemannianBallOf gX pole (R / 2))
    (hexit : γ T ∉ K) :
    ∃ τ : ℝ, τ ∈ Ioc 0 T ∧ (∀ t ∈ Icc 0 τ, γ t ∈ K) ∧ γ τ ∈ frontier K ∧
      ENNReal.ofReal (R / 2) ≤ riemannianEDistOf gX (γ 0) (γ τ) ∧
      riemannianEDistOf gX (γ 0) (γ τ) ≠ ⊤ ∧
      R / 2 ≤ (riemannianEDistOf gX (γ 0) (γ τ)).toReal := by
  have hstartR : γ 0 ∈ riemannianBallOf gX pole R :=
    hstart.trans_le (ENNReal.ofReal_le_ofReal (by linarith))
  obtain ⟨τ, hτ, hstay, hfront⟩ := DifferentialGeometry.exists_first_exit_frontier
    hK hT hγ.continuousOn (hball hstartR) hexit
  have hfar : ENNReal.ofReal R ≤ riemannianEDistOf gX pole (γ τ) := by
    apply le_of_not_gt
    intro hlt
    exact hfront.2 (hball hlt)
  have hdist : ENNReal.ofReal (R / 2) ≤ riemannianEDistOf gX (γ 0) (γ τ) := by
    have hR2 : 0 ≤ R / 2 := by linarith
    by_contra hnot
    have hh : riemannianEDistOf gX pole (γ τ) < ENNReal.ofReal R := by
      calc
        _ ≤ riemannianEDistOf gX pole (γ 0) + riemannianEDistOf gX (γ 0) (γ τ) :=
          riemannianEDistOf_triangle gX pole (γ 0) (γ τ)
        _ < ENNReal.ofReal (R / 2) + ENNReal.ofReal (R / 2) :=
          ENNReal.add_lt_add hstart (lt_of_not_ge hnot)
        _ = ENNReal.ofReal R := by
          rw [← ENNReal.ofReal_add hR2 hR2]
          congr 1
          ring
    exact (not_lt_of_ge hfar) hh
  have hfinite : riemannianEDistOf gX (γ 0) (γ τ) ≠ ⊤ :=
    ne_top_of_le_ne_top ENNReal.ofReal_ne_top
      (DifferentialGeometry.edistOf_le_arcLength gX hτ.1.le
        (hγ.mono (Icc_subset_Icc le_rfl hτ.2)))
  refine ⟨τ, hτ, hstay, hfront, hdist, hfinite, ?_⟩
  exact (ENNReal.ofReal_le_iff_le_toReal hfinite).mp hdist

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


theorem finiteFullPreparedMetric_exists_window_first_exit_distance
    (b : ModelGB) (heps : ε ≤ 1 / 2) {ρ : ℝ} (hρ : 0 < ρ) (hρD : ρ < D) :
    let : LocallyPathConnectedSpace M := originalModel_locallyPathConnected I Fact.out
    let : ChartedSpace ModelGE3 ModelGQ := finiteCapChartedSpace I Fact.out transitionEnd_pos hδ f hf hdisj
    let : IsManifold (𝓡 3) ∞ ModelGQ := finiteCapQuotient_isManifold Fact.out transitionEnd_pos hδ f hf hdisj hs
    let : T2Space ModelGQ := finiteCapQuotient_t2Space transitionEnd_pos hδ f hf hdisj
    let gRet := finiteFullPreparedMetric I hδ f hf hdisj hs U g R hRet c hc x₀ order d₀ hOriginal hrec d hmap hside w
    let F := finiteFullWitnessMap I Fact.out transitionEnd_pos hδ f hf hdisj hs R c hc b
    let Φ := F ∘ (w b).window
    let Q := metricScalarAt g ((d₀ b.val.1).offsetPoint (cuttingSign_sq b.val.2))
    let gQ := scaleMetric Q (d b).scalar_pos gRet
    let K := Φ '' {x : standardCapWindow D | ‖x.val‖ ≤ ρ}
    ∀ (γ : ℝ → ModelGRet) {T : ℝ}, 0 < T →
      ContMDiffOn 𝓘(ℝ, ℝ) ThreeModel 1 γ (Icc 0 T) →
      γ 0 ∈ Φ '' {x : standardCapWindow D | ‖x.val‖ ≤ ρ / 32} → γ T ∉ K →
      ∃ τ : ℝ, τ ∈ Ioc 0 T ∧ (∀ t ∈ Icc 0 τ, γ t ∈ K) ∧ γ τ ∈ frontier K ∧
        ENNReal.ofReal (ρ / 4) ≤ riemannianEDistOf gQ (γ 0) (γ τ) ∧
        riemannianEDistOf gQ (γ 0) (γ τ) ≠ ⊤ ∧
        ρ / 4 ≤ (riemannianEDistOf gQ (γ 0) (γ τ)).toReal := by
  let : LocallyPathConnectedSpace M := originalModel_locallyPathConnected I Fact.out
  let : ChartedSpace ModelGE3 ModelGQ := finiteCapChartedSpace I Fact.out transitionEnd_pos hδ f hf hdisj
  let : IsManifold (𝓡 3) ∞ ModelGQ := finiteCapQuotient_isManifold Fact.out transitionEnd_pos hδ f hf hdisj hs
  let : T2Space ModelGQ := finiteCapQuotient_t2Space transitionEnd_pos hδ f hf hdisj
  let gRet := finiteFullPreparedMetric I hδ f hf hdisj hs U g R hRet c hc x₀ order d₀ hOriginal hrec d hmap hside w
  let F := finiteFullWitnessMap I Fact.out transitionEnd_pos hδ f hf hdisj hs R c hc b
  let Φ := F ∘ (w b).window
  let Q := metricScalarAt g ((d₀ b.val.1).offsetPoint (cuttingSign_sq b.val.2))
  let gQ := scaleMetric Q (d b).scalar_pos gRet
  let K := Φ '' {x : standardCapWindow D | ‖x.val‖ ≤ ρ}
  dsimp only
  intro γ T hT hγ hstart hexit
  have hΦ : Continuous Φ :=
    (contMDiff_finiteFullWitnessMap I Fact.out transitionEnd_pos hδ f hf hdisj hs R c hc b).continuous.comp
      (w b).window.continuous
  have hsource : IsCompact {x : standardCapWindow D | ‖x.val‖ ≤ ρ} := by
    apply _root_.Topology.IsInducing.subtypeVal.isCompact_preimage'
      (show IsCompact {x : ThreeSpace | ‖x‖ ≤ ρ} from by
        simpa only [Metric.closedBall, dist_zero_right] using isCompact_closedBall (0 : ThreeSpace) ρ)
    intro x hx
    refine ⟨⟨x, ?_⟩, rfl⟩
    change ‖x‖ < D + 1
    change ‖x‖ ≤ ρ at hx
    linarith
  have hK : IsCompact K := hsource.image hΦ
  have hcap : riemannianBallOf gQ (F ((w b).data.tip)) (ρ / 2) ⊆ K :=
    finiteFullPreparedMetric_normalized_tip_ball_subset_window_image
      I hδ f hf hdisj hs U g R hRet c hc x₀ order d₀ hOriginal hrec d hmap hside w b heps hρ hρD
  have hopen : IsOpen (riemannianBallOf gQ (F ((w b).data.tip)) (ρ / 2)) :=
    isOpen_lt (continuous_riemannianEDist gQ _) continuous_const
  have hinterior := interior_maximal hcap hopen
  have hstart8 : γ 0 ∈ riemannianBallOf gQ (F ((w b).data.tip)) (ρ / 8) := by
    have hh := finiteFullPreparedMetric_window_image_subset_normalized_tip_ball
      I hδ f hf hdisj hs U g R hRet c hc x₀ order d₀ hOriginal hrec d hmap hside w b heps
      (by linarith : 0 < ρ / 8) (by linarith : ρ / 8 < D)
    apply hh
    have hr32 : (ρ / 8) / 4 = ρ / 32 := by ring
    simpa only [hr32] using hstart
  have hstart4 : γ 0 ∈ riemannianBallOf gQ (F ((w b).data.tip)) ((ρ / 2) / 2) :=
    hstart8.trans_le (ENNReal.ofReal_le_ofReal (by linarith))
  obtain ⟨τ, hτ, hstay, hfront, hdistENN, hfinite, hdist⟩ :=
    first_exit_distance_lower gQ hK.isClosed (F ((w b).data.tip)) (half_pos hρ) hT
      hinterior γ hγ hstart4 hexit
  have hr4 : (ρ / 2) / 2 = ρ / 4 := by ring
  rw [hr4] at hdist hdistENN
  exact ⟨τ, hτ, hstay, hfront, hdistENN, hfinite, hdist⟩

end DifferentialGeometry.PDE.RicciFlow.StandardCap
