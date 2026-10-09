import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.StandardCap.FullMetricModels
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.StandardCap.CanonicalStaticWindow
import DifferentialGeometry.Geometry.Flow.RicciFlow.Solution.LocalPullback
import DifferentialGeometry.Geometry.Metric.Family.JointSmoothness

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


theorem finiteFullPreparedMetric_exists_window_pullback_solution [SigmaCompactSpace M]
    (b : ModelGB) :
    let : LocallyPathConnectedSpace M := originalModel_locallyPathConnected I Fact.out
    let : ChartedSpace ModelGE3 ModelGQ := finiteCapChartedSpace I Fact.out transitionEnd_pos hδ f hf hdisj
    let : IsManifold (𝓡 3) ∞ ModelGQ := finiteCapQuotient_isManifold Fact.out transitionEnd_pos hδ f hf hdisj hs
    let : T2Space ModelGQ := finiteCapQuotient_t2Space transitionEnd_pos hδ f hf hdisj
    let : SigmaCompactSpace ModelGQ := finiteCapQuotient_sigmaCompactSpace transitionEnd_pos hδ f hf hdisj
    let : SigmaCompactSpace ModelGRet := isSigmaCompact_iff_sigmaCompactSpace.mp
      (DifferentialGeometry.Geometry.isSigmaCompact_of_isOpen (𝓡 3) (ModelGRet).isOpen)
    let gRet := finiteFullPreparedMetric I hδ f hf hdisj hs U g R hRet c hc x₀ order d₀ hOriginal hrec d hmap hside w
    let F := finiteFullWitnessMap I Fact.out transitionEnd_pos hδ f hf hdisj hs R c hc b
    let Φ := F ∘ (w b).window
    let Q := metricScalarAt g ((d₀ b.val.1).offsetPoint (cuttingSign_sq b.val.2))
    ∀ (Δ : RealTimeInterval) (S : SolutionOn (I := 𝓡 3) (M := ModelGRet) Δ),
      IsSolutionOn S → S.base.metric 0 = scaleMetric Q (d b).scalar_pos gRet →
      ∃ L : SolutionOn (I := 𝓡 3) (M := standardCapWindow D) Δ,
        IsSolutionOn L ∧ L.base.metric 0 = (w b).windowMetric ∧
        (∀ t (x : standardCapWindow D) (v z : TangentSpace (𝓡 3) x),
          (L.base.metric t).inner x v z = (S.base.metric t).inner (Φ x)
            (mfderiv (𝓡 3) (𝓡 3) Φ x v) (mfderiv (𝓡 3) (𝓡 3) Φ x z)) ∧
        (∀ J : Set ℝ,
          (∀ (p : ModelGRet) (i j : Fin (Module.finrank ℝ ModelGE3)),
            ContMDiffOn (𝓘(ℝ, ℝ).prod (𝓡 3)) 𝓘(ℝ) ∞
              (fun q : ℝ × ModelGRet =>
                DifferentialGeometry.Tensor.Coordinates.chartGramMatrix (S.base.metric q.1) p q.2 i j)
              (J ×ˢ (trivializationAt ModelGE3 (TangentSpace (𝓡 3)) p).baseSet)) →
          ∀ (p : standardCapWindow D) (i j : Fin (Module.finrank ℝ ModelGE3)),
            ContMDiffOn (𝓘(ℝ, ℝ).prod (𝓡 3)) 𝓘(ℝ) ∞
              (fun q : ℝ × standardCapWindow D =>
                DifferentialGeometry.Tensor.Coordinates.chartGramMatrix (L.base.metric q.1) p q.2 i j)
              (J ×ˢ (trivializationAt ModelGE3 (TangentSpace (𝓡 3)) p).baseSet)) := by
  let : LocallyPathConnectedSpace M := originalModel_locallyPathConnected I Fact.out
  let : ChartedSpace ModelGE3 ModelGQ := finiteCapChartedSpace I Fact.out transitionEnd_pos hδ f hf hdisj
  let : IsManifold (𝓡 3) ∞ ModelGQ := finiteCapQuotient_isManifold Fact.out transitionEnd_pos hδ f hf hdisj hs
  let : T2Space ModelGQ := finiteCapQuotient_t2Space transitionEnd_pos hδ f hf hdisj
  let : SigmaCompactSpace ModelGQ := finiteCapQuotient_sigmaCompactSpace transitionEnd_pos hδ f hf hdisj
  let : SigmaCompactSpace ModelGRet := isSigmaCompact_iff_sigmaCompactSpace.mp
    (DifferentialGeometry.Geometry.isSigmaCompact_of_isOpen (𝓡 3) (ModelGRet).isOpen)
  let gRet := finiteFullPreparedMetric I hδ f hf hdisj hs U g R hRet c hc x₀ order d₀ hOriginal hrec d hmap hside w
  let F := finiteFullWitnessMap I Fact.out transitionEnd_pos hδ f hf hdisj hs R c hc b
  let Φ := F ∘ (w b).window
  let Q := metricScalarAt g ((d₀ b.val.1).offsetPoint (cuttingSign_sq b.val.2))
  dsimp only
  intro Δ S hS hstart
  have hF := isLocalDiffeomorph_finiteFullWitnessMap I Fact.out transitionEnd_pos hδ f hf hdisj hs R c hc b
  have hΦ : IsLocalDiffeomorph (𝓡 3) (𝓡 3) ∞ Φ :=
    fun q => ((w b).properties.window_local q).comp (𝓡 3) ModelGRet (hF ((w b).window q))
  let L := S.localPullback Φ hΦ
  refine ⟨L, hS.localPullback Φ hΦ, ?_, ?_, ?_⟩
  · apply SmoothRiemannianMetric.ext_inner
    intro x v z
    change (localPullMetric (S.base.metric 0) Φ hΦ).inner x v z = _
    rw [localPullMetric_inner, hstart, scaleMetric_inner, (w b).window_inner]
    have hcomp := metric_inner_comp_of_isometry (w b).data.outMetric gRet F
      (contMDiff_finiteFullWitnessMap I Fact.out transitionEnd_pos hδ f hf hdisj hs R c hc b)
      (finiteFullPreparedMetric_witness_inner I hδ f hf hdisj hs U g R hRet c hc
        x₀ order d₀ hOriginal hrec d hmap hside w b)
      (w b).window (w b).window_smooth.contMDiff x v z
    exact congrArg (fun a => Q * a) hcomp
  · intro t x v z
    exact localPullMetric_inner (S.base.metric t) Φ hΦ x v z
  · intro J hgram p i j
    exact S.localPullback_chartGramMatrix_joint_contMDiffOn Φ hΦ J hgram p i j

end DifferentialGeometry.PDE.RicciFlow.StandardCap
