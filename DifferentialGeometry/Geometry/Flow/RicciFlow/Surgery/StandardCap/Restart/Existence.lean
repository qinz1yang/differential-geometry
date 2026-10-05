import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.StandardCap.FullMetricBallVolume
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.ControlledRestart
import DifferentialGeometry.Geometry.Curvature.CurvatureOperator.Derivatives.Scaling

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

theorem finiteFullPreparedMetric_exists_flow_tip_ball_volume_ge [SigmaCompactSpace M]
    (b : CurvGB) (heps : ε ≤ 1 / 2) {ρ : ℝ} (hρ : 0 < ρ) (hρD : ρ < D)
    {P a B : ℝ} (hP : 0 < P) :
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
    ∀ [CompactSpace CurvGRet], P ≤ a * Q →
      (∀ x, Surgery.Topology.InFixedHamiltonIveyRegion gRet a x) →
      (∀ x, metricScalarAt gRet x ≤ B * Q) →
      let K := 2 * Real.sqrt 3 * (max B 0 / 2 + max B (Real.exp 4 / P))
      let τ := compactCurvatureControlTime 3 K
      let L := Real.sqrt (2 * K ^ 2 + 1)
      ∃ T : ℝ, τ < T ∧ ∃ G : FlowTo (scaleMetric Q (d b).scalar_pos gRet) T,
        ∀ t ∈ Icc 0 τ,
          ENNReal.ofReal (Real.exp (-(27 * L * τ))) * (ENNReal.ofReal (1 / 4 : ℝ) *
            riemannianVolumeMeasure (𝓡 3) CurvGE3 metric
              (Metric.closedBall (0 : CurvGE3) (Real.exp (-(9 * L * τ)) * ρ / 4))) ≤
          riemannianVolumeMeasure (𝓡 3) CurvGRet (G.S.base.metric t)
            (riemannianBallOf (G.S.base.metric t) (F ((w b).data.tip)) ρ) := by
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
  intro _ ha hfixed hscalar
  let K := 2 * Real.sqrt 3 * (max B 0 / 2 + max B (Real.exp 4 / P))
  let τ := compactCurvatureControlTime 3 K
  let L := Real.sqrt (2 * K ^ 2 + 1)
  have hQ : 0 < Q := (d b).scalar_pos
  obtain ⟨T, hT, G, hbound⟩ :=
    Surgery.Topology.exists_compact_flow_of_normalized_scalar_bound_of_fixedHamiltonIveyRegion
      gRet hP hQ ha hfixed hscalar
  let H := G.scale Q hQ
  have hτ : 0 < τ := compactCurvatureControlTime_pos 3 K
  have htime : τ < Q * T := by
    exact (div_lt_iff₀ hQ).mp hT |>.trans_le (by rw [mul_comm])
  refine ⟨Q * T, htime, H, ?_⟩
  apply finiteFullPreparedMetric_tip_ball_volume_ge_on_curvature_controlled_flow I hδ f hf hdisj hs
    U g R hRet c hc x₀ order d₀ hOriginal hrec d hmap hside w b heps hρ hρD
    τ L hτ.le (Real.sqrt_nonneg _) _ H.S H.isSolution H.start
    (fun t ht => ⟨ht.1, ht.2.trans_lt htime⟩)
    (fun t ht => ⟨ht.1, ht.2.trans htime⟩)
  intro t ht x
  have hnorm := hbound (t / Q) ⟨div_nonneg ht.1 hQ.le,
    (div_le_div_iff_of_pos_right hQ).mpr ht.2⟩ x
  have hscale := CheegerGromovCompactness.curvDerivNorm_scaleMetric
    (G.S.base.metric (t / Q)) Q hQ 0 x
  have heq : Real.sqrt (Tensor0SBundle.normSq0S (H.S.base.metric t) x 4
      (H.S.base.rm04 t x)) =
      Real.sqrt (Tensor0SBundle.normSq0S (G.S.base.metric (t / Q)) x 4
        (metricRm04 (G.S.base.metric (t / Q)) x)) / Q := by
    rw [show H.S.base.metric t = scaleMetric Q hQ (G.S.base.metric (t / Q)) from rfl]
    convert! hscale using 1
    simp only [pow_zero, mul_one]
    rfl
  rw [heq]
  exact (div_le_iff₀ hQ).mpr hnorm

end DifferentialGeometry.PDE.RicciFlow.StandardCap
