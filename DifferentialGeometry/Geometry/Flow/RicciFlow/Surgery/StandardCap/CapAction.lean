import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.StandardCap.FirstExit
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.LGeometry.Action.Estimates.Curvature

set_option autoImplicit false
noncomputable section
open Set Function TopologicalSpace Manifold DifferentialGeometry
open DifferentialGeometry.Geometry.Neck DifferentialGeometry.Geometry.Metric DifferentialGeometry.Topology.ThreeManifold.Surgery DifferentialGeometry.Topology.Manifold.Attachment
open DifferentialGeometry.Tensor0SBundle DifferentialGeometry.CheegerGromovCompactness
open DifferentialGeometry.Topology.Manifold
open DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
open DifferentialGeometry.Geometry.Riemannian
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.PDE.RicciFlow.Perelman
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


theorem finiteFullPreparedMetric_action_ge_of_leaves_window
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
    ∀ (Δ : RealTimeInterval) (S : SolutionOn (I := ThreeModel) (M := ModelGRet) Δ),
      IsSolutionOn S → ∀ (poleClock : ℝ) (γ : ℝ → ModelGRet) {v μ B : ℝ},
      0 ≤ μ → 0 ≤ B → ContMDiff 𝓘(ℝ, ℝ) ThreeModel 1 γ →
      (∀ u ∈ Icc 0 v, poleClock - u ^ 2 ∈ Δ.carrier) →
      (∀ u ∈ Icc 0 v, γ u ∈ K →
        μ * gQ.inner (γ u) (lVelocity γ u) (lVelocity γ u) ≤
          (S.base.metric (poleClock - u ^ 2)).inner (γ u) (lVelocity γ u) (lVelocity γ u)) →
      (∀ u ∈ Icc 0 v, -B ≤ S.scalar (poleClock - u ^ 2) (γ u)) →
      γ 0 ∈ Φ '' {x : standardCapWindow D | ‖x.val‖ ≤ ρ / 32} →
      (∃ u ∈ Ioc 0 v, γ u ∉ K) →
      μ * ρ ^ 2 / (32 * v) - 2 * B * v ^ 3 ≤ lRegularizedAction S poleClock γ 0 v := by
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
  intro Δ S hS poleClock γ v μ B hμ hB hγ htime hmetric hscalar hstart hexit
  obtain ⟨u, hu, hexit⟩ := hexit
  obtain ⟨τ, hτ, hstay, _, hsep, _, _⟩ :=
    finiteFullPreparedMetric_exists_window_first_exit_distance
      I hδ f hf hdisj hs U g R hRet c hc x₀ order d₀ hOriginal hrec d hmap hside w b heps hρ hρD
      γ hu.1 hγ.contMDiffOn hstart hexit
  have hact := lRegularizedAction_ge_of_initial_segment_separation S hS poleClock γ
    hτ.1 (hτ.2.trans hu.2) hμ hB (by linarith : 0 ≤ ρ / 4) gQ hγ htime
    (fun s hs => hmetric s ⟨hs.1, hs.2.trans (hτ.2.trans hu.2)⟩ (hstay s hs)) hscalar hsep
  convert hact using 1
  ring

theorem finiteFullPreparedMetric_curve_mem_window_of_action_lt
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
    ∀ (Δ : RealTimeInterval) (S : SolutionOn (I := ThreeModel) (M := ModelGRet) Δ),
      IsSolutionOn S → ∀ (poleClock : ℝ) (γ : ℝ → ModelGRet) {v μ B : ℝ},
      0 ≤ μ → 0 ≤ B → ContMDiff 𝓘(ℝ, ℝ) ThreeModel 1 γ →
      (∀ u ∈ Icc 0 v, poleClock - u ^ 2 ∈ Δ.carrier) →
      (∀ u ∈ Icc 0 v, γ u ∈ K →
        μ * gQ.inner (γ u) (lVelocity γ u) (lVelocity γ u) ≤
          (S.base.metric (poleClock - u ^ 2)).inner (γ u) (lVelocity γ u) (lVelocity γ u)) →
      (∀ u ∈ Icc 0 v, -B ≤ S.scalar (poleClock - u ^ 2) (γ u)) →
      γ 0 ∈ Φ '' {x : standardCapWindow D | ‖x.val‖ ≤ ρ / 32} →
      lRegularizedAction S poleClock γ 0 v < μ * ρ ^ 2 / (32 * v) - 2 * B * v ^ 3 →
      ∀ u ∈ Icc 0 v, γ u ∈ K := by
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
  intro Δ S hS poleClock γ v μ B hμ hB hγ htime hmetric hscalar hstart hact u hu
  by_contra hnot
  have hu0 : 0 < u := by
    by_contra hn
    have hueq : u = 0 := le_antisymm (le_of_not_gt hn) hu.1
    subst u
    apply hnot
    obtain ⟨x, hx, hx0⟩ := hstart
    change ‖x.val‖ ≤ ρ / 32 at hx
    exact ⟨x, (show ‖x.val‖ ≤ ρ by linarith), hx0⟩
  have hge := finiteFullPreparedMetric_action_ge_of_leaves_window
    I hδ f hf hdisj hs U g R hRet c hc x₀ order d₀ hOriginal hrec d hmap hside w b heps hρ hρD
    Δ S hS poleClock γ hμ hB hγ htime hmetric hscalar hstart ⟨u, ⟨hu0, hu.2⟩, hnot⟩
  exact (not_lt_of_ge hge) hact

end DifferentialGeometry.PDE.RicciFlow.StandardCap
