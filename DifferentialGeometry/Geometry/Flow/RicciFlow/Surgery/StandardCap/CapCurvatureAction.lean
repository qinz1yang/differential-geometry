import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.LGeometry.Ray.SmoothExtension
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.StandardCap.CapAction
import DifferentialGeometry.Geometry.Flow.RicciFlow.Estimates.CurvatureMetricComparison

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
private theorem metric_inner_ge_initial_of_curvature_bound
    {X : Type*} [TopologicalSpace X] [ChartedSpace ThreeSpace X]
    [IsManifold ThreeModel ∞ X] [T2Space X] {Δ : RealTimeInterval}
    (S : SolutionOn (I := ThreeModel) (M := X) Δ) (hS : IsSolutionOn S)
    {σ C t : ℝ} (hC : 0 ≤ C) (hcarrier : Icc 0 σ ⊆ Δ.carrier)
    (hregular : Ioo 0 σ ⊆ Δ.regular) (x : X)
    (hRm : ∀ r ∈ Icc 0 σ,
      Real.sqrt (normSq0S (S.base.metric r) x 4 (S.base.rm04 r x)) ≤ C)
    (ht : t ∈ Icc 0 σ) (v : TangentSpace ThreeModel x) :
    Real.exp (-(18 * C * σ)) * (S.base.metric 0).inner x v v ≤
      (S.base.metric t).inner x v v := by
  have hsq : ∀ r ∈ Icc 0 σ,
      normSq0S (S.base.metric r) x 4 (S.base.rm04 r x) ≤ C ^ 2 := by
    intro r hr
    have hb := hRm r hr
    have hn := normSq0S_nonneg (S.base.metric r) x 4 (S.base.rm04 r x)
    have he := Real.sq_sqrt hn
    nlinarith [Real.sqrt_nonneg (normSq0S (S.base.metric r) x 4 (S.base.rm04 r x))]
  have hcmp := (metric_inner_exp_bounds_of_curvature_bound S hS hcarrier hregular x hsq
    ht ⟨le_rfl, ht.1.trans ht.2⟩ v).1
  have heq : 2 * (Module.finrank ℝ ThreeSpace : ℝ) ^ 2 * Real.sqrt (C ^ 2) * |t - 0| =
      18 * C * t := by
    rw [Real.sqrt_sq hC, sub_zero, abs_of_nonneg ht.1]
    norm_num [ThreeSpace]
  rw [heq] at hcmp
  have htime : 18 * C * t ≤ 18 * C * σ :=
    mul_le_mul_of_nonneg_left ht.2 (by positivity)
  exact (mul_le_mul_of_nonneg_right (Real.exp_le_exp.mpr (neg_le_neg htime))
    (metric_inner_self_nonneg (S.base.metric 0) x v)).trans hcmp

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


theorem finiteFullPreparedMetric_action_ge_of_window_exit_curvature_bound
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
      IsSolutionOn S → S.base.metric 0 = gQ →
      ∀ {σ C : ℝ}, 0 ≤ C → Icc 0 σ ⊆ Δ.carrier → Ioo 0 σ ⊆ Δ.regular →
      (∀ x ∈ K, ∀ t ∈ Icc 0 σ,
        Real.sqrt (normSq0S (S.base.metric t) x 4 (S.base.rm04 t x)) ≤ C) →
      ∀ (poleClock : ℝ) (γ : ℝ → ModelGRet) {v B : ℝ},
      0 ≤ B → ContMDiff 𝓘(ℝ, ℝ) ThreeModel 1 γ →
      (∀ u ∈ Icc 0 v, poleClock - u ^ 2 ∈ Icc 0 σ) →
      (∀ u ∈ Icc 0 v, -B ≤ S.scalar (poleClock - u ^ 2) (γ u)) →
      γ 0 ∈ Φ '' {x : standardCapWindow D | ‖x.val‖ ≤ ρ / 32} →
      (∃ u ∈ Ioc 0 v, γ u ∉ K) →
      Real.exp (-(18 * C * σ)) * ρ ^ 2 / (32 * v) - 2 * B * v ^ 3 ≤ lRegularizedAction S poleClock γ 0 v := by
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
  intro Δ S hS hzero σ C hC hcarrier hregular hRm poleClock γ v B hB hγ htime hscalar hstart hexit
  apply finiteFullPreparedMetric_action_ge_of_leaves_window
    I hδ f hf hdisj hs U g R hRet c hc x₀ order d₀ hOriginal hrec d hmap hside w b heps hρ hρD
    Δ S hS poleClock γ (Real.exp_pos _).le hB hγ (fun u hu => hcarrier (htime u hu))
    ?_ hscalar hstart hexit
  intro u hu hx
  have hcmp := metric_inner_ge_initial_of_curvature_bound S hS hC hcarrier hregular (γ u)
    (hRm (γ u) hx) (htime u hu) (lVelocity γ u)
  rw [hzero] at hcmp
  exact hcmp

theorem finiteFullPreparedMetric_curve_mem_window_of_curvature_bound_action_lt
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
      IsSolutionOn S → S.base.metric 0 = gQ →
      ∀ {σ C : ℝ}, 0 ≤ C → Icc 0 σ ⊆ Δ.carrier → Ioo 0 σ ⊆ Δ.regular →
      (∀ x ∈ K, ∀ t ∈ Icc 0 σ,
        Real.sqrt (normSq0S (S.base.metric t) x 4 (S.base.rm04 t x)) ≤ C) →
      ∀ (poleClock : ℝ) (γ : ℝ → ModelGRet) {v B : ℝ},
      0 ≤ B → ContMDiff 𝓘(ℝ, ℝ) ThreeModel 1 γ →
      (∀ u ∈ Icc 0 v, poleClock - u ^ 2 ∈ Icc 0 σ) →
      (∀ u ∈ Icc 0 v, -B ≤ S.scalar (poleClock - u ^ 2) (γ u)) →
      γ 0 ∈ Φ '' {x : standardCapWindow D | ‖x.val‖ ≤ ρ / 32} →
      lRegularizedAction S poleClock γ 0 v <
        Real.exp (-(18 * C * σ)) * ρ ^ 2 / (32 * v) - 2 * B * v ^ 3 →
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
  intro Δ S hS hzero σ C hC hcarrier hregular hRm poleClock γ v B hB hγ htime hscalar hstart hact
  apply finiteFullPreparedMetric_curve_mem_window_of_action_lt
    I hδ f hf hdisj hs U g R hRet c hc x₀ order d₀ hOriginal hrec d hmap hside w b heps hρ hρD
    Δ S hS poleClock γ (Real.exp_pos _).le hB hγ (fun u hu => hcarrier (htime u hu))
    ?_ hscalar hstart hact
  intro u hu hx
  have hcmp := metric_inner_ge_initial_of_curvature_bound S hS hC hcarrier hregular (γ u)
    (hRm (γ u) hx) (htime u hu) (lVelocity γ u)
  rw [hzero] at hcmp
  exact hcmp

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
theorem finiteFullPreparedMetric_lRegularizedCurve_mem_window_of_action_lt
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
      IsSolutionOn S → S.base.metric 0 = gQ →
      ∀ {σ C : ℝ}, 0 ≤ C → Icc 0 σ ⊆ Δ.carrier → Ioo 0 σ ⊆ Δ.regular →
      (∀ x ∈ K, ∀ t ∈ Icc 0 σ,
        Real.sqrt (normSq0S (S.base.metric t) x 4 (S.base.rm04 t x)) ≤ C) →
      ∀ (poleClock : ℝ) (x : ModelGRet) (Z : TangentSpace ThreeModel x) {v B : ℝ},
      0 < v → v ∈ lRegularizedDomain S poleClock x Z → 0 ≤ B →
      let γ := lRegularizedCurve S poleClock x Z
      (∀ u ∈ Icc 0 v, poleClock - u ^ 2 ∈ Icc 0 σ) →
      (∀ u ∈ Icc 0 v, -B ≤ S.scalar (poleClock - u ^ 2) (γ u)) →
      x ∈ Φ '' {x : standardCapWindow D | ‖x.val‖ ≤ ρ / 32} →
      lRegularizedAction S poleClock γ 0 v <
        Real.exp (-(18 * C * σ)) * ρ ^ 2 / (32 * v) - 2 * B * v ^ 3 →
      ∀ u ∈ Icc 0 v, γ u ∈ K := by
  let : LocallyPathConnectedSpace M := originalModel_locallyPathConnected I Fact.out
  let : ChartedSpace ModelGE3 ModelGQ := finiteCapChartedSpace I Fact.out transitionEnd_pos hδ f hf hdisj
  let : IsManifold (𝓡 3) ∞ ModelGQ := finiteCapQuotient_isManifold Fact.out transitionEnd_pos hδ f hf hdisj hs
  let : T2Space ModelGQ := finiteCapQuotient_t2Space transitionEnd_pos hδ f hf hdisj
  dsimp only
  intro Δ S hS hzero σ C hC hcarrier hregular hRm poleClock x Z v B hv hvdom hB htime hscalar hstart hact
  obtain ⟨η, hη, hηid, _, hηrange⟩ := exists_lRegularizedDomain_smoothClamp S poleClock x Z hv hvdom
  let γ := lRegularizedCurve S poleClock x Z
  let β : ℝ → ModelGRet := fun u => γ (η u)
  have hβinf : ContMDiff 𝓘(ℝ, ℝ) ThreeModel ∞ β := by
    have hpair : ContMDiff 𝓘(ℝ, ℝ) (𝓘(ℝ, ThreeSpace).prod 𝓘(ℝ, ℝ)) ∞
        (fun u : ℝ => (show ThreeSpace from Z, η u)) := contMDiff_const.prodMk (contMDiff_iff_contDiff.mpr hη)
    rw [← contMDiffOn_univ]
    exact (lRegularizedCurve_smoothOn S hS poleClock x).comp hpair.contMDiffOn
      (fun u _ => by change η u ∈ lRegularizedDomain S poleClock x Z; exact hηrange u)
  have hβ : ContMDiff 𝓘(ℝ, ℝ) ThreeModel 1 β := hβinf.of_le (by norm_num)
  have heq : EqOn β γ (Icc 0 v) := fun u hu => congrArg γ (hηid hu)
  have hβzero : β 0 = x := (heq ⟨le_rfl, hv.le⟩).trans (lRegularizedCurve_zero S poleClock x Z)
  have hβact : lRegularizedAction S poleClock β 0 v = lRegularizedAction S poleClock γ 0 v :=
    lRegularizedAction_congr S poleClock β γ 0 v
      (fun u hu => heq (by rw [uIoo_of_le hv.le] at hu; exact Ioo_subset_Icc_self hu))
  have hstay := finiteFullPreparedMetric_curve_mem_window_of_curvature_bound_action_lt
    I hδ f hf hdisj hs U g R hRet c hc x₀ order d₀ hOriginal hrec d hmap hside w b heps hρ hρD
    Δ S hS hzero hC hcarrier hregular hRm poleClock β hB hβ htime
    (fun u hu => by rw [heq hu]; exact hscalar u hu)
    (by rw [hβzero]; exact hstart) (hβact.trans_lt hact)
  intro u hu
  simpa only [heq hu] using hstay u hu


end DifferentialGeometry.PDE.RicciFlow.StandardCap
