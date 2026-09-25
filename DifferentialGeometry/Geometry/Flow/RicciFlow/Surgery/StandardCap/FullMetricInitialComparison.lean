import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.StandardCap.FullMetricWindowCurvature
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.StandardCap.InitialFlowComparison
set_option autoImplicit false
noncomputable section
open Set Function TopologicalSpace Manifold DifferentialGeometry
open DifferentialGeometry.Geometry.Neck DifferentialGeometry.Geometry.Metric
  DifferentialGeometry.Topology.ThreeManifold.Surgery
  DifferentialGeometry.Topology.Manifold.Attachment
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
  let : SecondCountableTopology (InsertionQuotient hB) :=
    radialCapAttachment_secondCountableTopology transitionEnd_pos hB
  let : LocallyCompactSpace (InsertionQuotient hB) := ChartedSpace.locallyCompactSpace ModelGE3
    (InsertionQuotient hB)
  infer_instance
private theorem initial_standard_cap_comparison_parameters
    (N : ℕ) (r D σ C ε : ℝ) (hr : 0 < r) (hfit : 2 * r ≤ D)
    (hσ : 0 < σ) (hε : 0 < ε) :
    ∃ η ε₀ : ℝ, 0 < η ∧ η ≤ σ ∧ η < 1 ∧
      (∀ S : StandardSolution, ENNReal.ofReal η < S.val.lifetime) ∧
      0 < ε₀ ∧ ε₀ ≤ 1 / 2 ∧
      ∀ {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
        [FiniteDimensional ℝ E] [Fact (Module.finrank ℝ E = 3)]
        [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
        [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [T2Space M]
        {g : SmoothRiemannianMetric I M} {x₀ : M} {δ : ℝ} {k : ℕ}
        {d : normalizedDatum g x₀ δ k} {A : ℝ} {hA : 0 < A} {m : ℕ} {ζ : ℝ}
        (w : CanonicalStaticInsertionWitness d A hA D m ζ),
      N ≤ m → ζ ≤ ε₀ →
      ∀ (J : RealTimeInterval), Icc 0 σ ⊆ J.carrier → Ioo 0 σ ⊆ J.regular →
        ∀ L : SolutionOn (I := ThreeModel) (M := standardCapWindow D) J,
        IsSolutionOn L → L.base.metric 0 = w.windowMetric →
        (∀ (p : standardCapWindow D) (i j : Fin (Module.finrank ℝ ThreeSpace)),
          ContMDiffOn (𝓘(ℝ, ℝ).prod ThreeModel) 𝓘(ℝ, ℝ) ∞
            (fun q : ℝ × standardCapWindow D =>
              DifferentialGeometry.Tensor.Coordinates.chartGramMatrix (L.base.metric q.1) p q.2 i
                j)
            (Icc 0 σ ×ˢ (trivializationAt ThreeSpace (TangentSpace ThreeModel) p).baseSet)) →
        (∀ j ≤ N, ∀ t ∈ Icc 0 σ, ∀ x : standardCapWindow D, ‖x.val‖ ≤ 2 * r →
          nablaKRm04NormSqIntrinsic L j t x ≤ C) →
        ∀ S : StandardSolution, ∀ t ∈ Icc 0 η,
          metricDerivNormSupOn {x : standardCapWindow D | ‖x.val‖ ≤ r} N
            (L.base.metric t) ((S.val.metric t).restrictOpen (standardCapWindow D))
            (standardCapMetric.restrictOpen (standardCapWindow D)) < ε := by
  obtain ⟨η₀, ε₀, hη₀, hη₀σ, hε₀, hε₀half, hcompare⟩ :=
    exists_uniform_initial_standard_cap_comparison D r (2 * r) σ ε
      (by linarith) hfit hσ hε N (fun _ => Real.sqrt C)
  obtain ⟨α, hα, _, _, hlife, _⟩ := standard_uniform_initial_window
  let η := min η₀ (min (1 / 2) α)
  have hη : 0 < η := lt_min hη₀ (lt_min (by norm_num) hα)
  have hη₀le : η ≤ η₀ := min_le_left _ _
  have hησ : η ≤ σ := hη₀le.trans hη₀σ
  have hη1 : η < 1 := ((min_le_right _ _).trans (min_le_left _ _)).trans_lt (by norm_num)
  have hηlife (S : StandardSolution) : ENNReal.ofReal η < S.val.lifetime :=
    (ENNReal.ofReal_le_ofReal ((min_le_right _ _).trans (min_le_right _ _))).trans_lt (hlife S)
  refine ⟨η, ε₀, hη, hησ, hη1, hηlife, hε₀, hε₀half, ?_⟩
  intro E H M _ _ _ _ _ I _ _ _ _ _ g x₀ δ k d A hA m ζ w hNm hζ
    J hcarrier hregular L hL hzero hgram hcurv S t ht
  apply hcompare w hNm hζ J σ hσ.le le_rfl hcarrier hregular L hL hzero hgram
    (fun j hj s hs x hx => ?_) S t (by rw [min_eq_left hη₀σ];exact ⟨ht.1,ht.2.trans hη₀le⟩)
  unfold curvDerivNorm
  rw [curvNormSq_eq]
  exact Real.sqrt_le_sqrt (hcurv j hj s hs x hx.le)

theorem exists_uniform_finiteFullPreparedMetric_initial_standard_cap_comparison
    (N : ℕ) (r D P B εtarget : ℝ) (hr : 0 < r) (hD : 64 * r < D)
    (hP : 0 < P) (hεtarget : 0 < εtarget) :
    ∃ τ ε₀ : ℝ, 0 < τ ∧ τ < 1 ∧
      (∀ S : StandardSolution, ENNReal.ofReal τ < S.val.lifetime) ∧
      0 < ε₀ ∧ ε₀ ≤ 1 / 2 ∧
      ∀ {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
      [Fact (Module.finrank ℝ E = 3)] [TopologicalSpace H] (I : ModelWithCorners ℝ E H)
        [I.Boundaryless]
      [TopologicalSpace M] [ChartedSpace H M] [T2Space M] [IsManifold I ∞ M]
      {ι : Type*} [Finite ι] {precision : ι → ℝ}
      (hδ : ∀ i, 0 < precision i) (f : ∀ i : ι, bufferedCylinder (precision i) → M)
      (hf : ∀ i, _root_.Topology.IsOpenEmbedding (f i))
      (hdisj : Pairwise (fun i j => Disjoint (range (f i)) (range (f j))))
      (hs : ∀ i, IsLocalDiffeomorph ModelGIC I ∞ (f i))
      (U : Opens M) (g : SmoothRiemannianMetric I U)
      (R : Set (ConnectedComponents (cutCore f)))
      (hRet : MapsTo (Subtype.val : cutCore f → M) (retainedCore f R) U)
      (c : ℝ) (hc : 4 ≤ c)
      (x₀ : ι → U) (order : ι → ℕ)
      (d₀ : ∀ i, normalizedDatum g (x₀ i) (precision i) (order i))
      (hOriginal : ∀ i, f i = neckAmbientMap U (d₀ i))
      {k' : {b : ι × Bool // cuttingSphereComponent hδ f hf hdisj b ∈ R} → ℕ}
      (hrec : ∀ b : {b : ι × Bool // cuttingSphereComponent hδ f hf hdisj b ∈ R}, (c * precision
        b.val.1)⁻¹ + 1 ≤ (precision b.val.1)⁻¹)
      (d : ∀ b : {b : ι × Bool // cuttingSphereComponent hδ f hf hdisj b ∈ R}, normalizedDatum g
      ((d₀ b.val.1).offsetPoint (cuttingSign_sq b.val.2)) (c * precision b.val.1) (k' b))
      (hmap : ∀ b : {b : ι × Bool // cuttingSphereComponent hδ f hf hdisj b ∈ R}, (d b).map = (d₀
        b.val.1).recenteringMap (cuttingSign_sq b.val.2) (hrec b))
      (hside : ∀ b : {b : ι × Bool // cuttingSphereComponent hδ f hf hdisj b ∈ R}, (d
        b).retainedSide = true)
      {A ε : ℝ} {hA : 0 < A} {m : ℕ}
      (w : ∀ b : {b : ι × Bool // cuttingSphereComponent hδ f hf hdisj b ∈ R},
        CanonicalStaticInsertionWitness (d b) A hA D m ε)
      [SigmaCompactSpace M] (b : {b : ι × Bool // cuttingSphereComponent hδ f hf hdisj b ∈ R}), ε
        ≤ ε₀ → N + 2 ≤ m →
    let : LocallyPathConnectedSpace M := originalModel_locallyPathConnected I Fact.out
    let : ChartedSpace ModelGE3 (FiniteCapQuotient transitionEnd_pos hδ f (fun i => (hf
      i).injective) hdisj) := finiteCapChartedSpace I Fact.out transitionEnd_pos hδ f hf hdisj
    let : IsManifold (𝓡 3) ∞ (FiniteCapQuotient transitionEnd_pos hδ f (fun i => (hf i).injective)
      hdisj) := finiteCapQuotient_isManifold Fact.out transitionEnd_pos hδ f hf hdisj hs
    let : T2Space (FiniteCapQuotient transitionEnd_pos hδ f (fun i => (hf i).injective) hdisj) :=
      finiteCapQuotient_t2Space transitionEnd_pos hδ f hf hdisj
    let : SigmaCompactSpace (FiniteCapQuotient transitionEnd_pos hδ f (fun i => (hf i).injective)
      hdisj) := finiteCapQuotient_sigmaCompactSpace transitionEnd_pos hδ f hf hdisj
    let : SigmaCompactSpace (finiteCapRetained transitionEnd_pos hδ f hf hdisj R) :=
      isSigmaCompact_iff_sigmaCompactSpace.mp
      (DifferentialGeometry.Geometry.isSigmaCompact_of_isOpen (𝓡 3) ((finiteCapRetained
        transitionEnd_pos hδ f hf hdisj R)).isOpen)
    let gRet := finiteFullPreparedMetric I hδ f hf hdisj hs U g R hRet c hc x₀ order d₀ hOriginal
      hrec d hmap hside w
    let F := finiteFullWitnessMap I Fact.out transitionEnd_pos hδ f hf hdisj hs R c hc b
    let Q := metricScalarAt g ((d₀ b.val.1).offsetPoint (cuttingSign_sq b.val.2))
    ∀ [CompactSpace (finiteCapRetained transitionEnd_pos hδ f hf hdisj R)], ∀ a : ℝ, P ≤ a * Q →
      (∀ x, InFixedHamiltonIveyRegion gRet a x) →
      (∀ x, metricScalarAt gRet x ≤ B * Q) →
      ∃ T : ℝ, τ < T ∧ ∃ H : FlowTo (scaleMetric Q (d b).scalar_pos gRet) T,
        ∃ L : SolutionOn (I := 𝓡 3) (M := standardCapWindow D)
          (RealTimeInterval.closedOpen 0 T H.time_pos),
          IsSolutionOn L ∧ L.base.metric 0 = (w b).windowMetric ∧
          (∀ t (x : standardCapWindow D) (v z : TangentSpace (𝓡 3) x),
            (L.base.metric t).inner x v z = (H.S.base.metric t).inner ((F ∘ (w b).window) x)
              (mfderiv (𝓡 3) (𝓡 3) (F ∘ (w b).window) x v)
              (mfderiv (𝓡 3) (𝓡 3) (F ∘ (w b).window) x z)) ∧
          (∀ (p : standardCapWindow D) (i j : Fin (Module.finrank ℝ ModelGE3)),
            ContMDiffOn (𝓘(ℝ, ℝ).prod (𝓡 3)) 𝓘(ℝ) ∞
              (fun q : ℝ × standardCapWindow D =>
                DifferentialGeometry.Tensor.Coordinates.chartGramMatrix (L.base.metric q.1) p q.2
                  i j)
              (Icc 0 τ ×ˢ (trivializationAt ModelGE3 (TangentSpace (𝓡 3)) p).baseSet)) ∧
          ∀ S : StandardSolution, ∀ t ∈ Icc 0 τ,
            metricDerivNormSupOn {x : standardCapWindow D | ‖x.val‖ ≤ r} N
              (L.base.metric t) ((S.val.metric t).restrictOpen (standardCapWindow D))
              (standardCapMetric.restrictOpen (standardCapWindow D)) < εtarget := by
  obtain ⟨σ, C, hσ, hC, hproduce⟩ :=
    exists_uniform_finiteFullPreparedMetric_window_flow_curvature_derivative_bound
      N (64 * r) P B (by positivity) hP
  obtain ⟨τ, ε₀, hτ, hτσ, hτ1, hτlife, hε₀, hε₀half, hcompare⟩ :=
    initial_standard_cap_comparison_parameters N r D σ C εtarget hr (by linarith) hσ hεtarget
  refine ⟨τ, ε₀, hτ, hτ1, hτlife, hε₀, hε₀half, ?_⟩
  intro E H M _ _ _ _ _ I _ _ _ _ _ ι _ precision hδ f hf hdisj hs U g R hRet
    c hc x₀ order d₀ hOriginal k' hrec d hmap hside A ε hA m w _ b heps hm
  let : LocallyPathConnectedSpace M := originalModel_locallyPathConnected I Fact.out
  let : ChartedSpace ModelGE3 (FiniteCapQuotient transitionEnd_pos hδ f (fun i => (hf
    i).injective) hdisj) := finiteCapChartedSpace I Fact.out transitionEnd_pos hδ f hf hdisj
  let : IsManifold (𝓡 3) ∞ (FiniteCapQuotient transitionEnd_pos hδ f (fun i => (hf i).injective)
    hdisj) := finiteCapQuotient_isManifold Fact.out transitionEnd_pos hδ f hf hdisj hs
  let : T2Space (FiniteCapQuotient transitionEnd_pos hδ f (fun i => (hf i).injective) hdisj) :=
    finiteCapQuotient_t2Space transitionEnd_pos hδ f hf hdisj
  let : SigmaCompactSpace (FiniteCapQuotient transitionEnd_pos hδ f (fun i => (hf i).injective)
    hdisj) := finiteCapQuotient_sigmaCompactSpace transitionEnd_pos hδ f hf hdisj
  let : SigmaCompactSpace (finiteCapRetained transitionEnd_pos hδ f hf hdisj R) :=
    isSigmaCompact_iff_sigmaCompactSpace.mp
    (DifferentialGeometry.Geometry.isSigmaCompact_of_isOpen (𝓡 3) ((finiteCapRetained
      transitionEnd_pos hδ f hf hdisj R)).isOpen)
  let gRet := finiteFullPreparedMetric I hδ f hf hdisj hs U g R hRet c hc x₀ order d₀ hOriginal
    hrec d hmap hside w
  let F := finiteFullWitnessMap I Fact.out transitionEnd_pos hδ f hf hdisj hs R c hc b
  let Q := metricScalarAt g ((d₀ b.val.1).offsetPoint (cuttingSign_sq b.val.2))
  dsimp only
  intro hcompact a ha hfixed hscalar
  obtain ⟨T, hσT, H, L, hL, hLstart, hmetric, hgram, hamb, hcurv⟩ :=
    hproduce (E := E) (H := H) (M := M) (ι := ι) (precision := precision)
      I hδ f hf hdisj hs U g R hRet c hc x₀ order d₀ hOriginal
      (k' := k') hrec d hmap hside (A := A) (D := D) (ε := ε) (hA := hA) (m := m) w b (heps.trans
        hε₀half) hm hD a ha hfixed hscalar
  refine ⟨T, hτσ.trans_lt hσT, H, L, hL, hLstart, hmetric, ?_, ?_⟩
  · intro p i j
    exact (hgram p i j).mono (prod_mono (Icc_subset_Icc le_rfl hτσ) subset_rfl)
  · intro S t ht
    have hcarrier : Icc 0 σ ⊆ (RealTimeInterval.closedOpen 0 T H.time_pos).carrier :=
      fun s hs => ⟨hs.1, hs.2.trans_lt hσT⟩
    have hregular : Ioo 0 σ ⊆ (RealTimeInterval.closedOpen 0 T H.time_pos).regular :=
      fun s hs => ⟨hs.1, hs.2.trans hσT⟩
    exact hcompare (w b) (by omega) heps _ hcarrier hregular L hL hLstart hgram
      (fun j hj s hs x hx => hcurv j hj s hs x (by nlinarith)) S t ht


end DifferentialGeometry.PDE.RicciFlow.StandardCap
