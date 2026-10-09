import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.StandardCap.FullMetricWindowCapture
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.StandardCap.InitialWindowBounds
import DifferentialGeometry.Geometry.Flow.RicciFlow.Estimates.Shi.CompleteInitialCutoff
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.ControlledRestart
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.StandardCap.FullMetricWindowFlow
import DifferentialGeometry.Geometry.Flow.RicciFlow.Solution.LocalPullbackCurvature
import DifferentialGeometry.Geometry.Curvature.CurvatureOperator.Derivatives.Scaling
import DifferentialGeometry.Geometry.Flow.RicciFlow.Compactness.Bounds.Curvature.TowerBridge

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
private theorem exists_normalized_compact_flow_of_scalar_bound_of_fixedHamiltonIveyRegion
    {X : Type*} [TopologicalSpace X] [ChartedSpace ThreeSpace X]
    [IsManifold ThreeModel ∞ X] [T2Space X] [CompactSpace X]
    [BoundarylessManifold ThreeModel X] (g : SmoothRiemannianMetric ThreeModel X) {P a Q B : ℝ}
    (hP : 0 < P) (hQ : 0 < Q) (ha : P ≤ a * Q)
    (hfixed : ∀ x, InFixedHamiltonIveyRegion g a x)
    (hscalar : ∀ x, metricScalarAt g x ≤ B * Q) :
    let K := 2 * Real.sqrt 3 * (max B 0 / 2 + max B (Real.exp 4 / P))
    let τ := compactCurvatureControlTime 3 K
    ∃ T : ℝ, τ < T ∧ ∃ H : FlowTo (scaleMetric Q hQ g) T,
      ∀ t ∈ Icc 0 τ, ∀ x : X,
        nablaKRm04NormSqIntrinsic H.S 0 t x ≤ 2 * K ^ 2 + 1 := by
  let K := 2 * Real.sqrt 3 * (max B 0 / 2 + max B (Real.exp 4 / P))
  let τ := compactCurvatureControlTime 3 K
  obtain ⟨T, hT, G, hRm⟩ :=
    exists_compact_flow_of_normalized_scalar_bound_of_fixedHamiltonIveyRegion
      g hP hQ ha hfixed hscalar
  let H := G.scale Q hQ
  have htime : τ < Q * T := by
    have hT' : τ / Q < T := hT
    have hh := (div_lt_iff₀ hQ).mp hT'
    rwa [mul_comm T Q] at hh
  refine ⟨Q * T, htime, H, ?_⟩
  intro t ht x
  have hh := hRm (t / Q) ⟨div_nonneg ht.1 hQ.le,
    (div_le_div_iff_of_pos_right hQ).mpr ht.2⟩ x
  have hscale := CheegerGromovCompactness.curvDerivNorm_scaleMetric
    (G.S.base.metric (t / Q)) Q hQ 0 x
  have heq : Real.sqrt (normSq0S (H.S.base.metric t) x 4 (H.S.base.rm04 t x)) =
      Real.sqrt (normSq0S (G.S.base.metric (t / Q)) x 4
        (metricRm04 (G.S.base.metric (t / Q)) x)) / Q := by
    rw [show H.S.base.metric t = scaleMetric Q hQ (G.S.base.metric (t / Q)) from rfl]
    convert! hscale using 1
    simp only [pow_zero, mul_one]
    rfl
  have hn : Real.sqrt (normSq0S (H.S.base.metric t) x 4 (H.S.base.rm04 t x)) ≤
      Real.sqrt (2 * K ^ 2 + 1) := by
    rw [heq]
    exact (div_le_iff₀ hQ).mpr hh
  have hsq := (Real.sqrt_le_iff.mp hn).2
  rw [Real.sq_sqrt (by positivity : 0 ≤ 2 * K ^ 2 + 1)] at hsq
  simpa only [nablaKRm04NormSqIntrinsic, nablaKRm04Field_zero, Nat.add_zero] using hsq


private theorem nablaKRm04NormSqIntrinsic_localPullback
    {X Y : Type*} [TopologicalSpace X] [ChartedSpace ModelGE3 X]
    [IsManifold (𝓡 3) ∞ X] [T2Space X]
    [TopologicalSpace Y] [ChartedSpace ModelGE3 Y]
    [IsManifold (𝓡 3) ∞ Y] [T2Space Y]
    {Δ : RealTimeInterval} (S : SolutionOn (I := 𝓡 3) (M := Y) Δ)
    (p : X → Y) (hp : IsLocalDiffeomorph (𝓡 3) (𝓡 3) ∞ p)
    (j : ℕ) (t : ℝ) (x : X) :
    nablaKRm04NormSqIntrinsic (S.localPullback p hp) j t x =
      nablaKRm04NormSqIntrinsic S j t (p x) := by
  rw [← curvNormSq_eq, ← curvNormSq_eq]
  unfold curvDerivNormSq
  rw [curvCovDeriv_normSq_eq, curvCovDeriv_normSq_eq]
  exact S.localPullback_curvature_derivative_normSq p hp t j x

private theorem nablaKRm04NormSqIntrinsic_eq_of_metric_eq
    {X : Type*} [TopologicalSpace X] [ChartedSpace ModelGE3 X]
    [IsManifold (𝓡 3) ∞ X] [T2Space X]
    {Δ Γ : RealTimeInterval} (S : SolutionOn (I := 𝓡 3) (M := X) Δ)
    (L : SolutionOn (I := 𝓡 3) (M := X) Γ) (j : ℕ) (t : ℝ) (x : X)
    (hmetric : S.base.metric t = L.base.metric t) :
    nablaKRm04NormSqIntrinsic S j t x = nablaKRm04NormSqIntrinsic L j t x := by
  rw [← curvNormSq_eq, ← curvNormSq_eq, hmetric]

private theorem nablaKRm04NormSqIntrinsic_eq_of_pullback_inner
    {X Y : Type*} [TopologicalSpace X] [ChartedSpace ModelGE3 X]
    [IsManifold (𝓡 3) ∞ X] [T2Space X]
    [TopologicalSpace Y] [ChartedSpace ModelGE3 Y]
    [IsManifold (𝓡 3) ∞ Y] [T2Space Y]
    {Δ Γ : RealTimeInterval} (S : SolutionOn (I := 𝓡 3) (M := Y) Δ)
    (L : SolutionOn (I := 𝓡 3) (M := X) Γ)
    (p : X → Y) (hp : IsLocalDiffeomorph (𝓡 3) (𝓡 3) ∞ p)
    (t : ℝ) (j : ℕ) (x : X)
    (hmetric : ∀ y (v z : TangentSpace (𝓡 3) y),
      (L.base.metric t).inner y v z = (S.base.metric t).inner (p y)
        (mfderiv (𝓡 3) (𝓡 3) p y v) (mfderiv (𝓡 3) (𝓡 3) p y z)) :
    nablaKRm04NormSqIntrinsic L j t x = nablaKRm04NormSqIntrinsic S j t (p x) := by
  have heq : L.base.metric t = (S.localPullback p hp).base.metric t := by
    apply SmoothRiemannianMetric.ext_inner
    intro y v z
    exact (hmetric y v z).trans (localPullMetric_inner (S.base.metric t) p hp y v z).symm
  rw [nablaKRm04NormSqIntrinsic_eq_of_metric_eq L (S.localPullback p hp) j t x heq,
    nablaKRm04NormSqIntrinsic_localPullback]

private theorem initial_nablaKRm04NormSqIntrinsic_le_of_metric_bound
    {X : Type*} [TopologicalSpace X] [ChartedSpace ModelGE3 X]
    [IsManifold (𝓡 3) ∞ X] [T2Space X]
    {Δ : RealTimeInterval} (S : SolutionOn (I := 𝓡 3) (M := X) Δ)
    (g₀ : SmoothRiemannianMetric (𝓡 3) X) (hstart : S.base.metric 0 = g₀)
    (j : ℕ) (x : X) (C : ℝ)
    (hbound : normSq0S g₀ x (4 + j) (iterCov g₀ 4 (metricRm04 g₀) j x) ≤ C) :
    nablaKRm04NormSqIntrinsic S j 0 x ≤ C := by
  rw [← curvNormSq_eq, hstart]
  unfold curvDerivNormSq
  rw [curvCovDeriv_normSq_eq]
  exact hbound

private theorem exists_uniform_finiteFullPreparedMetric_flow_curvature_derivative_bound
    (N : ℕ) (ρ P B : ℝ) (hρ : 0 < ρ) (hP : 0 < P) :
    ∃ τ C : ℝ, 0 < τ ∧ 1 ≤ C ∧
      ∀ {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
      [Fact (Module.finrank ℝ E = 3)] [TopologicalSpace H] (I : ModelWithCorners ℝ E H) [I.Boundaryless]
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
      (hrec : ∀ b : {b : ι × Bool // cuttingSphereComponent hδ f hf hdisj b ∈ R}, (c * precision b.val.1)⁻¹ + 1 ≤ (precision b.val.1)⁻¹)
      (d : ∀ b : {b : ι × Bool // cuttingSphereComponent hδ f hf hdisj b ∈ R}, normalizedDatum g
      ((d₀ b.val.1).offsetPoint (cuttingSign_sq b.val.2)) (c * precision b.val.1) (k' b))
      (hmap : ∀ b : {b : ι × Bool // cuttingSphereComponent hδ f hf hdisj b ∈ R}, (d b).map = (d₀ b.val.1).recenteringMap (cuttingSign_sq b.val.2) (hrec b))
      (hside : ∀ b : {b : ι × Bool // cuttingSphereComponent hδ f hf hdisj b ∈ R}, (d b).retainedSide = true)
      {A D ε : ℝ} {hA : 0 < A} {m : ℕ}
      (w : ∀ b : {b : ι × Bool // cuttingSphereComponent hδ f hf hdisj b ∈ R}, CanonicalStaticInsertionWitness (d b) A hA D m ε)
      [SigmaCompactSpace M] (b : {b : ι × Bool // cuttingSphereComponent hδ f hf hdisj b ∈ R}), ε ≤ 1 / 2 → N + 2 ≤ m → ρ < D →
    let : LocallyPathConnectedSpace M := originalModel_locallyPathConnected I Fact.out
    let : ChartedSpace ModelGE3 (FiniteCapQuotient transitionEnd_pos hδ f (fun i => (hf i).injective) hdisj) := finiteCapChartedSpace I Fact.out transitionEnd_pos hδ f hf hdisj
    let : IsManifold (𝓡 3) ∞ (FiniteCapQuotient transitionEnd_pos hδ f (fun i => (hf i).injective) hdisj) := finiteCapQuotient_isManifold Fact.out transitionEnd_pos hδ f hf hdisj hs
    let : T2Space (FiniteCapQuotient transitionEnd_pos hδ f (fun i => (hf i).injective) hdisj) := finiteCapQuotient_t2Space transitionEnd_pos hδ f hf hdisj
    let : SigmaCompactSpace (FiniteCapQuotient transitionEnd_pos hδ f (fun i => (hf i).injective) hdisj) := finiteCapQuotient_sigmaCompactSpace transitionEnd_pos hδ f hf hdisj
    let : SigmaCompactSpace (finiteCapRetained transitionEnd_pos hδ f hf hdisj R) := isSigmaCompact_iff_sigmaCompactSpace.mp
      (DifferentialGeometry.Geometry.isSigmaCompact_of_isOpen (𝓡 3) ((finiteCapRetained transitionEnd_pos hδ f hf hdisj R)).isOpen)
    let gRet := finiteFullPreparedMetric I hδ f hf hdisj hs U g R hRet c hc x₀ order d₀ hOriginal hrec d hmap hside w
    let F := finiteFullWitnessMap I Fact.out transitionEnd_pos hδ f hf hdisj hs R c hc b
    let Q := metricScalarAt g ((d₀ b.val.1).offsetPoint (cuttingSign_sq b.val.2))
    ∀ [CompactSpace (finiteCapRetained transitionEnd_pos hδ f hf hdisj R)], ∀ a : ℝ, P ≤ a * Q →
      (∀ x, InFixedHamiltonIveyRegion gRet a x) →
      (∀ x, metricScalarAt gRet x ≤ B * Q) →
      ∃ T : ℝ, τ < T ∧ ∃ H : FlowTo (scaleMetric Q (d b).scalar_pos gRet) T,
        ∀ k ≤ N, ∀ t ∈ Icc 0 τ, ∀ x : (finiteCapRetained transitionEnd_pos hδ f hf hdisj R),
          riemannianEDistOf (H.S.base.metric 0) (F ((w b).data.tip)) x ≤ ENNReal.ofReal (ρ / 8) →
          nablaKRm04NormSqIntrinsic H.S k t x ≤ C := by
  classical
  let K := 2 * Real.sqrt 3 * (max B 0 / 2 + max B (Real.exp 4 / P))
  let τ := compactCurvatureControlTime 3 K
  have hτ : 0 < τ := compactCurvatureControlTime_pos 3 K
  choose Cj hCj hCjbound using exists_uniform_window_curvature_derivative_bounds
  obtain ⟨C, hC, hbound⟩ := exists_uniform_initial_curvature_derivative_bound_on_ball
    (I := 𝓡 3) N τ (ρ / 4) (2 * K ^ 2 + 1) hτ (by positivity)
    (fun j => Cj j ^ 2) (fun _ _ _ => sq_nonneg _)
  refine ⟨τ, C, hτ, hC, ?_⟩
  intro E H M _ _ _ _ _ I _ _ _ _ _ ι _ precision hδ f hf hdisj hs U g R hRet
    c hc x₀ order d₀ hOriginal k' hrec d hmap hside A D ε hA m w _ b heps hm hρD
  let : LocallyPathConnectedSpace M := originalModel_locallyPathConnected I Fact.out
  let : ChartedSpace ModelGE3 (FiniteCapQuotient transitionEnd_pos hδ f (fun i => (hf i).injective) hdisj) := finiteCapChartedSpace I Fact.out transitionEnd_pos hδ f hf hdisj
  let : IsManifold (𝓡 3) ∞ (FiniteCapQuotient transitionEnd_pos hδ f (fun i => (hf i).injective) hdisj) := finiteCapQuotient_isManifold Fact.out transitionEnd_pos hδ f hf hdisj hs
  let : T2Space (FiniteCapQuotient transitionEnd_pos hδ f (fun i => (hf i).injective) hdisj) := finiteCapQuotient_t2Space transitionEnd_pos hδ f hf hdisj
  let : SigmaCompactSpace (FiniteCapQuotient transitionEnd_pos hδ f (fun i => (hf i).injective) hdisj) := finiteCapQuotient_sigmaCompactSpace transitionEnd_pos hδ f hf hdisj
  let : SigmaCompactSpace (finiteCapRetained transitionEnd_pos hδ f hf hdisj R) := isSigmaCompact_iff_sigmaCompactSpace.mp
    (DifferentialGeometry.Geometry.isSigmaCompact_of_isOpen (𝓡 3) ((finiteCapRetained transitionEnd_pos hδ f hf hdisj R)).isOpen)
  let gRet := finiteFullPreparedMetric I hδ f hf hdisj hs U g R hRet c hc x₀ order d₀ hOriginal hrec d hmap hside w
  let F := finiteFullWitnessMap I Fact.out transitionEnd_pos hδ f hf hdisj hs R c hc b
  let Q := metricScalarAt g ((d₀ b.val.1).offsetPoint (cuttingSign_sq b.val.2))
  have hQ : 0 < Q := (d b).scalar_pos
  dsimp only
  intro _ a ha hfixed hscalar
  obtain ⟨T, htime, H, hcurv⟩ :=
    exists_normalized_compact_flow_of_scalar_bound_of_fixedHamiltonIveyRegion
      gRet hP hQ ha hfixed hscalar
  have hstart : H.S.base.metric 0 = scaleMetric Q hQ gRet := H.start
  have hinit : ∀ j, 1 ≤ j → j ≤ N → ∀ x : (finiteCapRetained transitionEnd_pos hδ f hf hdisj R),
      riemannianEDistOf (H.S.base.metric 0) (F ((w b).data.tip)) x ≤ ENNReal.ofReal (ρ / 4) →
      nablaKRm04NormSqIntrinsic H.S j 0 x ≤ Cj j ^ 2 := by
    intro j _ hj x hx
    have hwin := hCjbound j (w b) heps (by omega)
    have hh := finiteFullPreparedMetric_curvature_derivative_bound_on_normalized_tip_ball
      I hδ f hf hdisj hs U g R hRet c hc x₀ order d₀ hOriginal hrec d hmap hside w
      b heps hρ hρD j (Cj j) hwin x (by
        change riemannianEDistOf (scaleMetric Q hQ gRet) (F ((w b).data.tip)) x ≤ _
        rwa [hstart] at hx)
    have hsqrt := (Real.sqrt_le_iff.mp hh).2
    exact initial_nablaKRm04NormSqIntrinsic_le_of_metric_bound H.S _ hstart j x _ hsqrt
  refine ⟨T, htime, H, ?_⟩
  have hb := hbound (finiteCapRetained transitionEnd_pos hδ f hf hdisj R) _ H.S H.isSolution
    (fun t ht => ⟨ht.1, ht.2.trans_lt htime⟩)
    (fun t ht => ⟨ht.1, ht.2.trans_lt htime⟩)
    (RiemannianMetricComplete.of_compact _) hcurv
    (fun p i j => (H.joint p i j).mono
      (fun q hq => ⟨⟨hq.1.1, hq.1.2.trans_lt htime⟩, hq.2⟩))
    (F ((w b).data.tip)) hinit
  simpa only [show ρ / 4 / 2 = ρ / 8 by ring] using hb


theorem exists_uniform_finiteFullPreparedMetric_window_flow_curvature_derivative_bound
    (N : ℕ) (ρ P B : ℝ) (hρ : 0 < ρ) (hP : 0 < P) :
    ∃ τ C : ℝ, 0 < τ ∧ 1 ≤ C ∧
      ∀ {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
      [Fact (Module.finrank ℝ E = 3)] [TopologicalSpace H] (I : ModelWithCorners ℝ E H) [I.Boundaryless]
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
      (hrec : ∀ b : {b : ι × Bool // cuttingSphereComponent hδ f hf hdisj b ∈ R}, (c * precision b.val.1)⁻¹ + 1 ≤ (precision b.val.1)⁻¹)
      (d : ∀ b : {b : ι × Bool // cuttingSphereComponent hδ f hf hdisj b ∈ R}, normalizedDatum g
      ((d₀ b.val.1).offsetPoint (cuttingSign_sq b.val.2)) (c * precision b.val.1) (k' b))
      (hmap : ∀ b : {b : ι × Bool // cuttingSphereComponent hδ f hf hdisj b ∈ R}, (d b).map = (d₀ b.val.1).recenteringMap (cuttingSign_sq b.val.2) (hrec b))
      (hside : ∀ b : {b : ι × Bool // cuttingSphereComponent hδ f hf hdisj b ∈ R}, (d b).retainedSide = true)
      {A D ε : ℝ} {hA : 0 < A} {m : ℕ}
      (w : ∀ b : {b : ι × Bool // cuttingSphereComponent hδ f hf hdisj b ∈ R}, CanonicalStaticInsertionWitness (d b) A hA D m ε)
      [SigmaCompactSpace M] (b : {b : ι × Bool // cuttingSphereComponent hδ f hf hdisj b ∈ R}), ε ≤ 1 / 2 → N + 2 ≤ m → ρ < D →
    let : LocallyPathConnectedSpace M := originalModel_locallyPathConnected I Fact.out
    let : ChartedSpace ModelGE3 (FiniteCapQuotient transitionEnd_pos hδ f (fun i => (hf i).injective) hdisj) := finiteCapChartedSpace I Fact.out transitionEnd_pos hδ f hf hdisj
    let : IsManifold (𝓡 3) ∞ (FiniteCapQuotient transitionEnd_pos hδ f (fun i => (hf i).injective) hdisj) := finiteCapQuotient_isManifold Fact.out transitionEnd_pos hδ f hf hdisj hs
    let : T2Space (FiniteCapQuotient transitionEnd_pos hδ f (fun i => (hf i).injective) hdisj) := finiteCapQuotient_t2Space transitionEnd_pos hδ f hf hdisj
    let : SigmaCompactSpace (FiniteCapQuotient transitionEnd_pos hδ f (fun i => (hf i).injective) hdisj) := finiteCapQuotient_sigmaCompactSpace transitionEnd_pos hδ f hf hdisj
    let : SigmaCompactSpace (finiteCapRetained transitionEnd_pos hδ f hf hdisj R) := isSigmaCompact_iff_sigmaCompactSpace.mp
      (DifferentialGeometry.Geometry.isSigmaCompact_of_isOpen (𝓡 3) ((finiteCapRetained transitionEnd_pos hδ f hf hdisj R)).isOpen)
    let gRet := finiteFullPreparedMetric I hδ f hf hdisj hs U g R hRet c hc x₀ order d₀ hOriginal hrec d hmap hside w
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
                DifferentialGeometry.Tensor.Coordinates.chartGramMatrix (L.base.metric q.1) p q.2 i j)
              (Icc 0 τ ×ˢ (trivializationAt ModelGE3 (TangentSpace (𝓡 3)) p).baseSet)) ∧
          (∀ k ≤ N, ∀ t ∈ Icc 0 τ, ∀ x : (finiteCapRetained transitionEnd_pos hδ f hf hdisj R),
            riemannianEDistOf (H.S.base.metric 0) (F ((w b).data.tip)) x ≤
              ENNReal.ofReal (ρ / 8) → nablaKRm04NormSqIntrinsic H.S k t x ≤ C) ∧
          ∀ k ≤ N, ∀ t ∈ Icc 0 τ, ∀ x : standardCapWindow D, ‖x.val‖ ≤ ρ / 32 →
            nablaKRm04NormSqIntrinsic L k t x ≤ C := by
  obtain ⟨τ, C, hτ, hC, hproduce⟩ :=
    exists_uniform_finiteFullPreparedMetric_flow_curvature_derivative_bound N ρ P B hρ hP
  refine ⟨τ, C, hτ, hC, ?_⟩
  intro E H M _ _ _ _ _ I _ _ _ _ _ ι _ precision hδ f hf hdisj hs U g R hRet
    c hc x₀ order d₀ hOriginal k' hrec d hmap hside A D ε hA m w _ b heps hm hρD
  let : LocallyPathConnectedSpace M := originalModel_locallyPathConnected I Fact.out
  let : ChartedSpace ModelGE3 (FiniteCapQuotient transitionEnd_pos hδ f (fun i => (hf i).injective) hdisj) := finiteCapChartedSpace I Fact.out transitionEnd_pos hδ f hf hdisj
  let : IsManifold (𝓡 3) ∞ (FiniteCapQuotient transitionEnd_pos hδ f (fun i => (hf i).injective) hdisj) := finiteCapQuotient_isManifold Fact.out transitionEnd_pos hδ f hf hdisj hs
  let : T2Space (FiniteCapQuotient transitionEnd_pos hδ f (fun i => (hf i).injective) hdisj) := finiteCapQuotient_t2Space transitionEnd_pos hδ f hf hdisj
  let : SigmaCompactSpace (FiniteCapQuotient transitionEnd_pos hδ f (fun i => (hf i).injective) hdisj) := finiteCapQuotient_sigmaCompactSpace transitionEnd_pos hδ f hf hdisj
  let : SigmaCompactSpace (finiteCapRetained transitionEnd_pos hδ f hf hdisj R) := isSigmaCompact_iff_sigmaCompactSpace.mp
    (DifferentialGeometry.Geometry.isSigmaCompact_of_isOpen (𝓡 3) ((finiteCapRetained transitionEnd_pos hδ f hf hdisj R)).isOpen)
  let gRet := finiteFullPreparedMetric I hδ f hf hdisj hs U g R hRet c hc x₀ order d₀ hOriginal hrec d hmap hside w
  let F := finiteFullWitnessMap I Fact.out transitionEnd_pos hδ f hf hdisj hs R c hc b
  let Q := metricScalarAt g ((d₀ b.val.1).offsetPoint (cuttingSign_sq b.val.2))
  dsimp only
  intro hcompact a ha hfixed hscalar
  obtain ⟨T, htime, H, hamb⟩ := hproduce I hδ f hf hdisj hs U g R hRet
    c hc x₀ order d₀ hOriginal hrec d hmap hside w b heps hm hρD a ha hfixed hscalar
  have hstart : H.S.base.metric 0 = scaleMetric Q (d b).scalar_pos gRet := H.start
  obtain ⟨L, hL, hLstart, hmetric, hgram⟩ :=
    finiteFullPreparedMetric_exists_window_pullback_solution I hδ f hf hdisj hs U g R hRet
      c hc x₀ order d₀ hOriginal hrec d hmap hside w b _ H.S H.isSolution H.start
  refine ⟨T, htime, H, L, hL, hLstart, hmetric, ?_, hamb, ?_⟩
  · exact hgram (Icc 0 τ) (fun p i j => (H.joint p i j).mono
      (fun q hq => ⟨⟨hq.1.1, hq.1.2.trans_lt htime⟩, hq.2⟩))
  · intro k hk t ht x hx
    let Φ := F ∘ (w b).window
    have hF := isLocalDiffeomorph_finiteFullWitnessMap I Fact.out transitionEnd_pos
      hδ f hf hdisj hs R c hc b
    have hΦ : IsLocalDiffeomorph (𝓡 3) (𝓡 3) ∞ Φ :=
      fun q => ((w b).properties.window_local q).comp (𝓡 3) (finiteCapRetained transitionEnd_pos hδ f hf hdisj R) (hF ((w b).window q))
    rw [nablaKRm04NormSqIntrinsic_eq_of_pullback_inner H.S L Φ hΦ t k x
      (hmetric t)]
    apply hamb k hk t ht (Φ x)
    rw [hstart]
    have hρsmall : ρ / 8 < D := (by linarith : ρ / 8 < ρ).trans hρD
    have himage := finiteFullPreparedMetric_window_image_subset_normalized_tip_ball
      I hδ f hf hdisj hs U g R hRet c hc x₀ order d₀ hOriginal hrec d hmap hside w b
      heps (by positivity : 0 < ρ / 8) hρsmall
      (show Φ x ∈ Φ '' {x : standardCapWindow D | ‖x.val‖ ≤ (ρ / 8) / 4} from
        ⟨x, by change ‖x.val‖ ≤ (ρ / 8) / 4; simpa only [show (ρ / 8) / 4 = ρ / 32 by ring] using hx, rfl⟩)
    exact himage.le


end DifferentialGeometry.PDE.RicciFlow.StandardCap
