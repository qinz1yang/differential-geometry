import DifferentialGeometry.Geometry.Neck.Recentering
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.StandardCap.FixedStaticInsertion
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.StandardCap.StaticRequestTransport
import DifferentialGeometry.Topology.ThreeManifold.Surgery.FiniteCap.FiniteCapNeckManifold
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.StandardCap.FullMetricConclusions
import DifferentialGeometry.Topology.ThreeManifold.Surgery.FiniteCap.OrientedFiniteCutCapGeometry

set_option autoImplicit false
noncomputable section
open Set Function TopologicalSpace Manifold DifferentialGeometry
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Topology.Manifold
open DifferentialGeometry.Geometry.Neck DifferentialGeometry.Geometry.Metric DifferentialGeometry.Topology.ThreeManifold.Surgery DifferentialGeometry.Topology.Manifold.Attachment
open scoped Manifold ContDiff Topology
namespace DifferentialGeometry.PDE.RicciFlow.StandardCap
universe u v w z
private abbrev UniformE3 := EuclideanSpace ℝ (Fin 3)
private abbrev UniformIC := (𝓡 2).prod 𝓘(ℝ)
private local instance {B : ℝ} {hB : 0 < B} : ChartedSpace UniformE3 (InsertionQuotient hB) :=
  radialCapAttachmentChartedSpace transitionEnd_pos hB
private local instance {B : ℝ} {hB : 0 < B} : IsManifold (𝓡 3) ∞ (InsertionQuotient hB) :=
  radialCapAttachment_isManifold transitionEnd_pos hB
private local instance {B : ℝ} {hB : 0 < B} : T2Space (InsertionQuotient hB) :=
  radialCapAttachment_t2Space transitionEnd_pos hB
private theorem actualNeck_local
    {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [Fact (Module.finrank ℝ E = 3)] [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
    [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [T2Space M]
    (U : Opens M) {g : SmoothRiemannianMetric I U} {x₀ : U} {δ : ℝ} {k : ℕ}
    (d : normalizedDatum g x₀ δ k) : IsLocalDiffeomorph UniformIC I ∞ (neckAmbientMap U d) := by
  apply DifferentialGeometry.Topology.Manifold.isLocalDiffeomorph_of_injective_mfderiv _
    (contMDiff_neckAmbientMap U d) _ (by simpa using (Fact.out : Module.finrank ℝ E = 3).symm)
  intro x
  rw [neckAmbientMap_mfderiv]
  exact d.immersion x

private abbrev UniformS2 := Metric.sphere (0 : UniformE3) 1
private abbrev UniformCap := {x : UniformE3 // ‖x‖ ≤ transitionEnd}
section OriginalMaps
variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
variable [Fact (Module.finrank ℝ E = 3)] [TopologicalSpace H] (I : ModelWithCorners ℝ E H) [I.Boundaryless]
variable [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [T2Space M]
variable {ι : Type*} [Finite ι] {precision : ι → ℝ}
variable (hδ : ∀ i, 0 < precision i) (f : ∀ i : ι, bufferedCylinder (precision i) → M)
variable (hf : ∀ i, _root_.Topology.IsOpenEmbedding (f i))
variable (hdisj : Pairwise (fun i j => Disjoint (range (f i)) (range (f j))))
variable (hs : ∀ i, IsLocalDiffeomorph UniformIC I ∞ (f i))
variable (R : Set (ConnectedComponents (cutCore f))) (c : ℝ) (hc : 4 ≤ c)
local notation "OriginalQ" => FiniteCapQuotient transitionEnd_pos hδ f (fun i => _root_.Topology.IsEmbedding.injective (_root_.Topology.IsOpenEmbedding.toIsEmbedding (hf i))) hdisj
variable (U : Opens M) (g : SmoothRiemannianMetric I U)
variable (b : {b : ι × Bool // cuttingSphereComponent hδ f hf hdisj b ∈ R})
variable {x : U} {k : ℕ} (d : normalizedDatum g x (c * precision b.val.1) k)
variable {A D ε : ℝ} {hA : 0 < A} {m : ℕ} (w : CanonicalStaticInsertionWitness d A hA D m ε)

private theorem placedCap :
    let : LocallyPathConnectedSpace M := originalModel_locallyPathConnected I Fact.out
    let : ChartedSpace UniformE3 OriginalQ := finiteCapChartedSpace I Fact.out transitionEnd_pos hδ f hf hdisj
    ∀ x : UniformCap,
      finiteFullWitnessMap I Fact.out transitionEnd_pos hδ f hf hdisj hs R c hc b (w.data.capMap x) =
        (⟨finiteCapInclusion transitionEnd_pos hδ f (fun i => (hf i).injective) hdisj ⟨b.val, x⟩, b.property⟩ : finiteCapRetained transitionEnd_pos hδ f hf hdisj R) := by
  let : LocallyPathConnectedSpace M := originalModel_locallyPathConnected I Fact.out
  let : ChartedSpace UniformE3 OriginalQ := finiteCapChartedSpace I Fact.out transitionEnd_pos hδ f hf hdisj
  dsimp only
  intro x
  rw [w.properties.capMap_eq, w.properties.capInclusion_eq]
  apply Subtype.ext
  exact congrArg (fun p : finiteCapRestrictedNeighborhood transitionEnd_pos hδ f hf hdisj b.val ((c * precision b.val.1)⁻¹) => p.val) (finiteCapFullInsertionDiffeomorph_symm_cap I Fact.out transitionEnd_pos hδ f hf hdisj hs b.val
    (preparedFullCapWidth_bounds c (precision b.val.1) hc (hδ b.val.1)).2.le
    (preparedFullCapWidth_bounds c (precision b.val.1) hc (hδ b.val.1)).1 x)

private theorem placedCollar :
    let : LocallyPathConnectedSpace M := originalModel_locallyPathConnected I Fact.out
    let : ChartedSpace UniformE3 OriginalQ := finiteCapChartedSpace I Fact.out transitionEnd_pos hδ f hf hdisj
    ∀ q : UniformS2 × Ico (0 : ℝ) (c * precision b.val.1)⁻¹,
      finiteFullWitnessMap I Fact.out transitionEnd_pos hδ f hf hdisj hs R c hc b (w.data.retainedInclusion q) =
        finiteRetainedCoreInclusion transitionEnd_pos hδ f hf hdisj R
          (finiteRetainedCollarCoreMap transitionEnd_pos hδ f hf hdisj R b
            (preparedFullCapWidth_bounds c (precision b.val.1) hc (hδ b.val.1)).2.le q) := by
  let : LocallyPathConnectedSpace M := originalModel_locallyPathConnected I Fact.out
  let : ChartedSpace UniformE3 OriginalQ := finiteCapChartedSpace I Fact.out transitionEnd_pos hδ f hf hdisj
  dsimp only
  intro q
  rw [w.properties.retainedInclusion_eq]
  apply Subtype.ext
  exact congrArg (fun p : finiteCapRestrictedNeighborhood transitionEnd_pos hδ f hf hdisj b.val ((c * precision b.val.1)⁻¹) => p.val) (finiteCapFullInsertionDiffeomorph_symm_collar I Fact.out transitionEnd_pos hδ f hf hdisj hs b.val
    (preparedFullCapWidth_bounds c (precision b.val.1) hc (hδ b.val.1)).2.le
    (preparedFullCapWidth_bounds c (precision b.val.1) hc (hδ b.val.1)).1 q)
end OriginalMaps

def FixedStaticInsertionProcedure (C : ℕ → ℝ) (A : ℝ) (hA : 0 < A)
    (δBase : ℝ) (δRequest : StaticRequest → ℝ) : Prop :=
      ∀ (δ : ℝ), 0 < δ → δ ≤ δBase → ∀ (k : ℕ) (hk : 8 ≤ k),
        ∀ {E : Type u} {H : Type v} {M : Type w} [NormedAddCommGroup E] [NormedSpace ℝ E]
        [FiniteDimensional ℝ E] [Fact (Module.finrank ℝ E = 3)]
        [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
        [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [T2Space M],
        ∀ (g : SmoothRiemannianMetric I M) (x₀ : M) (d : normalizedDatum g x₀ δ k),
        ∃ w : CanonicalStaticInsertionWitness (d.lowerOrder hk) A hA 1 4 1,
          FixedStaticInsertionProperties C w ∧
          ∀ P : StaticRequest, δ ≤ δRequest P → max 8 P.order ≤ k →
            P.IsSatisfied w.data.outMetric (metricScalarAt g x₀) d.scalar_pos
              (insertionBall δ⁻¹) (wideModelMap (inv_pos.mpr d.precision_pos))
              (wideModelMap_isLocalDiffeomorph (inv_pos.mpr d.precision_pos))
              (wideModelMap_isSmoothEmbedding (inv_pos.mpr d.precision_pos)).isEmbedding.injective
              w.data.tip

theorem exists_fixed_finite_insertion :
    ∃ (c : ℝ) (hc : 4 ≤ c), ∃ C : ℕ → ℝ, (∀ j, 0 < C j) ∧
      ∃ (A : ℝ) (hA : 0 < A), 2 * A < 1 / 2 ∧
      ∃ δLocal : ℝ, 0 < δLocal ∧ δLocal < 1 / 2 ∧
      ∃ δLocalRequest : StaticRequest → ℝ,
        (∀ P, 0 < δLocalRequest P ∧ δLocalRequest P ≤ δLocal) ∧
        FixedStaticInsertionProcedure.{u, v, w} C A hA δLocal δLocalRequest ∧
      ∃ δBase : ℝ, 0 < δBase ∧ δBase < 1 / 4 ∧
      ∃ δRequest : StaticRequest → ℝ, (∀ P, 0 < δRequest P ∧ δRequest P ≤ δBase) ∧
      ∀ {E : Type u} {H : Type v} {M : Type w}
        [NormedAddCommGroup E] [NormedSpace ℝ E]
        [FiniteDimensional ℝ E] [Fact (Module.finrank ℝ E = 3)]
        [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
        [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [T2Space M] [CompactSpace M] [Nonempty M],
      ∀ (o : SmoothOrientation I M) (U : Opens M) (g : SmoothRiemannianMetric I U)
        {ι : Type z} [Finite ι] (precision : ι → ℝ) (hδ : ∀ i, 0 < precision i),
        (∀ i, precision i ≤ δBase) → ∀ (x₀ : ι → U)
        (k : ℕ) (hk : 8 ≤ k) (d₀ : ∀ i, normalizedDatum g (x₀ i) (precision i) k),
      let f := fun i => neckAmbientMap U (d₀ i)
      let hf := fun i => isOpenEmbedding_neckAmbientMap U (d₀ i)
      let hs := fun i => actualNeck_local U (d₀ i)
      ∀ (hdisj : Pairwise (fun i j => Disjoint (range (f i)) (range (f j))))
        (R : Set (ConnectedComponents (cutCore f)))
        (hRet : MapsTo (Subtype.val : cutCore f → M) (retainedCore f R) U),
      (Nonempty ι ∨ Nonempty (retainedCore f Rᶜ)) →
      let B := {b : ι × Bool // cuttingSphereComponent hδ f hf hdisj b ∈ R}
      let Q := FiniteCapQuotient transitionEnd_pos hδ f (fun i => (hf i).injective) hdisj
      let : LocallyPathConnectedSpace M := originalModel_locallyPathConnected I Fact.out
      let : ChartedSpace UniformE3 Q := finiteCapChartedSpace I Fact.out transitionEnd_pos hδ f hf hdisj
      let : IsManifold (𝓡 3) ∞ Q := finiteCapQuotient_isManifold Fact.out transitionEnd_pos hδ f hf hdisj hs
      let : T2Space Q := finiteCapQuotient_t2Space transitionEnd_pos hδ f hf hdisj
      ∃ hrec : ∀ b : B, (c * precision b.val.1)⁻¹ + 1 ≤ (precision b.val.1)⁻¹,
        ∃ d : ∀ b : B, normalizedDatum g ((d₀ b.val.1).offsetPoint (cuttingSign_sq b.val.2))
          (c * precision b.val.1) k,
        ∃ hmap : ∀ b : B, (d b).map = (d₀ b.val.1).recenteringMap (cuttingSign_sq b.val.2) (hrec b),
        ∃ hside : ∀ b : B, (d b).retainedSide = true,
        ∃ w : ∀ b : B, CanonicalStaticInsertionWitness ((d b).lowerOrder hk) A hA 1 4 1,
          (∀ b : B, |metricScalarAt g ((d₀ b.val.1).offsetPoint (cuttingSign_sq b.val.2)) /
            metricScalarAt g (x₀ b.val.1) - 1| ≤ c * precision b.val.1) ∧
          (∀ b : B, FixedStaticInsertionProperties C (w b)) ∧
        ∃ gRet : SmoothRiemannianMetric (𝓡 3) (finiteCapRetained transitionEnd_pos hδ f hf hdisj R),
          (gRet = finiteFullPreparedMetric I hδ f hf hdisj hs U g R hRet c hc
            x₀ (fun _ => k) d₀ (fun _ => rfl) hrec (fun b => (d b).lowerOrder hk) hmap hside w ∧
          (∀ (b : B) (q : InsertionQuotient (inv_pos.mpr (d b).precision_pos))
            (v t : TangentSpace (𝓡 3) q),
            gRet.inner (finiteFullWitnessMap I Fact.out transitionEnd_pos hδ f hf hdisj hs R c hc b q)
              (mfderiv (𝓡 3) (𝓡 3) (finiteFullWitnessMap I Fact.out transitionEnd_pos hδ f hf hdisj hs R c hc b) q v)
              (mfderiv (𝓡 3) (𝓡 3) (finiteFullWitnessMap I Fact.out transitionEnd_pos hδ f hf hdisj hs R c hc b) q t) =
                (w b).data.outMetric.inner q v t) ∧
          (∀ (p : coreInteriorDomain f)
            (hp : (⟨p.val, interior_subset p.property⟩ : cutCore f) ∈ retainedCore f R)
            (v t : TangentSpace I p),
            gRet.inner (Opens.inclusion inf_le_left (finiteRetainedInteriorImage transitionEnd_pos hδ f hf hdisj R p hp))
              (mfderiv I (𝓡 3) (finiteCoreInteriorMap transitionEnd_pos hδ f (fun i => (hf i).injective) hdisj) p v)
              (mfderiv I (𝓡 3) (finiteCoreInteriorMap transitionEnd_pos hδ f (fun i => (hf i).injective) hdisj) p t) =
                g.inner ⟨p.val, hRet hp⟩ v t) ∧
          (∀ b : B, Injective (finiteFullWitnessMap I Fact.out transitionEnd_pos hδ f hf hdisj hs R c hc b) ∧
            IsLocalDiffeomorph (𝓡 3) (𝓡 3) ∞ (finiteFullWitnessMap I Fact.out transitionEnd_pos hδ f hf hdisj hs R c hc b)) ∧
          Pairwise (fun b d : B => Disjoint
            (range (finiteFullWitnessMap I Fact.out transitionEnd_pos hδ f hf hdisj hs R c hc b))
            (range (finiteFullWitnessMap I Fact.out transitionEnd_pos hδ f hf hdisj hs R c hc d)))) ∧
          OrientedFiniteCutCapGeometry I Fact.out transitionEnd_pos hδ f hf hdisj hs
            (fun i => (d₀ i).precision_lt_one) R o ∧
          FullMetricConclusions I hδ f hf hdisj hs U g R hRet c hc
            x₀ (fun _ => k) d₀ (fun b => (d b).lowerOrder hk) w C gRet ∧
          (∀ (b : B) (x : UniformCap),
            finiteFullWitnessMap I Fact.out transitionEnd_pos hδ f hf hdisj hs R c hc b ((w b).data.capMap x) =
              (⟨finiteCapInclusion transitionEnd_pos hδ f (fun i => (hf i).injective) hdisj ⟨b.val, x⟩, b.property⟩ : finiteCapRetained transitionEnd_pos hδ f hf hdisj R)) ∧
          (∀ (b : B) (q : UniformS2 × Ico (0 : ℝ) (c * precision b.val.1)⁻¹),
            finiteFullWitnessMap I Fact.out transitionEnd_pos hδ f hf hdisj hs R c hc b ((w b).data.retainedInclusion q) =
              finiteRetainedCoreInclusion transitionEnd_pos hδ f hf hdisj R
                (finiteRetainedCollarCoreMap transitionEnd_pos hδ f hf hdisj R b
                  (preparedFullCapWidth_bounds c (precision b.val.1) hc (hδ b.val.1)).2.le q)) ∧
          ∀ b : B,
          let F := finiteFullWitnessMap I Fact.out transitionEnd_pos hδ f hf hdisj hs R c hc b
          let J := wideModelMap (inv_pos.mpr (d b).precision_pos)
          let hF := isLocalDiffeomorph_finiteFullWitnessMap I Fact.out transitionEnd_pos hδ f hf hdisj hs R c hc b
          let hJ := wideModelMap_isLocalDiffeomorph (inv_pos.mpr (d b).precision_pos)
          ∀ P : StaticRequest, precision b.val.1 ≤ δRequest P → max 8 P.order ≤ k →
            P.IsSatisfied gRet (metricScalarAt g ((d₀ b.val.1).offsetPoint (cuttingSign_sq b.val.2)))
              (d b).scalar_pos (insertionBall (c * precision b.val.1)⁻¹) (F ∘ J)
              (fun q => (hJ q).comp (𝓡 3) (finiteCapRetained transitionEnd_pos hδ f hf hdisj R) (hF (J q)))
              ((injective_finiteFullWitnessMap I Fact.out transitionEnd_pos hδ f hf hdisj hs R c hc b).comp
                (wideModelMap_isSmoothEmbedding (inv_pos.mpr (d b).precision_pos)).isEmbedding.injective)
              (F ((w b).data.tip)) := by
  obtain ⟨c, δrec, hc, hδrec, hrecenter⟩ := exists_fixed_offset_recentering.{u, v, w}
  obtain ⟨C, hC, A, hA, hsmall, δLocal, hLocal, hLocalHalf, δLocalRequest, hLocalRequest, hfactory⟩ :=
    exists_fixed_static_insertion.{u, v, w}
  have hcpos : 0 < c := lt_of_lt_of_le (by norm_num) hc
  let δBase := min δrec (min (δLocal / c) (1 / 8))
  have hBase : 0 < δBase := lt_min hδrec (lt_min (div_pos hLocal hcpos) (by norm_num))
  let δRequest := fun P => min δBase (δLocalRequest P / c)
  refine ⟨c, hc, C, hC, A, hA, hsmall, δLocal, hLocal, hLocalHalf,
    δLocalRequest, hLocalRequest, hfactory, δBase, hBase,
    ((min_le_right _ _).trans (min_le_right _ _)).trans_lt (by norm_num),
    δRequest, fun P => ⟨lt_min hBase (div_pos (hLocalRequest P).1 hcpos), min_le_left _ _⟩, ?_⟩
  intro E H M _ _ _ _ _ I _ _ _ _ _ _ _ o U g ι _ precision hδ hle x₀ k hk d₀
  dsimp only
  intro hdisj R hRet hnontrivial
  let f := fun i => neckAmbientMap U (d₀ i)
  let hf := fun i => isOpenEmbedding_neckAmbientMap U (d₀ i)
  let hs := fun i => actualNeck_local U (d₀ i)
  let B := {b : ι × Bool // cuttingSphereComponent hδ f hf hdisj b ∈ R}
  let Q := FiniteCapQuotient transitionEnd_pos hδ f (fun i => (hf i).injective) hdisj
  let : LocallyPathConnectedSpace M := originalModel_locallyPathConnected I Fact.out
  let : ChartedSpace UniformE3 Q := finiteCapChartedSpace I Fact.out transitionEnd_pos hδ f hf hdisj
  let : IsManifold (𝓡 3) ∞ Q := finiteCapQuotient_isManifold Fact.out transitionEnd_pos hδ f hf hdisj hs
  let : T2Space Q := finiteCapQuotient_t2Space transitionEnd_pos hδ f hf hdisj
  have hp (b : B) := hrecenter E H I U g (x₀ b.val.1) (precision b.val.1) k (d₀ b.val.1)
    (by omega) ((hle b.val.1).trans (min_le_left _ _)) (cuttingSign b.val.2) (cuttingSign_sq b.val.2)
  choose hrec d hmap hside hratio using hp
  have hlocalSmall (b : B) : c * precision b.val.1 ≤ δLocal := by
    have h : precision b.val.1 ≤ δLocal / c :=
      (hle b.val.1).trans ((min_le_right _ _).trans (min_le_left _ _))
    exact (mul_comm c (precision b.val.1)) ▸ (le_div_iff₀ hcpos).mp h
  have hi (b : B) := hfactory (c * precision b.val.1) (mul_pos hcpos (hδ b.val.1))
    (hlocalSmall b) k hk g ((d₀ b.val.1).offsetPoint (cuttingSign_sq b.val.2)) (d b)
  choose w hw hrequests using hi
  let dl := fun b : B => (d b).lowerOrder hk
  let gRet := finiteFullPreparedMetric I hδ f hf hdisj hs U g R hRet c hc
    x₀ (fun _ => k) d₀ (fun _ => rfl) hrec dl hmap hside w
  have hInner := finiteFullPreparedMetric_witness_inner I hδ f hf hdisj hs U g R hRet c hc
    x₀ (fun _ => k) d₀ (fun _ => rfl) hrec dl hmap hside w
  refine ⟨hrec, d, hmap, hside, w, hratio, hw, gRet,
    ⟨rfl, hInner, ?_, ?_, ?_⟩, ?_, ?_, ?_, ?_, ?_⟩
  · exact finiteFullPreparedMetric_original_inner I hδ f hf hdisj hs U g R hRet c hc
      x₀ (fun _ => k) d₀ (fun _ => rfl) hrec dl hmap hside w
  · intro b
    exact ⟨injective_finiteFullWitnessMap I Fact.out transitionEnd_pos hδ f hf hdisj hs R c hc b,
      isLocalDiffeomorph_finiteFullWitnessMap I Fact.out transitionEnd_pos hδ f hf hdisj hs R c hc b⟩
  · exact pairwise_disjoint_finiteFullWitnessMaps I Fact.out transitionEnd_pos hδ f hf hdisj hs R c hc
  · exact orientedFiniteCutCapGeometry I Fact.out transitionEnd_pos hδ f hf hdisj hs
      (fun i => (d₀ i).precision_lt_one) R o hnontrivial
  · exact fullMetricConclusions I hδ f hf hdisj hs U g R hRet c hc
      x₀ (fun _ => k) d₀ (fun _ => rfl) hrec dl hmap hside w (fun b => (hw b).additional)
  · exact fun b => placedCap I hδ f hf hdisj hs R c hc U g b (dl b) (w b)
  · exact fun b => placedCollar I hδ f hf hdisj hs R c hc U g b (dl b) (w b)
  · intro b P hleP hPk
    have hlocalP : c * precision b.val.1 ≤ δLocalRequest P := by
      have h : precision b.val.1 ≤ δLocalRequest P / c := hleP.trans (min_le_right _ _)
      exact (mul_comm c (precision b.val.1)) ▸ (le_div_iff₀ hcpos).mp h
    have h := hrequests b P hlocalP hPk
    exact h.comp_of_isometry (w b).data.outMetric gRet
      (finiteFullWitnessMap I Fact.out transitionEnd_pos hδ f hf hdisj hs R c hc b)
      (isLocalDiffeomorph_finiteFullWitnessMap I Fact.out transitionEnd_pos hδ f hf hdisj hs R c hc b)
      (injective_finiteFullWitnessMap I Fact.out transitionEnd_pos hδ f hf hdisj hs R c hc b)
      (hInner b) (metricScalarAt g ((d₀ b.val.1).offsetPoint (cuttingSign_sq b.val.2)))
      (d b).scalar_pos (insertionBall (c * precision b.val.1)⁻¹)
      (wideModelMap (inv_pos.mpr (d b).precision_pos))
      (wideModelMap_isLocalDiffeomorph (inv_pos.mpr (d b).precision_pos))
      (wideModelMap_isSmoothEmbedding (inv_pos.mpr (d b).precision_pos)).isEmbedding.injective
      (w b).data.tip
end DifferentialGeometry.PDE.RicciFlow.StandardCap
