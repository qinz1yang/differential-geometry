import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.StandardCap.FullMetricModels
import DifferentialGeometry.Topology.ThreeManifold.Surgery.FiniteCap.RetainedCoreMaps

set_option autoImplicit false
noncomputable section
open Set Function TopologicalSpace Manifold DifferentialGeometry
open DifferentialGeometry.Geometry.Neck DifferentialGeometry.Geometry.Metric DifferentialGeometry.Topology.ThreeManifold.Surgery DifferentialGeometry.Topology.Manifold.Attachment
open DifferentialGeometry.Tensor0SBundle DifferentialGeometry.CheegerGromovCompactness
open DifferentialGeometry.Topology.Manifold
open DifferentialGeometry.Geometry.Riemannian
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Geometry.Curvature
open scoped Manifold ContDiff Topology ENNReal
namespace DifferentialGeometry.PDE.RicciFlow.StandardCap
private abbrev BoundaryGE3 := EuclideanSpace ℝ (Fin 3)
private abbrev BoundaryGIC := (𝓡 2).prod 𝓘(ℝ)
private local instance {B : ℝ} {hB : 0 < B} : ChartedSpace BoundaryGE3 (InsertionQuotient hB) :=
  radialCapAttachmentChartedSpace transitionEnd_pos hB
private local instance {B : ℝ} {hB : 0 < B} : IsManifold (𝓡 3) ∞ (InsertionQuotient hB) :=
  radialCapAttachment_isManifold transitionEnd_pos hB
private local instance : NeZero (Module.finrank ℝ BoundaryGE3) := ⟨by simp⟩
private local instance {B : ℝ} {hB : 0 < B} : T2Space (InsertionQuotient hB) :=
  radialCapAttachment_t2Space transitionEnd_pos hB
private abbrev BoundaryIR := (𝓡 2).prod (𝓡∂ 1)
private abbrev BoundaryS2 := Metric.sphere (0 : BoundaryGE3) 1
section Correspondence
variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [Fact (Module.finrank ℝ E = 3)] [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [T2Space M]
  {g : SmoothRiemannianMetric I M} {x₀ : M} {δ δ' : ℝ} {k k' : ℕ}

theorem preparedDatum_closed_collar (d : normalizedDatum g x₀ δ k) (b : Bool)
    (hrec : δ'⁻¹ + 1 ≤ δ⁻¹)
    (d' : normalizedDatum g (d.offsetPoint (cuttingSign_sq b)) δ' k')
    (hmap : d'.map = d.recenteringMap (cuttingSign_sq b) hrec) (hside : d'.retainedSide = true)
    (hfit : δ'⁻¹ ≤ cuttingCollarWidth δ) (q : BoundaryS2 × Ico (0 : ℝ) δ'⁻¹) :
    d'.oriented.positiveRetainedMap q = d.map (cuttingCollarCylinderMap d.precision_pos b
      (q.1, ⟨q.2.val, q.2.property.1, q.2.property.2.trans_le hfit⟩)) := by
  rw [normalizedDatum.positiveRetainedMap_apply, normalizedDatum.oriented_map_of_retainedSide_true d' hside,
    hmap, normalizedDatum.recenteringMap_apply]
  apply congrArg d.map
  apply Subtype.ext
  rw [cuttingCollarCylinderMap_val]
  change (q.1, cuttingSign b * (1 + q.2.val)) = (q.1, cuttingSign b + cuttingSign b * q.2.val)
  exact Prod.ext rfl (by ring)
end Correspondence
variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
variable [Fact (Module.finrank ℝ E = 3)] [TopologicalSpace H] (I : ModelWithCorners ℝ E H) [I.Boundaryless]
variable [TopologicalSpace M] [ChartedSpace H M] [T2Space M] [IsManifold I ∞ M]
variable {ι : Type*} [Finite ι] {precision : ι → ℝ}
variable (hδ : ∀ i, 0 < precision i) (f : ∀ i : ι, bufferedCylinder (precision i) → M)
variable (hf : ∀ i, _root_.Topology.IsOpenEmbedding (f i))
variable (hdisj : Pairwise (fun i j => Disjoint (range (f i)) (range (f j))))
variable (hs : ∀ i, IsLocalDiffeomorph BoundaryGIC I ∞ (f i))
local notation "BoundaryGQ" => FiniteCapQuotient transitionEnd_pos hδ f (fun i => _root_.Topology.IsEmbedding.injective (_root_.Topology.IsOpenEmbedding.toIsEmbedding (hf i))) hdisj
variable (U : Opens M) (g : SmoothRiemannianMetric I U)
variable (R : Set (ConnectedComponents (cutCore f)))
variable (hRet : MapsTo (Subtype.val : cutCore f → M) (retainedCore f R) U)
variable (c : ℝ) (hc : 4 ≤ c)
local notation "BoundaryGRet" => finiteCapRetained transitionEnd_pos hδ f hf hdisj R
local notation "BoundaryGOld" => finiteRetainedInteriorOpens transitionEnd_pos hδ f hf hdisj R
local notation "BoundaryGB" => {b : ι × Bool // cuttingSphereComponent hδ f hf hdisj b ∈ R}
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

theorem finiteFullWitnessMap_closed_collar (b : BoundaryGB) :
    let : LocallyPathConnectedSpace M := originalModel_locallyPathConnected I Fact.out
    let : ChartedSpace BoundaryGE3 BoundaryGQ := finiteCapChartedSpace I Fact.out transitionEnd_pos hδ f hf hdisj
    finiteRetainedCoreInclusion transitionEnd_pos hδ f hf hdisj R ∘ (finiteRetainedCollarCoreMap transitionEnd_pos hδ f hf hdisj R b (preparedFullCapWidth_bounds c (precision b.val.1) hc (hδ b.val.1)).2.le) =
      (finiteFullWitnessMap I Fact.out transitionEnd_pos hδ f hf hdisj hs R c hc b) ∘ (w b).data.retainedInclusion := by
  let : LocallyPathConnectedSpace M := originalModel_locallyPathConnected I Fact.out
  let : ChartedSpace BoundaryGE3 BoundaryGQ := finiteCapChartedSpace I Fact.out transitionEnd_pos hδ f hf hdisj
  dsimp only
  funext q
  apply Subtype.ext
  change finiteCoreInclusion transitionEnd_pos hδ f (fun i => (hf i).injective) hdisj
    (cuttingCollarMap hδ f (fun i => (hf i).injective) hdisj b.val
      (q.1, ⟨q.2.val, q.2.property.1, q.2.property.2.trans_le (preparedFullCapWidth_bounds c (precision b.val.1) hc (hδ b.val.1)).2.le⟩)) =
        ((finiteCapFullInsertionDiffeomorph I Fact.out transitionEnd_pos hδ f hf hdisj hs b.val (preparedFullCapWidth_bounds c (precision b.val.1) hc (hδ b.val.1)).2.le (preparedFullCapWidth_bounds c (precision b.val.1) hc (hδ b.val.1)).1).symm ((w b).data.retainedInclusion q)).val
  rw [(w b).properties.retainedInclusion_eq]
  exact (congrArg Subtype.val
    (finiteCapFullInsertionDiffeomorph_symm_collar I Fact.out transitionEnd_pos hδ f hf hdisj hs b.val (preparedFullCapWidth_bounds c (precision b.val.1) hc (hδ b.val.1)).2.le
      (preparedFullCapWidth_bounds c (precision b.val.1) hc (hδ b.val.1)).1 q)).symm

include hOriginal hmap hside in
theorem retainedCoreDomainMap_closed_collar (b : BoundaryGB) :
    let : LocallyPathConnectedSpace M := originalModel_locallyPathConnected I Fact.out
    let : ChartedSpace BoundaryGE3 BoundaryGQ := finiteCapChartedSpace I Fact.out transitionEnd_pos hδ f hf hdisj
    retainedCoreDomainMap f R U hRet ∘ (finiteRetainedCollarCoreMap transitionEnd_pos hδ f hf hdisj R b (preparedFullCapWidth_bounds c (precision b.val.1) hc (hδ b.val.1)).2.le) = (d b).oriented.positiveRetainedMap := by
  let : LocallyPathConnectedSpace M := originalModel_locallyPathConnected I Fact.out
  let : ChartedSpace BoundaryGE3 BoundaryGQ := finiteCapChartedSpace I Fact.out transitionEnd_pos hδ f hf hdisj
  dsimp only
  funext q
  apply Subtype.ext
  change f b.val.1 (cuttingCollarCylinderMap (hδ b.val.1) b.val.2
    (q.1, ⟨q.2.val, q.2.property.1, q.2.property.2.trans_le (preparedFullCapWidth_bounds c (precision b.val.1) hc (hδ b.val.1)).2.le⟩)) =
      ((d b).oriented.positiveRetainedMap q).val
  rw [hOriginal b.val.1]
  exact congrArg Subtype.val
    (preparedDatum_closed_collar (d₀ b.val.1) b.val.2 (hrec b) (d b) (hmap b) (hside b) (preparedFullCapWidth_bounds c (precision b.val.1) hc (hδ b.val.1)).2.le q).symm

include w hOriginal hmap hside in
theorem finiteRetained_closed_collar_smooth (b : BoundaryGB) :
    let : LocallyPathConnectedSpace M := originalModel_locallyPathConnected I Fact.out
    let : ChartedSpace BoundaryGE3 BoundaryGQ := finiteCapChartedSpace I Fact.out transitionEnd_pos hδ f hf hdisj
    let : IsManifold (𝓡 3) ∞ BoundaryGQ := finiteCapQuotient_isManifold Fact.out transitionEnd_pos hδ f hf hdisj hs
    let : ChartedSpace (EuclideanHalfSpace 1) (Ico (0 : ℝ) (c * precision b.val.1)⁻¹) :=
      halfClosedIntervalChartedSpace (inv_pos.mpr (d b).precision_pos)
    ContMDiff BoundaryIR (𝓡 3) ∞ (finiteRetainedCoreInclusion transitionEnd_pos hδ f hf hdisj R ∘ (finiteRetainedCollarCoreMap transitionEnd_pos hδ f hf hdisj R b (preparedFullCapWidth_bounds c (precision b.val.1) hc (hδ b.val.1)).2.le)) ∧
      ContMDiff BoundaryIR I ∞ (retainedCoreDomainMap f R U hRet ∘ (finiteRetainedCollarCoreMap transitionEnd_pos hδ f hf hdisj R b (preparedFullCapWidth_bounds c (precision b.val.1) hc (hδ b.val.1)).2.le)) := by
  let : LocallyPathConnectedSpace M := originalModel_locallyPathConnected I Fact.out
  let : ChartedSpace BoundaryGE3 BoundaryGQ := finiteCapChartedSpace I Fact.out transitionEnd_pos hδ f hf hdisj
  let : IsManifold (𝓡 3) ∞ BoundaryGQ := finiteCapQuotient_isManifold Fact.out transitionEnd_pos hδ f hf hdisj hs
  let : ChartedSpace (EuclideanHalfSpace 1) (Ico (0 : ℝ) (c * precision b.val.1)⁻¹) :=
    halfClosedIntervalChartedSpace (inv_pos.mpr (d b).precision_pos)
  dsimp only
  rw [finiteFullWitnessMap_closed_collar I hδ f hf hdisj hs U g R c hc x₀ order d₀ d w b, retainedCoreDomainMap_closed_collar I hδ f hf hdisj U g R hRet c hc x₀ order d₀ hOriginal hrec d hmap hside b]
  exact ⟨(contMDiff_finiteFullWitnessMap I Fact.out transitionEnd_pos hδ f hf hdisj hs R c hc b).comp
    (w b).properties.retained_embedding.contMDiff, (d b).oriented.positiveRetainedMap_smooth⟩

theorem finiteFullPreparedMetric_closed_collar (b : BoundaryGB) :
    let : LocallyPathConnectedSpace M := originalModel_locallyPathConnected I Fact.out
    let : ChartedSpace BoundaryGE3 BoundaryGQ := finiteCapChartedSpace I Fact.out transitionEnd_pos hδ f hf hdisj
    let : IsManifold (𝓡 3) ∞ BoundaryGQ := finiteCapQuotient_isManifold Fact.out transitionEnd_pos hδ f hf hdisj hs
    let : ChartedSpace (EuclideanHalfSpace 1) (Ico (0 : ℝ) (c * precision b.val.1)⁻¹) :=
      halfClosedIntervalChartedSpace (inv_pos.mpr (d b).precision_pos)
    let gRet := finiteFullPreparedMetric I hδ f hf hdisj hs U g R hRet c hc x₀ order d₀ hOriginal hrec d hmap hside w
    let Φ := finiteRetainedCoreInclusion transitionEnd_pos hδ f hf hdisj R ∘ (finiteRetainedCollarCoreMap transitionEnd_pos hδ f hf hdisj R b (preparedFullCapWidth_bounds c (precision b.val.1) hc (hδ b.val.1)).2.le)
    let Ψ := retainedCoreDomainMap f R U hRet ∘ (finiteRetainedCollarCoreMap transitionEnd_pos hδ f hf hdisj R b (preparedFullCapWidth_bounds c (precision b.val.1) hc (hδ b.val.1)).2.le)
    ∀ (q : BoundaryS2 × Ico (0 : ℝ) (c * precision b.val.1)⁻¹) (v z : TangentSpace BoundaryIR q),
      gRet.inner (Φ q) (mfderiv BoundaryIR (𝓡 3) Φ q v) (mfderiv BoundaryIR (𝓡 3) Φ q z) =
        g.inner (Ψ q) (mfderiv BoundaryIR I Ψ q v) (mfderiv BoundaryIR I Ψ q z) := by
  let : LocallyPathConnectedSpace M := originalModel_locallyPathConnected I Fact.out
  let : ChartedSpace BoundaryGE3 BoundaryGQ := finiteCapChartedSpace I Fact.out transitionEnd_pos hδ f hf hdisj
  let : IsManifold (𝓡 3) ∞ BoundaryGQ := finiteCapQuotient_isManifold Fact.out transitionEnd_pos hδ f hf hdisj hs
  let : ChartedSpace (EuclideanHalfSpace 1) (Ico (0 : ℝ) (c * precision b.val.1)⁻¹) :=
    halfClosedIntervalChartedSpace (inv_pos.mpr (d b).precision_pos)
  dsimp only
  rw [finiteFullWitnessMap_closed_collar I hδ f hf hdisj hs U g R c hc x₀ order d₀ d w b, retainedCoreDomainMap_closed_collar I hδ f hf hdisj U g R hRet c hc x₀ order d₀ hOriginal hrec d hmap hside b]
  intro q v z
  exact (metric_inner_comp_of_isometry (w b).data.outMetric
    (finiteFullPreparedMetric I hδ f hf hdisj hs U g R hRet c hc x₀ order d₀ hOriginal hrec d hmap hside w)
    (finiteFullWitnessMap I Fact.out transitionEnd_pos hδ f hf hdisj hs R c hc b)
    (contMDiff_finiteFullWitnessMap I Fact.out transitionEnd_pos hδ f hf hdisj hs R c hc b)
    (finiteFullPreparedMetric_witness_inner I hδ f hf hdisj hs U g R hRet c hc x₀ order d₀ hOriginal hrec d hmap hside w b)
    (w b).data.retainedInclusion (w b).properties.retained_embedding.contMDiff q v z).trans
      ((w b).properties.retained_metric q v z)
end DifferentialGeometry.PDE.RicciFlow.StandardCap
