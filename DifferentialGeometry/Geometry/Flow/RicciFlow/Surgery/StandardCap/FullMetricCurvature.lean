import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.StandardCap.FullPreparedGluing
import DifferentialGeometry.Geometry.Curvature.EmbeddingIsometry

set_option autoImplicit false
noncomputable section
open Set Function TopologicalSpace Manifold DifferentialGeometry
open DifferentialGeometry.Geometry.Neck DifferentialGeometry.Geometry.Metric DifferentialGeometry.Topology.ThreeManifold.Surgery DifferentialGeometry.Topology.Manifold.Attachment
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Geometry.Curvature
open scoped Manifold ContDiff Topology
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
local notation "CurvGOld" => finiteRetainedInteriorOpens transitionEnd_pos hδ f hf hdisj R
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

theorem finiteFullPreparedMetric_witness_curvature (b : CurvGB) :
    let : LocallyPathConnectedSpace M := originalModel_locallyPathConnected I Fact.out
    let : ChartedSpace CurvGE3 CurvGQ := finiteCapChartedSpace I Fact.out transitionEnd_pos hδ f hf hdisj
    let : IsManifold (𝓡 3) ∞ CurvGQ := finiteCapQuotient_isManifold Fact.out transitionEnd_pos hδ f hf hdisj hs
    let : T2Space CurvGQ := finiteCapQuotient_t2Space transitionEnd_pos hδ f hf hdisj
    let gRet := finiteFullPreparedMetric I hδ f hf hdisj hs U g R hRet c hc x₀ order d₀ hOriginal hrec d hmap hside w
    ∀ q : InsertionQuotient (inv_pos.mpr (d b).precision_pos),
      metricScalarAt gRet (finiteFullWitnessMap I Fact.out transitionEnd_pos hδ f hf hdisj hs R c hc b q) = metricScalarAt (w b).data.outMetric q ∧
        leastCurvatureOperatorEigenvalueAt gRet (finiteFullWitnessMap I Fact.out transitionEnd_pos hδ f hf hdisj hs R c hc b q)
          (metricAlgebraicCurvatureTensorAt gRet (finiteFullWitnessMap I Fact.out transitionEnd_pos hδ f hf hdisj hs R c hc b q)) =
            leastCurvatureOperatorEigenvalueAt (w b).data.outMetric q
              (metricAlgebraicCurvatureTensorAt (w b).data.outMetric q) := by
  let : LocallyPathConnectedSpace M := originalModel_locallyPathConnected I Fact.out
  let : ChartedSpace CurvGE3 CurvGQ := finiteCapChartedSpace I Fact.out transitionEnd_pos hδ f hf hdisj
  let : IsManifold (𝓡 3) ∞ CurvGQ := finiteCapQuotient_isManifold Fact.out transitionEnd_pos hδ f hf hdisj hs
  let : T2Space CurvGQ := finiteCapQuotient_t2Space transitionEnd_pos hδ f hf hdisj
  dsimp only
  intro q
  have he := curvature_of_injective_local_isometry (w b).data.outMetric
    (finiteFullPreparedMetric I hδ f hf hdisj hs U g R hRet c hc x₀ order d₀ hOriginal hrec d hmap hside w)
    (finiteFullWitnessMap I Fact.out transitionEnd_pos hδ f hf hdisj hs R c hc b)
    (isLocalDiffeomorph_finiteFullWitnessMap I Fact.out transitionEnd_pos hδ f hf hdisj hs R c hc b)
    (injective_finiteFullWitnessMap I Fact.out transitionEnd_pos hδ f hf hdisj hs R c hc b)
    (fun p v z => (finiteFullPreparedMetric_witness_inner I hδ f hf hdisj hs U g R hRet c hc x₀ order d₀ hOriginal hrec d hmap hside w b p v z).symm) q
  exact ⟨he.1.symm, he.2.symm⟩

theorem finiteFullPreparedMetric_witness_scalar {C : ℕ → ℝ}
    (hw : ∀ b : CurvGB, StaticInsertionAdditionalProperties C (w b)) (b : CurvGB) :
    let : LocallyPathConnectedSpace M := originalModel_locallyPathConnected I Fact.out
    let : ChartedSpace CurvGE3 CurvGQ := finiteCapChartedSpace I Fact.out transitionEnd_pos hδ f hf hdisj
    let : IsManifold (𝓡 3) ∞ CurvGQ := finiteCapQuotient_isManifold Fact.out transitionEnd_pos hδ f hf hdisj hs
    let : T2Space CurvGQ := finiteCapQuotient_t2Space transitionEnd_pos hδ f hf hdisj
    let gRet := finiteFullPreparedMetric I hδ f hf hdisj hs U g R hRet c hc x₀ order d₀ hOriginal hrec d hmap hside w
    (∀ q : InsertionQuotient (inv_pos.mpr (d b).precision_pos),
      0 < metricScalarAt gRet (finiteFullWitnessMap I Fact.out transitionEnd_pos hδ f hf hdisj hs R c hc b q)) ∧
    (∀ q ∈ range (w b).data.capMap,
      metricScalarAt gRet (finiteFullWitnessMap I Fact.out transitionEnd_pos hδ f hf hdisj hs R c hc b q) ≤ C 0 *
        metricScalarAt g ((d₀ b.val.1).offsetPoint (cuttingSign_sq b.val.2))) := by
  let : LocallyPathConnectedSpace M := originalModel_locallyPathConnected I Fact.out
  let : ChartedSpace CurvGE3 CurvGQ := finiteCapChartedSpace I Fact.out transitionEnd_pos hδ f hf hdisj
  let : IsManifold (𝓡 3) ∞ CurvGQ := finiteCapQuotient_isManifold Fact.out transitionEnd_pos hδ f hf hdisj hs
  let : T2Space CurvGQ := finiteCapQuotient_t2Space transitionEnd_pos hδ f hf hdisj
  constructor
  · intro q
    rw [(finiteFullPreparedMetric_witness_curvature I hδ f hf hdisj hs U g R hRet c hc x₀ order d₀ hOriginal hrec d hmap hside w b q).1]
    exact (hw b).scalar_positive q
  · intro q hq
    rw [(finiteFullPreparedMetric_witness_curvature I hδ f hf hdisj hs U g R hRet c hc x₀ order d₀ hOriginal hrec d hmap hside w b q).1]
    exact ((hw b).cap_scalar q hq).2

theorem finiteFullPreparedMetric_old_curvature [CompactSpace M] :
    let : LocallyPathConnectedSpace M := originalModel_locallyPathConnected I Fact.out
    let : ChartedSpace CurvGE3 CurvGQ := finiteCapChartedSpace I Fact.out transitionEnd_pos hδ f hf hdisj
    let : IsManifold (𝓡 3) ∞ CurvGQ := finiteCapQuotient_isManifold Fact.out transitionEnd_pos hδ f hf hdisj hs
    let : T2Space CurvGQ := finiteCapQuotient_t2Space transitionEnd_pos hδ f hf hdisj
    let gRet := finiteFullPreparedMetric I hδ f hf hdisj hs U g R hRet c hc x₀ order d₀ hOriginal hrec d hmap hside w
    ∀ q : CurvGOld,
      metricScalarAt gRet (Opens.inclusion inf_le_left q) = metricScalarAt g (finiteRetainedInteriorOriginalMap transitionEnd_pos hδ f hf hdisj U R hRet q) ∧
        leastCurvatureOperatorEigenvalueAt gRet (Opens.inclusion inf_le_left q)
          (metricAlgebraicCurvatureTensorAt gRet (Opens.inclusion inf_le_left q)) =
            leastCurvatureOperatorEigenvalueAt g (finiteRetainedInteriorOriginalMap transitionEnd_pos hδ f hf hdisj U R hRet q)
              (metricAlgebraicCurvatureTensorAt g (finiteRetainedInteriorOriginalMap transitionEnd_pos hδ f hf hdisj U R hRet q)) := by
  let : LocallyPathConnectedSpace M := originalModel_locallyPathConnected I Fact.out
  let : ChartedSpace CurvGE3 CurvGQ := finiteCapChartedSpace I Fact.out transitionEnd_pos hδ f hf hdisj
  let : IsManifold (𝓡 3) ∞ CurvGQ := finiteCapQuotient_isManifold Fact.out transitionEnd_pos hδ f hf hdisj hs
  let : T2Space CurvGQ := finiteCapQuotient_t2Space transitionEnd_pos hδ f hf hdisj
  let : CompactSpace CurvGQ := finiteCapQuotient_compactSpace transitionEnd_pos hδ f hf hdisj
  let : SecondCountableTopology CurvGQ := ChartedSpace.secondCountable_of_sigmaCompact CurvGE3 CurvGQ
  let : SigmaCompactSpace CurvGOld := isSigmaCompact_iff_sigmaCompactSpace.mp
    (DifferentialGeometry.Geometry.isSigmaCompact_of_isOpen (𝓡 3) (CurvGOld).isOpen)
  let old := finiteOldMetric I Fact.out transitionEnd_pos hδ f hf hdisj hs U g R hRet
  let gRet := finiteFullPreparedMetric I hδ f hf hdisj hs U g R hRet c hc x₀ order d₀ hOriginal hrec d hmap hside w
  let inc : CurvGOld → CurvGRet := Opens.inclusion inf_le_left
  have hi : Injective inc := fun _ _ he => Subtype.ext (congrArg (fun q : CurvGRet => q.val) he)
  have hl : IsLocalDiffeomorph (𝓡 3) (𝓡 3) ∞ inc := by
    apply DifferentialGeometry.Topology.Manifold.isLocalDiffeomorph_of_injective_mfderiv _
      (contMDiff_inclusion (n := ∞) (show CurvGOld ≤ CurvGRet from inf_le_left)) _ rfl
    intro q
    rw [mfderiv_opens_incl]
    exact fun _ _ he => he
  have hm : ∀ (q : CurvGOld) (v z : TangentSpace (𝓡 3) q),
      old.inner q v z = gRet.inner (inc q) (mfderiv (𝓡 3) (𝓡 3) inc q v) (mfderiv (𝓡 3) (𝓡 3) inc q z) := by
    intro q v z
    dsimp only [inc]
    rw [mfderiv_opens_incl]
    exact (finiteGluedMetric_inner_old I hδ f hf hdisj hs U g R hRet
      (fun b => (c * precision b.1)⁻¹) (fun b => (preparedFullCapWidth_bounds c (precision b.1) hc (hδ b.1)).1)
      x₀ order d₀ hOriginal hrec d hmap hside w
      (fun b => (preparedFullCapWidth_bounds c (precision b.val.1) hc (hδ b.val.1)).2.le) (fun _ => le_rfl) q v z).symm
  dsimp only
  intro q
  have hglobal := curvature_of_injective_local_isometry old gRet inc hl hi hm q
  have horiginal := curvature_of_injective_local_isometry old g (finiteRetainedInteriorOriginalMap transitionEnd_pos hδ f hf hdisj U R hRet)
    (isLocalDiffeomorph_finiteRetainedInteriorOriginalMap transitionEnd_pos hδ f hf hdisj I Fact.out hs U R hRet)
    (injective_finiteRetainedInteriorOriginalMap transitionEnd_pos hδ f hf hdisj U R hRet)
    (finiteOldMetric_inner I Fact.out transitionEnd_pos hδ f hf hdisj hs U g R hRet) q
  exact ⟨hglobal.1.symm.trans horiginal.1, hglobal.2.symm.trans horiginal.2⟩

theorem finiteFullPreparedMetric_hamiltonIvey [CompactSpace M] {C : ℕ → ℝ}
    (hw : ∀ b : CurvGB, StaticInsertionAdditionalProperties C (w b))
    (a : ℝ) (ha : 0 < a)
    (hin : ∀ p : U, (metricScalarAt g p,
      2 * leastCurvatureOperatorEigenvalueAt g p (metricAlgebraicCurvatureTensorAt g p)) ∈ fixedHamiltonIveyRegion a) :
    let : LocallyPathConnectedSpace M := originalModel_locallyPathConnected I Fact.out
    let : ChartedSpace CurvGE3 CurvGQ := finiteCapChartedSpace I Fact.out transitionEnd_pos hδ f hf hdisj
    let : IsManifold (𝓡 3) ∞ CurvGQ := finiteCapQuotient_isManifold Fact.out transitionEnd_pos hδ f hf hdisj hs
    let : T2Space CurvGQ := finiteCapQuotient_t2Space transitionEnd_pos hδ f hf hdisj
    let gRet := finiteFullPreparedMetric I hδ f hf hdisj hs U g R hRet c hc x₀ order d₀ hOriginal hrec d hmap hside w
    ∀ q : CurvGRet, (metricScalarAt gRet q,
      2 * leastCurvatureOperatorEigenvalueAt gRet q (metricAlgebraicCurvatureTensorAt gRet q)) ∈ fixedHamiltonIveyRegion a := by
  let : LocallyPathConnectedSpace M := originalModel_locallyPathConnected I Fact.out
  let : ChartedSpace CurvGE3 CurvGQ := finiteCapChartedSpace I Fact.out transitionEnd_pos hδ f hf hdisj
  let : IsManifold (𝓡 3) ∞ CurvGQ := finiteCapQuotient_isManifold Fact.out transitionEnd_pos hδ f hf hdisj hs
  let : T2Space CurvGQ := finiteCapQuotient_t2Space transitionEnd_pos hδ f hf hdisj
  dsimp only
  intro q
  have hcover := Set.ext_iff.mp (finiteCapRetained_restricted_cover transitionEnd_pos hδ f hf hdisj R
    (fun b => (c * precision b.1)⁻¹) (fun b => (preparedFullCapWidth_bounds c (precision b.1) hc (hδ b.1)).1)) q.val
  rcases hcover.mpr q.property with hold | hcap
  · let p : CurvGOld := ⟨q.val, hold⟩
    have hq : Opens.inclusion (show CurvGOld ≤ CurvGRet from inf_le_left) p = q := rfl
    obtain ⟨hR, hν⟩ := finiteFullPreparedMetric_old_curvature I hδ f hf hdisj hs U g R hRet c hc x₀ order d₀ hOriginal hrec d hmap hside w p
    rw [hq] at hR hν
    rw [hR, hν]
    exact hin _
  · obtain ⟨b, hb⟩ := mem_iUnion.mp hcap
    have hrange := range_finiteFullWitnessMap I Fact.out transitionEnd_pos hδ f hf hdisj hs R c hc b
    have hq : q ∈ range (finiteFullWitnessMap I Fact.out transitionEnd_pos hδ f hf hdisj hs R c hc b) := hrange.symm ▸ hb
    obtain ⟨p, rfl⟩ := hq
    obtain ⟨hR, hν⟩ := finiteFullPreparedMetric_witness_curvature I hδ f hf hdisj hs U g R hRet c hc x₀ order d₀ hOriginal hrec d hmap hside w b p
    rw [hR, hν]
    exact (hw b).hamiltonIvey a ha (fun x => hin ((d b).controlledMap x)) p

theorem finiteFullPreparedMetric_scalar_floor [CompactSpace M] {C : ℕ → ℝ}
    (hw : ∀ b : CurvGB, StaticInsertionAdditionalProperties C (w b))
    (L₀ : ℝ) (hL₀ : L₀ ≤ 0) (hin : ∀ p : U, L₀ ≤ metricScalarAt g p) :
    let : LocallyPathConnectedSpace M := originalModel_locallyPathConnected I Fact.out
    let : ChartedSpace CurvGE3 CurvGQ := finiteCapChartedSpace I Fact.out transitionEnd_pos hδ f hf hdisj
    let : IsManifold (𝓡 3) ∞ CurvGQ := finiteCapQuotient_isManifold Fact.out transitionEnd_pos hδ f hf hdisj hs
    let : T2Space CurvGQ := finiteCapQuotient_t2Space transitionEnd_pos hδ f hf hdisj
    let gRet := finiteFullPreparedMetric I hδ f hf hdisj hs U g R hRet c hc x₀ order d₀ hOriginal hrec d hmap hside w
    ∀ q : CurvGRet, L₀ ≤ metricScalarAt gRet q := by
  let : LocallyPathConnectedSpace M := originalModel_locallyPathConnected I Fact.out
  let : ChartedSpace CurvGE3 CurvGQ := finiteCapChartedSpace I Fact.out transitionEnd_pos hδ f hf hdisj
  let : IsManifold (𝓡 3) ∞ CurvGQ := finiteCapQuotient_isManifold Fact.out transitionEnd_pos hδ f hf hdisj hs
  let : T2Space CurvGQ := finiteCapQuotient_t2Space transitionEnd_pos hδ f hf hdisj
  dsimp only
  intro q
  have hcover := Set.ext_iff.mp (finiteCapRetained_restricted_cover transitionEnd_pos hδ f hf hdisj R
    (fun b => (c * precision b.1)⁻¹) (fun b => (preparedFullCapWidth_bounds c (precision b.1) hc (hδ b.1)).1)) q.val
  rcases hcover.mpr q.property with hold | hcap
  · let p : CurvGOld := ⟨q.val, hold⟩
    have hq : Opens.inclusion (show CurvGOld ≤ CurvGRet from inf_le_left) p = q := rfl
    have hR := (finiteFullPreparedMetric_old_curvature I hδ f hf hdisj hs U g R hRet c hc x₀ order d₀ hOriginal hrec d hmap hside w p).1
    rw [hq] at hR
    rw [hR]
    exact hin _
  · obtain ⟨b, hb⟩ := mem_iUnion.mp hcap
    have hrange := range_finiteFullWitnessMap I Fact.out transitionEnd_pos hδ f hf hdisj hs R c hc b
    have hq : q ∈ range (finiteFullWitnessMap I Fact.out transitionEnd_pos hδ f hf hdisj hs R c hc b) := hrange.symm ▸ hb
    obtain ⟨p, rfl⟩ := hq
    exact hL₀.trans ((finiteFullPreparedMetric_witness_scalar I hδ f hf hdisj hs U g R hRet c hc x₀ order d₀ hOriginal hrec d hmap hside w hw b).1 p).le
end DifferentialGeometry.PDE.RicciFlow.StandardCap
