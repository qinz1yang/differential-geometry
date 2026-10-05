import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.StandardCap.FullPreparedGluing
import DifferentialGeometry.Geometry.Measure.LocalIsometry
import DifferentialGeometry.Topology.ThreeManifold.Surgery.FiniteCap.RetainedCoreMaps
import DifferentialGeometry.Topology.ThreeManifold.Surgery.FiniteCap.FiniteCapExhaustiveness

set_option autoImplicit false
noncomputable section
open Set Function TopologicalSpace Manifold DifferentialGeometry
open DifferentialGeometry.Geometry.Neck DifferentialGeometry.Geometry.Metric DifferentialGeometry.Topology.ThreeManifold.Surgery DifferentialGeometry.Topology.Manifold.Attachment
open DifferentialGeometry.Topology.Manifold
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Integral.Measure MeasureTheory
open scoped Manifold ContDiff Topology
namespace DifferentialGeometry.PDE.RicciFlow.StandardCap
private theorem retained_interior_inclusion_range
    {ι M : Type*} [Finite ι] [TopologicalSpace M] [T2Space M]
    [LocallyPathConnectedSpace M] {precision : ι → ℝ} {L : ℝ}
    (hL : 0 < L) (hδ : ∀ i, 0 < precision i)
    (f : ∀ i : ι, bufferedCylinder (precision i) → M)
    (hf : ∀ i, _root_.Topology.IsOpenEmbedding (f i))
    (hdisj : Pairwise fun i j => Disjoint (range (f i)) (range (f j)))
    (R : Set (ConnectedComponents (cutCore f))) :
    range (Opens.inclusion inf_le_left :
      finiteRetainedInteriorOpens hL hδ f hf hdisj R →
        finiteCapRetained hL hδ f hf hdisj R) =
      interior (range (finiteRetainedCoreInclusion hL hδ f hf hdisj R)) := by
  let Q := FiniteCapQuotient hL hδ f (fun i => (hf i).injective) hdisj
  let Ret := finiteCapRetained hL hδ f hf hdisj R
  let j := finiteCoreInclusion hL hδ f (fun i => (hf i).injective) hdisj
  have hr : range (finiteRetainedCoreInclusion hL hδ f hf hdisj R) =
      (Subtype.val : Ret → Q) ⁻¹' range j := by
    ext q
    constructor
    · rintro ⟨p, rfl⟩
      exact ⟨p.val, rfl⟩
    · rintro ⟨p, hp⟩
      have hpr : p ∈ retainedCore f R := by
        have hq := q.property
        change q.val ∈ (Ret : Set Q) at hq
        rw [← hp] at hq
        exact hq
      exact ⟨⟨p, hpr⟩, Subtype.ext hp⟩
  have hi := Ret.isOpen.isOpenMap_subtype_val.preimage_interior_eq_interior_preimage
    continuous_subtype_val (s := range j)
  apply Eq.trans ?_ ((congrArg interior hr).trans hi.symm).symm
  rw [finiteCoreInclusion_interior_range hL hδ f hf hdisj]
  ext q
  constructor
  · rintro ⟨p, rfl⟩
    exact p.property.2
  · intro hq
    exact ⟨⟨q.val, q.property, hq⟩, Subtype.ext rfl⟩

private abbrev CurvGE3 := EuclideanSpace ℝ (Fin 3)
private abbrev CurvCap := {x : EuclideanSpace ℝ (Fin 3) // ‖x‖ ≤ transitionEnd}
private local instance : CompactSpace CurvCap :=
  (closedBallUnitHomeomorph transitionEnd_pos).symm.compactSpace
private local instance : ChartedSpace (EuclideanHalfSpace 3) CurvCap := closedBallChartedSpace transitionEnd_pos
private local instance : IsManifold (𝓡∂ 3) ∞ CurvCap := closedBall_isManifold transitionEnd_pos
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

private local instance {B : ℝ} {hB : 0 < B} :
    MeasurableSpace (InsertionQuotient hB) := borel (InsertionQuotient hB)
private local instance {B : ℝ} {hB : 0 < B} : BorelSpace (InsertionQuotient hB) := ⟨rfl⟩

theorem finiteFullPreparedMetric_cap_volume [CompactSpace M] (b : CurvGB) :
    let : LocallyPathConnectedSpace M := originalModel_locallyPathConnected I Fact.out
    let : ChartedSpace CurvGE3 CurvGQ := finiteCapChartedSpace I Fact.out transitionEnd_pos hδ f hf hdisj
    let : IsManifold (𝓡 3) ∞ CurvGQ := finiteCapQuotient_isManifold Fact.out transitionEnd_pos hδ f hf hdisj hs
    let : T2Space CurvGQ := finiteCapQuotient_t2Space transitionEnd_pos hδ f hf hdisj
    let : CompactSpace CurvGQ := finiteCapQuotient_compactSpace transitionEnd_pos hδ f hf hdisj
    let : CompactSpace CurvGRet :=
      (finiteCapRetained_discarded_compactSpace transitionEnd_pos hδ f hf hdisj R).1
    let gRet := finiteFullPreparedMetric I hδ f hf hdisj hs U g R hRet c hc x₀ order d₀ hOriginal hrec d hmap hside w
    riemannianVolumeMeasure (𝓡 3) CurvGRet gRet
      (range (finiteFullWitnessMap I Fact.out transitionEnd_pos hδ f hf hdisj hs R c hc b ∘
        (w b).data.capMap)) =
      riemannianVolumeMeasure (𝓡 3) (InsertionQuotient (inv_pos.mpr (d b).precision_pos))
        (w b).data.outMetric (range (w b).data.capMap) := by
  let : LocallyPathConnectedSpace M := originalModel_locallyPathConnected I Fact.out
  let : ChartedSpace CurvGE3 CurvGQ := finiteCapChartedSpace I Fact.out transitionEnd_pos hδ f hf hdisj
  let : IsManifold (𝓡 3) ∞ CurvGQ := finiteCapQuotient_isManifold Fact.out transitionEnd_pos hδ f hf hdisj hs
  let : T2Space CurvGQ := finiteCapQuotient_t2Space transitionEnd_pos hδ f hf hdisj
  let : CompactSpace CurvGQ := finiteCapQuotient_compactSpace transitionEnd_pos hδ f hf hdisj
  let : CompactSpace CurvGRet :=
    (finiteCapRetained_discarded_compactSpace transitionEnd_pos hδ f hf hdisj R).1
  dsimp only
  rw [range_comp]
  exact (DifferentialGeometry.Geometry.Measure.riemannianVolumeMeasure_image_eq_of_injective_local_isometry
    (w b).data.outMetric
    (finiteFullPreparedMetric I hδ f hf hdisj hs U g R hRet c hc x₀ order d₀ hOriginal hrec d hmap hside w)
    (finiteFullWitnessMap I Fact.out transitionEnd_pos hδ f hf hdisj hs R c hc b)
    (isLocalDiffeomorph_finiteFullWitnessMap I Fact.out transitionEnd_pos hδ f hf hdisj hs R c hc b)
    (injective_finiteFullWitnessMap I Fact.out transitionEnd_pos hδ f hf hdisj hs R c hc b)
    (fun p v z => (finiteFullPreparedMetric_witness_inner I hδ f hf hdisj hs U g R hRet c hc
      x₀ order d₀ hOriginal hrec d hmap hside w b p v z).symm)
    (isCompact_range (w b).properties.capMap_embedding.contMDiff.continuous).measurableSet).symm

theorem finiteFullPreparedMetric_old_volume_le [CompactSpace M] :
    let : SecondCountableTopology H := I.secondCountableTopology
    let : SecondCountableTopology M := ChartedSpace.secondCountable_of_sigmaCompact H M
    let : SigmaCompactSpace U := isSigmaCompact_iff_sigmaCompactSpace.mp
      (DifferentialGeometry.Geometry.isSigmaCompact_of_isOpen I U.isOpen)
    let : LocallyPathConnectedSpace M := originalModel_locallyPathConnected I Fact.out
    let : ChartedSpace CurvGE3 CurvGQ := finiteCapChartedSpace I Fact.out transitionEnd_pos hδ f hf hdisj
    let : IsManifold (𝓡 3) ∞ CurvGQ := finiteCapQuotient_isManifold Fact.out transitionEnd_pos hδ f hf hdisj hs
    let : T2Space CurvGQ := finiteCapQuotient_t2Space transitionEnd_pos hδ f hf hdisj
    let : CompactSpace CurvGQ := finiteCapQuotient_compactSpace transitionEnd_pos hδ f hf hdisj
    let : CompactSpace CurvGRet :=
      (finiteCapRetained_discarded_compactSpace transitionEnd_pos hδ f hf hdisj R).1
    let gRet := finiteFullPreparedMetric I hδ f hf hdisj hs U g R hRet c hc x₀ order d₀ hOriginal hrec d hmap hside w
    riemannianVolumeMeasure (𝓡 3) CurvGRet gRet
      (range (Opens.inclusion (show CurvGOld ≤ CurvGRet from inf_le_left))) ≤
      riemannianVolumeMeasure I U g (range (retainedCoreDomainMap f R U hRet)) := by
  let : LocallyPathConnectedSpace M := originalModel_locallyPathConnected I Fact.out
  let : ChartedSpace CurvGE3 CurvGQ := finiteCapChartedSpace I Fact.out transitionEnd_pos hδ f hf hdisj
  let : IsManifold (𝓡 3) ∞ CurvGQ := finiteCapQuotient_isManifold Fact.out transitionEnd_pos hδ f hf hdisj hs
  let : T2Space CurvGQ := finiteCapQuotient_t2Space transitionEnd_pos hδ f hf hdisj
  let : CompactSpace CurvGQ := finiteCapQuotient_compactSpace transitionEnd_pos hδ f hf hdisj
  let : SecondCountableTopology CurvGQ := ChartedSpace.secondCountable_of_sigmaCompact CurvGE3 CurvGQ
  let : SigmaCompactSpace CurvGOld := isSigmaCompact_iff_sigmaCompactSpace.mp
    (DifferentialGeometry.Geometry.isSigmaCompact_of_isOpen (𝓡 3) (CurvGOld).isOpen)
  let : SecondCountableTopology H := I.secondCountableTopology
  let : SecondCountableTopology M := ChartedSpace.secondCountable_of_sigmaCompact H M
  let : SigmaCompactSpace U := isSigmaCompact_iff_sigmaCompactSpace.mp
    (DifferentialGeometry.Geometry.isSigmaCompact_of_isOpen I U.isOpen)
  let : CompactSpace CurvGRet :=
    (finiteCapRetained_discarded_compactSpace transitionEnd_pos hδ f hf hdisj R).1
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
  have hout := DifferentialGeometry.Geometry.Measure.riemannianVolumeMeasure_image_eq_of_injective_local_isometry
    old gRet inc hl hi hm MeasurableSet.univ
  have hin := DifferentialGeometry.Geometry.Measure.riemannianVolumeMeasure_image_eq_of_injective_local_isometry
    old g (finiteRetainedInteriorOriginalMap transitionEnd_pos hδ f hf hdisj U R hRet)
    (isLocalDiffeomorph_finiteRetainedInteriorOriginalMap transitionEnd_pos hδ f hf hdisj I Fact.out hs U R hRet)
    (injective_finiteRetainedInteriorOriginalMap transitionEnd_pos hδ f hf hdisj U R hRet)
    (finiteOldMetric_inner I Fact.out transitionEnd_pos hδ f hf hdisj hs U g R hRet)
    MeasurableSet.univ
  rw [image_univ] at hout hin
  dsimp only
  change riemannianVolumeMeasure (𝓡 3) CurvGRet gRet (range inc) ≤ _
  rw [← hout, hin]
  apply measure_mono
  rintro y ⟨q, rfl⟩
  let x := (finiteCoreInteriorHomeomorph transitionEnd_pos hδ f hf hdisj).symm
    (Opens.inclusion inf_le_right q)
  have hxR : (⟨x.val, interior_subset x.property⟩ : cutCore f) ∈ retainedCore f R := by
    change finiteCapComponentLabel transitionEnd_pos hδ f hf hdisj
      (finiteCoreInteriorMap transitionEnd_pos hδ f (fun i => (hf i).injective) hdisj x) ∈ R
    rw [finiteRetainedInterior_original_point]
    exact q.property.1
  exact ⟨⟨⟨x.val, interior_subset x.property⟩, hxR⟩, rfl⟩

private theorem finiteFullPreparedMetric_cap_cover :
    let : LocallyPathConnectedSpace M := originalModel_locallyPathConnected I Fact.out
    let : ChartedSpace CurvGE3 CurvGQ := finiteCapChartedSpace I Fact.out transitionEnd_pos hδ f hf hdisj
    (univ : Set CurvGRet) =
      range (Opens.inclusion (show CurvGOld ≤ CurvGRet from inf_le_left)) ∪
      ⋃ b : CurvGB, range (finiteFullWitnessMap I Fact.out transitionEnd_pos hδ f hf hdisj hs R c hc b ∘
        (w b).data.capMap) := by
  let : LocallyPathConnectedSpace M := originalModel_locallyPathConnected I Fact.out
  let : ChartedSpace CurvGE3 CurvGQ := finiteCapChartedSpace I Fact.out transitionEnd_pos hδ f hf hdisj
  dsimp only
  have hcap (b : CurvGB) :
      (finiteFullWitnessMap I Fact.out transitionEnd_pos hδ f hf hdisj hs R c hc b ∘ (w b).data.capMap) =
      (fun x : CurvCap => (⟨finiteCapInclusion transitionEnd_pos hδ f (fun i => (hf i).injective) hdisj
        ⟨b.val, x⟩, b.property⟩ : CurvGRet)) := by
    funext x
    change finiteFullWitnessMap I Fact.out transitionEnd_pos hδ f hf hdisj hs R c hc b ((w b).data.capMap x) = _
    rw [(w b).properties.capMap_eq, (w b).properties.capInclusion_eq]
    apply Subtype.ext
    exact congrArg (fun p : finiteCapRestrictedNeighborhood transitionEnd_pos hδ f hf hdisj
      b.val ((c * precision b.val.1)⁻¹) => p.val)
      (finiteCapFullInsertionDiffeomorph_symm_cap I Fact.out transitionEnd_pos hδ f hf hdisj hs b.val
        (preparedFullCapWidth_bounds c (precision b.val.1) hc (hδ b.val.1)).2.le
        (preparedFullCapWidth_bounds c (precision b.val.1) hc (hδ b.val.1)).1 x)
  simp_rw [hcap]
  rw [retained_interior_inclusion_range transitionEnd_pos hδ f hf hdisj R,
    ← finiteRetained_compl_interior_core transitionEnd_pos hδ f hf hdisj R]
  exact (union_compl_self _).symm

theorem finiteFullPreparedMetric_volume_le [CompactSpace M] :
    let : SecondCountableTopology H := I.secondCountableTopology
    let : SecondCountableTopology M := ChartedSpace.secondCountable_of_sigmaCompact H M
    let : SigmaCompactSpace U := isSigmaCompact_iff_sigmaCompactSpace.mp
      (DifferentialGeometry.Geometry.isSigmaCompact_of_isOpen I U.isOpen)
    let : LocallyPathConnectedSpace M := originalModel_locallyPathConnected I Fact.out
    let : ChartedSpace CurvGE3 CurvGQ := finiteCapChartedSpace I Fact.out transitionEnd_pos hδ f hf hdisj
    let : IsManifold (𝓡 3) ∞ CurvGQ := finiteCapQuotient_isManifold Fact.out transitionEnd_pos hδ f hf hdisj hs
    let : T2Space CurvGQ := finiteCapQuotient_t2Space transitionEnd_pos hδ f hf hdisj
    let : CompactSpace CurvGQ := finiteCapQuotient_compactSpace transitionEnd_pos hδ f hf hdisj
    let : CompactSpace CurvGRet :=
      (finiteCapRetained_discarded_compactSpace transitionEnd_pos hδ f hf hdisj R).1
    let gRet := finiteFullPreparedMetric I hδ f hf hdisj hs U g R hRet c hc x₀ order d₀ hOriginal hrec d hmap hside w
    riemannianVolumeMeasure (𝓡 3) CurvGRet gRet univ ≤
      riemannianVolumeMeasure I U g (range (retainedCoreDomainMap f R U hRet)) +
      ∑' b : CurvGB, riemannianVolumeMeasure (𝓡 3)
        (InsertionQuotient (inv_pos.mpr (d b).precision_pos))
        (w b).data.outMetric (range (w b).data.capMap) := by
  let : SecondCountableTopology H := I.secondCountableTopology
  let : SecondCountableTopology M := ChartedSpace.secondCountable_of_sigmaCompact H M
  let : SigmaCompactSpace U := isSigmaCompact_iff_sigmaCompactSpace.mp
    (DifferentialGeometry.Geometry.isSigmaCompact_of_isOpen I U.isOpen)
  let : LocallyPathConnectedSpace M := originalModel_locallyPathConnected I Fact.out
  let : ChartedSpace CurvGE3 CurvGQ := finiteCapChartedSpace I Fact.out transitionEnd_pos hδ f hf hdisj
  let : IsManifold (𝓡 3) ∞ CurvGQ := finiteCapQuotient_isManifold Fact.out transitionEnd_pos hδ f hf hdisj hs
  let : T2Space CurvGQ := finiteCapQuotient_t2Space transitionEnd_pos hδ f hf hdisj
  let : CompactSpace CurvGQ := finiteCapQuotient_compactSpace transitionEnd_pos hδ f hf hdisj
  let : CompactSpace CurvGRet :=
    (finiteCapRetained_discarded_compactSpace transitionEnd_pos hδ f hf hdisj R).1
  dsimp only
  let gRet := finiteFullPreparedMetric I hδ f hf hdisj hs U g R hRet c hc x₀ order d₀ hOriginal hrec d hmap hside w
  let μ := riemannianVolumeMeasure (𝓡 3) CurvGRet gRet
  let O := range (Opens.inclusion (show CurvGOld ≤ CurvGRet from inf_le_left))
  let caps := fun b : CurvGB => range
    (finiteFullWitnessMap I Fact.out transitionEnd_pos hδ f hf hdisj hs R c hc b ∘ (w b).data.capMap)
  have hcover : (univ : Set CurvGRet) = O ∪ ⋃ b, caps b :=
    finiteFullPreparedMetric_cap_cover (I := I) (hδ := hδ) (f := f) (hf := hf)
      (hdisj := hdisj) (hs := hs) (U := U) (g := g) (R := R) (c := c) (hc := hc)
      (x₀ := x₀) (order := order) (d₀ := d₀) (d := d) (w := w)
  change μ univ ≤ _
  calc
    μ univ = μ (O ∪ ⋃ b, caps b) := congrArg μ hcover
    _ ≤ μ O + μ (⋃ b, caps b) := measure_union_le _ _
    _ ≤ μ O + ∑' b, μ (caps b) := add_le_add_right (measure_iUnion_le _) _
    _ ≤ _ := by
      apply add_le_add
      · exact finiteFullPreparedMetric_old_volume_le I hδ f hf hdisj hs U g R hRet c hc
          x₀ order d₀ hOriginal hrec d hmap hside w
      · apply ENNReal.tsum_le_tsum
        intro b
        exact (finiteFullPreparedMetric_cap_volume I hδ f hf hdisj hs U g R hRet c hc
          x₀ order d₀ hOriginal hrec d hmap hside w b).le

end DifferentialGeometry.PDE.RicciFlow.StandardCap
