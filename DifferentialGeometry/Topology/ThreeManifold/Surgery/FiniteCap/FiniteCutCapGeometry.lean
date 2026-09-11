import DifferentialGeometry.Topology.ThreeManifold.Surgery.FiniteCap.OriginalTubularEmbedding
import DifferentialGeometry.Topology.ThreeManifold.Surgery.FiniteCap.NativeBoundaryComponents
import DifferentialGeometry.Topology.ThreeManifold.Surgery.FiniteCap.NativeCoreBoundaryOrientation
import DifferentialGeometry.Topology.ThreeManifold.Surgery.FiniteCap.FiniteCapExhaustiveness
import DifferentialGeometry.Topology.ThreeManifold.Surgery.FiniteCap.FiniteCapBallSmooth
import DifferentialGeometry.Topology.ThreeManifold.Surgery.FiniteCap.FiniteCoreSmoothEmbedding
import DifferentialGeometry.Topology.ThreeManifold.Surgery.FiniteCap.FiniteCapDecomposition

set_option autoImplicit false
noncomputable section
open Set Function TopologicalSpace Manifold
open DifferentialGeometry.Integral.DivergenceTheorem.WithBoundary
open DifferentialGeometry.Geometry.Neck DifferentialGeometry.Topology.Manifold DifferentialGeometry.Topology.Manifold.Attachment
open scoped Manifold ContDiff Topology
namespace DifferentialGeometry.Topology.ThreeManifold.Surgery
private abbrev E3 := EuclideanSpace ℝ (Fin 3)
private abbrev Ball (L : ℝ) := {x : E3 // ‖x‖ ≤ L}
private abbrev E2 := EuclideanSpace ℝ (Fin 2)
private abbrev ER := E2 × EuclideanSpace ℝ (Fin 1)
private abbrev IR := (𝓡 2).prod (𝓡∂ 1)
private abbrev IH := ModelProd E2 (EuclideanHalfSpace 1)
private abbrev S2 := Metric.sphere (0 : E3) 1
private abbrev IC := (𝓡 2).prod 𝓘(ℝ)
private local instance : Fact (Module.finrank ℝ E3 = 2 + 1) := ⟨by simp⟩
private local instance : HasSmoothBoundary ER IH IR := productHalfSpaceBoundaryModel
private local instance : Nonempty (HasSmoothBoundary.boundaryH IR) := show Nonempty E2 from inferInstance
private local instance {X : Type*} [TopologicalSpace X] [ChartedSpace IH X] [IsManifold IR ∞ X] :
    ChartedSpace E2 (BoundaryManifold IR X) := BoundaryManifold.chartedSpace (I := IR)
private local instance {X : Type*} [TopologicalSpace X] [ChartedSpace IH X] [IsManifold IR ∞ X] :
    IsManifold (𝓡 2) ∞ (BoundaryManifold IR X) := BoundaryManifold.isManifold (I := IR)
private local instance : Nonempty (HasSmoothBoundary.boundaryH (𝓡∂ 3)) := show Nonempty E2 from inferInstance
private local instance {X : Type*} [TopologicalSpace X] [ChartedSpace (EuclideanHalfSpace 3) X] [IsManifold (𝓡∂ 3) ∞ X] :
    ChartedSpace E2 (BoundaryManifold (𝓡∂ 3) X) := BoundaryManifold.chartedSpace (I := 𝓡∂ 3)
private local instance {X : Type*} [TopologicalSpace X] [ChartedSpace (EuclideanHalfSpace 3) X] [IsManifold (𝓡∂ 3) ∞ X] :
    IsManifold (𝓡 2) ∞ (BoundaryManifold (𝓡∂ 3) X) := BoundaryManifold.isManifold (I := 𝓡∂ 3)

private local instance : Fact ((-2 : ℝ) < 2) := ⟨by norm_num⟩
variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
variable [TopologicalSpace H] (I : ModelWithCorners ℝ E H) [I.Boundaryless]
variable [TopologicalSpace M] [ChartedSpace H M] [T2Space M] [IsManifold I ∞ M]
variable {ι : Type*} [Finite ι] {precision : ι → ℝ} {L : ℝ}
variable (hdim : Module.finrank ℝ E = 3) (hL : 0 < L) (hδ : ∀ i, 0 < precision i)
variable (f : ∀ i : ι, bufferedCylinder (precision i) → M)
variable (hf : ∀ i, _root_.Topology.IsOpenEmbedding (f i))
variable (hdisj : Pairwise (fun i j => Disjoint (range (f i)) (range (f j))))
variable (hs : ∀ i, IsLocalDiffeomorph IC I ∞ (f i))
local notation "Q" => FiniteCapQuotient hL hδ f (fun i => _root_.Topology.IsEmbedding.injective (_root_.Topology.IsOpenEmbedding.toIsEmbedding (hf i))) hdisj

def FiniteCutCapGeometry (hδ1 : ∀ i, precision i < 1)
    (R : Set (ConnectedComponents (cutCore f))) : Prop :=
    let : LocallyPathConnectedSpace M := originalModel_locallyPathConnected I hdim
    letI := closedBallChartedSpace hL
    letI := closedBall_isManifold hL
    let : ChartedSpace IH (cutCore f) := cutCoreBoundaryChartedSpace I hdim hδ f hf hdisj
    let : IsManifold IR ∞ (cutCore f) := cutCore_isManifold I hdim hδ f hf hdisj hs
    let : ChartedSpace IH (retainedCore f R) := retainedCoreChartedSpace I hdim hδ f hf hdisj R
    let : IsManifold IR ∞ (retainedCore f R) := retainedCore_isManifold I hdim hδ f hf hdisj R hs
    let : ChartedSpace IH (retainedCore f Rᶜ) := retainedCoreChartedSpace I hdim hδ f hf hdisj Rᶜ
    let : IsManifold IR ∞ (retainedCore f Rᶜ) := retainedCore_isManifold I hdim hδ f hf hdisj Rᶜ hs
    let : ChartedSpace E3 Q := finiteCapChartedSpace I hdim hL hδ f hf hdisj
    let : IsManifold (𝓡 3) ∞ Q := finiteCapQuotient_isManifold hdim hL hδ f hf hdisj hs
    let ν := fun i => originalTubularMap (hδ i) (hδ1 i) (f i)
    let j := finiteCoreInclusion hL hδ f (fun i => (hf i).injective) hdisj
    let c := fun (b : ι × Bool) (x : Ball L) => finiteCapInclusion hL hδ f (fun i => (hf i).injective) hdisj ⟨b, x⟩
    let F := (finiteCapSelectedDiffeomorph I hdim hL hδ f hf hdisj R).symm
    let jRet := finiteRetainedCoreInclusion hL hδ f hf hdisj R
    let jDisc := finiteRetainedCoreInclusion hL hδ f hf hdisj Rᶜ
    (Nonempty M) ∧
    (∀ i, IsSmoothEmbedding IR I ∞ (ν i)) ∧
    (Pairwise (fun i k => Disjoint (range (ν i)) (range (ν k)))) ∧
    (cutCore f = (⋃ i, ν i '' {q : S2 × Icc (-2 : ℝ) 2 | q.2.val ∈ Ioo (-1 : ℝ) 1})ᶜ) ∧
    (IsCompact (cutCore f)) ∧
    (IsCompact (retainedCore f R) ∧ IsCompact (retainedCore f Rᶜ)) ∧
    (IsSmoothEmbedding IR I ∞ (Subtype.val : cutCore f → M)) ∧
    (IsSmoothEmbedding IR I ∞ (fun p : retainedCore f R => p.val.val)) ∧
    (IsSmoothEmbedding IR I ∞ (fun p : retainedCore f Rᶜ => p.val.val)) ∧
    (CompactSpace Q ∧ T2Space Q ∧ SecondCountableTopology Q) ∧
    (IsManifold (𝓡 3) ∞ (finiteCapRetained hL hδ f hf hdisj R) ∧ IsManifold (𝓡 3) ∞ (finiteCapDiscarded hL hδ f hf hdisj R) ∧ CompactSpace (finiteCapRetained hL hδ f hf hdisj R) ∧ CompactSpace (finiteCapDiscarded hL hδ f hf hdisj R) ∧ T2Space (finiteCapRetained hL hδ f hf hdisj R) ∧ T2Space (finiteCapDiscarded hL hδ f hf hdisj R) ∧ SecondCountableTopology (finiteCapRetained hL hδ f hf hdisj R) ∧ SecondCountableTopology (finiteCapDiscarded hL hδ f hf hdisj R)) ∧
    ((𝓡 3).boundary Q = ∅ ∧ (𝓡 3).boundary (finiteCapRetained hL hδ f hf hdisj R) = ∅ ∧ (𝓡 3).boundary (finiteCapDiscarded hL hδ f hf hdisj R) = ∅) ∧
    (∀ (b : ι × Bool) (y : S2), nativeCuttingSphereComponentsEquiv I hdim hδ f hf hdisj hs b = ConnectedComponents.mk (nativeCuttingSphereMap I hdim hδ f hf hdisj hs b y)) ∧
    (∀ (b : ι × Bool) (y : S2), connectedComponent (nativeCuttingSphereMap I hdim hδ f hf hdisj hs b y) = range (nativeCuttingSphereMap I hdim hδ f hf hdisj hs b)) ∧
    (IsSmoothEmbedding IR (𝓡 3) ∞ j) ∧
    (∀ b, IsSmoothEmbedding (𝓡∂ 3) (𝓡 3) ∞ (c b)) ∧
    (IsSmoothEmbedding IR (𝓡 3) ∞ jRet) ∧
    (IsSmoothEmbedding IR (𝓡 3) ∞ jDisc) ∧
    (range j ∪ (⋃ b, range (c b)) = univ) ∧
    (∀ b, range j ∩ range (c b) = range (fun p : nativeCuttingSphereOpens I hdim hδ f hf hdisj hs b => j p.val.val)) ∧
    (∀ b, range (fun p : nativeCuttingSphereOpens I hdim hδ f hf hdisj hs b => j p.val.val) = range (fun x : BoundaryManifold (𝓡∂ 3) (Ball L) => c b x.val)) ∧
    (Pairwise (fun b k => Disjoint (range (c b)) (range (c k)))) ∧
    (∀ (b : ι × Bool) (x : BoundaryManifold (𝓡∂ 3) (Ball L)), c b x.val = j (nativeCoreBoundaryAttachingDiffeomorph I hdim hδ f hf hdisj hs hL b x).val.val) ∧
    (∀ p : retainedCore f R, F (j p.val) = Sum.inl (jRet p)) ∧
    (∀ p : retainedCore f Rᶜ, F (j p.val) = Sum.inr (jDisc p)) ∧
    (retainedCore f R = (F ∘ j) ⁻¹' range Sum.inl) ∧
    (∀ q : finiteCapRetained hL hδ f hf hdisj R, ∃ p : retainedCore f R, jRet p ∈ connectedComponent q) ∧
    ((interior (range jRet))ᶜ = ⋃ b : {b : ι × Bool // cuttingSphereComponent hδ f hf hdisj b ∈ R}, range (fun x : Ball L => (⟨c b.val x, b.property⟩ : finiteCapRetained hL hδ f hf hdisj R))) ∧
    (Nonempty (finiteCapRetained hL hδ f hf hdisj R) ↔ Nonempty (retainedCore f R)) ∧
    (Nonempty ι ∨ Nonempty (finiteCapDiscarded hL hδ f hf hdisj R))

theorem finiteCutCapGeometry [CompactSpace M] [Nonempty M]
    (hδ1 : ∀ i, precision i < 1) (R : Set (ConnectedComponents (cutCore f)))
    (hnontrivial : Nonempty ι ∨ Nonempty (retainedCore f Rᶜ)) :
    FiniteCutCapGeometry I hdim hL hδ f hf hdisj hs hδ1 R := by
  let : LocallyPathConnectedSpace M := originalModel_locallyPathConnected I hdim
  let := closedBallChartedSpace hL
  let := closedBall_isManifold hL
  let : ChartedSpace IH (cutCore f) := cutCoreBoundaryChartedSpace I hdim hδ f hf hdisj
  let : IsManifold IR ∞ (cutCore f) := cutCore_isManifold I hdim hδ f hf hdisj hs
  let : ChartedSpace IH (retainedCore f R) := retainedCoreChartedSpace I hdim hδ f hf hdisj R
  let : IsManifold IR ∞ (retainedCore f R) := retainedCore_isManifold I hdim hδ f hf hdisj R hs
  let : ChartedSpace IH (retainedCore f Rᶜ) := retainedCoreChartedSpace I hdim hδ f hf hdisj Rᶜ
  let : IsManifold IR ∞ (retainedCore f Rᶜ) := retainedCore_isManifold I hdim hδ f hf hdisj Rᶜ hs
  let : ChartedSpace E3 Q := finiteCapChartedSpace I hdim hL hδ f hf hdisj
  let : IsManifold (𝓡 3) ∞ Q := finiteCapQuotient_isManifold hdim hL hδ f hf hdisj hs
  let ν := fun i => originalTubularMap (hδ i) (hδ1 i) (f i)
  let j := finiteCoreInclusion hL hδ f (fun i => (hf i).injective) hdisj
  let c := fun (b : ι × Bool) (x : Ball L) => finiteCapInclusion hL hδ f (fun i => (hf i).injective) hdisj ⟨b, x⟩
  let F := (finiteCapSelectedDiffeomorph I hdim hL hδ f hf hdisj R).symm
  let jRet := finiteRetainedCoreInclusion hL hδ f hf hdisj R
  let jDisc := finiteRetainedCoreInclusion hL hδ f hf hdisj Rᶜ
  have htop := finiteCapQuotient_topological_properties I hdim hL hδ f hf hdisj
  refine ⟨inferInstance,
    fun i => originalTubularMap_isSmoothEmbedding I hdim (hδ i) (hδ1 i) (f i) (hf i) (hs i),
    originalTubularMap_pairwise_disjoint hδ hδ1 f hdisj,
    cutCore_eq_originalTubularComplement hδ hδ1 f,
    isCompact_cutCore f hf,
    isCompact_retained_discardedCore hδ f hf hdisj R,
    cutCore_ambientInclusion_isSmoothEmbedding I hdim hδ f hf hdisj hs,
    retainedCore_ambientInclusion_isSmoothEmbedding I hdim hδ f hf hdisj R hs,
    retainedCore_ambientInclusion_isSmoothEmbedding I hdim hδ f hf hdisj Rᶜ hs,
    ⟨htop.1, htop.2.1, htop.2.2.1⟩,
    finiteCapSelected_closedManifold_properties I hdim hL hδ f hf hdisj hs R,
    ⟨ModelWithCorners.Boundaryless.boundary_eq_empty, ModelWithCorners.Boundaryless.boundary_eq_empty, ModelWithCorners.Boundaryless.boundary_eq_empty⟩,
    nativeCuttingSphereComponentsEquiv_apply I hdim hδ f hf hdisj hs,
    nativeCuttingSphereMap_connectedComponent I hdim hδ f hf hdisj hs,
    finiteCoreInclusion_isSmoothEmbedding I hdim hL hδ f hf hdisj hs,
    finiteCapInclusion_ball_isSmoothEmbedding I hdim hL hδ f hf hdisj hs,
    finiteRetainedCoreInclusion_isSmoothEmbedding I hdim hL hδ f hf hdisj hs R,
    finiteRetainedCoreInclusion_isSmoothEmbedding I hdim hL hδ f hf hdisj hs Rᶜ,
    ?cover,
    ?inter,
    ?native,
    finiteCap_ball_images_disjoint hL hδ f hf hdisj,
    nativeCoreBoundaryAttachingDiffeomorph_coherence I hdim hδ f hf hdisj hs hL,
    ?ret,
    ?disc,
    ?preimage,
    finiteCapRetained_component_meets_original_core hL hδ f hf hdisj R,
    finiteRetained_compl_interior_core hL hδ f hf hdisj R,
    finiteCapRetained_nonempty_iff_core hL hδ f hf hdisj R,
    hnontrivial.imp_right ((finiteCapRetained_nonempty_iff_core hL hδ f hf hdisj Rᶜ).mpr)⟩
  case cover =>
    ext q
    constructor
    · exact fun _ => mem_univ q
    · intro _
      have h := Set.ext_iff.mp (finiteCapQuotient_cover hL hδ f (fun i => (hf i).injective) hdisj) q
      rcases h.mpr (mem_univ q) with ⟨⟨b, x⟩, hx⟩ | hj
      · exact Or.inr (mem_iUnion.mpr ⟨b, ⟨x, hx⟩⟩)
      · exact Or.inl hj
  case inter =>
    intro b
    apply (finiteCap_core_inter_ball hL hδ f hf hdisj b).trans
    let D := nativeCuttingSphereDiffeomorph I hdim hδ f hf hdisj hs b
    ext q
    constructor
    · rintro ⟨y, rfl⟩
      exact ⟨D y, congrArg j (nativeCuttingSphereDiffeomorph_apply I hdim hδ f hf hdisj hs b y)⟩
    · rintro ⟨p, rfl⟩
      obtain ⟨y, rfl⟩ := D.surjective p
      exact ⟨y, (congrArg j (nativeCuttingSphereDiffeomorph_apply I hdim hδ f hf hdisj hs b y)).symm⟩
  case native =>
    intro b
    let φ := nativeCoreBoundaryAttachingDiffeomorph I hdim hδ f hf hdisj hs hL b
    ext q
    constructor
    · rintro ⟨p, rfl⟩
      obtain ⟨x, rfl⟩ := φ.surjective p
      exact ⟨x, nativeCoreBoundaryAttachingDiffeomorph_coherence I hdim hδ f hf hdisj hs hL b x⟩
    · rintro ⟨x, rfl⟩
      exact ⟨φ x, (nativeCoreBoundaryAttachingDiffeomorph_coherence I hdim hδ f hf hdisj hs hL b x).symm⟩
  case ret =>
    intro p
    exact finiteCapSelectedDiffeomorph_symm_retained I hdim hL hδ f hf hdisj R (j p.val) p.property
  case disc =>
    intro p
    exact finiteCapSelectedDiffeomorph_symm_discarded I hdim hL hδ f hf hdisj R (j p.val) p.property
  case preimage =>
    ext p
    constructor
    · intro hp
      exact ⟨jRet ⟨p, hp⟩, (finiteCapSelectedDiffeomorph_symm_retained I hdim hL hδ f hf hdisj R (j p) hp).symm⟩
    · rintro ⟨q, hq⟩
      have hv := congrArg F.symm hq
      change q.val = F.symm (F (j p)) at hv
      rw [F.symm_apply_apply] at hv
      have hr := q.property
      change q.val ∈ (finiteCapRetained hL hδ f hf hdisj R : Set Q) at hr
      rw [hv] at hr
      exact hr
end DifferentialGeometry.Topology.ThreeManifold.Surgery
