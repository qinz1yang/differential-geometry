import DifferentialGeometry.Geometry.Collapse.LocalExport.BoundaryZeroDomainHderBGR
import DifferentialGeometry.Geometry.Collapse.LocalExport.BoundaryPacketsBFRZFaceStandardOCX
import DifferentialGeometry.Topology.Embedding.CrossModelPartialOCX
import DifferentialGeometry.Topology.Embedding.Diffeomorph

/-!
# BCG07 `face_param`: the standard smooth parametrization of the actual zero faces
(lane O-CROSS, G4)

The field `face_param` of `BoundaryActualZeroDomains_BIFc` asks, for every zero index `k`, a smooth
embedding `S² = ClosureSphere → W` (model `𝓡 2`) or `T² = Circle × Circle → W` (model
`(𝓡 1).prod (𝓡 1)`) onto the actual zero face of `C.E`. Route:

1. the interior family (`S.family`, complete metric `ĝ` on `W°`, interior atlas `𝓘(ℝ, ℝ³)`) gives
   the original face `{radial_k = 2/5}` as the image of a smooth embedding `e₀` into `W°`
   (`LocalPacketsOnBFRZ.zero_face_standard_param_OCX`); the compact-model alternative is
   impossible since `W°` is not compact (`not_compactSpace_pieceInterior_top_OCX`: a cusp boundary
   point exists and `W` is connected);
2. the inclusion `W° → W` is the partial diffeomorphism `interiorInclusion_BDRY1` (model
   `𝓡 3 → W.model`), and `val ∘ e₀` is a smooth embedding into `W` for both carrier kinds
   (`isImmersion_carrier_partialDiffeomorph_comp_OCX`: same model, or the half-space kernel of
   O-CROSS G1/G4);
3. the transport `Ψ` of ZSP02 (`zsp02_transport_BGR`, ONE ambient diffeomorphism of `W`) carries
   `val '' {radial_k = 2/5}` onto the actual face; `Ψ ∘ val ∘ e₀` is the parametrization.

* **`BoundaryGaf02ChainE.face_param_OCX`** (premise `εr < 1/2`, as the `transport` field) — the
  field `face_param` verbatim.
-/

set_option autoImplicit false

noncomputable section

open Set Function Metric Bundle Manifold Filter
open scoped ContDiff Manifold Topology ENNReal
open DifferentialGeometry.Topology.Ehresmann DifferentialGeometry.Topology.Manifold
open DifferentialGeometry.Geometry.Riemannian GC.MetricGeometry
open DifferentialGeometry GC.Endpoint DifferentialGeometry.Geometry.Hyperbolic
open DifferentialGeometry.Analysis

namespace DifferentialGeometry.Geometry.Collapse

local notation "E3" => EuclideanSpace ℝ (Fin 3)

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace

attribute [local instance] nezero_finrank_euclideanThree_LC87

universe u

/-- **An immersion into an `𝓘(ℝ, ℝ³)`-manifold followed by a partial diffeomorphism into a carrier
of either kind** is an immersion (`closed`: one model; `withBoundary`: half-space kernel; the
source model needs one nonzero range-preserving translation `s₀`). -/
theorem isImmersion_carrier_partialDiffeomorph_comp_OCX {W : CompactCarrier.{u}}
    {EQ HQ : Type*} [NormedAddCommGroup EQ] [NormedSpace ℝ EQ] [TopologicalSpace HQ]
    {IQ : ModelWithCorners ℝ EQ HQ} {Q : Type*} [TopologicalSpace Q] [ChartedSpace HQ Q]
    [IsManifold IQ ∞ Q] (s₀ : EQ) (hs₀ : s₀ ≠ 0) (hs₀I : ∀ v, v + s₀ ∈ range IQ ↔ v ∈ range IQ)
    {N₀ : Type*} [TopologicalSpace N₀] [ChartedSpace E3 N₀]
    (Θ : PartialDiffeomorph (𝓡 3) W.model N₀ W.Carrier ∞) {f : Q → N₀}
    (hf : IsImmersion IQ (𝓡 3) ∞ f) (hsrc : ∀ y, f y ∈ Θ.source) :
    IsImmersion IQ W.model ∞ (Θ ∘ f) := by
  cases W with
  | mk k M o =>
    cases k
    · exact hf.partialDiffeomorph_comp_OCX Θ hsrc
    · exact hf.partialDiffeomorph_comp_toHalfSpace_OCX s₀ hs₀ hs₀I Θ hsrc

/-- **The interior of a connected carrier with a boundary point is not compact.** -/
theorem not_compactSpace_pieceInterior_top_OCX {W : CompactCarrier.{u}}
    [ConnectedSpace W.Carrier] (x₀ : W.pieceInterior ⊤) {y : W.Carrier}
    (hy : W.model.IsBoundaryPoint y) : ¬ CompactSpace (W.pieceInterior ⊤) := by
  intro hc
  have hK : IsCompact ((W.pieceInterior ⊤ : TopologicalSpace.Opens W.Carrier) : Set W.Carrier) :=
    isCompact_iff_compactSpace.mpr hc
  have hclopen : IsClopen ((W.pieceInterior ⊤ : TopologicalSpace.Opens W.Carrier) :
      Set W.Carrier) := ⟨hK.isClosed, (W.pieceInterior ⊤).isOpen⟩
  have huniv := hclopen.eq_univ ⟨x₀.1, x₀.2⟩
  have hyI : y ∈ W.model.interior W.Carrier := by
    rw [← coe_pieceInterior_top_BDRY1 W, huniv]
    exact mem_univ y
  exact ((W.model.isInteriorPoint_iff_not_isBoundaryPoint y).mp hyI) hy

attribute [local instance] interiorCharted_BDRY1 interiorManifold_BDRY1
  connectedSpace_interior_BDRY2

variable {K : ℕ} {A : ℝ → ℝ} {β : ℕ → ℝ}
  {βd εN Λ w Δ σs σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V vs ζ Λz θ : ℝ}
  {W : CompactCarrier.{0}} [ConnectedSpace W.Carrier] {g : SmoothRiemannianMetric W.model W.Carrier}
  {δn : ℝ} {n : ℕ} {B : NearlyCuspidalBoundary W g K δn}
  {oM : ManifoldOrientation 𝓘(ℝ, E3) (W.pieceInterior ⊤) 3}

/-- **The inclusion of the interior, composed with a smooth embedding into `W°`**, is a smooth
embedding into `W` (interior atlas on `W°`, either kind of carrier). -/
theorem isSmoothEmbedding_val_comp_OCX {EQ HQ : Type*} [NormedAddCommGroup EQ]
    [NormedSpace ℝ EQ] [TopologicalSpace HQ] {IQ : ModelWithCorners ℝ EQ HQ} {Q : Type*}
    [TopologicalSpace Q] [ChartedSpace HQ Q] [IsManifold IQ ∞ Q] (s₀ : EQ) (hs₀ : s₀ ≠ 0)
    (hs₀I : ∀ v, v + s₀ ∈ range IQ ↔ v ∈ range IQ) {f : Q → W.pieceInterior ⊤}
    (hf : IsSmoothEmbedding IQ (𝓡 3) ∞ f) :
    IsSmoothEmbedding IQ W.model ∞ (Subtype.val ∘ f) :=
  ⟨isImmersion_carrier_partialDiffeomorph_comp_OCX s₀ hs₀ hs₀I (interiorInclusion_BDRY1 W)
      hf.isImmersion (fun _ => trivial),
    Topology.IsEmbedding.subtypeVal.comp hf.isEmbedding⟩

namespace BoundaryGaf02ChainE

variable {S : BoundarySupply K A β βd εN Λ w Δ σs σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V vs ζ
  Λz θ W g δn n B oM} {Γ Sg eg : Fin 3 → ℝ}
  {DP : BoundaryAugmentedDataPV3 S (actualSlotsV2_BAUGD S) Γ Sg eg} {Kj : ℕ}
  {Ξ c cw : Fin 3 → ℝ} {bcut bder κ cadj : ℝ}
  (C : BoundaryGaf02ChainE DP Kj Ξ c cw bcut bder κ cadj)

/-- **BCG07 `face_param`** (the STANDARD smooth face type, review 70 D70-5): for every zero index
`k`, the actual zero face of `C.E` is the image of a smooth embedding of `S²` (model `𝓡 2`) or of
`T²` (model `(𝓡 1).prod (𝓡 1)`) into `W`. Premise `εr < 1/2` (that of the `transport` field). -/
theorem face_param_OCX (hεr : εr < 1 / 2) (k : S.ZeroIdx_BAUGC) :
    (∃ e : GC.GraphManifold.ClosureSphere.{0} → W.Carrier,
        IsSmoothEmbedding (𝓡 2) W.model ∞ e ∧ range e = C.toChain.actualZeroFace_BIFc k) ∨
      ∃ e : Circle × Circle → W.Carrier, IsSmoothEmbedding ((𝓡 1).prod (𝓡 1)) W.model ∞ e ∧
        range e = C.toChain.actualZeroFace_BIFc k := by
  obtain ⟨Ψ, -, hΨ⟩ := C.zsp02_transport_BGR hεr k
  rw [← hΨ]
  have hstd : CompactSpace (W.pieceInterior ⊤) ∨
      (∃ e₀ : GC.GraphManifold.ClosureSphere.{0} → W.pieceInterior ⊤,
        IsSmoothEmbedding (𝓡 2) (𝓡 3) ∞ e₀ ∧ range e₀ = {q | S.zeroRadial_BIFc k q = 2 / 5}) ∨
      (∃ e₀ : Torus → W.pieceInterior ⊤, IsSmoothEmbedding torusModel (𝓡 3) ∞ e₀ ∧
        range e₀ = {q | S.zeroRadial_BIFc k q = 2 / 5}) := by
    let _ := inducedMetricSpace S.completion.metric
    let _ := S.completion.complete
    let _ := S.family.instMetricN
    let _ := S.family.instChartedN
    let _ := S.family.instMetricC
    exact S.family.zero_face_standard_param_OCX ((Set.Finite.mem_toFinset _).mp k.2)
      ⟨by norm_num, by norm_num⟩
  obtain ⟨-, -, -, hbd⟩ := (S.packet.cusp.collar ⟨0, S.packet.cusp.count_pos⟩).boundary_param
  rcases hstd with hc | ⟨e₀, he₀, hr₀⟩ | ⟨e₀, he₀, hr₀⟩
  · exact absurd hc (not_compactSpace_pieceInterior_top_OCX k.1 (hbd (1, 1)))
  · have hs : (EuclideanSpace.single 0 1 : EuclideanSpace ℝ (Fin 2)) ≠ 0 := by
      intro h
      have h1 := congrArg (fun v : EuclideanSpace ℝ (Fin 2) => v 0) h
      simp at h1
    refine Or.inl ⟨Ψ ∘ (Subtype.val ∘ e₀), ?_, ?_⟩
    · exact (isSmoothEmbedding_val_comp_OCX _ hs
        (fun _ => modelWithCornersSelf_shift_range_OCX _) he₀).diffeomorph_comp Ψ
    · rw [range_comp, range_comp, hr₀]
  · have hs : ((EuclideanSpace.single 0 1, 0) :
        EuclideanSpace ℝ (Fin 1) × EuclideanSpace ℝ (Fin 1)) ≠ 0 := by
      intro h
      have h1 := congrArg (fun v : EuclideanSpace ℝ (Fin 1) × EuclideanSpace ℝ (Fin 1) =>
        v.1 0) h
      simp at h1
    have hsI : ∀ v : EuclideanSpace ℝ (Fin 1) × EuclideanSpace ℝ (Fin 1),
        v + (EuclideanSpace.single 0 1, 0) ∈ range torusModel ↔ v ∈ range torusModel := by
      intro v
      rw [ModelWithCorners.range_prod]
      simp
    refine Or.inr ⟨Ψ ∘ (Subtype.val ∘ e₀), ?_, ?_⟩
    · exact (isSmoothEmbedding_val_comp_OCX _ hs hsI he₀).diffeomorph_comp Ψ
    · rw [range_comp, range_comp, hr₀]

end BoundaryGaf02ChainE

end DifferentialGeometry.Geometry.Collapse
