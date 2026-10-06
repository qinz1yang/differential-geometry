import DifferentialGeometry.Geometry.Collapse.LocalExport.BoundaryCutFactsOBD
import DifferentialGeometry.Geometry.Collapse.LocalExport.BoundaryStageGeometrySmoothOBD
import DifferentialGeometry.Geometry.Fibration.ActualStageChainEdgeRankTwoEFE

/-!
# `EdgeCutFacts74.cbase_domain` for the produced stages (lane S-BD2c)

Lane O-BD1 (by S-BD2c, suffix `_OBD`), group G8c (hlift, the cut facts `H`, `EdgeCutFacts74`,
third field). For ANY `P : BoundaryStageGeometry74b zc` with smooth edge inclusion:

* `mem_C₂_iff_OBD`: `c ∈ C₂ ⟺ ∀ ℓ, 0 ≤ h_ℓ (ι_edge c)` (`dec.edge.base_eq`);
* `faceFun_continuousAt_OBD`: `h_ℓ ∘ ι_edge` is continuous on the base (through the whole-fibre
  disk chart `dec.fibres.edge_chart`: `h_ℓ ∘ σ = (h_ℓ ∘ f₂) ∘ φ(·, 0)`);
* `exists_zero_label_OBD`: at a frontier point of `C₂` some label vanishes (finitely many labels);
* `edge_cbase_domain_OBD`: the local defining function `φ = h_ℓ ∘ ι_edge` of `C₂` at a frontier
  point (smoothness: `geom.edgeFacesSmooth` (G4s); regularity: `dec.edge.regular` through
  `d(proj)`; sign model: `dec.edge.local_single`).
-/

set_option autoImplicit false

noncomputable section

open Set Function Metric Bundle Manifold Filter Topology
open scoped ContDiff Manifold Topology ENNReal
open DifferentialGeometry.Topology.Ehresmann DifferentialGeometry.Topology.Manifold
open DifferentialGeometry.Geometry.Riemannian GC.MetricGeometry
open DifferentialGeometry GC.Endpoint DifferentialGeometry.Geometry.Hyperbolic
open DifferentialGeometry.Analysis DifferentialGeometry.Topology GC.GraphManifold
  GC.GraphManifold.Assembly GC.GraphManifold.Assembly.FC39P0

namespace DifferentialGeometry.Geometry.Collapse

local notation "E3" => EuclideanSpace ℝ (Fin 3)

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace

attribute [local instance] nezero_finrank_euclideanThree_LC87

attribute [local instance] interiorCharted_BDRY1 interiorManifold_BDRY1
  connectedSpace_interior_BDRY2

attribute [local instance] DifferentialGeometry.Topology.Handle.closedCellChartedSpaceSucc
  DifferentialGeometry.Topology.Handle.closedCellIsManifold

variable {K : ℕ} {A : ℝ → ℝ} {β : ℕ → ℝ}
  {βd εN Λ w Δ σs σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V vs ζ Λz θ : ℝ}
  {W : CompactCarrier.{0}} [ConnectedSpace W.Carrier] {g : SmoothRiemannianMetric W.model W.Carrier}
  {δn : ℝ} {n : ℕ} {B : NearlyCuspidalBoundary W g K δn}
  {oM : ManifoldOrientation 𝓘(ℝ, E3) (W.pieceInterior ⊤) 3}

section CbaseDomain

variable {S : BoundarySupply K A β βd εN Λ w Δ σs σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V vs ζ Λz
    θ W g δn n B oM} {Φ : BoundaryInteriorSlots_BIF S} {D : BoundaryAugmentedData S Φ}
  {Kj : ℕ} {Ξ Sg eg c cw : Fin 3 → ℝ} {bcut bder κ : ℝ}
  {C : BoundaryGaf02Chain D Kj Ξ Sg eg c cw bcut bder κ}
  {dec : BoundaryActualDecompositionV2b C} {zc : BoundaryZeroCuspExit74b C dec}
  (P : BoundaryStageGeometry74b zc)

/-- **The edge piece in terms of the face functions**: `c ∈ C₂ ⟺ ∀ ℓ, 0 ≤ h_ℓ (ι_edge c)`. -/
theorem BoundaryStageGeometry74b.mem_C₂_iff_OBD {P : BoundaryStageGeometry74b zc}
    {x : P.edge.Base} :
    x ∈ P.cut.C₂ ↔ ∀ ℓ, 0 ≤ dec.edge.faceFun ℓ (P.ιedge x) := by
  have h1 : P.ιedge '' P.cut.C₂ = {y ∈ dec.bases.base 1 | ∀ ℓ, 0 ≤ dec.edge.faceFun ℓ y} := by
    rw [P.cut_C₂]
    exact dec.edge.base_eq
  have hb : P.ιedge x ∈ dec.bases.base 1 := P.edge_range ⟨x, rfl⟩
  constructor
  · intro hc ℓ
    have : P.ιedge x ∈ P.ιedge '' P.cut.C₂ := ⟨x, hc, rfl⟩
    rw [h1] at this
    exact this.2 ℓ
  · intro h
    have : P.ιedge x ∈ P.ιedge '' P.cut.C₂ := by
      rw [h1]
      exact ⟨hb, h⟩
    obtain ⟨c', hc', hcc⟩ := this
    rw [← P.edge_ident.emb.injective hcc]
    exact hc'

/-- **The face functions are continuous along the edge base**: `h_ℓ ∘ ι_edge` is continuous at
every point of the edge base (the whole-fibre disk chart at the point, `h_ℓ ∘ σ = (h_ℓ ∘ f₂) ∘
φ(·, 0)`). -/
theorem BoundaryStageGeometry74b.faceFun_continuousAt_OBD
    (ℓ : dec.slim.EdgeFaceLabel_BIFc) (c : P.edge.Base) :
    ContinuousAt (fun c' : P.edge.Base => dec.edge.faceFun ℓ (P.ιedge c')) c := by
  have hy : P.ιedge c ∈ dec.bases.base 1 := P.edge_range ⟨c, rfl⟩
  obtain ⟨σ, φ, O, h0, -, hσe, -, hO, hrσ, hφ, hrange, hf, -⟩ := dec.fibres.edge_chart _ hy
  let w₀ : ClosedCell 2 := ⟨0, by simp⟩
  have hk : Continuous fun x : EuclideanSpace ℝ (Fin 1) => φ (x, w₀) :=
    hφ.contMDiff.continuous.comp (continuous_id.prodMk continuous_const)
  have hmem : ∀ x : EuclideanSpace ℝ (Fin 1), φ (x, w₀) ∈ dec.bases.source 1 := by
    intro x
    have : φ (x, w₀) ∈ range φ := mem_range_self _
    rw [hrange] at this
    exact this.1
  have hcont : Continuous fun x : EuclideanSpace ℝ (Fin 1) => dec.edge.faceFun ℓ (σ x) := by
    have h1 := (dec.edge.face_continuousOn ℓ).comp_continuous hk hmem
    convert h1 using 1
    funext x
    exact (congrArg (dec.edge.faceFun ℓ) (hf x w₀)).symm
  have hon : Continuous ((range σ).domRestrict (dec.edge.faceFun ℓ)) := by
    have : (range σ).domRestrict (dec.edge.faceFun ℓ) =
        (fun x => dec.edge.faceFun ℓ (σ x)) ∘ hσe.toHomeomorph.symm := by
      funext p
      have hp := hσe.toHomeomorph.apply_symm_apply p
      have hp' : σ (hσe.toHomeomorph.symm p) = p.1 := congrArg Subtype.val hp
      change dec.edge.faceFun ℓ p.1 = dec.edge.faceFun ℓ (σ (hσe.toHomeomorph.symm p))
      rw [hp']
    rw [this]
    exact hcont.comp hσe.toHomeomorph.symm.continuous
  have hN : IsOpen {c' : P.edge.Base | P.ιedge c' ∈ O} := hO.preimage P.edge_ident.emb.continuous
  have hcN : c ∈ {c' : P.edge.Base | P.ιedge c' ∈ O} := by
    have : P.ιedge c ∈ range σ := h0 ▸ mem_range_self 0
    rw [hrσ] at this
    exact this.2
  have hrg : ∀ c' : {c' : P.edge.Base | P.ιedge c' ∈ O}, P.ιedge c'.1 ∈ range σ := fun c' => by
    rw [hrσ]
    exact ⟨P.edge_range ⟨c'.1, rfl⟩, c'.2⟩
  have hg₁ : Continuous fun c' : {c' : P.edge.Base | P.ιedge c' ∈ O} =>
      (⟨P.ιedge c'.1, hrg c'⟩ : range σ) :=
    (P.edge_ident.emb.continuous.comp continuous_subtype_val).subtype_mk _
  have hcontN : ContinuousOn (fun c' : P.edge.Base => dec.edge.faceFun ℓ (P.ιedge c'))
      {c' : P.edge.Base | P.ιedge c' ∈ O} := by
    rw [continuousOn_iff_continuous_domRestrict]
    exact hon.comp hg₁
  exact hcontN.continuousAt (hN.mem_nhds hcN)

/-- **A label vanishes at every frontier point of `C₂`** (finitely many labels, continuity of the
face functions along the base, `mem_C₂_iff_OBD`). -/
theorem BoundaryStageGeometry74b.exists_zero_label_OBD
    (hS : IsCompact (Subtype.val ⁻¹' P.cut.C₂ : Set P.cut.edgeBaseOpen))
    {c : P.cut.edgeBaseOpen}
    (hc : c ∈ frontier (Subtype.val ⁻¹' P.cut.C₂ : Set P.cut.edgeBaseOpen)) :
    ∃ ℓ, dec.edge.faceFun ℓ (P.ιedge c.1) = 0 := by
  have hcS : c ∈ (Subtype.val ⁻¹' P.cut.C₂ : Set P.cut.edgeBaseOpen) :=
    hS.isClosed.frontier_subset hc
  have hmem := fun c' : P.edge.Base => BoundaryStageGeometry74b.mem_C₂_iff_OBD (P := P) (x := c')
  have hnn : ∀ ℓ, 0 ≤ dec.edge.faceFun ℓ (P.ιedge c.1) := (hmem c.1).1 hcS
  by_contra hne
  have hpos : ∀ ℓ, 0 < dec.edge.faceFun ℓ (P.ιedge c.1) := fun ℓ =>
    lt_of_le_of_ne (hnn ℓ) fun h => hne ⟨ℓ, h.symm⟩
  have hev : ∀ᶠ c' in 𝓝 c, ∀ ℓ, 0 < dec.edge.faceFun ℓ (P.ιedge c'.1) := by
    rw [Filter.eventually_all]
    intro ℓ
    have h1 : ContinuousAt (fun c' : P.cut.edgeBaseOpen =>
        dec.edge.faceFun ℓ (P.ιedge c'.1)) c :=
      (P.faceFun_continuousAt_OBD ℓ c.1).comp (f := Subtype.val) continuous_subtype_val.continuousAt
    exact h1.eventually (lt_mem_nhds (hpos ℓ))
  have hint : (Subtype.val ⁻¹' P.cut.C₂ : Set P.cut.edgeBaseOpen) ∈ 𝓝 c :=
    hev.mono fun c' h => (hmem c'.1).2 fun ℓ => (h ℓ).le
  exact hc.2 (mem_interior_iff_mem_nhds.2 hint)

/-- **The face function has a nonzero differential along the base at a zero**: `d(h_ℓ ∘ ι_edge)
≠ 0` at `c`, from `dec.edge.regular` at a point of the fibre and the chain rule through
`proj`. -/
theorem BoundaryStageGeometry74b.mfderiv_faceFun_ne_zero_OBD
    (ℓ : dec.slim.EdgeFaceLabel_BIFc) (c : P.cut.edgeBaseOpen)
    (hℓ : dec.edge.faceFun ℓ (P.ιedge c.1) = 0)
    (hdiff : MDifferentiableAt (𝓡 1) 𝓘(ℝ, ℝ)
      (fun c' : P.cut.edgeBaseOpen => dec.edge.faceFun ℓ (P.ιedge c'.1)) c) :
    mfderiv (𝓡 1) 𝓘(ℝ, ℝ)
      (fun c' : P.cut.edgeBaseOpen => dec.edge.faceFun ℓ (P.ιedge c'.1)) c ≠ 0 := by
  intro h0
  have hy : P.ιedge c.1 ∈ dec.bases.base 1 := P.edge_range ⟨c.1, rfl⟩
  obtain ⟨p, hp, hpf⟩ : ∃ p ∈ dec.bases.source 1, C.stageMap 1 p = P.ιedge c.1 := by
    rw [← dec.bases.image_eq 1] at hy
    exact hy
  have hpe : p ∈ dec.bases.edgeParent := by
    have := hp
    rw [dec.bases.parent.edgeParent_cut] at this
    exact this.1
  have hpar : p ∈ P.edge.parent := by
    rw [← SetLike.mem_coe, P.edge_ident.parent_eq]
    exact hpe
  have hproj : P.edge.proj ⟨p, hpar⟩ = c.1 := by
    refine P.edge_ident.emb.injective ?_
    rw [P.edge_ident.proj_eq ⟨p, hpar⟩]
    exact hpf
  let x₀ : P.edge.restrictParent P.cut.edgeBaseOpen :=
    ⟨p, P.edge.mem_restrictParent_of hpar (by rw [hproj]; exact c.2)⟩
  let Pj := P.stageGeometry.edge.restrictProj P.cut.edgeBaseOpen
  have hPx : Pj x₀ = c := Subtype.ext hproj
  have hzero : dec.edge.faceFun ℓ (C.stageMap 1 p) = 0 := by rw [hpf]; exact hℓ
  have hreg := dec.edge.regular ℓ p hp hzero
  have hsm := dec.edge.face_smooth ℓ p hp hzero
  have hPj : ContMDiff W.model (𝓡 1) ∞ Pj := P.stageGeometry.edge.restrictProj_smooth _
  have hlhs : mvfderiv W.model ((fun c' : P.cut.edgeBaseOpen =>
      dec.edge.faceFun ℓ (P.ιedge c'.1)) ∘ Pj) x₀ =
      mvfderiv W.model (fun q => dec.edge.faceFun ℓ (C.stageMap 1 q)) p :=
    mvfderiv_comp_subtype_val_EFE P.cut.edgeSource
      (f := fun q => dec.edge.faceFun ℓ (C.stageMap 1 q))
      (g := (fun c' : P.cut.edgeBaseOpen => dec.edge.faceFun ℓ (P.ιedge c'.1)) ∘ Pj)
      (fun z => congrArg (dec.edge.faceFun ℓ)
        (P.edge_ident.proj_eq (P.stageGeometry.edge.restrictIncl _ z))) x₀
      (hsm.mdifferentiableAt (by simp))
  have hchain := mvfderiv_comp_of_eq (x := x₀) hdiff (hPj.mdifferentiableAt (by simp)) hPx
  have h00 : mvfderiv (𝓡 1) (fun c' : P.cut.edgeBaseOpen =>
      dec.edge.faceFun ℓ (P.ιedge c'.1)) (Pj x₀) = 0 := by
    rw [hPx]
    unfold mvfderiv
    rw [h0]
    ext v
    simp
  have h1 : mvfderiv W.model ((fun c' : P.cut.edgeBaseOpen =>
      dec.edge.faceFun ℓ (P.ιedge c'.1)) ∘ Pj) x₀ = 0 := by
    rw [hchain, h00]
    ext v
    simp
  exact hreg (hlhs.symm.trans h1)

/-- **`EdgeCutFacts74.cbase_domain` for the produced stages**: at a frontier point of `C₂` in the
edge base, `C₂` is locally `{φ ≥ 0}` with `φ = h_ℓ ∘ ι_edge` smooth and regular. -/
theorem BoundaryStageGeometry74b.edge_cbase_domain_OBD
    (hι : ContMDiff (𝓡 1) 𝓘(ℝ, BoundaryAmbient_BIF S.IntTag_BAUGA (Fin S.packet.cusp.count)) ∞
      P.ιedge)
    (hS : IsCompact (Subtype.val ⁻¹' P.cut.C₂ : Set P.cut.edgeBaseOpen))
    (geom : BoundaryGeometricExports74b C dec) :
    ∀ c ∈ frontier (Subtype.val ⁻¹' P.cut.C₂ : Set P.cut.edgeBaseOpen),
      ∃ U : TopologicalSpace.Opens P.cut.edgeBaseOpen, c ∈ U ∧
        ∃ φ : P.cut.edgeBaseOpen → ℝ, ContMDiffOn (𝓡 1) 𝓘(ℝ, ℝ) ∞ φ U ∧ φ c = 0 ∧
          mfderiv (𝓡 1) 𝓘(ℝ, ℝ) φ c ≠ 0 ∧
          (Subtype.val ⁻¹' P.cut.C₂ : Set P.cut.edgeBaseOpen) ∩ U = {c' | c' ∈ U ∧ 0 ≤ φ c'} := by
  intro c hc
  have hmem := fun c' : P.edge.Base => BoundaryStageGeometry74b.mem_C₂_iff_OBD (P := P) (x := c')
  obtain ⟨ℓ, hℓ⟩ := P.exists_zero_label_OBD hS hc
  have hcS : c ∈ (Subtype.val ⁻¹' P.cut.C₂ : Set P.cut.edgeBaseOpen) :=
    hS.isClosed.frontier_subset hc
  have hy : P.ιedge c.1 ∈ dec.bases.base 1 := P.edge_range ⟨c.1, rfl⟩
  have hyPiece : P.ιedge c.1 ∈ C.stageMap 1 '' (dec.slim.M₂ ∩ dec.bases.source 1) := by
    have : P.ιedge c.1 ∈ P.ιedge '' P.cut.C₂ := ⟨c.1, hcS, rfl⟩
    rw [P.cut_C₂] at this
    exact this
  obtain ⟨O₁, hO₁, hyO₁, hloc⟩ := dec.edge.local_single _ hyPiece ℓ hℓ
  obtain ⟨O₂, hO₂, hyO₂, hsm⟩ := geom.edgeFacesSmooth ℓ _ hy hℓ
  let ιV : P.cut.edgeBaseOpen → BoundaryAmbient_BIF S.IntTag_BAUGA (Fin S.packet.cusp.count) :=
    fun c' => P.ιedge c'.1
  have hιV : ContMDiff (𝓡 1) 𝓘(ℝ, BoundaryAmbient_BIF S.IntTag_BAUGA
      (Fin S.packet.cusp.count)) ∞ ιV :=
    hι.comp (contMDiff_subtype_val (I := 𝓡 1) (U := P.cut.edgeBaseOpen))
  let U : TopologicalSpace.Opens P.cut.edgeBaseOpen :=
    ⟨ιV ⁻¹' (O₁ ∩ O₂), (hO₁.inter hO₂).preimage hιV.continuous⟩
  have hφU : ContMDiffOn (𝓡 1) 𝓘(ℝ, ℝ) ∞
      (fun c' : P.cut.edgeBaseOpen => dec.edge.faceFun ℓ (P.ιedge c'.1)) U :=
    (hsm.contMDiffOn).comp hιV.contMDiffOn (fun c' hc' => hc'.2)
  have hcU : c ∈ U := ⟨hyO₁, hyO₂⟩
  refine ⟨U, hcU, fun c' => dec.edge.faceFun ℓ (P.ιedge c'.1), hφU, hℓ, ?_, ?_⟩
  · exact P.mfderiv_faceFun_ne_zero_OBD ℓ c hℓ
      ((hφU.contMDiffAt (U.isOpen.mem_nhds hcU)).mdifferentiableAt (by simp))
  · ext c'
    constructor
    · rintro ⟨hc'S, hc'U⟩
      exact ⟨hc'U, (hmem c'.1).1 hc'S ℓ⟩
    · rintro ⟨hc'U, hnn⟩
      refine ⟨(hmem c'.1).2 fun ℓ' => ?_, hc'U⟩
      by_cases h : ℓ' = ℓ
      · subst h
        exact hnn
      · exact (hloc ℓ' h _ ⟨hc'U.1, P.edge_range ⟨c'.1, rfl⟩⟩).le

end CbaseDomain

end DifferentialGeometry.Geometry.Collapse
