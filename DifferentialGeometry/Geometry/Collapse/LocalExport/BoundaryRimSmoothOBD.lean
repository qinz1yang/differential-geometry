import DifferentialGeometry.Geometry.Collapse.LocalExport.BoundaryRimBaseOBD
import DifferentialGeometry.Geometry.Collapse.LocalExport.BoundaryStageGeometryEmbeddedOBD
import DifferentialGeometry.Topology.Manifold.ImmersionCriterion

/-!
# The rim base is smooth (lane S-BD2c)

Lane O-BD1 (by S-BD2c, suffix `_OBD`), group G11a (hlift, `JunctionRimFacts74.rimBase_smooth`).
For the produced stages with embedded base inclusions (G7f), every map `rimBase` with
`rim c = fibre (rimBase c)` on `C₂` is smooth on `C₂`:

* `contMDiffAt_invFun_comp_OBD`: a map into a manifold that is smooth after composition with a
  smooth embedding `σ` and takes values in the range of `σ` near `x₀` is smooth at `x₀` (through
  `Function.invFun σ`; `ContMDiffAt.iff_comp_isImmersionAt`);
* `isSmoothEmbedding_of_fderiv_inj_OBD`: a smooth topological embedding of finite-dimensional
  vector spaces with injective differentials is a smooth embedding;
* `rimBase_contMDiffOn_OBD`: the rim point section `x ↦ φ(x, w₁)` of the disk chart at the point,
  `κ = σ⁻¹ ∘ ι_edge` (smooth through the chart embedding `σ`), and `ι_circle⁻¹ ∘ f₀ ∘ section ∘ κ`
  (smooth through the embedding `ι_circle`).
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


/-- A smooth map into a manifold factors smoothly through a smooth embedding (local form). -/
theorem contMDiffAt_invFun_comp_OBD {𝕜 : Type*} [RCLike 𝕜] {EM EY EZ : Type*}
    [NormedAddCommGroup EM] [NormedSpace 𝕜 EM] [NormedAddCommGroup EY] [NormedSpace 𝕜 EY]
    [NormedAddCommGroup EZ] [NormedSpace 𝕜 EZ] {HM HY HZ : Type*} [TopologicalSpace HM]
    [TopologicalSpace HY] [TopologicalSpace HZ] {I : ModelWithCorners 𝕜 EM HM}
    {J : ModelWithCorners 𝕜 EY HY} {J' : ModelWithCorners 𝕜 EZ HZ} {M Y Z : Type*}
    [TopologicalSpace M] [ChartedSpace HM M] [TopologicalSpace Y] [ChartedSpace HY Y]
    [TopologicalSpace Z] [ChartedSpace HZ Z] [Nonempty Y] {σ : Y → Z}
    (hσ : IsSmoothEmbedding J J' ∞ σ) {f : M → Z} {x₀ : M} (hf : ContMDiffAt I J' ∞ f x₀)
    (hev : ∀ᶠ x in 𝓝 x₀, f x ∈ range σ) :
    ContMDiffAt I J ∞ (fun x => Function.invFun σ (f x)) x₀ := by
  have heq : (σ ∘ fun x => Function.invFun σ (f x)) =ᶠ[𝓝 x₀] f := by
    filter_upwards [hev] with x hx
    exact Function.invFun_eq hx
  have hcont : ContinuousAt (fun x => Function.invFun σ (f x)) x₀ := by
    rw [hσ.isEmbedding.isInducing.continuousAt_iff]
    exact hf.continuousAt.congr_of_eventuallyEq heq
  exact (ContMDiffAt.iff_comp_isImmersionAt (hσ.isImmersion.isImmersionAt _)).2
    ⟨hcont, hf.congr_of_eventuallyEq heq⟩

/-- A smooth injective-differential embedding of finite-dimensional vector spaces. -/
theorem isSmoothEmbedding_of_fderiv_inj_OBD {E F : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [FiniteDimensional ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F]
    [FiniteDimensional ℝ F] {σ : E → F} (hs : ContDiff ℝ ∞ σ) (he : IsEmbedding σ)
    (hi : ∀ x, Injective (fderiv ℝ σ x)) : IsSmoothEmbedding 𝓘(ℝ, E) 𝓘(ℝ, F) ∞ σ :=
  ⟨DifferentialGeometry.Topology.Manifold.isImmersion_of_injective_mfderiv (by simp)
    hs.contMDiff (fun x => by
      have : mfderiv 𝓘(ℝ, E) 𝓘(ℝ, F) σ x =
          (NormedSpace.fromTangentSpace (σ x)).symm.toContinuousLinearMap ∘L
            (fderiv ℝ σ x) ∘L (NormedSpace.fromTangentSpace x).toContinuousLinearMap :=
        mfderiv_eq_fderiv
      rw [this]
      exact (NormedSpace.fromTangentSpace (σ x)).symm.injective.comp
        ((hi x).comp (NormedSpace.fromTangentSpace x).injective)), he⟩

section RimSmooth

variable {S : BoundarySupply K A β βd εN Λ w Δ σs σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V vs ζ Λz
    θ W g δn n B oM} {Γ Sg eg : Fin 3 → ℝ}
  {DP : BoundaryAugmentedDataPV3 S (actualSlotsV2_BAUGD S) Γ Sg eg} {Kj : ℕ}
  {Ξ c cw : Fin 3 → ℝ} {bcut bder κ cadj : ℝ}

namespace BoundaryGaf02ChainE

variable (C : BoundaryGaf02ChainE DP Kj Ξ c cw bcut bder κ cadj)
  {dec : BoundaryActualDecompositionV2b C.toChain} {zc : BoundaryZeroCuspExit74b C.toChain dec}
  (P : BoundaryStageGeometry74b zc)

include C in
/-- A point of the level `≤ 4Δ` over the edge base lies in the edge parent. -/
theorem edge_parent_of_OBD {y : W.Carrier}
    (hy : C.toChain.stageMap 1 y ∈ P.ιedge '' ((P.cut.edgeBaseOpen : Set P.edge.Base)))
    (hT : C.toChain.heightRatio y ≤ 4 * Δ) : y ∈ P.edge.parent := by
  have hS : y ∈ dec.bases.source 1 := by
    rw [dec.bases.edge_source_eq]
    refine ⟨?_, hT⟩
    obtain ⟨c', -, hc'⟩ := hy
    rw [mem_preimage, ← hc']
    exact P.edge_range ⟨c', rfl⟩
  rw [dec.bases.parent.edgeParent_cut] at hS
  rw [← SetLike.mem_coe, P.edge_ident.parent_eq]
  exact hS.1

include C in
/-- A point over the circle base lies in the circle parent. -/
theorem circle_parent_of_OBD {y : W.Carrier}
    (hy : C.toChain.stageMap 0 y ∈ range P.ιcircle) : y ∈ P.circle.parent := by
  obtain ⟨b, hb⟩ := hy
  have hS : y ∈ dec.bases.source 0 := by
    rw [dec.bases.circle_source_eq, mem_preimage, ← hb]
    exact P.circle_range ⟨b, rfl⟩
  rw [← SetLike.mem_coe, P.circle_ident.parent_eq]
  exact hS

include C in
/-- The circle base is the range of `ι_circle`. -/
theorem base_zero_subset_range_OBD : dec.bases.base 0 ⊆ range P.ιcircle := by
  intro z hz
  rw [← dec.bases.image_eq 0] at hz
  obtain ⟨p, hp, rfl⟩ := hz
  have hpar : p ∈ P.circle.parent := by
    rw [← SetLike.mem_coe, P.circle_ident.parent_eq]
    exact hp
  exact ⟨P.circle.proj ⟨p, hpar⟩, P.circle_ident.proj_eq ⟨p, hpar⟩⟩

include C in
/-- The rim of the restricted edge bundle as a set of `W`. -/
theorem edgeRim_set_OBD (F : EdgeCutFacts74 P.stageGeometry P.cut) (c' : P.cut.edgeBaseOpen) :
    (edgeBundle74 P.stageGeometry P.cut F).rim c' =
      {y | C.toChain.stageMap 1 y = P.ιedge c'.1 ∧
        C.toChain.heightRatio y = P.stageGeometry.edge.level} := by
  have h := edgeBundle74_rim_eq_JN74 P.cut (Equiv.refl W.Carrier) (C.toChain.stageMap 1)
    P.ιedge C.toChain.heightRatio F (fun x => P.edge_ident.proj_eq x)
    P.edge_ident.emb.injective
    (fun y hy hT => C.edge_parent_of_OBD P hy (by
      have : P.stageGeometry.edge.level = 4 * Δ := P.edge_level
      rw [← this]
      exact hT))
    (fun x => P.edge_height x) c'
  rw [h]
  simp

include C in
/-- The circle fibre of the restricted circle bundle as a set of `W`. -/
theorem circleFibre_set_OBD (G : CircleCutFacts74 P.stageGeometry P.cut)
    (b' : P.cut.circleBaseOpen) :
    (circleBundle74 P.stageGeometry P.cut G).fibre b' =
      {y | C.toChain.stageMap 0 y = P.ιcircle b'.1} := by
  have h := circleBundle74_fibre_eq_JN74 P.cut (Equiv.refl W.Carrier) (C.toChain.stageMap 0)
    P.ιcircle G (fun x => P.circle_ident.proj_eq x) P.circle_ident.emb.injective
    (fun y hy => C.circle_parent_of_OBD P hy) b'
  rw [h]
  ext y
  simp

include C in
/-- **The rim base is smooth on `C₂`** (`rimBase_smooth` of `JunctionRimFacts74`): every map
`rimBase` of the edge base into the circle base with `rim c = fibre (rimBase c)` on `C₂` is smooth
on `C₂`. -/
theorem rimBase_contMDiffOn_OBD (geom : BoundaryGeometricExports74b C.toChain dec)
    (F : EdgeCutFacts74 P.stageGeometry P.cut) (G : CircleCutFacts74 P.stageGeometry P.cut)
    (hιe : ContMDiff (𝓡 1) 𝓘(ℝ, BoundaryAmbient_BIF S.IntTag_BAUGA (Fin S.packet.cusp.count)) ∞
      P.ιedge)
    (hιc : IsSmoothEmbedding (𝓡 2) 𝓘(ℝ, BoundaryAmbient_BIF S.IntTag_BAUGA
      (Fin S.packet.cusp.count)) ∞ P.ιcircle)
    (rimBase : (edgeBundle74 P.stageGeometry P.cut F).Base →
      (circleBundle74 P.stageGeometry P.cut G).Base)
    (hrim : ∀ c' ∈ (edgeBundle74 P.stageGeometry P.cut F).cbase,
      (edgeBundle74 P.stageGeometry P.cut F).rim c' =
        (circleBundle74 P.stageGeometry P.cut G).fibre (rimBase c')) :
    ContMDiffOn (𝓡 1) (𝓡 2) ∞ rimBase (edgeBundle74 P.stageGeometry P.cut F).cbase := by
  intro c₀ hc₀
  have hlev : P.stageGeometry.edge.level = 4 * Δ := P.edge_level
  have hy₀ : P.ιedge c₀.1 ∈ dec.bases.base 1 := P.edge_range ⟨c₀.1, rfl⟩
  obtain ⟨σ, φ, O, h0, hσs, hσe, hσi, hO, hrσ, hφ, hrange, hf, hT⟩ :=
    dec.fibres.edge_chart _ hy₀
  have hσemb : IsSmoothEmbedding (𝓡 1) 𝓘(ℝ, BoundaryAmbient_BIF S.IntTag_BAUGA
      (Fin S.packet.cusp.count)) ∞ σ := isSmoothEmbedding_of_fderiv_inj_OBD hσs hσe hσi
  have : Nonempty P.circle.Base := ⟨(rimBase c₀).1⟩
  let w₁ : ClosedCell 2 := ⟨EuclideanSpace.single 0 1, by simp⟩
  -- the rim point section
  have hsecS : ∀ x, φ (x, w₁) ∈ dec.bases.source 1 := by
    intro x
    have : φ (x, w₁) ∈ range φ := mem_range_self _
    rw [hrange] at this
    exact this.1
  have hsecT : ∀ x, C.toChain.heightRatio (φ (x, w₁)) = 4 * Δ := fun x =>
    (hT x w₁).2 (by simp [w₁])
  have hsec0 : ∀ x, φ (x, w₁) ∈ dec.bases.source 0 := by
    intro x
    have hb : σ x ∈ dec.bases.base 1 := by
      have : σ x ∈ range σ := mem_range_self x
      rw [hrσ] at this
      exact this.1
    exact (geom.diskRim _ hb (φ (x, w₁)) ⟨hsecS x, hf x w₁⟩ (hsecT x)).1
  have hg : ContMDiff (𝓡 1) 𝓘(ℝ, BoundaryAmbient_BIF S.IntTag_BAUGA
      (Fin S.packet.cusp.count)) ∞ (fun x => C.toChain.stageMap 0 (φ (x, w₁))) :=
    (C.contMDiff_stageMap_OBD 0).comp
      (hφ.contMDiff.comp (contMDiff_id.prodMk contMDiff_const))
  -- the chart coordinate of the edge base near `c₀`
  let ιV : P.cut.edgeBaseOpen → BoundaryAmbient_BIF S.IntTag_BAUGA (Fin S.packet.cusp.count) :=
    fun c' => P.ιedge c'.1
  have hιV : ContMDiff (𝓡 1) 𝓘(ℝ, BoundaryAmbient_BIF S.IntTag_BAUGA
      (Fin S.packet.cusp.count)) ∞ ιV :=
    hιe.comp (contMDiff_subtype_val (I := 𝓡 1) (U := P.cut.edgeBaseOpen))
  have hN : ∀ᶠ c' in 𝓝 c₀, ιV c' ∈ range σ := by
    have h0O : ιV c₀ ∈ O := by
      have : ιV c₀ ∈ range σ := ⟨0, h0⟩
      rw [hrσ] at this
      exact this.2
    filter_upwards [(hO.preimage hιV.continuous).mem_nhds h0O] with c' hc'
    rw [hrσ]
    exact ⟨P.edge_range ⟨c'.1, rfl⟩, hc'⟩
  have hκ : ContMDiffAt (𝓡 1) (𝓡 1) ∞ (fun c' => Function.invFun σ (ιV c')) c₀ :=
    contMDiffAt_invFun_comp_OBD hσemb hιV.contMDiffAt hN
  have hĜ : ContMDiffAt (𝓡 1) 𝓘(ℝ, BoundaryAmbient_BIF S.IntTag_BAUGA
      (Fin S.packet.cusp.count)) ∞
      (fun c' => C.toChain.stageMap 0 (φ (Function.invFun σ (ιV c'), w₁))) c₀ :=
    hg.contMDiffAt.comp c₀ hκ
  have hev2 : ∀ᶠ c' in 𝓝 c₀, C.toChain.stageMap 0 (φ (Function.invFun σ (ιV c'), w₁)) ∈
      range P.ιcircle := by
    filter_upwards with c'
    apply C.base_zero_subset_range_OBD P
    rw [← dec.bases.image_eq 0]
    exact ⟨_, hsec0 _, rfl⟩
  have hR : ContMDiffAt (𝓡 1) (𝓡 2) ∞ (fun c' => Function.invFun P.ιcircle
      (C.toChain.stageMap 0 (φ (Function.invFun σ (ιV c'), w₁)))) c₀ :=
    contMDiffAt_invFun_comp_OBD hιc hĜ hev2
  -- agreement with `rimBase` on `C₂` near `c₀`
  have hagree : ∀ᶠ c' in 𝓝[(edgeBundle74 P.stageGeometry P.cut F).cbase] c₀,
      Function.invFun P.ιcircle
        (C.toChain.stageMap 0 (φ (Function.invFun σ (ιV c'), w₁))) = (rimBase c').1 := by
    have hmem : ∀ᶠ c' in 𝓝[(edgeBundle74 P.stageGeometry P.cut F).cbase] c₀,
        c' ∈ (edgeBundle74 P.stageGeometry P.cut F).cbase ∧ ιV c' ∈ range σ :=
      (hN.filter_mono nhdsWithin_le_nhds).and self_mem_nhdsWithin |>.mono fun c' h => ⟨h.2, h.1⟩
    filter_upwards [hmem] with c' ⟨hc', hr'⟩
    have hs : C.toChain.stageMap 1 (φ (Function.invFun σ (ιV c'), w₁)) = P.ιedge c'.1 := by
      rw [hf]
      exact Function.invFun_eq hr'
    have hsrim : φ (Function.invFun σ (ιV c'), w₁) ∈
        (edgeBundle74 P.stageGeometry P.cut F).rim c' := by
      rw [C.edgeRim_set_OBD P F c']
      exact ⟨hs, by rw [hlev]; exact hsecT _⟩
    have hsfib := hrim c' hc' ▸ hsrim
    have hf0 : C.toChain.stageMap 0 (φ (Function.invFun σ (ιV c'), w₁)) =
        P.ιcircle (rimBase c').1 := (C.circleFibre_set_OBD P G (rimBase c')).subset hsfib
    rw [hf0]
    exact Function.leftInverse_invFun hιc.isEmbedding.injective _
  have hR' : ContMDiffWithinAt (𝓡 1) (𝓡 2) ∞ (fun c' : P.cut.edgeBaseOpen =>
      Function.invFun P.ιcircle
        (C.toChain.stageMap 0 (φ (Function.invFun σ (ιV c'), w₁))))
      (edgeBundle74 P.stageGeometry P.cut F).cbase c₀ := hR.contMDiffWithinAt
  have hfin : ContMDiffWithinAt (𝓡 1) (𝓡 2) ∞ (fun c' : P.cut.edgeBaseOpen => (rimBase c').1)
      (edgeBundle74 P.stageGeometry P.cut F).cbase c₀ :=
    hR'.congr_of_eventuallyEq (hagree.mono fun c' h => h.symm)
      (hagree.self_of_nhdsWithin hc₀).symm
  exact (ContMDiffWithinAt.subtypeVal_comp_iff P.cut.circleBaseOpen rimBase _ c₀).1 hfin

end BoundaryGaf02ChainE

end RimSmooth

end DifferentialGeometry.Geometry.Collapse
