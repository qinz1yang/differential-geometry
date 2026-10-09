import DifferentialGeometry.Geometry.Collapse.LocalExport.BoundaryInterfaceDecomposition
import DifferentialGeometry.Topology.Maps.RelativeInteriorRemoval

/-!
# BCF01 on the interface: continuity of the stage maps, compact `S` and `M₂`, the collar and the
face inclusions (lane B-BCF134)

Blueprint `master207B.tex`, BCF01 (B:9642–9716), frozen target G3 of
`docs/geometrization/chapter14/evidence/boundary/TargetsBoundary.lean.txt` (T:390–395). Everything
here follows from the fields of `BoundaryGaf02Bases`, `BoundaryInitialCoresSpec` and
`BoundaryCompactSlimChoice` alone (`f_j = C.stageMap j`, `X_j = Bs.source j`, `B_j = Bs.base j`,
`D₃ = Bs.slimBaseDomain_BIF ZC`, `S = Kc.piece`, `M₁ = ZC.M₁`, `M₂ = Kc.M₂`):

* `BoundaryGaf02Bases.continuousAt_stageMap_BCF`: `f_j` is continuous at every point of `X_j`
  (the rank field `rank_eq` makes `mvfderiv f_j p ≠ 0`, hence `f_j` is differentiable at `p`);
* `BoundaryCompactSlimChoice.isCompact_inter_slimBaseDomain_BCF`: `K₃ ∩ D₃ = f₃(M₁ ∩ X₃ ∩ f₃⁻¹K₃)`
  is compact (properness of `f₃|X₃`, `M₁` closed); `isCompact_piece_BCF`: `S` is compact;
  `isCompact_M₂_BCF`: `M₂` is compact (BCF01.a, compactness part);
* `BoundaryCompactSlimChoice.piece_inter_frontier_subset_BCF` (the collar of the ZSP05 kernel
  `relative_interior_removal`): `S ∩ ∂M₁ ⊆ int_{M₁} S`, from (K)'s `faces_subset`;
* the face inclusions of (BCF01.b) that need only the collar and closedness of `S`:
  `piece_inter_M₂_subset_BCF` (`S ∩ M₂ ⊆ ∂S \ ∂M₁`), `frontier_M₁_diff_subset_BCF`
  (`∂M₁ \ S ⊆ ∂M₂`), `frontier_M₂_subset_BCF` (`∂M₂ ⊆ (∂M₁ \ S) ∪ (∂S \ ∂M₁)`) and
  `disjoint_faces_BCF` (the third conjunct of G3).

The two remaining inclusions of G3 (`∂S \ ∂M₁ ⊆ S ∩ M₂` and `∂S \ ∂M₁ ⊆ ∂M₂`) need `S ⊆ M₁`
(saturation of the zero faces, `BoundaryInitialCoresSpecSat`) and regularity `cl(int S) = S`.
-/

set_option autoImplicit false

noncomputable section

open Set Function Metric Bundle Manifold Filter
open scoped ContDiff Manifold Topology ENNReal
open DifferentialGeometry.Topology.Ehresmann DifferentialGeometry.Topology.Manifold
open DifferentialGeometry.Geometry.Riemannian GC.MetricGeometry
open DifferentialGeometry GC.Endpoint DifferentialGeometry.Geometry.Hyperbolic
open DifferentialGeometry.Analysis DifferentialGeometry.Topology

namespace DifferentialGeometry.Geometry.Collapse

local notation "E3" => EuclideanSpace ℝ (Fin 3)

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace

attribute [local instance] nezero_finrank_euclideanThree_LC87

attribute [local instance] interiorCharted_BDRY1 interiorManifold_BDRY1
  connectedSpace_interior_BDRY2

/-- Membership in the relative interior `int_Y Z`: a point of `Y` with an open neighbourhood `O`
such that `O ∩ Y ⊆ Z`. -/
theorem mem_relInterior_iff_BCF {X : Type*} [TopologicalSpace X] {Y Z : Set X} {x : X} :
    x ∈ relInterior_BIF Y Z ↔ x ∈ Y ∧ ∃ O : Set X, IsOpen O ∧ x ∈ O ∧ O ∩ Y ⊆ Z :=
  mem_image_interior_preimage_val_iff

variable {K : ℕ} {A : ℝ → ℝ} {β : ℕ → ℝ}
  {βd εN Λ w Δ σs σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V vs ζ Λz θ : ℝ}
  {W : CompactCarrier.{0}} [ConnectedSpace W.Carrier] {g : SmoothRiemannianMetric W.model W.Carrier}
  {δn : ℝ} {n : ℕ} {B : NearlyCuspidalBoundary W g K δn}
  {oM : ManifoldOrientation 𝓘(ℝ, E3) (W.pieceInterior ⊤) 3}
  {S : BoundarySupply K A β βd εN Λ w Δ σs σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V vs ζ Λz θ W g
    δn n B oM} {Φ : BoundaryInteriorSlots_BIF S} {D : BoundaryAugmentedData S Φ} {Kj : ℕ}
  {Ξ Sg eg c cw : Fin 3 → ℝ} {bcut bder κ : ℝ}
  {C : BoundaryGaf02Chain D Kj Ξ Sg eg c cw bcut bder κ}

/-- The submersion dimension of every stage is positive. -/
theorem gafStageDim_ne_zero_BCF (st : Fin 3) : gafStageDim st ≠ 0 := by
  fin_cases st <;> simp [gafStageDim]

/-- A continuous linear map whose range has positive dimension is nonzero. -/
theorem ne_zero_of_finrank_range_BCF {E F : Type*} [TopologicalSpace E] [AddCommMonoid E]
    [Module ℝ E] [TopologicalSpace F] [AddCommMonoid F] [Module ℝ F] (f : E →L[ℝ] F) {k : ℕ}
    (hk : k ≠ 0) (h : Module.finrank ℝ (LinearMap.range (f : E →ₗ[ℝ] F)) = k) : f ≠ 0 := by
  rintro rfl
  have hb : LinearMap.range ((0 : E →L[ℝ] F) : E →ₗ[ℝ] F) = ⊥ := by
    rw [LinearMap.range_eq_bot]
    rfl
  rw [hb, finrank_bot] at h
  exact hk h.symm

/-- **The stage map is continuous on its source domain**: at `p ∈ X_j` the rank field gives
`rank d f_j(p) = k_j > 0`, so `f_j` is differentiable, hence continuous, at `p`. -/
theorem BoundaryGaf02Bases.continuousAt_stageMap_BCF (Bs : BoundaryGaf02Bases C) {st : Fin 3}
    {p : W.Carrier} (hp : p ∈ Bs.source st) : ContinuousAt (C.stageMap st) p := by
  have hne : mvfderiv W.model (C.stageMap st) p ≠ 0 :=
    ne_zero_of_finrank_range_BCF _ (gafStageDim_ne_zero_BCF st) (Bs.rank_eq st p hp)
  by_contra hc
  have hnd : ¬ MDifferentiableAt W.model
      𝓘(ℝ, BoundaryAmbient_BIF S.IntTag_BAUGA (Fin S.packet.cusp.count)) (C.stageMap st) p :=
    fun h => hc h.continuousAt
  apply hne
  simp [mvfderiv, mfderiv_zero_of_not_mdifferentiableAt hnd]

/-- `f_j` is continuous on `X_j`. -/
theorem BoundaryGaf02Bases.continuousOn_stageMap_BCF (Bs : BoundaryGaf02Bases C) (st : Fin 3) :
    ContinuousOn (C.stageMap st) (Bs.source st) :=
  fun _ hp => (Bs.continuousAt_stageMap_BCF hp).continuousWithinAt

/-- `M₁ = W \ int_W(Z ∪ C_∂)` is closed. -/
theorem BoundaryInitialCoresSpec.isClosed_M₁_BCF (ZC : BoundaryInitialCoresSpec C) :
    IsClosed ZC.M₁ :=
  isOpen_interior.isClosed_compl

namespace BoundaryCompactSlimChoice

variable {Bs : BoundaryGaf02Bases C} {ZC : BoundaryInitialCoresSpec C}
  (Kc : BoundaryCompactSlimChoice Bs ZC)

/-- `K₃ ⊆ B₃`. -/
theorem K₃_subset_base_BCF : Kc.K₃ ⊆ Bs.base 2 :=
  iUnion_subset fun k => Kc.arc_subset_base k

/-- `K₃ ∩ D₃ = f₃(M₁ ∩ X₃ ∩ f₃⁻¹K₃)`. -/
theorem inter_slimBaseDomain_eq_image_BCF :
    Kc.K₃ ∩ Bs.slimBaseDomain_BIF ZC =
      C.stageMap 2 '' (ZC.M₁ ∩ (Bs.source 2 ∩ C.stageMap 2 ⁻¹' Kc.K₃)) := by
  ext y
  constructor
  · rintro ⟨hyK, p, ⟨hpM, hpX⟩, rfl⟩
    exact ⟨p, ⟨hpM, hpX, hyK⟩, rfl⟩
  · rintro ⟨p, ⟨hpM, hpX, hpK⟩, rfl⟩
    exact ⟨hpK, p, ⟨hpM, hpX⟩, rfl⟩

/-- **`K₃ ∩ D₃` is compact**: the image of the compact set `M₁ ∩ (X₃ ∩ f₃⁻¹K₃)` (properness of
`f₃|X₃`, `M₁` closed) under `f₃`, continuous on `X₃`. -/
theorem isCompact_inter_slimBaseDomain_BCF : IsCompact (Kc.K₃ ∩ Bs.slimBaseDomain_BIF ZC) := by
  rw [Kc.inter_slimBaseDomain_eq_image_BCF]
  have hK : IsCompact (Bs.source 2 ∩ C.stageMap 2 ⁻¹' Kc.K₃) :=
    Bs.proper 2 Kc.K₃ Kc.K₃_subset_base_BCF Kc.isCompact_K₃
  exact (hK.inter_left ZC.isClosed_M₁_BCF).image_of_continuousOn
    ((Bs.continuousOn_stageMap_BCF 2).mono fun _ hp => hp.2.1)

/-- **BCF01.a, `S` is compact**: `S = X₃ ∩ f₃⁻¹(K₃ ∩ D₃)` with `K₃ ∩ D₃ ⊆ B₃` compact. -/
theorem isCompact_piece_BCF : IsCompact Kc.piece :=
  Bs.proper 2 _ (inter_subset_left.trans Kc.K₃_subset_base_BCF)
    Kc.isCompact_inter_slimBaseDomain_BCF

/-- `S` is closed. -/
theorem isClosed_piece_BCF : IsClosed Kc.piece :=
  Kc.isCompact_piece_BCF.isClosed

/-- `M₂` is closed. -/
theorem isClosed_M₂_BCF : IsClosed Kc.M₂ :=
  (isCompact_relative_interior_removal (ZC.union ∪ C.cuspCores_BIF) Kc.piece).isClosed

/-- **BCF01.a, `M₂` is compact**. -/
theorem isCompact_M₂_BCF : IsCompact Kc.M₂ :=
  isCompact_relative_interior_removal (ZC.union ∪ C.cuspCores_BIF) Kc.piece

/-- `int_{M₁} S ⊆ S`. -/
theorem relInterior_subset_piece_BCF : relInterior_BIF ZC.M₁ Kc.piece ⊆ Kc.piece := by
  intro x hx
  obtain ⟨hxM, O, -, hxO, hOS⟩ := mem_relInterior_iff_BCF.mp hx
  exact hOS ⟨hxO, hxM⟩

/-- `M₂ ⊆ M₁`. -/
theorem M₂_subset_M₁_BCF : Kc.M₂ ⊆ ZC.M₁ :=
  sdiff_subset

/-- **The collar of the old faces** (BCF01: "At any shared old face `K₃` imposes no restriction on
a full base neighborhood, so its entire inward collar is retained"): `S ∩ ∂M₁ ⊆ int_{M₁} S`. A point
of `S` on `∂M₁` has its base point in `f₃(∂M₁ ∩ X₃) ⊆ int_{B₃} K₃` by (K); the preimage under the
continuous `f₃|X₃` of a relatively open base neighbourhood inside `K₃` meets `M₁` inside `S`. -/
theorem piece_inter_frontier_subset_BCF :
    Kc.piece ∩ frontier ZC.M₁ ⊆ relInterior_BIF ZC.M₁ Kc.piece := by
  rintro x ⟨hxS, hxf⟩
  have hxX : x ∈ Bs.source 2 := hxS.1
  have hy : C.stageMap 2 x ∈ relInterior_BIF (Bs.base 2) Kc.K₃ :=
    Kc.faces_subset ⟨x, ⟨hxf, hxX⟩, rfl⟩
  obtain ⟨-, O, hO, hyO, hOK⟩ := mem_relInterior_iff_BCF.mp hy
  have hnhds : Bs.source 2 ∩ C.stageMap 2 ⁻¹' O ∈ 𝓝 x :=
    inter_mem ((Bs.isOpen_source 2 (by decide)).mem_nhds hxX)
      ((Bs.continuousAt_stageMap_BCF hxX).preimage_mem_nhds (hO.mem_nhds hyO))
  obtain ⟨U, hUsub, hU, hxU⟩ := mem_nhds_iff.mp hnhds
  have hxM : x ∈ ZC.M₁ := ZC.isClosed_M₁_BCF.frontier_subset hxf
  refine mem_relInterior_iff_BCF.mpr ⟨hxM, U, hU, hxU, ?_⟩
  rintro z ⟨hzU, hzM⟩
  have hzX : z ∈ Bs.source 2 := (hUsub hzU).1
  have hzB : C.stageMap 2 z ∈ Bs.base 2 := Bs.image_eq 2 ▸ mem_image_of_mem _ hzX
  exact ⟨hzX, hOK ⟨(hUsub hzU).2, hzB⟩, z, ⟨hzM, hzX⟩, rfl⟩

/-- **G3, first conjunct, `⊆`**: `S ∩ M₂ ⊆ ∂S \ ∂M₁`. -/
theorem piece_inter_M₂_subset_BCF :
    Kc.piece ∩ Kc.M₂ ⊆ frontier Kc.piece \ frontier ZC.M₁ := by
  rintro x ⟨hxS, hxM, hxrel⟩
  refine ⟨?_, fun hxf => hxrel (Kc.piece_inter_frontier_subset_BCF ⟨hxS, hxf⟩)⟩
  rw [Kc.isClosed_piece_BCF.frontier_eq]
  exact ⟨hxS, fun hint => hxrel (mem_relInterior_iff_BCF.mpr
    ⟨hxM, interior Kc.piece, isOpen_interior, hint, fun _ hy => interior_subset hy.1⟩)⟩

/-- **G3, second conjunct, the old faces**: `∂M₁ \ S ⊆ ∂M₂`. -/
theorem frontier_M₁_diff_subset_BCF : frontier ZC.M₁ \ Kc.piece ⊆ frontier Kc.M₂ := by
  rintro x ⟨hxf, hxS⟩
  rw [ZC.isClosed_M₁_BCF.frontier_eq] at hxf
  rw [Kc.isClosed_M₂_BCF.frontier_eq]
  exact ⟨⟨hxf.1, fun hrel => hxS (Kc.relInterior_subset_piece_BCF hrel)⟩,
    fun hint => hxf.2 (interior_mono Kc.M₂_subset_M₁_BCF hint)⟩

/-- **G3, second conjunct, `⊆`**: `∂M₂ ⊆ (∂M₁ \ S) ∪ (∂S \ ∂M₁)`. -/
theorem frontier_M₂_subset_BCF :
    frontier Kc.M₂ ⊆ (frontier ZC.M₁ \ Kc.piece) ∪ (frontier Kc.piece \ frontier ZC.M₁) := by
  intro x hx
  rw [Kc.isClosed_M₂_BCF.frontier_eq] at hx
  obtain ⟨hxM₂, hxint⟩ := hx
  by_cases hxf₁ : x ∈ frontier ZC.M₁
  · exact Or.inl ⟨hxf₁, fun hxS => hxM₂.2 (Kc.piece_inter_frontier_subset_BCF ⟨hxS, hxf₁⟩)⟩
  · have hxint₁ : x ∈ interior ZC.M₁ := by
      by_contra h
      rw [ZC.isClosed_M₁_BCF.frontier_eq] at hxf₁
      exact hxf₁ ⟨hxM₂.1, h⟩
    by_cases hxS : x ∈ Kc.piece
    · exact Or.inr (Kc.piece_inter_M₂_subset_BCF ⟨hxS, hxM₂⟩)
    · exfalso
      apply hxint
      rw [mem_interior]
      refine ⟨interior ZC.M₁ ∩ Kc.pieceᶜ, fun y hy => ⟨interior_subset hy.1, fun hyrel =>
        hy.2 (Kc.relInterior_subset_piece_BCF hyrel)⟩,
        isOpen_interior.inter Kc.isClosed_piece_BCF.isOpen_compl, hxint₁, hxS⟩

/-- **G3, third conjunct**: the two face families are disjoint. -/
theorem disjoint_faces_BCF :
    Disjoint (frontier ZC.M₁ \ Kc.piece) (frontier Kc.piece \ frontier ZC.M₁) :=
  Set.disjoint_left.mpr fun _ hx hx' => hx'.2 hx.1

end BoundaryCompactSlimChoice

end DifferentialGeometry.Geometry.Collapse
