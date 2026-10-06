import DifferentialGeometry.Geometry.Collapse.LocalExport.BoundaryCircleNestingRM1
import DifferentialGeometry.Geometry.Collapse.LocalExport.BoundarySlimArcsBCF
import DifferentialGeometry.Geometry.Collapse.LocalExport.BoundaryInterfaceFibresV2b
import DifferentialGeometry.Geometry.Collapse.LocalExport.BoundaryInterfaceZeroDomainsV2
import DifferentialGeometry.Geometry.Collapse.LocalExport.BoundaryPiecesRestBC2

/-!
# BCF02 rim clauses, G4: the circle remainder is saturated by whole `f₁`-fibres (lane S-RIM81)

External review 81 (d), D81-9, the full derivation of `hsat`:

* `relInterior_saturated_of_openMap_RM1` (generic topology): if `f` is continuous and relatively
  open on an open `U` (a map `U → f(U)`) and `A`, `D` are `f`-saturated inside `U`, then `int_A D`
  is `f`-saturated inside `U`;
* `BoundaryCompactSlimChoiceV2.remainder_saturated_actual_RM1`: on the actual slot,
  `X₁ ∩ f₁⁻¹(f₁(R_c)) ⊆ R_c` (given `R_c ⊆ X₁`). `M₁ ∩ X₁` is saturated by `Z.face_saturated`; the
  slim piece `S` and `X₂` are saturated because `f₃`, `f₂`, `T` factor through `f₁ = E`
  (`final_data_eq_of_circle_eq_RM1`); `f₁|X₁` is open by the whole circle charts
  (`SmoothProductChartAt_BIFc.exists_relOpen_subset_image_BCF`); two applications of the generic
  lemma (`M₂ = M₁ ∖ int_{M₁} S`, `R_c = M₂ ∖ int_{M₂} P_e`) and the final use of `hX1`.
-/

set_option autoImplicit false

noncomputable section

open Set Function Metric Bundle Manifold Filter Topology
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

/-- **Relative interiors of saturated sets are saturated** (generic): `f` continuous on the open `U`
and relatively open as a map `U → f(U)`; `A`, `D` saturated inside `U`; then a point of `U` in
`int_A D` has its whole `f`-fibre inside `U` in `int_A D`. -/
theorem relInterior_saturated_of_openMap_RM1 {X Y : Type*} [TopologicalSpace X]
    [TopologicalSpace Y] {f : X → Y} {U : Set X} (hU : IsOpen U) (hf : ContinuousOn f U)
    (hopen : ∀ V : Set X, IsOpen V → V ⊆ U → ∀ p ∈ V, ∃ O : Set Y, IsOpen O ∧ f p ∈ O ∧
      O ∩ f '' U ⊆ f '' V)
    {A D : Set X} (hA : ∀ x ∈ A ∩ U, ∀ y ∈ U, f y = f x → y ∈ A)
    (hD : ∀ x ∈ D ∩ U, ∀ y ∈ U, f y = f x → y ∈ D)
    {x y : X} (hx : x ∈ U) (hxr : x ∈ relInterior_BIF A D) (hy : y ∈ U) (hxy : f y = f x) :
    y ∈ relInterior_BIF A D := by
  obtain ⟨hxA, O, hOo, hxO, hOsub⟩ := mem_relInterior_iff_BCF.mp hxr
  obtain ⟨O', hO'o, hfxO', hO'sub⟩ :=
    hopen (O ∩ U) (hOo.inter hU) inter_subset_right x ⟨hxO, hx⟩
  refine mem_relInterior_iff_BCF.mpr ⟨hA x ⟨hxA, hx⟩ y hy hxy, U ∩ f ⁻¹' O',
    hf.isOpen_inter_preimage hU hO'o, ⟨hy, ?_⟩, ?_⟩
  · change f y ∈ O'
    rw [hxy]
    exact hfxO'
  · rintro z ⟨⟨hzU, hzO'⟩, hzA⟩
    obtain ⟨z₀, ⟨hz₀O, hz₀U⟩, hz₀z⟩ := hO'sub ⟨hzO', mem_image_of_mem f hzU⟩
    have hz₀A : z₀ ∈ A := hA z ⟨hzA, hzU⟩ z₀ hz₀U hz₀z
    have hz₀D : z₀ ∈ D := hOsub ⟨hz₀O, hz₀A⟩
    exact hD z₀ ⟨hz₀D, hz₀U⟩ z hzU hz₀z.symm

variable {K : ℕ} {A : ℝ → ℝ} {β : ℕ → ℝ}
  {βd εN Λ w Δ σs σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V vs ζ Λz θ : ℝ}
  {W : CompactCarrier.{0}} [ConnectedSpace W.Carrier] {g : SmoothRiemannianMetric W.model W.Carrier}
  {δn : ℝ} {n : ℕ} {B : NearlyCuspidalBoundary W g K δn}
  {oM : ManifoldOrientation 𝓘(ℝ, E3) (W.pieceInterior ⊤) 3}
  {S : BoundarySupply K A β βd εN Λ w Δ σs σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V vs ζ
    Λz θ W g δn n B oM} {D : BoundaryAugmentedData S (actualSlotsV2_BAUGD S)} {Kj : ℕ}
  {Ξ Sg eg c cw : Fin 3 → ℝ} {bcut bder κ : ℝ}
  {C : BoundaryGaf02Chain D Kj Ξ Sg eg c cw bcut bder κ} {Bs : BoundaryGaf02BasesV2 C}

namespace BoundaryCompactSlimChoiceV2

/-- **`hsat` on the actual slot (review 81 (d), D81-9)**: `X₁ ∩ f₁⁻¹(f₁(R_c)) ⊆ R_c`. -/
theorem remainder_saturated_actual_RM1 (WF : BoundaryWholeFiberSpecV2b C Bs)
    (Z : BoundaryActualZeroDomains_BIFc C Bs) (Kc : BoundaryCompactSlimChoiceV2 Bs)
    (hX1 : Kc.remainder ⊆ Bs.source 0) :
    Bs.source 0 ∩ C.stageMap 0 ⁻¹' (C.stageMap 0 '' Kc.remainder) ⊆ Kc.remainder := by
  have hU : IsOpen (Bs.source 0) := Bs.isOpen_source 0 (by decide)
  have hf : ContinuousOn (C.stageMap 0) (Bs.source 0) := Bs.continuousOn_stageMap_BCF 0
  -- `f₁ : X₁ → B₁` is open (whole circle charts)
  have hopen : ∀ V : Set W.Carrier, IsOpen V → V ⊆ Bs.source 0 → ∀ p ∈ V, ∃ O : Set _,
      IsOpen O ∧ C.stageMap 0 p ∈ O ∧ O ∩ C.stageMap 0 '' Bs.source 0 ⊆ C.stageMap 0 '' V := by
    intro V hV hVU p hp
    have hb : C.stageMap 0 p ∈ Bs.base 0 := Bs.image_eq 0 ▸ mem_image_of_mem _ (hVU hp)
    obtain ⟨O, hOo, hpO, hOsub⟩ :=
      (WF.circle_chart _ hb).exists_relOpen_subset_image_BCF hVU hV hp rfl
    exact ⟨O, hOo, hpO, by rw [Bs.image_eq 0]; exact hOsub⟩
  -- the nesting: `f₃`, `f₂`, `T` are functions of `f₁`
  have hnest : ∀ {x y : W.Carrier}, C.stageMap 0 y = C.stageMap 0 x →
      (∀ st : Fin 3, C.stageMap st y = C.stageMap st x) ∧ C.heightRatio y = C.heightRatio x :=
    fun h => C.final_data_eq_of_circle_eq_RM1 h
  -- `M₁ ∩ X₁` is saturated
  have hM₁ : ∀ x ∈ C.M₁_BIFc ∩ Bs.source 0, ∀ y ∈ Bs.source 0,
      C.stageMap 0 y = C.stageMap 0 x → y ∈ C.M₁_BIFc :=
    fun x hx y hy hxy => Z.face_saturated 0 (by decide) x hx.2 y hy hxy hx.1
  -- `S ∩ X₁` is saturated
  have hS : ∀ x ∈ Kc.piece ∩ Bs.source 0, ∀ y ∈ Bs.source 0,
      C.stageMap 0 y = C.stageMap 0 x → y ∈ Kc.piece := by
    intro x hx y hy hxy
    obtain ⟨⟨hx2, hxK⟩, -⟩ := hx
    have h3 : C.stageMap 2 y = C.stageMap 2 x := (hnest hxy).1 2
    refine ⟨?_, ?_⟩
    · rw [Bs.slim_source_eq] at hx2 ⊢
      change C.stageMap 2 y ∈ Bs.base 2
      rw [h3]
      exact hx2
    · change C.stageMap 2 y ∈ Kc.K₃ ∩ Bs.slimBaseDomain_BIFc
      rw [h3]
      exact hxK
  have hrM₁ : ∀ x ∈ Bs.source 0, x ∈ relInterior_BIF C.M₁_BIFc Kc.piece →
      ∀ y ∈ Bs.source 0, C.stageMap 0 y = C.stageMap 0 x →
        y ∈ relInterior_BIF C.M₁_BIFc Kc.piece :=
    fun x hx hxr y hy hxy => relInterior_saturated_of_openMap_RM1 hU hf hopen hM₁ hS hx hxr hy hxy
  -- `M₂ ∩ X₁` is saturated
  have hM₂ : ∀ x ∈ Kc.M₂ ∩ Bs.source 0, ∀ y ∈ Bs.source 0,
      C.stageMap 0 y = C.stageMap 0 x → y ∈ Kc.M₂ := by
    intro x hx y hy hxy
    refine ⟨hM₁ x ⟨hx.1.1, hx.2⟩ y hy hxy, fun hyr => hx.1.2 ?_⟩
    exact hrM₁ y hy hyr x hx.2 hxy.symm
  -- `P_e ∩ X₁` is saturated
  have hP : ∀ x ∈ Kc.edgePiece ∩ Bs.source 0, ∀ y ∈ Bs.source 0,
      C.stageMap 0 y = C.stageMap 0 x → y ∈ Kc.edgePiece := by
    intro x hx y hy hxy
    obtain ⟨⟨hxM, hx1⟩, hx0⟩ := hx
    refine ⟨hM₂ x ⟨hxM, hx0⟩ y hy hxy, ?_⟩
    obtain ⟨hf2, hT⟩ := hnest hxy
    rw [Bs.edge_source_eq] at hx1 ⊢
    refine ⟨?_, ?_⟩
    · change C.stageMap 1 y ∈ Bs.base 1
      rw [hf2 1]
      exact hx1.1
    · change C.heightRatio y ≤ 4 * Δ
      rw [hT]
      exact hx1.2
  have hrM₂ : ∀ x ∈ Bs.source 0, x ∈ relInterior_BIF Kc.M₂ Kc.edgePiece →
      ∀ y ∈ Bs.source 0, C.stageMap 0 y = C.stageMap 0 x →
        y ∈ relInterior_BIF Kc.M₂ Kc.edgePiece :=
    fun x hx hxr y hy hxy => relInterior_saturated_of_openMap_RM1 hU hf hopen hM₂ hP hx hxr hy hxy
  -- conclusion, using `R_c ⊆ X₁`
  rintro x ⟨hx0, r, hr, hrx⟩
  have hr0 : r ∈ Bs.source 0 := hX1 hr
  have hxr : C.stageMap 0 x = C.stageMap 0 r := hrx.symm
  refine ⟨hM₂ r ⟨hr.1, hr0⟩ x hx0 hxr, fun hxrel => hr.2 ?_⟩
  exact hrM₂ x hx0 hxrel r hr0 hrx

end BoundaryCompactSlimChoiceV2

end DifferentialGeometry.Geometry.Collapse
