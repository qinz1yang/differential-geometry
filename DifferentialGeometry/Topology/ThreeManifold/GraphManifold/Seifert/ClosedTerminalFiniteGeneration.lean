import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Seifert.ClosedTerminalFibre

/-!
# The actual host generates the fundamental group after three fillings

A filling solid torus contributes no generators beyond its boundary longitude. Actual leaf
retractions preserve the source port, and van Kampen eliminates the leaf at each of three
successive open covers. The middle region retracts onto the original product piece. The result
is surjectivity of the actual product-to-carrier map on fundamental groups at every host point.
-/

set_option autoImplicit false
noncomputable section
open Set CategoryTheory DifferentialGeometry DifferentialGeometry.Topology GC.Endpoint
open GC.GraphManifold DifferentialGeometry.Topology.VanKampen
open scoped Topology ContinuousMap unitInterval
universe u v
namespace GC.Seifert

section Cover
variable {X : Type u} [TopologicalSpace X]

private theorem pushout_right_surjective {H : Type v} [Group H] {M : Bool → Type v}
    [∀ i, Group (M i)] (φ : ∀ i, H →* M i) (hφ : Function.Surjective (φ false)) :
    Function.Surjective (Monoid.PushoutI.of (φ := φ) true) := by
  intro w
  induction w using Monoid.PushoutI.induction_on with
  | of i a =>
    cases i
    · obtain ⟨c, rfl⟩ := hφ a
      exact ⟨φ true c, by rw [Monoid.PushoutI.of_apply_eq_base,
        Monoid.PushoutI.of_apply_eq_base]⟩
    · exact ⟨a, rfl⟩
  | base c => exact ⟨φ true c, Monoid.PushoutI.of_apply_eq_base φ true c⟩
  | mul a b ha hb =>
    obtain ⟨a', rfl⟩ := ha
    obtain ⟨b', rfl⟩ := hb
    exact ⟨a' * b', map_mul _ _ _⟩

set_option backward.isDefEq.respectTransparency false in
theorem surjective_map_transfer {Y : Type v} [TopologicalSpace Y] (f : C(X, Y))
    {x y : X} (β : Path x y) (hs : Function.Surjective (FundamentalGroup.map f x)) :
    Function.Surjective (FundamentalGroup.map f y) := by
  intro g
  obtain ⟨a, ha⟩ := hs (fundamentalGroupChangeBasepoint (β.map f.continuous) g)
  refine ⟨(fundamentalGroupChangeBasepoint β).symm a, ?_⟩
  apply (fundamentalGroupChangeBasepoint (β.map f.continuous)).injective
  rw [← changeBasepoint_map, MulEquiv.apply_symm_apply]
  exact ha

set_option backward.isDefEq.respectTransparency false in
theorem surjective_right_of_openCover (U V : Set X) (hU : IsOpen U) (hV : IsOpen V)
    (hcover : U ∪ V = univ) (x : ↑(U ∩ V))
    [PathConnectedSpace U] [PathConnectedSpace V] [PathConnectedSpace ↑(U ∩ V)]
    (hleft : Function.Surjective (FundamentalGroup.map (interToLeft U V) x)) :
    Function.Surjective (FundamentalGroup.map (subsetToAmbient V) (interToRight U V x)) := by
  let e := fundamentalGroupEquivAmalgamatedProduct U V hU hV hcover x.1 x.2
  let φ := fundamentalGroupAmalgamation U V x.1 x.2
  have hφ : Function.Surjective (φ false) := by
    change Function.Surjective (FundamentalGroup.mapOfEq (interToLeft U V) rfl)
    rwa [mapOfEq_rfl']
  have hs := pushout_right_surjective φ hφ
  intro g
  obtain ⟨w, rfl⟩ := e.surjective g
  obtain ⟨b, rfl⟩ := hs w
  refine ⟨b, ?_⟩
  have h := DFunLike.congr_fun
    (fundamentalGroupEquivAmalgamatedProduct_comp_right U V hU hV hcover x.1 x.2) b
  change e (Monoid.PushoutI.of (φ := φ) true b) =
    FundamentalGroup.mapOfEq (subsetToAmbient V) rfl b at h
  rw [mapOfEq_rfl'] at h
  exact h.symm

set_option backward.isDefEq.respectTransparency false in
theorem surjective_right_of_openCover_map (U V : Set X) (hU : IsOpen U) (hV : IsOpen V)
    (hcover : U ∪ V = univ) [PathConnectedSpace U] [PathConnectedSpace V]
    [PathConnectedSpace ↑(U ∩ V)] (g : C(Torus, ↑(U ∩ V))) (t : Torus)
    (hg : Function.Surjective (FundamentalGroup.map ((interToLeft U V).comp g) t))
    (v : V) : Function.Surjective (FundamentalGroup.map (subsetToAmbient V) v) := by
  have hs : Function.Surjective (FundamentalGroup.map (interToLeft U V) (g t)) :=
    surjective_fundamentalGroup_map_of_comp g (interToLeft U V) t hg
  have hs' := surjective_right_of_openCover U V hU hV hcover (g t) hs
  exact surjective_map_transfer (subsetToAmbient V)
    (PathConnectedSpace.somePath (interToRight U V (g t)) v) hs'


end Cover

namespace SeifertBlock
variable {W : CompactCarrier.{u}} {d : SeifertData} (B : SeifertBlock W d)

theorem exists_bijective_leafRetraction_with_seam (m : Fin d.fillingCount) :
    ∃ f : C(B.presentation.leftRegion (B.seam m),
        B.presentation.components.piece (B.piece (some m))),
      (∀ y, Function.Bijective (FundamentalGroup.map f y)) ∧
        f.comp (B.presentation.seamTorusToLeft (B.seam m)) = (B.solid m).portMap 0 := by
  have hS := B.pieceImage_inter_solid m
  have hU := B.presentation.leftRegion_inter_pieceComplImage_subset hS
  rw [B.leftPiece_seam] at hS hU
  obtain ⟨φ, hφA, hφB⟩ := B.presentation.exists_collarShrinkHomotopy_ite (B.seam m)
    (B.presentation.isClosed_pieceComplImage _) (B.presentation.isClosed_pieceImage _)
    (fun w => (B.presentation.mem_pieceImage_or_mem_pieceComplImage (B.piece (some m)) w).symm)
    (fun w hw => hS ⟨hw.2, hw.1⟩) hU
    ⟨fun p => p.2.1, continuous_subtype_val.comp continuous_snd⟩ (fun τ u hu => rfl)
  have hcases : ∀ (τ : I) (u : B.presentation.leftRegion (B.seam m)),
      (φ (τ, u) = u.1 ∧ u.1 ∈ B.presentation.pieceImage (B.piece (some m))) ∨
        (φ (τ, u) = B.presentation.collarShrink (B.seam m) (τ, u.1) ∧
          u.1 ∈ B.presentation.seamCollar (B.seam m)) := by
    intro τ u
    rcases B.presentation.mem_pieceImage_or_mem_pieceComplImage (B.piece (some m)) u.1 with h | h
    · exact Or.inl ⟨hφB τ u h, h⟩
    · exact Or.inr ⟨hφA τ u h, hU ⟨u.2, h⟩⟩
  obtain ⟨f, hf, hfx⟩ := B.presentation.exists_bijective_retraction_of_deformation
    (B.piece (some m))
    (B.presentation.injOn_cutMap_of_ne B.leftPiece_ne_rightPiece _)
    (B.pieceImage_solid_subset_leftRegion m) φ
    (fun p => by
      rcases hcases p.1 p.2 with ⟨h, -⟩ | ⟨h, hc⟩
      · rw [h]
        exact p.2.2
      · rw [h]
        exact Or.inr (B.presentation.collarShrink_mem_seamCollar (B.seam m) p.1 hc))
    (fun u => by
      rcases hcases 0 u with ⟨h, -⟩ | ⟨h, hc⟩
      · exact h
      · rw [h]
        exact B.presentation.collarShrink_zero (B.seam m) hc)
    (fun u => by
      rcases hcases 1 u with ⟨h, hk⟩ | ⟨h, -⟩
      · rw [h]
        exact hk
      · rw [h]
        exact B.seamSurface_subset_pieceImage_some m
          (B.presentation.collarShrink_one_mem_seamSurface _ _))
    (fun u hu => hφB 1 u hu)
  refine ⟨f, hf, ContinuousMap.ext fun t => ?_⟩
  have hp : (B.presentation.pairing.leftParam (B.seam m) t : B.presentation.cutCarrier.Carrier) ∈
      B.presentation.components.piece (B.piece (some m)) := by
    rw [← B.leftPiece_seam]
    exact B.presentation.left_owned _ (B.presentation.pairing.leftParam _ t).2
  have hx : B.presentation.cutMap (B.presentation.pairing.leftParam (B.seam m) t) ∈
      B.presentation.leftRegion (B.seam m) := by
    rw [← B.presentation.seamTorus_eq_cutMap]
    exact Or.inr (B.presentation.seamTorus_mem_seamCollar _ t)
  have hs : B.presentation.seamTorusToLeft (B.seam m) t =
      ⟨B.presentation.cutMap (B.presentation.pairing.leftParam (B.seam m) t), hx⟩ :=
    Subtype.ext (B.presentation.seamTorus_eq_cutMap (B.seam m) t)
  change f (B.presentation.seamTorusToLeft (B.seam m) t) = _
  rw [hs, hfx ⟨_, hp⟩ hx]
  apply Subtype.ext
  rw [ProductFibredPiece.portMap_val, B.solid_port]
  exact (B.presentation.pairing.left_zero _ t).symm


theorem surjective_map_seamTorusToLeft (m : Fin d.fillingCount) (t : Torus) :
    Function.Surjective (FundamentalGroup.map
      (B.presentation.seamTorusToLeft (B.seam m)) t) := by
  obtain ⟨f, hf, hcomp⟩ := B.exists_bijective_leafRetraction_with_seam m
  exact surjective_fundamentalGroup_map_of_comp_eq _ f _ hcomp t (hf _).1
    ((B.solid m).surjective_map_portMap t)

def leafSeamIn {S : Set W.Carrier} (m : Fin d.fillingCount)
    (hLS : B.presentation.leftRegion (B.seam m) ⊆ S) :
    C(Torus, (Subtype.val ⁻¹' B.presentation.leftRegion (B.seam m) : Set S)) :=
  ⟨fun t => ⟨⟨B.presentation.seamTorus (B.seam m) t,
    hLS (Or.inr (B.presentation.seamTorus_mem_seamCollar _ t))⟩,
    Or.inr (B.presentation.seamTorus_mem_seamCollar _ t)⟩,
    ((B.presentation.seamTorus (B.seam m)).continuous.subtype_mk _).subtype_mk _⟩

set_option backward.isDefEq.respectTransparency false in
theorem surjective_map_leafSeamIn {S : Set W.Carrier} (m : Fin d.fillingCount)
    (hLS : B.presentation.leftRegion (B.seam m) ⊆ S) (t : Torus) :
    Function.Surjective (FundamentalGroup.map (B.leafSeamIn m hLS) t) := by
  let e := preimageValHomeo S (B.presentation.leftRegion (B.seam m)) hLS
  have hcomp : (e : C(_, _)).comp (B.leafSeamIn m hLS) =
      B.presentation.seamTorusToLeft (B.seam m) := ContinuousMap.ext fun t => rfl
  exact surjective_fundamentalGroup_map_of_comp_eq _ (e : C(_, _)) _ hcomp t
    (bijective_map_homeomorph e _).1 (B.surjective_map_seamTorusToLeft m t)

set_option backward.isDefEq.respectTransparency false in
theorem surjective_productToCarrier_of_fillingCount_eq_three (h3 : d.fillingCount = 3)
    (p : B.presentation.components.piece (B.piece none)) :
    Function.Surjective (FundamentalGroup.map B.productToCarrier p) := by
  have hW := B.connectedSpace
  let m₀ : Fin d.fillingCount := ⟨0, by omega⟩
  let m₁ : Fin d.fillingCount := ⟨1, by omega⟩
  let m₂ : Fin d.fillingCount := ⟨2, by omega⟩
  have h01 : m₀ ≠ m₁ := Fin.ne_of_val_ne (show (0 : ℕ) ≠ 1 by norm_num)
  have h02 : m₀ ≠ m₂ := Fin.ne_of_val_ne (show (0 : ℕ) ≠ 2 by norm_num)
  have h12 : m₁ ≠ m₂ := Fin.ne_of_val_ne (show (1 : ℕ) ≠ 2 by norm_num)
  have hcov : ∀ n : Fin d.fillingCount, n = m₀ ∨ n = m₁ ∨ n = m₂ := by
    intro n
    rcases n with ⟨n, hn⟩
    have hn3 : n < 3 := h3 ▸ hn
    rcases (by omega : n = 0 ∨ n = 1 ∨ n = 2) with rfl | rfl | rfl
    · exact Or.inl rfl
    · exact Or.inr (Or.inl rfl)
    · exact Or.inr (Or.inr rfl)
  obtain ⟨hc₀M, -, -⟩ := B.seamCollar_subset_middle₃ h01 h02 h12
  have hpcM := B.isPathConnected_middle₃ h01 h02 h12 hcov
  set G := B.presentation with hG
  have hL₀R₁ : G.leftRegion (B.seam m₀) ⊆ G.rightRegion (B.seam m₁) :=
    B.leftRegion_subset_rightRegion (Ne.symm h01)
  have hL₀R₂ : G.leftRegion (B.seam m₀) ⊆ G.rightRegion (B.seam m₂) :=
    B.leftRegion_subset_rightRegion (Ne.symm h02)
  have hL₁R₂ : G.leftRegion (B.seam m₁) ⊆ G.rightRegion (B.seam m₂) :=
    B.leftRegion_subset_rightRegion (Ne.symm h12)
  have hL₀N : G.leftRegion (B.seam m₀) ⊆
      G.rightRegion (B.seam m₁) ∩ G.rightRegion (B.seam m₂) := fun w hw => ⟨hL₀R₁ hw, hL₀R₂ hw⟩
  have hMN : G.rightRegion (B.seam m₀) ∩ G.rightRegion (B.seam m₁) ∩
      G.rightRegion (B.seam m₂) ⊆ G.rightRegion (B.seam m₁) ∩ G.rightRegion (B.seam m₂) :=
    fun w hw => ⟨hw.1.2, hw.2⟩
  have hNR₂ : G.rightRegion (B.seam m₁) ∩ G.rightRegion (B.seam m₂) ⊆
      G.rightRegion (B.seam m₂) := inter_subset_right
  have hPM : ∀ q : G.components.piece (B.piece none), B.productToCarrier q ∈
      G.rightRegion (B.seam m₀) ∩ G.rightRegion (B.seam m₁) ∩ G.rightRegion (B.seam m₂) :=
    fun q => B.pieceImage_none_subset_middle₃ m₀ m₁ m₂ ⟨q.1, q.2, rfl⟩
  have hL₀M : G.leftRegion (B.seam m₀) ∩ (G.rightRegion (B.seam m₀) ∩
      G.rightRegion (B.seam m₁) ∩ G.rightRegion (B.seam m₂)) = G.seamCollar (B.seam m₀) := by
    ext w
    constructor
    · rintro ⟨hl, ⟨hr, -⟩, -⟩
      rw [← G.leftRegion_inter_rightRegion (B.seam m₀) (B.isSeparating_seam m₀)]
      exact ⟨hl, hr⟩
    · intro hw
      exact ⟨Or.inr hw, hc₀M hw⟩
  have hNcases : ∀ w ∈ G.rightRegion (B.seam m₁) ∩ G.rightRegion (B.seam m₂),
      w ∈ G.leftRegion (B.seam m₀) ∨ w ∈ G.rightRegion (B.seam m₀) ∩
        G.rightRegion (B.seam m₁) ∩ G.rightRegion (B.seam m₂) := by
    intro w hw
    rcases B.mem_pieceImage_cases₃ hcov w with h | h | h | h
    · exact Or.inr ⟨⟨B.pieceImage_subset_rightRegion m₀ (B.piece_some_ne_none m₀) h, hw.1⟩,
        hw.2⟩
    · exact Or.inl (B.pieceImage_solid_subset_leftRegion m₀ h)
    · have hc := B.rightRegion_inter_pieceImage_subset m₁ ⟨hw.1, h⟩
      exact Or.inr ⟨⟨B.seamCollar_subset_rightRegion h01 hc, hw.1⟩, hw.2⟩
    · have hc := B.rightRegion_inter_pieceImage_subset m₂ ⟨hw.2, h⟩
      exact Or.inr ⟨⟨B.seamCollar_subset_rightRegion h02 hc, hw.1⟩, hw.2⟩
  have hpcN : IsPathConnected (G.rightRegion (B.seam m₁) ∩ G.rightRegion (B.seam m₂)) := by
    have heq : G.rightRegion (B.seam m₁) ∩ G.rightRegion (B.seam m₂) =
        G.leftRegion (B.seam m₀) ∪ (G.rightRegion (B.seam m₀) ∩ G.rightRegion (B.seam m₁) ∩
          G.rightRegion (B.seam m₂)) :=
      Subset.antisymm (fun w hw => hNcases w hw) (union_subset hL₀N hMN)
    rw [heq]
    exact (G.isPathConnected_leftRegion _).union hpcM
      ⟨_, Or.inr (G.seamTorus_mem_seamCollar _ torusBase),
        hc₀M (G.seamTorus_mem_seamCollar _ torusBase)⟩
  have hcov₀ : (Subtype.val ⁻¹' G.leftRegion (B.seam m₀) :
      Set ↥(G.rightRegion (B.seam m₁) ∩ G.rightRegion (B.seam m₂))) ∪
      Subtype.val ⁻¹' (G.rightRegion (B.seam m₀) ∩ G.rightRegion (B.seam m₁) ∩
        G.rightRegion (B.seam m₂)) = univ :=
    eq_univ_of_forall fun w => hNcases w.1 w.2
  have i01 : PathConnectedSpace (Subtype.val ⁻¹' G.leftRegion (B.seam m₀) :
      Set ↥(G.rightRegion (B.seam m₁) ∩ G.rightRegion (B.seam m₂))) :=
    pathConnectedSpace_preimage (G.isPathConnected_leftRegion _) hL₀N
  have i02 : PathConnectedSpace (Subtype.val ⁻¹' (G.rightRegion (B.seam m₀) ∩
      G.rightRegion (B.seam m₁) ∩ G.rightRegion (B.seam m₂)) :
      Set ↥(G.rightRegion (B.seam m₁) ∩ G.rightRegion (B.seam m₂))) :=
    pathConnectedSpace_preimage hpcM hMN
  have i03 : PathConnectedSpace ↑((Subtype.val ⁻¹' G.leftRegion (B.seam m₀) :
      Set ↥(G.rightRegion (B.seam m₁) ∩ G.rightRegion (B.seam m₂))) ∩
      Subtype.val ⁻¹' (G.rightRegion (B.seam m₀) ∩ G.rightRegion (B.seam m₁) ∩
        G.rightRegion (B.seam m₂))) :=
    pathConnectedSpace_preimage (hL₀M ▸ G.isPathConnected_seamCollar (B.seam m₀))
      (inter_subset_left.trans hL₀N)
  let ιV₀ : C(G.components.piece (B.piece none), (Subtype.val ⁻¹' (G.rightRegion (B.seam m₀) ∩
      G.rightRegion (B.seam m₁) ∩ G.rightRegion (B.seam m₂)) :
      Set ↥(G.rightRegion (B.seam m₁) ∩ G.rightRegion (B.seam m₂)))) :=
    ⟨fun q => ⟨⟨B.productToCarrier q, hMN (hPM q)⟩, hPM q⟩,
      (B.productToCarrier.continuous.subtype_mk _).subtype_mk _⟩
  obtain ⟨fM, hfMb, hfMx⟩ := B.exists_bijective_middleRetraction₃ h01 h02 h12 hcov
  let eM := preimageValHomeo _ _ hMN
  let f' : C(↑(Subtype.val ⁻¹' (G.rightRegion (B.seam m₀) ∩ G.rightRegion (B.seam m₁) ∩
      G.rightRegion (B.seam m₂)) :
      Set ↥(G.rightRegion (B.seam m₁) ∩ G.rightRegion (B.seam m₂))),
      G.components.piece (B.piece none)) :=
    fM.comp ⟨eM, eM.continuous⟩
  have hcomp : f'.comp ιV₀ = ContinuousMap.id _ := ContinuousMap.ext fun q => hfMx q _
  have hid : Function.Bijective (FundamentalGroup.map (f'.comp ιV₀) p) := by
    rw [hcomp]
    exact bijective_map_homeomorph (Homeomorph.refl _) p
  rw [GC.Topology.fundamentalGroup_map_comp] at hid
  change Function.Bijective ((FundamentalGroup.map f' (ιV₀ p)) ∘
    (FundamentalGroup.map ιV₀ p)) at hid
  have hf' : Function.Bijective (FundamentalGroup.map f' (ιV₀ p)) := by
    change Function.Bijective (FundamentalGroup.map (fM.comp ⟨eM, eM.continuous⟩) (ιV₀ p))
    rw [GC.Topology.fundamentalGroup_map_comp]
    change Function.Bijective ((FundamentalGroup.map fM (eM (ιV₀ p))) ∘
      (FundamentalGroup.map ⟨eM, eM.continuous⟩ (ιV₀ p)))
    exact (hfMb _).comp (bijective_map_homeomorph eM _)
  have hιV₀ : Function.Bijective (FundamentalGroup.map ιV₀ p) :=
    (Function.Bijective.of_comp_iff' hf' _).mp hid
  let g₀ : C(Torus, ↑((Subtype.val ⁻¹' G.leftRegion (B.seam m₀) :
      Set ↥(G.rightRegion (B.seam m₁) ∩ G.rightRegion (B.seam m₂))) ∩
      Subtype.val ⁻¹' (G.rightRegion (B.seam m₀) ∩ G.rightRegion (B.seam m₁) ∩
        G.rightRegion (B.seam m₂)))) :=
    ⟨fun t => ⟨⟨G.seamTorus (B.seam m₀) t,
      hL₀N (Or.inr (G.seamTorus_mem_seamCollar _ t))⟩,
      Or.inr (G.seamTorus_mem_seamCollar _ t),
      hc₀M (G.seamTorus_mem_seamCollar _ t)⟩,
      ((G.seamTorus (B.seam m₀)).continuous.subtype_mk _).subtype_mk _⟩
  have hg₀ : Function.Surjective (FundamentalGroup.map
      ((interToLeft _ _).comp g₀) torusBase) := by
    have heq : (interToLeft _ _).comp g₀ = B.leafSeamIn m₀ hL₀N :=
      ContinuousMap.ext fun t => rfl
    rw [heq]
    exact B.surjective_map_leafSeamIn m₀ hL₀N torusBase
  have hsurj₀ := surjective_right_of_openCover_map _ _
    ((G.isOpen_leftRegion _).preimage continuous_subtype_val)
    ((((G.isOpen_rightRegion _).inter (G.isOpen_rightRegion _)).inter
      (G.isOpen_rightRegion _)).preimage continuous_subtype_val)
    hcov₀ g₀ torusBase hg₀ (ιV₀ p)
  have hinner₀ : Function.Surjective (FundamentalGroup.map
      ((subsetToAmbient _).comp ιV₀) p) :=
    surjective_fundamentalGroup_map_comp _ _ p hιV₀.2 hsurj₀
  have hL₁N : G.leftRegion (B.seam m₁) ∩ (G.rightRegion (B.seam m₁) ∩
      G.rightRegion (B.seam m₂)) = G.seamCollar (B.seam m₁) := by
    ext w
    constructor
    · rintro ⟨hl, hr, -⟩
      rw [← G.leftRegion_inter_rightRegion (B.seam m₁) (B.isSeparating_seam m₁)]
      exact ⟨hl, hr⟩
    · intro hw
      exact ⟨Or.inr hw, Or.inr hw, B.seamCollar_subset_rightRegion (Ne.symm h12) hw⟩
  have hcov₁ : (Subtype.val ⁻¹' G.leftRegion (B.seam m₁) : Set (G.rightRegion (B.seam m₂))) ∪
      Subtype.val ⁻¹' (G.rightRegion (B.seam m₁) ∩ G.rightRegion (B.seam m₂)) = univ := by
    refine eq_univ_of_forall fun w => ?_
    rcases B.mem_pieceImage_cases₃ hcov w.1 with h | h | h | h
    · exact Or.inr ⟨B.pieceImage_subset_rightRegion m₁ (B.piece_some_ne_none m₁) h, w.2⟩
    · exact Or.inr ⟨hL₀R₁ (B.pieceImage_solid_subset_leftRegion m₀ h), w.2⟩
    · exact Or.inl (B.pieceImage_solid_subset_leftRegion m₁ h)
    · have hc := B.rightRegion_inter_pieceImage_subset m₂ ⟨w.2, h⟩
      exact Or.inr ⟨B.seamCollar_subset_rightRegion h12 hc, w.2⟩
  have i11 : PathConnectedSpace (Subtype.val ⁻¹' G.leftRegion (B.seam m₁) :
      Set (G.rightRegion (B.seam m₂))) :=
    pathConnectedSpace_preimage (G.isPathConnected_leftRegion _) hL₁R₂
  have i12 : PathConnectedSpace (Subtype.val ⁻¹' (G.rightRegion (B.seam m₁) ∩
      G.rightRegion (B.seam m₂)) : Set (G.rightRegion (B.seam m₂))) :=
    pathConnectedSpace_preimage hpcN hNR₂
  have i13 : PathConnectedSpace ↑((Subtype.val ⁻¹' G.leftRegion (B.seam m₁) :
      Set (G.rightRegion (B.seam m₂))) ∩ Subtype.val ⁻¹' (G.rightRegion (B.seam m₁) ∩
        G.rightRegion (B.seam m₂))) :=
    pathConnectedSpace_preimage (hL₁N ▸ G.isPathConnected_seamCollar (B.seam m₁))
      (inter_subset_left.trans hL₁R₂)
  let e₁ := (preimageValHomeo _ _ hNR₂).symm
  let ιV₁ : C(G.components.piece (B.piece none), (Subtype.val ⁻¹' (G.rightRegion (B.seam m₁) ∩
      G.rightRegion (B.seam m₂)) : Set (G.rightRegion (B.seam m₂)))) :=
    (e₁ : C(_, _)).comp ((subsetToAmbient _).comp ιV₀)
  have hιV₁ : Function.Surjective (FundamentalGroup.map ιV₁ p) :=
    surjective_fundamentalGroup_map_comp _ _ p hinner₀
      (bijective_map_homeomorph e₁ _).2
  let g₁ : C(Torus, ↑((Subtype.val ⁻¹' G.leftRegion (B.seam m₁) :
      Set (G.rightRegion (B.seam m₂))) ∩ Subtype.val ⁻¹'
        (G.rightRegion (B.seam m₁) ∩ G.rightRegion (B.seam m₂)))) :=
    ⟨fun t => ⟨⟨G.seamTorus (B.seam m₁) t,
      hL₁R₂ (Or.inr (G.seamTorus_mem_seamCollar _ t))⟩,
      Or.inr (G.seamTorus_mem_seamCollar _ t),
      Or.inr (G.seamTorus_mem_seamCollar _ t),
      B.seamCollar_subset_rightRegion (Ne.symm h12) (G.seamTorus_mem_seamCollar _ t)⟩,
      ((G.seamTorus (B.seam m₁)).continuous.subtype_mk _).subtype_mk _⟩
  have hg₁ : Function.Surjective (FundamentalGroup.map
      ((interToLeft _ _).comp g₁) torusBase) := by
    have heq : (interToLeft _ _).comp g₁ = B.leafSeamIn m₁ hL₁R₂ :=
      ContinuousMap.ext fun t => rfl
    rw [heq]
    exact B.surjective_map_leafSeamIn m₁ hL₁R₂ torusBase
  have hsurj₁ := surjective_right_of_openCover_map _ _
    ((G.isOpen_leftRegion _).preimage continuous_subtype_val)
    (((G.isOpen_rightRegion _).inter (G.isOpen_rightRegion _)).preimage continuous_subtype_val)
    hcov₁ g₁ torusBase hg₁ (ιV₁ p)
  let ιV₂ : C(G.components.piece (B.piece none), G.rightRegion (B.seam m₂)) :=
    (subsetToAmbient _).comp ιV₁
  have hιV₂ : Function.Surjective (FundamentalGroup.map ιV₂ p) :=
    surjective_fundamentalGroup_map_comp _ _ p hιV₁ hsurj₁
  have := isPathConnected_iff_pathConnectedSpace.mp (G.isPathConnected_leftRegion (B.seam m₂))
  have := isPathConnected_iff_pathConnectedSpace.mp (G.isPathConnected_rightRegion (B.seam m₂))
  have := G.pathConnectedSpace_inter (B.seam m₂) (B.isSeparating_seam m₂)
  let g₂ := G.seamTorusIn (B.seam m₂) _
    (G.leftRegion_inter_rightRegion (B.seam m₂) (B.isSeparating_seam m₂)).ge
  have hg₂ : Function.Surjective (FundamentalGroup.map
      ((interToLeft _ _).comp g₂) torusBase) := by
    have heq : (interToLeft _ _).comp g₂ = G.seamTorusToLeft (B.seam m₂) :=
      ContinuousMap.ext fun t => rfl
    rw [heq]
    exact B.surjective_map_seamTorusToLeft m₂ torusBase
  have hsurj₂ := surjective_right_of_openCover_map _ _ (G.isOpen_leftRegion _)
    (G.isOpen_rightRegion _) (G.leftRegion_union_rightRegion _) g₂ torusBase hg₂ (ιV₂ p)
  have hfinal := surjective_fundamentalGroup_map_comp _ _ p hιV₂ hsurj₂
  have heq : (subsetToAmbient _).comp ιV₂ = B.productToCarrier :=
    ContinuousMap.ext fun q => rfl
  rwa [heq] at hfinal


theorem surjective_productToCarrier_of_closed_three_cones (hclosed : d.ports = 0)
    (hcones : d.cones.length = 3) (p : B.presentation.components.piece (B.piece none)) :
    Function.Surjective (FundamentalGroup.map B.productToCarrier p) := by
  have hk := d.ports_add_fillingCount
  have hk3 := d.k_le_three
  have hf : d.fillingCount = 3 := by
    change d.ports + (d.cones.length + d.normals.length) = d.k at hk
    change d.cones.length + d.normals.length = 3
    omega
  exact B.surjective_productToCarrier_of_fillingCount_eq_three hf p

end SeifertBlock
end GC.Seifert
