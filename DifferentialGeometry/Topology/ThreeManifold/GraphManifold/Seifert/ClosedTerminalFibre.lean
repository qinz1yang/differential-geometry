import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Seifert.TerminalUnionPrimeTwo

/-!
# The fibre of a closed block is central

Chapter 5 plan P5, closed-block fibre centrality. A Seifert block has at most three fillings
(`fillingCount ≤ k ≤ 3`), and neither the zero/one-filling case
(`exists_fibreClass_commute_of_fillingCount_le_one`) nor the two-filling case
(`exists_fibreClass_commute_of_fillingCount_eq_two`) uses a free port. The new case is three
fillings, one more level of the nested van Kampen argument of the two-filling case.

Three fillings `m₀, m₁, m₂` with left regions `Lᵢ` (solid torus side) and right regions `Rᵢ`.
The middle region `R₀ ∩ R₁ ∩ R₂` is the product piece with three seam collars
(`isPathConnected_middle₃`), and three nested collar shrinks retract it π₁-bijectively onto the
product piece (`exists_bijective_middleRetraction₃`). The fibre is then central in
`R₁ ∩ R₂ = L₀ ∪ (R₀ ∩ R₁ ∩ R₂)`, in `R₂ = L₁ ∪ (R₁ ∩ R₂)` and in the block `L₂ ∪ R₂`
(`commute_of_cover` three times, moving the base point along the product piece in between;
`exists_fibreClass_commute_of_fillingCount_eq_three`). Hence every block over a closed carrier
has a central fibre class (`exists_closedFibreClass_commute`).

The data `(3, 1), (3, 1), (3, -2)` give a closed block with three cones and
`orbChi = 0 = euler` (`exists_closedData_orbChi_eq_zero_euler_eq_zero`): the nonpositive branch
of P5 cannot rely on a nonzero Euler number.
-/

set_option autoImplicit false

noncomputable section
open Set CategoryTheory DifferentialGeometry DifferentialGeometry.Topology GC.Endpoint
open GC.GraphManifold DifferentialGeometry.Topology.VanKampen
open scoped Topology ContinuousMap unitInterval

universe u

namespace GC.Seifert

namespace SeifertBlock

variable {W : CompactCarrier.{u}} {d : SeifertData} (B : SeifertBlock W d)

theorem mem_pieceImage_cases₃ {m₀ m₁ m₂ : Fin d.fillingCount}
    (hcov : ∀ n, n = m₀ ∨ n = m₁ ∨ n = m₂) (w : W.Carrier) :
    w ∈ B.presentation.pieceImage (B.piece none) ∨
      w ∈ B.presentation.pieceImage (B.piece (some m₀)) ∨
        w ∈ B.presentation.pieceImage (B.piece (some m₁)) ∨
          w ∈ B.presentation.pieceImage (B.piece (some m₂)) := by
  obtain ⟨i, hi⟩ := B.presentation.exists_mem_pieceImage w
  rw [← B.piece.apply_symm_apply i] at hi
  rcases h : B.piece.symm i with _ | n
  · rw [h] at hi
    exact Or.inl hi
  · rw [h] at hi
    rcases hcov n with rfl | rfl | rfl
    · exact Or.inr (Or.inl hi)
    · exact Or.inr (Or.inr (Or.inl hi))
    · exact Or.inr (Or.inr (Or.inr hi))

theorem seamCollar_subset_middle₃ {m₀ m₁ m₂ : Fin d.fillingCount} (h01 : m₀ ≠ m₁)
    (h02 : m₀ ≠ m₂) (h12 : m₁ ≠ m₂) :
    B.presentation.seamCollar (B.seam m₀) ⊆ B.presentation.rightRegion (B.seam m₀) ∩
      B.presentation.rightRegion (B.seam m₁) ∩ B.presentation.rightRegion (B.seam m₂) ∧
    B.presentation.seamCollar (B.seam m₁) ⊆ B.presentation.rightRegion (B.seam m₀) ∩
      B.presentation.rightRegion (B.seam m₁) ∩ B.presentation.rightRegion (B.seam m₂) ∧
    B.presentation.seamCollar (B.seam m₂) ⊆ B.presentation.rightRegion (B.seam m₀) ∩
      B.presentation.rightRegion (B.seam m₁) ∩ B.presentation.rightRegion (B.seam m₂) :=
  ⟨fun _ hw => ⟨⟨Or.inr hw, B.seamCollar_subset_rightRegion (Ne.symm h01) hw⟩,
      B.seamCollar_subset_rightRegion (Ne.symm h02) hw⟩,
    fun _ hw => ⟨⟨B.seamCollar_subset_rightRegion h01 hw, Or.inr hw⟩,
      B.seamCollar_subset_rightRegion (Ne.symm h12) hw⟩,
    fun _ hw => ⟨⟨B.seamCollar_subset_rightRegion h02 hw,
      B.seamCollar_subset_rightRegion h12 hw⟩, Or.inr hw⟩⟩

theorem pieceImage_none_subset_middle₃ (m₀ m₁ m₂ : Fin d.fillingCount) :
    B.presentation.pieceImage (B.piece none) ⊆ B.presentation.rightRegion (B.seam m₀) ∩
      B.presentation.rightRegion (B.seam m₁) ∩ B.presentation.rightRegion (B.seam m₂) :=
  fun _ hw => ⟨⟨B.pieceImage_subset_rightRegion m₀ (B.piece_some_ne_none m₀) hw,
    B.pieceImage_subset_rightRegion m₁ (B.piece_some_ne_none m₁) hw⟩,
    B.pieceImage_subset_rightRegion m₂ (B.piece_some_ne_none m₂) hw⟩

theorem isPathConnected_middle₃ {m₀ m₁ m₂ : Fin d.fillingCount} (h01 : m₀ ≠ m₁)
    (h02 : m₀ ≠ m₂) (h12 : m₁ ≠ m₂) (hcov : ∀ n, n = m₀ ∨ n = m₁ ∨ n = m₂) :
    IsPathConnected (B.presentation.rightRegion (B.seam m₀) ∩
      B.presentation.rightRegion (B.seam m₁) ∩ B.presentation.rightRegion (B.seam m₂)) := by
  have := B.connectedSpace
  obtain ⟨hC₀, hC₁, hC₂⟩ := B.seamCollar_subset_middle₃ h01 h02 h12
  have heq : B.presentation.rightRegion (B.seam m₀) ∩ B.presentation.rightRegion (B.seam m₁) ∩
      B.presentation.rightRegion (B.seam m₂) =
      B.presentation.pieceImage (B.piece none) ∪ B.presentation.seamCollar (B.seam m₀) ∪
        B.presentation.seamCollar (B.seam m₁) ∪ B.presentation.seamCollar (B.seam m₂) := by
    refine Subset.antisymm (fun w hw => ?_) (union_subset (union_subset (union_subset
      (B.pieceImage_none_subset_middle₃ m₀ m₁ m₂) hC₀) hC₁) hC₂)
    rcases B.mem_pieceImage_cases₃ hcov w with h | h | h | h
    · exact Or.inl (Or.inl (Or.inl h))
    · exact Or.inl (Or.inl (Or.inr (B.rightRegion_inter_pieceImage_subset m₀ ⟨hw.1.1, h⟩)))
    · exact Or.inl (Or.inr (B.rightRegion_inter_pieceImage_subset m₁ ⟨hw.1.2, h⟩))
    · exact Or.inr (B.rightRegion_inter_pieceImage_subset m₂ ⟨hw.2, h⟩)
  rw [heq]
  exact (((B.presentation.isPathConnected_pieceImage _).union
    (B.presentation.isPathConnected_seamCollar _)
    ⟨_, B.seamSurface_subset_pieceImage_none m₀ ⟨torusBase, rfl⟩,
      B.presentation.seamTorus_mem_seamCollar _ torusBase⟩).union
    (B.presentation.isPathConnected_seamCollar _)
    ⟨_, Or.inl (B.seamSurface_subset_pieceImage_none m₁ ⟨torusBase, rfl⟩),
      B.presentation.seamTorus_mem_seamCollar _ torusBase⟩).union
    (B.presentation.isPathConnected_seamCollar _)
    ⟨_, Or.inl (Or.inl (B.seamSurface_subset_pieceImage_none m₂ ⟨torusBase, rfl⟩)),
      B.presentation.seamTorus_mem_seamCollar _ torusBase⟩

theorem exists_bijective_middleRetraction₃ {m₀ m₁ m₂ : Fin d.fillingCount} (h01 : m₀ ≠ m₁)
    (h02 : m₀ ≠ m₂) (h12 : m₁ ≠ m₂) (hcov : ∀ n, n = m₀ ∨ n = m₁ ∨ n = m₂) :
    ∃ f : C(↥(B.presentation.rightRegion (B.seam m₀) ∩ B.presentation.rightRegion (B.seam m₁) ∩
        B.presentation.rightRegion (B.seam m₂)), B.presentation.components.piece (B.piece none)),
      (∀ y, Function.Bijective (FundamentalGroup.map f y)) ∧
        ∀ (x : B.presentation.components.piece (B.piece none)) (hx : B.presentation.cutMap x ∈
          B.presentation.rightRegion (B.seam m₀) ∩ B.presentation.rightRegion (B.seam m₁) ∩
            B.presentation.rightRegion (B.seam m₂)),
          f ⟨B.presentation.cutMap x, hx⟩ = x := by
  have hS₀ := B.pieceImage_inter_solid m₀
  have hS₁ := B.pieceImage_inter_solid m₁
  have hS₂ := B.pieceImage_inter_solid m₂
  rw [B.leftPiece_seam] at hS₀ hS₁ hS₂
  obtain ⟨hc₀, hc₁, hc₂⟩ := B.seamCollar_subset_middle₃ h01 h02 h12
  set G := B.presentation with hG
  set M := G.rightRegion (B.seam m₀) ∩ G.rightRegion (B.seam m₁) ∩ G.rightRegion (B.seam m₂)
    with hM
  obtain ⟨φ₁, h1A, h1B⟩ := G.exists_collarShrinkHomotopy_ite (B.seam m₂) (U := M)
    (G.isClosed_pieceImage _) (G.isClosed_pieceComplImage _)
    (G.mem_pieceImage_or_mem_pieceComplImage (B.piece (some m₂))) hS₂
    (fun w hw => B.rightRegion_inter_pieceImage_subset m₂ ⟨hw.1.2, hw.2⟩)
    ⟨fun p => p.2.1, continuous_subtype_val.comp continuous_snd⟩ (fun _ _ _ => rfl)
  obtain ⟨φ₂, h2A, h2B⟩ := G.exists_collarShrinkHomotopy_ite (B.seam m₁) (U := M)
    (G.isClosed_pieceImage _) (G.isClosed_pieceComplImage _)
    (G.mem_pieceImage_or_mem_pieceComplImage (B.piece (some m₁))) hS₁
    (fun w hw => B.rightRegion_inter_pieceImage_subset m₁ ⟨hw.1.1.2, hw.2⟩) φ₁
    (fun τ u hu => h1B τ u (G.pieceImage_subset_pieceComplImage
      (B.piece_some_ne_some (Ne.symm h12)) (B.seamSurface_subset_pieceImage_some m₁ hu)))
  obtain ⟨φ₃, h3A, h3B⟩ := G.exists_collarShrinkHomotopy_ite (B.seam m₀) (U := M)
    (G.isClosed_pieceImage _) (G.isClosed_pieceComplImage _)
    (G.mem_pieceImage_or_mem_pieceComplImage (B.piece (some m₀))) hS₀
    (fun w hw => B.rightRegion_inter_pieceImage_subset m₀ ⟨hw.1.1.1, hw.2⟩) φ₂
    (fun τ u hu => (h2B τ u (G.pieceImage_subset_pieceComplImage
      (B.piece_some_ne_some (Ne.symm h01)) (B.seamSurface_subset_pieceImage_some m₀ hu))).trans
      (h1B τ u (G.pieceImage_subset_pieceComplImage
        (B.piece_some_ne_some (Ne.symm h02)) (B.seamSurface_subset_pieceImage_some m₀ hu))))
  have hcases : ∀ (τ : I) (u : M),
      (φ₃ (τ, u) = u.1 ∧ u.1 ∈ G.pieceImage (B.piece none)) ∨
        (φ₃ (τ, u) = G.collarShrink (B.seam m₀) (τ, u.1) ∧ u.1 ∈ G.seamCollar (B.seam m₀)) ∨
        (φ₃ (τ, u) = G.collarShrink (B.seam m₁) (τ, u.1) ∧ u.1 ∈ G.seamCollar (B.seam m₁)) ∨
        (φ₃ (τ, u) = G.collarShrink (B.seam m₂) (τ, u.1) ∧
          u.1 ∈ G.seamCollar (B.seam m₂)) := by
    intro τ u
    have k₀ : u.1 ∈ G.pieceImage (B.piece (some m₀)) →
        φ₃ (τ, u) = G.collarShrink (B.seam m₀) (τ, u.1) ∧ u.1 ∈ G.seamCollar (B.seam m₀) :=
      fun h => ⟨h3A τ u h, B.rightRegion_inter_pieceImage_subset m₀ ⟨u.2.1.1, h⟩⟩
    rcases B.mem_pieceImage_cases₃ hcov u.1 with h | h | h | h
    · refine Or.inl ⟨?_, h⟩
      exact ((h3B τ u (G.pieceImage_subset_pieceComplImage (B.piece_some_ne_none m₀) h)).trans
        (h2B τ u (G.pieceImage_subset_pieceComplImage (B.piece_some_ne_none m₁) h))).trans
        (h1B τ u (G.pieceImage_subset_pieceComplImage (B.piece_some_ne_none m₂) h))
    · exact Or.inr (Or.inl (k₀ h))
    · rcases G.mem_pieceImage_or_mem_pieceComplImage (B.piece (some m₀)) u.1 with h' | h'
      · exact Or.inr (Or.inl (k₀ h'))
      · exact Or.inr (Or.inr (Or.inl ⟨(h3B τ u h').trans (h2A τ u h),
          B.rightRegion_inter_pieceImage_subset m₁ ⟨u.2.1.2, h⟩⟩))
    · rcases G.mem_pieceImage_or_mem_pieceComplImage (B.piece (some m₀)) u.1 with h' | h'
      · exact Or.inr (Or.inl (k₀ h'))
      · rcases G.mem_pieceImage_or_mem_pieceComplImage (B.piece (some m₁)) u.1 with h'' | h''
        · exact Or.inr (Or.inr (Or.inl ⟨(h3B τ u h').trans (h2A τ u h''),
            B.rightRegion_inter_pieceImage_subset m₁ ⟨u.2.1.2, h''⟩⟩))
        · exact Or.inr (Or.inr (Or.inr ⟨((h3B τ u h').trans (h2B τ u h'')).trans (h1A τ u h),
            B.rightRegion_inter_pieceImage_subset m₂ ⟨u.2.2, h⟩⟩))
  refine G.exists_bijective_retraction_of_deformation (B.piece none)
    (G.injOn_cutMap_of_ne B.leftPiece_ne_rightPiece _)
    (B.pieceImage_none_subset_middle₃ m₀ m₁ m₂) φ₃ ?_ ?_ ?_ ?_
  · intro p
    rcases hcases p.1 p.2 with ⟨h, -⟩ | ⟨h, hc⟩ | ⟨h, hc⟩ | ⟨h, hc⟩
    · rw [h]
      exact p.2.2
    · rw [h]
      exact hc₀ (G.collarShrink_mem_seamCollar (B.seam m₀) p.1 hc)
    · rw [h]
      exact hc₁ (G.collarShrink_mem_seamCollar (B.seam m₁) p.1 hc)
    · rw [h]
      exact hc₂ (G.collarShrink_mem_seamCollar (B.seam m₂) p.1 hc)
  · intro u
    rcases hcases 0 u with ⟨h, -⟩ | ⟨h, hc⟩ | ⟨h, hc⟩ | ⟨h, hc⟩
    · exact h
    · rw [h]
      exact G.collarShrink_zero (B.seam m₀) hc
    · rw [h]
      exact G.collarShrink_zero (B.seam m₁) hc
    · rw [h]
      exact G.collarShrink_zero (B.seam m₂) hc
  · intro u
    rcases hcases 1 u with ⟨h, hk⟩ | ⟨h, -⟩ | ⟨h, -⟩ | ⟨h, -⟩
    · rw [h]
      exact hk
    · rw [h]
      exact B.seamSurface_subset_pieceImage_none m₀ (G.collarShrink_one_mem_seamSurface _ _)
    · rw [h]
      exact B.seamSurface_subset_pieceImage_none m₁ (G.collarShrink_one_mem_seamSurface _ _)
    · rw [h]
      exact B.seamSurface_subset_pieceImage_none m₂ (G.collarShrink_one_mem_seamSurface _ _)
  · intro u hu
    exact ((h3B 1 u (G.pieceImage_subset_pieceComplImage (B.piece_some_ne_none m₀) hu)).trans
      (h2B 1 u (G.pieceImage_subset_pieceComplImage (B.piece_some_ne_none m₁) hu))).trans
      (h1B 1 u (G.pieceImage_subset_pieceComplImage (B.piece_some_ne_none m₂) hu))

theorem exists_fibreClass_commute_of_fillingCount_eq_three (h3 : d.fillingCount = 3) :
    ∃ p, ∀ g : FundamentalGroup W.Carrier (B.productToCarrier p),
      g * B.fibreClass p = B.fibreClass p * g := by
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
  let t₀ : Torus := (1, 1)
  have hval : ∀ (m : Fin d.fillingCount) (w : Torus),
      B.productToCarrier (B.product.portMap (B.port (.inr m)) w) =
        G.seamTorus (B.seam m) ((G.pairing.matching (B.seam m)).symm w) := by
    intro m w
    rw [G.seamTorus_eq_cutMap_right, Diffeomorph.apply_symm_apply]
    change G.cutMap (B.product.portMap (B.port (.inr m)) w : G.cutCarrier.Carrier) = _
    rw [B.portMap_filled_val]
  have hloop : ∀ (m : Fin d.fillingCount) (w : Torus) (θ : I),
      B.productToCarrier (B.product.turn (θ, B.product.portMap (B.port (.inr m)) w)) ∈
        G.seamCollar (B.seam m) := by
    intro m w θ
    rw [B.product.turn_portMap, hval]
    exact G.seamTorus_mem_seamCollar _ _
  let p₀ := B.product.portMap (B.port (.inr m₀)) (G.pairing.matching (B.seam m₀) t₀)
  let p₁ := B.product.portMap (B.port (.inr m₁)) (G.pairing.matching (B.seam m₁) t₀)
  let p₂ := B.product.portMap (B.port (.inr m₂)) (G.pairing.matching (B.seam m₂) t₀)
  refine ⟨p₂, ?_⟩
  have := G.pathConnectedSpace_piece (B.piece none)
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
  have hid : Function.Bijective (FundamentalGroup.map (f'.comp ιV₀) p₀) := by
    rw [hcomp]
    exact bijective_map_homeomorph (Homeomorph.refl _) p₀
  rw [GC.Topology.fundamentalGroup_map_comp, MonoidHom.coe_comp] at hid
  have hf' : Function.Bijective (FundamentalGroup.map f' (ιV₀ p₀)) := by
    change Function.Bijective (FundamentalGroup.map (fM.comp ⟨eM, eM.continuous⟩) (ιV₀ p₀))
    rw [GC.Topology.fundamentalGroup_map_comp, MonoidHom.coe_comp]
    exact (hfMb _).comp (bijective_map_homeomorph eM _)
  have hιV₀ : Function.Bijective (FundamentalGroup.map ιV₀ p₀) :=
    (Function.Bijective.of_comp_iff' hf' _).mp hid
  have hinner₀ := commute_of_cover _ _
    ((G.isOpen_leftRegion _).preimage continuous_subtype_val)
    ((((G.isOpen_rightRegion _).inter (G.isOpen_rightRegion _)).inter
      (G.isOpen_rightRegion _)).preimage continuous_subtype_val)
    hcov₀ B.product.turn ιV₀ p₀
    (fun u a b => by
      let e := preimageValHomeo _ _ hL₀N
      have hinj := (bijective_map_homeomorph e u).1
      have hc := B.commute_leftRegion m₀ (e u)
      apply hinj
      rw [map_mul, map_mul]
      exact hc _ _)
    (fun g => commute_map_of_surjective ιV₀ p₀ hιV₀.2 _ (commute_turnLoop _ p₀) g)
    (fun θ => Or.inr (hloop m₀ _ θ))
  have hcen₀ := commute_iff_of_conj _ _ _ (turnLoop_naturality B.product.turn
    ((subsetToAmbient _).comp ιV₀) (PathConnectedSpace.somePath p₀ p₁)) hinner₀
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
  have hinner₁ := commute_of_cover _ _
    ((G.isOpen_leftRegion _).preimage continuous_subtype_val)
    (((G.isOpen_rightRegion _).inter (G.isOpen_rightRegion _)).preimage continuous_subtype_val)
    hcov₁ B.product.turn ιV₁ p₁
    (fun u a b => by
      let e := preimageValHomeo _ _ hL₁R₂
      have hinj := (bijective_map_homeomorph e u).1
      have hc := B.commute_leftRegion m₁ (e u)
      apply hinj
      rw [map_mul, map_mul]
      exact hc _ _)
    (fun g => by
      have h := commute_map_of_surjective (e₁ : C(↥(G.rightRegion (B.seam m₁) ∩
        G.rightRegion (B.seam m₂)), ↥(Subtype.val ⁻¹' (G.rightRegion (B.seam m₁) ∩
          G.rightRegion (B.seam m₂)) : Set (G.rightRegion (B.seam m₂))))) _
        (bijective_map_homeomorph e₁ _).2 _ hcen₀ g
      rwa [← MonoidHom.comp_apply, ← GC.Topology.fundamentalGroup_map_comp] at h)
    (fun θ => Or.inr (hloop m₁ _ θ))
  have hcen₁ := commute_iff_of_conj _ _ _ (turnLoop_naturality B.product.turn
    ((subsetToAmbient _).comp ιV₁) (PathConnectedSpace.somePath p₁ p₂)) hinner₁
  have := isPathConnected_iff_pathConnectedSpace.mp (G.isPathConnected_leftRegion (B.seam m₂))
  have := isPathConnected_iff_pathConnectedSpace.mp (G.isPathConnected_rightRegion (B.seam m₂))
  have := G.pathConnectedSpace_inter (B.seam m₂) (B.isSeparating_seam m₂)
  intro g
  exact commute_of_cover _ _ (G.isOpen_leftRegion _) (G.isOpen_rightRegion _)
    (G.leftRegion_union_rightRegion _) B.product.turn ((subsetToAmbient _).comp ιV₁) p₂
    (B.commute_leftRegion m₂) hcen₁ (fun θ => Or.inr (hloop m₂ _ θ)) g

end SeifertBlock

theorem exists_closedFibreClass_commute (Q : ConnectedClosedOrientedManifold.{u} 3)
    (d : SeifertData) (B : SeifertBlock (NoCuts.carrier Q) d) (hclosed : d.ports = 0) :
    ∃ p : B.presentation.components.piece (B.piece none),
      ∀ g : FundamentalGroup Q.Carrier (B.productToCarrier p),
        g * B.fibreClass p = B.fibreClass p * g := by
  have hk := d.ports_add_fillingCount
  rw [hclosed, zero_add] at hk
  have hk3 := d.k_le_three
  rcases (by omega : d.fillingCount ≤ 1 ∨ d.fillingCount = 2 ∨ d.fillingCount = 3) with
    h | h | h
  · exact B.exists_fibreClass_commute_of_fillingCount_le_one h
  · exact B.exists_fibreClass_commute_of_fillingCount_eq_two h
  · exact B.exists_fibreClass_commute_of_fillingCount_eq_three h

theorem exists_closedData_orbChi_eq_zero_euler_eq_zero :
    ∃ d : SeifertData, d.ports = 0 ∧ d.cones = [(3, 1), (3, 1), (3, -2)] ∧ d.normals = [] ∧
      d.orbChi = 0 ∧ d.euler = 0 := by
  refine ⟨⟨3, 0, [(3, 1), (3, 1), (3, -2)], [], by norm_num, le_rfl, ?_, ?_, rfl⟩,
    rfl, rfl, rfl, ?_, ?_⟩
  · intro c hc
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with rfl | rfl | rfl <;> norm_num
  · intro c hc
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with rfl | rfl | rfl <;> norm_num
  · norm_num [SeifertData.orbChi]
  · norm_num [SeifertData.euler]

end GC.Seifert
