import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Seifert.TerminalUnionPrimeVertex

/-!
# The fibre of a block with two fillings is central

Chapter 5 plan P4, the vertex condition of T2 for blocks with two fillings (and one free port).

Deformations. `exists_collarShrinkHomotopy_ite` is the homotopy form of K10e's
`exists_collarShrink_ite`: the collar shrink of one seam on a closed part, a given homotopy on the
other. A deformation of an open set `U` into the image of a piece `i`, fixing that image, makes the
induced retraction onto the piece a π₁-bijection (`exists_bijective_retraction_of_deformation`,
the homotopy-equivalence half of `exists_regionRetraction` of `TwoSolidTori.lean`). For a block
this gives π₁-bijective retractions of the left region of a filling seam onto its solid torus
(`exists_bijective_leafRetraction`) and, for two fillings, of the middle region
`R₀ ∩ R₁` onto the product piece (`exists_bijective_middleRetraction`).

Centrality. `commute_of_cover`: if a space is covered by open path-connected `U`, `V` with
path-connected intersection, `π₁ U` is commutative, a fibre loop pushed into `V` is central in
`π₁ V` and runs in `U ∩ V`, then it is central in the whole space. For two fillings this is
applied inside `R₁ = L₀ ∪ (R₀ ∩ R₁)` and then to `W = L₁ ∪ R₁`
(`exists_fibreClass_commute_of_fillingCount_eq_two`). With the zero- and one-filling cases every
good block with a free port has freely indecomposable, non-cyclic π₁
(`SeifertBlock.indecomposableNoncyclic`).
-/

set_option autoImplicit false

noncomputable section
open Set CategoryTheory DifferentialGeometry DifferentialGeometry.Topology GC.Endpoint
open GC.GraphManifold DifferentialGeometry.Topology.VanKampen
open scoped Topology ContinuousMap unitInterval

universe u

namespace GC.Seifert

namespace TorusPresentation

variable {W : CompactCarrier.{u}} (G : TorusPresentation W) (j : Fin G.pairing.count)

theorem exists_collarShrinkHomotopy_ite {U : Set W.Carrier} {A B : Set W.Carrier}
    (hA : IsClosed A) (hB : IsClosed B) (hAB : ∀ w, w ∈ A ∨ w ∈ B)
    (hABS : A ∩ B ⊆ G.seamSurface j) (hUA : U ∩ A ⊆ G.seamCollar j) (g : C(I × U, W.Carrier))
    (hg : ∀ (τ : I) (u : U), u.1 ∈ G.seamSurface j → g (τ, u) = u.1) :
    ∃ φ : C(I × U, W.Carrier),
      (∀ (τ : I) (u : U), u.1 ∈ A → φ (τ, u) = G.collarShrink j (τ, u.1)) ∧
        ∀ (τ : I) (u : U), u.1 ∈ B → φ (τ, u) = g (τ, u) := by
  classical
  have hshrink : ContinuousOn (fun p : I × U => G.collarShrink j (p.1, p.2.1))
      {p | p.2.1 ∈ A} :=
    (G.continuousOn_collarShrink j).comp (continuous_fst.prodMk
      (continuous_subtype_val.comp continuous_snd)).continuousOn
      fun p hp => ⟨trivial, hUA ⟨p.2.2, hp⟩⟩
  have heq : ∀ p : I × U, p.2.1 ∈ A → p.2.1 ∈ B → g p = G.collarShrink j (p.1, p.2.1) :=
    fun p hA hB => (hg p.1 p.2 (hABS ⟨hA, hB⟩)).trans
      (G.collarShrink_of_mem_seamSurface j p.1 (hABS ⟨hA, hB⟩)).symm
  let φ : I × U → W.Carrier := fun p =>
    if p.2.1 ∈ B then g p else G.collarShrink j (p.1, p.2.1)
  have hφA : ∀ p : I × U, p.2.1 ∈ A → φ p = G.collarShrink j (p.1, p.2.1) := by
    intro p hp
    by_cases hb : p.2.1 ∈ B
    · simp only [φ, hb, ↓reduceIte]
      exact heq p hp hb
    · simp only [φ, hb, ↓reduceIte]
  have hφB : ∀ p : I × U, p.2.1 ∈ B → φ p = g p := fun p hp => by
    simp only [φ, hp, ↓reduceIte]
  have hcont : Continuous φ := by
    have hA' : IsClosed {p : I × U | p.2.1 ∈ A} :=
      hA.preimage (continuous_subtype_val.comp continuous_snd)
    have hB' : IsClosed {p : I × U | p.2.1 ∈ B} :=
      hB.preimage (continuous_subtype_val.comp continuous_snd)
    have hcov : {p : I × U | p.2.1 ∈ A} ∪ {p : I × U | p.2.1 ∈ B} = univ :=
      eq_univ_of_forall fun p => hAB p.2.1
    rw [← continuousOn_univ, ← hcov]
    exact ContinuousOn.union_of_isClosed (hshrink.congr fun p hp => hφA p hp)
      (g.continuous.continuousOn.congr fun p hp => hφB p hp) hA' hB'
  exact ⟨⟨φ, hcont⟩, fun τ u hu => hφA (τ, u) hu, fun τ u hu => hφB (τ, u) hu⟩

theorem exists_bijective_retraction_of_deformation (i : Fin G.components.count)
    (hinj : InjOn G.cutMap (G.components.piece i : Set G.cutCarrier.Carrier))
    {U : Set W.Carrier} (hKU : G.pieceImage i ⊆ U) (R : C(I × U, W.Carrier))
    (hRU : ∀ p, R p ∈ U) (hR0 : ∀ u : U, R (0, u) = u.1)
    (hR1 : ∀ u : U, R (1, u) ∈ G.pieceImage i)
    (hRK : ∀ u : U, u.1 ∈ G.pieceImage i → R (1, u) = u.1) :
    ∃ f : C(U, G.components.piece i), (∀ y, Function.Bijective (FundamentalGroup.map f y)) ∧
      ∀ (x : G.components.piece i) (hx : G.cutMap x ∈ U), f ⟨G.cutMap x, hx⟩ = x := by
  have : CompactSpace (G.components.piece i) :=
    isCompact_iff_compactSpace.mp (G.components.piece_compact i)
  let c : C(G.components.piece i, W.Carrier) :=
    ⟨fun x => G.cutMap x, G.continuous_cutMap.comp continuous_subtype_val⟩
  have hcinj : Function.Injective c := fun x y h => Subtype.ext (hinj x.2 y.2 h)
  have hemb : Topology.IsEmbedding c := (c.continuous.isClosedEmbedding hcinj).isEmbedding
  have hrange : range c = G.pieceImage i := by
    ext w
    constructor
    · rintro ⟨x, rfl⟩
      exact ⟨x, x.2, rfl⟩
    · rintro ⟨x, hx, rfl⟩
      exact ⟨⟨x, hx⟩, rfl⟩
  have hR1' : ∀ u : U, R (1, u) ∈ range c := fun u => hrange ▸ hR1 u
  let e := hemb.toHomeomorph
  have key : ∀ (w : W.Carrier) (hw : w ∈ range c) (x : G.components.piece i), w = c x →
      e.symm ⟨w, hw⟩ = x := by
    rintro w hw x rfl
    exact hemb.toHomeomorph_symm_apply x
  let f : C(U, G.components.piece i) :=
    ⟨fun u => e.symm ⟨R (1, u), hR1' u⟩, e.symm.continuous.comp
      ((R.continuous.comp (continuous_const.prodMk continuous_id)).subtype_mk _)⟩
  let g : C(G.components.piece i, U) :=
    ⟨fun x => ⟨c x, hKU ⟨x, x.2, rfl⟩⟩, c.continuous.subtype_mk _⟩
  have hfg : ∀ x, f (g x) = x := fun x => key _ _ x (hRK (g x) ⟨x, x.2, rfl⟩)
  have hgf : ∀ u, (g (f u)).1 = R (1, u) := fun u =>
    congrArg Subtype.val (e.apply_symm_apply ⟨R (1, u), hR1' u⟩)
  let H : ContinuousMap.Homotopy (ContinuousMap.id U) (g.comp f) :=
    { toFun := fun p => ⟨R p, hRU p⟩
      continuous_toFun := R.continuous.subtype_mk _
      map_zero_left := fun u => Subtype.ext (hR0 u)
      map_one_left := fun u => Subtype.ext (hgf u).symm }
  let E : ContinuousMap.HomotopyEquiv U (G.components.piece i) :=
    { toFun := f
      invFun := g
      left_inv := ⟨H.symm⟩
      right_inv := by
        rw [show f.comp g = ContinuousMap.id _ from ContinuousMap.ext hfg] }
  refine ⟨f, fun y => ?_, fun x hx => hfg x⟩
  have h : Function.Bijective (FundamentalGroup.mapOfEq f (rfl : f y = f y)) :=
    fundamentalGroup_mapOfEq_bijective_of_homotopyEquiv E y (f y) rfl
  rwa [mapOfEq_rfl'] at h

end TorusPresentation

section CoverFibre
variable {X : Type u} [TopologicalSpace X] {Y : Type*} [TopologicalSpace Y]

theorem commute_of_cover (U V : Set X) (hU : IsOpen U) (hV : IsOpen V) (hcov : U ∪ V = univ)
    [PathConnectedSpace U] [PathConnectedSpace V] [PathConnectedSpace ↑(U ∩ V)]
    (H : (ContinuousMap.id Y).Homotopy (ContinuousMap.id Y)) (ιV : C(Y, V)) (y : Y)
    (hcomm : ∀ (u : U) (a b : FundamentalGroup U u), a * b = b * a)
    (hcen : ∀ g : FundamentalGroup V (ιV y),
      g * FundamentalGroup.map ιV y (turnLoop H y) =
        FundamentalGroup.map ιV y (turnLoop H y) * g)
    (hmem : ∀ θ : I, (ιV (H (θ, y)) : X) ∈ U)
    (g : FundamentalGroup X ((subsetToAmbient V).comp ιV y)) :
    g * FundamentalGroup.map ((subsetToAmbient V).comp ιV) y (turnLoop H y) =
      FundamentalGroup.map ((subsetToAmbient V).comp ιV) y (turnLoop H y) * g := by
  have hy0 : (ιV y : X) ∈ U := by
    have h := hmem 0
    rw [H.apply_zero, ContinuousMap.id_apply] at h
    exact h
  let x : ↑(U ∩ V) := ⟨(ιV y : X), hy0, (ιV y).2⟩
  let γ : Path x x :=
    { toFun := fun θ => ⟨(ιV (H (θ, y)) : X), hmem θ, (ιV (H (θ, y))).2⟩
      continuous_toFun := ((continuous_subtype_val.comp (ιV.continuous.comp H.continuous)).comp
        (continuous_id.prodMk continuous_const)).subtype_mk _
      source' := Subtype.ext (congrArg (fun z => (ιV z : X)) (H.apply_zero y))
      target' := Subtype.ext (congrArg (fun z => (ιV z : X)) (H.apply_one y)) }
  let c : FundamentalGroup ↑(U ∩ V) x := FundamentalGroup.fromPath (Path.Homotopic.Quotient.mk γ)
  have hcW : FundamentalGroup.map (subsetToAmbient (U ∩ V)) x c =
      FundamentalGroup.map ((subsetToAmbient V).comp ιV) y (turnLoop H y) := by
    change Path.Homotopic.Quotient.mk (γ.map (subsetToAmbient (U ∩ V)).continuous) =
      Path.Homotopic.Quotient.mk ((H.evalAt y).map ((subsetToAmbient V).comp ιV).continuous)
    congr 1
  have hcR : FundamentalGroup.map (interToRight U V) x c =
      FundamentalGroup.map ιV y (turnLoop H y) := by
    change Path.Homotopic.Quotient.mk (γ.map (interToRight U V).continuous) =
      Path.Homotopic.Quotient.mk ((H.evalAt y).map ιV.continuous)
    congr 1
  have key := commute_of_openCover U V hU hV hcov x c (fun a => hcomm _ a _)
    (fun b => by
      rw [hcR]
      exact hcen b) g
  rw [hcW] at key
  exact key

end CoverFibre

namespace SeifertBlock

variable {W : CompactCarrier.{u}} {d : SeifertData} (B : SeifertBlock W d)

theorem exists_bijective_leafRetraction (m : Fin d.fillingCount) :
    ∃ f : C(B.presentation.leftRegion (B.seam m),
        B.presentation.components.piece (B.piece (some m))),
      ∀ y, Function.Bijective (FundamentalGroup.map f y) := by
  have hS := B.pieceImage_inter_solid m
  have hU := B.presentation.leftRegion_inter_pieceComplImage_subset hS
  rw [B.leftPiece_seam] at hS hU
  obtain ⟨φ, hφA, hφB⟩ := B.presentation.exists_collarShrinkHomotopy_ite (B.seam m)
    (B.presentation.isClosed_pieceComplImage _) (B.presentation.isClosed_pieceImage _)
    (fun w => (B.presentation.mem_pieceImage_or_mem_pieceComplImage (B.piece (some m)) w).symm)
    (fun w hw => hS ⟨hw.2, hw.1⟩) hU
    ⟨fun p => p.2.1, continuous_subtype_val.comp continuous_snd⟩ (fun _ _ _ => rfl)
  have hcases : ∀ (τ : I) (u : B.presentation.leftRegion (B.seam m)),
      (φ (τ, u) = u.1 ∧ u.1 ∈ B.presentation.pieceImage (B.piece (some m))) ∨
        (φ (τ, u) = B.presentation.collarShrink (B.seam m) (τ, u.1) ∧
          u.1 ∈ B.presentation.seamCollar (B.seam m)) := by
    intro τ u
    rcases B.presentation.mem_pieceImage_or_mem_pieceComplImage (B.piece (some m)) u.1 with h | h
    · exact Or.inl ⟨hφB τ u h, h⟩
    · exact Or.inr ⟨hφA τ u h, hU ⟨u.2, h⟩⟩
  obtain ⟨f, hf, -⟩ := B.presentation.exists_bijective_retraction_of_deformation (B.piece (some m))
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
  exact ⟨f, hf⟩

theorem exists_bijective_middleRetraction {m m' : Fin d.fillingCount} (hmm : m ≠ m')
    (hcov : ∀ n, n = m ∨ n = m') :
    ∃ f : C(↥(B.presentation.rightRegion (B.seam m) ∩ B.presentation.rightRegion (B.seam m')),
        B.presentation.components.piece (B.piece none)),
      (∀ y, Function.Bijective (FundamentalGroup.map f y)) ∧
        ∀ (x : B.presentation.components.piece (B.piece none)) (hx : B.presentation.cutMap x ∈
          B.presentation.rightRegion (B.seam m) ∩ B.presentation.rightRegion (B.seam m')),
          f ⟨B.presentation.cutMap x, hx⟩ = x := by
  have hS := B.pieceImage_inter_solid m
  have hS' := B.pieceImage_inter_solid m'
  rw [B.leftPiece_seam] at hS hS'
  obtain ⟨φ₁, h1A, h1B⟩ := B.presentation.exists_collarShrinkHomotopy_ite (B.seam m')
    (U := B.presentation.rightRegion (B.seam m) ∩ B.presentation.rightRegion (B.seam m'))
    (B.presentation.isClosed_pieceImage _) (B.presentation.isClosed_pieceComplImage _)
    (B.presentation.mem_pieceImage_or_mem_pieceComplImage (B.piece (some m'))) hS'
    (fun w hw => B.rightRegion_inter_pieceImage_subset m' ⟨hw.1.2, hw.2⟩)
    ⟨fun p => p.2.1, continuous_subtype_val.comp continuous_snd⟩ (fun _ _ _ => rfl)
  obtain ⟨φ₂, h2A, h2B⟩ := B.presentation.exists_collarShrinkHomotopy_ite (B.seam m)
    (U := B.presentation.rightRegion (B.seam m) ∩ B.presentation.rightRegion (B.seam m'))
    (B.presentation.isClosed_pieceImage _) (B.presentation.isClosed_pieceComplImage _)
    (B.presentation.mem_pieceImage_or_mem_pieceComplImage (B.piece (some m))) hS
    (fun w hw => B.rightRegion_inter_pieceImage_subset m ⟨hw.1.1, hw.2⟩) φ₁
    (fun τ u hu => h1B τ u (B.presentation.pieceImage_subset_pieceComplImage
      (B.piece_some_ne_some (Ne.symm hmm)) (B.seamSurface_subset_pieceImage_some m hu)))
  have hcm : B.presentation.seamCollar (B.seam m) ⊆
      B.presentation.rightRegion (B.seam m) ∩ B.presentation.rightRegion (B.seam m') :=
    fun w hw => ⟨Or.inr hw, B.seamCollar_subset_rightRegion (Ne.symm hmm) hw⟩
  have hcm' : B.presentation.seamCollar (B.seam m') ⊆
      B.presentation.rightRegion (B.seam m) ∩ B.presentation.rightRegion (B.seam m') :=
    fun w hw => ⟨B.seamCollar_subset_rightRegion hmm hw, Or.inr hw⟩
  have hcases : ∀ (τ : I) (u : ↥(B.presentation.rightRegion (B.seam m) ∩
      B.presentation.rightRegion (B.seam m'))),
      (φ₂ (τ, u) = u.1 ∧ u.1 ∈ B.presentation.pieceImage (B.piece none)) ∨
        (φ₂ (τ, u) = B.presentation.collarShrink (B.seam m) (τ, u.1) ∧
          u.1 ∈ B.presentation.seamCollar (B.seam m)) ∨
        (φ₂ (τ, u) = B.presentation.collarShrink (B.seam m') (τ, u.1) ∧
          u.1 ∈ B.presentation.seamCollar (B.seam m')) := by
    intro τ u
    rcases B.mem_pieceImage_cases hcov u.1 with h | h | h
    · refine Or.inl ⟨?_, h⟩
      exact (h2B τ u (B.presentation.pieceImage_subset_pieceComplImage
        (B.piece_some_ne_none m) h)).trans (h1B τ u
          (B.presentation.pieceImage_subset_pieceComplImage (B.piece_some_ne_none m') h))
    · exact Or.inr (Or.inl ⟨h2A τ u h, B.rightRegion_inter_pieceImage_subset m ⟨u.2.1, h⟩⟩)
    · rcases B.presentation.mem_pieceImage_or_mem_pieceComplImage (B.piece (some m)) u.1
        with h' | h'
      · exact Or.inr (Or.inl ⟨h2A τ u h', B.rightRegion_inter_pieceImage_subset m ⟨u.2.1, h'⟩⟩)
      · exact Or.inr (Or.inr ⟨(h2B τ u h').trans (h1A τ u h),
          B.rightRegion_inter_pieceImage_subset m' ⟨u.2.2, h⟩⟩)
  refine B.presentation.exists_bijective_retraction_of_deformation (B.piece none)
    (B.presentation.injOn_cutMap_of_ne B.leftPiece_ne_rightPiece _)
    (fun w hw => ⟨B.pieceImage_subset_rightRegion m (B.piece_some_ne_none m) hw,
      B.pieceImage_subset_rightRegion m' (B.piece_some_ne_none m') hw⟩) φ₂ ?_ ?_ ?_ ?_
  · intro p
    rcases hcases p.1 p.2 with ⟨h, -⟩ | ⟨h, hc⟩ | ⟨h, hc⟩
    · rw [h]
      exact p.2.2
    · rw [h]
      exact hcm (B.presentation.collarShrink_mem_seamCollar (B.seam m) p.1 hc)
    · rw [h]
      exact hcm' (B.presentation.collarShrink_mem_seamCollar (B.seam m') p.1 hc)
  · intro u
    rcases hcases 0 u with ⟨h, -⟩ | ⟨h, hc⟩ | ⟨h, hc⟩
    · exact h
    · rw [h]
      exact B.presentation.collarShrink_zero (B.seam m) hc
    · rw [h]
      exact B.presentation.collarShrink_zero (B.seam m') hc
  · intro u
    rcases hcases 1 u with ⟨h, hk⟩ | ⟨h, -⟩ | ⟨h, -⟩
    · rw [h]
      exact hk
    · rw [h]
      exact B.seamSurface_subset_pieceImage_none m
        (B.presentation.collarShrink_one_mem_seamSurface _ _)
    · rw [h]
      exact B.seamSurface_subset_pieceImage_none m'
        (B.presentation.collarShrink_one_mem_seamSurface _ _)
  · intro u hu
    exact (h2B 1 u (B.presentation.pieceImage_subset_pieceComplImage
      (B.piece_some_ne_none m) hu)).trans (h1B 1 u
        (B.presentation.pieceImage_subset_pieceComplImage (B.piece_some_ne_none m') hu))

theorem commute_leftRegion (m : Fin d.fillingCount) (u : B.presentation.leftRegion (B.seam m))
    (a b : FundamentalGroup (B.presentation.leftRegion (B.seam m)) u) : a * b = b * a := by
  obtain ⟨f, hf⟩ := B.exists_bijective_leafRetraction m
  have := (B.solid m).isCyclic_fundamentalGroup (f u)
  exact commute_of_injective_isCyclic (FundamentalGroup.map f u) (hf u).1 a b

theorem exists_fibreClass_commute_of_fillingCount_eq_two (h2 : d.fillingCount = 2) :
    ∃ p, ∀ g : FundamentalGroup W.Carrier (B.productToCarrier p),
      g * B.fibreClass p = B.fibreClass p * g := by
  have hW := B.connectedSpace
  let m₀ : Fin d.fillingCount := ⟨0, by omega⟩
  let m₁ : Fin d.fillingCount := ⟨1, by omega⟩
  have hmm : m₀ ≠ m₁ := Fin.ne_of_val_ne (show (0 : ℕ) ≠ 1 from zero_ne_one)
  have hcov : ∀ n : Fin d.fillingCount, n = m₀ ∨ n = m₁ := by
    intro n
    rcases n with ⟨n, hn⟩
    rcases Nat.lt_succ_iff_lt_or_eq.mp (h2 ▸ hn : n < 2) with h | h
    · exact Or.inl (Fin.ext (Nat.lt_one_iff.mp h))
    · exact Or.inr (Fin.ext h)
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
  refine ⟨p₁, ?_⟩
  have hL₀R₁ : G.leftRegion (B.seam m₀) ⊆ G.rightRegion (B.seam m₁) :=
    B.leftRegion_subset_rightRegion (Ne.symm hmm)
  have hMR₁ : G.rightRegion (B.seam m₀) ∩ G.rightRegion (B.seam m₁) ⊆
      G.rightRegion (B.seam m₁) := inter_subset_right
  have hPM : ∀ q : G.components.piece (B.piece none), B.productToCarrier q ∈
      G.rightRegion (B.seam m₀) ∩ G.rightRegion (B.seam m₁) := fun q =>
    ⟨B.pieceImage_subset_rightRegion m₀ (B.piece_some_ne_none m₀) ⟨q.1, q.2, rfl⟩,
      B.pieceImage_subset_rightRegion m₁ (B.piece_some_ne_none m₁) ⟨q.1, q.2, rfl⟩⟩
  have hL₀M : G.leftRegion (B.seam m₀) ∩
      (G.rightRegion (B.seam m₀) ∩ G.rightRegion (B.seam m₁)) = G.seamCollar (B.seam m₀) := by
    ext w
    constructor
    · rintro ⟨hl, hr, -⟩
      rw [← G.leftRegion_inter_rightRegion (B.seam m₀) (B.isSeparating_seam m₀)]
      exact ⟨hl, hr⟩
    · intro hw
      exact ⟨Or.inr hw, Or.inr hw, B.seamCollar_subset_rightRegion (Ne.symm hmm) hw⟩
  have hcovR₁ : (Subtype.val ⁻¹' G.leftRegion (B.seam m₀) : Set (G.rightRegion (B.seam m₁))) ∪
      Subtype.val ⁻¹' (G.rightRegion (B.seam m₀) ∩ G.rightRegion (B.seam m₁)) = univ := by
    refine eq_univ_of_forall fun w => ?_
    rcases B.mem_pieceImage_cases hcov w.1 with h | h | h
    · exact Or.inr ⟨B.pieceImage_subset_rightRegion m₀ (B.piece_some_ne_none m₀) h, w.2⟩
    · exact Or.inl (B.pieceImage_solid_subset_leftRegion m₀ h)
    · have hc := B.rightRegion_inter_pieceImage_subset m₁ ⟨w.2, h⟩
      exact Or.inr ⟨B.seamCollar_subset_rightRegion hmm hc, w.2⟩
  have i1 : PathConnectedSpace (Subtype.val ⁻¹' G.leftRegion (B.seam m₀) :
      Set (G.rightRegion (B.seam m₁))) :=
    pathConnectedSpace_preimage (G.isPathConnected_leftRegion _) hL₀R₁
  have i2 : PathConnectedSpace (Subtype.val ⁻¹' (G.rightRegion (B.seam m₀) ∩
      G.rightRegion (B.seam m₁)) : Set (G.rightRegion (B.seam m₁))) :=
    pathConnectedSpace_preimage (B.isPathConnected_middle hmm hcov) hMR₁
  have i3 : PathConnectedSpace ↑((Subtype.val ⁻¹' G.leftRegion (B.seam m₀) :
      Set (G.rightRegion (B.seam m₁))) ∩ Subtype.val ⁻¹' (G.rightRegion (B.seam m₀) ∩
        G.rightRegion (B.seam m₁))) :=
    pathConnectedSpace_preimage (hL₀M ▸ G.isPathConnected_seamCollar (B.seam m₀))
      (inter_subset_left.trans hL₀R₁)
  let ιV : C(G.components.piece (B.piece none), (Subtype.val ⁻¹' (G.rightRegion (B.seam m₀) ∩
      G.rightRegion (B.seam m₁)) : Set (G.rightRegion (B.seam m₁)))) :=
    ⟨fun q => ⟨⟨B.productToCarrier q, (hPM q).2⟩, hPM q⟩,
      (B.productToCarrier.continuous.subtype_mk _).subtype_mk _⟩
  obtain ⟨fM, hfMb, hfMx⟩ := B.exists_bijective_middleRetraction hmm hcov
  let eM := preimageValHomeo _ _ hMR₁
  let f' : C(↑(Subtype.val ⁻¹' (G.rightRegion (B.seam m₀) ∩ G.rightRegion (B.seam m₁)) :
      Set (G.rightRegion (B.seam m₁))), G.components.piece (B.piece none)) :=
    fM.comp ⟨eM, eM.continuous⟩
  have hcomp : f'.comp ιV = ContinuousMap.id _ := ContinuousMap.ext fun q => hfMx q _
  have hid : Function.Bijective (FundamentalGroup.map (f'.comp ιV) p₀) := by
    rw [hcomp]
    exact bijective_map_homeomorph (Homeomorph.refl _) p₀
  rw [GC.Topology.fundamentalGroup_map_comp, MonoidHom.coe_comp] at hid
  have hf' : Function.Bijective (FundamentalGroup.map f' (ιV p₀)) := by
    change Function.Bijective (FundamentalGroup.map (fM.comp ⟨eM, eM.continuous⟩) (ιV p₀))
    rw [GC.Topology.fundamentalGroup_map_comp, MonoidHom.coe_comp]
    exact (hfMb _).comp (bijective_map_homeomorph eM _)
  have hιV : Function.Bijective (FundamentalGroup.map ιV p₀) :=
    (Function.Bijective.of_comp_iff' hf' _).mp hid
  have hinner := commute_of_cover _ _
    ((G.isOpen_leftRegion _).preimage continuous_subtype_val)
    (((G.isOpen_rightRegion _).inter (G.isOpen_rightRegion _)).preimage continuous_subtype_val)
    hcovR₁ B.product.turn ιV p₀
    (fun u a b => by
      let e := preimageValHomeo _ _ hL₀R₁
      have hinj := (bijective_map_homeomorph e u).1
      have hc := B.commute_leftRegion m₀ (e u)
      apply hinj
      rw [map_mul, map_mul]
      exact hc _ _)
    (fun g => commute_map_of_surjective ιV p₀ hιV.2 _ (commute_turnLoop _ p₀) g)
    (fun θ => Or.inr (hloop m₀ _ θ))
  have := B.presentation.pathConnectedSpace_piece (B.piece none)
  have hR₁cen := commute_iff_of_conj _ _ _ (turnLoop_naturality B.product.turn
    ((subsetToAmbient _).comp ιV) (PathConnectedSpace.somePath p₀ p₁)) hinner
  have := isPathConnected_iff_pathConnectedSpace.mp (G.isPathConnected_leftRegion (B.seam m₁))
  have := isPathConnected_iff_pathConnectedSpace.mp (G.isPathConnected_rightRegion (B.seam m₁))
  have := G.pathConnectedSpace_inter (B.seam m₁) (B.isSeparating_seam m₁)
  intro g
  exact commute_of_cover _ _ (G.isOpen_leftRegion _) (G.isOpen_rightRegion _)
    (G.leftRegion_union_rightRegion _) B.product.turn ((subsetToAmbient _).comp ιV) p₁
    (B.commute_leftRegion m₁) hR₁cen (fun θ => Or.inr (hloop m₁ _ θ)) g

theorem exists_fibreClass_commute (hp : d.ports ≠ 0) :
    ∃ p, ∀ g : FundamentalGroup W.Carrier (B.productToCarrier p),
      g * B.fibreClass p = B.fibreClass p * g := by
  have hk := d.ports_add_fillingCount
  have hk3 := d.k_le_three
  rcases (by omega : d.fillingCount ≤ 1 ∨ d.fillingCount = 2) with h | h
  · exact B.exists_fibreClass_commute_of_fillingCount_le_one h
  · exact B.exists_fibreClass_commute_of_fillingCount_eq_two h

theorem indecomposableNoncyclic (hB : B.IsGoodBlock) (hp : d.ports ≠ 0) (x : W.Carrier) :
    IndecomposableNoncyclic (FundamentalGroup W.Carrier x) :=
  B.indecomposableNoncyclic_of_commute hB hp (B.exists_fibreClass_commute hp) x

end SeifertBlock

end GC.Seifert
