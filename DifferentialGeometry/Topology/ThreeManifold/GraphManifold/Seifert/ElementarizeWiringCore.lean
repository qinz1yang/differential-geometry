import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Seifert.CoreDecompositionOrientable
import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Seifert.BaseMorseExistence

/-!
# Planar pieces and base cuts of the core decomposition

Lane P1W. Lane MD3's `exists_planarDecomposition_core_of_shrink_orientable` builds a planar
decomposition of the core `D'.core` of Morse data, but its statement forgets two facts of the
construction that the wiring needs: every piece is a model planar base
(`ElementaryBase.planar`), and every cut, a bicollar of the core, is pointwise the restriction of
a bicollar of the base `B` (the shrunk level bicollar `shrinkBicollar`, via `coreCutFun_val`).
This file repeats MD3's assembly and records its output as a `PlanarCore D`: the planar bases
`base j` with their embeddings into the core, the cuts as bicollars of `B` lying above level 0,
the cut sides with their collar formulas, the bottom sides as level bicollars, and the overlap on
the cut circles (`nonempty_planarCore_of_pieces`, `nonempty_planarCore_of_gap`,
`exists_planarCore_of_shrink`, `exists_planarCore_orientable`). For an orientable base some Morse
data has a planar core (`exists_planarCore_of_orientable`).
-/

set_option autoImplicit false

noncomputable section
open Set Function TopologicalSpace Topology Metric
open DifferentialGeometry DifferentialGeometry.Topology GC.Endpoint GC.GraphManifold
open DifferentialGeometry.Topology.Morse
open scoped Manifold ContDiff Topology

universe u

namespace GC.Seifert

structure PlanarCore {B : CompactSurface.{u}} (D : BaseMorseData B) where
  cutCount : ℕ
  cut : Fin cutCount → PartialDiffeomorph ((𝓡 1).prod 𝓘(ℝ, ℝ)) (SurfaceModel.model B.kind)
    (Circle × ℝ) B.Carrier ∞
  cut_source : ∀ c, (cut c).source = {p | -1 < p.2 ∧ p.2 < 1}
  cut_level : ∀ c t s, -1 < s → s < 1 → D.level 0 < D.f (cut c (t, s))
  pieceCount : ℕ
  kind : Fin pieceCount → ℕ
  kind_mem : ∀ j, kind j ∈ ({1, 2, 3} : Finset ℕ)
  base : ∀ j, PlanarBase.{u} (kind j)
  inclusion : ∀ j, (base j).surface.Carrier → D.core.Carrier
  isSmoothEmbedding : ∀ j, Manifold.IsSmoothEmbedding (SurfaceModel.model (base j).surface.kind)
    (SurfaceModel.model D.core.kind) ∞ (inclusion j)
  covers : ⋃ j, range (inclusion j) = univ
  cutSide : Fin cutCount → Bool → Σ j, Fin (kind j)
  cutSide_injective : Function.Injective (Function.uncurry cutSide)
  cutSide_collar : ∀ c b, ∃ σ : Circle ≃ₘ⟮𝓡 1, 𝓡 1⟯ Circle, ∀ t s (hs : 0 ≤ s), s < 1 →
    (inclusion (cutSide c b).1 ((base _).collar (cutSide c b).2 (t, halfPoint s hs))).val =
      cut c (σ t, if b then s else -s)
  bottom_collar : ∀ j l, (∀ c b, cutSide c b ≠ ⟨j, l⟩) → ∃ (x₀ : B.Carrier)
    (hx₀ : D.f x₀ = D.level 0) (σ : Circle ≃ₘ⟮𝓡 1, 𝓡 1⟯ Circle), ∀ t s (hs : 0 ≤ s), s < 1 →
      (inclusion j ((base j).collar l (t, halfPoint s hs))).val =
        Classical.choose (D.exists_levelBicollar 0 hx₀) (σ t, s)
  overlap : ∀ j j' x x', j ≠ j' → inclusion j x = inclusion j' x' →
    ∃ c t, (inclusion j x).val = cut c (t, 0)

end GC.Seifert

namespace GC.Seifert.CoreDecomposition

variable {B : CompactSurface.{u}}

section Pieces

variable (D : BaseMorseData B)
  (sp : ∀ (i : Fin D.m) (x₀ : Ambient B) (hx₀ : x₀ ∈ slabS D i), SlabPiece D i hx₀)

include sp in
theorem nonempty_planarCore_of_pieces (hgap : D.κ < D.level 1 - D.level 0) :
    Nonempty (PlanarCore D) := by
  classical
  obtain ⟨lam, hlam0, hlam1, hlamb, hlamg⟩ := exists_shrink_factor D hgap
  have hκ := D.κ_pos
  have : ∀ i, Finite (ConnectedComponents (slabS D i)) := finite_slabComponents D
  let n := Nat.card (PIdx D)
  let eP : Fin n ≃ PIdx D := (Finite.equivFin (PIdx D)).symm
  choose bc hbcs hbcr hbcf hbcc using fun (π : PIdx D) (l : Fin (pSp D sp π).k) =>
    D.exists_levelBicollar (pLvl D sp π l) (pGam_level D sp π l 1)
  choose above habove using exists_above D sp eP
  choose below hbelow1 hbelow2 using exists_below D sp eP
  have hbl : ∀ (j : Fin n) (l : Fin (pSp D sp (eP j)).k),
      (pSp D sp (eP j)).lev l = false ∧ (eP j).1.val = 0 →
        D.f (pGam D sp (eP j) l 1) = D.level 0 := fun j l h => bottom_level D sp h.1 h.2 1
  let U : (j : Fin n) → (l : Fin (pSp D sp (eP j)).k) → PartialDiffeomorph ((𝓡 1).prod 𝓘(ℝ, ℝ))
      (SurfaceModel.model B.kind) (Circle × ℝ) B.Carrier ∞ := fun j l =>
    if hl : (pSp D sp (eP j)).lev l = true then bc (eP (above j l hl).1.1) (above j l hl).1.2
    else if hb : (pSp D sp (eP j)).lev l = false ∧ (eP j).1.val = 0 then
      Classical.choose (D.exists_levelBicollar 0 (hbl j l hb))
    else bc (eP j) l
  let I : (j : Fin n) → (l : Fin (pSp D sp (eP j)).k) → Fin (D.m + 1) := fun j l =>
    if hl : (pSp D sp (eP j)).lev l = true then pLvl D sp (eP (above j l hl).1.1) (above j l hl).1.2
    else if (pSp D sp (eP j)).lev l = false ∧ (eP j).1.val = 0 then 0
    else pLvl D sp (eP j) l
  let lam' : (j : Fin n) → (l : Fin (pSp D sp (eP j)).k) → ℝ := fun j l =>
    if (pSp D sp (eP j)).lev l = false ∧ (eP j).1.val = 0 then 1 else lam
  have hdata : ∀ (j : Fin n) (l : Fin (pSp D sp (eP j)).k),
      (U j l).source = {p | -1 < p.2 ∧ p.2 < 1} ∧
      range (fun t => U j l (t, 0)) = range (pGam D sp (eP j) l) ∧
      (∀ t s, -1 < s → s < 1 → D.f (U j l (t, s)) = D.level (I j l) + D.κ * s) ∧
      (∀ t, IsMIntegralCurveOn (fun s => U j l (t, s)) (fun x => D.κ • D.field x)
        (Ioo (-1) 1)) ∧
      D.level (I j l) = if (pSp D sp (eP j)).lev l then D.level (eP j).1.succ
        else D.level (eP j).1.castSucc := by
    intro j l
    by_cases hl : (pSp D sp (eP j)).lev l = true
    · have hU : U j l = bc (eP (above j l hl).1.1) (above j l hl).1.2 := by
        simp only [U, hl, ↓reduceDIte]
      have hI : I j l = pLvl D sp (eP (above j l hl).1.1) (above j l hl).1.2 := by
        simp only [I, hl, ↓reduceDIte]
      rw [hU, hI]
      have hmeet := habove j l hl
      refine ⟨hbcs _ _, ?_, hbcf _ _, hbcc _ _, ?_⟩
      · rw [hbcr, ← range_pGam]
        exact range_eq_of_meet D sp hmeet
      · rw [pLvl_eq_of_meet D sp hmeet, (lev_eq_of_pLvl D sp).mp hl]
        simp only [hl, ↓reduceIte]
    · have hl' : (pSp D sp (eP j)).lev l = false := by simpa using hl
      by_cases hb : (pSp D sp (eP j)).lev l = false ∧ (eP j).1.val = 0
      · have hU : U j l = Classical.choose (D.exists_levelBicollar 0 (hbl j l hb)) := by
          simp [U, hl', hb]
        have hI : I j l = 0 := by simp [I, hl', hb]
        rw [hU, hI]
        obtain ⟨h1, h2, h3, h4⟩ := Classical.choose_spec (D.exists_levelBicollar 0 (hbl j l hb))
        refine ⟨h1, ?_, h3, h4, ?_⟩
        · rw [h2, range_pGam]
          have hL : D.level (pLvl D sp (eP j) l) = D.level 0 := by
            rw [← pGam_level D sp (eP j) l 1]; exact hbl j l hb
          rw [hL]
        · rw [hl']
          simp only [Bool.false_eq_true, ↓reduceIte]
          congr 1
          exact Fin.ext (by simp [hb.2])
      · have hb' : ¬ (eP j).1.val = 0 := fun h => hb ⟨hl', h⟩
        have hU : U j l = bc (eP j) l := by simp [U, hl', hb']
        have hI : I j l = pLvl D sp (eP j) l := by simp [I, hl', hb']
        rw [hU, hI]
        refine ⟨hbcs _ _, ?_, hbcf _ _, hbcc _ _, ?_⟩
        · rw [hbcr, ← range_pGam]
        · rw [pLvl, hl']
          simp
  choose Q ι hιe hιc hιK hιs hιb hιz using fun j : Fin n =>
    exists_recollared_of_data D (eP j).1 (pSp D sp (eP j)) hlam0 hlam1 hlamb hlamg (U j) (I j)
      (lam' j) (fun l => rfl) (fun l => (hdata j l).1) (fun l => (hdata j l).2.1)
      (fun l => (hdata j l).2.2.1) (fun l => (hdata j l).2.2.2.1) (fun l => (hdata j l).2.2.2.2)
  have : Finite (CIdx D sp eP) := by unfold CIdx; infer_instance
  let nc := Nat.card (CIdx D sp eP)
  let eC : Fin nc ≃ CIdx D sp eP := (Finite.equivFin _).symm
  have hcutlev : ∀ q : CIdx D sp eP, 1 ≤ (pLvl D sp (eP q.1.1) q.1.2).val ∧
      pLvl D sp (eP q.1.1) q.1.2 = (eP q.1.1).1.castSucc := by
    intro q
    have h : pLvl D sp (eP q.1.1) q.1.2 = (eP q.1.1).1.castSucc := by
      rw [pLvl, q.2.1]; rfl
    refine ⟨?_, h⟩
    rw [h, Fin.val_castSucc]
    exact Nat.one_le_iff_ne_zero.mpr q.2.2
  have hlev1 : ∀ q : CIdx D sp eP, D.level 1 ≤ D.level (pLvl D sp (eP q.1.1) q.1.2) := by
    intro q
    apply D.level_strictMono.monotone
    rw [Fin.le_def]
    have hm : 1 < D.m + 1 := by have := (eP q.1.1).1.2; omega
    simp only [Fin.val_one', Nat.mod_eq_of_lt hm]
    exact (hcutlev q).1
  have hpos : ∀ q : CIdx D sp eP, ∀ t s, -1 < s → s < 1 →
      D.level 0 < D.f (bc (eP q.1.1) q.1.2 (t, lam * s)) := by
    intro q t s h1 h2
    have hb : |lam * s| < 1 := by
      rw [abs_mul, abs_of_pos hlam0]
      have : |s| < 1 := abs_lt.mpr ⟨h1, h2⟩
      nlinarith [abs_nonneg s]
    rw [hbcf _ _ t _ (abs_lt.mp hb).1 (abs_lt.mp hb).2]
    have := hlev1 q
    nlinarith [mul_pos hκ hlam0]
  let cut : Fin nc → PartialDiffeomorph ((𝓡 1).prod 𝓘(ℝ, ℝ)) (𝓡∂ 2) (Circle × ℝ)
      D.core.Carrier ∞ := fun k =>
    coreCut D (bc (eP (eC k).1.1) (eC k).1.2) lam (hbcs _ _) hlam0 hlam1 (hpos (eC k))
  have hzero : ∀ (π : PIdx D) (l : Fin (pSp D sp π).k) (y : B.Carrier),
      y ∈ range (pGam D sp π l) → ∃ t, bc π l (t, 0) = y := by
    intro π l y hy
    rw [range_pGam, ← hbcr] at hy
    exact hy
  have hzero' : ∀ (π : PIdx D) (l : Fin (pSp D sp π).k) (t : Circle),
      bc π l (t, 0) ∈ range (pGam D sp π l) := by
    intro π l t
    rw [range_pGam, ← hbcr]
    exact mem_range_self t
  have hcut_eq : ∀ q q' : CIdx D sp eP,
      (range (pGam D sp (eP q.1.1) q.1.2) ∩ range (pGam D sp (eP q'.1.1) q'.1.2)).Nonempty →
        q = q' := by
    intro q q' h
    have hL := pLvl_eq_of_meet D sp h
    rw [(hcutlev q).2, (hcutlev q').2] at hL
    have hi : (eP q.1.1).1 = (eP q'.1.1).1 := Fin.castSucc_injective _ hL
    exact Subtype.ext (eq_of_meet_same_slab D sp eP h hi)
  have hlevgap : ∀ a b : Fin (D.m + 1), a < b → 2 * (D.κ * lam) < D.level b - D.level a := by
    intro a b hab
    have ha : a.val < D.m := by have := b.2; omega
    have h1 := hlamg ⟨a.val, ha⟩
    have e1 : (⟨a.val, ha⟩ : Fin D.m).castSucc = a := Fin.ext rfl
    have e2 : (⟨a.val, ha⟩ : Fin D.m).succ ≤ b := by rw [Fin.le_def]; simp; omega
    rw [e1] at h1
    have := D.level_strictMono.monotone e2
    linarith
  have hshrink : ∀ (q : CIdx D sp eP) (y : B.Carrier), y ∈ (bc (eP q.1.1) q.1.2).target →
      |((bc (eP q.1.1) q.1.2).symm y).2| < lam →
        |D.f y - D.level (pLvl D sp (eP q.1.1) q.1.2)| < D.κ * lam := by
    intro q y hy hs
    have hp := (bc (eP q.1.1) q.1.2).map_target hy
    rw [hbcs] at hp
    have hr : bc (eP q.1.1) q.1.2 ((bc (eP q.1.1) q.1.2).symm y) = y :=
      (bc (eP q.1.1) q.1.2).right_inv hy
    have h := hbcf (eP q.1.1) q.1.2 ((bc (eP q.1.1) q.1.2).symm y).1
      ((bc (eP q.1.1) q.1.2).symm y).2 hp.1 hp.2
    rw [show (((bc (eP q.1.1) q.1.2).symm y).1, ((bc (eP q.1.1) q.1.2).symm y).2) =
      (bc (eP q.1.1) q.1.2).symm y from rfl, hr] at h
    rw [h, add_sub_cancel_left, abs_mul, abs_of_pos hκ]
    exact mul_lt_mul_of_pos_left hs hκ
  let cutSide : Fin nc → Bool → Σ j : Fin n, Fin (pSp D sp (eP j)).k := fun k b =>
    if b then ⟨(eC k).1.1, (eC k).1.2⟩ else below (eC k)
  have hbotOf : ∀ (j : Fin n) (l : Fin (pSp D sp (eP j)).k),
      (∀ k b, cutSide k b ≠ ⟨j, l⟩) → (pSp D sp (eP j)).lev l = false ∧ (eP j).1.val = 0 := by
    intro j l hns
    by_contra hnb
    by_cases hl : (pSp D sp (eP j)).lev l = true
    · apply hns (eC.symm (above j l hl)) false
      change below (eC (eC.symm (above j l hl))) = ⟨j, l⟩
      rw [Equiv.apply_symm_apply]
      have hmeet : (range (pGam D sp (eP (below (above j l hl)).1) (below (above j l hl)).2) ∩
          range (pGam D sp (eP j) l)).Nonempty := by
        rw [range_eq_of_meet D sp (hbelow2 _), range_eq_of_meet D sp (habove j l hl)]
        obtain ⟨t₀⟩ : Nonempty Circle := inferInstance
        exact ⟨_, mem_range_self t₀, mem_range_self t₀⟩
      have hL := pLvl_eq_of_meet D sp hmeet
      rw [(lev_eq_of_pLvl D sp).mp (hbelow1 _), (lev_eq_of_pLvl D sp).mp hl] at hL
      exact eq_of_meet_same_slab D sp eP hmeet (Fin.succ_injective _ hL)
    · have hl' : (pSp D sp (eP j)).lev l = false := by simpa using hl
      have h0 : (eP j).1.val ≠ 0 := fun h => hnb ⟨hl', h⟩
      apply hns (eC.symm ⟨⟨j, l⟩, hl', h0⟩) true
      exact congrArg Subtype.val (Equiv.apply_symm_apply eC ⟨⟨j, l⟩, hl', h0⟩)
  let P : PlanarDecomposition D.core :=
    { cutCount := nc
      cut := cut
      cut_source := fun k => rfl
      cut_interior := by
        intro k y hy
        have h := abs_sub_lt_of_mem_target (hbcs _ _) hκ (hbcf _ _) hy.1
        have h1 := hlev1 (eC k)
        have hne : D.f y.val ≠ D.level 0 := by
          intro h0
          rw [h0, abs_lt] at h
          nlinarith [mul_pos hκ hlam0]
        exact ((SurfaceModel.model D.core.kind).isInteriorPoint_iff_not_isBoundaryPoint y).mpr
          fun hb => hne ((D.core_isBoundaryPoint_iff y).mp hb)
      cut_disjoint := by
        intro k k' hkk
        rw [Set.disjoint_left]
        intro y hy hy'
        set q := eC k with hq
        set q' := eC k' with hq'
        by_cases hL : pLvl D sp (eP q.1.1) q.1.2 = pLvl D sp (eP q'.1.1) q'.1.2
        · have hp := (bc (eP q.1.1) q.1.2).map_target hy.1
          have hp' := (bc (eP q'.1.1) q'.1.2).map_target hy'.1
          rw [hbcs] at hp hp'
          have hr := (bc (eP q.1.1) q.1.2).right_inv hy.1
          have hr' := (bc (eP q'.1.1) q'.1.2).right_inv hy'.1
          have hf' : ∀ t s, -1 < s → s < 1 → D.f (bc (eP q'.1.1) q'.1.2 (t, s)) =
              D.level (pLvl D sp (eP q.1.1) q.1.2) + D.κ * s := by
            rw [hL]; exact hbcf _ _
          obtain ⟨-, h0⟩ := eq_of_bicollar_eq D (hbcf _ _) hf' (hbcc _ _) (hbcc _ _) hp hp'
            (hr.trans hr'.symm)
          have hmeet : (range (pGam D sp (eP q.1.1) q.1.2) ∩
              range (pGam D sp (eP q'.1.1) q'.1.2)).Nonempty :=
            ⟨_, hzero' _ _ _, by rw [h0]; exact hzero' _ _ _⟩
          exact hkk (eC.injective (hcut_eq q q' hmeet))
        · have h1 := hshrink q y.val hy.1 hy.2
          have h2 := hshrink q' y.val hy'.1 hy'.2
          rw [abs_lt] at h1 h2
          rcases lt_or_gt_of_ne hL with h | h
          · have := hlevgap _ _ h
            linarith
          · have := hlevgap _ _ h
            linarith
      pieceCount := n
      piece := fun j => ElementaryBase.planar (pSp D sp (eP j)).k (pSp D sp (eP j)).hk (Q j)
      inclusion := ι
      isSmoothEmbedding := hιe
      covers := by
        refine Set.eq_univ_of_forall fun y => ?_
        have hy0 : D.level 0 ≤ D.f y.val := y.2
        obtain ⟨i, hi⟩ := exists_slab_of_level_zero_le D hy0
        obtain ⟨c, hc⟩ := exists_pK_of_mem D i hi
        obtain ⟨j, hj⟩ := eP.surjective ⟨i, c⟩
        have hyK : y.val ∈ pK D (eP j) := by rw [hj]; exact hc
        obtain ⟨x, hx⟩ := hιs j y.val hyK
        exact mem_iUnion.mpr ⟨j, x, Subtype.ext hx⟩
      cutSide := cutSide
      cutSide_injective := by
        have hlevf : ∀ r r' : Σ j : Fin n, Fin (pSp D sp (eP j)).k, r = r' →
            (pSp D sp (eP r.1)).lev r.2 = (pSp D sp (eP r'.1)).lev r'.2 := by
          rintro r r' rfl; rfl
        have hrb : ∀ q : CIdx D sp eP, range (pGam D sp (eP (below q).1) (below q).2) =
            range (pGam D sp (eP q.1.1) q.1.2) := fun q => range_eq_of_meet D sp (hbelow2 q)
        rintro ⟨k, b⟩ ⟨k', b'⟩ h
        simp only [uncurry] at h
        cases b <;> cases b' <;> simp only [cutSide, Bool.false_eq_true, ↓reduceIte] at h
        · have hq : eC k = eC k' := by
            apply hcut_eq
            rw [← hrb, ← hrb, h]
            obtain ⟨t⟩ : Nonempty Circle := inferInstance
            exact ⟨_, mem_range_self t, mem_range_self t⟩
          rw [eC.injective hq]
        · have := hlevf _ _ h
          rw [hbelow1, (eC k').2.1] at this
          exact absurd this (by decide)
        · have := hlevf _ _ h
          rw [hbelow1, (eC k).2.1] at this
          exact absurd this (by decide)
        · have hq : eC k = eC k' := Subtype.ext h
          rw [eC.injective hq]
      cutSide_collar := by
        intro k b
        have hcutval : ∀ (t : Circle) (s : ℝ), -1 < s → s < 1 →
            (cut k (t, s)).val = bc (eP (eC k).1.1) (eC k).1.2 (t, lam * s) := fun t s h1 h2 =>
          coreCutFun_val D _ lam (hpos (eC k) t s h1 h2).le
        cases b
        · obtain ⟨σ, hσ⟩ := hιc (below (eC k)).1 (below (eC k)).2
          refine ⟨σ, fun t s hs hs1 => ?_⟩
          have hl : (pSp D sp (eP (below (eC k)).1)).lev (below (eC k)).2 = true := hbelow1 (eC k)
          have hab : above (below (eC k)).1 (below (eC k)).2 hl = eC k := by
            apply hcut_eq
            rw [range_eq_of_meet D sp (habove _ _ hl), range_eq_of_meet D sp (hbelow2 (eC k))]
            obtain ⟨t₀⟩ : Nonempty Circle := inferInstance
            exact ⟨_, mem_range_self t₀, mem_range_self t₀⟩
          have hU : U (below (eC k)).1 (below (eC k)).2 = bc (eP (eC k).1.1) (eC k).1.2 := by
            simp only [U, hl, ↓reduceDIte]
            rw [hab]
          have hlam : lam' (below (eC k)).1 (below (eC k)).2 = lam := by simp [lam', hl]
          have h := hσ t s hs hs1
          rw [hU, hlam] at h
          simp only [hl, ↓reduceIte] at h
          apply Subtype.ext
          change (ι (below (eC k)).1 ((Q (below (eC k)).1).collar (below (eC k)).2
            (t, halfPoint s hs))).val = (cut k (σ t, -s)).val
          rw [h, hcutval (σ t) (-s) (by linarith) (by linarith)]
          ring_nf
        · obtain ⟨σ, hσ⟩ := hιc (eC k).1.1 (eC k).1.2
          refine ⟨σ, fun t s hs hs1 => ?_⟩
          have hl : (pSp D sp (eP (eC k).1.1)).lev (eC k).1.2 = false := (eC k).2.1
          have hl' : ¬ (pSp D sp (eP (eC k).1.1)).lev (eC k).1.2 = true := by simp [hl]
          have hb : ¬ ((pSp D sp (eP (eC k).1.1)).lev (eC k).1.2 = false ∧
              (eP (eC k).1.1).1.val = 0) := fun h => (eC k).2.2 h.2
          have hb' : ¬ (eP (eC k).1.1).1.val = 0 := (eC k).2.2
          have hU : U (eC k).1.1 (eC k).1.2 = bc (eP (eC k).1.1) (eC k).1.2 := by
            simp [U, hl, hb']
          have hlam : lam' (eC k).1.1 (eC k).1.2 = lam := by simp only [lam', hb, ↓reduceIte]
          have h := hσ t s hs hs1
          rw [hU, hlam] at h
          simp only [hl, Bool.false_eq_true, ↓reduceIte, one_mul] at h
          apply Subtype.ext
          change (ι (eC k).1.1 ((Q (eC k).1.1).collar (eC k).1.2
            (t, halfPoint s hs))).val = (cut k (σ t, s)).val
          rw [h, hcutval (σ t) s (by linarith) hs1]
      boundary_side := by
        intro j l hns t
        have hbot := hbotOf j l hns
        refine (D.core_isBoundaryPoint_iff _).mpr ?_
        change D.f (ι j ((Q j).collar l (t, halfZero))).val = D.level 0
        rw [hιz j l t]
        exact bottom_level D sp hbot.1 hbot.2 t
      overlap := by
        have hcutzero : ∀ (k : Fin nc) (t : Circle),
            (cut k (t, 0)).val = bc (eP (eC k).1.1) (eC k).1.2 (t, 0) := by
          intro k t
          rw [show (cut k (t, 0)).val = bc (eP (eC k).1.1) (eC k).1.2 (t, lam * 0) from
            coreCutFun_val D _ lam (hpos (eC k) t 0 (by norm_num) (by norm_num)).le, mul_zero]
        have hlow : ∀ (j' : Fin n) (x' : (Q j').surface.Carrier),
            D.f (ι j' x').val = D.level (eP j').1.castSucc → (eP j').1.val ≠ 0 →
              ∃ (k : Fin nc) (t : Circle), ι j' x' = cut k (t, 0) := by
          intro j' x' hfa h0
          obtain ⟨l', t', hx'⟩ := hιb j' x' (Or.inl hfa)
          have hyγ : (ι j' x').val = pGam D sp (eP j') l' t' := by rw [hx', hιz]; rfl
          have hlev : (pSp D sp (eP j')).lev l' = false :=
            lev_false_of_level D sp (t := t') (by rw [← hyγ]; exact hfa)
          obtain ⟨t'', ht''⟩ := hzero (eP j') l' _ ⟨t', hyγ.symm⟩
          refine ⟨eC.symm ⟨⟨j', l'⟩, hlev, h0⟩, t'', Subtype.ext ?_⟩
          rw [hcutzero]
          have he := Equiv.apply_symm_apply eC ⟨⟨j', l'⟩, hlev, h0⟩
          rw [he]
          exact ht''.symm
        intro j j' x x' hjj h
        have hy' : (ι j x).val = (ι j' x').val := congrArg Subtype.val h
        have hyK : (ι j x).val ∈ pK D (eP j) := hιK j x
        have hyK' : (ι j x).val ∈ pK D (eP j') := by rw [hy']; exact hιK j' x'
        have hfy : D.f (ι j x).val ∈ Icc (D.level (eP j).1.castSucc) (D.level (eP j).1.succ) :=
          connectedComponentIn_subset (D.f ⁻¹' Icc (D.level (eP j).1.castSucc)
            (D.level (eP j).1.succ)) _ hyK
        have hfy' : D.f (ι j x).val ∈ Icc (D.level (eP j').1.castSucc)
            (D.level (eP j').1.succ) := connectedComponentIn_subset (D.f ⁻¹' Icc
              (D.level (eP j').1.castSucc) (D.level (eP j').1.succ)) _ hyK'
        by_cases hii : (eP j).1 = (eP j').1
        · exact absurd (eP.injective (pIdx_eq_of_pK_meet D ⟨_, hyK, hyK'⟩ hii)) hjj
        · rcases lt_or_gt_of_ne hii with hlt | hgt
          · have hle : D.level (eP j).1.succ ≤ D.level (eP j').1.castSucc :=
              D.level_strictMono.monotone (Fin.succ_le_castSucc_iff.mpr hlt)
            have hfa : D.f (ι j' x').val = D.level (eP j').1.castSucc := by
              rw [← hy']; linarith [hfy.2, hfy'.1]
            have h0 : (eP j').1.val ≠ 0 := by
              have := Fin.lt_def.mp hlt; omega
            obtain ⟨k, t, hk⟩ := hlow j' x' hfa h0
            exact ⟨k, t, h.trans hk⟩
          · have hle : D.level (eP j').1.succ ≤ D.level (eP j).1.castSucc :=
              D.level_strictMono.monotone (Fin.succ_le_castSucc_iff.mpr hgt)
            have hfa : D.f (ι j x).val = D.level (eP j).1.castSucc := by
              linarith [hfy.1, hfy'.2]
            have h0 : (eP j).1.val ≠ 0 := by
              have := Fin.lt_def.mp hgt; omega
            exact hlow j x hfa h0 }
  have hcv : ∀ (k : Fin nc) (t : Circle) (s : ℝ), -1 < s → s < 1 →
      (P.cut k (t, s)).val = shrinkBicollar (bc (eP (eC k).1.1) (eC k).1.2) lam (hbcs _ _) hlam0
        hlam1 (t, s) := fun k t s h1 h2 => coreCutFun_val D _ lam (hpos (eC k) t s h1 h2).le
  refine ⟨{ cutCount := nc
            cut := fun k => shrinkBicollar (bc (eP (eC k).1.1) (eC k).1.2) lam (hbcs _ _) hlam0
              hlam1
            cut_source := fun k => rfl
            cut_level := fun k t s h1 h2 => hpos (eC k) t s h1 h2
            pieceCount := n
            kind := fun j => (pSp D sp (eP j)).k
            kind_mem := fun j => (pSp D sp (eP j)).hk
            base := Q
            inclusion := ι
            isSmoothEmbedding := hιe
            covers := P.covers
            cutSide := cutSide
            cutSide_injective := P.cutSide_injective
            cutSide_collar := fun k b => ?_
            bottom_collar := fun j l hns => ?_
            overlap := fun j j' x x' hjj h => ?_ }⟩
  · obtain ⟨σ, hσ⟩ := P.cutSide_collar k b
    refine ⟨σ, fun t s hs hs1 => ?_⟩
    have h := congrArg Subtype.val (hσ t s hs hs1)
    refine h.trans (hcv k (σ t) _ ?_ ?_) <;> cases b <;> simp only [Bool.false_eq_true,
      ↓reduceIte] <;> linarith
  rotate_left
  · obtain ⟨c, t, h⟩ := P.overlap j j' x x' hjj h
    exact ⟨c, t, (congrArg Subtype.val h).trans (hcv c t 0 (by norm_num) (by norm_num))⟩
  have hb := hbotOf j l hns
  have hl' : ¬ (pSp D sp (eP j)).lev l = true := by simp [hb.1]
  refine ⟨pGam D sp (eP j) l 1, hbl j l hb, ?_⟩
  obtain ⟨σ, hσ⟩ := hιc j l
  refine ⟨σ, fun t s hs hs1 => ?_⟩
  have hU : U j l = Classical.choose (D.exists_levelBicollar 0 (hbl j l hb)) := by
    simp only [U, hl', hb, ↓reduceDIte, and_self, Bool.false_eq_true]
  have hlam : lam' j l = 1 := by simp only [lam', hb, and_self, ↓reduceIte]
  have h := hσ t s hs hs1
  rw [hU, hlam] at h
  simp only [hb.1, Bool.false_eq_true, ↓reduceIte, one_mul] at h
  exact h

end Pieces

section Final

variable (D : BaseMorseData B)

theorem nonempty_planarCore_of_gap (hgap : D.κ < D.level 1 - D.level 0)
    (h11 : ∀ (i : Fin D.m) (p : B.Carrier), p ∈ D.crit →
      sigNeg (chartHessianAt
        (fun y => D.f ((extChartAt (SurfaceModel.model B.kind) p).symm y))
        (extChartAt (SurfaceModel.model B.kind) p p)) = 1 →
      D.f p ∈ Ioo (D.level i.castSucc) (D.level i.succ) →
      ¬ IsPreconnected (connectedComponentIn (D.f ⁻¹' Icc (D.level i.castSucc) (D.level i.succ))
        p ∩ D.f ⁻¹' {D.level i.castSucc}) ∨
      ¬ IsPreconnected (connectedComponentIn (D.f ⁻¹' Icc (D.level i.castSucc) (D.level i.succ))
        p ∩ D.f ⁻¹' {D.level i.succ})) :
    Nonempty (PlanarCore D) :=
  nonempty_planarCore_of_pieces D
    (fun i x₀ hx₀ => Classical.choice (nonempty_slabPiece D h11 i x₀ hx₀)) hgap

theorem exists_planarCore_of_shrink
    (h11 : ∀ (i : Fin D.m) (p : B.Carrier), p ∈ D.crit →
      sigNeg (chartHessianAt
        (fun y => D.f ((extChartAt (SurfaceModel.model B.kind) p).symm y))
        (extChartAt (SurfaceModel.model B.kind) p p)) = 1 →
      D.f p ∈ Ioo (D.level i.castSucc) (D.level i.succ) →
      ¬ IsPreconnected (connectedComponentIn (D.f ⁻¹' Icc (D.level i.castSucc) (D.level i.succ))
        p ∩ D.f ⁻¹' {D.level i.castSucc}) ∨
      ¬ IsPreconnected (connectedComponentIn (D.f ⁻¹' Icc (D.level i.castSucc) (D.level i.succ))
        p ∩ D.f ⁻¹' {D.level i.succ})) :
    ∃ D' : BaseMorseData B, D'.f = D.f ∧ D'.crit = D.crit ∧ D'.m = D.m ∧ D'.κ ≤ D.κ ∧
      (∀ i : Fin (D'.m + 1), ∃ j : Fin (D.m + 1), D'.level i = D.level j) ∧
      Nonempty (PlanarCore D') := by
  have hm : 0 < D.m := by
    obtain ⟨x, hx⟩ := D.exists_level_zero_lt
    by_contra h
    have h0 : D.m = 0 := by omega
    have hlt := D.lt_level_last x
    have hl : Fin.last D.m = 0 := Fin.ext (by simp [h0])
    rw [hl] at hlt
    linarith
  have hgap0 : 0 < D.level 1 - D.level 0 := by
    have : (0 : Fin (D.m + 1)) < 1 := by
      rw [Fin.lt_def]
      simp [Nat.mod_eq_of_lt (show 1 < D.m + 1 by omega)]
    linarith [D.level_strictMono this]
  set κ' := min D.κ ((D.level 1 - D.level 0) / 2)
  have hκ' : 0 < κ' := lt_min D.κ_pos (by linarith)
  have hκ'κ : κ' ≤ D.κ := min_le_left _ _
  refine ⟨withKappa D κ' hκ' hκ'κ, rfl, rfl, rfl, hκ'κ, fun i => ⟨i, rfl⟩, ?_⟩
  refine nonempty_planarCore_of_gap (withKappa D κ' hκ' hκ'κ) ?_ h11
  change κ' < D.level 1 - D.level 0
  have : κ' ≤ (D.level 1 - D.level 0) / 2 := min_le_right _ _
  linarith

end Final

theorem exists_planarCore_orientable (D : BaseMorseData B)
    (o : ManifoldOrientation (SurfaceModel.model B.kind) B.Carrier 2) :
    ∃ D' : BaseMorseData B, D'.f = D.f ∧ D'.crit = D.crit ∧ D'.m = D.m ∧ D'.κ ≤ D.κ ∧
      (∀ i : Fin (D'.m + 1), ∃ j : Fin (D.m + 1), D'.level i = D.level j) ∧
      Nonempty (PlanarCore D') :=
  exists_planarCore_of_shrink D (h11_of_orientable D o)

theorem exists_planarCore_of_orientable
    (o : ManifoldOrientation (SurfaceModel.model B.kind) B.Carrier 2) :
    ∃ D : BaseMorseData B, Nonempty (PlanarCore D) := by
  obtain ⟨D, -, -, -, -, -, h⟩ := exists_planarCore_orientable (exists_baseMorseData B).some o
  exact ⟨D, h⟩

end GC.Seifert.CoreDecomposition
