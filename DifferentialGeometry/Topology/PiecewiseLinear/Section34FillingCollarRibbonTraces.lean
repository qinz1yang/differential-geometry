import DifferentialGeometry.Topology.PiecewiseLinear.Section34CrossingCornerCollarExterior
import DifferentialGeometry.Topology.PiecewiseLinear.Section34AnnularCollarExtensionSupport

open Set Topology

namespace DifferentialGeometry.Topology.PiecewiseLinear

private theorem corner_smul_mem (a b : Bool) {p : ℝ × ℝ} {t : ℝ}
    (hp : p ∈ section34CornerBase a b) (ht : t ∈ Icc (0 : ℝ) 1) :
    t • p ∈ section34CornerBase a b := by
  rcases p with ⟨x, y⟩
  cases a <;> cases b <;> rcases hp with ⟨hx, hy⟩ | ⟨hx, hy⟩
  all_goals
    simp only [Bool.false_eq_true, ↓reduceIte, mem_Icc, mem_singleton_iff] at hx hy
    simp only [section34CornerBase, Bool.false_eq_true, ↓reduceIte, Prod.smul_mk,
      smul_eq_mul, mem_union, mem_prod, mem_Icc, mem_singleton_iff]
    first
    | left; refine ⟨⟨?_, ?_⟩, ?_⟩ <;> nlinarith [ht.1, ht.2]
    | right; refine ⟨?_, ?_, ?_⟩ <;> nlinarith [ht.1, ht.2]

theorem IsCylindricalDiagram.exists_short_corner_strip_in_neighborhood
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {f : (ℝ × ℝ) × ℝ → E} {C S L : Set E}
    (hf : IsCylindricalDiagram f spliceSquare C) (a b : Bool)
    (hB : f '' (section34CornerBase a b ×ˢ Icc (0 : ℝ) 1) ⊆ S)
    (hL : L ∈ 𝓝ˢ[S] (f '' section34MarkedAxis)) :
    ∃ d : ℝ, 0 < d ∧ d ≤ 1 ∧
      ∀ p ∈ section34CornerBase a b, ∀ s ∈ Icc (0 : ℝ) 1,
        ∀ t ∈ Icc (0 : ℝ) d, f (t • p, s) ∈ L := by
  let K := section34CornerBase a b ×ˢ Icc (0 : ℝ) 1
  let φ : ((ℝ × ℝ) × ℝ) × ℝ → (ℝ × ℝ) × ℝ :=
    fun z => (z.2 • z.1.1, z.1.2)
  have hφ : Continuous φ :=
    (continuous_snd.smul continuous_fst.fst).prodMk continuous_fst.snd
  have hφB : MapsTo φ (K ×ˢ Icc (0 : ℝ) 1) K :=
    fun z hz => ⟨corner_smul_mem a b hz.1.1 hz.2, hz.1.2⟩
  have hKC : K ⊆ spliceCylinder := prod_mono
    ((section34_corner_base_subset a b).trans (section34_crossing_quadrant_subset_square a b))
    subset_rfl
  obtain ⟨d, hd, hd1, hsmall⟩ := exists_short_product_image_subset_of_compact
    ((section34_corner_base_isPolyhedron a b).isCompact.prod isCompact_Icc)
    (by norm_num : (0 : ℝ) < 1)
    (hf.isPiecewiseAffineOn.continuousOn.comp hφ.continuousOn (hφB.mono_right hKC))
    (fun z hz => hB (mem_image_of_mem f (hφB hz)))
    (fun z hz => by
      change f (0 • z.1, z.2) ∈ f '' section34MarkedAxis
      simp only [zero_smul]
      exact mem_image_of_mem f (show ((0 : ℝ × ℝ), z.2) ∈ section34MarkedAxis from
        ⟨rfl, hz.2⟩)) hL
  exact ⟨d, hd, hd1, fun p hp s hs t ht =>
    hsmall (mem_image_of_mem (f ∘ φ)
      (show ((p, s), t) ∈ K ×ˢ Icc (0 : ℝ) d from ⟨⟨hp, hs⟩, ht⟩))⟩

private theorem corner_feet (a b : Bool) {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) :
    (0, if b then t / 2 else -t / 2) ∈ section34CornerBase a b ∧
      (if a then t / 2 else -t / 2, 0) ∈ section34CornerBase a b := by
  constructor
  · right
    cases b <;> simp only [Bool.false_eq_true, ↓reduceIte, mem_prod, mem_singleton_iff,
      mem_Icc, true_and] <;> constructor <;> linarith [ht.1, ht.2]
  · left
    cases a <;> simp only [Bool.false_eq_true, ↓reduceIte, mem_prod, mem_singleton_iff,
      mem_Icc, and_true] <;> constructor <;> linarith [ht.1, ht.2]

private theorem corner_first_foot (a b : Bool) {p : ℝ × ℝ} {t : ℝ}
    (hp : p ∈ section34CornerBase a b) (ht : 0 < t)
    (hy : p.2 = (if b then t / 2 else -t / 2)) :
    p = (0, if b then t / 2 else -t / 2) := by
  apply Prod.ext
  · rcases hp with ⟨-, hp⟩ | ⟨hp, -⟩
    · change p.2 = 0 at hp
      cases b <;> simp only [Bool.false_eq_true, ↓reduceIte] at hy <;> linarith
    · exact hp
  · exact hy

private theorem corner_second_foot (a b : Bool) {p : ℝ × ℝ} {t : ℝ}
    (hp : p ∈ section34CornerBase a b) (ht : 0 < t)
    (hx : p.1 = (if a then t / 2 else -t / 2)) :
    p = (if a then t / 2 else -t / 2, 0) := by
  apply Prod.ext
  · exact hx
  · rcases hp with ⟨-, hp⟩ | ⟨hp, -⟩
    · exact hp
    · change p.1 = 0 at hp
      cases a <;> simp only [Bool.false_eq_true, ↓reduceIte] at hx <;> linarith

private theorem exterior_feet (a b : Bool) (t : ℝ) :
    section34CornerExteriorPush a b ((0, if b then t / 2 else -t / 2), t) =
      ((if a then -t / 2 else t / 2), 0) ∧
    section34CornerExteriorPush a b ((if a then t / 2 else -t / 2, 0), t) =
      (0, if b then -t / 2 else t / 2) := by
  cases a <;> cases b <;>
    simp [section34CornerExteriorPush, section34CornerPush, neg_div]

theorem section34_whole_collar_level_ribbon_traces
    {E M : Type*} {u : E → M} {ρ : E × ℝ → E}
    {f : Fin 2 → (ℝ × ℝ) × ℝ → E} {S L : Set E} {A B : Set M}
    (a b : Fin 2 → Bool) {t : ℝ} (ht : 0 < t) (ht1 : t ≤ 1)
    (hbase : ∀ k, f k '' (section34CornerBase (a k) (b k) ×ˢ Icc (0 : ℝ) 1) ⊆ S)
    (hfeet : ∀ k, ∀ s ∈ Icc (0 : ℝ) 1,
      f k ((0, if b k then t / 2 else -t / 2), s) ∈ L ∧
      f k ((if a k then t / 2 else -t / 2, 0), s) ∈ L)
    (hformula : ∀ k, ∀ p ∈ section34CornerBase (a k) (b k), ∀ s ∈ Icc (0 : ℝ) 1,
      f k (p, s) ∈ L →
        ρ (f k (p, s), t) = f k (section34CornerExteriorPush (a k) (b k) (p, t), s))
    (hfull : ∀ x ∈ S,
      (u (ρ (x, t)) ∈ A ↔
        ∃ k p s, p ∈ section34CornerBase (a k) (b k) ∧ s ∈ Icc (0 : ℝ) 1 ∧
          x = f k (p, s) ∧ x ∈ L ∧ p.2 = (if b k then t / 2 else -t / 2)) ∧
      (u (ρ (x, t)) ∈ B ↔
        ∃ k p s, p ∈ section34CornerBase (a k) (b k) ∧ s ∈ Icc (0 : ℝ) 1 ∧
          x = f k (p, s) ∧ x ∈ L ∧ p.1 = (if a k then t / 2 else -t / 2))) :
    (u ∘ ρ) '' (S ×ˢ {t}) ∩ A =
      ⋃ k, (u ∘ f k) '' ({((if a k then -t / 2 else t / 2), 0)} ×ˢ Icc (0 : ℝ) 1) ∧
    (u ∘ ρ) '' (S ×ˢ {t}) ∩ B =
      ⋃ k, (u ∘ f k) '' ({(0, if b k then -t / 2 else t / 2)} ×ˢ Icc (0 : ℝ) 1) := by
  have hmem (k) := corner_feet (a k) (b k) ⟨ht.le, ht1⟩
  constructor
  · ext y
    constructor
    · rintro ⟨⟨⟨x, v⟩, ⟨hx, hv⟩, rfl⟩, hy⟩
      change v = t at hv
      subst v
      obtain ⟨k, p, s, hp, hs, rfl, hL, heq⟩ := (hfull x hx).1.mp hy
      have hp' := corner_first_foot (a k) (b k) hp ht heq
      rw [hp'] at hL ⊢
      apply mem_iUnion.mpr
      refine ⟨k, ?_⟩
      refine ⟨(((if a k then -t / 2 else t / 2), 0), s), ⟨rfl, hs⟩, ?_⟩
      dsimp only [Function.comp_apply]
      rw [hformula k _ (hmem k).1 s hs hL, (exterior_feet (a k) (b k) t).1]
    · intro hy
      obtain ⟨k, ⟨⟨p, s⟩, ⟨hp, hs⟩, rfl⟩⟩ := mem_iUnion.mp hy
      change p = _ at hp
      subst p
      let q : ℝ × ℝ := (0, if b k then t / 2 else -t / 2)
      have hx := hbase k (mem_image_of_mem (f k)
        (show (q, s) ∈ section34CornerBase (a k) (b k) ×ˢ Icc (0 : ℝ) 1 from
          ⟨(hmem k).1, hs⟩))
      have heq : (u ∘ f k) (((if a k then -t / 2 else t / 2), 0), s) =
          u (ρ (f k (q, s), t)) := by
        rw [hformula k q (hmem k).1 s hs (hfeet k s hs).1,
          (exterior_feet (a k) (b k) t).1]
        rfl
      rw [heq]
      exact ⟨⟨(f k (q, s), t), ⟨hx, rfl⟩, rfl⟩,
        (hfull _ hx).1.mpr ⟨k, q, s, (hmem k).1, hs, rfl, (hfeet k s hs).1, rfl⟩⟩
  · ext y
    constructor
    · rintro ⟨⟨⟨x, v⟩, ⟨hx, hv⟩, rfl⟩, hy⟩
      change v = t at hv
      subst v
      obtain ⟨k, p, s, hp, hs, rfl, hL, heq⟩ := (hfull x hx).2.mp hy
      have hp' := corner_second_foot (a k) (b k) hp ht heq
      rw [hp'] at hL ⊢
      apply mem_iUnion.mpr
      refine ⟨k, ?_⟩
      refine ⟨((0, if b k then -t / 2 else t / 2), s), ⟨rfl, hs⟩, ?_⟩
      dsimp only [Function.comp_apply]
      rw [hformula k _ (hmem k).2 s hs hL, (exterior_feet (a k) (b k) t).2]
    · intro hy
      obtain ⟨k, ⟨⟨p, s⟩, ⟨hp, hs⟩, rfl⟩⟩ := mem_iUnion.mp hy
      change p = _ at hp
      subst p
      let q : ℝ × ℝ := (if a k then t / 2 else -t / 2, 0)
      have hx := hbase k (mem_image_of_mem (f k)
        (show (q, s) ∈ section34CornerBase (a k) (b k) ×ˢ Icc (0 : ℝ) 1 from
          ⟨(hmem k).2, hs⟩))
      have heq : (u ∘ f k) ((0, if b k then -t / 2 else t / 2), s) =
          u (ρ (f k (q, s), t)) := by
        rw [hformula k q (hmem k).2 s hs (hfeet k s hs).2,
          (exterior_feet (a k) (b k) t).2]
        rfl
      rw [heq]
      exact ⟨⟨(f k (q, s), t), ⟨hx, rfl⟩, rfl⟩,
        (hfull _ hx).2.mpr ⟨k, q, s, (hmem k).2, hs, rfl, (hfeet k s hs).2, rfl⟩⟩

theorem section34_positive_collar_disjoint_sheet_intersection
    {E M : Type*} {u : E → M} {ρ : E × ℝ → E}
    {f : Fin 2 → (ℝ × ℝ) × ℝ → E} {S L : Set E} {A B : Set M}
    (a b : Fin 2 → Bool) {c : ℝ}
    (hsecond : ∀ k, ∀ p ∈ section34CornerBase (a k) (b k), ∀ s ∈ Icc (0 : ℝ) 1,
      f k (p, s) ∈ L → ∀ t ∈ Ioc (0 : ℝ) c,
        u (ρ (f k (p, s), t)) ∈ B → p.1 = (if a k then t / 2 else -t / 2))
    (hfirst : ∀ x ∈ S, ∀ t ∈ Ioc (0 : ℝ) c, u (ρ (x, t)) ∈ A →
      ∃ k p s, p ∈ section34CornerBase (a k) (b k) ∧ s ∈ Icc (0 : ℝ) 1 ∧
        x = f k (p, s) ∧ x ∈ L ∧ p.2 = (if b k then t / 2 else -t / 2)) :
    Disjoint ((u ∘ ρ) '' (S ×ˢ Ioc (0 : ℝ) c)) (A ∩ B) := by
  apply disjoint_left.mpr
  rintro _ ⟨⟨x, t⟩, ⟨hx, ht⟩, rfl⟩ ⟨hA, hB⟩
  obtain ⟨k, p, s, hp, hs, rfl, hL, hy⟩ := hfirst x hx t ht hA
  have hx := hsecond k p hp s hs hL t ht hB
  have hfoot := corner_first_foot (a k) (b k) hp ht.1 hy
  have hp0 : p.1 = 0 := congrArg Prod.fst hfoot
  split_ifs at hx <;> linarith [ht.1]

theorem collar_union_preserves_sheet_intersection
    {E M : Type*} {u : E → M} {ρ : E × ℝ → E}
    {R W S : Set E} {A B : Set M} {c : ℝ} (hSR : S ⊆ R)
    (hW : ρ '' (S ×ˢ Icc (0 : ℝ) c) = W)
    (hzero : ∀ x ∈ S, ρ (x, 0) = x)
    (hdis : Disjoint ((u ∘ ρ) '' (S ×ˢ Ioc (0 : ℝ) c)) (A ∩ B)) :
    u '' (R ∪ W) ∩ (A ∩ B) = u '' R ∩ (A ∩ B) := by
  apply Subset.antisymm
  · rintro _ ⟨⟨x, hx, rfl⟩, hxAB⟩
    rcases hx with hx | hx
    · exact ⟨mem_image_of_mem u hx, hxAB⟩
    · obtain ⟨⟨y, t⟩, ⟨hy, ht⟩, rfl⟩ := hW.symm.subset hx
      by_cases ht0 : t = 0
      · rw [ht0, hzero y hy] at hxAB ⊢
        exact ⟨mem_image_of_mem u (hSR hy), hxAB⟩
      · exact False.elim (disjoint_left.mp hdis
          (mem_image_of_mem (u ∘ ρ)
            (show (y, t) ∈ S ×ˢ Ioc (0 : ℝ) c from
              ⟨hy, lt_of_le_of_ne ht.1 (Ne.symm ht0), ht.2⟩)) hxAB)
  · exact inter_subset_inter_left _ (image_mono subset_union_left)

end DifferentialGeometry.Topology.PiecewiseLinear
