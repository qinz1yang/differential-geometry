import DifferentialGeometry.Topology.Algebra.Group.FreeProduct.KuroshFreeFactors
import DifferentialGeometry.Topology.Algebra.Group.FreeProduct.Center
import Mathlib.GroupTheory.PushoutI
import Mathlib.GroupTheory.HNNExtension
import Mathlib.GroupTheory.SpecificGroups.Cyclic

/-!
# Graphs of groups with indecomposable vertex groups

The fundamental group of a connected graph of groups whose edge groups are nontrivial and inject
into the vertex groups, and whose vertex groups are freely indecomposable and not cyclic, is
freely indecomposable.

A freely indecomposable, non-cyclic subgroup of a free product lies in a conjugate of one factor
(`exists_le_conjugateSubgroup_of_freelyIndecomposable`): in the Bass-Serre form of the Kurosh
theorem only one component survives, a free component of rank at most one is cyclic and a free
component of rank at least two splits (`freeGroupEquivCoprodI`). Conjugates of factors are
malnormal (`conjugateSubgroup_factor_malnormal`), by a reduced word count in `Monoid.CoprodI`.
In a splitting of an amalgam `Monoid.PushoutI φ` (any nonempty index type, injective `φ i`,
nontrivial base) all vertex images lie in conjugates of factors, which share the image of a
nontrivial base element and therefore coincide; hence the whole group lies in one conjugate
factor and the other factor is trivial (`freelyIndecomposable_pushoutI`; the two-vertex case
`ι = Bool` is `freelyIndecomposable_pushout`). For an HNN extension the stable letter
conjugates a nontrivial associated element back into the same conjugate factor
(`freelyIndecomposable_hnnExtension`).

Finite connected graphs of groups are presented by `IsIndecomposableGraphOfGroups`: vertex groups
freely indecomposable and not cyclic; amalgams `Monoid.PushoutI φ` over a nontrivial `C` with
injective `φ i` of assembled groups (a spanning tree, one edge at a time, uses `ι = Bool`);
HNN extensions `HNNExtension G A B φ` of an assembled group with nontrivial `A` (the remaining
edges); and isomorphic copies. Every such group is freely indecomposable and not cyclic
(`IsIndecomposableGraphOfGroups.freelyIndecomposable_and_not_isCyclic`).
-/

set_option autoImplicit false

noncomputable section

universe u v w

namespace GC.Group

open GraphCoveringTheory.Kurosh Monoid.CoprodI

theorem FreelyIndecomposable.subsingleton_of_mulEquiv {G : Type u} [Group G]
    (hG : FreelyIndecomposable G) {B : Type v} {C : Type w} [Group B] [Group C]
    (e : G ≃* Monoid.Coprod B C) : Subsingleton B ∨ Subsingleton C := by
  let f₁ : B →* G := e.symm.toMonoidHom.comp Monoid.Coprod.inl
  let f₂ : C →* G := e.symm.toMonoidHom.comp Monoid.Coprod.inr
  have h₁ : Function.Injective f₁ := e.symm.injective.comp Monoid.Coprod.inl_injective
  have h₂ : Function.Injective f₂ := e.symm.injective.comp Monoid.Coprod.inr_injective
  let e₁ := MonoidHom.ofInjective h₁
  let e₂ := MonoidHom.ofInjective h₂
  rcases hG f₁.range f₂.range ⟨e.trans (e₁.coprodCongr e₂)⟩ with h | h
  · exact Or.inl (@Equiv.subsingleton _ _ e₁.toEquiv h)
  · exact Or.inr (@Equiv.subsingleton _ _ e₂.toEquiv h)

theorem FreelyIndecomposable.of_mulEquiv {G : Type u} {H : Type v} [Group G] [Group H]
    (hG : FreelyIndecomposable G) (e : G ≃* H) : FreelyIndecomposable H := by
  intro A B _ _ he
  obtain ⟨f⟩ := he
  exact hG.subsingleton_of_mulEquiv (e.trans f)

theorem FreelyIndecomposable.subsingleton_of_coprodI {G : Type u} [Group G]
    (hG : FreelyIndecomposable G) {ι : Type v} {M : ι → Type w} [∀ i, Group (M i)]
    (e : G ≃* Monoid.CoprodI M) {i j : ι} (hij : i ≠ j) [Nontrivial (M i)] :
    Subsingleton (M j) := by
  classical
  rcases hG.subsingleton_of_mulEquiv (e.trans (coprodIFactorEquiv M i)) with h | h
  · exact (not_subsingleton (M i) h).elim
  · refine ⟨fun x y => ?_⟩
    exact Monoid.CoprodI.of_injective (M := fun k : {k // k ≠ i} => M k.val)
      ⟨j, hij.symm⟩ (Subsingleton.elim _ _)

theorem isCyclic_freeGroup_of_subsingleton (X : Type u) [Subsingleton X] :
    IsCyclic (FreeGroup X) := by
  rw [isCyclic_iff_exists_zpowers_eq_top]
  rcases isEmpty_or_nonempty X with hX | ⟨⟨x⟩⟩
  · refine ⟨1, top_unique ?_⟩
    rw [← FreeGroup.closure_range_of, Subgroup.closure_le]
    rintro _ ⟨y, rfl⟩
    exact (IsEmpty.false y).elim
  · refine ⟨FreeGroup.of x, top_unique ?_⟩
    rw [← FreeGroup.closure_range_of, Subgroup.closure_le]
    rintro _ ⟨y, rfl⟩
    rw [Subsingleton.elim y x]
    exact Subgroup.mem_zpowers _

theorem FreelyIndecomposable.subsingleton_of_freeGroup {G : Type u} [Group G]
    (hG : FreelyIndecomposable G) {X : Type v} (e : G ≃* FreeGroup X) : Subsingleton X := by
  by_contra hX
  obtain ⟨x, y, hxy⟩ := (not_subsingleton_iff_nontrivial.mp hX).exists_pair_ne
  have h := hG.subsingleton_of_coprodI (e.trans freeGroupEquivCoprodI) hxy
  exact not_subsingleton (FreeGroup Unit) h

theorem FreelyIndecomposable.isCyclic_of_isFreeGroup {G : Type u} [Group G]
    (hG : FreelyIndecomposable G) {F : Type v} [Group F] [IsFreeGroup F] (e : G ≃* F) :
    IsCyclic G := by
  let e' := e.trans (IsFreeGroup.toFreeGroup F)
  let := hG.subsingleton_of_freeGroup e'
  exact e'.isCyclic.mpr (isCyclic_freeGroup_of_subsingleton _)

theorem exists_le_conjugateSubgroup_of_freelyIndecomposable {ι : Type v} (M : ι → Type u)
    [∀ i, Group (M i)] (H : Subgroup (FreeProduct M)) (hH : FreelyIndecomposable H)
    (hc : ¬ IsCyclic H) :
    ∃ (i : ι) (g : FreeProduct M),
      H ≤ conjugateSubgroup (MonoidHom.range (factorInclusion M i)) g := by
  classical
  let e := kuroshBassSerreEquiv M H
  have hHn : Nontrivial H := by
    by_contra h
    exact hc (@isCyclic_of_subsingleton _ _ (not_nontrivial_iff_subsingleton.mp h))
  have hex : ∃ q, Nontrivial (TreeKuroshComponent M H q) := by
    by_contra h
    have hs (q : TreeKuroshComponentIndex M H) : Subsingleton (TreeKuroshComponent M H q) :=
      not_nontrivial_iff_subsingleton.mp (fun hq => h ⟨q, hq⟩)
    have hz (z : TreeKuroshProduct M H) : z = 1 := by
      induction z using Monoid.CoprodI.induction_on with
      | one => rfl
      | of q a =>
          let := hs q
          rw [Subsingleton.elim a 1, map_one]
      | mul x y hx hy => rw [hx, hy, one_mul]
    obtain ⟨x, hx⟩ := exists_ne (1 : H)
    apply hx
    rw [← e.apply_symm_apply x, hz (e.symm x), map_one]
  obtain ⟨q, hq⟩ := hex
  have hothers (j : TreeKuroshComponentIndex M H) (hj : j ≠ q) :
      Subsingleton (TreeKuroshComponent M H j) :=
    hH.subsingleton_of_coprodI e.symm (Ne.symm hj)
  have hsurj := coprodI_of_surjective_of_others_trivial (TreeKuroshComponent M H) q hothers
  let f : TreeKuroshComponent M H q ≃* TreeKuroshProduct M H :=
    MulEquiv.ofBijective Monoid.CoprodI.of ⟨Monoid.CoprodI.of_injective q, hsurj⟩
  cases q with
  | inr q =>
      let g : H ≃* KuroshFreePart M H := e.symm.trans (f.symm.trans MulEquiv.ulift)
      exact (hc (hH.isCyclic_of_isFreeGroup g)).elim
  | inl a =>
      have htop : treeVertexStabilizer M H a = ⊤ := by
        apply top_unique
        intro x _
        obtain ⟨z, hz⟩ := hsurj (e.symm x)
        have hzx : treeKuroshComponentHom M H (Sum.inl a) z = x := by
          have hh : e (Monoid.CoprodI.of z) = treeKuroshComponentHom M H (Sum.inl a) z :=
            Monoid.CoprodI.lift_of _ _
          rw [← hh, hz, e.apply_symm_apply]
        change z.down.val = x at hzx
        exact hzx ▸ z.down.property
      rcases kurosh_vertex_stabilizer_classification M H a with h | h
      · obtain ⟨g, _, hbot⟩ := h
        have hbad : (⊥ : Subgroup H) = ⊤ := hbot.symm.trans htop
        exact (bot_ne_top hbad).elim
      · obtain ⟨i, g, _, heq⟩ := h
        refine ⟨i, g, ?_⟩
        intro x hx
        have hi : (⟨x, hx⟩ : H) ∈ intersectionFactorInH H i g := by
          rw [← heq, htop]; trivial
        exact hi.2

private theorem neWord_fstIdx_toWord {ι : Type u} {M : ι → Type v} [∀ i, Monoid (M i)]
    {i j : ι} (w : NeWord M i j) : w.toWord.fstIdx = some i := by
  change w.toList.head?.map Sigma.fst = some i
  simp

private theorem neWord_toWord_eq_of_prod_eq {ι : Type u} {M : ι → Type v}
    [∀ i, Monoid (M i)] {i j k l : ι} (w₁ : NeWord M i j) (w₂ : NeWord M k l)
    (h : w₁.prod = w₂.prod) : w₁.toWord = w₂.toWord := by
  classical
  exact (Word.equiv (M := M)).symm.injective h

theorem coprodI_index_eq_of_of_eq {ι : Type v} {M : ι → Type u} [∀ i, Group (M i)] {i j : ι}
    {a : M i} (ha : a ≠ 1) {b : M j} (h : (of a : Monoid.CoprodI M) = of b) : i = j := by
  classical
  have hb : b ≠ 1 := by
    rintro rfl
    rw [map_one] at h
    exact ha (Monoid.CoprodI.of_injective i (h.trans (map_one _).symm))
  have hw := neWord_toWord_eq_of_prod_eq (NeWord.singleton a ha) (NeWord.singleton b hb)
    (by rw [NeWord.prod_singleton, NeWord.prod_singleton, h])
  have hf := congrArg Word.fstIdx hw
  rw [neWord_fstIdx_toWord, neWord_fstIdx_toWord] at hf
  exact Option.some.inj hf

theorem coprodI_mem_range_of_of_conj_eq {ι : Type v} {M : ι → Type u} [∀ i, Group (M i)]
    {i j : ι} {a : M i} (ha : a ≠ 1) {b : M j} {m : Monoid.CoprodI M}
    (h : m⁻¹ * of a * m = of b) : m ∈ (of : M i →* Monoid.CoprodI M).range := by
  classical
  by_contra hm
  let p := Word.equivPair i (Word.equiv m)
  have ht : p.tail.prod = of p.head⁻¹ * m := by
    change (Word.equivPair i (Word.equiv m)).tail.prod = _
    rw [Word.equivPair_tail_eq_inv_smul, Word.prod_smul, map_inv]
    congr 1
    exact (Word.equiv (M := M)).symm_apply_apply m
  have hp : m = of p.head * p.tail.prod := by
    rw [ht, map_inv, mul_inv_cancel_left]
  have hne : p.tail ≠ Word.empty := by
    intro he
    apply hm
    refine ⟨p.head, ?_⟩
    rw [hp, he, Word.prod_empty, mul_one]
  obtain ⟨k, l, w, hw⟩ := NeWord.of_word p.tail hne
  have hk : k ≠ i := by
    intro hki
    apply p.fstIdx_ne
    rw [← hw, neWord_fstIdx_toWord, hki]
  have hwp : w.prod = p.tail.prod := by
    change w.toWord.prod = _
    rw [hw]
  let a' := p.head⁻¹ * a * p.head
  have ha' : a' ≠ 1 := by
    intro h1
    apply ha
    have h2 : p.head * a' * p.head⁻¹ = a := by simp only [a']; group
    rw [← h2, h1, mul_one, mul_inv_cancel]
  let W := NeWord.append (NeWord.append w.inv hk (NeWord.singleton a' ha')) hk.symm w
  have hW : W.prod = of b := by
    rw [NeWord.append_prod, NeWord.append_prod, NeWord.inv_prod, NeWord.prod_singleton, ← h,
      hp, hwp]
    simp only [a', map_mul, map_inv, mul_inv_rev]
    group
  have hlen : 3 ≤ W.toList.length := by
    have h1 := List.length_pos_of_ne_nil (NeWord.toList_ne_nil w.inv)
    have h2 := List.length_pos_of_ne_nil (NeWord.toList_ne_nil w)
    simp only [W, NeWord.toList, List.length_append, List.length_singleton]
    omega
  by_cases hb : b = 1
  · have hW1 : W.toWord = Word.empty :=
      (Word.equiv (M := M)).symm.injective (by
        change W.prod = Word.empty.prod
        rw [hW, hb, map_one, Word.prod_empty])
    have hl := congrArg (fun z : Word M => z.toList.length) hW1
    simp only [Word.empty] at hl
    change W.toList.length = 0 at hl
    omega
  · have hW1 := neWord_toWord_eq_of_prod_eq W (NeWord.singleton b hb)
      (by rw [hW, NeWord.prod_singleton])
    have hl := congrArg (fun z : Word M => z.toList.length) hW1
    change W.toList.length = (NeWord.singleton b hb).toList.length at hl
    simp only [NeWord.toList, List.length_singleton] at hl
    omega

theorem conjugateSubgroup_factor_malnormal {ι : Type v} {M : ι → Type u}
    [∀ i, Group (M i)] {i j : ι} {g h x : FreeProduct M} (hx : x ≠ 1)
    (hg : x ∈ conjugateSubgroup (MonoidHom.range (factorInclusion M i)) g)
    (hh : x ∈ conjugateSubgroup (MonoidHom.range (factorInclusion M j)) h) :
    i = j ∧ g⁻¹ * h ∈ MonoidHom.range (factorInclusion M i) := by
  rw [mem_conjugateSubgroup_iff] at hg hh
  obtain ⟨a, ha⟩ := hg
  obtain ⟨b, hb⟩ := hh
  simp only [factorInclusion_apply] at ha hb
  have ha1 : a ≠ 1 := by
    rintro rfl
    apply hx
    have h1 : x = g * (g⁻¹ * x * g) * g⁻¹ := by group
    rw [h1, ← ha, map_one, mul_one, mul_inv_cancel]
  have hm : (g⁻¹ * h)⁻¹ * of a * (g⁻¹ * h) = of b := by
    rw [ha, hb]
    group
  obtain ⟨c, hc⟩ := coprodI_mem_range_of_of_conj_eq ha1 hm
  have hc' : (of (c⁻¹ * a * c) : Monoid.CoprodI M) = of b := by
    rw [map_mul, map_mul, map_inv, hc, ← hm]
  have hca : c⁻¹ * a * c ≠ 1 := by
    intro h1
    apply ha1
    have h2 : a = c * (c⁻¹ * a * c) * c⁻¹ := by group
    rw [h2, h1, mul_one, mul_inv_cancel]
  exact ⟨coprodI_index_eq_of_of_eq hca hc', ⟨c, hc⟩⟩

theorem conjugateSubgroup_factor_eq_of_mem {ι : Type v} {M : ι → Type u}
    [∀ i, Group (M i)] {i j : ι} {g h x : FreeProduct M} (hx : x ≠ 1)
    (hg : x ∈ conjugateSubgroup (MonoidHom.range (factorInclusion M i)) g)
    (hh : x ∈ conjugateSubgroup (MonoidHom.range (factorInclusion M j)) h) :
    conjugateSubgroup (MonoidHom.range (factorInclusion M i)) g =
      conjugateSubgroup (MonoidHom.range (factorInclusion M j)) h := by
  obtain ⟨hij, hgh⟩ := conjugateSubgroup_factor_malnormal hx hg hh
  subst hij
  ext z
  simp only [mem_conjugateSubgroup_iff]
  have hz : h⁻¹ * z * h = (g⁻¹ * h)⁻¹ * (g⁻¹ * z * g) * (g⁻¹ * h) := by group
  rw [hz]
  constructor
  · intro hz'
    exact mul_mem (mul_mem (inv_mem hgh) hz') hgh
  · intro hz'
    have h2 : g⁻¹ * z * g =
        (g⁻¹ * h) * ((g⁻¹ * h)⁻¹ * (g⁻¹ * z * g) * (g⁻¹ * h)) * (g⁻¹ * h)⁻¹ := by group
    rw [h2]
    exact mul_mem (mul_mem hgh hz') (inv_mem hgh)

theorem subsingleton_of_forall_mem_conjugateSubgroup {ι : Type v} {M : ι → Type u}
    [∀ i, Group (M i)] {i j : ι} (hij : i ≠ j) (g : FreeProduct M)
    (h : ∀ z, z ∈ conjugateSubgroup (MonoidHom.range (factorInclusion M i)) g) :
    Subsingleton (M j) := by
  have h1 (y : M j) : y = 1 := by
    by_contra hy
    have hx : (of y : FreeProduct M) ≠ 1 := by
      intro h0
      exact hy (Monoid.CoprodI.of_injective j (h0.trans (map_one _).symm))
    have hj : (of y : FreeProduct M) ∈
        conjugateSubgroup (MonoidHom.range (factorInclusion M j)) 1 := by
      rw [mem_conjugateSubgroup_iff]
      exact ⟨y, by simp⟩
    exact hij (conjugateSubgroup_factor_malnormal hx (h _) hj).1
  exact ⟨fun a b => (h1 a).trans (h1 b).symm⟩

theorem freelyIndecomposable_of_forall_conjugate {G : Type u} [Group G]
    (h : ∀ (X Y : Type u) [Group X] [Group Y]
      (f : G ≃* FreeProduct (DifferentialGeometry.Algebra.Group.boolCoprodFamily X Y)),
      ∃ (i : Bool) (g : FreeProduct (DifferentialGeometry.Algebra.Group.boolCoprodFamily X Y)),
        ∀ x : G, f x ∈ conjugateSubgroup (MonoidHom.range (factorInclusion _ i)) g) :
    FreelyIndecomposable G := by
  intro X Y _ _ he
  obtain ⟨e⟩ := he
  let f := e.trans (DifferentialGeometry.Algebra.Group.coprodIBoolEquivCoprod X Y).symm
  obtain ⟨i, g, hi⟩ := h X Y f
  have hall (z : FreeProduct (DifferentialGeometry.Algebra.Group.boolCoprodFamily X Y)) :
      z ∈ conjugateSubgroup (MonoidHom.range (factorInclusion _ i)) g := by
    obtain ⟨x, rfl⟩ := f.surjective z
    exact hi x
  cases i
  · have hs := subsingleton_of_forall_mem_conjugateSubgroup Bool.false_ne_true g hall
    exact Or.inr ⟨fun a b => ULift.up_injective (@Subsingleton.elim _ hs _ _)⟩
  · have hs := subsingleton_of_forall_mem_conjugateSubgroup Bool.false_ne_true.symm g hall
    exact Or.inl ⟨fun a b => ULift.up_injective (@Subsingleton.elim _ hs _ _)⟩

theorem freelyIndecomposable_pushoutI {ι : Type v} [Nonempty ι] {G : ι → Type u}
    [∀ i, Group (G i)] {C : Type w} [Group C] [Nontrivial C] (φ : ∀ i, C →* G i)
    (hφ : ∀ i, Function.Injective (φ i)) (hG : ∀ i, FreelyIndecomposable (G i))
    (hc : ∀ i, ¬ IsCyclic (G i)) : FreelyIndecomposable (Monoid.PushoutI φ) := by
  apply freelyIndecomposable_of_forall_conjugate
  intro X Y _ _ f
  have key (i : ι) : ∃ (k : Bool) (g : FreeProduct _),
      (f.toMonoidHom.comp (Monoid.PushoutI.of i)).range ≤
        conjugateSubgroup (MonoidHom.range (factorInclusion _ k)) g := by
    have hinj := f.injective.comp (Monoid.PushoutI.of_injective hφ i)
    let e := MonoidHom.ofInjective (f := f.toMonoidHom.comp (Monoid.PushoutI.of i)) hinj
    exact exists_le_conjugateSubgroup_of_freelyIndecomposable _ _ ((hG i).of_mulEquiv e)
      (fun h => hc i (e.isCyclic.mpr h))
  choose k g hk using key
  obtain ⟨i₀⟩ := ‹Nonempty ι›
  obtain ⟨c, hc1⟩ := exists_ne (1 : C)
  have hx : f (Monoid.PushoutI.base φ c) ≠ 1 := by
    intro h1
    apply hc1
    apply Monoid.PushoutI.base_injective hφ
    apply f.injective
    rw [h1, map_one, map_one]
  have hxi (i : ι) : f (Monoid.PushoutI.base φ c) ∈
      conjugateSubgroup (MonoidHom.range (factorInclusion _ (k i))) (g i) :=
    hk i ⟨φ i c, by simp [Monoid.PushoutI.of_apply_eq_base]⟩
  have heq (i : ι) := conjugateSubgroup_factor_eq_of_mem hx (hxi i) (hxi i₀)
  refine ⟨k i₀, g i₀, fun z => ?_⟩
  induction z using Monoid.PushoutI.induction_on with
  | of i a =>
      rw [← heq i]
      exact hk i ⟨a, rfl⟩
  | base c' =>
      rw [← heq i₀]
      exact hk i₀ ⟨φ i₀ c', by simp [Monoid.PushoutI.of_apply_eq_base]⟩
  | mul x y hx hy =>
      rw [map_mul]
      exact mul_mem hx hy

theorem freelyIndecomposable_pushout {G : Bool → Type u} [∀ i, Group (G i)] {C : Type w}
    [Group C] [Nontrivial C] (φ : ∀ i, C →* G i) (hφ : ∀ i, Function.Injective (φ i))
    (hG : ∀ i, FreelyIndecomposable (G i)) (hc : ∀ i, ¬ IsCyclic (G i)) :
    FreelyIndecomposable (Monoid.PushoutI φ) :=
  freelyIndecomposable_pushoutI φ hφ hG hc

theorem freelyIndecomposable_hnnExtension {G : Type u} [Group G] {A B : Subgroup G}
    [Nontrivial A] (φ : A ≃* B) (hG : FreelyIndecomposable G) (hc : ¬ IsCyclic G) :
    FreelyIndecomposable (HNNExtension G A B φ) := by
  apply freelyIndecomposable_of_forall_conjugate
  intro X Y _ _ f
  have hinj := f.injective.comp (HNNExtension.of_injective (φ := φ))
  let e := MonoidHom.ofInjective (f := f.toMonoidHom.comp HNNExtension.of) hinj
  obtain ⟨k, g, hk⟩ := exists_le_conjugateSubgroup_of_freelyIndecomposable _ _
    (hG.of_mulEquiv e) (fun h => hc (e.isCyclic.mpr h))
  obtain ⟨a, ha⟩ := exists_ne (1 : A)
  have hx : f (HNNExtension.of (a : G)) ≠ 1 := by
    intro h1
    apply ha
    apply Subtype.ext
    apply hinj
    change f (HNNExtension.of (a : G)) = f (HNNExtension.of 1)
    rw [h1, map_one, map_one]
  have h1 : f (HNNExtension.of (a : G)) ∈
      conjugateSubgroup (MonoidHom.range (factorInclusion _ k)) g := hk ⟨a, rfl⟩
  have h2 : f (HNNExtension.of (a : G)) ∈
      conjugateSubgroup (MonoidHom.range (factorInclusion _ k)) (f HNNExtension.t⁻¹ * g) := by
    have h3 : f (HNNExtension.of (φ a : G)) ∈
        conjugateSubgroup (MonoidHom.range (factorInclusion _ k)) g := hk ⟨φ a, rfl⟩
    rw [HNNExtension.equiv_eq_conj, map_mul, map_mul] at h3
    rw [mem_conjugateSubgroup_iff] at h3 ⊢
    convert h3 using 1
    simp only [map_inv, mul_inv_rev, inv_inv]
    group
  obtain ⟨-, hs⟩ := conjugateSubgroup_factor_malnormal hx h2 h1
  have ht : f HNNExtension.t ∈ conjugateSubgroup (MonoidHom.range (factorInclusion _ k)) g := by
    rw [mem_conjugateSubgroup_iff]
    convert hs using 1
    simp only [map_inv, mul_inv_rev, inv_inv]
  refine ⟨k, g, fun z => ?_⟩
  induction z using HNNExtension.induction_on with
  | of a => exact hk ⟨a, rfl⟩
  | t => exact ht
  | mul x y hx hy =>
      rw [map_mul]
      exact mul_mem hx hy
  | inv x hx =>
      rw [map_inv]
      exact inv_mem hx

inductive IsIndecomposableGraphOfGroups : (G : Type u) → [Group G] → Prop
  | vertex (G : Type u) [Group G] (hG : FreelyIndecomposable G) (hc : ¬ IsCyclic G) :
      IsIndecomposableGraphOfGroups G
  | amalgam {ι : Type} [Nonempty ι] (G : ι → Type u) [∀ i, Group (G i)] (C : Type u)
      [Group C] [Nontrivial C] (φ : ∀ i, C →* G i) (hφ : ∀ i, Function.Injective (φ i))
      (hG : ∀ i, IsIndecomposableGraphOfGroups (G i)) :
      IsIndecomposableGraphOfGroups (Monoid.PushoutI φ)
  | hnn (G : Type u) [Group G] (A B : Subgroup G) [Nontrivial A] (φ : A ≃* B)
      (hG : IsIndecomposableGraphOfGroups G) :
      IsIndecomposableGraphOfGroups (HNNExtension G A B φ)
  | congr {G H : Type u} [Group G] [Group H] (e : G ≃* H)
      (hG : IsIndecomposableGraphOfGroups G) : IsIndecomposableGraphOfGroups H

theorem IsIndecomposableGraphOfGroups.freelyIndecomposable_and_not_isCyclic {G : Type u}
    [Group G] (h : IsIndecomposableGraphOfGroups G) :
    FreelyIndecomposable G ∧ ¬ IsCyclic G := by
  induction h with
  | vertex _ hG hc => exact ⟨hG, hc⟩
  | amalgam _ _ φ hφ _ ih =>
      refine ⟨freelyIndecomposable_pushoutI φ hφ (fun i => (ih i).1) (fun i => (ih i).2), ?_⟩
      intro hcyc
      obtain ⟨i⟩ := ‹Nonempty _›
      exact (ih i).2 (isCyclic_of_injective _ (Monoid.PushoutI.of_injective hφ i))
  | hnn _ _ _ φ _ ih =>
      refine ⟨freelyIndecomposable_hnnExtension φ ih.1 ih.2, ?_⟩
      intro hcyc
      exact ih.2 (isCyclic_of_injective _ (HNNExtension.of_injective (φ := φ)))
  | congr e _ ih => exact ⟨ih.1.of_mulEquiv e, fun hcyc => ih.2 (e.isCyclic.mpr hcyc)⟩

theorem IsIndecomposableGraphOfGroups.freelyIndecomposable {G : Type u} [Group G]
    (h : IsIndecomposableGraphOfGroups G) : FreelyIndecomposable G :=
  h.freelyIndecomposable_and_not_isCyclic.1

theorem not_isCyclic_of_mul_ne {G : Type u} [Group G] (a b : G) (h : a * b ≠ b * a) :
    ¬ IsCyclic G := by
  intro hc
  obtain ⟨g, hg⟩ := IsCyclic.exists_generator (α := G)
  obtain ⟨m, rfl⟩ := Subgroup.mem_zpowers_iff.mp (hg a)
  obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.mp (hg b)
  exact h (zpow_mul_comm g m n)

theorem IsIndecomposableGraphOfGroups.vertex_of_center (G : Type u) [Group G] (z : G)
    (hz : z ≠ 1) (hcen : ∀ x : G, x * z = z * x) (hc : ¬ IsCyclic G) :
    IsIndecomposableGraphOfGroups G :=
  .vertex G (freelyIndecomposable_of_center_nontrivial G z hz hcen) hc

end GC.Group
