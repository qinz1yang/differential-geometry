/-
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hongzhou Lin
-/
import Mathlib.Algebra.CharP.Defs
import Mathlib.Algebra.Order.Archimedean.Real.Basic
import Mathlib.GroupTheory.Index

noncomputable section

namespace DifferentialGeometry.CosetGrowth

variable {G X : Type*} [Group G]

theorem exists_generator_exit [MulAction G X] [MulAction.IsPretransitive G X]
    (S : Set G) (hgen : Subgroup.closure S = ⊤)
    (hSinv : ∀ s ∈ S, s⁻¹ ∈ S) (F : Finset X) (hF : F.Nonempty)
    (hproper : ∃ y : X, y ∉ F) :
    ∃ s ∈ S, ∃ x ∈ F, s • x ∉ F := by
  classical
  by_contra h
  have hclosed : ∀ s ∈ S, ∀ x ∈ F, s • x ∈ F := by
    intro s hs x hx
    by_contra hnot
    exact h ⟨s, hs, x, hx, hnot⟩
  have hact : ∀ g : G, ∀ x ∈ F, g • x ∈ F ∧ g⁻¹ • x ∈ F := by
    intro g
    have hg : g ∈ Subgroup.closure S := by rw [hgen]; trivial
    refine Subgroup.closure_induction ?_ ?_ ?_ ?_ hg
    · intro s hs x hx
      exact ⟨hclosed s hs x hx, hclosed s⁻¹ (hSinv s hs) x hx⟩
    · intro x hx
      simpa only [inv_one, one_smul] using And.intro hx hx
    · intro a b _ _ ha hb x hx
      constructor
      · rw [mul_smul]
        exact (ha (b • x) (hb x hx).1).1
      · rw [mul_inv_rev, mul_smul]
        exact (hb (a⁻¹ • x) (ha x hx).2).2
    · intro a _ ha x hx
      simpa only [inv_inv] using (ha x hx).symm
  obtain ⟨x, hx⟩ := hF
  obtain ⟨y, hy⟩ := hproper
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq G x y
  exact hy (hg ▸ (hact g x hx).1)

theorem exists_separated_representatives (S : Set G) (hgen : Subgroup.closure S = ⊤)
    (hSinv : ∀ s ∈ S, s⁻¹ ∈ S) (H : Subgroup G) [Infinite (G ⧸ H)]
    (d : G → ℝ) (hd1 : d 1 = 0) (hdmul : ∀ a b, d (a * b) ≤ d a + d b)
    {r : ℝ} (hr : 0 ≤ r) (hS : ∀ s ∈ S, d s ≤ r) (k : ℕ) :
    ∃ F : Finset G, F.card = k + 1 ∧
      Set.InjOn (QuotientGroup.mk : G → G ⧸ H) F ∧
      ∀ g ∈ F, d g ≤ (k : ℝ) * r := by
  classical
  let q : G → G ⧸ H := QuotientGroup.mk
  induction k with
  | zero =>
    refine ⟨{1}, by simp, ?_, ?_⟩
    · intro a ha b hb _
      have ha' : a = 1 := Finset.mem_singleton.mp ha
      have hb' : b = 1 := Finset.mem_singleton.mp hb
      exact ha'.trans hb'.symm
    · intro g hg
      rw [Finset.mem_singleton.mp hg, hd1]
      simp
  | succ k ih =>
    obtain ⟨F, hcard, hinj, hbound⟩ := ih
    have hF : F.Nonempty := Finset.card_pos.mp (by omega)
    obtain ⟨s, hs, z, hz, hout⟩ :=
      exists_generator_exit S hgen hSinv (F.image q) (hF.image q)
        (Infinite.exists_notMem_finset (F.image q))
    obtain ⟨g, hg, rfl⟩ := Finset.mem_image.mp hz
    change q (s * g) ∉ F.image q at hout
    have hnew : s * g ∉ F := fun h => hout (Finset.mem_image_of_mem q h)
    refine ⟨insert (s * g) F, by rw [Finset.card_insert_of_notMem hnew, hcard], ?_, ?_⟩
    · intro a ha b hb hab
      rcases Finset.mem_insert.mp ha with rfl | ha
      · rcases Finset.mem_insert.mp hb with rfl | hb
        · rfl
        · apply False.elim
          apply hout
          change q (s * g) = q b at hab
          rw [hab]
          exact Finset.mem_image_of_mem q hb
      · rcases Finset.mem_insert.mp hb with rfl | hb
        · apply False.elim
          apply hout
          change q a = q (s * g) at hab
          rw [← hab]
          exact Finset.mem_image_of_mem q ha
        · exact hinj ha hb hab
    · intro a ha
      rcases Finset.mem_insert.mp ha with rfl | ha
      · have h := (hdmul s g).trans (add_le_add (hS s hs) (hbound g hg))
        simpa only [Nat.cast_add, Nat.cast_one, add_mul, one_mul, add_comm] using h
      · have h := hbound a ha
        push_cast
        nlinarith

theorem finiteIndex_of_cover {ι : Type*} (S : Set G) (hgen : Subgroup.closure S = ⊤)
    (hSinv : ∀ s ∈ S, s⁻¹ ∈ S) (H : Subgroup G)
    (d : G → ℝ) (hd1 : d 1 = 0) (hdmul : ∀ a b, d (a * b) ≤ d a + d b)
    {r : ℝ} (hr : 0 ≤ r) (hS : ∀ s ∈ S, d s ≤ r)
    (F : Finset ι) (P : ι → G → Prop) (hscale : (F.card : ℝ) * r ≤ 1)
    (hcover : ∀ g : G, d g ≤ 1 → ∃ i ∈ F, P i g)
    (hcoset : ∀ i : ι, ∀ a b : G, P i a → P i b → a⁻¹ * b ∈ H) :
    H.FiniteIndex := by
  classical
  apply Subgroup.finiteIndex_iff_finite_quotient.mpr
  by_contra hfinite
  let : Infinite (G ⧸ H) := not_finite_iff_infinite.mp hfinite
  obtain ⟨A, hcard, hinj, hbound⟩ :=
    exists_separated_representatives S hgen hSinv H d hd1 hdmul hr hS F.card
  have hchoice : ∀ a : A, ∃ i : F, P i a := by
    intro a
    obtain ⟨i, hi, hia⟩ := hcover a ((hbound a a.property).trans hscale)
    exact ⟨⟨i, hi⟩, hia⟩
  choose c hc using hchoice
  have hc_inj : Function.Injective c := by
    intro a b hab
    apply Subtype.ext
    apply hinj a.property b.property
    apply QuotientGroup.eq.mpr
    exact hcoset (c a) a b (hc a) (by rw [hab]; exact hc b)
  have hle := Fintype.card_le_of_injective c hc_inj
  simp only [Fintype.card_coe] at hle
  omega

end DifferentialGeometry.CosetGrowth
