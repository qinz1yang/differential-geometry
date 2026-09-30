import DifferentialGeometry.Topology.FundamentalGroup.FiniteGeneration.FiniteLocalCover
import DifferentialGeometry.Topology.VanKampen.TorsionFreeCover
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open Set Metric CategoryTheory
open scoped unitInterval
open DifferentialGeometry.Topology.VanKampen
namespace GC.Topology
universe u v w

theorem exists_indexed_covered_subdivision {X : Type u} [TopologicalSpace X]
    {ι : Type v} (V : ι → Set X) (hopen : ∀ i, IsOpen (V i))
    (hcover : (⋃ i, V i) = univ) {a b : X} (p : _root_.Path a b) :
    ∃ n : ℕ, 0 < n ∧ ∀ j : Fin n, ∃ i, range (standardSubpath p j) ⊆ V i := by
  have hc : (univ : Set unitInterval) ⊆ ⋃ i, p ⁻¹' V i := by
    intro t _
    have ht : p t ∈ ⋃ i, V i := hcover ▸ mem_univ _
    obtain ⟨i, hi⟩ := mem_iUnion.mp ht
    exact mem_iUnion.mpr ⟨i, hi⟩
  obtain ⟨δ, hδ, hball⟩ := lebesgue_number_lemma_of_metric isCompact_univ
    (fun i => (hopen i).preimage p.continuous) hc
  obtain ⟨m, hm⟩ := exists_nat_one_div_lt (K := ℝ) hδ
  let n := m + 1
  have hn : 0 < n := Nat.succ_pos m
  have hmesh : 1 / (n : ℝ) < δ := by simpa [n] using hm
  refine ⟨n, hn, ?_⟩
  intro j
  obtain ⟨i, hi⟩ := hball (standardTime n j.castSucc) (mem_univ _)
  refine ⟨i, ?_⟩
  rw [standardSubpath, _root_.Path.range_subpath_of_le _ _ _
    (standardTime_castSucc_le_succ hn j)]
  rintro _ ⟨t, ht, rfl⟩
  apply hi
  rw [mem_ball]
  simpa [dist_comm] using (Path.dist_standardTime_le hn j t ht).trans_lt hmesh

theorem functor_concat_mem {X : Type u} [TopologicalSpace X] {G : Type w} [Group G]
    (F : FundamentalGroupoid X ⥤ SingleObj G) (S : Subgroup G)
    {n : ℕ} (x : Fin (n + 1) → X)
    (p : ∀ i : Fin n, _root_.Path (x i.castSucc) (x i.succ))
    (hp : ∀ i, F.map (show FundamentalGroupoid.mk (x i.castSucc) ⟶
      FundamentalGroupoid.mk (x i.succ) from ⟦p i⟧) ∈ S) :
    F.map (show FundamentalGroupoid.mk (x 0) ⟶ FundamentalGroupoid.mk (x (Fin.last n))
      from ⟦_root_.Path.concat x p⟧) ∈ S := by
  induction n with
  | zero =>
    simp only [_root_.Path.concat_zero]
    change F.map (𝟙 (FundamentalGroupoid.mk (x 0))) ∈ S
    rw [CategoryTheory.Functor.map_id]
    exact S.one_mem
  | succ n ih =>
    rw [_root_.Path.concat_succ]
    change F.map ((show FundamentalGroupoid.mk (x 0) ⟶ FundamentalGroupoid.mk (x (Fin.last n).castSucc)
      from ⟦_root_.Path.concat (x ∘ Fin.castSucc) (fun i => p i.castSucc)⟧) ≫
        (show FundamentalGroupoid.mk (x (Fin.last n).castSucc) ⟶
          FundamentalGroupoid.mk (x (Fin.last (n + 1))) from ⟦p (Fin.last n)⟧)) ∈ S
    rw [Functor.map_comp]
    exact S.mul_mem (hp (Fin.last n))
      (ih (x ∘ Fin.castSucc) (fun i => p i.castSucc) (fun i => hp i.castSucc))

theorem functor_map_pathCast {X : Type u} [TopologicalSpace X] {G : Type w} [Group G]
    (F : FundamentalGroupoid X ⥤ SingleObj G) {a b a' b' : X}
    (p : _root_.Path a b) (ha : a' = a) (hb : b' = b) :
    F.map (show FundamentalGroupoid.mk a' ⟶ FundamentalGroupoid.mk b'
      from ⟦p.cast ha hb⟧) =
    F.map (show FundamentalGroupoid.mk a ⟶ FundamentalGroupoid.mk b from ⟦p⟧) := by
  subst a'
  subst b'
  rfl

theorem functor_path_mem_of_cover {X : Type u} [TopologicalSpace X]
    {ι : Type v} (V : ι → Set X) (hopen : ∀ i, IsOpen (V i))
    (hcover : (⋃ i, V i) = univ) {G : Type w} [Group G]
    (F : FundamentalGroupoid X ⥤ SingleObj G) (S : Subgroup G)
    (hlocal : ∀ i {a b : X} (p : _root_.Path a b), range p ⊆ V i →
      F.map (show FundamentalGroupoid.mk a ⟶ FundamentalGroupoid.mk b from ⟦p⟧) ∈ S)
    {a b : X} (p : _root_.Path a b) :
    F.map (show FundamentalGroupoid.mk a ⟶ FundamentalGroupoid.mk b from ⟦p⟧) ∈ S := by
  change F.map (X := FundamentalGroupoid.mk a) (Y := FundamentalGroupoid.mk b)
    (Path.Homotopic.Quotient.mk p) ∈ S
  obtain ⟨n, hn, hcov⟩ := exists_indexed_covered_subdivision V hopen hcover p
  have hchain := functor_concat_mem F S (p ∘ standardTime n) (standardSubpath p) (by
    intro j
    obtain ⟨i, hi⟩ := hcov j
    exact hlocal i _ hi)
  have he := congrArg (fun f : FundamentalGroupoid.mk a ⟶ FundamentalGroupoid.mk b => F.map f)
    (standardConcat_quotient_eq p hn)
  have hstd : F.map (X := FundamentalGroupoid.mk a) (Y := FundamentalGroupoid.mk b)
      (Path.Homotopic.Quotient.mk (standardConcat p hn)) ∈ S := by
    change F.map (show FundamentalGroupoid.mk a ⟶ FundamentalGroupoid.mk b from
      ⟦(_root_.Path.concat (p ∘ standardTime n) (standardSubpath p)).cast _ _⟧) ∈ S
    have hc := functor_map_pathCast F (_root_.Path.concat (p ∘ standardTime n) (standardSubpath p))
      (show a = p (standardTime n 0) from by simp)
      (show b = p (standardTime n (Fin.last n)) from by simp [standardTime_last hn])
    exact hc.symm ▸ hchain
  exact he ▸ hstd

end GC.Topology
