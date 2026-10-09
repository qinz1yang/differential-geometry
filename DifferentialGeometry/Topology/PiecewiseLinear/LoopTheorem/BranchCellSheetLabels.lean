/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.Topology.Covering.CyclicSheetLabels
import DifferentialGeometry.Topology.PiecewiseLinear.LoopTheorem.BranchSourceSections

open Set

namespace DifferentialGeometry.Topology.PiecewiseLinear.NormalSingularCellData

universe u

variable {M : Type u} [TopologicalSpace M] [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
  [T2Space M] {D : SingularTwoCell M} {BdM B : Set M}
  {E : Type*} [TopologicalSpace E] [T2Space E]

open Classical in
theorem exists_source_sheet_labels_on_cyclic_cells
    (hD : NormalSingularCellData D BdM B) {c : hD.singularSet.Branch}
    {ι : M → E} (hιc : Continuous ι) (hι : Function.Injective ι)
    {J : Set (EuclideanSpace ℝ (Fin 2))} (hJ : IsPLSphere 1 J)
    (hpreJ : hD.branchPreimage c = J) (a₀ : hD.branchPreimage c)
    {m : ℕ} (H : ℕ → Set E) (A : ℕ → Bool → Set (EuclideanSpace ℝ (Fin 2)))
    (hH : ∀ k ≤ m, IsClosed (H k))
    (hcover : ι '' hD.singularSet.branchCarrier c ⊆ ⋃ k ≤ m, H k)
    (hAc : ∀ k b, IsCompact (A k b)) (hAdom : ∀ k b, A k b ⊆ D.domain)
    (hAi : ∀ k b, InjOn D (A k b)) (hAA : ∀ k, Disjoint (A k false) (A k true))
    (hpre : ∀ k, ∀ x ∈ D.domain, ι (D x) ∈ H k → x ∈ A k false ∪ A k true)
    (hcore : ∀ k b, ∀ y ∈ hD.singularSet.branchCarrier c,
      ι y ∈ H k → y ∈ D '' (A k b ∩ J))
    (y : ℕ → E) (hy : ∀ k < m, y k ∈ ι '' hD.singularSet.branchCarrier c)
    (hadj : ∀ k < m,
      (ι '' hD.singularSet.branchCarrier c) ∩ (H k ∩ H (k + 1)) = {y k})
    {z : E} (hz : z ∈ ι '' hD.singularSet.branchCarrier c)
    (hseam : (ι '' hD.singularSet.branchCarrier c) ∩ (H 0 ∩ H m) = {z})
    (hfar : ∀ j k, j + 1 < k → k ≤ m → (j ≠ 0 ∨ k ≠ m) → Disjoint (H j) (H k))
    (b₀ : Bool) :
    ∃ b : ℕ → Bool, b 0 = b₀ ∧
      (∀ k < m, ∀ u : Bool, ∃ a ∈ J,
        a ∈ A k (Bool.xor u (b k)) ∧ a ∈ A (k + 1) (Bool.xor u (b (k + 1))) ∧
          ι (D a) = y k) ∧
      ∀ u : Bool, ∃ a ∈ J,
        a ∈ A m (Bool.xor u (b m)) ∧ a ∈ A 0 (Bool.xor (!u) (b 0)) ∧ ι (D a) = z := by
  let P := hD.singularSet.branchPieceIn c
  let F : P.complex.space → E := fun x => ι (P.map x)
  have hFc : Continuous F := hιc.comp P.continuousOn.domRestrict
  have hFi : Function.Injective F := fun x y h =>
    Subtype.ext (P.bijOn.injOn x.2 y.2 (hι h))
  have hFG : ∀ x, F x ∈ ι '' hD.singularSet.branchCarrier c :=
    fun x => ⟨P.map x, P.bijOn.mapsTo x.2, rfl⟩
  have hsurj : ∀ x ∈ ι '' hD.singularSet.branchCarrier c, ∃ q, F q = x := by
    rintro x ⟨v, hv, rfl⟩
    obtain ⟨q, hq, hqv⟩ := P.bijOn.surjOn hv
    exact ⟨⟨q, hq⟩, congrArg ι hqv⟩
  obtain ⟨z', hz'⟩ := hsurj z hz
  have hqexist : ∀ k : ℕ, ∃ q : P.complex.space, k < m → F q = y k := by
    intro k
    by_cases hk : k < m
    · obtain ⟨q, hq⟩ := hsurj (y k) (hy k hk)
      exact ⟨q, fun _ => hq⟩
    · exact ⟨z', fun h => (hk h).elim⟩
  choose q hq using hqexist
  let Ck : ℕ → Set P.complex.space := fun k => F ⁻¹' H k
  obtain ⟨s, hsc, hss, hsne, hsfib⟩ :=
    hD.exists_branch_sections_of_compact_source_sheets hιc hι hpreJ a₀ A H hAc hAdom
      hAi hAA hpre hcore
  have hCcover : ⋃ k ≤ m, Ck k = univ := by
    ext x
    constructor
    · exact fun _ => mem_univ _
    · intro _
      obtain ⟨k, hk, hx⟩ := mem_iUnion₂.mp (hcover (hFG x))
      exact mem_iUnion₂.mpr ⟨k, hk, hx⟩
  have hqmem : ∀ k < m, q k ∈ Ck k ∩ Ck (k + 1) := by
    intro k hk
    have h := (hadj k hk).symm.subset (mem_singleton (y k))
    change F (q k) ∈ H k ∩ H (k + 1)
    rw [hq k hk]
    exact h.2
  have hcadj : ∀ k < m, Ck k ∩ Ck (k + 1) ⊆ {q k} := by
    intro k hk x hx
    apply hFi
    exact (hadj k hk).subset ⟨hFG x, hx⟩ |>.trans (hq k hk).symm
  have hcz : z' ∈ Ck 0 ∩ Ck m := by
    change F z' ∈ H 0 ∩ H m
    rw [hz']
    exact (hseam.symm.subset (mem_singleton z)).2
  have hcseam : Ck 0 ∩ Ck m ⊆ {z'} := by
    intro x hx
    apply hFi
    exact (hseam.subset ⟨hFG x, hx⟩).trans hz'.symm
  have hcfar : ∀ j k, j + 1 < k → k ≤ m → (j ≠ 0 ∨ k ≠ m) →
      Disjoint (Ck j) (Ck k) :=
    fun j k hjk hk hjm => disjoint_left.mpr fun x hxj hxk =>
      disjoint_left.mp (hfar j k hjk hk hjm) hxj hxk
  obtain ⟨b, hb0, hb, hbc⟩ := Covering.exists_cyclic_two_section_labels
    (hD.not_exists_rightInverse_branchProjection_of_isPLSphere_one c hJ hpreJ) Ck s
    (fun k hk => (hH k hk).preimage hFc) hCcover
    (fun k _ u => hsc k u) (fun k _ u x hx => (hss k u x hx).2)
    (fun k _ x hx => hsne k x hx) (fun k _ x hx => hsfib k x hx)
    q hqmem hcadj hcfar hcz hcseam b₀
  have hpD : ∀ x : hD.branchPreimage c, P.map (hD.branchProjection c x) = D x :=
    fun x => hD.branchPieceIn_map_branchCoordinate c x.2
  refine ⟨b, hb0, ?_, ?_⟩
  · intro k hk u
    let a := s k (Bool.xor u (b k)) (q k)
    have haJ : (a : EuclideanSpace ℝ (Fin 2)) ∈ J := hpreJ ▸ a.2
    have hae := hb k hk u (hqmem k hk)
    refine ⟨a, haJ, (hss k _ _ (hqmem k hk).1).1, ?_, ?_⟩
    · rw [show a = s (k + 1) (Bool.xor u (b (k + 1))) (q k) from hae]
      exact (hss (k + 1) _ _ (hqmem k hk).2).1
    · rw [← hpD a, (hss k _ _ (hqmem k hk).1).2]
      exact hq k hk
  · intro u
    let a := s m (Bool.xor u (b m)) z'
    have haJ : (a : EuclideanSpace ℝ (Fin 2)) ∈ J := hpreJ ▸ a.2
    refine ⟨a, haJ, (hss m _ _ hcz.2).1, ?_, ?_⟩
    · rw [show a = s 0 (Bool.xor (!u) (b 0)) z' from hbc u]
      exact (hss 0 _ _ hcz.1).1
    · rw [← hpD a, (hss m _ _ hcz.2).2]
      exact hz'

end DifferentialGeometry.Topology.PiecewiseLinear.NormalSingularCellData
