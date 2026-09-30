/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.Topology.PiecewiseLinear.Section34FaceBallVocabulary

open Set Topology

namespace DifferentialGeometry.Topology.PiecewiseLinear

universe u

variable {Ea : Type} [NormedAddCommGroup Ea] [NormedSpace ℝ Ea]
  {M₁ M₂ : Type u} [TopologicalSpace M₁] [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M₁]
  [MetricSpace M₂] [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M₂]
  {U : Set M₁} {𝒦 𝒦' : LocallyFinitePLPieceIn Ea 3 M₁ U}
  {tgtV tgtVBd : Section34VertexIndex 𝒦 𝒦' → Set M₂}
  {tgtE tgtEBd : Section34EdgeIndex 𝒦 𝒦' → Set M₂}
  {fbl fblBd : Section34SimplexIndex 𝒦 3 → Set M₂}

theorem section34_trace_of_intrinsic_operation_dichotomies
    (hcircles : ∀ s : Section34SimplexIndex 𝒦 3, ∃ (r : ℕ) (J : Fin r → Set M₂),
      0 < r ∧ (∀ i, IsPolyhedralSphere (n := 3) 1 (J i)) ∧
      Pairwise (fun i j => Disjoint (J i) (J j)) ∧
      fblBd s ∩ frontier (⋃ w, tgtV w) = ⋃ i, J i ∧
      fblBd s ∩ frontier (section34FaceTorus tgtV s) = ⋃ i, J i)
    (hmeet : ∀ (s : Section34SimplexIndex 𝒦 3) (J : Set M₂),
      IsPolyhedralSphere (n := 3) 1 J → J ⊆ fblBd s ∩ frontier (⋃ w, tgtV w) →
      ∀ e : Section34EdgeIndex 𝒦 𝒦', Section34Incident e.1 s.1 →
        (J ∩ tgtEBd e).Nonempty ∨ ∃ t,
          Section34Compression 𝒦 𝒦' tgtVBd tgtE fbl fblBd t ∨
          Section34BigonSlide 𝒦 𝒦' tgtV tgtVBd tgtE tgtEBd fblBd t)
    (hexcess : ∀ (s : Section34SimplexIndex 𝒦 3) (J : Set M₂),
      IsPolyhedralSphere (n := 3) 1 J → J ⊆ fblBd s ∩ frontier (⋃ w, tgtV w) →
      ∀ e : Section34EdgeIndex 𝒦 𝒦', Section34Incident e.1 s.1 →
        (J ∩ tgtEBd e).Nontrivial → ∃ t,
          Section34Compression 𝒦 𝒦' tgtVBd tgtE fbl fblBd t ∨
          Section34BigonSlide 𝒦 𝒦' tgtV tgtVBd tgtE tgtEBd fblBd t)
    (hnc : ∀ s, ¬ Section34Compression 𝒦 𝒦' tgtVBd tgtE fbl fblBd s)
    (hnb : ∀ s, ¬ Section34BigonSlide 𝒦 𝒦' tgtV tgtVBd tgtE tgtEBd fblBd s) :
    Section34Trace 𝒦 𝒦' tgtV tgtEBd fblBd := by
  classical
  choose r F hr hF hdis hFN hFT using hcircles
  let J := fun s (i : ℕ) => if hi : i < r s then F s ⟨i, hi⟩ else ∅
  have hJi (s) (i : ℕ) (hi : i < r s) : J s i = F s ⟨i, hi⟩ := dite_eq_left hi
  have hU (s) : (⋃ i < r s, J s i) = ⋃ i : Fin (r s), F s i := by
    ext x
    simp only [mem_iUnion]
    constructor
    · rintro ⟨i, hi, hx⟩
      exact ⟨⟨i, hi⟩, by rwa [hJi s i hi] at hx⟩
    · rintro ⟨i, hx⟩
      exact ⟨i, i.isLt, by rwa [hJi s i i.isLt]⟩
  have hsub (s) (i : Fin (r s)) : F s i ⊆ fblBd s ∩ frontier (⋃ w, tgtV w) := by
    intro x hx
    exact (hFN s).symm.subset (mem_iUnion.mpr ⟨i, hx⟩)
  have hop (t) : ¬ (Section34Compression 𝒦 𝒦' tgtVBd tgtE fbl fblBd t ∨
      Section34BigonSlide 𝒦 𝒦' tgtV tgtVBd tgtE tgtEBd fblBd t) :=
    fun h => h.elim (hnc t) (hnb t)
  refine ⟨r, J, hr, ?_, ?_, ?_, ?_, ?_⟩
  · intro s i hi
    rw [hJi s i hi]
    exact hF s ⟨i, hi⟩
  · intro s i hi j hj hij
    rw [hJi s i hi, hJi s j hj]
    exact hdis s (fun h => hij (congrArg Fin.val h))
  · exact fun s => (hFN s).trans (hU s).symm
  · exact fun s => (hFT s).trans (hU s).symm
  · intro s i hi e he
    rw [hJi s i hi]
    have hnon : (F s ⟨i, hi⟩ ∩ tgtEBd e).Nonempty := by
      rcases hmeet s (F s ⟨i, hi⟩) (hF s ⟨i, hi⟩) (hsub s ⟨i, hi⟩) e he with h | ⟨t, h⟩
      · exact h
      · exact (hop t h).elim
    obtain ⟨p, hp⟩ := hnon
    refine ⟨p, Subset.antisymm ?_ (singleton_subset_iff.mpr hp)⟩
    intro x hx
    apply mem_singleton_iff.mpr
    by_contra hxp
    obtain ⟨t, ht⟩ := hexcess s (F s ⟨i, hi⟩) (hF s ⟨i, hi⟩) (hsub s ⟨i, hi⟩)
      e he ⟨x, hx, p, hp, hxp⟩
    exact hop t ht

end DifferentialGeometry.Topology.PiecewiseLinear
