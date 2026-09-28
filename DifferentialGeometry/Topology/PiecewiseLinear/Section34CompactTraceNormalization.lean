/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.Topology.PiecewiseLinear.Section34CompactExcessCrossings
import DifferentialGeometry.Topology.PiecewiseLinear.Section34CompactTraceMeetsMeridians

open Set Topology

namespace DifferentialGeometry.Topology.PiecewiseLinear

universe v

section Leaves

variable {C V : Set (EuclideanSpace ℝ (Fin 3))}
  {h f₁ : EuclideanSpace ℝ (Fin 3) → EuclideanSpace ℝ (Fin 3)} {ε : ℝ}
  {K K' : Geometry.SimplicialComplex ℝ (EuclideanSpace ℝ (Fin 3))}
  {src srcBd : Section34CompactLabelOf K K' → Set (EuclideanSpace ℝ (Fin 3))}
  {H : Finset (EuclideanSpace ℝ (Fin 3)) → Set (EuclideanSpace ℝ (Fin 3))}
  {env : Section34CompactSimplexIndex K 3 → Set (EuclideanSpace ℝ (Fin 3))}

theorem compactTrace_of_noOperation (hcut : Section34CompactCutFrame C K K' src srcBd)
    (hgraph : Section34CompactGraphFrame V h ε K K' src H f₁)
    {fbl fblBd : Section34CompactSimplexIndex K 3 → Set (EuclideanSpace ℝ (Fin 3))}
    (hinv : Section34CompactFaceBallInvariants K K' h H
      (section34CompactVertexBallImage src f₁) (section34CompactSplitDiskImage srcBd f₁)
      fbl fblBd)
    (hnc : ∀ s, ¬ Section34CompactCompression K K' (section34CompactVertexBallImage srcBd f₁)
      (section34CompactSplitDiskImage src f₁) fbl fblBd s)
    (hnb : ∀ s, ¬ Section34CompactBigonSlide K K' (section34CompactVertexBallImage src f₁)
      (section34CompactVertexBallImage srcBd f₁) (section34CompactSplitDiskImage src f₁)
      (section34CompactSplitDiskImage srcBd f₁) fblBd s) :
    Section34CompactTrace K K' (section34CompactVertexBallImage src f₁)
      (section34CompactSplitDiskImage srcBd f₁) fblBd := by
  classical
  choose r F hr hF hdis hFN hFΘ hcarry hsurj using
    fun s => exists_positive_finite_compact_trace_circles hcut hgraph hinv s
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
  have hFT (s) (i : Fin (r s)) : F s i ⊆
      fblBd s ∩ frontier (⋃ w, section34CompactVertexBallImage src f₁ w) := by
    intro x hx
    exact (hFN s).symm.subset (mem_iUnion.mpr ⟨i, hx⟩)
  refine ⟨r, J, hr, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro s i hi
    rw [hJi s i hi]
    exact hF s ⟨i, hi⟩
  · intro s i hi j hj hij
    rw [hJi s i hi, hJi s j hj]
    exact hdis s (fun h => hij (congrArg Fin.val h))
  · intro s
    exact (hFN s).trans (hU s).symm
  · intro s
    exact (hFΘ s).trans (hU s).symm
  · intro s i hi e he
    rw [hJi s i hi]
    obtain ⟨p, hp⟩ := hinv.trace_circle_inter_splitDiskBoundary_nonempty
      hcut hgraph hnc hnb s (hF s ⟨i, hi⟩) (hFT s ⟨i, hi⟩) e he
    refine ⟨p, Subset.antisymm ?_ (singleton_subset_iff.mpr hp)⟩
    intro x hx
    apply mem_singleton_iff.mpr
    by_contra hxp
    have hmore : (F s ⟨i, hi⟩ ∩ section34CompactSplitDiskImage srcBd f₁ e).Nontrivial :=
      ⟨x, hx, p, hp, hxp⟩
    obtain ⟨t, ht⟩ := exists_admissible_bigon_of_excess_meridian_crossings
      hinv hcut hgraph hnc hnb s (hF s ⟨i, hi⟩) (hFT s ⟨i, hi⟩) ⟨e, he, hmore⟩
    exact hnb t ht
  · intro s i hi hsub
    exact hinv.trace_circle_homologyMap_ne_zero_of_no_operation
      hcut hgraph hnc hnb s (by rw [hJi s i hi]; exact hF s ⟨i, hi⟩)
      (by rw [hJi s i hi]; exact hFT s ⟨i, hi⟩) hsub

end Leaves

end DifferentialGeometry.Topology.PiecewiseLinear
