/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.Topology.PiecewiseLinear.CollaredTraceSplit

open Set Topology

namespace DifferentialGeometry.Topology.PiecewiseLinear

local notation "E3" => EuclideanSpace ℝ (Fin 3)

theorem HasFiniteCollaredTrace.exists_nullTraceCount_eq_zero
    {I H K R T L O F : Set E3} (h : HasFiniteCollaredTrace L T) (hT : IsPLTorus T)
    (h303 : Moise303) (hI : IsOpen I) (hIc : IsConnected I)
    (hHI : H ⊆ I) (hKI : K ⊆ I) (hHK : Disjoint H K)
    (hH : IsClosed (((↑) : I → E3) ⁻¹' H)) (hK : IsClosed (((↑) : I → E3) ⁻¹' K))
    (hCI : R ∪ (T ∪ L) ⊆ I) (hC : IsSeparatorIn I (R ∪ (T ∪ L)) H K)
    (hO : IsOpen O) (hTO : T ⊆ O) (hOI : O ⊆ I) (hOHK : Disjoint O (H ∪ K))
    (hRO : Disjoint R O) (hFO : Disjoint F O) :
    ∃ L' : Set E3, HasFiniteCollaredTrace L' T ∧
      IsSeparatorIn I (R ∪ (T ∪ L')) H K ∧ R ∪ (T ∪ L') ⊆ I ∧
      IsProtectedReplacement (R ∪ (T ∪ L)) (R ∪ (T ∪ L')) F O ∧
      L' \ O = L \ O ∧ traceCircles L' T ⊆ traceCircles L T ∧
      nullTraceCount L' T = 0 := by
  generalize hn : nullTraceCount L T = n
  induction n using Nat.strong_induction_on generalizing L with
  | h n ih =>
    by_cases hzero : n = 0
    · exact ⟨L, h, hC, hCI, ⟨rfl, rfl⟩, rfl, subset_rfl, hn.trans hzero⟩
    have hnull : ∃ G ∈ traceCircles L T, boundsDiskIn G T := by
      by_contra hnone
      have hall : ∀ G ∈ traceCircles L T, ¬ boundsDiskIn G T := by
        intro G hG hbound
        exact hnone ⟨G, hG, hbound⟩
      exact hzero (hn.symm.trans ((nullTraceCount_eq_zero_iff h.finiteTrace).mpr hall))
    obtain ⟨L₁, h₁, hC₁, hCI₁, hprot₁, hout₁, hsub₁, hdrop⟩ :=
      h.exists_split_reducing_nullTraceCount hT h303 hI hIc hHI hKI hHK hH hK hCI hC
        hO hTO hOI hOHK hRO hFO hnull
    obtain ⟨L₂, h₂, hC₂, hCI₂, hprot₂, hout₂, hsub₂, hzero₂⟩ :=
      ih (nullTraceCount L₁ T) (hn ▸ hdrop) h₁ hCI₁ hC₁ rfl
    exact ⟨L₂, h₂, hC₂, hCI₂, ⟨hprot₂.1.trans hprot₁.1, hprot₂.2.trans hprot₁.2⟩,
      hout₂.trans hout₁, hsub₂.trans hsub₁, hzero₂⟩

end DifferentialGeometry.Topology.PiecewiseLinear
