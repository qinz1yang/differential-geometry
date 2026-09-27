/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.Topology.PiecewiseLinear.SeparatingSurfaceSplit

open Set Topology

namespace DifferentialGeometry.Topology.PiecewiseLinear

local notation "E3" => EuclideanSpace ℝ (Fin 3)

theorem IsCombinatorialManifoldWithBoundary.exists_separating_nullTraceCount_eq_zero
    [d : DecidableEq E3] (X : Geometry.SimplicialComplex ℝ E3) [Finite X.faces]
    (hX : IsCombinatorialManifoldWithBoundary 2 X) (hXo : IsOrientable 2 X)
    {I H K R T O F : Set E3} (htrace : HasFiniteCollaredTrace X.space T)
    (hT : IsPLTorus T) (h303 : Moise303) (hI : IsOpen I) (hIc : IsConnected I)
    (hHI : H ⊆ I) (hKI : K ⊆ I) (hHK : Disjoint H K)
    (hH : IsClosed (((↑) : I → E3) ⁻¹' H)) (hK : IsClosed (((↑) : I → E3) ⁻¹' K))
    (hCI : R ∪ (T ∪ X.space) ⊆ I) (hC : IsSeparatorIn I (R ∪ (T ∪ X.space)) H K)
    (hO : IsOpen O) (hTO : T ⊆ O) (hOI : O ⊆ I) (hOHK : Disjoint O (H ∪ K))
    (hRO : Disjoint R O) (hFO : Disjoint F O)
    (hboundary : (boundaryComplex 2 X).space ∩ O ⊆ T) :
    ∃ (Q : Geometry.SimplicialComplex ℝ E3) (hQfin : Q.faces.Finite) (m : ℕ),
      letI := hQfin.to_subtype
      IsCombinatorialManifoldWithBoundary 2 Q ∧ IsOrientable 2 Q ∧
      HasFiniteCollaredTrace Q.space T ∧ IsSeparatorIn I (R ∪ (T ∪ Q.space)) H K ∧
      R ∪ (T ∪ Q.space) ⊆ I ∧
      IsProtectedReplacement (R ∪ (T ∪ X.space)) (R ∪ (T ∪ Q.space)) F O ∧
      Q.space \ O = X.space \ O ∧ traceCircles Q.space T ⊆ traceCircles X.space T ∧
      nullTraceCount Q.space T = 0 ∧ (boundaryComplex 2 Q).space ∩ O ⊆ T ∧
      (boundaryComplex 2 Q).space ⊆ (boundaryComplex 2 X).space ∧
      (boundaryComplex 2 Q).space \ O = (boundaryComplex 2 X).space \ O ∧
      m ≤ nullTraceCount X.space T ∧ eulerChar Q = eulerChar X + m := by
  have hd : d = fun a b => Classical.propDecidable (a = b) := Subsingleton.elim _ _
  subst d
  let _ : DecidableEq E3 := fun a b => Classical.propDecidable (a = b)
  generalize hn : nullTraceCount X.space T = n
  induction n using Nat.strong_induction_on generalizing X with
  | h n ih =>
    by_cases hzero : n = 0
    · exact ⟨X, Set.toFinite X.faces, 0, hX, hXo, htrace, hC, hCI, ⟨rfl, rfl⟩,
        rfl, subset_rfl, hn.trans hzero, hboundary, subset_rfl, rfl, Nat.zero_le _, by simp⟩
    have hnull : ∃ G ∈ traceCircles X.space T, boundsDiskIn G T := by
      by_contra hnone
      have hall : ∀ G ∈ traceCircles X.space T, ¬ boundsDiskIn G T := by
        intro G hG hbound
        exact hnone ⟨G, hG, hbound⟩
      exact hzero (hn.symm.trans ((nullTraceCount_eq_zero_iff htrace.finiteTrace).mpr hall))
    obtain ⟨X₁, hX₁fin, hX₁, hX₁o, htrace₁, hC₁, hCI₁, hprot₁, hout₁, hseams₁,
        hdrop, hboundary₁, hBsub₁, hχ₁, G, hG, hBG⟩ :=
      hX.exists_separating_split_reducing_nullTraceCount X hXo htrace hT h303 hI hIc
        hHI hKI hHK hH hK hCI hC hO hTO hOI hOHK hRO hFO hboundary hnull
    let _ : Finite X₁.faces := hX₁fin.to_subtype
    have hBout₁ : (boundaryComplex 2 X₁).space \ O = (boundaryComplex 2 X).space \ O := by
      rw [hBG]
      ext x
      have hGO : x ∈ G → x ∈ O := fun hx => hTO (traceCircles_subset hG hx).2
      simp only [mem_sdiff]
      tauto
    obtain ⟨X₂, hX₂fin, m, hX₂, hX₂o, htrace₂, hC₂, hCI₂, hprot₂, hout₂,
        hseams₂, hzero₂, hboundary₂, hBsub₂, hBout₂, hm, hχ₂⟩ :=
      ih (nullTraceCount X₁.space T) (hn ▸ hdrop) X₁ hX₁ hX₁o htrace₁ hCI₁ hC₁ hboundary₁ rfl
    let _ : Finite X₂.faces := hX₂fin.to_subtype
    refine ⟨X₂, hX₂fin, m + 1, hX₂, hX₂o, htrace₂, hC₂, hCI₂,
      ⟨hprot₂.1.trans hprot₁.1, hprot₂.2.trans hprot₁.2⟩, hout₂.trans hout₁,
      hseams₂.trans hseams₁, hzero₂, hboundary₂, hBsub₂.trans hBsub₁,
      hBout₂.trans hBout₁, ?_, ?_⟩
    · omega
    · simp only [Nat.cast_add, Nat.cast_one]
      omega

end DifferentialGeometry.Topology.PiecewiseLinear
