/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.Topology.PiecewiseLinear.CircleCappingMarkedComponents
import DifferentialGeometry.Topology.PiecewiseLinear.CollaredTraceCircleMembership
import DifferentialGeometry.Topology.PiecewiseLinear.CanonicalComponentSeamDisks

open Set

namespace DifferentialGeometry.Topology.PiecewiseLinear

local notation "E3" => EuclideanSpace ℝ (Fin 3)

private theorem capping_preserves_component_circles
    (K Q : Geometry.SimplicialComplex ℝ E3) [Finite K.faces] [Finite Q.faces]
    {T₀ T₁ G₀ G₁ : Set E3} (htrace : HasFiniteCollaredTrace K.space T₀)
    (hdis : Disjoint T₀ T₁)
    (hcap : IsCircleCapping K.space Q.space T₀ (K.space ∩ (T₀ ∪ T₁)))
    (c : ConnectedComponents K.space)
    (h₀ : G₀ ∈ traceCircles (connectedComponentComplex K c).space T₀)
    (h₁ : G₁ ∈ traceCircles (connectedComponentComplex K c).space T₁)
    (hess : ¬ boundsDiskIn G₀ T₀) :
    ∃ d : ConnectedComponents Q.space, G₀ ∪ G₁ ⊆ (connectedComponentComplex Q d).space := by
  have hCK : (connectedComponentComplex K c).space ⊆ K.space :=
    (subset_iUnion (fun d => (connectedComponentComplex K d).space) c).trans
      (iUnion_connectedComponentComplex_space K).subset
  have h₀K : G₀ ∈ traceCircles K.space T₀ :=
    traceCircles_subset_of_inter_subset htrace.traceCover
      (fun _ hx => ⟨hCK hx.1, hx.2⟩) h₀
  obtain ⟨G, hG, hnull, e, he⟩ := hcap.exists_component_equiv_preserving_marks K Q
  have h₀G : Disjoint G₀ G := pairwiseDisjoint_traceCircles K.space T₀ h₀K hG
    (fun h => hess (h.symm ▸ hnull))
  have h₁G : Disjoint G₁ G := hdis.symm.mono
    ((traceCircles_subset h₁).trans inter_subset_right)
    ((traceCircles_subset hG).trans inter_subset_right)
  refine ⟨e c, fun x hx => he c ?_⟩
  rcases hx with hx | hx
  · have hx₀ := traceCircles_subset h₀ hx
    exact ⟨⟨⟨hCK hx₀.1, Or.inl hx₀.2⟩, disjoint_left.mp h₀G hx⟩, hx₀.1⟩
  · have hx₁ := traceCircles_subset h₁ hx
    exact ⟨⟨⟨hCK hx₁.1, Or.inr hx₁.2⟩, disjoint_left.mp h₁G hx⟩, hx₁.1⟩

private theorem homeomorph_preserves_component_circles
    (K Q : Geometry.SimplicialComplex ℝ E3) [Finite K.faces]
    {T₀ T₁ G₀ G₁ : Set E3} {f : E3 → E3}
    (hf : IsPLHomeomorphOn f K.space Q.space)
    (hfix : EqOn f id (K.space ∩ (T₀ ∪ T₁))) (c : ConnectedComponents K.space)
    (h₀ : G₀ ∈ traceCircles (connectedComponentComplex K c).space T₀)
    (h₁ : G₁ ∈ traceCircles (connectedComponentComplex K c).space T₁) :
    ∃ d : ConnectedComponents Q.space, G₀ ∪ G₁ ⊆ (connectedComponentComplex Q d).space := by
  have hCK : (connectedComponentComplex K c).space ⊆ K.space :=
    (subset_iUnion (fun d => (connectedComponentComplex K d).space) c).trans
      (iUnion_connectedComponentComplex_space K).subset
  obtain ⟨e, he⟩ := hf.exists_component_equiv_preserving_marks K Q hfix
  refine ⟨e c, fun x hx => he c ?_⟩
  rcases hx with hx | hx
  · have hx₀ := traceCircles_subset h₀ hx
    exact ⟨⟨hCK hx₀.1, Or.inl hx₀.2⟩, hx₀.1⟩
  · have hx₁ := traceCircles_subset h₁ hx
    exact ⟨⟨hCK hx₁.1, Or.inr hx₁.2⟩, hx₁.1⟩

variable [DecidableEq E3] {φ : E3 → E3} {Pt : ℤ → E3}
  {Dp Dpint J A S T S'' T'' : ℤ → Set E3} {Dimg Dbdimg W I : Set E3} {P' a b : E3}

theorem IsCanonicalNullSplit.exists_component_containing_essential_seams
    (htw : IsCanonicalTower φ Pt Dp Dpint J A S T S'' T'' Dimg Dbdimg W I P')
    (h314 : Moise314) {X Y : ℤ → Geometry.SimplicialComplex ℝ E3} {i : ℤ}
    (hX : IsCanonicalSurface X (fun j => φ '' S j) T'' I P' a b)
    (hY : IsCanonicalSurface Y (fun j => φ '' S j) T'' I P' a b)
    (hstep : IsCanonicalNullSplit (fun j => φ '' S j) T'' i X Y)
    (j : ℤ) (c : ConnectedComponents (X j).space) {G₀ G₁ : Set E3}
    (h₀ : G₀ ∈ traceCircles (connectedComponentComplex (X j) c).space (T'' (2 * j)))
    (h₁ : G₁ ∈ traceCircles (connectedComponentComplex (X j) c).space (T'' (2 * (j + 1))))
    (hess₀ : ¬ boundsDiskIn G₀ (T'' (2 * j + 1)))
    (hess₁ : ¬ boundsDiskIn G₁ (T'' (2 * j + 1))) :
    ∃ d : ConnectedComponents (Y j).space,
      G₀ ∈ traceCircles (connectedComponentComplex (Y j) d).space (T'' (2 * j)) ∧
      G₁ ∈ traceCircles (connectedComponentComplex (Y j) d).space (T'' (2 * (j + 1))) := by
  classical
  let _ (k : ℤ) : Finite (X k).faces := (hX.finiteFaces k).to_subtype
  let _ (k : ℤ) : Finite (Y k).faces := (hY.finiteFaces k).to_subtype
  have hess₀' : ¬ boundsDiskIn G₀ (T'' (2 * j)) :=
    fun h => hess₀ ((hX.lower_component_boundsDiskIn_iff htw h314 j c h₀).mp h)
  have hess₁' : ¬ boundsDiskIn G₁ (T'' (2 * (j + 1))) :=
    fun h => hess₁ ((hX.upper_component_boundsDiskIn_iff htw h314 j c h₁).mp h)
  have hdis (k : ℤ) : Disjoint (T'' (2 * k)) (T'' (2 * (k + 1))) :=
    (htw.apart (2 * k) (2 * (k + 1)) (by rw [le_abs]; omega)).mono
      (htw.boundary_subset_outer _) (htw.boundary_subset_outer _)
  have hcontain : ∃ d : ConnectedComponents (Y j).space,
      G₀ ∪ G₁ ⊆ (connectedComponentComplex (Y j) d).space := by
    by_cases hj : j = i - 1
    · subst j
      have h₁' : G₁ ∈ traceCircles (connectedComponentComplex (X (i - 1)) c).space
          (T'' (2 * i)) := by simpa only [sub_add_cancel] using h₁
      have hess₁'' : ¬ boundsDiskIn G₁ (T'' (2 * i)) := by
        simpa only [sub_add_cancel] using hess₁'
      have hdis' : Disjoint (T'' (2 * i)) (T'' (2 * (i - 1))) := by
        simpa only [sub_add_cancel] using (hdis (i - 1)).symm
      rcases hstep.capping with ⟨hcap, -, -, -⟩ | ⟨⟨f, hf, hfix⟩, -⟩
      · obtain ⟨d, hd⟩ := capping_preserves_component_circles (X (i - 1)) (Y (i - 1))
          (by simpa only [sub_add_cancel] using hX.upperTrace (i - 1)) hdis'
          (by simpa only [union_comm] using hcap) c h₁' h₀ hess₁''
        exact ⟨d, by simpa only [union_comm] using hd⟩
      · exact homeomorph_preserves_component_circles (X (i - 1)) (Y (i - 1))
          hf hfix c h₀ h₁'
    · by_cases hji : j = i
      · subst j
        rcases hstep.capping with ⟨-, f, hf, hfix⟩ | ⟨-, hcap⟩
        · exact homeomorph_preserves_component_circles (X i) (Y i) hf hfix c h₀ h₁
        · exact capping_preserves_component_circles (X i) (Y i) (hX.lowerTrace i)
            (hdis i) hcap c h₀ h₁ hess₀'
      · rw [hstep.unchanged j hj hji]
        exact ⟨c, union_subset ((traceCircles_subset h₀).trans inter_subset_left)
          ((traceCircles_subset h₁).trans inter_subset_left)⟩
  obtain ⟨d, hd⟩ := hcontain
  refine ⟨d, ?_, ?_⟩
  · apply ((hY.lowerTrace j).of_connected_component (Y j) d).mem_traceCircles_of_isPLSphere
      (traceCircles_isPLSphere h₀)
    exact fun x hx => ⟨hd (Or.inl hx), (traceCircles_subset h₀ hx).2⟩
  · apply ((hY.upperTrace j).of_connected_component (Y j) d).mem_traceCircles_of_isPLSphere
      (traceCircles_isPLSphere h₁)
    exact fun x hx => ⟨hd (Or.inr hx), (traceCircles_subset h₁ hx).2⟩

theorem IsCanonicalTower.exists_component_containing_essential_seams_of_null_splits
    (htw : IsCanonicalTower φ Pt Dp Dpint J A S T S'' T'' Dimg Dbdimg W I P')
    (h314 : Moise314) {X Y : ℤ → Geometry.SimplicialComplex ℝ E3} (window : Finset ℤ)
    (hpath : Relation.ReflTransGen (fun U V =>
      IsCanonicalSurface U (fun j => φ '' S j) T'' I P' a b ∧
      IsCanonicalSurface V (fun j => φ '' S j) T'' I P' a b ∧
      ∃ i ∈ window, IsCanonicalNullSplit (fun j => φ '' S j) T'' i U V) X Y)
    (j : ℤ) {G₀ G₁ : Set E3}
    (hstart : ∃ c : ConnectedComponents (X j).space,
      G₀ ∈ traceCircles (connectedComponentComplex (X j) c).space (T'' (2 * j)) ∧
      G₁ ∈ traceCircles (connectedComponentComplex (X j) c).space (T'' (2 * (j + 1))))
    (hess₀ : ¬ boundsDiskIn G₀ (T'' (2 * j + 1)))
    (hess₁ : ¬ boundsDiskIn G₁ (T'' (2 * j + 1))) :
    ∃ d : ConnectedComponents (Y j).space,
      G₀ ∈ traceCircles (connectedComponentComplex (Y j) d).space (T'' (2 * j)) ∧
      G₁ ∈ traceCircles (connectedComponentComplex (Y j) d).space (T'' (2 * (j + 1))) := by
  induction hpath with
  | refl => exact hstart
  | tail hpath hlast ih =>
    obtain ⟨hU, hV, i, -, hstep⟩ := hlast
    obtain ⟨c, h₀, h₁⟩ := ih
    exact hstep.exists_component_containing_essential_seams htw h314 hU hV j c
      h₀ h₁ hess₀ hess₁

end DifferentialGeometry.Topology.PiecewiseLinear
