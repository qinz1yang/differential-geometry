/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.Topology.PiecewiseLinear.CanonicalReturningWindowReduction

open Set

namespace DifferentialGeometry.Topology.PiecewiseLinear

local notation "E3" => EuclideanSpace ℝ (Fin 3)

variable [DecidableEq E3] {X Y : ℤ → Geometry.SimplicialComplex ℝ E3} {i : ℤ}

theorem IsCanonicalClosedDeletion.exists_component_of_boundary_nonempty
    (hd : IsCanonicalClosedDeletion i X Y) (j : ℤ) (c : ConnectedComponents (X j).space)
    (hc : (boundaryComplex 2 (connectedComponentComplex (X j) c)).space ≠ ∅) :
    ∃ d : ConnectedComponents (Y j).space,
      (connectedComponentComplex (Y j) d).space = (connectedComponentComplex (X j) c).space := by
  by_cases hji : j = i
  · subst j
    obtain ⟨c₀, hc₀, -, e, he⟩ := hd.removed
    have hne : c ≠ c₀ := fun h => hc (h.symm ▸ hc₀)
    exact ⟨e ⟨c, hne⟩, he ⟨c, hne⟩⟩
  · rw [hd.unchanged j hji]
    exact ⟨c, rfl⟩

variable {S' T'' : ℤ → Set E3} {I : Set E3} {P' a b : E3}

private theorem seam_subset_component_boundary
    (hX : IsCanonicalSurface X S' T'' I P' a b) (j : ℤ)
    (c : ConnectedComponents (X j).space) {G : Set E3} (k : ℤ)
    (hk : k = j ∨ k = j + 1)
    (hG : G ∈ traceCircles (connectedComponentComplex (X j) c).space (T'' (2 * k))) :
    G ⊆ (boundaryComplex 2 (connectedComponentComplex (X j) c)).space := by
  intro x hx
  have hxG := traceCircles_subset hG hx
  apply (boundaryComplex_space_connectedComponentComplex 2 (X j) c).symm.subset
  refine ⟨(hX.boundary j).symm.subset ⟨?_, ?_⟩, hxG.1⟩
  · exact (iUnion_connectedComponentComplex_space (X j)).subset (mem_iUnion.mpr ⟨c, hxG.1⟩)
  · rcases hk with rfl | rfl
    · exact Or.inl hxG.2
    · exact Or.inr hxG.2

theorem IsCanonicalClosedWindowReduction.exists_component_containing_opposite_seams
    {rows : Finset ℤ} {F : Set E3}
    (hred : IsCanonicalClosedWindowReduction X Y S' T'' I P' a b rows F)
    (j : ℤ) {G₀ G₁ : Set E3}
    (hstart : ∃ c : ConnectedComponents (X j).space,
      G₀ ∈ traceCircles (connectedComponentComplex (X j) c).space (T'' (2 * j)) ∧
      G₁ ∈ traceCircles (connectedComponentComplex (X j) c).space (T'' (2 * (j + 1)))) :
    ∃ d : ConnectedComponents (Y j).space,
      G₀ ∈ traceCircles (connectedComponentComplex (Y j) d).space (T'' (2 * j)) ∧
      G₁ ∈ traceCircles (connectedComponentComplex (Y j) d).space (T'' (2 * (j + 1))) := by
  have hpath := hred.steps
  clear hred
  induction hpath with
  | refl => exact hstart
  | tail hpath hlast ih =>
    obtain ⟨hU, -, k, -, _, -, hd, -⟩ := hlast
    obtain ⟨c, h₀, h₁⟩ := ih
    have hbd :=
      ((traceCircles_isPLSphere h₀).nonempty.mono
        (seam_subset_component_boundary hU j c j (Or.inl rfl) h₀)).ne_empty
    obtain ⟨d, hspace⟩ := hd.exists_component_of_boundary_nonempty j c hbd
    exact ⟨d, by simpa only [hspace] using h₀, by simpa only [hspace] using h₁⟩

variable {φ : E3 → E3} {Pt : ℤ → E3} {Dp Dpint J A S T S'' : ℤ → Set E3}
  {Dimg Dbdimg W : Set E3}

theorem IsCanonicalSurface.not_returning_component_of_opposite_seams
    (hX : IsCanonicalSurface X (fun j => φ '' S j) T'' I P' a b)
    (htw : IsCanonicalTower φ Pt Dp Dpint J A S T S'' T'' Dimg Dbdimg W I P')
    (j : ℤ) (c : ConnectedComponents (X j).space) {G₀ G₁ : Set E3}
    (h₀ : G₀ ∈ traceCircles (connectedComponentComplex (X j) c).space (T'' (2 * j)))
    (h₁ : G₁ ∈ traceCircles (connectedComponentComplex (X j) c).space (T'' (2 * (j + 1)))) :
    ¬ IsCanonicalReturningComponent X T'' j c := by
  let _ : Finite (X j).faces := (hX.finiteFaces j).to_subtype
  let _ : Finite (connectedComponentComplex (X j) c).faces :=
    (connectedComponentComplex_faces_finite (X j) c).to_subtype
  rintro ⟨k, J₀, J₁, hk, hC, -, hJ₀, hJ₁, -, -⟩
  have hbd : (boundaryComplex 2 (connectedComponentComplex (X j) c)).space ⊆ T'' (2 * k) := by
    rw [hC.boundaryComplex_space _]
    exact union_subset ((traceCircles_subset hJ₀).trans inter_subset_right)
      ((traceCircles_subset hJ₁).trans inter_subset_right)
  have hdis : Disjoint (T'' (2 * j)) (T'' (2 * (j + 1))) :=
    (htw.apart (2 * j) (2 * (j + 1)) (by rw [le_abs]; omega)).mono
      (htw.boundary_subset_outer _) (htw.boundary_subset_outer _)
  rcases hk with hk | hk
  · subst k
    obtain ⟨x, hx⟩ := (traceCircles_isPLSphere h₁).nonempty
    exact disjoint_left.mp hdis
      (hbd (seam_subset_component_boundary hX j c (j + 1) (Or.inr rfl) h₁ hx))
      (traceCircles_subset h₁ hx).2
  · subst k
    obtain ⟨x, hx⟩ := (traceCircles_isPLSphere h₀).nonempty
    exact disjoint_left.mp hdis (traceCircles_subset h₀ hx).2
      (hbd (seam_subset_component_boundary hX j c j (Or.inl rfl) h₀ hx))

theorem IsCanonicalReturningWindowReduction.exists_component_containing_opposite_seams
    {rows : Finset ℤ} {F : Set E3}
    (hred : IsCanonicalReturningWindowReduction X Y (fun j => φ '' S j) S'' T'' I P' a b rows F)
    (htw : IsCanonicalTower φ Pt Dp Dpint J A S T S'' T'' Dimg Dbdimg W I P')
    (j : ℤ) {G₀ G₁ : Set E3}
    (hstart : ∃ c : ConnectedComponents (X j).space,
      G₀ ∈ traceCircles (connectedComponentComplex (X j) c).space (T'' (2 * j)) ∧
      G₁ ∈ traceCircles (connectedComponentComplex (X j) c).space (T'' (2 * (j + 1)))) :
    ∃ d : ConnectedComponents (Y j).space,
      G₀ ∈ traceCircles (connectedComponentComplex (Y j) d).space (T'' (2 * j)) ∧
      G₁ ∈ traceCircles (connectedComponentComplex (Y j) d).space (T'' (2 * (j + 1))) := by
  have hpath := hred.steps
  clear hred
  induction hpath with
  | refl => exact hstart
  | tail hpath hlast ih =>
    obtain ⟨hU, -, k, -, c₀, hreturn, hd, -⟩ := hlast
    obtain ⟨c, h₀, h₁⟩ := ih
    by_cases hjk : j = k
    · subst k
      have hne : c ≠ c₀ := by
        intro hc
        exact hU.surface.not_returning_component_of_opposite_seams htw j c h₀ h₁
          (hc.symm ▸ hreturn)
      obtain ⟨e, he⟩ := hd.retained
      refine ⟨e ⟨c, hne⟩, ?_, ?_⟩
      · simpa only [he ⟨c, hne⟩] using h₀
      · simpa only [he ⟨c, hne⟩] using h₁
    · rw [hd.unchanged j hjk]
      exact ⟨c, h₀, h₁⟩

end DifferentialGeometry.Topology.PiecewiseLinear
