/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.Topology.PiecewiseLinear.CanonicalSurfaceTraceLocality
import DifferentialGeometry.Topology.PiecewiseLinear.SurfaceTraceMonotonicity

open Set Topology

namespace DifferentialGeometry.Topology.PiecewiseLinear

local notation "E3" => EuclideanSpace ℝ (Fin 3)

private theorem forall_replaceAdjacentSurfaces
    (X : ℤ → Geometry.SimplicialComplex ℝ E3) (i : ℤ)
    (Q₀ Q₁ : Geometry.SimplicialComplex ℝ E3)
    {p : ℤ → Geometry.SimplicialComplex ℝ E3 → Prop}
    (h₀ : p (i - 1) Q₀) (h₁ : p i Q₁)
    (hrest : ∀ j, j ≠ i - 1 → j ≠ i → p j (X j)) :
    ∀ j, p j (replaceAdjacentSurfaces X i Q₀ Q₁ j) := by
  intro j
  by_cases hj₀ : j = i - 1
  · subst j
    simpa only [replaceAdjacentSurfaces_left] using h₀
  · by_cases hj₁ : j = i
    · subst j
      simpa only [replaceAdjacentSurfaces_right] using h₁
    · simpa only [replaceAdjacentSurfaces_of_ne X i Q₀ Q₁ hj₀ hj₁] using hrest j hj₀ hj₁

variable {φ : E3 → E3} {Pt : ℤ → E3} {Dp Dpint J A S T S'' T'' : ℤ → Set E3}
  {Dimg Dbdimg W I : Set E3} {P' a b : E3}

theorem IsCanonicalSurface.of_adjacent_replacement [DecidableEq E3]
    {X : ℤ → Geometry.SimplicialComplex ℝ E3}
    (h : IsCanonicalSurface X (fun j => φ '' S j) T'' I P' a b)
    (htw : IsCanonicalTower φ Pt Dp Dpint J A S T S'' T'' Dimg Dbdimg W I P') (i : ℤ)
    (Q₀ Q₁ : Geometry.SimplicialComplex ℝ E3) [Finite Q₀.faces] [Finite Q₁.faces]
    (hQ₀ : IsCombinatorialManifoldWithBoundary 2 Q₀) (hQ₀o : IsOrientable 2 Q₀)
    (hQ₁ : IsCombinatorialManifoldWithBoundary 2 Q₁) (hQ₁o : IsOrientable 2 Q₁)
    (htrace₀ : HasFiniteCollaredTrace Q₀.space (T'' (2 * i)))
    (htrace₁ : HasFiniteCollaredTrace Q₁.space (T'' (2 * i)))
    (hdis : Disjoint Q₀.space Q₁.space) {G : Set E3} (hG : G ⊆ T'' (2 * i))
    (hout₀ : Q₀.space \ interior (φ '' S (2 * i)) =
      (X (i - 1)).space \ interior (φ '' S (2 * i)))
    (hout₁ : Q₁.space \ interior (φ '' S (2 * i)) =
      (X i).space \ interior (φ '' S (2 * i)))
    (hmeet₀ : Q₀.space ∩ T'' (2 * i) = ((X (i - 1)).space ∩ T'' (2 * i)) \ G)
    (hmeet₁ : Q₁.space ∩ T'' (2 * i) = ((X i).space ∩ T'' (2 * i)) \ G)
    (hb₀ : (boundaryComplex 2 Q₀).space = (boundaryComplex 2 (X (i - 1))).space \ G)
    (hb₁ : (boundaryComplex 2 Q₁).space = (boundaryComplex 2 (X i)).space \ G)
    (hCI : towerRemainder T'' (fun j => (X j).space) P' i ∪
      (T'' (2 * i) ∪ (Q₀.space ∪ Q₁.space)) ⊆ I)
    (hsep : IsSeparatorIn I (towerRemainder T'' (fun j => (X j).space) P' i ∪
      (T'' (2 * i) ∪ (Q₀.space ∪ Q₁.space))) {a} {b}) :
    IsCanonicalSurface (replaceAdjacentSurfaces X i Q₀ Q₁)
      (fun j => φ '' S j) T'' I P' a b := by
  classical
  let Y := replaceAdjacentSurfaces X i Q₀ Q₁
  have hbasic : ∀ j, ∃ hf : (Y j).faces.Finite,
      IsCombinatorialManifoldWithBoundary 2 (Y j) ∧
        letI := hf.to_subtype; IsOrientable 2 (Y j) :=
    forall_replaceAdjacentSurfaces X i Q₀ Q₁
      (p := fun _ Q => ∃ hf : Q.faces.Finite,
        IsCombinatorialManifoldWithBoundary 2 Q ∧ letI := hf.to_subtype; IsOrientable 2 Q)
      ⟨Set.toFinite _, hQ₀, hQ₀o⟩
      ⟨Set.toFinite _, hQ₁, hQ₁o⟩
      (fun j _ _ => ⟨h.finiteFaces j, h.manifold j, h.orientable j⟩)
  have hpoly (j : ℤ) : IsPolyhedron (Y j).space := by
    let _ : Finite (Y j).faces := (hbasic j).choose.to_subtype
    exact isPolyhedron_space (Y j)
  have hout : ∀ j, (Y j).space \ interior (φ '' S (2 * i)) =
      (X j).space \ interior (φ '' S (2 * i)) :=
    forall_replaceAdjacentSurfaces X i Q₀ Q₁
      (p := fun j Q => Q.space \ interior (φ '' S (2 * i)) =
        (X j).space \ interior (φ '' S (2 * i))) hout₀ hout₁ (fun _ _ _ => rfl)
  have hactive {j : ℤ} {x : E3} (hx : x ∈ (Y j).space)
      (hxO : x ∈ interior (φ '' S (2 * i))) : j = i - 1 ∨ j = i := by
    by_contra! hj
    have hxX : x ∈ (X j).space := by
      simpa only [Y, replaceAdjacentSurfaces_of_ne X i Q₀ Q₁ hj.1 hj.2] using hx
    exact disjoint_left.mp (h.remainder_disjoint_interior_outer htw i)
      (Or.inr (Or.inr (mem_iUnion₂.mpr ⟨j, hj, hxX⟩))) hxO
  have htraces (j k : ℤ) (hk : HasFiniteCollaredTrace (X j).space (T'' (2 * k))) :
      HasFiniteCollaredTrace (Y j).space (T'' (2 * k)) := by
    by_cases hki : k = i
    · subst k
      by_cases hj₀ : j = i - 1
      · subst j
        simpa only [Y, replaceAdjacentSurfaces_left] using htrace₀
      · by_cases hj₁ : j = i
        · subst j
          simpa only [Y, replaceAdjacentSurfaces_right] using htrace₁
        · simpa only [Y, replaceAdjacentSurfaces_of_ne X i Q₀ Q₁ hj₀ hj₁] using hk
    · exact htw.hasFiniteCollaredTrace_of_sdiff_eq hki hk (hpoly j) (hout j)
  have hmeets : ∀ j k, (Y j).space ∩ T'' (2 * k) ⊆ (X j).space ∩ T'' (2 * k) :=
    forall_replaceAdjacentSurfaces X i Q₀ Q₁
      (p := fun j Q => ∀ k, Q.space ∩ T'' (2 * k) ⊆ (X j).space ∩ T'' (2 * k))
      (fun k => (htw.inter_even_eq_sdiff_of_local_replacement hG hout₀ hmeet₀ k).subset.trans
        sdiff_subset)
      (fun k => (htw.inter_even_eq_sdiff_of_local_replacement hG hout₁ hmeet₁ k).subset.trans
        sdiff_subset) (fun _ _ _ _ => Subset.rfl)
  have hboundary (j : ℤ) (Q : Geometry.SimplicialComplex ℝ E3)
      (hQo : Q.space \ interior (φ '' S (2 * i)) =
        (X j).space \ interior (φ '' S (2 * i)))
      (hQm : Q.space ∩ T'' (2 * i) = ((X j).space ∩ T'' (2 * i)) \ G)
      (hQb : (boundaryComplex 2 Q).space = (boundaryComplex 2 (X j)).space \ G) :
      (boundaryComplex 2 Q).space = Q.space ∩ (T'' (2 * j) ∪ T'' (2 * (j + 1))) := by
    rw [hQb, h.boundary j, inter_union_distrib_left, union_sdiff_distrib,
      inter_union_distrib_left,
      htw.inter_even_eq_sdiff_of_local_replacement hG hQo hQm j,
      htw.inter_even_eq_sdiff_of_local_replacement hG hQo hQm (j + 1)]
  refine
    { finiteFaces := fun j => (hbasic j).choose
      manifold := fun j => (hbasic j).choose_spec.1
      orientable := fun j => (hbasic j).choose_spec.2
      interiorCarrier := ?_
      piecesDisjoint := ?_
      boundary := forall_replaceAdjacentSurfaces X i Q₀ Q₁
        (p := fun j Q => (boundaryComplex 2 Q).space =
          Q.space ∩ (T'' (2 * j) ∪ T'' (2 * (j + 1))))
        (hboundary (i - 1) Q₀ hout₀ hmeet₀ hb₀) (hboundary i Q₁ hout₁ hmeet₁ hb₁)
        (fun j _ _ => h.boundary j)
      lowerTrace := fun j => htraces j j (h.lowerTrace j)
      upperTrace := fun j => htraces j (j + 1) (h.upperTrace j)
      lowerOrigin := fun j =>
        (traceCircles_subset_of_inter_subset (h.lowerTrace j).traceCover (hmeets j j)).trans
          (h.lowerOrigin j)
      upperOrigin := fun j =>
        (traceCircles_subset_of_inter_subset (h.upperTrace j).traceCover (hmeets j (j + 1))).trans
          (h.upperOrigin j)
      centerNotMem := ?_
      subsetInterior := ?_
      separator := ?_ }
  · intro j x hx
    by_cases hxO : x ∈ interior (φ '' S (2 * i))
    · rcases hactive hx hxO with rfl | rfl
      · apply interior_mono (fun _ hx => Or.inr hx)
        simpa only [sub_add_cancel] using hxO
      · exact interior_mono (fun _ hx => Or.inl (Or.inl hx)) hxO
    · exact h.interiorCarrier j ((hout j).subset ⟨hx, hxO⟩).1
  · intro j k hjk
    apply disjoint_left.mpr
    intro x hxj hxk
    by_cases hxO : x ∈ interior (φ '' S (2 * i))
    · rcases hactive hxj hxO with rfl | rfl <;> rcases hactive hxk hxO with rfl | rfl
      · exact hjk rfl
      · exact disjoint_left.mp hdis (by simpa only [Y, replaceAdjacentSurfaces_left] using hxj)
          (by simpa only [Y, replaceAdjacentSurfaces_right] using hxk)
      · exact disjoint_left.mp hdis (by simpa only [Y, replaceAdjacentSurfaces_left] using hxk)
          (by simpa only [Y, replaceAdjacentSurfaces_right] using hxj)
      · exact hjk rfl
    · exact disjoint_left.mp (h.piecesDisjoint hjk) ((hout j).subset ⟨hxj, hxO⟩).1
        ((hout k).subset ⟨hxk, hxO⟩).1
  · intro j hx
    exact h.centerNotMem j ((hout j).subset ⟨hx, htw.center_notMem_interior_outer _⟩).1
  · simpa only [towerSurface_replaceAdjacentSurfaces] using hCI
  · simpa only [towerSurface_replaceAdjacentSurfaces] using hsep

end DifferentialGeometry.Topology.PiecewiseLinear
