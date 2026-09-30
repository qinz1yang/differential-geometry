/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.Topology.PiecewiseLinear.CircleIntersection
import DifferentialGeometry.Topology.Connected.TwoComponentPartition

open Set Topology

namespace DifferentialGeometry.Topology.PiecewiseLinear

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem mem_heightSingularPoints_congr {S T : Set E} {ℓ : E → ℝ} {p : E}
    (hST : ∀ᶠ x in 𝓝 p, x ∈ S ↔ x ∈ T) :
    p ∈ heightSingularPoints S ℓ ↔ p ∈ heightSingularPoints T ℓ := by
  have hp : p ∈ S ↔ p ∈ T := hST.self_of_nhds
  have hcross : HasPLCrossingAt S {x | ℓ x = ℓ p} p ↔
      HasPLCrossingAt T {x | ℓ x = ℓ p} p :=
    ⟨fun h => h.congr hST (Filter.Eventually.of_forall fun _ => Iff.rfl),
      fun h => h.congr (hST.mono fun _ h => h.symm) (Filter.Eventually.of_forall fun _ => Iff.rfl)⟩
  have hnhds : 𝓝[S ∩ {x | ℓ x = ℓ p}] p = 𝓝[T ∩ {x | ℓ x = ℓ p}] p := by
    apply nhdsWithin_eq_iff_eventuallyEqSet.mpr
    filter_upwards [hST] with x hx
    exact propext (and_congr_left fun _ => hx)
  change (p ∈ S ∧ ¬ HasPLCrossingAt S {x | ℓ x = ℓ p} p ∧ _) ↔
    (p ∈ T ∧ ¬ HasPLCrossingAt T {x | ℓ x = ℓ p} p ∧ _)
  rw [hp, hcross, hnhds]

theorem heightSingularPoints_union_sdiff {S T : Set E} (hT : IsClosed T) (ℓ : E → ℝ) :
    heightSingularPoints (S ∪ T) ℓ \ T = heightSingularPoints S ℓ \ T := by
  ext p
  by_cases hp : p ∈ T
  · simp only [mem_sdiff, hp, not_true_eq_false, and_false]
  · have hlocal : ∀ᶠ x in 𝓝 p, x ∈ S ∪ T ↔ x ∈ S := by
      filter_upwards [hT.isOpen_compl.mem_nhds hp] with x hx
      exact or_iff_left hx
    simp only [mem_sdiff, mem_heightSingularPoints_congr hlocal]

theorem heightSingularPoints_cap_sdiff {A B D : Set E} (hB : IsClosed B) (hD : IsClosed D)
    (hAB : A ∩ B ⊆ D) (ℓ : E → ℝ) :
    heightSingularPoints (A ∪ D) ℓ \ D = (heightSingularPoints (A ∪ B) ℓ ∩ A) \ D := by
  rw [heightSingularPoints_union_sdiff hD]
  ext p
  by_cases hpD : p ∈ D
  · simp only [mem_sdiff, hpD, not_true_eq_false, and_false]
  · constructor
    · rintro ⟨hp, hpD⟩
      have hpB : p ∉ B := fun h => hpD (hAB ⟨hp.1, h⟩)
      have hsing := (show p ∈ heightSingularPoints A ℓ \ B from ⟨hp, hpB⟩)
      rw [← heightSingularPoints_union_sdiff hB] at hsing
      exact ⟨⟨hsing.1, hp.1⟩, hpD⟩
    · rintro ⟨⟨hp, hpA⟩, hpD⟩
      have hpB : p ∉ B := fun h => hpD (hAB ⟨hpA, h⟩)
      have hsing := (show p ∈ heightSingularPoints (A ∪ B) ℓ \ B from ⟨hp, hpB⟩)
      rw [heightSingularPoints_union_sdiff hB] at hsing
      exact ⟨hsing.1, hpD⟩

theorem levelPolygons_union_of_subset_fiber {A D : Set E} {ℓ : E → ℝ} {c r : ℝ}
    (hD : D ⊆ {x | ℓ x = c}) (hr : r ≠ c) :
    levelPolygons (A ∪ D) ℓ r = levelPolygons A ℓ r := by
  ext J
  constructor
  · rintro ⟨hJ, hJA⟩
    refine ⟨hJ, fun x hx => ?_⟩
    obtain ⟨hxA | hxD, hxr⟩ := hJA hx
    · exact ⟨hxA, hxr⟩
    · exact (hr (hxr.symm.trans (hD hxD))).elim
  · rintro ⟨hJ, hJA⟩
    exact ⟨hJ, fun x hx => ⟨Or.inl (hJA hx).1, (hJA hx).2⟩⟩

theorem levelPolygons_union_of_disjoint_fibers {A B : Set E} (hA : IsClosed A) (hB : IsClosed B)
    (ℓ : E → ℝ) (hℓ : Continuous ℓ) (r : ℝ)
    (hdis : Disjoint (A ∩ {x | ℓ x = r}) (B ∩ {x | ℓ x = r})) :
    levelPolygons (A ∪ B) ℓ r = levelPolygons A ℓ r ∪ levelPolygons B ℓ r := by
  ext J
  constructor
  · rintro ⟨hJ, hsub⟩
    have hclosed : IsClosed {x | ℓ x = r} := isClosed_eq hℓ continuous_const
    have hcover : J ⊆ (A ∩ {x | ℓ x = r}) ∪ (B ∩ {x | ℓ x = r}) := by
      intro x hx
      exact ((hsub hx).1).elim (fun h => Or.inl ⟨h, (hsub hx).2⟩)
        (fun h => Or.inr ⟨h, (hsub hx).2⟩)
    rcases subset_or_subset_of_isPreconnected_of_isClosed hJ.isConnected_one.isPreconnected
      (hA.inter hclosed) (hB.inter hclosed) hdis hcover with h | h
    · exact Or.inl ⟨hJ, h⟩
    · exact Or.inr ⟨hJ, h⟩
  · rintro (⟨hJ, hsub⟩ | ⟨hJ, hsub⟩)
    · exact ⟨hJ, fun x hx => ⟨Or.inl (hsub hx).1, (hsub hx).2⟩⟩
    · exact ⟨hJ, fun x hx => ⟨Or.inr (hsub hx).1, (hsub hx).2⟩⟩

theorem encard_levelPolygons_union_of_disjoint_fibers {A B : Set E}
    (hA : IsClosed A) (hB : IsClosed B) (ℓ : E → ℝ) (hℓ : Continuous ℓ) (r : ℝ)
    (hdis : Disjoint (A ∩ {x | ℓ x = r}) (B ∩ {x | ℓ x = r})) :
    (levelPolygons (A ∪ B) ℓ r).encard =
      (levelPolygons A ℓ r).encard + (levelPolygons B ℓ r).encard := by
  rw [levelPolygons_union_of_disjoint_fibers hA hB ℓ hℓ r hdis]
  apply Set.encard_union_eq
  apply Set.disjoint_left.mpr
  intro J hJA hJB
  obtain ⟨x, hx⟩ := hJA.1.nonempty
  exact Set.disjoint_left.mp hdis (hJA.2 hx) (hJB.2 hx)

theorem encard_levelPolygons_cap_eq {A B D : Set E} (hA : IsClosed A) (hB : IsClosed B)
    (ℓ : E → ℝ) (hℓ : Continuous ℓ) {c r : ℝ} (hAB : A ∩ B ⊆ D)
    (hD : D ⊆ {x | ℓ x = c}) (hr : r ≠ c) :
    (levelPolygons (A ∪ B) ℓ r).encard =
      (levelPolygons (A ∪ D) ℓ r).encard + (levelPolygons (B ∪ D) ℓ r).encard := by
  rw [levelPolygons_union_of_subset_fiber hD hr, levelPolygons_union_of_subset_fiber hD hr]
  apply encard_levelPolygons_union_of_disjoint_fibers hA hB ℓ hℓ r
  apply Set.disjoint_left.mpr
  rintro x ⟨hxA, hxr⟩ ⟨hxB, -⟩
  exact hr (hxr.symm.trans (hD (hAB ⟨hxA, hxB⟩)))

theorem levelPolygons_union_of_inter_eq {A B J : Set E} (hA : IsClosed A) (hB : IsClosed B)
    (ℓ : E → ℝ) (r : ℝ) (hAB : A ∩ B = J) (p : E)
    (hmeet : ∀ T ∈ levelPolygons (A ∪ B) ℓ r, T ≠ J → T ∩ J ⊆ {p}) :
    levelPolygons (A ∪ B) ℓ r = levelPolygons A ℓ r ∪ levelPolygons B ℓ r := by
  ext T
  constructor
  · intro hT
    by_cases hTJ : T = J
    · subst T
      exact Or.inl ⟨hT.1, fun x hx => ⟨(hAB.symm.subset hx).1, (hT.2 hx).2⟩⟩
    have hcover : T \ {p} ⊆ A ∪ B := sdiff_subset.trans (hT.2.trans inter_subset_left)
    have hsplit : T \ {p} ⊆ A ∨ T \ {p} ⊆ B := by
      by_cases hsub : T \ {p} ⊆ A
      · exact Or.inl hsub
      obtain ⟨x, hxT, hxA⟩ := Set.not_subset.mp hsub
      refine Or.inr fun y hyT => ?_
      by_contra hyB
      obtain ⟨z, hzT, hzA, hzB⟩ :=
        isPreconnected_closed_iff.mp (hT.1.isConnected_sdiff_singleton_one p).isPreconnected
          A B hA hB hcover ⟨y, hyT, (hcover hyT).resolve_right hyB⟩
            ⟨x, hxT, (hcover hxT).resolve_left hxA⟩
      exact hzT.2 (hmeet T hT hTJ ⟨hzT.1, hAB.subset ⟨hzA, hzB⟩⟩)
    rcases hsplit with hsub | hsub
    · have hTA : T ⊆ A := (hT.1.closure_sdiff_singleton_one p).symm.subset.trans
        (closure_minimal hsub hA)
      exact Or.inl ⟨hT.1, fun x hx => ⟨hTA hx, (hT.2 hx).2⟩⟩
    · have hTB : T ⊆ B := (hT.1.closure_sdiff_singleton_one p).symm.subset.trans
        (closure_minimal hsub hB)
      exact Or.inr ⟨hT.1, fun x hx => ⟨hTB hx, (hT.2 hx).2⟩⟩
  · rintro (⟨hT, hsub⟩ | ⟨hT, hsub⟩)
    · exact ⟨hT, fun x hx => ⟨Or.inl (hsub hx).1, (hsub hx).2⟩⟩
    · exact ⟨hT, fun x hx => ⟨Or.inr (hsub hx).1, (hsub hx).2⟩⟩

variable [FiniteDimensional ℝ E]

theorem levelPolygons_inter_of_inter_eq_circle {A B J : Set E} (ℓ : E → ℝ) (r : ℝ)
    (hAB : A ∩ B = J) (hJ : IsPLSphere 1 J) (hlevel : J ⊆ {x | ℓ x = r}) :
    levelPolygons A ℓ r ∩ levelPolygons B ℓ r = {J} := by
  ext T
  constructor
  · rintro ⟨hTA, hTB⟩
    exact eq_of_subset_of_isPLSphere_one hTA.1 hJ
      (fun x hx => hAB.subset ⟨(hTA.2 hx).1, (hTB.2 hx).1⟩)
  · rintro rfl
    exact ⟨⟨hJ, fun x hx => ⟨(hAB.symm.subset hx).1, hlevel hx⟩⟩,
      ⟨hJ, fun x hx => ⟨(hAB.symm.subset hx).2, hlevel hx⟩⟩⟩

theorem encard_levelPolygons_add_of_inter_eq_circle {A B J : Set E}
    (hA : IsClosed A) (hB : IsClosed B) (ℓ : E → ℝ) (r : ℝ)
    (hAB : A ∩ B = J) (hJ : IsPLSphere 1 J) (hlevel : J ⊆ {x | ℓ x = r}) (p : E)
    (hmeet : ∀ T ∈ levelPolygons (A ∪ B) ℓ r, T ≠ J → T ∩ J ⊆ {p}) :
    (levelPolygons A ℓ r).encard + (levelPolygons B ℓ r).encard =
      (levelPolygons (A ∪ B) ℓ r).encard + 1 := by
  rw [← Set.encard_union_add_encard_inter,
    ← levelPolygons_union_of_inter_eq hA hB ℓ r hAB p hmeet,
    levelPolygons_inter_of_inter_eq_circle ℓ r hAB hJ hlevel, encard_singleton]

end DifferentialGeometry.Topology.PiecewiseLinear
