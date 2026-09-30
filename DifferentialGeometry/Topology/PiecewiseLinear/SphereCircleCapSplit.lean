/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.Topology.PiecewiseLinear.PLDiskArcGluing
import DifferentialGeometry.Topology.PiecewiseLinear.BallInterior
import DifferentialGeometry.Topology.PiecewiseLinear.SphereSchoenflies

open Set

namespace DifferentialGeometry.Topology.PiecewiseLinear

variable {F : Type} [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]

theorem IsPLHomeomorphOn.isPreconnected_sdiff_of_subset_boundary {E β : Set F}
    {r : (Fin 3 → ℝ) → F} (hr : IsPLHomeomorphOn r (Convexity.StdSimplex.coordinateSet ℝ (Fin 3)) E)
    (hβ : β ⊆ r '' stdSimplexBoundary 2) : IsPreconnected (E \ β) ∧ closure (E \ β) = E := by
  have hO : IsPreconnected (r '' openSimplex (stdVertices 1)) :=
    (convex_openSimplex _).isPreconnected.image r
      (hr.isPiecewiseAffineOn.continuousOn.mono openSimplex_stdVertices_subset_stdSimplex)
  have hOeq : r '' openSimplex (stdVertices 1) = E \ r '' stdSimplexBoundary 2 :=
    IsPLHomeomorphOn.image_openSimplex_stdVertices (n := 1) hr
  have hcl : closure (E \ r '' stdSimplexBoundary 2) = E :=
    IsPLHomeomorphOn.closure_sdiff_image_stdSimplexBoundary (n := 1) hr
  have hEc : IsClosed E := (show IsPLBall 2 E from ⟨r, hr⟩).isPolyhedron.isClosed
  have hsub1 : E \ r '' stdSimplexBoundary 2 ⊆ E \ β := sdiff_subset_sdiff_right hβ
  have hsub2 : E \ β ⊆ closure (E \ r '' stdSimplexBoundary 2) := by
    rw [hcl]
    exact sdiff_subset
  rw [hOeq] at hO
  refine ⟨hO.subset_closure hsub1 hsub2, Subset.antisymm (closure_minimal sdiff_subset hEc) ?_⟩
  calc E = closure (E \ r '' stdSimplexBoundary 2) := hcl.symm
    _ ⊆ closure (E \ β) := closure_mono hsub1

theorem exists_isPLHomeomorphOn_closure_sdiff_biUnion_of_caps {D : Set F}
    {q : (Fin 3 → ℝ) → F} (hq : IsPLHomeomorphOn q (Convexity.StdSimplex.coordinateSet ℝ (Fin 3)) D) {ι : Type*}
    {E β : ι → Set F} {r : ι → (Fin 3 → ℝ) → F} {γ : ι → ℝ → F}
    (hr : ∀ i, IsPLHomeomorphOn (r i) (Convexity.StdSimplex.coordinateSet ℝ (Fin 3)) (E i))
    (hγ : ∀ i, IsPLHomeomorphOn (γ i) (Icc 0 1) (β i))
    (hβ : ∀ i, β i ⊆ r i '' stdSimplexBoundary 2) (s : Finset ι)
    (hED : ∀ i ∈ s, E i ⊆ D) (hEDb : ∀ i ∈ s, E i ∩ q '' stdSimplexBoundary 2 = β i)
    (hdisj : ∀ i ∈ s, ∀ j ∈ s, i ≠ j → Disjoint (E i) (E j)) :
    ∃ q' : (Fin 3 → ℝ) → F,
      IsPLHomeomorphOn q' (Convexity.StdSimplex.coordinateSet ℝ (Fin 3)) (closure (D \ ⋃ i ∈ s, E i)) ∧
      q' '' stdSimplexBoundary 2 = (q '' stdSimplexBoundary 2 \
          ⋃ i ∈ s, (β i \ {γ i 0, γ i 1})) ∪
        ⋃ i ∈ s, closure (r i '' stdSimplexBoundary 2 \ β i) ∧
      (∀ i ∈ s, closure (D \ ⋃ j ∈ s, E j) ∩ E i =
        closure (r i '' stdSimplexBoundary 2 \ β i)) ∧
      closure (D \ ⋃ i ∈ s, E i) ∪ ⋃ i ∈ s, E i = D := by
  classical
  have hDc : IsClosed D := (show IsPLBall 2 D from ⟨q, hq⟩).isPolyhedron.isClosed
  have hEc : ∀ i, IsClosed (E i) := fun i =>
    (show IsPLBall 2 (E i) from ⟨r i, hr i⟩).isPolyhedron.isClosed
  have hEbE : ∀ i, r i '' stdSimplexBoundary 2 ⊆ E i := fun i => by
    rw [← (hr i).image_eq]
    exact image_mono fun x hx => hx.1
  have hβ'E : ∀ i, closure (r i '' stdSimplexBoundary 2 \ β i) ⊆ E i := fun i =>
    closure_minimal (sdiff_subset.trans (hEbE i)) (hEc i)
  induction s using Finset.induction_on with
  | empty =>
    refine ⟨q, ?_, ?_, fun i hi => absurd hi (Finset.notMem_empty i), ?_⟩
    · simpa [hDc.closure_eq] using hq
    · simp
    · simp
  | @insert j s hjs ih =>
    obtain ⟨q₁, hq₁, hq₁b, hq₁i, hq₁u⟩ := ih (fun i hi => hED i (Finset.mem_insert_of_mem hi))
      (fun i hi => hEDb i (Finset.mem_insert_of_mem hi))
      (fun i hi k hk hik => hdisj i (Finset.mem_insert_of_mem hi) k (Finset.mem_insert_of_mem hk)
        hik)
    set U := ⋃ i ∈ s, E i with hUdef
    set D₁ := closure (D \ U) with hD₁def
    have hjU : Disjoint (E j) U := by
      refine Set.disjoint_left.mpr fun x hxj hxU => ?_
      obtain ⟨i, hi, hxi⟩ := mem_iUnion₂.mp hxU
      have hij : i ≠ j := fun h => hjs (h ▸ hi)
      exact Set.disjoint_left.mp (hdisj j (Finset.mem_insert_self j s) i
        (Finset.mem_insert_of_mem hi) hij.symm) hxj hxi
    have hjD₁ : E j ⊆ D₁ := fun x hx =>
      subset_closure ⟨hED j (Finset.mem_insert_self j s) hx, Set.disjoint_left.mp hjU hx⟩
    have hβjU : ∀ i ∈ s, Disjoint (β j) (E i) := fun i hi =>
      Disjoint.mono ((hβ j).trans (hEbE j)) (subset_iUnion₂ (s := fun i (_ : i ∈ s) => E i) i hi)
        hjU
    have hjb : E j ∩ q₁ '' stdSimplexBoundary 2 = β j := by
      rw [hq₁b]
      apply Subset.antisymm
      · rintro x ⟨hxj, hx | hx⟩
        · rw [← hEDb j (Finset.mem_insert_self j s)]
          exact ⟨hxj, hx.1⟩
        · obtain ⟨i, hi, hxi⟩ := mem_iUnion₂.mp hx
          exact absurd (mem_iUnion₂.mpr ⟨i, hi, hβ'E i hxi⟩) (Set.disjoint_left.mp hjU hxj)
      · intro x hx
        have hxE := (hEDb j (Finset.mem_insert_self j s)).symm.subset hx
        refine ⟨hxE.1, Or.inl ⟨hxE.2, fun hxU => ?_⟩⟩
        obtain ⟨i, hi, hxi⟩ := mem_iUnion₂.mp hxU
        exact Set.disjoint_left.mp (hβjU i hi) hx ((hβ i).trans (hEbE i) hxi.1)
    obtain ⟨q₂, hq₂, hq₂b, hq₂i, hq₂u⟩ := exists_isPLHomeomorphOn_closure_sdiff_of_cap hq₁ (hr j)
      hjD₁ (hγ j) (hβ j) hjb
    have hU' : ⋃ i ∈ insert j s, E i = E j ∪ U := Finset.set_biUnion_insert j s E
    have hD₂ : closure (D₁ \ E j) = closure (D \ ⋃ i ∈ insert j s, E i) := by
      rw [hU']
      apply Subset.antisymm
      · refine closure_minimal (fun x hx => ?_) isClosed_closure
        have h := (hEc j).isOpen_compl.inter_closure ⟨hx.2, hx.1⟩
        refine closure_mono (fun y hy => ?_) h
        exact ⟨hy.2.1, fun hy' => hy'.elim hy.1 hy.2.2⟩
      · exact closure_mono fun y hy => ⟨subset_closure ⟨hy.1, fun h => hy.2 (Or.inr h)⟩,
          fun h => hy.2 (Or.inl h)⟩
    rw [← hD₂]
    refine ⟨q₂, hq₂, ?_, ?_, ?_⟩
    · rw [hq₂b, hq₁b, Finset.set_biUnion_insert, Finset.set_biUnion_insert]
      ext x
      constructor
      · rintro (⟨hx | hx, hxj⟩ | hx)
        · refine Or.inl ⟨hx.1, ?_⟩
          rintro (h | h)
          · exact hxj h
          · exact hx.2 h
        · exact Or.inr (Or.inr hx)
        · exact Or.inr (Or.inl hx)
      · rintro (⟨hxq, hxn⟩ | hx | hx)
        · exact Or.inl ⟨Or.inl ⟨hxq, fun h => hxn (Or.inr h)⟩, fun h => hxn (Or.inl h)⟩
        · exact Or.inr hx
        · refine Or.inl ⟨Or.inr hx, fun h => ?_⟩
          obtain ⟨i, hi, hxi⟩ := mem_iUnion₂.mp hx
          exact Set.disjoint_left.mp (hβjU i hi) h.1 (hβ'E i hxi)
    · intro i hi
      rcases Finset.mem_insert.mp hi with rfl | hi
      · exact hq₂i
      · apply Subset.antisymm
        · rw [← hq₁i i hi]
          exact inter_subset_inter_left _ (closure_minimal sdiff_subset isClosed_closure)
        · intro x hx
          have hxD₁ : x ∈ D₁ ∩ E i := (hq₁i i hi).symm ▸ hx
          have hxj : x ∉ E j := fun h => Set.disjoint_left.mp hjU h
            (mem_iUnion₂.mpr ⟨i, hi, hxD₁.2⟩)
          exact ⟨subset_closure ⟨hxD₁.1, hxj⟩, hxD₁.2⟩
    · rw [hU', ← union_assoc, hq₂u, hq₁u]

theorem IsPLSphere.exists_split_of_circle_caps {S J : Set F} (hS : IsPLSphere 2 S)
    (hJ : IsPLSphere 1 J) (hJS : J ⊆ S) {ι : Type*} [Finite ι] {E β : ι → Set F}
    {r : ι → (Fin 3 → ℝ) → F} {γ : ι → ℝ → F}
    (hr : ∀ i, IsPLHomeomorphOn (r i) (Convexity.StdSimplex.coordinateSet ℝ (Fin 3)) (E i)) (hES : ∀ i, E i ⊆ S)
    (hdisj : Pairwise fun i j => Disjoint (E i) (E j))
    (hγ : ∀ i, IsPLHomeomorphOn (γ i) (Icc 0 1) (β i))
    (hβ : ∀ i, β i ⊆ r i '' stdSimplexBoundary 2) (hEJ : ∀ i, E i ∩ J = β i) :
    ∃ (X Y : Set F) (qX qY : (Fin 3 → ℝ) → F),
      IsPLHomeomorphOn qX (Convexity.StdSimplex.coordinateSet ℝ (Fin 3)) X ∧
      IsPLHomeomorphOn qY (Convexity.StdSimplex.coordinateSet ℝ (Fin 3)) Y ∧
      X ∪ Y ∪ (⋃ i, E i) = S ∧ X ∩ Y = J \ ⋃ i, (β i \ {γ i 0, γ i 1}) ∧
      (∀ i, (X ∩ E i = β i ∧ Y ∩ E i = closure (r i '' stdSimplexBoundary 2 \ β i)) ∨
        (X ∩ E i = closure (r i '' stdSimplexBoundary 2 \ β i) ∧ Y ∩ E i = β i)) ∧
      qX '' stdSimplexBoundary 2 = (J \ ⋃ i, (β i \ {γ i 0, γ i 1})) ∪ ⋃ i, (X ∩ E i) ∧
      qY '' stdSimplexBoundary 2 = (J \ ⋃ i, (β i \ {γ i 0, γ i 1})) ∪ ⋃ i, (Y ∩ E i) := by
  classical
  let _ : Fintype ι := Fintype.ofFinite ι
  obtain ⟨D₀, D₁, q₀, q₁, hq₀, hq₁, hq₀J, hq₁J, hunion, hinter⟩ :=
    exists_isPLBall_pair_of_isPLSphere_two hS hJ hJS
  have hD₀c : IsClosed D₀ := (show IsPLBall 2 D₀ from ⟨q₀, hq₀⟩).isPolyhedron.isClosed
  have hD₁c : IsClosed D₁ := (show IsPLBall 2 D₁ from ⟨q₁, hq₁⟩).isPolyhedron.isClosed
  have hEbE : ∀ i, r i '' stdSimplexBoundary 2 ⊆ E i := fun i => by
    rw [← (hr i).image_eq]
    exact image_mono fun x hx => hx.1
  have hEc : ∀ i, IsClosed (E i) := fun i =>
    (show IsPLBall 2 (E i) from ⟨r i, hr i⟩).isPolyhedron.isClosed
  have hβ'E : ∀ i, closure (r i '' stdSimplexBoundary 2 \ β i) ⊆ E i := fun i =>
    closure_minimal (sdiff_subset.trans (hEbE i)) (hEc i)
  have hβE : ∀ i, β i ⊆ E i := fun i => (hβ i).trans (hEbE i)
  have hββ' : ∀ i, β i ∩ closure (r i '' stdSimplexBoundary 2 \ β i) = {γ i 0, γ i 1} := by
    intro i
    have hcirc : IsPLSphere 1 (r i '' stdSimplexBoundary 2) :=
      ⟨r i, (hr i).restrict isPolyhedron_stdSimplexBoundary_two fun x hx => hx.1⟩
    obtain ⟨-, -, -, -, h, -⟩ := hcirc.exists_isPLHomeomorphOn_closure_sdiff (hγ i) (hβ i)
    exact h
  have hside : ∀ i, E i ⊆ D₀ ∨ E i ⊆ D₁ := by
    intro i
    obtain ⟨hpre, hcl⟩ := (hr i).isPreconnected_sdiff_of_subset_boundary (hβ i)
    have hsub : E i \ β i ⊆ D₁ᶜ ∪ D₀ᶜ := by
      rintro x ⟨hxE, hxβ⟩
      by_contra h
      simp only [mem_union, mem_compl_iff, not_or, not_not] at h
      have hxJ : x ∈ J := hinter ▸ ⟨h.2, h.1⟩
      exact hxβ ((hEJ i).subset ⟨hxE, hxJ⟩)
    have hemp : E i \ β i ∩ (D₁ᶜ ∩ D₀ᶜ) = ∅ := by
      refine eq_empty_of_forall_notMem fun x hx => ?_
      have hxS : x ∈ D₀ ∪ D₁ := hunion.symm ▸ hES i hx.1.1
      rcases hxS with h | h
      · exact hx.2.2 h
      · exact hx.2.1 h
    rcases isPreconnected_iff_subset_of_disjoint.mp hpre _ _ hD₁c.isOpen_compl hD₀c.isOpen_compl
      hsub hemp with h | h
    · left
      rw [← hcl]
      refine closure_minimal (fun x hx => ?_) hD₀c
      have hxS : x ∈ D₀ ∪ D₁ := hunion.symm ▸ hES i hx.1
      exact hxS.resolve_right (h hx)
    · right
      rw [← hcl]
      refine closure_minimal (fun x hx => ?_) hD₁c
      have hxS : x ∈ D₀ ∪ D₁ := hunion.symm ▸ hES i hx.1
      exact hxS.resolve_left (h hx)
  set s₀ := Finset.univ.filter (fun i => E i ⊆ D₀) with hs₀
  set s₁ := Finset.univ.filter (fun i => ¬ E i ⊆ D₀) with hs₁
  have hmem₀ : ∀ i, i ∈ s₀ ↔ E i ⊆ D₀ := fun i => by simp [hs₀]
  have hmem₁ : ∀ i, i ∈ s₁ ↔ ¬ E i ⊆ D₀ := fun i => by simp [hs₁]
  have hs₁D : ∀ i ∈ s₁, E i ⊆ D₁ := fun i hi => (hside i).resolve_left ((hmem₁ i).mp hi)
  obtain ⟨qX, hqX, hqXb, hqXi, hqXu⟩ := exists_isPLHomeomorphOn_closure_sdiff_biUnion_of_caps
    hq₀ hr hγ hβ s₀ (fun i hi => (hmem₀ i).mp hi)
    (fun i hi => by rw [hq₀J, hEJ i]) (fun i _ j _ hij => hdisj hij)
  obtain ⟨qY, hqY, hqYb, hqYi, hqYu⟩ := exists_isPLHomeomorphOn_closure_sdiff_biUnion_of_caps
    hq₁ hr hγ hβ s₁ hs₁D (fun i hi => by rw [hq₁J, hEJ i]) (fun i _ j _ hij => hdisj hij)
  set X := closure (D₀ \ ⋃ i ∈ s₀, E i) with hXdef
  set Y := closure (D₁ \ ⋃ i ∈ s₁, E i) with hYdef
  have hXD₀ : X ⊆ D₀ := closure_minimal sdiff_subset hD₀c
  have hYD₁ : Y ⊆ D₁ := closure_minimal sdiff_subset hD₁c
  have hqXX : qX '' stdSimplexBoundary 2 ⊆ X := by
    rw [← hqX.image_eq]
    exact image_mono fun x hx => hx.1
  have hqYY : qY '' stdSimplexBoundary 2 ⊆ Y := by
    rw [← hqY.image_eq]
    exact image_mono fun x hx => hx.1
  have hβfar : ∀ i k, i ≠ k → Disjoint (β i) (E k) := fun i k hik =>
    Disjoint.mono_left (hβE i) (hdisj hik)
  have hβX : ∀ i, i ∉ s₀ → β i ⊆ X := by
    intro i hi x hx
    refine hqXX ?_
    rw [hqXb, hq₀J]
    refine Or.inl ⟨((hEJ i).symm.subset hx).2, fun hxU => ?_⟩
    obtain ⟨k, hk, hxk⟩ := mem_iUnion₂.mp hxU
    have hik : i ≠ k := fun h => hi (h ▸ hk)
    exact Set.disjoint_left.mp (hβfar i k hik) hx (hβE k hxk.1)
  have hβY : ∀ i, i ∉ s₁ → β i ⊆ Y := by
    intro i hi x hx
    refine hqYY ?_
    rw [hqYb, hq₁J]
    refine Or.inl ⟨((hEJ i).symm.subset hx).2, fun hxU => ?_⟩
    obtain ⟨k, hk, hxk⟩ := mem_iUnion₂.mp hxU
    have hik : i ≠ k := fun h => hi (h ▸ hk)
    exact Set.disjoint_left.mp (hβfar i k hik) hx (hβE k hxk.1)
  have hXE : ∀ i, i ∉ s₀ → X ∩ E i = β i := by
    intro i hi
    have hi₁ : i ∈ s₁ := (hmem₁ i).mpr fun h => hi ((hmem₀ i).mpr h)
    refine Subset.antisymm (fun x hx => ?_) (subset_inter (hβX i hi) (hβE i))
    have hxJ : x ∈ J := hinter ▸ ⟨hXD₀ hx.1, hs₁D i hi₁ hx.2⟩
    exact (hEJ i).subset ⟨hx.2, hxJ⟩
  have hYE : ∀ i, i ∉ s₁ → Y ∩ E i = β i := by
    intro i hi
    have hi₀ : i ∈ s₀ := by
      by_contra h
      exact hi ((hmem₁ i).mpr fun h' => h ((hmem₀ i).mpr h'))
    refine Subset.antisymm (fun x hx => ?_) (subset_inter (hβY i hi) (hβE i))
    have hxJ : x ∈ J := hinter ▸ ⟨(hmem₀ i).mp hi₀ hx.2, hYD₁ hx.1⟩
    exact (hEJ i).subset ⟨hx.2, hxJ⟩
  have hcase : ∀ i, (X ∩ E i = β i ∧ Y ∩ E i = closure (r i '' stdSimplexBoundary 2 \ β i)) ∨
      (X ∩ E i = closure (r i '' stdSimplexBoundary 2 \ β i) ∧ Y ∩ E i = β i) := by
    intro i
    by_cases hi : i ∈ s₀
    · have hi₁ : i ∉ s₁ := fun h => (hmem₁ i).mp h ((hmem₀ i).mp hi)
      exact Or.inr ⟨hqXi i hi, hYE i hi₁⟩
    · have hi₁ : i ∈ s₁ := (hmem₁ i).mpr fun h => hi ((hmem₀ i).mpr h)
      exact Or.inl ⟨hXE i hi, hqYi i hi₁⟩
  have hopen_out : ∀ i, ∀ x ∈ β i \ {γ i 0, γ i 1},
      x ∉ closure (r i '' stdSimplexBoundary 2 \ β i) := by
    intro i x hx hx'
    exact hx.2 ((hββ' i).subset ⟨hx.1, hx'⟩)
  have hXY : X ∩ Y = J \ ⋃ i, (β i \ {γ i 0, γ i 1}) := by
    apply Subset.antisymm
    · rintro x ⟨hxX, hxY⟩
      refine ⟨hinter ▸ ⟨hXD₀ hxX, hYD₁ hxY⟩, fun hxU => ?_⟩
      obtain ⟨i, hxi⟩ := mem_iUnion.mp hxU
      rcases hcase i with ⟨-, hY⟩ | ⟨hX, -⟩
      · exact hopen_out i x hxi (hY ▸ ⟨hxY, hβE i hxi.1⟩)
      · exact hopen_out i x hxi (hX ▸ ⟨hxX, hβE i hxi.1⟩)
    · rintro x ⟨hxJ, hxn⟩
      refine ⟨hqXX ?_, hqYY ?_⟩
      · rw [hqXb, hq₀J]
        exact Or.inl ⟨hxJ, fun h => hxn (by
          obtain ⟨i, -, hxi⟩ := mem_iUnion₂.mp h
          exact mem_iUnion.mpr ⟨i, hxi⟩)⟩
      · rw [hqYb, hq₁J]
        exact Or.inl ⟨hxJ, fun h => hxn (by
          obtain ⟨i, -, hxi⟩ := mem_iUnion₂.mp h
          exact mem_iUnion.mpr ⟨i, hxi⟩)⟩
  have hbd : ∀ (s : Finset ι) (Z : Set F) (qZ : (Fin 3 → ℝ) → F),
      (∀ i, i ∈ s → Z ∩ E i = closure (r i '' stdSimplexBoundary 2 \ β i)) →
      (∀ i, i ∉ s → Z ∩ E i = β i) →
      qZ '' stdSimplexBoundary 2 = (J \ ⋃ i ∈ s, (β i \ {γ i 0, γ i 1})) ∪
        ⋃ i ∈ s, closure (r i '' stdSimplexBoundary 2 \ β i) →
      qZ '' stdSimplexBoundary 2 = (J \ ⋃ i, (β i \ {γ i 0, γ i 1})) ∪ ⋃ i, (Z ∩ E i) := by
    intro s Z qZ hin hout hqZ
    rw [hqZ]
    ext x
    constructor
    · rintro (⟨hxJ, hxn⟩ | hx)
      · by_cases hxo : ∃ i, x ∈ β i \ {γ i 0, γ i 1}
        · obtain ⟨i, hxi⟩ := hxo
          have hi : i ∉ s := fun hi => hxn (mem_iUnion₂.mpr ⟨i, hi, hxi⟩)
          exact Or.inr (mem_iUnion.mpr ⟨i, (hout i hi).symm ▸ hxi.1⟩)
        · refine Or.inl ⟨hxJ, fun h => hxo ?_⟩
          obtain ⟨i, hxi⟩ := mem_iUnion.mp h
          exact ⟨i, hxi⟩
      · obtain ⟨i, hi, hxi⟩ := mem_iUnion₂.mp hx
        exact Or.inr (mem_iUnion.mpr ⟨i, (hin i hi).symm ▸ hxi⟩)
    · rintro (⟨hxJ, hxn⟩ | hx)
      · refine Or.inl ⟨hxJ, fun h => hxn ?_⟩
        obtain ⟨i, -, hxi⟩ := mem_iUnion₂.mp h
        exact mem_iUnion.mpr ⟨i, hxi⟩
      · obtain ⟨i, hxi⟩ := mem_iUnion.mp hx
        by_cases hi : i ∈ s
        · exact Or.inr (mem_iUnion₂.mpr ⟨i, hi, (hin i hi) ▸ hxi⟩)
        · have hxβ : x ∈ β i := (hout i hi) ▸ hxi
          refine Or.inl ⟨((hEJ i).symm.subset hxβ).2, fun h => ?_⟩
          obtain ⟨k, hk, hxk⟩ := mem_iUnion₂.mp h
          have hik : i ≠ k := fun h' => hi (h' ▸ hk)
          exact Set.disjoint_left.mp (hβfar i k hik) hxβ (hβE k hxk.1)
  refine ⟨X, Y, qX, qY, hqX, hqY, ?_, hXY, hcase, ?_, ?_⟩
  · have hsplit : (⋃ i, E i) = (⋃ i ∈ s₀, E i) ∪ ⋃ i ∈ s₁, E i := by
      ext x
      simp only [mem_iUnion, mem_union, exists_prop]
      constructor
      · rintro ⟨i, hi⟩
        by_cases h : i ∈ s₀
        · exact Or.inl ⟨i, h, hi⟩
        · exact Or.inr ⟨i, (hmem₁ i).mpr fun h' => h ((hmem₀ i).mpr h'), hi⟩
      · rintro (⟨i, -, hi⟩ | ⟨i, -, hi⟩) <;> exact ⟨i, hi⟩
    rw [hsplit, ← hunion, ← hqXu, ← hqYu]
    ext x
    simp only [mem_union]
    tauto
  · rw [hq₀J] at hqXb
    exact hbd s₀ X qX hqXi hXE hqXb
  · rw [hq₁J] at hqYb
    exact hbd s₁ Y qY hqYi hYE hqYb

end DifferentialGeometry.Topology.PiecewiseLinear
