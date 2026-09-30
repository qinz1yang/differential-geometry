/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.Topology.PiecewiseLinear.HoledSphereClosed
import DifferentialGeometry.Topology.PiecewiseLinear.LocallyFinitePLHomeomorphGluing
import DifferentialGeometry.Topology.PiecewiseLinear.BallPairRelativeGluing
import DifferentialGeometry.Topology.PiecewiseLinear.CircleAnnulusOrientation

open Set Topology

namespace DifferentialGeometry.Topology.PiecewiseLinear

private theorem holed_disk_inter_eq {X ι : Type*} {S : Set X} {D J : ι → Set X}
    (hDS : ∀ i, D i ⊆ S) (hJD : ∀ i, J i ⊆ D i)
    (hdis : Pairwise fun i j => Disjoint (D i) (D j)) (i : ι) :
    (S \ ⋃ j, (D j \ J j)) ∩ D i = J i := by
  apply Subset.antisymm
  · intro x hx
    by_contra hxJ
    exact hx.1.2 (mem_iUnion.mpr ⟨i, hx.2, hxJ⟩)
  · intro x hx
    refine ⟨⟨hDS i (hJD i hx), ?_⟩, hJD i hx⟩
    intro hhole
    obtain ⟨j, hj⟩ := mem_iUnion.mp hhole
    by_cases hji : j = i
    · subst j
      exact hj.2 hx
    · exact disjoint_left.mp (hdis hji) hj.1 (hJD i hx)

private theorem holed_disk_cover {X ι : Type*} {S : Set X} {D J : ι → Set X}
    (hDS : ∀ i, D i ⊆ S) : (S \ ⋃ i, (D i \ J i)) ∪ ⋃ i, D i = S := by
  apply Subset.antisymm (union_subset sdiff_subset (iUnion_subset hDS))
  intro x hx
  by_cases hD : ∃ i, x ∈ D i
  · exact Or.inr (mem_iUnion.mpr hD)
  · refine Or.inl ⟨hx, ?_⟩
    intro hhole
    obtain ⟨i, hi⟩ := mem_iUnion.mp hhole
    exact hD ⟨i, hi.1⟩

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F]
  [FiniteDimensional ℝ F]

theorem IsPLSphere.exists_isPLHomeomorphOn_glue_holed_disks
    {ι : Type*} [Finite ι] {S : Set E} {S' : Set F}
    (hS : IsPLSphere 2 S) (hS' : IsPLSphere 2 S')
    {D : ι → Set E} {D' : ι → Set F}
    {q : ι → (Fin 3 → ℝ) → E} {q' : ι → (Fin 3 → ℝ) → F}
    (hq : ∀ i, IsPLHomeomorphOn (q i) (Convexity.StdSimplex.coordinateSet ℝ (Fin 3)) (D i))
    (hq' : ∀ i, IsPLHomeomorphOn (q' i) (Convexity.StdSimplex.coordinateSet ℝ (Fin 3)) (D' i))
    (hDS : ∀ i, D i ⊆ S) (hD'S' : ∀ i, D' i ⊆ S')
    (hdis : Pairwise fun i j => Disjoint (D i) (D j))
    (hdis' : Pairwise fun i j => Disjoint (D' i) (D' j))
    {G₀ : E → F} {f : ι → E → F}
    (hG₀ : IsPLHomeomorphOn G₀ (S \ ⋃ i, (D i \ q i '' stdSimplexBoundary 2))
      (S' \ ⋃ i, (D' i \ q' i '' stdSimplexBoundary 2)))
    (hf : ∀ i, IsPLHomeomorphOn (f i) (D i) (D' i))
    (hmatch : ∀ i, EqOn G₀ (f i) (q i '' stdSimplexBoundary 2)) :
    ∃ G : E → F, IsPLHomeomorphOn G S S' ∧
      EqOn G G₀ (S \ ⋃ i, (D i \ q i '' stdSimplexBoundary 2)) ∧
      ∀ i, EqOn G (f i) (D i) := by
  classical
  let J : ι → Set E := fun i => q i '' stdSimplexBoundary 2
  let J' : ι → Set F := fun i => q' i '' stdSimplexBoundary 2
  let R := S \ ⋃ i, (D i \ J i)
  let R' := S' \ ⋃ i, (D' i \ J' i)
  have hJD : ∀ i, J i ⊆ D i := by
    rintro i _ ⟨x, hx, rfl⟩
    exact (hq i).bijOn.mapsTo hx.1
  have hJ'D' : ∀ i, J' i ⊆ D' i := by
    rintro i _ ⟨x, hx, rfl⟩
    exact (hq' i).bijOn.mapsTo hx.1
  have hRDi : ∀ i, R ∩ D i = J i := holed_disk_inter_eq hDS hJD hdis
  have hR'D'i : ∀ i, R' ∩ D' i = J' i := holed_disk_inter_eq hD'S' hJ'D' hdis'
  have hRc : IsClosed R := by
    by_cases hne : Nonempty ι
    · exact hS.isClosed_holed_disk_family hq hDS hdis (Classical.choice hne)
    · let _ : IsEmpty ι := ⟨fun i => hne ⟨i⟩⟩
      simpa [R] using hS.isPolyhedron.isClosed
  have hR'c : IsClosed R' := by
    by_cases hne : Nonempty ι
    · exact hS'.isClosed_holed_disk_family hq' hD'S' hdis' (Classical.choice hne)
    · let _ : IsEmpty ι := ⟨fun i => hne ⟨i⟩⟩
      simpa [R'] using hS'.isPolyhedron.isClosed
  have hfJ : ∀ i, f i '' J i = J' i := by
    intro i
    have h := IsPLHomeomorphOn.image_stdSimplexBoundary_congr
      (m := 1) ((hq i).trans (hf i)) (hq' i)
    simpa only [image_comp] using h
  have hbase : ∀ i, EqOn G₀ (f i) (R ∩ D i) := by
    intro i
    rw [hRDi i]
    exact hmatch i
  have hbaseMeet : ∀ i, G₀ '' (R ∩ D i) = R' ∩ D' i := by
    intro i
    rw [hRDi i, hR'D'i i, (hmatch i).image_eq, hfJ i]
  have hcompat : ∀ i j, EqOn (f i) (f j) (D i ∩ D j) := by
    intro i j
    by_cases hij : i = j
    · subst j
      exact fun _ _ => rfl
    · exact fun _ hx => (disjoint_left.mp (hdis hij) hx.1 hx.2).elim
  have hmeet : ∀ i j, f i '' (D i ∩ D j) = D' i ∩ D' j := by
    intro i j
    by_cases hij : i = j
    · subst j
      simpa only [inter_self] using (hf i).image_eq
    · rw [(hdis hij).inter_eq, image_empty, (hdis' hij).inter_eq]
  obtain ⟨G, hG, hGR, hGD⟩ := exists_isPLHomeomorphOn_union_of_locallyFinite_pieces
    hRc hR'c (fun i => (IsPLBall.isPolyhedron ⟨q i, hq i⟩).isClosed)
    (fun i => (IsPLBall.isPolyhedron ⟨q' i, hq' i⟩).isClosed)
    hG₀ hf hbase hbaseMeet hcompat hmeet (holed_disk_cover hDS) (holed_disk_cover hD'S')
    (fun _ _ => ⟨univ, Filter.univ_mem, Set.toFinite _⟩)
    (fun _ _ => ⟨univ, Filter.univ_mem, Set.toFinite _⟩)
  exact ⟨G, hG, hGR, fun i => (hGD i).1⟩

theorem IsPLSphere.exists_isPLHomeomorphOn_disk_family_eqOn_circle
    {ι : Type*} [Finite ι] {S : Set E} {S' : Set F}
    (hS : IsPLSphere 2 S) (hS' : IsPLSphere 2 S')
    {D : ι → Set E} {D' : ι → Set F}
    {q : ι → (Fin 3 → ℝ) → E} {q' : ι → (Fin 3 → ℝ) → F}
    (hq : ∀ i, IsPLHomeomorphOn (q i) (Convexity.StdSimplex.coordinateSet ℝ (Fin 3)) (D i))
    (hq' : ∀ i, IsPLHomeomorphOn (q' i) (Convexity.StdSimplex.coordinateSet ℝ (Fin 3)) (D' i))
    (hDS : ∀ i, D i ⊆ S) (hD'S' : ∀ i, D' i ⊆ S')
    (hdis : Pairwise fun i j => Disjoint (D i) (D j))
    (hdis' : Pairwise fun i j => Disjoint (D' i) (D' j))
    (i₀ : ι) {φ : E → F}
    (hφ : IsPLHomeomorphOn φ (q i₀ '' stdSimplexBoundary 2) (q' i₀ '' stdSimplexBoundary 2)) :
    ∃ G : E → F, IsPLHomeomorphOn G S S' ∧
      (∀ i, G '' D i = D' i) ∧ EqOn G φ (q i₀ '' stdSimplexBoundary 2) := by
  obtain ⟨G₀, hG₀, hG₀φ, hG₀J, -⟩ :=
    hS.exists_isPLHomeomorphOn_holed hS' hq hq' hDS hD'S' hdis hdis' i₀ hφ
  have hJD : ∀ i, q i '' stdSimplexBoundary 2 ⊆ D i := by
    rintro i _ ⟨x, hx, rfl⟩
    exact (hq i).bijOn.mapsTo hx.1
  have hJR : ∀ i, q i '' stdSimplexBoundary 2 ⊆
      S \ ⋃ j, (D j \ q j '' stdSimplexBoundary 2) := fun i =>
    (holed_disk_inter_eq hDS hJD hdis i).symm.subset.trans inter_subset_left
  have hG₀Ji : ∀ i, IsPLHomeomorphOn G₀ (q i '' stdSimplexBoundary 2)
      (q' i '' stdSimplexBoundary 2) := by
    intro i
    have h := hG₀.restrict ((hq i).isPLSphere_image_stdSimplexBoundary (n := 1)).isPolyhedron
      (hJR i)
    rwa [hG₀J i] at h
  choose f hf hfeq using fun i =>
    exists_isPLHomeomorphOn_extension_of_stdSimplexBoundary (hq i) (hq' i) (hG₀Ji i)
  obtain ⟨G, hG, hGR, hGD⟩ := hS.exists_isPLHomeomorphOn_glue_holed_disks
    hS' hq hq' hDS hD'S' hdis hdis' hG₀ hf (fun i => (hfeq i).symm)
  exact ⟨G, hG, fun i => (hGD i).image_eq.trans (hf i).image_eq,
    (hGR.mono (hJR i₀)).trans hG₀φ⟩

omit [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F] in
theorem IsPLSphere.exists_disk_family_map_not_isPLCirclePositive
    {ι : Type*} [Finite ι] {S : Set E} (hS : IsPLSphere 2 S)
    {D : ι → Set E} {q : ι → (Fin 3 → ℝ) → E}
    (hq : ∀ i, IsPLHomeomorphOn (q i) (Convexity.StdSimplex.coordinateSet ℝ (Fin 3)) (D i))
    (hDS : ∀ i, D i ⊆ S) (hdis : Pairwise fun i j => Disjoint (D i) (D j)) (i₀ : ι) :
    ∃ G : E → E, IsPLHomeomorphOn G S S ∧ (∀ i, G '' D i = D i) ∧
      ¬ IsPLCirclePositive (q i₀ '' stdSimplexBoundary 2) G := by
  obtain ⟨φ, hφ, hφneg⟩ := exists_not_isPLCirclePositive_of_isPLSphere_one
    ((hq i₀).isPLSphere_image_stdSimplexBoundary (n := 1))
  obtain ⟨G, hG, hGD, hGφ⟩ := hS.exists_isPLHomeomorphOn_disk_family_eqOn_circle
    hS hq hq hDS hDS hdis hdis i₀ hφ
  exact ⟨G, hG, hGD, fun hpos => hφneg (hpos.of_eqOn hGφ.symm)⟩

end DifferentialGeometry.Topology.PiecewiseLinear
