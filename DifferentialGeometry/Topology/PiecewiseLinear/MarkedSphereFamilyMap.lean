/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.Topology.PiecewiseLinear.HoledSphereClosed
import DifferentialGeometry.Topology.PiecewiseLinear.LocallyFinitePLHomeomorphGluing
import DifferentialGeometry.Topology.PiecewiseLinear.BallPairRelativeGluing

open Set Topology

namespace DifferentialGeometry.Topology.PiecewiseLinear

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F]
  [FiniteDimensional ℝ F]

open Classical in
theorem IsPLSphere.exists_isPLHomeomorphOn_disk_family
    {ι : Type*} [Finite ι] {S : Set E} {S' : Set F}
    (hS : IsPLSphere 2 S) (hS' : IsPLSphere 2 S')
    {D : ι → Set E} {D' : ι → Set F}
    {q : ι → (Fin 3 → ℝ) → E} {q' : ι → (Fin 3 → ℝ) → F}
    (hq : ∀ i, IsPLHomeomorphOn (q i) (Convexity.StdSimplex.coordinateSet ℝ (Fin 3)) (D i))
    (hq' : ∀ i, IsPLHomeomorphOn (q' i) (Convexity.StdSimplex.coordinateSet ℝ (Fin 3)) (D' i))
    (hDS : ∀ i, D i ⊆ S) (hD'S' : ∀ i, D' i ⊆ S')
    (hdis : Pairwise fun i j => Disjoint (D i) (D j))
    (hdis' : Pairwise fun i j => Disjoint (D' i) (D' j))
    (i₀ : ι) :
    ∃ G : E → F, IsPLHomeomorphOn G S S' ∧ ∀ i, G '' D i = D' i := by
  classical
  let J : ι → Set E := fun i => q i '' stdSimplexBoundary 2
  let J' : ι → Set F := fun i => q' i '' stdSimplexBoundary 2
  let R : Set E := S \ ⋃ i, (D i \ J i)
  let R' : Set F := S' \ ⋃ i, (D' i \ J' i)
  have hJsub : ∀ i, J i ⊆ D i := by
    intro i
    rintro _ ⟨z, hz, rfl⟩
    exact (hq i).bijOn.mapsTo hz.1
  have hJ'sub : ∀ i, J' i ⊆ D' i := by
    intro i
    rintro _ ⟨z, hz, rfl⟩
    exact (hq' i).bijOn.mapsTo hz.1
  have hJpoly : ∀ i, IsPolyhedron (J i) := fun i =>
    ((hq i).isPLSphere_image_stdSimplexBoundary (n := 1)).isPolyhedron
  have hJ'spoly : ∀ i, IsPolyhedron (J' i) := fun i =>
    ((hq' i).isPLSphere_image_stdSimplexBoundary (n := 1)).isPolyhedron
  have hJR : ∀ i, J i ⊆ R := by
    intro i x hx
    refine ⟨hDS i (hJsub i hx), ?_⟩
    intro hxhole
    obtain ⟨j, hxj⟩ := mem_iUnion.mp hxhole
    by_cases hij : j = i
    · subst j
      exact hxj.2 hx
    · exact disjoint_left.mp (hdis hij) hxj.1 (hJsub i hx)
  have hJ'R' : ∀ i, J' i ⊆ R' := by
    intro i x hx
    refine ⟨hD'S' i (hJ'sub i hx), ?_⟩
    intro hxhole
    obtain ⟨j, hxj⟩ := mem_iUnion.mp hxhole
    by_cases hij : j = i
    · subst j
      exact hxj.2 hx
    · exact disjoint_left.mp (hdis' hij) hxj.1 (hJ'sub i hx)
  have hRDi : ∀ i, R ∩ D i = J i := by
    intro i
    apply Subset.antisymm
    · intro x hx
      by_contra hxJ
      exact hx.1.2 (mem_iUnion.mpr ⟨i, hx.2, hxJ⟩)
    · intro x hx
      exact ⟨hJR i hx, hJsub i hx⟩
  have hR'D'i : ∀ i, R' ∩ D' i = J' i := by
    intro i
    apply Subset.antisymm
    · intro x hx
      by_contra hxJ
      exact hx.1.2 (mem_iUnion.mpr ⟨i, hx.2, hxJ⟩)
    · intro x hx
      exact ⟨hJ'R' i hx, hJ'sub i hx⟩
  have hRclosed : IsClosed R := hS.isClosed_holed_disk_family hq hDS hdis i₀
  have hR'closed : IsClosed R' := hS'.isClosed_holed_disk_family hq' hD'S' hdis' i₀
  obtain ⟨φ, hφ⟩ :=
    (hq i₀).isPLSphere_image_stdSimplexBoundary.exists_isPLHomeomorphOn
      (hq' i₀).isPLSphere_image_stdSimplexBoundary
  obtain ⟨G₀, hG₀, -, hG₀J, -⟩ :=
    hS.exists_isPLHomeomorphOn_holed hS' hq hq' hDS hD'S' hdis hdis' i₀ hφ
  have hG₀Ji : ∀ i, IsPLHomeomorphOn G₀ (J i) (J' i) := by
    intro i
    have h := hG₀.restrict (hJpoly i) (hJR i)
    rwa [hG₀J i] at h
  choose f hf hfeq using fun i =>
    exists_isPLHomeomorphOn_extension_of_stdSimplexBoundary (hq i) (hq' i) (hG₀Ji i)
  have hbase : ∀ i, EqOn G₀ (f i) (R ∩ D i) := by
    intro i
    rw [hRDi i]
    exact (hfeq i).symm
  have hbaseMeet : ∀ i, G₀ '' (R ∩ D i) = R' ∩ D' i := by
    intro i
    rw [hRDi i, hR'D'i i]
    exact hG₀J i
  have hcompat : ∀ i j, EqOn (f i) (f j) (D i ∩ D j) := by
    intro i j
    by_cases hij : i = j
    · subst j
      exact fun _ _ => rfl
    · intro x hx
      exact (disjoint_left.mp (hdis hij) hx.1 hx.2).elim
  have hmeet : ∀ i j, f i '' (D i ∩ D j) = D' i ∩ D' j := by
    intro i j
    by_cases hij : i = j
    · subst j
      simpa only [inter_self] using (hf i).bijOn.image_eq
    · rw [Set.disjoint_iff_inter_eq_empty.mp (hdis hij), image_empty,
        Set.disjoint_iff_inter_eq_empty.mp (hdis' hij)]
  have hcover : R ∪ ⋃ i, D i = S := by
    apply Subset.antisymm
    · exact union_subset (fun _ hx => hx.1) (iUnion_subset hDS)
    · intro x hx
      by_cases hD : ∃ i, x ∈ D i
      · exact Or.inr (mem_iUnion.mpr hD)
      · refine Or.inl ⟨hx, ?_⟩
        intro hxhole
        obtain ⟨i, hxi⟩ := mem_iUnion.mp hxhole
        exact hD ⟨i, hxi.1⟩
  have hcover' : R' ∪ ⋃ i, D' i = S' := by
    apply Subset.antisymm
    · exact union_subset (fun _ hx => hx.1) (iUnion_subset hD'S')
    · intro x hx
      by_cases hD : ∃ i, x ∈ D' i
      · exact Or.inr (mem_iUnion.mpr hD)
      · refine Or.inl ⟨hx, ?_⟩
        intro hxhole
        obtain ⟨i, hxi⟩ := mem_iUnion.mp hxhole
        exact hD ⟨i, hxi.1⟩
  have hlocal : ∀ x ∈ S, ∃ V ∈ 𝓝 x, {i | (D i ∩ V).Nonempty}.Finite := by
    intro x _
    exact ⟨univ, Filter.univ_mem, Set.toFinite _⟩
  have hlocal' : ∀ x ∈ S', ∃ V ∈ 𝓝 x, {i | (D' i ∩ V).Nonempty}.Finite := by
    intro x _
    exact ⟨univ, Filter.univ_mem, Set.toFinite _⟩
  obtain ⟨G, hG, -, hGD⟩ :=
    exists_isPLHomeomorphOn_union_of_locallyFinite_pieces
      hRclosed hR'closed (fun i => (IsPLBall.isPolyhedron ⟨q i, hq i⟩).isClosed)
      (fun i => (IsPLBall.isPolyhedron ⟨q' i, hq' i⟩).isClosed)
      hG₀ hf hbase hbaseMeet hcompat hmeet hcover hcover' hlocal hlocal'
  exact ⟨G, hG, fun i => (hGD i).2⟩

end DifferentialGeometry.Topology.PiecewiseLinear
