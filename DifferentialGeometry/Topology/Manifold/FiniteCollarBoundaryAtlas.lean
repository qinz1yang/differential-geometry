import DifferentialGeometry.Topology.OpenPartialHomeomorph.FiniteCollarFrontier
import DifferentialGeometry.Topology.Manifold.EuclideanBoundaryCoordinates
import DifferentialGeometry.Topology.Manifold.SmoothBoundaryAtlas

noncomputable section

open Set Manifold
open scoped Manifold ContDiff

namespace DifferentialGeometry.Topology

private def productBoundaryChart {n : ℕ} {N M : Type*}
    [TopologicalSpace N] [ChartedSpace (EuclideanSpace ℝ (Fin n)) N]
    [IsManifold (𝓡 n) ∞ N]
    [TopologicalSpace M] [ChartedSpace (EuclideanSpace ℝ (Fin (n + 1))) M]
    (e : PartialDiffeomorph ((𝓡 n).prod 𝓘(ℝ)) (𝓡 (n + 1)) (N × ℝ) M ∞)
    (q : N) (positive : Bool) :
    PartialDiffeomorph (𝓡 (n + 1)) (𝓡 (n + 1)) M (EuclideanSpace ℝ (Fin (n + 1))) ∞ :=
  (e.symm.trans (PartialDiffeomorph.prod
    (PartialDiffeomorph.extendedChart (I := 𝓡 n) q)
    (Diffeomorph.refl 𝓘(ℝ) ℝ ∞).toPartialDiffeomorph)).trans
      (signedNormalFirstDiffeomorph n positive).toPartialDiffeomorph

private theorem productBoundaryChart_mem_source {n : ℕ} {N M : Type*}
    [TopologicalSpace N] [ChartedSpace (EuclideanSpace ℝ (Fin n)) N]
    [IsManifold (𝓡 n) ∞ N]
    [TopologicalSpace M] [ChartedSpace (EuclideanSpace ℝ (Fin (n + 1))) M]
    (e : PartialDiffeomorph ((𝓡 n).prod 𝓘(ℝ)) (𝓡 (n + 1)) (N × ℝ) M ∞)
    (q : N) (positive : Bool) (hq : (q, (0 : ℝ)) ∈ e.source) :
    e (q, 0) ∈ (productBoundaryChart e q positive).source := by
  change ((e (q, 0) ∈ e.target ∧
    (e.symm (e (q, 0))).1 ∈ (extChartAt (𝓡 n) q).source ∧ True) ∧ True)
  refine ⟨⟨e.map_source hq, ?_, trivial⟩, trivial⟩
  exact (congrArg Prod.fst (e.left_inv hq)).symm ▸ mem_extChartAt_source q

private theorem productBoundaryChart_zero {n : ℕ} {N M : Type*}
    [TopologicalSpace N] [ChartedSpace (EuclideanSpace ℝ (Fin n)) N]
    [IsManifold (𝓡 n) ∞ N]
    [TopologicalSpace M] [ChartedSpace (EuclideanSpace ℝ (Fin (n + 1))) M]
    (e : PartialDiffeomorph ((𝓡 n).prod 𝓘(ℝ)) (𝓡 (n + 1)) (N × ℝ) M ∞)
    (q : N) (positive : Bool) (y : M) :
    productBoundaryChart e q positive y 0 =
      if positive then (e.symm y).2 else -(e.symm y).2 := by
  change signedNormalFirstEquiv n positive (_, (e.symm y).2) 0 = _
  exact signedNormalFirstEquiv_zero n positive _

private theorem exists_boundaryChart_of_cylinder_side {n : ℕ} {N M : Type*}
    [TopologicalSpace N] [ChartedSpace (EuclideanSpace ℝ (Fin n)) N]
    [IsManifold (𝓡 n) ∞ N]
    [TopologicalSpace M] [ChartedSpace (EuclideanSpace ℝ (Fin (n + 1))) M]
    (e : PartialDiffeomorph ((𝓡 n).prod 𝓘(ℝ)) (𝓡 (n + 1)) (N × ℝ) M ∞)
    {r : ℝ} (hr : 0 < r) (hsource : univ ×ˢ Ioo (-r) r ⊆ e.source)
    {K : Set M} (positive : Bool)
    (hside : ∀ q t, t ∈ Ioo (-r) r →
      (e (q, t) ∈ K ↔ 0 ≤ if positive then t else -t))
    (q : N) :
    ∃ φ : PartialDiffeomorph (𝓡 (n + 1)) (𝓡 (n + 1))
        M (EuclideanSpace ℝ (Fin (n + 1))) ∞,
      e (q, 0) ∈ φ.source ∧ (∀ y ∈ φ.source, y ∈ K ↔ 0 ≤ φ y 0) ∧
      φ (e (q, 0)) 0 = 0 := by
  let V := e '' (univ ×ˢ Ioo (-r) r)
  have hVo : IsOpen V := e.toOpenPartialHomeomorph.isOpen_image_of_subset_source
    (isOpen_univ.prod isOpen_Ioo) hsource
  let φ := PartialDiffeomorph.restrict (productBoundaryChart e q positive) V hVo
  have hqsource : (q, (0 : ℝ)) ∈ e.source :=
    hsource ⟨mem_univ _, neg_lt_zero.mpr hr, hr⟩
  refine ⟨φ, ⟨productBoundaryChart_mem_source e q positive hqsource,
    (q, 0), ⟨mem_univ _, neg_lt_zero.mpr hr, hr⟩, rfl⟩, ?_, ?_⟩
  · intro y hy
    obtain ⟨⟨z, t⟩, ⟨_, ht⟩, hzt⟩ := hy.2
    have hinv : e.symm y = (z, t) := hzt ▸ e.left_inv (hsource ⟨mem_univ _, ht⟩)
    have hcoord : φ y 0 = if positive then t else -t := by
      change productBoundaryChart e q positive y 0 = _
      rw [productBoundaryChart_zero]
      exact congrArg (fun p : N × ℝ => if positive then p.2 else -p.2) hinv
    rw [hcoord, ← hzt]
    exact hside z t ht
  · change productBoundaryChart e q positive (e (q, 0)) 0 = _
    rw [productBoundaryChart_zero]
    have heq := congrArg (fun p : N × ℝ => if positive then p.2 else -p.2)
      (e.left_inv hqsource)
    exact heq.trans (by cases positive <;> simp)

theorem exists_smoothBoundaryAtlas_of_finite_disjoint_collars
    {n : ℕ} {N M ι : Type*}
    [TopologicalSpace N] [ChartedSpace (EuclideanSpace ℝ (Fin n)) N]
    [IsManifold (𝓡 n) ∞ N] [CompactSpace N] [PreconnectedSpace N]
    [TopologicalSpace M] [ChartedSpace (EuclideanSpace ℝ (Fin (n + 1))) M]
    [IsManifold (𝓡 (n + 1)) ∞ M] [T2Space M] [Finite ι]
    (e : ι → PartialDiffeomorph ((𝓡 n).prod 𝓘(ℝ)) (𝓡 (n + 1)) (N × ℝ) M ∞)
    (hzero : ∀ i q, (q, (0 : ℝ)) ∈ (e i).source)
    (hdisjoint : Pairwise (fun i j => Disjoint
      (range (fun q : N => e i (q, 0))) (range (fun q : N => e j (q, 0)))))
    {K : Set M} (hregular : closure (interior K) = K)
    (hfrontier : frontier K ⊆ ⋃ i, range (fun q : N => e i (q, 0))) :
    ∃ C : SmoothBoundaryAtlas (𝓡 (n + 1)) (n + 1) K,
      ∀ x : K, C.ambientChart x x.val 0 = 0 ↔ x.val ∈ frontier K := by
  classical
  have hcharts : ∀ x : K,
      ∃ φ : PartialDiffeomorph (𝓡 (n + 1)) (𝓡 (n + 1))
          M (EuclideanSpace ℝ (Fin (n + 1))) ∞,
        x.val ∈ φ.source ∧ (∀ y ∈ φ.source, y ∈ K ↔ 0 ≤ φ y 0) ∧
        (φ x.val 0 = 0 ↔ x.val ∈ frontier K) := by
    intro x
    by_cases hx : x.val ∈ interior K
    · obtain ⟨φ, hxφ, hφK, hpos⟩ := exists_positiveChart_of_mem_open (n := n + 1) isOpen_interior hx
      refine ⟨φ, hxφ, ?_, ?_⟩
      · exact fun y hy => iff_of_true (interior_subset (hφK hy)) (hpos y hy).le
      · exact iff_of_false (ne_of_gt (hpos x.val hxφ)) (fun hxf => hxf.2 hx)
    · have hxf : x.val ∈ frontier K := ⟨subset_closure x.property, hx⟩
      obtain ⟨i, q, hq⟩ := mem_iUnion.mp (hfrontier hxf)
      obtain ⟨r, σ, hr, hσ, hsource, hside, _⟩ :=
        (frontier_eq_iUnion_of_finite_disjoint_collars
          (fun i => (e i).toOpenPartialHomeomorph) hzero hdisjoint hregular hfrontier).2
          i ⟨x.val, ⟨q, hq⟩, hxf⟩
      have hex : ∃ φ : PartialDiffeomorph (𝓡 (n + 1)) (𝓡 (n + 1))
          M (EuclideanSpace ℝ (Fin (n + 1))) ∞,
          e i (q, 0) ∈ φ.source ∧ (∀ y ∈ φ.source, y ∈ K ↔ 0 ≤ φ y 0) ∧
          φ (e i (q, 0)) 0 = 0 := by
        rcases hσ with rfl | rfl
        · refine exists_boundaryChart_of_cylinder_side (e i) hr hsource false ?_ q
          intro z t ht
          have h := hside z t ht
          change e i (z, t) ∈ K ↔ 1 * t ≤ 0 at h
          simpa only [one_mul, Bool.false_eq_true, ↓reduceIte, neg_nonneg] using h
        · refine exists_boundaryChart_of_cylinder_side (e i) hr hsource true ?_ q
          intro z t ht
          have h := hside z t ht
          change e i (z, t) ∈ K ↔ -1 * t ≤ 0 at h
          simpa only [neg_one_mul, ↓reduceIte, neg_nonpos] using h
      obtain ⟨φ, hxφ, hφ, hzφ⟩ := hex
      exact ⟨φ, hq ▸ hxφ, hφ, iff_of_true (hq ▸ hzφ) hxf⟩
  choose φ hmem hiff hz using hcharts
  exact ⟨⟨φ, hmem, hiff⟩, hz⟩

end DifferentialGeometry.Topology
