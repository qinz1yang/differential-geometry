import DifferentialGeometry.Topology.Manifold.CylinderCollar.AttachedSlab
import DifferentialGeometry.Topology.Manifold.FiniteCollarBoundaryAtlas
import DifferentialGeometry.Topology.Manifold.SmoothBoundaryAtlas.Inclusion

set_option autoImplicit false
noncomputable section
open Set Manifold
open scoped Manifold ContDiff Topology

namespace DifferentialGeometry.Topology

universe u v w

theorem exists_isManifold_of_finite_half_cylinders
    {n : ℕ} {N : Type u} {M : Type v} {ι : Type w}
    [TopologicalSpace N] [ChartedSpace (EuclideanSpace ℝ (Fin n)) N]
    [IsManifold (𝓡 n) ∞ N] [CompactSpace N] [PreconnectedSpace N]
    [TopologicalSpace M] [ChartedSpace (EuclideanSpace ℝ (Fin (n + 1))) M]
    [IsManifold (𝓡 (n + 1)) ∞ M] [T2Space M] [Finite ι]
    (Θ : ι → N × ℝ → M)
    (P : ι → PartialDiffeomorph ((𝓡 n).prod 𝓘(ℝ)) (𝓡 (n + 1)) (N × ℝ) M ∞)
    (hsource : ∀ i, univ ×ˢ Icc (0 : ℝ) 1 ⊆ (P i).source)
    (hfirst : ∀ i q t, t ∈ Icc (0 : ℝ) 1 → Θ i (q, t) = P i (q, t))
    (hdisjoint : Pairwise (fun i j => Disjoint
      (Θ i '' (univ ×ˢ Ici (0 : ℝ))) (Θ j '' (univ ×ˢ Ici (0 : ℝ)))))
    {K : Set M} (hregular : closure (interior K) = K)
    (hfrontier : frontier K = ⋃ i, range (fun q : N => Θ i (q, 0)))
    (hinter : ∀ i, Θ i '' (univ ×ˢ Ici (0 : ℝ)) ∩ K = range (fun q : N => Θ i (q, 0))) :
    ∃ (charts : ChartedSpace (EuclideanHalfSpace (n + 1)) K)
      (c : ∀ i, SmoothTwoSidedCollar (𝓡 n) (𝓡 (n + 1)) (fun q => Θ i (q, 0))),
      (let _ := charts
       IsManifold (𝓡∂ (n + 1)) ∞ K ∧
         IsSmoothEmbedding (𝓡∂ (n + 1)) (𝓡 (n + 1)) ∞ (Subtype.val : K → M) ∧
         (∀ x : K, (𝓡∂ (n + 1)).IsBoundaryPoint x ↔ x.val ∈ frontier K) ∧
         (∀ x : K, (𝓡∂ (n + 1)).IsInteriorPoint x ↔ x.val ∈ interior K) ∧
         Subtype.val '' ((𝓡∂ (n + 1)).boundary K) = frontier K ∧
         Subtype.val '' ((𝓡∂ (n + 1)).interior K) = interior K) ∧
      ∀ i, (c i).radius < 1 ∧
        (∀ q t, t ∈ Icc (-(c i).radius) (c i).radius → (q, t) ∈ (P i).source) ∧
        (∀ z : N × symmetricOpenInterval (c i).radius,
          (c i).toFun z = P i (z.1, z.2.val)) ∧
        (∀ z : N × symmetricOpenInterval (c i).radius,
          (c i).toFun z ∈ K ↔ z.2.val ≤ 0) ∧
        (∀ z : N × symmetricOpenInterval (c i).radius,
          z.2.val < 0 → (c i).toFun z ∈ interior K) ∧
        ∀ z : N × symmetricOpenInterval (c i).radius,
          0 ≤ z.2.val → (c i).toFun z = Θ i (z.1, z.2.val) := by
  classical
  have hzero (i : ι) (q : N) : Θ i (q, 0) = P i (q, 0) :=
    hfirst i q 0 ⟨le_rfl, zero_le_one⟩
  have hsource₀ (i : ι) (q : N) : (q, (0 : ℝ)) ∈ (P i).source :=
    hsource i ⟨mem_univ _, le_rfl, zero_le_one⟩
  have hcompact (i : ι) : IsCompact (range (fun q : N => Θ i (q, 0))) := by
    have heq : (fun q : N => Θ i (q, 0)) = (fun q : N => P i (q, 0)) := funext (hzero i)
    rw [heq]
    exact isCompact_range ((P i).contMDiffOn_toFun.continuousOn.comp_continuous
      (continuous_id.prodMk continuous_const) (hsource₀ i))
  have hbase (i : ι) : range (fun q : N => Θ i (q, 0)) ⊆ Θ i '' (univ ×ˢ Ici (0 : ℝ)) := by
    rintro x ⟨q, rfl⟩
    exact ⟨(q, (0 : ℝ)), ⟨mem_univ _, by change (0 : ℝ) ≤ 0; exact le_rfl⟩, rfl⟩
  have hbasedisjoint : Pairwise (fun i j => Disjoint
      (range (fun q : N => Θ i (q, 0))) (range (fun q : N => Θ j (q, 0)))) :=
    fun _ _ hij => (hdisjoint hij).mono (hbase _) (hbase _)
  let S : ι → Set M := fun i => ⋃ j ∈ ({i}ᶜ : Set ι), range (fun q : N => Θ j (q, 0))
  have hSclosed (i : ι) : IsClosed (S i) :=
    Set.toFinite {i}ᶜ |>.isClosed_biUnion (fun j _ => (hcompact j).isClosed)
  have hsplit (i : ι) : frontier K = range (fun q : N => Θ i (q, 0)) ∪ S i := by
    rw [hfrontier]
    ext x
    simp only [S, mem_iUnion, mem_compl_iff, mem_singleton_iff, mem_union, exists_prop]
    constructor
    · rintro ⟨j, hj⟩
      by_cases hji : j = i
      · exact Or.inl (hji ▸ hj)
      · exact Or.inr ⟨j, hji, hj⟩
    · rintro (hi | ⟨j, _, hj⟩)
      · exact ⟨i, hi⟩
      · exact ⟨j, hj⟩
  have hsplitdisjoint (i : ι) : Disjoint (range (fun q : N => Θ i (q, 0))) (S i) := by
    rw [disjoint_left]
    intro x hx hxs
    obtain ⟨j, hji, hxj⟩ := mem_iUnion₂.mp hxs
    exact disjoint_left.mp (hbasedisjoint (Ne.symm hji)) hx hxj
  have hcollars (i : ι) := exists_smoothTwoSidedCollar_of_half_cylinder_first_slab
    (P i) (hsource i) (Θ i) (hfirst i) hregular (hSclosed i)
      (hsplit i) (hsplitdisjoint i) (hinter i)
  choose c hrad hsrc hmap hK hnegative hΘ using hcollars
  have hdisjointP : Pairwise (fun i j => Disjoint
      (range (fun q : N => P i (q, 0))) (range (fun q : N => P j (q, 0)))) := by
    simpa only [← hzero] using hbasedisjoint
  have hfrontierP : frontier K ⊆ ⋃ i, range (fun q : N => P i (q, 0)) := by
    simpa only [← hzero] using hfrontier.le
  obtain ⟨C, hC⟩ := exists_smoothBoundaryAtlas_of_finite_disjoint_collars
    P hsource₀ hdisjointP hregular hfrontierP
  refine ⟨C.toChartedSpace, c, ?_, fun i => ⟨hrad i, hsrc i, hmap i, hK i, hnegative i, hΘ i⟩⟩
  exact ⟨C.isManifold, C.isSmoothEmbedding_subtype_val,
    C.isBoundaryPoint_iff_mem_frontier hC, C.isInteriorPoint_iff_mem_interior hC,
    C.image_boundary_subtype_val (hregular ▸ isClosed_closure) hC, C.image_interior_subtype_val hC⟩

end DifferentialGeometry.Topology
