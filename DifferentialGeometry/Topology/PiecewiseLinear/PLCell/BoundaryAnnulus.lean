import DifferentialGeometry.Topology.PiecewiseLinear.Section34CapDeletion
import DifferentialGeometry.Topology.PiecewiseLinear.SurfaceCircleBicollar
import DifferentialGeometry.Topology.PiecewiseLinear.AnnulusBoundary
import DifferentialGeometry.Topology.PiecewiseLinear.MobiusEmbedding

open Set Topology

namespace DifferentialGeometry.Topology.PiecewiseLinear

open Classical in
theorem IsPLCellOn.exists_boundary_annular_neighborhood {M : Type*}
    [TopologicalSpace M] [T2Space M] [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
    {S B J O : Set M} (hS : IsPLCellOn 3 S B)
    (hJ : IsPolyhedralSphere (n := 3) 1 J) (hJB : J ⊆ B) (hO : O ∈ 𝓝ˢ[B] J) :
    let _ : DecidableEq (EuclideanSpace ℝ (Fin 3)) := Classical.decEq _
    ∃ (Q C : Set (EuclideanSpace ℝ (Fin 3))) (v : EuclideanSpace ℝ (Fin 3) → M)
      (A : Geometry.SimplicialComplex ℝ (EuclideanSpace ℝ (Fin 3)))
      (ρ : EuclideanSpace ℝ (Fin 3) × ℝ → EuclideanSpace ℝ (Fin 3)) (V : Set M),
      ∃ hAfin : A.faces.Finite, let _ : Finite A.faces := hAfin.to_subtype
      IsPLBall 3 Q ∧ IsPLHomeomorphInto 3 v Q ∧ v '' Q = S ∧ v '' frontier Q = B ∧
      IsPLSphere 1 C ∧ v '' C = J ∧ C ⊆ A.space ∧
      IsCombinatorialManifoldWithBoundary 2 A ∧ IsOrientable 2 A ∧
      A.space ⊆ frontier Q ∧ IsPLHomeomorphOn ρ (C ×ˢ Icc (-1 : ℝ) 1) A.space ∧
      (∀ x ∈ C, ρ (x, 0) = x) ∧ Disjoint C (boundaryComplex 2 A).space ∧
      v '' A.space ⊆ O ∧ IsOpen V ∧ J ⊆ V ∧ V ∩ B = V ∩ (v '' A.space) := by
  let _ : DecidableEq (EuclideanSpace ℝ (Fin 3)) := Classical.decEq _
  obtain ⟨Q, r, v, hr, hv, hSimage, hB⟩ := hS
  have hQ : IsPLBall 3 Q := ⟨r, hr⟩
  have hfront : frontier Q ⊆ Q := hQ.isPolyhedron.isClosed.frontier_subset
  rw [hr.image_stdSimplexBoundary_eq_frontier] at hB
  have hJP : J ⊆ v '' Q := hJB.trans (hB ▸ image_mono hfront)
  let C := Function.invFunOn v Q '' J
  have hC : IsPLSphere 1 C := hv.isPLSphere_invFunOn_image hJ hJP
  have hCS : C ⊆ frontier Q := by
    rintro _ ⟨x, hx, rfl⟩
    obtain ⟨y, hy, rfl⟩ : x ∈ v '' frontier Q := hB ▸ hJB hx
    rw [hv.injOn.leftInvOn_invFunOn (hfront hy)]
    exact hy
  have hvC : v '' C = J := by
    rw [image_image]
    exact (image_congr fun x hx => hv.injOn.bijOn_image.invOn_invFunOn.2 (hJP hx)).trans
      (image_id' J)
  have hpre := (hv.continuousOn.mono hfront).preimage_mem_nhdsSetWithin hO
  have hfull : frontier Q ∩ v ⁻¹' B = frontier Q :=
    inter_eq_left.mpr fun x hx => hB.symm ▸ mem_image_of_mem v hx
  rw [hfull] at hpre
  have hcenter : C ⊆ frontier Q ∩ v ⁻¹' J :=
    fun x hx => ⟨hCS hx, hvC ▸ mem_image_of_mem v hx⟩
  have hnear : v ⁻¹' O ∈ 𝓝ˢ[frontier Q] C := (nhdsSetWithin_mono_left hcenter) hpre
  obtain ⟨W, ρ, -, hWS, hWO, hWnear, hρ, hρ₀⟩ :=
    hQ.isPLSphere_frontier.exists_bicollar_of_isPLSphere_one hC hCS hnear
  obtain ⟨A, hAfin, hA, -, hAW, hAbd⟩ :=
    hρ.exists_annulus_complex hC (by norm_num : (-1 : ℝ) < 1)
  let _ : Finite A.faces := hAfin.to_subtype
  have hAS : A.space ⊆ frontier Q := hAW.subset.trans hWS
  have hρA : IsPLHomeomorphOn ρ (C ×ˢ Icc (-1 : ℝ) 1) A.space := hAW.symm ▸ hρ
  have hCA : C ⊆ A.space :=
    fun x hx => hρ₀ x hx ▸ hρA.bijOn.mapsTo ⟨hx, by norm_num⟩
  obtain ⟨K, hKfin, hKS⟩ := hQ.isPLSphere_frontier.isPolyhedron.exists_simplicialComplex
  let _ : Finite K.faces := hKfin.to_subtype
  have hKSphere : IsPLSphere 2 K.space := hKS.symm ▸ hQ.isPLSphere_frontier
  have hor : IsOrientable 2 A :=
    (isOrientable_of_isPLSphere hKSphere).of_space_subset K A (hAS.trans hKS.symm.subset)
      hKSphere.isCombinatorialManifold.isCombinatorialManifoldWithBoundary hA
  have hdis : Disjoint C (boundaryComplex 2 A).space := by
    rw [hAbd]
    refine disjoint_left.mpr ?_
    rintro x hx ⟨⟨y, t⟩, ⟨hy, ht⟩, heq⟩
    simp only [mem_insert_iff, mem_singleton_iff] at ht
    have htI : t ∈ Icc (-1 : ℝ) 1 := by
      rcases ht with ht | ht <;> rw [ht] <;> norm_num
    have heq' := hρ.bijOn.injOn (show (y, t) ∈ C ×ˢ Icc (-1 : ℝ) 1 from
      ⟨hy, htI⟩)
      (show (x, (0 : ℝ)) ∈ C ×ˢ Icc (-1 : ℝ) 1 from ⟨hx, by norm_num⟩)
      (heq.trans (hρ₀ x hx).symm)
    have ht0 : t = 0 := congrArg Prod.snd heq'
    rcases ht with ht | ht <;> rw [ht] at ht0 <;> norm_num at ht0
  obtain ⟨D, hD, hCD, hDW⟩ := mem_nhdsSetWithin.mp hWnear
  have hclosed : IsClosed (v '' (frontier Q \ D)) :=
    ((hQ.isPLSphere_frontier.isPolyhedron.isCompact.diff hD).image_of_continuousOn
      (hv.continuousOn.mono (sdiff_subset.trans hfront))).isClosed
  let V := (v '' (frontier Q \ D))ᶜ
  have hJV : J ⊆ V := by
    intro x hx
    obtain ⟨y, hy, rfl⟩ := hvC.symm.subset hx
    rintro ⟨z, hz, hzy⟩
    have heq := hv.injOn (hfront hz.1) (hfront (hCS hy)) hzy
    exact hz.2 (heq.symm ▸ hCD hy)
  refine ⟨Q, C, v, A, ρ, V, hAfin, hQ, hv, hSimage.symm, hB.symm, hC, hvC, hCA,
    hA, hor, hAS, hρA, hρ₀, hdis, ?_, hclosed.isOpen_compl, hJV, ?_⟩
  · rintro _ ⟨x, hx, rfl⟩
    exact hWO (hAW.subset hx)
  · apply Subset.antisymm
    · rintro x ⟨hxV, hxB⟩
      obtain ⟨y, hy, rfl⟩ := hB.subset hxB
      have hyD : y ∈ D := by
        by_contra hn
        exact hxV ⟨y, ⟨hy, hn⟩, rfl⟩
      exact ⟨hxV, y, hAW.symm.subset (hDW ⟨hyD, hy⟩), rfl⟩
    · rintro x ⟨hxV, y, hy, rfl⟩
      exact ⟨hxV, hB.symm ▸ mem_image_of_mem v (hAS hy)⟩

end DifferentialGeometry.Topology.PiecewiseLinear
