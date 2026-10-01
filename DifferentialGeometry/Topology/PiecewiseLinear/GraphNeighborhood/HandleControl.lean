import DifferentialGeometry.Topology.PiecewiseLinear.PseudoCell.Splitting

open Set Topology

namespace DifferentialGeometry.Topology.PiecewiseLinear

section Assembly

variable {K : Geometry.SimplicialComplex ℝ (EuclideanSpace ℝ (Fin 3))}
  {N N' : Set (EuclideanSpace ℝ (Fin 3))}
  {C : EuclideanSpace ℝ (Fin 3) → Set (EuclideanSpace ℝ (Fin 3))}
  {D Dbd : Finset (EuclideanSpace ℝ (Fin 3)) → Set (EuclideanSpace ℝ (Fin 3))}
  {h : EuclideanSpace ℝ (Fin 3) → EuclideanSpace ℝ (Fin 3)}

theorem IsTube.exists_handleDecomposition_diam_lt (ht : IsTube K N C D Dbd h N') {δ : ℝ}
    (hsmall : ∀ v ∈ K.vertices, ∀ x ∈ C v, ∀ y ∈ C v, dist (h x) (h y) < δ) :
    ∃ (Ec Eint Ebd : Finset (EuclideanSpace ℝ (Fin 3)) → Set (EuclideanSpace ℝ (Fin 3)))
      (Cpp : EuclideanSpace ℝ (Fin 3) → Set (EuclideanSpace ℝ (Fin 3))),
      IsHandleDecompositionOfTube K N C D Dbd h N' Ec Eint Ebd Cpp ∧
      ∀ v ∈ K.vertices, ∀ x ∈ Cpp v, ∀ y ∈ Cpp v, dist x y < δ := by
  have hcont : ContinuousOn h N :=
    continuousOn_iff_continuous_domRestrict.mpr ht.isEmbedding.continuous
  have key : ∀ v : EuclideanSpace ℝ (Fin 3), ∃ V : Set (EuclideanSpace ℝ (Fin 3)),
      v ∈ K.vertices → V ∈ nhdsSet (h '' C v) ∧ ∀ x ∈ V, ∀ y ∈ V, dist x y < δ := by
    intro v
    by_cases hv : v ∈ K.vertices
    · have hCN : C v ⊆ N := by
        rw [ht.unionEq]
        exact subset_biUnion_of_mem (u := C) hv
      have hvC : v ∈ C v := by
        have hmem : v ∈ C v ∩ K.vertices := by
          rw [ht.dualVertex hv]
          exact mem_singleton v
        exact hmem.1
      have hSc : IsCompact (h '' C v) :=
        (ht.dualBall v hv).isPolyhedron.isCompact.image_of_continuousOn (hcont.mono hCN)
      have hne : (h '' C v).Nonempty := ⟨h v, mem_image_of_mem h hvC⟩
      obtain ⟨p, hp, hmax⟩ := (hSc.prod hSc).exists_isMaxOn (hne.prod hne)
        (continuous_dist.continuousOn (s := (h '' C v) ×ˢ (h '' C v)))
      obtain ⟨x₀, hx₀, hpx⟩ := (mem_prod.mp hp).1
      obtain ⟨y₀, hy₀, hpy⟩ := (mem_prod.mp hp).2
      have hm : dist p.1 p.2 < δ := by
        rw [← hpx, ← hpy]
        exact hsmall v hv x₀ hx₀ y₀ hy₀
      have hrpos : 0 < (δ - dist p.1 p.2) / 3 := by linarith
      refine ⟨Metric.thickening ((δ - dist p.1 p.2) / 3) (h '' C v), fun _ => ⟨?_, ?_⟩⟩
      · exact Metric.isOpen_thickening.mem_nhdsSet.mpr (Metric.self_subset_thickening hrpos _)
      · intro x hx y hy
        obtain ⟨s, hs, hxs⟩ := Metric.mem_thickening_iff.mp hx
        obtain ⟨s', hs', hys⟩ := Metric.mem_thickening_iff.mp hy
        have hss' : dist s s' ≤ dist p.1 p.2 :=
          isMaxOn_iff.mp hmax (s, s') (mk_mem_prod hs hs')
        have h4 := dist_triangle4 x s s' y
        rw [dist_comm s' y] at h4
        linarith
    · exact ⟨univ, fun hv' => absurd hv' hv⟩
  choose V hV using key
  obtain ⟨Ec, Eint, Ebd, Cpp, hd, hsub⟩ :=
    ht.exists_handleDecomposition_subset V fun v hv => (hV v hv).1
  exact ⟨Ec, Eint, Ebd, Cpp, hd,
    fun v hv x hx y hy => (hV v hv).2 x (hsub v hv hx) y (hsub v hv hy)⟩

end Assembly

end DifferentialGeometry.Topology.PiecewiseLinear
