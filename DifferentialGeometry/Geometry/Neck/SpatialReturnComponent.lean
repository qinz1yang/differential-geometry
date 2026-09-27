import DifferentialGeometry.Geometry.Neck.SpatialFiniteFrontier
import DifferentialGeometry.Topology.Connected.ComponentFilling

noncomputable section
open Set Manifold
open scoped Manifold ContDiff

namespace DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn

open DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

universe u

theorem exists_spatial_neck_return_component_tolerance :
    ∃ eta : ℝ, 0 < eta ∧ ∀ eps : ℝ, eps ≤ eta →
      ∀ (M : Type u) [TopologicalSpace M] [ChartedSpace ThreeSpace M]
        [IsManifold I3 ∞ M] [T2Space M]
        (g : SmoothRiemannianMetric I3 M) (p : M) (nk : SpatialNeck g eps p)
        (ι : Type*) [Finite ι] (point : ι → M) (neck : ∀ i, SpatialNeck g eps (point i))
        (level : ι → ℝ), (∀ i, |level i| ≤ 4) →
        Pairwise (fun i j => Disjoint (range (fun q => (neck i).map (q, level i)))
          (range (fun q => (neck j).map (q, level j)))) →
        ∀ f : Sphere 2 → ℝ, ContMDiff I2 𝓘(ℝ) ∞ f → (∀ q, |f q| < 1 / 10) →
        f nk.center = 0 →
        (∀ i, Disjoint (range (fun q => nk.map (q, f q)))
          (range (fun q => (neck i).map (q, level i)))) →
        ∀ W : Set M, closure (interior W) = W →
        frontier W = range (fun q => nk.map (q, f q)) ∪
          ⋃ i, range (fun q => (neck i).map (q, level i)) →
        (∃ δ > 0, ∀ t, 0 < t → t < δ → nk.map (nk.center, t) ∉ W) →
        (∃ i, (nk.map '' {z : Cylinder | f z.1 ≤ z.2 ∧ z.2 ≤ 3} ∩
          range (fun q => (neck i).map (q, level i))).Nonempty) →
        ∃ i, ∃ (η : Sphere 2 ≃ₘ⟮I2, I2⟯ Sphere 2)
          (A : PartialDiffeomorph IC I3 Cylinder M ∞),
          univ ×ˢ Icc (0 : ℝ) 1 ⊆ A.source ∧
          (∀ q, A (q, 0) = nk.map (q, f q)) ∧
          (∀ q, A (q, 1) = (neck i).map (η q, level i)) ∧
          IsCompact (A '' (univ ×ˢ Icc (0 : ℝ) 1)) ∧
          (A '' (univ ×ˢ Icc (0 : ℝ) 1)) ∩ W =
            range (fun q => nk.map (q, f q)) ∪ range (fun q => (neck i).map (q, level i)) ∧
          closure (interior (W ∪ A '' (univ ×ˢ Icc (0 : ℝ) 1))) =
            W ∪ A '' (univ ×ˢ Icc (0 : ℝ) 1) ∧
          frontier (W ∪ A '' (univ ×ˢ Icc (0 : ℝ) 1)) =
            ⋃ j : {j // j ≠ i}, range (fun q => (neck j.val).map (q, level j.val)) ∧
          (∀ y ∈ A '' (univ ×ˢ Icc (0 : ℝ) 1),
            connectedComponentIn (interior W)ᶜ y = A '' (univ ×ˢ Icc (0 : ℝ) 1)) := by
  obtain ⟨eta, heta, hreturn⟩ := exists_spatial_neck_return_deleting_frontier_tolerance.{u}
  refine ⟨eta, heta, ?_⟩
  intro eps heps M _ _ _ _ g p nk ι _ point neck level hlevel hpair
    f hf hfsmall hfzero havoid W hregular hfront hout hmeet
  obtain ⟨i, η, A, hA, hzero, hone, hcompact, hinter, hreg, hdelete⟩ :=
    hreturn eps heps M g p nk ι point neck level hlevel hpair
      f hf hfsmall hfzero havoid W hregular hfront hout hmeet
  let B := A '' (univ ×ˢ Icc (0 : ℝ) 1)
  have hBclosed : IsClosed B := hcompact.isClosed
  have hBreg : closure (interior B) = B := by
    apply A.toOpenPartialHomeomorph.closure_interior_image_of_subset_source hA _ hBclosed
    rw [interior_prod_eq, interior_univ, interior_Icc, closure_prod_eq,
      closure_univ, closure_Ioo zero_ne_one]
  have hBfront : frontier B = range (fun q => nk.map (q, f q)) ∪
      range (fun q => (neck i).map (q, level i)) := by
    have h := A.toOpenPartialHomeomorph.image_frontier_of_subset_source
      hA (isClosed_univ.prod isClosed_Icc) hBclosed
    change A '' frontier (univ ×ˢ Icc (0 : ℝ) 1) = frontier B at h
    rw [frontier_univ_prod_eq, frontier_Icc zero_le_one] at h
    rw [← h]
    ext y
    constructor
    · rintro ⟨⟨q, t⟩, ⟨_, ht⟩, rfl⟩
      rcases ht with ht | ht
      · have ht : t = 0 := ht
        subst t
        exact Or.inl ⟨q, (hzero q).symm⟩
      · have ht : t = 1 := ht
        subst t
        exact Or.inr ⟨η q, (hone q).symm⟩
    · rintro (⟨q, hq⟩ | ⟨q, hq⟩)
      · exact ⟨(q, 0), ⟨mem_univ _, Or.inl rfl⟩, (hzero q).trans hq⟩
      · refine ⟨(η.symm q, 1), ⟨mem_univ _, Or.inr rfl⟩, ?_⟩
        rw [hone, η.apply_symm_apply]
        exact hq
  have hBsub : B ⊆ (interior W)ᶜ := by
    have hd : Disjoint (interior B) (interior W) := by
      rw [disjoint_left]
      intro y hyB hyW
      have hmem : y ∈ frontier B := hBfront.symm ▸
        (hinter ▸ ⟨interior_subset hyB, interior_subset hyW⟩)
      exact hmem.2 hyB
    rw [← hBreg]
    exact (hd.closure_left isOpen_interior).subset_compl_right
  have hBfrontdis : Disjoint B (frontier (W ∪ B)) := by
    rw [hdelete, disjoint_iUnion_right]
    intro j
    rw [disjoint_left]
    intro y hyB hyj
    have hyW : y ∈ W := (hregular ▸ isClosed_closure).frontier_subset
      (hfront.symm ▸ Or.inr (mem_iUnion.mpr ⟨j.val, hyj⟩))
    rcases hinter ▸ (show y ∈ B ∩ W from ⟨hyB, hyW⟩) with hactive | hi
    · exact disjoint_left.mp (havoid j.val) hactive hyj
    · exact disjoint_left.mp (hpair j.property) hyj hi
  let _ : ConnectedSpace (Sphere 2) := isConnected_iff_connectedSpace.mp
    (isConnected_sphere (Module.one_lt_rank_of_one_lt_finrank (by simp [ThreeSpace]))
      (0 : ThreeSpace) zero_le_one)
  have hBconn : IsPreconnected B :=
    (isPreconnected_univ.prod isPreconnected_Icc).image A
      (A.contMDiffOn_toFun.continuousOn.mono hA)
  refine ⟨i, η, A, hA, hzero, hone, hcompact, hinter, hreg, hdelete, ?_⟩
  intro y hy
  exact DifferentialGeometry.Topology.connectedComponentIn_closed_exterior_eq_of_disjoint_frontier_union hBclosed hBconn hBsub hBfrontdis hy

end DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn
