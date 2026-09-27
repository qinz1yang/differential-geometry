import DifferentialGeometry.Topology.Manifold.InfiniteSlabProduct
import DifferentialGeometry.Topology.ProperMap.HalfCylinder
import DifferentialGeometry.Geometry.Neck.SpatialScalarEscape

set_option autoImplicit false
noncomputable section
open Set Filter Manifold
open scoped Manifold ContDiff Topology NNReal

namespace DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn

open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

theorem exists_proper_neck_product_of_fresh_slabs_eq_on_first_slab
    {M : Type*} [TopologicalSpace M] [ChartedSpace ThreeSpace M] [IsManifold I3 ∞ M]
    [T2Space M] [CompactlyCoherentSpace M]
    (g : SmoothRiemannianMetric I3 M) {eps : ℝ} (heps : eps ≤ 1 / 156000)
    (p : ℕ → M) (neck : ∀ n, SpatialNeck g eps (p n))
    (hcompact : ∀ B : ℝ, IsCompact {x : M | metricScalarAt g x ≤ B})
    (P : ℕ → PartialDiffeomorph IC I3 Cylinder M ∞)
    (η : ℕ → Sphere 2 ≃ₘ⟮I2, I2⟯ Sphere 2)
    (hsource : ∀ n, univ ×ˢ Icc (0 : ℝ) 1 ⊆ (P n).source)
    (hseam : ∀ n z, P (n + 1) (z, 0) = P n (η n z, 1))
    (hadjacent : ∀ n, P n '' (univ ×ˢ Icc (0 : ℝ) 1) ∩
      P (n + 1) '' (univ ×ˢ Icc (0 : ℝ) 1) = P n '' (univ ×ˢ ({1} : Set ℝ)))
    (hseparated : ∀ m n : ℕ, m + 1 < n →
      Disjoint (P m '' (univ ×ˢ Icc (0 : ℝ) 1)) (P n '' (univ ×ˢ Icc (0 : ℝ) 1)))
    (hcontrolled : ∀ n, P n '' (univ ×ˢ Icc (0 : ℝ) 1) ⊆
      (neck n).map '' (univ ×ˢ Ioo (-eps⁻¹) eps⁻¹))
    (hband : ∀ n, (neck n).map '' (univ ×ˢ Icc (1 : ℝ) 2) ⊆
      P n '' (univ ×ˢ Icc (0 : ℝ) 1))
 :
    ∃ Θ : Cylinder → M,
      ContMDiffOn IC I3 ∞ Θ (univ ×ˢ Ici (0 : ℝ)) ∧
      InjOn Θ (univ ×ˢ Ici (0 : ℝ)) ∧
      IsProperMap (fun z : Sphere 2 × ℝ≥0 => Θ (z.1, z.2.val)) ∧
      (let U : TopologicalSpace.Opens Cylinder :=
        ⟨univ ×ˢ Ioi (0 : ℝ), isOpen_univ.prod isOpen_Ioi⟩
       IsSmoothEmbedding IC I3 ∞ (fun z : U => Θ z)) ∧
      Θ '' (univ ×ˢ Ici (0 : ℝ)) = ⋃ n, P n '' (univ ×ˢ Icc (0 : ℝ) 1) ∧
      (∀ z t, t ∈ Icc (0 : ℝ) 1 → Θ (z, t) = P 0 (z, t)) ∧
      (∀ n : ℕ, Θ '' (univ ×ˢ Icc (n : ℝ) ((n : ℝ) + 1)) =
        P n '' (univ ×ˢ Icc (0 : ℝ) 1)) ∧
      ∀ B : ℝ, ∃ T : ℝ≥0, ∀ (z : Sphere 2) (t : ℝ≥0),
        T ≤ t → B < metricScalarAt g (Θ (z, t.val)) := by
  have havoid (i j : ℕ) (hij : i < j) :
      (neck j).map ((neck j).center, 3 / 2) ∉ P i '' (univ ×ˢ Icc (0 : ℝ) 1) := by
    let x := (neck j).map ((neck j).center, 3 / 2)
    have hlen : (2 : ℝ) < eps⁻¹ :=
      (lt_inv_comm₀ (by norm_num) (neck j).eps_pos).mpr (by linarith)
    have hwindow : univ ×ˢ Ioo (1 : ℝ) 2 ⊆ (neck j).map.source := by
      intro z hz
      exact (neck j).domain ⟨mem_univ _, by constructor <;> linarith [hz.2.1, hz.2.2]⟩
    have hxo : IsOpen ((neck j).map '' (univ ×ˢ Ioo (1 : ℝ) 2)) :=
      (neck j).map.toOpenPartialHomeomorph.isOpen_image_of_subset_source
        (isOpen_univ.prod isOpen_Ioo) hwindow
    have hxint : x ∈ interior (P j '' (univ ×ˢ Icc (0 : ℝ) 1)) := by
      apply mem_interior.mpr
      refine ⟨(neck j).map '' (univ ×ˢ Ioo (1 : ℝ) 2), ?_, hxo, ?_⟩
      · exact (image_mono (prod_mono_right Ioo_subset_Icc_self)).trans (hband j)
      · exact ⟨((neck j).center, 3 / 2), ⟨mem_univ _, by norm_num⟩, rfl⟩
    intro hxi
    by_cases hsucc : j = i + 1
    · subst j
      have hm := hadjacent i ▸ (show x ∈ P i '' (univ ×ˢ Icc (0 : ℝ) 1) ∩
          P (i + 1) '' (univ ×ˢ Icc (0 : ℝ) 1) from ⟨hxi, interior_subset hxint⟩)
      obtain ⟨⟨z, t⟩, ⟨_, ht⟩, hz⟩ := hm
      have ht1 : t = 1 := ht
      subst t
      have hxface : x ∈ P (i + 1) '' (univ ×ˢ ({0} : Set ℝ)) := by
        refine ⟨((η i).symm z, 0), ⟨mem_univ _, rfl⟩, ?_⟩
        have he := hseam i ((η i).symm z)
        exact he.trans ((congrArg (fun q => P i (q, 1))
          (show η i ((η i).symm z) = z from (η i).apply_symm_apply z)).trans hz)
      have hclosed : IsClosed (P (i + 1) '' (univ ×ˢ Icc (0 : ℝ) 1)) :=
        ((isCompact_univ.prod isCompact_Icc).image_of_continuousOn
          ((P (i + 1)).contMDiffOn_toFun.continuousOn.mono (hsource (i + 1)))).isClosed
      have hf := (P (i + 1)).toOpenPartialHomeomorph.image_frontier_of_subset_source
        (hsource (i + 1)) (isClosed_univ.prod isClosed_Icc) hclosed
      change P (i + 1) '' frontier (univ ×ˢ Icc (0 : ℝ) 1) =
        frontier (P (i + 1) '' (univ ×ˢ Icc (0 : ℝ) 1)) at hf
      rw [frontier_univ_prod_eq, frontier_Icc zero_le_one] at hf
      have hxfront : x ∈ frontier (P (i + 1) '' (univ ×ˢ Icc (0 : ℝ) 1)) := by
        rw [← hf]
        exact image_mono (prod_mono_right (by intro a ha; exact Or.inl ha)) hxface
      exact hxfront.2 hxint
    · have hfar : i + 1 < j := by omega
      exact disjoint_left.mp (hseparated i j hfar) hxi (interior_subset hxint)
  have havoidband (i j : ℕ) (hij : i < j) :
      (neck j).map ((neck j).center, 3 / 2) ∉
        (neck i).map '' (univ ×ˢ Icc (1 : ℝ) 2) := fun h => havoid i j hij (hband i h)
  have hescape (K : Set M) (hK : IsCompact K) : ∀ᶠ n in atTop,
      Disjoint (P n '' (univ ×ˢ Icc (0 : ℝ) 1)) K := by
    filter_upwards [eventually_disjoint_spatial_neck_window_of_midpoint_avoids_earlier_band
      heps p neck hcompact havoidband hK] with n hn
    exact (hn.mono_right (hcontrolled n)).symm
  obtain ⟨Θ, hsmooth, hinj, hproper, hembed, hrange, hbase, hstrip⟩ :=
    DifferentialGeometry.Topology.Manifold.exists_proper_smooth_product_of_slabs_eq_on_first_slab
      P η hsource hseam hadjacent hseparated hescape
  exact ⟨Θ, hsmooth, hinj, hproper, hembed, hrange, hbase, hstrip,
    fun B => DifferentialGeometry.Topology.uniform_scalar_divergence_of_isProperMap
      (metricScalarAt g) hcompact _ hproper B⟩


theorem exists_proper_neck_product_of_fresh_slabs
    {M : Type*} [TopologicalSpace M] [ChartedSpace ThreeSpace M] [IsManifold I3 ∞ M]
    [T2Space M] [CompactlyCoherentSpace M]
    (g : SmoothRiemannianMetric I3 M) {eps : ℝ} (heps : eps ≤ 1 / 156000)
    (p : ℕ → M) (neck : ∀ n, SpatialNeck g eps (p n))
    (hcompact : ∀ B : ℝ, IsCompact {x : M | metricScalarAt g x ≤ B})
    (P : ℕ → PartialDiffeomorph IC I3 Cylinder M ∞)
    (η : ℕ → Sphere 2 ≃ₘ⟮I2, I2⟯ Sphere 2)
    (hsource : ∀ n, univ ×ˢ Icc (0 : ℝ) 1 ⊆ (P n).source)
    (hseam : ∀ n z, P (n + 1) (z, 0) = P n (η n z, 1))
    (hadjacent : ∀ n, P n '' (univ ×ˢ Icc (0 : ℝ) 1) ∩
      P (n + 1) '' (univ ×ˢ Icc (0 : ℝ) 1) = P n '' (univ ×ˢ ({1} : Set ℝ)))
    (hseparated : ∀ m n : ℕ, m + 1 < n →
      Disjoint (P m '' (univ ×ˢ Icc (0 : ℝ) 1)) (P n '' (univ ×ˢ Icc (0 : ℝ) 1)))
    (hcontrolled : ∀ n, P n '' (univ ×ˢ Icc (0 : ℝ) 1) ⊆
      (neck n).map '' (univ ×ˢ Ioo (-eps⁻¹) eps⁻¹))
    (hband : ∀ n, (neck n).map '' (univ ×ˢ Icc (1 : ℝ) 2) ⊆
      P n '' (univ ×ˢ Icc (0 : ℝ) 1))
 :
    ∃ Θ : Cylinder → M,
      ContMDiffOn IC I3 ∞ Θ (univ ×ˢ Ici (0 : ℝ)) ∧
      InjOn Θ (univ ×ˢ Ici (0 : ℝ)) ∧
      IsProperMap (fun z : Sphere 2 × ℝ≥0 => Θ (z.1, z.2.val)) ∧
      (let U : TopologicalSpace.Opens Cylinder :=
        ⟨univ ×ˢ Ioi (0 : ℝ), isOpen_univ.prod isOpen_Ioi⟩
       IsSmoothEmbedding IC I3 ∞ (fun z : U => Θ z)) ∧
      Θ '' (univ ×ˢ Ici (0 : ℝ)) = ⋃ n, P n '' (univ ×ˢ Icc (0 : ℝ) 1) ∧
      (∀ z, Θ (z, 0) = P 0 (z, 0)) ∧
      (∀ n : ℕ, Θ '' (univ ×ˢ Icc (n : ℝ) ((n : ℝ) + 1)) =
        P n '' (univ ×ˢ Icc (0 : ℝ) 1)) ∧
      ∀ B : ℝ, ∃ T : ℝ≥0, ∀ (z : Sphere 2) (t : ℝ≥0),
        T ≤ t → B < metricScalarAt g (Θ (z, t.val)) := by
  obtain ⟨Theta, hsmooth, hinj, hproper, hembed, hrange, hfirst, hstrip, hscalar⟩ :=
    exists_proper_neck_product_of_fresh_slabs_eq_on_first_slab g heps p neck hcompact
      P η hsource hseam hadjacent hseparated hcontrolled hband
  exact ⟨Theta, hsmooth, hinj, hproper, hembed, hrange,
    fun z => hfirst z 0 ⟨le_rfl, zero_le_one⟩, hstrip, hscalar⟩


theorem scalar_le_on_first_slab_of_neck_product
    {M : Type*} [TopologicalSpace M] [ChartedSpace ThreeSpace M] [IsManifold I3 ∞ M]
    [T2Space M] {g : SmoothRiemannianMetric I3 M} {eps : ℝ} {p : M}
    (nk : SpatialNeck g eps p)
    (P : PartialDiffeomorph IC I3 Cylinder M ∞) (Theta : Cylinder → M)
    (hfirst : ∀ z t, t ∈ Icc (0 : ℝ) 1 → Theta (z, t) = P (z, t))
    (hcontrolled : P '' (univ ×ˢ Icc (0 : ℝ) 1) ⊆ nk.map '' (univ ×ˢ Ioo (-eps⁻¹) eps⁻¹)) :
    ∀ z t, t ∈ Icc (0 : ℝ) 1 →
      metricScalarAt g (Theta (z, t)) ≤ (1 + 4323 * eps) * metricScalarAt g p := by
  intro z t ht
  rw [hfirst z t ht]
  exact (nk.scalar_bounds_on_image_window (hcontrolled ⟨(z, t), ⟨mem_univ _, ht⟩, rfl⟩)).2


theorem scalar_le_on_first_slab_of_original_base_bound
    {M : Type*} [TopologicalSpace M] [ChartedSpace ThreeSpace M] [IsManifold I3 ∞ M]
    [T2Space M] {g : SmoothRiemannianMetric I3 M} {eps : ℝ} {p : M}
    (nk : SpatialNeck g eps p) (P : PartialDiffeomorph IC I3 Cylinder M ∞)
    (Theta : Cylinder → M) (S : Set M) (hp : p ∈ S) (B : ℝ)
    (hB : ∀ x ∈ S, metricScalarAt g x ≤ B)
    (hfirst : ∀ z t, t ∈ Icc (0 : ℝ) 1 → Theta (z, t) = P (z, t))
    (hcontrolled : P '' (univ ×ˢ Icc (0 : ℝ) 1) ⊆
      nk.map '' (univ ×ˢ Ioo (-eps⁻¹) eps⁻¹)) :
    ∀ z t, t ∈ Icc (0 : ℝ) 1 →
      metricScalarAt g (Theta (z, t)) ≤ (1 + 4323 * eps) * B := by
  intro z t ht
  exact (scalar_le_on_first_slab_of_neck_product nk P Theta hfirst hcontrolled z t ht).trans
    (mul_le_mul_of_nonneg_left (hB p hp) (by have := nk.eps_pos; positivity))

end DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn
