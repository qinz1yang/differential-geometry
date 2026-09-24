import DifferentialGeometry.Geometry.Neck.SpatialOverlap
import DifferentialGeometry.Topology.Manifold.ProductChartCollar

set_option autoImplicit false
noncomputable section
open Set Manifold
open scoped Manifold ContDiff

namespace DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn

open DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
open DifferentialGeometry.Topology

universe u

theorem exists_spatial_neck_shared_collar_tolerance :
    ∃ eta : ℝ, 0 < eta ∧
      ∀ eps : ℝ, eps ≤ eta →
        ∀ (M : Type u) [TopologicalSpace M] [ChartedSpace ThreeSpace M]
          [IsManifold I3 ∞ M] [T2Space M]
          (g : SmoothRiemannianMetric I3 M) (p₀ p₁ : M)
          (nk₀ : SpatialNeck g eps p₀) (nk₁ : SpatialNeck g eps p₁),
          (nk₀.map '' (univ ×ˢ Icc (-1 : ℝ) 1) ∩
            nk₁.map '' (univ ×ˢ Icc (-1 : ℝ) 1)).Nonempty →
          ∀ t : ℝ, t ∈ Ioo (-1 : ℝ) 1 →
          ∃ c : SmoothTwoSidedCollar I2 I3 (fun p : Sphere 2 => nk₀.map (p, t)),
            c.radius < min (t + 1) (1 - t) ∧
            (∀ x : Sphere 2 × symmetricOpenInterval c.radius,
              c.toFun x = nk₀.map (x.1, t + (x.2 : ℝ))) ∧
            range c.toFun ⊆ nk₀.map '' (univ ×ˢ Ioo (-1 : ℝ) 1) ∧
            range c.toFun ⊆ nk₁.map '' (univ ×ˢ Ioo (-eps⁻¹ + 1) (eps⁻¹ - 1)) := by
  obtain ⟨eta, heta, _, hcontrol⟩ := exists_spatial_neck_intersection_tolerance.{u}
  refine ⟨eta, heta, ?_⟩
  intro eps heps M _ _ _ _ g p₀ p₁ nk₀ nk₁ hmeet t ht
  obtain ⟨_, _, _, hbuffer, _⟩ := hcontrol eps heps M g p₀ p₁ nk₀ nk₁ hmeet
  have hunit : (1 : ℝ) < eps⁻¹ :=
    (one_lt_inv₀ nk₀.eps_pos).mpr (nk₀.eps_small.trans (by norm_num))
  have hgraph (p : Sphere 2) : (p, t) ∈ nk₀.cylindricalChart.domain :=
    ⟨mem_univ _, (neg_lt_neg hunit).trans ht.1, ht.2.trans hunit⟩
  have hr : 0 < min (t + 1) (1 - t) := lt_min (by linarith [ht.1]) (by linarith [ht.2])
  obtain ⟨c, hcr, _, hcoord⟩ := exists_smoothTwoSidedCollar_of_product_chart_graph
    nk₀.cylindricalChart.domain nk₀.cylindricalChart.target nk₀.cylindricalChart.chart
    (fun _ => t) contMDiff_const hgraph hr
  refine ⟨c, hcr, ?_, ?_, ?_⟩
  · intro x
    obtain ⟨hx, heq⟩ := hcoord x
    exact heq
  · rintro y ⟨x, rfl⟩
    obtain ⟨hx, heq⟩ := hcoord x
    refine ⟨(x.1, t + (x.2 : ℝ)), ⟨mem_univ _, ?_⟩, heq.symm⟩
    have hl := hcr.trans_le (min_le_left _ _)
    have hu := hcr.trans_le (min_le_right _ _)
    constructor <;> linarith [x.2.property.1, x.2.property.2]
  · rintro y ⟨x, rfl⟩
    obtain ⟨hx, heq⟩ := hcoord x
    apply hbuffer
    left
    refine ⟨(x.1, t + (x.2 : ℝ)), ⟨mem_univ _, ?_⟩, heq.symm⟩
    have hl := hcr.trans_le (min_le_left _ _)
    have hu := hcr.trans_le (min_le_right _ _)
    constructor <;> linarith [x.2.property.1, x.2.property.2]

theorem SpatialNeck.unit_slab_local_sides
    {M : Type*} [TopologicalSpace M] [ChartedSpace ThreeSpace M] [IsManifold I3 ∞ M]
    {g : SmoothRiemannianMetric I3 M} {eps : ℝ} {p : M} (nk : SpatialNeck g eps p)
    {t : ℝ} (ht : t ∈ Ioo (-1 : ℝ) 1) :
    let L := nk.map '' (univ ×ˢ Ioo (-1 : ℝ) t)
    let U := nk.map '' (univ ×ˢ Ioo t 1)
    IsOpen L ∧ IsOpen U ∧ IsConnected L ∧ IsConnected U ∧ Disjoint L U ∧
      (nk.map '' (univ ×ˢ Ioo (-1 : ℝ) 1)) \ range (fun q : Sphere 2 => nk.map (q, t)) = L ∪ U := by
  have hlen : (1 : ℝ) < eps⁻¹ :=
    (one_lt_inv₀ nk.eps_pos).mpr (nk.eps_small.trans (by norm_num))
  have hslab : (univ ×ˢ Ioo (-1 : ℝ) 1 : Set Cylinder) ⊆ nk.map.source := by
    intro z hz
    exact nk.domain ⟨hz.1, (neg_lt_neg hlen).trans hz.2.1, hz.2.2.trans hlen⟩
  have hl : (univ ×ˢ Ioo (-1 : ℝ) t : Set Cylinder) ⊆ univ ×ˢ Ioo (-1 : ℝ) 1 := by
    intro z hz
    exact ⟨hz.1, hz.2.1, hz.2.2.trans ht.2⟩
  have hu : (univ ×ˢ Ioo t 1 : Set Cylinder) ⊆ univ ×ˢ Ioo (-1 : ℝ) 1 := by
    intro z hz
    exact ⟨hz.1, ht.1.trans hz.2.1, hz.2.2⟩
  let : ConnectedSpace (Sphere 2) := isConnected_iff_connectedSpace.mp
    (isConnected_sphere (Module.one_lt_rank_of_one_lt_finrank (by simp [ThreeSpace]))
      (0 : ThreeSpace) (by norm_num : (0 : ℝ) ≤ 1))
  have hconn (a b : ℝ) (hab : a < b)
      (hs : (univ ×ˢ Ioo a b : Set Cylinder) ⊆ nk.map.source) :
      IsConnected (nk.map '' (univ ×ˢ Ioo a b)) := by
    have hprod : IsConnected (univ ×ˢ Ioo a b : Set Cylinder) :=
      IsConnected.prod isConnected_univ (isConnected_Ioo hab)
    exact hprod.image nk.map (nk.map.contMDiffOn_toFun.continuousOn.mono hs)
  refine ⟨nk.map.toOpenPartialHomeomorph.isOpen_image_of_subset_source
      (isOpen_univ.prod isOpen_Ioo) (hl.trans hslab),
    nk.map.toOpenPartialHomeomorph.isOpen_image_of_subset_source
      (isOpen_univ.prod isOpen_Ioo) (hu.trans hslab),
    hconn (-1) t ht.1 (hl.trans hslab), hconn t 1 ht.2 (hu.trans hslab), ?_, ?_⟩
  · apply Set.disjoint_left.mpr
    rintro y ⟨x, hx, rfl⟩ ⟨z, hz, heq⟩
    have he := nk.map.injOn (hslab (hu hz)) (hslab (hl hx)) heq
    have hh := congrArg Prod.snd he
    linarith [hx.2.2, hz.2.1]
  · ext y
    constructor
    · rintro ⟨⟨x, hx, rfl⟩, hcenter⟩
      have hne : x.2 ≠ t := by
        intro heq
        exact hcenter ⟨x.1, by rw [← heq]⟩
      rcases lt_or_gt_of_ne hne with h | h
      · exact Or.inl ⟨x, ⟨hx.1, hx.2.1, h⟩, rfl⟩
      · exact Or.inr ⟨x, ⟨hx.1, h, hx.2.2⟩, rfl⟩
    · rintro (⟨x, hx, rfl⟩ | ⟨x, hx, rfl⟩)
      · refine ⟨⟨x, hl hx, rfl⟩, ?_⟩
        rintro ⟨q, hq⟩
        have he := nk.map.injOn (hslab ⟨mem_univ _, ht⟩) (hslab (hl hx)) hq
        have hh := congrArg Prod.snd he
        linarith [hx.2.2]
      · refine ⟨⟨x, hu hx, rfl⟩, ?_⟩
        rintro ⟨q, hq⟩
        have he := nk.map.injOn (hslab ⟨mem_univ _, ht⟩) (hslab (hu hx)) hq
        have hh := congrArg Prod.snd he
        linarith [hx.2.1]

end DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn
