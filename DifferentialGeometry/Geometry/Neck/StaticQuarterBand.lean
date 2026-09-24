import DifferentialGeometry.Geometry.Neck.StaticSlabCapture
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.CompactCanonicalCover

noncomputable section
open Set Manifold
open DifferentialGeometry.Geometry.Curvature
open scoped Manifold ContDiff Topology

namespace DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn
open DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

universe u
variable {M : Type u} [TopologicalSpace M] [ChartedSpace ThreeSpace M]
  [IsManifold I3 ∞ M] [T2Space M] {g : SmoothRiemannianMetric I3 M}
  {eps : ℝ} {p : M} {W : Set M}

theorem SpatialNeck.quarter_band_subset_ball_sdiff_of_outward_graph
    (nk : SpatialNeck g eps p) (heps : eps ≤ 1 / 8646)
    {V : Set M}
    (hball : riemannianBallOf g p (1000 / Real.sqrt (metricScalarAt g p)) ⊆ V)
    (f : Sphere 2 → ℝ) (hf : Continuous f) (hsmall : ∀ q, |f q| < 1 / 10)
    (hzero : f nk.center = 0) (hW : IsClosed W)
    (hfront : frontier W = range (fun q : Sphere 2 => nk.map (q, f q)))
    (hout : ∃ r > 0, ∀ a, 0 < a → a < r → nk.map (nk.center, a) ∉ W) :
    nk.map '' (univ ×ˢ Icc (1 / 8 : ℝ) (3 / 8)) ⊆ V \ W := by
  have hcap := nk.image_slab_subset_of_ball_subset heps nk.center
    (by norm_num : |(0 : ℝ)| ≤ 4) nk.center_eq hball
  have hlen : (1 : ℝ) < eps⁻¹ :=
    (one_lt_inv₀ nk.eps_pos).mpr (by linarith [nk.eps_small])
  let A := nk.map '' {z : Cylinder | f z.1 < z.2 ∧ z.2 < 1}
  have hsrc : {z : Cylinder | f z.1 < z.2 ∧ z.2 < 1} ⊆ nk.map.source := by
    intro z hz
    exact nk.domain ⟨mem_univ _, by linarith [(abs_lt.mp (hsmall z.1)).1, hz.1], hz.2.trans hlen⟩
  have hfsrc (q : Sphere 2) : (q, f q) ∈ nk.map.source :=
    nk.domain ⟨mem_univ _, by constructor <;>
      linarith [(abs_lt.mp (hsmall q)).1, (abs_lt.mp (hsmall q)).2]⟩
  let _ : ConnectedSpace (Sphere 2) := isConnected_iff_connectedSpace.mp
    (isConnected_sphere (Module.one_lt_rank_of_one_lt_finrank (by simp [ThreeSpace]))
      (0 : ThreeSpace) zero_le_one)
  have hconn : IsPreconnected A :=
    (DifferentialGeometry.Topology.isPreconnected_openGraphBand f (fun _ => 1) hf continuous_const
      (by intro q; linarith [(abs_lt.mp (hsmall q)).2])).image nk.map
      (nk.map.contMDiffOn_toFun.continuousOn.mono hsrc)
  have havoid : Disjoint A (frontier Wᶜ) := by
    rw [frontier_compl, hfront, disjoint_left]
    rintro x ⟨z, hz, rfl⟩ ⟨q, hq⟩
    have he := nk.map.toPartialEquiv.injOn (hfsrc q) (hsrc hz) hq
    have hqz : q = z.1 := congrArg Prod.fst he
    have hheight := congrArg Prod.snd he
    change f q = z.2 at hheight
    rw [hqz] at hheight
    exact hz.1.ne hheight
  obtain ⟨r, hr, hrout⟩ := hout
  let b := min r 1 / 2
  have hb : 0 < b := half_pos (lt_min hr zero_lt_one)
  have hbr : b < r := (half_lt_self (lt_min hr zero_lt_one)).trans_le (min_le_left _ _)
  have hb1 : b < 1 := (half_lt_self (lt_min hr zero_lt_one)).trans_le (min_le_right _ _)
  have hAout : A ⊆ Wᶜ :=
    (DifferentialGeometry.Topology.subset_interior_of_isPreconnected_of_disjoint_frontier
      hconn havoid ⟨nk.map (nk.center, b),
        ⟨(nk.center, b), ⟨by simpa only [hzero] using hb, hb1⟩, rfl⟩,
        hW.isOpen_compl.interior_eq.symm ▸ hrout b hb hbr⟩).trans interior_subset
  rintro x ⟨z, hz, rfl⟩
  refine ⟨hcap ⟨z, ⟨hz.1, by constructor <;> linarith [hz.2.1, hz.2.2]⟩, rfl⟩, ?_⟩
  exact hAout ⟨z, ⟨by linarith [(abs_lt.mp (hsmall z.1)).2, hz.2.1],
    by linarith [hz.2.2]⟩, rfl⟩


end DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn
