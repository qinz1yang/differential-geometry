import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.CapRegionStructure
import DifferentialGeometry.Geometry.Metric.Distance.Boundary
import DifferentialGeometry.Geometry.Comparison.Distance.Continuity

set_option autoImplicit false
noncomputable section
open Set
open scoped Manifold ContDiff Topology ENNReal

namespace DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn

open DifferentialGeometry.Geometry.Curvature DifferentialGeometry.Geometry.Riemannian
open DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

universe u
variable {M : Type u} [TopologicalSpace M] [ChartedSpace ThreeSpace M]
  [IsManifold I3 ∞ M] {D : RealTimeInterval}
  {S : SolutionOn (I := I3) (M := M) D} {eps t : ℝ} {x : M} {U : Set M}

theorem LocalCap.tube_map_mem_core_iff
    (cap : LocalCap S eps x t U) {z : Sphere 2} {a : ℝ} (ha : a ∈ Icc (0 : ℝ) 1) :
    cap.tubeMap (z, a) ∈ cap.core.carrier ↔ a = 0 := by
  have hsource : (z, a) ∈ cap.tubeMap.source := cap.tube_domain ⟨mem_univ z, ha⟩
  have htube : cap.tubeMap (z, a) ∈ cap.tube :=
    cap.tube_eq ▸ ⟨(z, a), ⟨mem_univ z, ha⟩, rfl⟩
  constructor
  · intro hcore
    have hboundary : cap.tubeMap (z, a) ∈ frontier cap.core.carrier :=
      cap.overlap_eq ▸ ⟨hcore, htube⟩
    rw [← cap.inner_boundary] at hboundary
    obtain ⟨⟨w, b⟩, hb, heq⟩ := hboundary
    have hb0 : b = 0 := hb.2
    have hsource' : (w, b) ∈ cap.tubeMap.source :=
      cap.tube_domain ⟨mem_univ w, by
        simpa only [hb0] using (show (0 : ℝ) ∈ Icc 0 1 from ⟨le_rfl, zero_le_one⟩)⟩
    have heq' : (w, b) = (z, a) := by
      calc
        (w, b) = cap.tubeMap.symm (cap.tubeMap (w, b)) :=
          (cap.tubeMap.left_inv' hsource').symm
        _ = cap.tubeMap.symm (cap.tubeMap (z, a)) := congrArg cap.tubeMap.symm heq
        _ = (z, a) := cap.tubeMap.left_inv' hsource
    exact (congrArg Prod.snd heq').symm.trans hb0
  · rintro rfl
    have hboundary : cap.tubeMap (z, 0) ∈ frontier cap.core.carrier :=
      cap.inner_boundary ▸ ⟨(z, 0), ⟨mem_univ z, rfl⟩, rfl⟩
    rw [← cap.overlap_eq] at hboundary
    exact hboundary.1

variable [T2Space M] [PreconnectedSpace M]

theorem LocalCap.lt_metricDistance_of_pos_tube_coordinate
    (cap : LocalCap S eps x t U) (g : SmoothRiemannianMetric I3 M) {r : ℝ}
    (hdepth : ∀ y ∈ frontier cap.core.carrier, r ≤ metricDistance g x y)
    {z : Sphere 2} {a : ℝ} (ha : a ∈ Ioc (0 : ℝ) 1) :
    r < metricDistance g x (cap.tubeMap (z, a)) := by
  let _ : LocallyCompactSpace M := ChartedSpace.locallyCompactSpace ThreeSpace M
  let _ : RegularSpace M := inferInstance
  have hball : riemannianClosedBallOf g x r ⊆ cap.core.carrier :=
    Geometry.Metric.riemannianEDistOf_closedBall_subset_of_le_frontier_distance g
      cap.core.compact.isClosed cap.center_inside ENNReal.ofReal_ne_top (by
        intro y hy
        exact (ENNReal.ofReal_le_iff_le_toReal (riemannianEDistOf_ne_top g x y)).mpr
          (hdepth y hy))
  have hnot : cap.tubeMap (z, a) ∉ cap.core.carrier := by
    rw [cap.tube_map_mem_core_iff ⟨ha.1.le, ha.2⟩]
    exact ha.1.ne'
  apply lt_of_not_ge
  intro hle
  have hr : 0 ≤ r := ENNReal.toReal_nonneg.trans hle
  exact hnot (hball ((ENNReal.le_ofReal_iff_toReal_le
    (riemannianEDistOf_ne_top g x (cap.tubeMap (z, a))) hr).mpr hle))

theorem LocalCap.exists_uniform_depth_on_tube_strip
    (cap : LocalCap S eps x t U) (g : SmoothRiemannianMetric I3 M) {r : ℝ}
    (hdepth : ∀ y ∈ frontier cap.core.carrier, r ≤ metricDistance g x y)
    {a : ℝ} (ha : 0 < a) (ha1 : a ≤ 1) :
    ∃ r' : ℝ, r < r' ∧ ∀ y ∈ cap.tubeMap '' (univ ×ˢ Icc a 1),
      r' ≤ metricDistance g x y := by
  have hsource : univ ×ˢ Icc a 1 ⊆ cap.tubeMap.source := by
    intro z hz
    exact cap.tube_domain ⟨hz.1, ha.le.trans hz.2.1, hz.2.2⟩
  have hcompact : IsCompact (cap.tubeMap '' (univ ×ˢ Icc a 1)) :=
    (isCompact_univ.prod isCompact_Icc).image_of_continuousOn
      (cap.tubeMap.contMDiffOn_toFun.continuousOn.mono hsource)
  let z : Sphere 2 := ⟨EuclideanSpace.single 0 1, by simp⟩
  have hnonempty : (cap.tubeMap '' (univ ×ˢ Icc a 1)).Nonempty :=
    ⟨cap.tubeMap (z, a), (z, a), ⟨mem_univ z, le_rfl, ha1⟩, rfl⟩
  have hcontinuous : Continuous (fun y => metricDistance g x y) := by
    apply continuous_iff_continuousAt.mpr
    intro y
    exact (ENNReal.continuousAt_toReal (riemannianEDistOf_ne_top g x y)).comp
      (continuous_riemannianEDist g x).continuousAt
  obtain ⟨y, hy, hmin⟩ := hcompact.exists_isMinOn hnonempty hcontinuous.continuousOn
  refine ⟨metricDistance g x y, ?_, hmin⟩
  obtain ⟨⟨w, b⟩, hb, rfl⟩ := hy
  exact cap.lt_metricDistance_of_pos_tube_coordinate g hdepth ⟨ha.trans_le hb.2.1, hb.2.2⟩

end DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn
