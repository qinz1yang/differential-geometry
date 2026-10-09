import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Contract.BallEmbeddingIsotopy
import DifferentialGeometry.Topology.Manifold.ManifoldIsotopyExtension

set_option autoImplicit false
noncomputable section
open Bundle Manifold Set Metric Filter Topology
open scoped Manifold ContDiff Topology
open DifferentialGeometry.Topology (BallChart)

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

universe u

def ballChartCenterTubeWithin {U : Type u} [TopologicalSpace U] [ChartedSpace ThreeSpace U]
    (b b' : BallChart 3 (𝓡 3) U) (C : Set U) : Prop :=
  ∀ t ∈ Set.Icc (0 : ℝ) 1,
    (1 - t) • (b'.chart.symm (b.chart 0)) + t • (0 : ThreeSpace)
      ∈ b'.chart.source ∩ b'.chart ⁻¹' Cᶜ

theorem ballChartCenterTubeWithin_of_center_eq {U : Type u} [TopologicalSpace U]
    [ChartedSpace ThreeSpace U] (b b' : BallChart 3 (𝓡 3) U) {C : Set U}
    (hcenter : b.chart (0 : ThreeSpace) = b'.chart (0 : ThreeSpace))
    (hdisj : Disjoint (b'.chart '' Metric.closedBall (0 : ThreeSpace) 1) C) :
    ballChartCenterTubeWithin b b' C := by
  have h0src : (0 : ThreeSpace) ∈ b'.chart.source :=
    b'.closedBall_subset_source (Metric.mem_closedBall_self (by norm_num))
  have hsymm : b'.chart.symm (b.chart (0 : ThreeSpace)) = (0 : ThreeSpace) := by
    rw [hcenter]
    exact PartialDiffeomorph.symm_apply_apply b'.chart h0src
  intro t ht
  rw [hsymm]
  simp only [smul_zero, zero_add]
  refine ⟨h0src, ?_⟩
  intro hC
  exact Set.disjoint_left.mp hdisj ⟨0, Metric.mem_closedBall_self (by norm_num), rfl⟩ hC

theorem orientedBallChartIsotopicAwayFromCompact_of_centerComparison_and_centerTubeWithin
    {U : Type u} [TopologicalSpace U] [ChartedSpace ThreeSpace U] [IsManifold ThreeModel ∞ U]
    [T2Space U] (o : ManifoldOrientation ThreeModel U 3) (b b' : OrientedBallEmbedding U o)
    (C : Set U) (hC : IsCompact C)
    (hdisj : Disjoint (b.chart '' Metric.closedBall (0 : ThreeSpace) 1) C)
    (hdisj' : Disjoint (b'.chart '' Metric.closedBall (0 : ThreeSpace) 1) C)
    (hcenter : b.chart (0 : ThreeSpace) ∈ b'.chart.target)
    (hdet : 0 < (fderiv ℝ (fun x : ThreeSpace => b'.chart.symm (b.chart x)) 0).det)
    (htube : ballChartCenterTubeWithin b.toBallChart b'.toBallChart C) :
    orientedBallChartIsotopicAwayFromCompact o b b' C :=
  orientedBallChartIsotopicAwayFromCompact_of_centerComparison_and_tube o b b' C hC hdisj hdisj'
    hcenter hdet htube

theorem ballChart_center_mem_target_of_center_eq {U : Type u} [TopologicalSpace U]
    [ChartedSpace ThreeSpace U] (b b' : BallChart 3 (𝓡 3) U)
    (hcenter : b.chart (0 : ThreeSpace) = b'.chart (0 : ThreeSpace)) :
    b.chart (0 : ThreeSpace) ∈ b'.chart.target := by
  rw [hcenter]
  exact b'.chart.map_source (b'.closedBall_subset_source (Metric.mem_closedBall_self (by norm_num)))

theorem orientedBallChartIsotopicAwayFromCompact_of_center_eq
    {U : Type u} [TopologicalSpace U] [ChartedSpace ThreeSpace U] [IsManifold ThreeModel ∞ U]
    [T2Space U] (o : ManifoldOrientation ThreeModel U 3) (b b' : OrientedBallEmbedding U o)
    (C : Set U) (hC : IsCompact C)
    (hdisj : Disjoint (b.chart '' Metric.closedBall (0 : ThreeSpace) 1) C)
    (hdisj' : Disjoint (b'.chart '' Metric.closedBall (0 : ThreeSpace) 1) C)
    (hdet : 0 < (fderiv ℝ (fun x : ThreeSpace => b'.chart.symm (b.chart x)) 0).det)
    (hctr : b.chart (0 : ThreeSpace) = b'.chart (0 : ThreeSpace)) :
    orientedBallChartIsotopicAwayFromCompact o b b' C :=
  orientedBallChartIsotopicAwayFromCompact_of_centerComparison_and_centerTubeWithin o b b' C hC
    hdisj hdisj' (ballChart_center_mem_target_of_center_eq b.toBallChart b'.toBallChart hctr) hdet
    (ballChartCenterTubeWithin_of_center_eq b.toBallChart b'.toBallChart hctr hdisj')

private theorem affineBallChart_mem_source_iff
    {M : DifferentialGeometry.Topology.ClosedOrientedManifold.{u} 3}
    (c : DifferentialGeometry.Topology.OrientedBallChart M) {s : ThreeSpace} {r : ℝ} (hr : 0 < r)
    (hs : ‖s‖ + 2 * r ≤ 2) (x : ThreeSpace) :
    x ∈ (c.affine s r hr hs).chart.source ↔ s + r • x ∈ c.chart.source := by
  constructor
  · intro hx
    exact DifferentialGeometry.Topology.BallChart.affine_source_subset c.toBallChart s r hr hs hx
  · intro hx
    rw [show (c.affine s r hr hs).chart.source
        = Set.univ ∩ (DifferentialGeometry.Topology.AffineModel.affineDiffeomorph s r
            (ne_of_gt hr)).toPartialDiffeomorph.toPartialEquiv ⁻¹' c.chart.source from rfl]
    exact ⟨Set.mem_univ _, hx⟩

private theorem affineBallChart_centerTube_symm
    {M : DifferentialGeometry.Topology.ClosedOrientedManifold.{u} 3}
    (c : DifferentialGeometry.Topology.OrientedBallChart M) {s : ThreeSpace} {r : ℝ} (hr : 0 < r)
    (hs : ‖s‖ + 2 * r ≤ 2) :
    (c.affine s r hr hs).chart.symm (c.chart (0 : ThreeSpace)) = -(r⁻¹ • s) := by
  have h0src : (0 : ThreeSpace) ∈ c.chart.source :=
    c.closedBall_subset_source (Metric.mem_closedBall_self (by norm_num))
  change r⁻¹ • (c.chart.symm (c.chart (0 : ThreeSpace)) - s) = -(r⁻¹ • s)
  rw [PartialDiffeomorph.symm_apply_apply c.chart h0src, zero_sub, smul_neg]

private theorem affineBallChart_centerTube_mem
    {M : DifferentialGeometry.Topology.ClosedOrientedManifold.{u} 3}
    (c : DifferentialGeometry.Topology.OrientedBallChart M) {s : ThreeSpace} {r : ℝ} (hr : 0 < r)
    (hs : ‖s‖ + 2 * r ≤ 2) {u : ℝ} (hu : u ∈ Set.Icc (0 : ℝ) 1) :
    (1 - u) • ((c.affine s r hr hs).chart.symm (c.chart (0 : ThreeSpace)))
        + u • (0 : ThreeSpace) ∈ (c.affine s r hr hs).chart.source ∧
      (c.affine s r hr hs).chart
          ((1 - u) • ((c.affine s r hr hs).chart.symm (c.chart (0 : ThreeSpace)))
            + u • (0 : ThreeSpace)) = c.chart (u • s) := by
  have hsymm := affineBallChart_centerTube_symm c hr hs
  have hpoint : (1 - u) • ((c.affine s r hr hs).chart.symm (c.chart (0 : ThreeSpace)))
      + u • (0 : ThreeSpace) = -((1 - u) * r⁻¹) • s := by
    rw [hsymm]
    simp only [smul_zero, add_zero]
    module
  have hshift : s + r • (-((1 - u) * r⁻¹) • s) = u • s := by
    rw [smul_smul]
    have hcoef : r * -((1 - u) * r⁻¹) = -(1 - u) := by
      field_simp
    rw [hcoef]
    module
  have husrc : u • s ∈ c.chart.source := by
    refine c.closedBall_subset_source ?_
    rw [Metric.mem_closedBall, dist_zero_right, norm_smul, Real.norm_eq_abs, abs_of_nonneg hu.1]
    nlinarith [hu.2, norm_nonneg s]
  refine ⟨?_, ?_⟩
  · rw [hpoint]
    exact (affineBallChart_mem_source_iff c hr hs _).mpr (by rw [hshift]; exact husrc)
  · rw [hpoint, DifferentialGeometry.Topology.OrientedBallChart.affine_apply, hshift]

theorem exists_orientedBallEmbedding_not_ballChartCenterTubeWithin :
    ∃ (b b' : OrientedBallEmbedding
        (DifferentialGeometry.Topology.standardThreeSphereLift.{0}).Carrier
        (DifferentialGeometry.Topology.standardThreeSphereLift.{0}).orientation)
      (C : Set (DifferentialGeometry.Topology.standardThreeSphereLift.{0}).Carrier),
      IsCompact C ∧
      Disjoint (b.chart '' Metric.closedBall (0 : ThreeSpace) 1) C ∧
      Disjoint (b'.chart '' Metric.closedBall (0 : ThreeSpace) 1) C ∧
      b.chart (0 : ThreeSpace) ∈ b'.chart.target ∧
      ¬ ballChartCenterTubeWithin b.toBallChart b'.toBallChart C := by
  let M : DifferentialGeometry.Topology.ClosedOrientedManifold.{0} 3 :=
    DifferentialGeometry.Topology.standardThreeSphereLift.{0}.toClosedOrientedManifold
  let c : DifferentialGeometry.Topology.OrientedBallChart M :=
    DifferentialGeometry.Topology.orientedBallChart
      DifferentialGeometry.Topology.standardThreeSphereLift.{0}
  set s : ThreeSpace := (3 / 2 : ℝ) • EuclideanSpace.single (0 : Fin 3) (1 : ℝ) with hsdef
  have hnorm : ‖s‖ = 3 / 2 := by
    rw [hsdef, norm_smul, Real.norm_eq_abs, abs_of_pos (by norm_num : (0 : ℝ) < 3 / 2)]
    simp
  have hr : (0 : ℝ) < 1 / 8 := by norm_num
  have hs : ‖s‖ + 2 * (1 / 8 : ℝ) ≤ 2 := by rw [hnorm]; norm_num
  have h0src : (0 : ThreeSpace) ∈ c.chart.source :=
    c.closedBall_subset_source (Metric.mem_closedBall_self (by norm_num))
  have h3src : (3 / 4 : ℝ) • s ∈ c.chart.source := by
    refine c.closedBall_subset_source ?_
    rw [Metric.mem_closedBall, dist_zero_right, norm_smul, Real.norm_eq_abs,
      abs_of_pos (by norm_num : (0 : ℝ) < 3 / 4), hnorm]
    norm_num
  let b : OrientedBallEmbedding M.Carrier M.orientation :=
    OrientedBallEmbedding.ofOrientedBallChart c
  let b' : OrientedBallEmbedding M.Carrier M.orientation :=
    OrientedBallEmbedding.ofOrientedBallChart (c.affine s (1 / 8) hr hs)
  have hb : b.chart = c.chart := rfl
  have hb' : b'.chart = (c.affine s (1 / 8) hr hs).chart := rfl
  refine ⟨b, b', {c.chart ((3 / 4 : ℝ) • s)}, isCompact_singleton, ?_, ?_, ?_, ?_⟩
  · rw [hb, Set.disjoint_left]
    rintro y ⟨x, hx, rfl⟩ hy
    rw [Set.mem_singleton_iff] at hy
    have hxsrc : x ∈ c.chart.source :=
      c.closedBall_subset_source (Metric.closedBall_subset_closedBall (by norm_num) hx)
    have hxval : x = (3 / 4 : ℝ) • s := c.chart.toPartialEquiv.injOn hxsrc h3src hy
    have h1 : ‖x‖ ≤ 1 := by simpa [Metric.mem_closedBall, dist_eq_norm] using hx
    rw [hxval] at h1
    have h2 : ‖(3 / 4 : ℝ) • s‖ = 9 / 8 := by
      rw [norm_smul, Real.norm_eq_abs, abs_of_pos (by norm_num : (0 : ℝ) < 3 / 4), hnorm]
      norm_num
    rw [h2] at h1
    norm_num at h1
  · rw [hb', Set.disjoint_left]
    rintro y ⟨x, hx, rfl⟩ hy
    rw [Set.mem_singleton_iff] at hy
    rw [DifferentialGeometry.Topology.OrientedBallChart.affine_apply] at hy
    have hx1 : ‖x‖ ≤ 1 := by simpa [Metric.mem_closedBall, dist_eq_norm] using hx
    have h1src : s + (1 / 8 : ℝ) • x ∈ c.chart.source := by
      refine c.closedBall_subset_source ?_
      rw [Metric.mem_closedBall, dist_zero_right]
      have hbn : ‖(1 / 8 : ℝ) • x‖ = 1 / 8 * ‖x‖ := by
        rw [norm_smul, Real.norm_eq_abs, abs_of_pos (by norm_num : (0 : ℝ) < 1 / 8)]
      calc ‖s + (1 / 8 : ℝ) • x‖ ≤ ‖s‖ + ‖(1 / 8 : ℝ) • x‖ := norm_add_le _ _
        _ = 3 / 2 + 1 / 8 * ‖x‖ := by rw [hbn, hnorm]
        _ ≤ 2 := by nlinarith
    have heq : s + (1 / 8 : ℝ) • x = (3 / 4 : ℝ) • s :=
      c.chart.toPartialEquiv.injOn h1src h3src hy
    have hxval : x = (-2 : ℝ) • s := by
      have h8 : (1 / 8 : ℝ) • x = (3 / 4 : ℝ) • s - s := by
        rw [← heq]
        module
      calc x = (8 : ℝ) • ((1 / 8 : ℝ) • x) := by
            rw [smul_smul, show (8 : ℝ) * (1 / 8) = 1 by norm_num, one_smul]
        _ = (8 : ℝ) • ((3 / 4 : ℝ) • s - s) := by rw [h8]
        _ = (-2 : ℝ) • s := by
            rw [smul_sub, smul_smul]
            module
    have h3 : ‖x‖ = 3 := by
      rw [hxval, norm_smul, Real.norm_eq_abs, abs_of_neg (by norm_num : (-2 : ℝ) < 0), hnorm]
      norm_num
    linarith
  · rw [hb, hb']
    exact ⟨c.chart.map_source h0src, Set.mem_univ _⟩
  · intro h
    have h' : ∀ t ∈ Set.Icc (0 : ℝ) 1,
        (1 - t) • ((c.affine s (1 / 8) hr hs).chart.symm (c.chart (0 : ThreeSpace)))
            + t • (0 : ThreeSpace)
          ∈ (c.affine s (1 / 8) hr hs).chart.source ∩
            (c.affine s (1 / 8) hr hs).chart ⁻¹'
              ({c.chart ((3 / 4 : ℝ) • s)} : Set M.Carrier)ᶜ := h
    have hu : (3 / 4 : ℝ) ∈ Set.Icc (0 : ℝ) 1 := ⟨by norm_num, by norm_num⟩
    have hmem := (h' (3 / 4) hu).2
    rw [Set.mem_preimage] at hmem
    rw [(affineBallChart_centerTube_mem c hr hs hu).2] at hmem
    exact hmem (by simp)

theorem exists_orientedBallEmbedding_ballChartCenterTubeWithin :
    ∃ (b b' : OrientedBallEmbedding
        (DifferentialGeometry.Topology.standardThreeSphereLift.{0}).Carrier
        (DifferentialGeometry.Topology.standardThreeSphereLift.{0}).orientation)
      (C : Set (DifferentialGeometry.Topology.standardThreeSphereLift.{0}).Carrier),
      b.chart (0 : ThreeSpace) ≠ b'.chart (0 : ThreeSpace) ∧ C.Nonempty ∧ IsCompact C ∧
      Disjoint (b.chart '' Metric.closedBall (0 : ThreeSpace) 1) C ∧
      Disjoint (b'.chart '' Metric.closedBall (0 : ThreeSpace) 1) C ∧
      b.chart (0 : ThreeSpace) ∈ b'.chart.target ∧
      ballChartCenterTubeWithin b.toBallChart b'.toBallChart C := by
  let M : DifferentialGeometry.Topology.ClosedOrientedManifold.{0} 3 :=
    DifferentialGeometry.Topology.standardThreeSphereLift.{0}.toClosedOrientedManifold
  let c : DifferentialGeometry.Topology.OrientedBallChart M :=
    DifferentialGeometry.Topology.orientedBallChart
      DifferentialGeometry.Topology.standardThreeSphereLift.{0}
  set s : ThreeSpace := (3 / 2 : ℝ) • EuclideanSpace.single (0 : Fin 3) (1 : ℝ) with hsdef
  have hnorm : ‖s‖ = 3 / 2 := by
    rw [hsdef, norm_smul, Real.norm_eq_abs, abs_of_pos (by norm_num : (0 : ℝ) < 3 / 2)]
    simp
  have hr : (0 : ℝ) < 1 / 8 := by norm_num
  have hs : ‖s‖ + 2 * (1 / 8 : ℝ) ≤ 2 := by rw [hnorm]; norm_num
  have h0src : (0 : ThreeSpace) ∈ c.chart.source :=
    c.closedBall_subset_source (Metric.mem_closedBall_self (by norm_num))
  have hssrc : s ∈ c.chart.source := by
    refine c.closedBall_subset_source ?_
    rw [Metric.mem_closedBall, dist_zero_right, hnorm]
    norm_num
  have h9src : (9 / 8 : ℝ) • s ∈ c.chart.source := by
    refine c.closedBall_subset_source ?_
    rw [Metric.mem_closedBall, dist_zero_right, norm_smul, Real.norm_eq_abs,
      abs_of_pos (by norm_num : (0 : ℝ) < 9 / 8), hnorm]
    norm_num
  let b : OrientedBallEmbedding M.Carrier M.orientation :=
    OrientedBallEmbedding.ofOrientedBallChart c
  let b' : OrientedBallEmbedding M.Carrier M.orientation :=
    OrientedBallEmbedding.ofOrientedBallChart (c.affine s (1 / 8) hr hs)
  have hb : b.chart = c.chart := rfl
  have hb' : b'.chart = (c.affine s (1 / 8) hr hs).chart := rfl
  refine ⟨b, b', {c.chart ((9 / 8 : ℝ) • s)}, ?_, Set.singleton_nonempty _,
    isCompact_singleton, ?_, ?_, ?_, ?_⟩
  · intro hzero
    rw [hb, hb'] at hzero
    rw [DifferentialGeometry.Topology.OrientedBallChart.affine_apply] at hzero
    simp only [smul_zero, add_zero] at hzero
    have heq : (0 : ThreeSpace) = s := c.chart.toPartialEquiv.injOn h0src hssrc hzero
    rw [← heq] at hnorm
    norm_num at hnorm
  · rw [hb, Set.disjoint_left]
    rintro y ⟨x, hx, rfl⟩ hy
    rw [Set.mem_singleton_iff] at hy
    have hxsrc : x ∈ c.chart.source :=
      c.closedBall_subset_source (Metric.closedBall_subset_closedBall (by norm_num) hx)
    have hxval : x = (9 / 8 : ℝ) • s := c.chart.toPartialEquiv.injOn hxsrc h9src hy
    have h1 : ‖x‖ ≤ 1 := by simpa [Metric.mem_closedBall, dist_eq_norm] using hx
    rw [hxval] at h1
    have h2 : ‖(9 / 8 : ℝ) • s‖ = 27 / 16 := by
      rw [norm_smul, Real.norm_eq_abs, abs_of_pos (by norm_num : (0 : ℝ) < 9 / 8), hnorm]
      norm_num
    rw [h2] at h1
    norm_num at h1
  · rw [hb', Set.disjoint_left]
    rintro y ⟨x, hx, rfl⟩ hy
    rw [Set.mem_singleton_iff] at hy
    rw [DifferentialGeometry.Topology.OrientedBallChart.affine_apply] at hy
    have hx1 : ‖x‖ ≤ 1 := by simpa [Metric.mem_closedBall, dist_eq_norm] using hx
    have h1src : s + (1 / 8 : ℝ) • x ∈ c.chart.source := by
      refine c.closedBall_subset_source ?_
      rw [Metric.mem_closedBall, dist_zero_right]
      have hbn : ‖(1 / 8 : ℝ) • x‖ = 1 / 8 * ‖x‖ := by
        rw [norm_smul, Real.norm_eq_abs, abs_of_pos (by norm_num : (0 : ℝ) < 1 / 8)]
      calc ‖s + (1 / 8 : ℝ) • x‖ ≤ ‖s‖ + ‖(1 / 8 : ℝ) • x‖ := norm_add_le _ _
        _ = 3 / 2 + 1 / 8 * ‖x‖ := by rw [hbn, hnorm]
        _ ≤ 2 := by nlinarith
    have heq : s + (1 / 8 : ℝ) • x = (9 / 8 : ℝ) • s :=
      c.chart.toPartialEquiv.injOn h1src h9src hy
    have h8 : (1 / 8 : ℝ) • x = (1 / 8 : ℝ) • s := by
      have h3 : s + (1 / 8 : ℝ) • s = (9 / 8 : ℝ) • s := by module
      rw [← h3] at heq
      exact add_left_cancel heq
    have hxval : x = s := by
      have h := congrArg (fun z : ThreeSpace => (8 : ℝ) • z) h8
      simpa only [smul_smul, show (8 : ℝ) * (1 / 8) = 1 by norm_num, one_smul] using h
    rw [hxval] at hx1
    rw [hnorm] at hx1
    norm_num at hx1
  · rw [hb, hb']
    exact ⟨c.chart.map_source h0src, Set.mem_univ _⟩
  · intro v hv
    change (1 - v) • ((c.affine s (1 / 8) hr hs).chart.symm (c.chart (0 : ThreeSpace)))
        + v • (0 : ThreeSpace)
      ∈ (c.affine s (1 / 8) hr hs).chart.source ∩
        (c.affine s (1 / 8) hr hs).chart ⁻¹' ({c.chart ((9 / 8 : ℝ) • s)} : Set M.Carrier)ᶜ
    obtain ⟨hsrc, happly⟩ := affineBallChart_centerTube_mem c hr hs hv
    refine ⟨hsrc, ?_⟩
    rw [Set.mem_preimage, happly]
    intro hmem
    rw [Set.mem_singleton_iff] at hmem
    have hvsrc : v • s ∈ c.chart.source := by
      refine c.closedBall_subset_source ?_
      rw [Metric.mem_closedBall, dist_zero_right, norm_smul, Real.norm_eq_abs, abs_of_nonneg hv.1]
      nlinarith [hv.2, norm_nonneg s]
    have hvs : v • s = (9 / 8 : ℝ) • s := c.chart.toPartialEquiv.injOn hvsrc h9src hmem
    have hn : ‖v • s‖ = 27 / 16 := by
      rw [hvs, norm_smul, Real.norm_eq_abs, abs_of_pos (by norm_num : (0 : ℝ) < 9 / 8), hnorm]
      norm_num
    have hle : ‖v • s‖ ≤ 3 / 2 := by
      rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg hv.1, hnorm]
      nlinarith [hv.2]
    linarith

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
