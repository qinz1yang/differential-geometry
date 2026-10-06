import DifferentialGeometry.Topology.MetricSpace.BallPasting
import DifferentialGeometry.Geometry.MinimalSurface.Plateau.MorreyDisk
import DifferentialGeometry.Geometry.Measure.Area.ManifoldLipschitz
import DifferentialGeometry.Geometry.Measure.Area.RegionCongruence

set_option autoImplicit false

noncomputable section

open Set Filter MeasureTheory Metric Bundle Manifold
open DifferentialGeometry.Topology
open scoped Manifold ContDiff Topology NNReal ENNReal

namespace DifferentialGeometry.Geometry

variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [TopologicalSpace M] [ChartedSpace E M]
  [IsManifold 𝓘(ℝ, E) ∞ M] [T3Space M]

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
/-- Pasting a metric Lipschitz filling into an interior source ball preserves the
original trace and gives the subtraction/addition identity for actual area. -/
theorem exists_disk_area_replacement_of_eqOn_sphere
    (g : SmoothRiemannianMetric 𝓘(ℝ, E) M)
    (u : C(closedDisk, M)) {v : ℂ → M} {K L : ℝ≥0}
    (hu : ∀ z z', riemannianEDistOf g (u z) (u z') ≤ (K : ℝ≥0∞) * edist z z')
    {b : ℂ} {r : ℝ} (hbr : ‖b‖ + r < 1)
    (hv : ∀ z ∈ closedBall b r, ∀ z' ∈ closedBall b r,
      riemannianEDistOf g (v z) (v z') ≤ (L : ℝ≥0∞) * edist z z')
    (heq : ∀ z ∈ sphere b r, v z = diskExtension u z) :
    ∃ w : C(closedDisk, M),
      (∀ z z', riemannianEDistOf g (w z) (w z') ≤
        ((L + K : ℝ≥0) : ℝ≥0∞) * edist z z') ∧
      (∀ z : closedDisk, dist (z : ℂ) b ≤ r → w z = v z) ∧
      (∀ z : closedDisk, r ≤ dist (z : ℂ) b → w z = u z) ∧
      diskTrace w = diskTrace u ∧
      riemannianDiskArea g w = riemannianDiskArea g u -
        riemannianArea g (diskExtension u) (closedBall b r) +
          riemannianArea g v (closedBall b r) := by
  classical
  let : RiemannianBundle (TangentSpace 𝓘(ℝ, E) : M → Type _) := ⟨g.toRiemannianMetric⟩
  have : IsContinuousRiemannianBundle E (TangentSpace 𝓘(ℝ, E) : M → Type _) :=
    ⟨g.inner, g.contMDiff.continuous, fun _ _ _ => rfl⟩
  let : PseudoEMetricSpace M := .ofRiemannianMetric 𝓘(ℝ, E) M
  let U : ℂ → M := diskExtension u
  let f : ℂ → M := (closedBall b r).piecewise v U
  have hULip : LipschitzWith K U := diskExtension_riemannian_lipschitz g hu
  have hvLip : LipschitzOnWith L v (closedBall b r) := hv
  have hfLip : LipschitzWith (L + K) f :=
    DifferentialGeometry.Analysis.lipschitzWith_piecewise_closedBall_of_eqOn_sphere
      hvLip hULip.lipschitzOnWith heq
  let w : C(closedDisk, M) := ⟨fun z => f z, hfLip.continuous.comp continuous_subtype_val⟩
  have hwLip : ∀ z z', riemannianEDistOf g (w z) (w z') ≤
      ((L + K : ℝ≥0) : ℝ≥0∞) * edist z z' := fun z z' => hfLip z z'
  have hball : closedBall b r ⊆ ball (0 : ℂ) 1 := by
    intro z hz
    rw [mem_ball, dist_zero_right]
    have hn : ‖z‖ ≤ dist z b + ‖b‖ := by
      simpa only [dist_eq_norm, sub_add_cancel] using norm_add_le (z - b) b
    exact hn.trans_lt (by have hd := mem_closedBall.mp hz; linarith)
  have hsubset : closedBall b r ⊆ closedBall (0 : ℂ) 1 :=
    hball.trans ball_subset_closedBall
  have hinner (z : closedDisk) (hz : dist (z : ℂ) b ≤ r) : w z = v z := by
    change (closedBall b r).piecewise v U z = v z
    exact piecewise_eq_of_mem _ _ _ (mem_closedBall.mpr hz)
  have houter (z : closedDisk) (hz : r ≤ dist (z : ℂ) b) : w z = u z := by
    by_cases hzr : dist (z : ℂ) b = r
    · rw [hinner z hzr.le, heq z (mem_sphere.mpr hzr)]
      exact diskExtension_coe u z
    · have hn : (z : ℂ) ∉ closedBall b r := not_le.mpr (lt_of_le_of_ne hz (Ne.symm hzr))
      change (closedBall b r).piecewise v U z = u z
      rw [piecewise_eq_of_notMem _ _ _ hn]
      exact diskExtension_coe u z
  have htrace : diskTrace w = diskTrace u := by
    ext θ
    change w (diskBoundary θ) = u (diskBoundary θ)
    apply houter
    have hnorm : ‖((diskBoundary θ : closedDisk) : ℂ)‖ = 1 := Circle.norm_coe _
    by_contra hnot
    have hin := hball (show (diskBoundary θ : ℂ) ∈ closedBall b r from (not_le.mp hnot).le)
    have hn : ‖(diskBoundary θ : ℂ)‖ < 1 := by
      simpa only [mem_ball, dist_zero_right] using hin
    exact (not_lt_of_ge hnorm.ge) hn
  have hinArea : riemannianArea g (diskExtension w) (closedBall b r) =
      riemannianArea g v (closedBall b r) := by
    apply riemannianArea_congr_on_closedBall g
    intro z hz
    let q : closedDisk := ⟨z, hsubset hz⟩
    exact (diskExtension_coe w q).trans (hinner q (mem_closedBall.mp hz))
  have houtArea :
      (∫ z in closedBall (0 : ℂ) 1 \ closedBall b r,
        riemannianAreaDensity g (diskExtension w) z) =
      ∫ z in closedBall (0 : ℂ) 1 \ closedBall b r,
        riemannianAreaDensity g (diskExtension u) z := by
    have hzin : ∀ᵐ z ∂volume.restrict (closedBall (0 : ℂ) 1 \ closedBall b r),
        z ∈ ball (0 : ℂ) 1 :=
      ae_restrict_of_ae_restrict_of_subset sdiff_subset ae_disk_interior
    apply integral_congr_ae
    filter_upwards [hzin,
      ae_restrict_mem (measurableSet_closedBall.diff measurableSet_closedBall)] with z hz hzd
    apply riemannianAreaDensity_congr g
    filter_upwards [(isOpen_ball.inter isClosed_closedBall.isOpen_compl).mem_nhds
      ⟨hz, hzd.2⟩] with y hy
    let q : closedDisk := ⟨y, ball_subset_closedBall hy.1⟩
    exact (diskExtension_coe w q).trans
      ((houter q (le_of_lt (not_le.mp hy.2))).trans (diskExtension_coe u q).symm)
  have hiu := integrable_riemannianDiskAreaDensity g hu
  have hiw := integrable_riemannianDiskAreaDensity g hwLip
  have hsu := setIntegral_sdiff measurableSet_closedBall hiu hsubset
  have hsw := setIntegral_sdiff measurableSet_closedBall hiw hsubset
  change (∫ z in closedBall b r, riemannianAreaDensity g (diskExtension w) z) =
    (∫ z in closedBall b r, riemannianAreaDensity g v z) at hinArea
  rw [houtArea, hinArea, hsu] at hsw
  refine ⟨w, hwLip, hinner, houter, htrace, ?_⟩
  change (∫ z in closedBall (0 : ℂ) 1, riemannianAreaDensity g (diskExtension w) z) =
    (∫ z in closedBall (0 : ℂ) 1, riemannianAreaDensity g (diskExtension u) z) -
      (∫ z in closedBall b r, riemannianAreaDensity g (diskExtension u) z) +
        ∫ z in closedBall b r, riemannianAreaDensity g v z
  linarith

/-- A metric Lipschitz Morrey disk minimizes the original-metric area on every
interior source ball against metric Lipschitz fillings with the same sphere trace.
No immersion or branch exclusion is needed for this local comparison. -/
theorem IsMorreyDisk.area_closedBall_le_of_eqOn_sphere
    {g : SmoothRiemannianMetric 𝓘(ℝ, E) M} {γ : freeLoop M}
    {u : C(closedDisk, M)} (hu : IsMorreyDisk g γ u) {K : ℝ≥0}
    (huLip : ∀ z z', riemannianEDistOf g (u z) (u z') ≤
      (K : ℝ≥0∞) * edist z z')
    {v : ℂ → M} {L : ℝ≥0}
    {b : ℂ} {r : ℝ} (hbr : ‖b‖ + r < 1)
    (hv : ∀ z ∈ closedBall b r, ∀ z' ∈ closedBall b r,
      riemannianEDistOf g (v z) (v z') ≤ (L : ℝ≥0∞) * edist z z')
    (heq : ∀ z ∈ sphere b r, v z = diskExtension u z) :
    riemannianArea g (diskExtension u) (closedBall b r) ≤
      riemannianArea g v (closedBall b r) := by
  obtain ⟨w, hwLip, _, _, htrace, harea⟩ :=
    exists_disk_area_replacement_of_eqOn_sphere g u huLip hbr hv heq
  have hwTrace : DiskWeakJordanTrace γ w := by
    obtain ⟨σ, hσ, ht⟩ := hu.trace
    exact ⟨σ, hσ, htrace.trans ht⟩
  have hmin := hu.minimizesLipschitz w hwTrace ⟨L + K, hwLip⟩
  linarith

end DifferentialGeometry.Geometry
