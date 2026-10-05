import DifferentialGeometry.Geometry.Comparison.Volume.BoundaryChartDistance
import DifferentialGeometry.Geometry.Comparison.Volume.BoundaryChartGeodesic
import DifferentialGeometry.Geometry.Comparison.Volume.BoundaryConvexSegment
import DifferentialGeometry.Geometry.Metric.Distance.LocalBall
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
Original intrinsic minimizing segments are produced from actual convex ambient chart
segments, with minimum original length, interior membership and original geodesic equation.
-/

set_option autoImplicit false

noncomputable section

open Manifold Set Bundle MeasureTheory
open scoped Manifold ContDiff Topology ENNReal
open DifferentialGeometry.Geometry.Connection

namespace DifferentialGeometry.Geometry.Riemannian.VolumeComparison

variable {E : Type*} [ambientNorm : NormedAddCommGroup E]
  [ambientSpace : NormedSpace ℝ E] {H : Type*}
  [modelTopology : TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [manifoldTopology : TopologicalSpace M]
  [manifoldCharts : ChartedSpace H M] [manifoldSmooth : IsManifold I ∞ M]

variable [ambientFinite : FiniteDimensional ℝ E] [manifoldT2 : T2Space M]

variable [ambientDimension : NeZero (Module.finrank ℝ E)]

open DifferentialGeometry.Geometry.Riemannian.Geodesic

attribute [-instance] DifferentialGeometry.Tensor0SBundle.tangentSpaceNormedAddCommGroup
  DifferentialGeometry.Tensor0SBundle.tangentSpaceNormedSpace in
theorem exists_boundaryChart_intrinsic_segment
    (g : SmoothRiemannianMetric I M) (G : SmoothRiemannianMetric 𝓘(ℝ, E) E)
    (p : M) (U : TopologicalSpace.Opens E) (hpU : extChartAt I p p ∈ U)
    (hU : (U : Set E) ⊆ I.symm ⁻¹' (chartAt H p).target)
    (hmetric : ∀ y ∈ (U : Set E) ∩ range I, ∀ v w : E,
      G.inner y v w = metricFlatModelInChart g p y v w)
    (u : E → ℝ) (hu : ContDiff ℝ ∞ u) (hp : u (extChartAt I p p) = 0)
    (hdomain : ∀ y ∈ U, y ∈ range I ↔ 0 ≤ u y)
    (hinterior : ∀ y ∈ U, y ∈ interior (range I) ↔ 0 < u y)
    (hH : ∀ v : E, fderiv ℝ u (extChartAt I p p) v = 0 → v ≠ 0 →
      abstractHessian G u (extChartAt I p p) v v < 0) :
    ∃ r : ℝ, 0 < r ∧ ∀ a ∈ riemannianClosedBallOf g p r,
      ∀ b ∈ riemannianClosedBallOf g p r, a ≠ b →
      riemannianEDistOf G (extChartAt I p a) (extChartAt I p b) =
        riemannianEDistOf g a b ∧ ∃ γ : ℝ → M,
        γ 0 = a ∧ γ 1 = b ∧ ContMDiffOn 𝓘(ℝ) I ∞ γ (Icc 0 1) ∧
        metricPathELength g γ 0 1 = riemannianEDistOf g a b ∧
        ∀ t ∈ Ioo (0 : ℝ) 1, I.IsInteriorPoint (γ t) ∧ HasGeodesicEquationAt g γ t := by
  obtain ⟨rD, hrD, hdist⟩ := exists_boundaryChart_edist_le g G p U hpU hmetric
  obtain ⟨rA, hrA, hsegments⟩ :=
    exists_boundary_convex_segment G u hu (extChartAt I p p) hp U U.isOpen hpU hH
  have hnb : (extChartAt I p).source ∩ (extChartAt I p) ⁻¹' (U : Set E) ∈ 𝓝 p :=
    Filter.inter_mem (extChartAt_source_mem_nhds p)
      ((continuousAt_extChartAt p).preimage_mem_nhds (U.isOpen.mem_nhds hpU))
  obtain ⟨rS, hrS, hsource⟩ :=
    Geometry.Metric.exists_pos_riemannianClosedBallOf_subset_of_mem_nhds g p hnb
  let r : ℝ := min rD (min rA rS)
  have hr : 0 < r := lt_min hrD (lt_min hrA hrS)
  have hrDle : r ≤ rD := min_le_left _ _
  have hrAle : r ≤ rA := (min_le_right _ _).trans (min_le_left _ _)
  have hrSle : r ≤ rS := (min_le_right _ _).trans (min_le_right _ _)
  have hpball : p ∈ riemannianClosedBallOf g p rD := by
    change riemannianEDistOf g p p ≤ ENNReal.ofReal rD
    rw [riemannianEDistOf_self]
    exact bot_le
  refine ⟨r, hr, ?_⟩
  intro a ha b hb hab
  have hsmall {x : M} (hx : x ∈ riemannianClosedBallOf g p r) :
      x ∈ riemannianClosedBallOf g p rD ∧
      x ∈ (extChartAt I p).source ∧ extChartAt I p x ∈ U ∧
      extChartAt I p x ∈ riemannianClosedBallOf G (extChartAt I p p) rA := by
    have hxD : x ∈ riemannianClosedBallOf g p rD :=
      hx.trans (ENNReal.ofReal_le_ofReal hrDle)
    have hxS : x ∈ riemannianClosedBallOf g p rS :=
      hx.trans (ENNReal.ofReal_le_ofReal hrSle)
    have hc := hsource hxS
    refine ⟨hxD, hc.1, hc.2, ?_⟩
    exact (hdist p hpball x hxD).trans (hx.trans (ENNReal.ofReal_le_ofReal hrAle))
  obtain ⟨haD, haS, haU, haA⟩ := hsmall ha
  obtain ⟨hbD, hbS, hbU, hbA⟩ := hsmall hb
  have hcoordNe : extChartAt I p a ≠ extChartAt I p b := by
    intro heq
    have hh := congrArg (extChartAt I p).symm heq
    rw [(extChartAt I p).left_inv haS, (extChartAt I p).left_inv hbS] at hh
    exact hab hh
  have hua : 0 ≤ u (extChartAt I p a) :=
    (hdomain _ haU).mp (extChartAt_target_subset_range p ((extChartAt I p).map_source haS))
  have hub : 0 ≤ u (extChartAt I p b) :=
    (hdomain _ hbU).mp (extChartAt_target_subset_range p ((extChartAt I p).map_source hbS))
  obtain ⟨η, hstart, hend, hη, hmem, hlength, hgeo, hpos⟩ :=
    hsegments _ haA _ hbA hcoordNe hua hub
  have htarget : ∀ t ∈ Icc (0 : ℝ) 1, η t ∈ (extChartAt I p).target := by
    intro t ht
    rw [extChartAt_target]
    refine ⟨hU (hmem t ht), (hdomain _ (hmem t ht)).mpr ?_⟩
    by_cases hzero : t = 0
    · simpa only [hzero, hstart] using hua
    by_cases hone : t = 1
    · simpa only [hone, hend] using hub
    exact (hpos t ⟨lt_of_le_of_ne ht.1 (Ne.symm hzero), lt_of_le_of_ne ht.2 hone⟩).le
  have htargetInt : ∀ t ∈ Ioo (0 : ℝ) 1, η t ∈ interior (extChartAt I p).target := by
    intro t ht
    have hi : η t ∈ interior (range I) :=
      (hinterior _ (hmem t ⟨ht.1.le, ht.2.le⟩)).mpr (hpos t ht)
    apply mem_interior_iff_mem_nhds.mpr
    apply Filter.mem_of_superset ((U.isOpen.inter isOpen_interior).mem_nhds
      ⟨hmem t ⟨ht.1.le, ht.2.le⟩, hi⟩)
    intro y hy
    rw [extChartAt_target]
    exact ⟨hU hy.1, interior_subset hy.2⟩
  let γ : ℝ → M := (extChartAt I p).symm ∘ η
  have hγ : ContMDiffOn 𝓘(ℝ) I ∞ γ (Icc 0 1) :=
    (contMDiffOn_extChartAt_symm p).comp hη.contMDiffOn htarget
  have hγstart : γ 0 = a := by
    dsimp only [γ, Function.comp_apply]
    rw [hstart, (extChartAt I p).left_inv haS]
  have hγend : γ 1 = b := by
    dsimp only [γ, Function.comp_apply]
    rw [hend, (extChartAt I p).left_inv hbS]
  have hγlength : metricPathELength g γ 0 1 = riemannianEDistOf G
      (extChartAt I p a) (extChartAt I p b) := by
    exact (boundaryChart_symm_metricPathELength g G p η 0 1
      (hη.of_le (by simp)).contMDiffOn htargetInt (by
        intro t ht
        ext v w
        exact hmetric _ ⟨hmem t ⟨ht.1.le, ht.2.le⟩,
          extChartAt_target_subset_range p (htarget t ⟨ht.1.le, ht.2.le⟩)⟩ v w)).trans hlength
  have hlower := edistOf_le_metricPathELength g zero_le_one (hγ.of_le (by simp))
  rw [hγstart, hγend] at hlower
  refine ⟨le_antisymm (hdist a haD b hbD) (hlower.trans_eq hγlength),
    γ, hγstart, hγend, hγ, le_antisymm
    (hγlength.le.trans (hdist a haD b hbD)) hlower, ?_⟩
  intro t ht
  constructor
  · exact DifferentialGeometry.Manifold.isInteriorPoint_of_model_partialDiffeomorph I ∞
      (DifferentialGeometry.Manifold.interiorChart I ∞ p).symm (by simp) (htargetInt t ht)
  · exact boundaryChart_geodesicEquation g p G U hmetric η t
      ⟨hmem t ⟨ht.1.le, ht.2.le⟩, htargetInt t ht⟩ (hη t)
      (hgeo t ⟨ht.1.le, ht.2.le⟩)

end DifferentialGeometry.Geometry.Riemannian.VolumeComparison
