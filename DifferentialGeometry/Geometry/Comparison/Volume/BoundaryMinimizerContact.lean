import DifferentialGeometry.Geometry.Comparison.Volume.BoundaryIntrinsicSegment
import DifferentialGeometry.Geometry.Metric.Distance.InducedMetricSpace
import DifferentialGeometry.Geometry.Geodesic.Minimizing.MetricSegmentRegularity
import DifferentialGeometry.Geometry.Metric.Distance.LocalBall
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
An actual unit-speed intrinsic metric segment cannot have interior-time contact with a
strictly convex defining-function boundary. Its ambient smoothness is derived from distances.
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
theorem boundary_intrinsic_segment_zero_contact
    (g : SmoothRiemannianMetric I M) (G : SmoothRiemannianMetric 𝓘(ℝ, E) E)
    (p : M) (U : TopologicalSpace.Opens E) (hpU : extChartAt I p p ∈ U)
    (hU : (U : Set E) ⊆ I.symm ⁻¹' (chartAt H p).target)
    (hmetric : ∀ y ∈ (U : Set E) ∩ range I, ∀ v w : E,
      G.inner y v w = metricFlatModelInChart g p y v w)
    (u : E → ℝ) (hu : ContDiff ℝ ∞ u) (hp : u (extChartAt I p p) = 0)
    (hdomain : ∀ y ∈ U, y ∈ range I ↔ 0 ≤ u y)
    (hinterior : ∀ y ∈ U, y ∈ interior (range I) ↔ 0 < u y)
    (hH : ∀ v : E, fderiv ℝ u (extChartAt I p p) v = 0 → v ≠ 0 →
      abstractHessian G u (extChartAt I p p) v v < 0)
    (f : ℝ → M) (t R : ℝ) (hft : f t = p) (hR : 0 < R)
    (hdist : ∀ s ∈ Icc (-R) R, ∀ v ∈ Icc (-R) R,
      riemannianEDistOf g (f (t + s)) (f (t + v)) = ENNReal.ofReal |s - v|) : False := by
  obtain ⟨r, hr, hlocal⟩ := exists_boundaryChart_intrinsic_segment g G p U hpU hU
    hmetric u hu hp hdomain hinterior hH
  have hnb : (extChartAt I p).source ∩ (extChartAt I p) ⁻¹' (U : Set E) ∈ 𝓝 p :=
    Filter.inter_mem (extChartAt_source_mem_nhds p)
      ((continuousAt_extChartAt p).preimage_mem_nhds (U.isOpen.mem_nhds hpU))
  obtain ⟨rS, hrS, hsource⟩ :=
    Geometry.Metric.exists_pos_riemannianClosedBallOf_subset_of_mem_nhds g p hnb
  let S : ℝ := min R (min r rS) / 2
  have hS : 0 < S := half_pos (lt_min hR (lt_min hr hrS))
  have hSR : S ≤ R := (half_le_self (lt_min hR (lt_min hr hrS)).le).trans
    (min_le_left _ _)
  have hSr : S ≤ r := ((half_le_self (lt_min hR (lt_min hr hrS)).le).trans
    (min_le_right _ _)).trans (min_le_left _ _)
  have hSrS : S ≤ rS := ((half_le_self (lt_min hR (lt_min hr hrS)).le).trans
    (min_le_right _ _)).trans (min_le_right _ _)
  have hparam {s : ℝ} (hs : s ∈ Icc (-S) S) : s ∈ Icc (-R) R :=
    ⟨by linarith only [hs.1, hSR], hs.2.trans hSR⟩
  have hball (s : ℝ) (hs : s ∈ Icc (-S) S) :
      f (t + s) ∈ riemannianClosedBallOf g p S := by
    have hh := hdist 0 ⟨by linarith, hR.le⟩ s (hparam hs)
    rw [add_zero, hft, zero_sub, abs_neg] at hh
    change riemannianEDistOf g p (f (t + s)) ≤ ENNReal.ofReal S
    rw [hh]
    exact ENNReal.ofReal_le_ofReal (abs_le.mpr hs)
  have hstay (s : ℝ) (hs : s ∈ Icc (-S) S) :
      f (t + s) ∈ (extChartAt I p).source ∧ extChartAt I p (f (t + s)) ∈ U :=
    hsource ((hball s hs).trans (ENNReal.ofReal_le_ofReal hSrS))
  let ζ : ℝ → E := (extChartAt I p) ∘ f
  have hζdist (s : ℝ) (hs : s ∈ Icc (-S) S) (v : ℝ) (hv : v ∈ Icc (-S) S) :
      riemannianEDistOf G (ζ (t + s)) (ζ (t + v)) = ENNReal.ofReal |s - v| := by
    have hsball : f (t + s) ∈ riemannianClosedBallOf g p r :=
      (hball s hs).trans (ENNReal.ofReal_le_ofReal hSr)
    have hvball : f (t + v) ∈ riemannianClosedBallOf g p r :=
      (hball v hv).trans (ENNReal.ofReal_le_ofReal hSr)
    have heq : riemannianEDistOf G (ζ (t + s)) (ζ (t + v)) =
        riemannianEDistOf g (f (t + s)) (f (t + v)) := by
      by_cases hsame : f (t + s) = f (t + v)
      · simp only [ζ, Function.comp_apply, hsame, riemannianEDistOf_self]
      · exact (hlocal _ hsball _ hvball hsame).1
    exact heq.trans (hdist s (hparam hs) v (hparam hv))
  let ambientDistance : MetricSpace E := inducedMetricSpace G
  have hcompat : ∀ x y : E, edist x y = riemannianEDistOf G x y :=
    inducedMetricSpace_edist G
  have hζdistReal : ∀ s ∈ Icc (-S) S, ∀ v ∈ Icc (-S) S,
      ambientDistance.dist (ζ (t + s)) (ζ (t + v)) = |s - v| := by
    intro s hs v hv
    change (riemannianEDistOf G (ζ (t + s)) (ζ (t + v))).toReal = _
    rw [hζdist s hs v hv, ENNReal.toReal_ofReal (abs_nonneg _)]
  obtain ⟨hζ, hgeo, hspeed⟩ :=
    contMDiffAt_and_geodesicEquationAt_of_metric_segment G hcompat ζ t hS hζdistReal
  have hvelocity : mfderiv 𝓘(ℝ) 𝓘(ℝ, E) ζ t 1 = deriv ζ t := by
    rw [mfderiv_eq_fderiv]
    change fderiv ℝ ζ t 1 = deriv ζ t
    exact fderiv_apply_one_eq_deriv
  have hvel : deriv ζ t ≠ 0 := by
    intro hz
    have hmetricZero : G.inner (ζ t) (0 : TangentSpace 𝓘(ℝ, E) (ζ t))
        (0 : TangentSpace 𝓘(ℝ, E) (ζ t)) = 0 :=
      congrArg (fun B : TangentSpace 𝓘(ℝ, E) (ζ t) →L[ℝ] ℝ => B 0)
        ((G.inner (ζ t)).map_zero)
    rw [hvelocity, hz] at hspeed
    exact zero_ne_one (hmetricZero.symm.trans hspeed)
  have hinside : ∀ᶠ s in 𝓝 t, 0 ≤ u (ζ s) := by
    filter_upwards [Metric.ball_mem_nhds t hS] with s hs
    have habs : |s - t| < S := by simpa only [Metric.mem_ball, Real.dist_eq] using hs
    have hss : s - t ∈ Icc (-S) S := (abs_le.mp habs.le)
    obtain ⟨hsS, hsU⟩ := hstay (s - t) hss
    rw [add_sub_cancel] at hsS hsU
    exact (hdomain _ hsU).mp (extChartAt_target_subset_range p
      ((extChartAt I p).map_source hsS))
  have hζpoint : ζ t = extChartAt I p p := by simp only [ζ, Function.comp_apply, hft]
  apply boundary_geodesic_zero_contact G u ζ t
    (hu.of_le (by simp)).contDiffAt (hζ.of_le (by simp)).contDiffAt hgeo
    (hζpoint ▸ hp) hinside hvel
  intro v htangent hv
  exact hζpoint.symm ▸ hH v (hζpoint ▸ htangent) hv

end DifferentialGeometry.Geometry.Riemannian.VolumeComparison
