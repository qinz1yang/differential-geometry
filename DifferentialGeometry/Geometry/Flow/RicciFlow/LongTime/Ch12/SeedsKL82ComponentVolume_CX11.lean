import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch12.SeedsKL82BallVolume_O11
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch12.SeedsKL82EventDistance_CX11
import DifferentialGeometry.Geometry.Metric.ConnectedComponentDistance
import DifferentialGeometry.Geometry.Measure.OpenSubtypeVolume
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch12.InteriorScaleMain

set_option autoImplicit false

noncomputable section

open Set Manifold DifferentialGeometry
  DifferentialGeometry.Geometry.Curvature DifferentialGeometry.Geometry.Riemannian
  DifferentialGeometry.Geometry.Collapse
  DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
open scoped Manifold ContDiff ENNReal

namespace GC.LongTime.Ch12

universe u

variable {M : Type u} [TopologicalSpace M] [ChartedSpace ThreeSpace M]
  [IsManifold ThreeModel ∞ M] [T2Space M] [SigmaCompactSpace M]

/-- O11's local lower volume comparison on a possibly disconnected stage. All
balls and measures are the original ambient ones; only the proof passes to a component. -/
theorem ballVolume_small_of_sec_component_CX11 (g : SmoothRiemannianMetric ThreeModel M)
    (hg : RiemannianMetricComplete g) (p : M)
    {q w s R : ℝ} (hq : 0 ≤ q) (hs : 0 < s) (hsR : s ≤ R)
    (hsec : ∀ z ∈ riemannianBallOf g p R, SectionalBoundedBelowAt g z (-(q ^ 2)))
    (hvol : ENNReal.ofReal (w * R ^ 3) ≤ ballVolume g p R) :
    ENNReal.ofReal (w * s ^ 3 / Real.exp (2 * q * R)) ≤ ballVolume g p s := by
  let C := connectedComponentOpen (I := ThreeModel) p
  let : ConnectedSpace C := connectedComponentOpen_connectedSpace (I := ThreeModel) p
  let : SigmaCompactSpace C :=
    (show IsClosed (C : Set M) from isClosed_connectedComponent).sigmaCompactSpace
  let pC : C := ⟨p, mem_connectedComponent⟩
  have hgC := Geometry.Metric.riemannianMetricComplete_restrictOpen_connCompOpen g p hg
  have hball (r : ℝ) : (Subtype.val : C → M) ⁻¹' riemannianBallOf g p r =
      riemannianBallOf (g.restrictOpen C) pC r := by
    ext z
    change riemannianEDistOf g p z < _ ↔
      riemannianEDistOf (g.restrictOpen C) pC z < _
    rw [Geometry.Metric.edistOf_restrictOpen_connCompOpen]
  have hvolume (r : ℝ) : ballVolume (g.restrictOpen C) pC r = ballVolume g p r := by
    let : MeasurableSpace M := borel M
    let : BorelSpace M := ⟨rfl⟩
    have hm := Geometry.Measure.riemannianVolumeMeasure_restrictOpen_preimage_of_subset g C
      (isOpen_riemannianBallOf g p r).measurableSet
      (Geometry.Metric.edistOf_ball_subset_connCompOpen g p r)
    simpa only [hball, ballVolume] using hm
  have hsecC : ∀ z ∈ riemannianBallOf (g.restrictOpen C) pC R,
      SectionalBoundedBelowAt (g.restrictOpen C) z (-(q ^ 2)) := by
    intro z hz
    rw [sectionalBoundedBelowAt_restrictOpen_iff_T2]
    rw [← hball] at hz
    exact hsec z hz
  rw [← hvolume R] at hvol
  rw [← hvolume s]
  exact ballVolume_small_of_sec_O11 _ hgC (by simp [ThreeSpace]) pC hq hs hsR hsecC hvol

/-- The recentering step in KL82 point picking: a point in the three-eighths
ball sees the known quarter-ball volume inside its five-eighths ball. -/
theorem ballVolume_recenter_lower_CX11 (g : SmoothRiemannianMetric ThreeModel M)
    (hg : RiemannianMetricComplete g) (p x : M)
    {r w s : ℝ} (hr : 0 < r) (hs : 0 < s) (hsr : s ≤ 5 * r / 8)
    (hx : x ∈ riemannianBallOf g p (3 * r / 8))
    (hsec : ∀ z ∈ riemannianBallOf g p r, SectionalBoundedBelowAt g z (-(r ^ 2)⁻¹))
    (hvol : ENNReal.ofReal (w * (r / 4) ^ 3 / 10) ≤ ballVolume g p (r / 4)) :
    ENNReal.ofReal ((4 * w / 625) * s ^ 3 / Real.exp (5 / 4)) ≤ ballVolume g x s := by
  have hsub : riemannianBallOf g p (r / 4) ⊆ riemannianBallOf g x (5 * r / 8) := by
    intro z hz
    have hxp : riemannianEDistOf g x p < ENNReal.ofReal (3 * r / 8) := by
      rw [riemannianEDistOf_comm]
      exact hx
    have hh := (riemannianEDistOf_triangle g x p z).trans_lt (ENNReal.add_lt_add hxp hz)
    rw [← ENNReal.ofReal_add (by positivity) (by positivity)] at hh
    change riemannianEDistOf g x z < ENNReal.ofReal (5 * r / 8)
    convert hh using 1
    congr 1
    ring
  have hbig : riemannianBallOf g x (5 * r / 8) ⊆ riemannianBallOf g p r := by
    intro z hz
    have hh := (riemannianEDistOf_triangle g p x z).trans_lt (ENNReal.add_lt_add hx hz)
    rw [← ENNReal.ofReal_add (by positivity) (by positivity)] at hh
    change riemannianEDistOf g p z < ENNReal.ofReal r
    convert hh using 1
    congr 1
    ring
  have hv : ENNReal.ofReal ((4 * w / 625) * (5 * r / 8) ^ 3) ≤
      ballVolume g x (5 * r / 8) := by
    have he : (4 * w / 625) * (5 * r / 8) ^ 3 = w * (r / 4) ^ 3 / 10 := by ring
    rw [he]
    exact hvol.trans (MeasureTheory.measure_mono hsub)
  have hh := ballVolume_small_of_sec_component_CX11 g hg x (q := r⁻¹) (inv_nonneg.mpr hr.le)
    hs hsr (fun z hz => by simpa only [inv_pow] using hsec z (hbig hz)) hv
  have he : 2 * r⁻¹ * (5 * r / 8) = (5 / 4 : ℝ) := by field_simp; norm_num
  rwa [he] at hh

end GC.LongTime.Ch12
