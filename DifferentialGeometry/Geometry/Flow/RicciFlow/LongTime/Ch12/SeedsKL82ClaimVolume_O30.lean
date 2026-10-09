import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch12.SeedsKL82ComponentVolume_CX11

/-!
# CH12-O30, G1b: recentred local volume for the selected point of claim (C)

Source: corrected w-dependent local variant of KL 82.1 / Perelman II.6.5 (volume step of the
claim); not a verbatim transcription.  The reference PDFs named in AGENTS.md are not on this
machine; locators follow the CX11 report and the DELIVERIES records.

The point selected by `kl82_select_O30` lies in the `7r/16`-ball, outside the `3r/8` range of
`ballVolume_recenter_lower_CX11`.  `ballVolume_recentre_far_O30` recentres the quarter-ball
volume to any point of the `15r/32`-ball, at all radii `s ≤ 17r/32`, using O11's local lower
volume comparison (`ballVolume_small_of_sec_component_CX11`) twice: from `B(p, r/4)` down to
`B(p, r/16)`, and from `B(x, 17r/32) ⊇ B(p, r/16)` down to `B(x, s)`.
-/

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

/-- Recentring the quarter-ball volume to the `15r/32`-ball, at all radii `s ≤ 17r/32`. -/
theorem ballVolume_recentre_far_O30 (g : SmoothRiemannianMetric ThreeModel M)
    (hg : RiemannianMetricComplete g) (p x : M)
    {r w s : ℝ} (hr : 0 < r) (hs : 0 < s) (hsr : s ≤ 17 * r / 32)
    (hx : x ∈ riemannianBallOf g p (15 * r / 32))
    (hsec : ∀ z ∈ riemannianBallOf g p r, SectionalBoundedBelowAt g z (-(r ^ 2)⁻¹))
    (hvol : ENNReal.ofReal (w * (r / 4) ^ 3 / 10) ≤ ballVolume g p (r / 4)) :
    ENNReal.ofReal (w / 10 * (2 / 17) ^ 3 * s ^ 3 / Real.exp (25 / 16)) ≤
      ballVolume g x s := by
  have hsecq : ∀ z ∈ riemannianBallOf g p r,
      SectionalBoundedBelowAt g z (-(r⁻¹ ^ 2)) := by
    intro z hz
    simpa only [inv_pow] using hsec z hz
  -- step 1: from `B(p, r/4)` down to `B(p, r/16)`
  have hquarter : riemannianBallOf g p (r / 4) ⊆ riemannianBallOf g p r :=
    riemannianBallOf_mono g p (by linarith)
  have hv1 : ENNReal.ofReal ((w / 10) * (r / 4) ^ 3) ≤ ballVolume g p (r / 4) := by
    have he : (w / 10) * (r / 4) ^ 3 = w * (r / 4) ^ 3 / 10 := by ring
    rw [he]; exact hvol
  have h1 := ballVolume_small_of_sec_component_CX11 g hg p (q := r⁻¹) (s := r / 16)
    (R := r / 4) (inv_nonneg.mpr hr.le) (by positivity) (by linarith)
    (fun z hz => hsecq z (hquarter hz)) hv1
  have he1 : 2 * r⁻¹ * (r / 4) = (1 / 2 : ℝ) := by field_simp; norm_num
  rw [he1] at h1
  -- step 2: `B(p, r/16) ⊆ B(x, 17r/32) ⊆ B(p, r)`
  have hsub : riemannianBallOf g p (r / 16) ⊆ riemannianBallOf g x (17 * r / 32) := by
    intro z hz
    have hxp : riemannianEDistOf g x p < ENNReal.ofReal (15 * r / 32) := by
      rw [riemannianEDistOf_comm]
      exact hx
    have hh := (riemannianEDistOf_triangle g x p z).trans_lt (ENNReal.add_lt_add hxp hz)
    rw [← ENNReal.ofReal_add (by positivity) (by positivity)] at hh
    change riemannianEDistOf g x z < ENNReal.ofReal (17 * r / 32)
    convert hh using 2
    ring
  have hbig : riemannianBallOf g x (17 * r / 32) ⊆ riemannianBallOf g p r := by
    intro z hz
    have hh := (riemannianEDistOf_triangle g p x z).trans_lt (ENNReal.add_lt_add hx hz)
    rw [← ENNReal.ofReal_add (by positivity) (by positivity)] at hh
    change riemannianEDistOf g p z < ENNReal.ofReal r
    convert hh using 2
    ring
  have hv2 : ENNReal.ofReal ((w / 10 * (2 / 17) ^ 3 / Real.exp (1 / 2)) * (17 * r / 32) ^ 3) ≤
      ballVolume g x (17 * r / 32) := by
    have he : (w / 10 * (2 / 17) ^ 3 / Real.exp (1 / 2)) * (17 * r / 32) ^ 3 =
        w / 10 * (r / 16) ^ 3 / Real.exp (1 / 2) := by ring
    rw [he]
    exact h1.trans (MeasureTheory.measure_mono hsub)
  -- step 3: from `B(x, 17r/32)` down to `B(x, s)`
  have h3 := ballVolume_small_of_sec_component_CX11 g hg x (q := r⁻¹) (s := s)
    (R := 17 * r / 32) (inv_nonneg.mpr hr.le) hs hsr (fun z hz => hsecq z (hbig hz)) hv2
  have he3 : 2 * r⁻¹ * (17 * r / 32) = (17 / 16 : ℝ) := by field_simp; norm_num
  rw [he3] at h3
  have hfin : w / 10 * (2 / 17) ^ 3 / Real.exp (1 / 2) * s ^ 3 / Real.exp (17 / 16) =
      w / 10 * (2 / 17) ^ 3 * s ^ 3 / Real.exp (25 / 16) := by
    have hexp : Real.exp (25 / 16) = Real.exp (1 / 2) * Real.exp (17 / 16) := by
      rw [← Real.exp_add]; norm_num
    rw [hexp]
    field_simp
  rw [hfin] at h3
  exact h3

end GC.LongTime.Ch12
