import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch12.ThickLimitVolumeLimit_O5
import DifferentialGeometry.Geometry.Comparison.RadialHessianLowerBound

/-!
# CH12-S21 / T3, group R: a small normalised Ricci defect forces curvature scale `≤ 5`
-/

set_option autoImplicit false
noncomputable section
open DifferentialGeometry DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Geometry.Collapse DifferentialGeometry.Geometry.Riemannian
open DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
open GC.LongTime Set Filter
open scoped Manifold ContDiff ENNReal Topology
namespace GC.LongTime.Ch12
universe u

variable {M : Type*} [TopologicalSpace M] [ChartedSpace ThreeSpace M]
  [IsManifold ThreeModel ∞ M] [T2Space M] [SigmaCompactSpace M]

omit [SigmaCompactSpace M] in
/-- `sSup (defectSet) < 1/4` forbids `sec ≥ -1/25` at the point. -/
theorem not_sectionalBoundedBelowAt_of_defect_S21 (g : SmoothRiemannianMetric ThreeModel M)
    (p : M) (hdef : sSup (defectSet_O5 g p) < 1 / 4) :
    ¬ SectionalBoundedBelowAt g p (-(1 / 25 : ℝ)) := by
  intro hsec
  have hdim : Module.finrank ℝ ThreeSpace = 3 := by simp
  have hric := DifferentialGeometry.Geometry.Riemannian.ricci_lower_of_sectionalBoundedBelowAt
    (I := ThreeModel) g p hsec
  obtain ⟨V, hV⟩ : ∃ V : TangentSpace ThreeModel p, V ≠ 0 := by
    have : Nontrivial (TangentSpace ThreeModel p) :=
      inferInstanceAs (Nontrivial ThreeSpace)
    exact exists_ne 0
  have hpos : 0 < g.inner p V V := g.pos p V hV
  have h1 := hric V
  have h2 := defect_quad_le_O5 g p V
  have h3 := (abs_le.mp h2).2
  rw [hdim] at h1
  norm_num at h1
  have hd0 : 0 ≤ sSup (defectSet_O5 g p) := by
    exact Real.sSup_nonneg (by rintro _ ⟨v, w, -, -, rfl⟩; exact abs_nonneg _)
  nlinarith [mul_pos hpos (by linarith : (0:ℝ) < 1/4 - sSup (defectSet_O5 g p))]

omit [SigmaCompactSpace M] in
/-- Curvature radius at most `5` from a small defect. -/
theorem curvatureRadius_le_five_of_defect_S21 (g : SmoothRiemannianMetric ThreeModel M)
    (p : M) (hdef : sSup (defectSet_O5 g p) < 1 / 4) :
    curvatureRadius g p ≤ ENNReal.ofReal 5 := by
  have hn := not_sectionalBoundedBelowAt_of_defect_S21 g p hdef
  unfold curvatureRadius
  refine iSup_le fun r => iSup_le fun hr => iSup_le fun hball => ?_
  by_contra hlt
  push Not at hlt
  have hr5 : 5 < r := by
    by_contra h; push Not at h
    exact absurd (ENNReal.ofReal_le_ofReal h) (not_le_of_gt hlt)
  apply hn
  have hp : p ∈ riemannianBallOf g p r := by
    change riemannianEDistOf g p p < ENNReal.ofReal r
    rw [riemannianEDistOf_self]; exact ENNReal.ofReal_pos.mpr hr
  refine (hball p hp).mono ?_
  have : (25:ℝ) < r ^ 2 := by nlinarith
  have h' : (r ^ 2)⁻¹ ≤ 1 / 25 := by
    rw [one_div]; exact inv_anti₀ (by norm_num) this.le
  linarith

end GC.LongTime.Ch12
