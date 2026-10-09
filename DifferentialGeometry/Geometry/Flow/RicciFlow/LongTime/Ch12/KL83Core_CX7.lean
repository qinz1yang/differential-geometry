import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch12.KL83UnitCore_CX7
import DifferentialGeometry.Analysis.Integration.Measure.OpenSubtypeBall
import DifferentialGeometry.Geometry.Collapse.CurvatureScaleRestriction

/-!
# CH12-CX7: KL83.1 with the O6 core discharged

The unit-scale result is applied to the clopen component of the basepoint, with
the induced length metric, and then rescaled back. The public core has exactly
O6's quantifier order, curvature normalization and extended-distance buffer.

Source: Kleiner--Lott, G&T 12 (2008), Lemma 83.1 and (83.2)--(83.4),
printed pp. 2791--2792 / PDF pp. 205--206 of the author's 272-page PDF
https://math.berkeley.edu/~lott/gt-2008-12-059p.pdf (read 2026-10-06).
Also compared with corrected arXiv:math/0605667v5 (19 February 2013), §83,
printed/PDF pp. 163--164; the relevant hypotheses and transfer are unchanged.
The sharp strainer route is the frozen O8 design; it replaces the source's
volume-convergence input with proved finite-cover and distance-coordinate bounds.
-/

set_option autoImplicit false

noncomputable section

open Set Metric
open scoped Manifold ContDiff ENNReal NNReal
open DifferentialGeometry DifferentialGeometry.Geometry.Riemannian
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Geometry.Riemannian.VolumeComparison
  (modelVolume euclideanUnitBallVolume euclideanUnitBallVolume_pos)
open DifferentialGeometry.Geometry.Collapse
open DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

namespace GC.LongTime.Ch12

universe u

/-- The complete KL83.1 core, exactly as consumed by `almost_euclidean_subball_of_core_O6`. -/
theorem hcore_CX7 :
    ∀ w : ℝ, 0 < w → ∀ ε₁ : ℝ, 0 < ε₁ → ∃ σ₀ : ℝ, 0 < σ₀ ∧
      ∀ (X : Type u) [TopologicalSpace X] [ChartedSpace ThreeSpace X]
        [IsManifold ThreeModel ∞ X] [T2Space X] [CompactSpace X]
        (g : SmoothRiemannianMetric ThreeModel X) (p : X) (r : ℝ), 0 < r →
        (∀ q ∈ riemannianBallOf g p r, SectionalBoundedBelowAt g q (-(r ^ 2)⁻¹)) →
        ENNReal.ofReal (w * r ^ 3) ≤ ballVolume g p r →
        ∃ (y : X) (σ : ℝ), σ₀ * r ≤ σ ∧
          riemannianEDistOf g p y + ENNReal.ofReal (2 * σ) ≤ ENNReal.ofReal r ∧
          ENNReal.ofReal ((1 - ε₁) * modelVolume (-(r ^ 2)⁻¹) 3 σ) ≤ ballVolume g y σ := by
  intro w hw ε₁ hε₁
  let ε := min ε₁ (1 / 2)
  have hε : 0 < ε := by positivity
  have hε1 : ε < 1 := (min_le_right _ _).trans_lt (by norm_num)
  have hεle : ε ≤ ε₁ := min_le_left _ _
  obtain ⟨σ₀, hσ₀, hunit⟩ := unit_core_CX7.{u} w hw ε hε hε1
  refine ⟨σ₀, hσ₀, ?_⟩
  intro X _ _ _ _ _ g p r hr hsec hvol
  let U := connectedComponentOpen (I := ThreeModel) p
  have : CompactSpace U := connectedComponentOpen_compactSpace (I := ThreeModel) p
  have : ConnectedSpace U := connectedComponentOpen_connectedSpace (I := ThreeModel) p
  let pU : U := connectedComponentPoint (I := ThreeModel) p
  have hpU : pU.val = p := rfl
  let gU := g.restrictOpen U
  have hU : IsClosed (U : Set X) := isClosed_connectedComponent
  have hvolU (x : U) (s : ℝ) : ballVolume gU x s = ballVolume g x.val s :=
    Integral.Measure.riemannianVolumeMeasure_ball_restrictOpen_of_isClosed g U hU x s
  let m := inducedMetricSpace gU
  let : MetricSpace U := m
  have hm : ∀ a b : U, riemannianEDistOf gU a b = ENNReal.ofReal (dist a b) :=
    inducedMetricSpace_hmetric gU
  let g' := scaleMetric (r⁻¹ ^ 2) (pow_pos (inv_pos.mpr hr) 2) gU
  let : MetricSpace U := m.rescale r⁻¹ (inv_pos.mpr hr)
  have hm' : ∀ a b : U, riemannianEDistOf g' a b = ENNReal.ofReal (dist a b) :=
    riemannianEDistOf_scaleMetric_inv_sq_eq_rescale (m := m) gU hm hr
  have hdim : Module.finrank ℝ ThreeSpace = 3 := by simp [ThreeSpace]
  have hsqrt : Real.sqrt (r⁻¹ ^ 2) * r = 1 := by
    rw [Real.sqrt_sq (inv_pos.mpr hr).le, inv_mul_cancel₀ hr.ne']
  have hb : riemannianBallOf g' pU 1 = riemannianBallOf gU pU r := by
    rw [← hsqrt, riemannianBallOf_scaleMetric]
  have hsec' : ∀ q ∈ riemannianBallOf g' pU 1, SectionalBoundedBelowAt g' q (-1) := by
    intro q hq
    rw [hb] at hq
    have hqX : q.val ∈ riemannianBallOf g p r := by
      change riemannianEDistOf g p q.val < ENNReal.ofReal r
      change riemannianEDistOf gU pU q < ENNReal.ofReal r at hq
      rwa [riemannianEDistOf_restrictOpen_of_isClosed g U hU] at hq
    rw [sectionalBoundedBelowAt_scaleMetric_iff]
    have h : SectionalBoundedBelowAt gU q (-(r ^ 2)⁻¹) := by
      intro v w
      have hRm : metricRm04StandardAt (g.restrictOpen U) q v w w v =
          metricRm04StandardAt g q.val v w w v := by
        simpa only [mfderiv_subtype_val_apply] using
          metricRm04StandardAt_restrictOpen g U q v w w v
      simpa only [gU, SmoothRiemannianMetric.restrictOpen_inner, hRm] using hsec q.val hqX v w
    simpa only [neg_mul, one_mul, inv_pow] using h
  have hvol' : ENNReal.ofReal w ≤ ballVolume g' pU 1 := by
    have h := (le_ballVolume_scaleMetric_iff hdim (r⁻¹ ^ 2) (pow_pos (inv_pos.mpr hr) 2)
      (g := gU) (p := pU) (w := w) (t := r)).mpr (by simpa only [hvolU, hpU] using hvol)
    simpa only [hsqrt, one_pow, mul_one] using h
  obtain ⟨y, s, hs, hdist, hyv⟩ := hunit U g' hm' pU hsec' hvol'
  have hspos : 0 < s := hσ₀.trans_le hs
  have hσpos : 0 < r * s := mul_pos hr hspos
  refine ⟨y.val, r * s, ?_, ?_, ?_⟩
  · nlinarith only [mul_le_mul_of_nonneg_right hs hr.le]
  · have hd : r⁻¹ * @dist U m.toDist pU y + 2 * s ≤ 1 := hdist
    have hback : @dist U m.toDist pU y + 2 * (r * s) ≤ r := by
      have hh := mul_le_mul_of_nonneg_left hd hr.le
      have he : r * (r⁻¹ * @dist U m.toDist pU y + 2 * s) =
          @dist U m.toDist pU y + 2 * (r * s) := by field_simp
      rw [he, mul_one] at hh
      exact hh
    have hedist : riemannianEDistOf g p y.val = ENNReal.ofReal (@dist U m.toDist pU y) := by
      exact (riemannianEDistOf_restrictOpen_of_isClosed g U hU pU y).symm.trans (hm pU y)
    have hdnonneg : 0 ≤ @dist U m.toDist pU y := @dist_nonneg U m.toPseudoMetricSpace pU y
    rw [hedist, ← ENNReal.ofReal_add hdnonneg (by positivity)]
    exact ENNReal.ofReal_le_ofReal hback
  · have hsqrt' : Real.sqrt (r⁻¹ ^ 2) * (r * s) = s := by
      rw [← mul_assoc, hsqrt, one_mul]
    have hscale := ballVolume_scaleMetric hdim (r⁻¹ ^ 2) (pow_pos (inv_pos.mpr hr) 2) gU y (r * s)
    rw [hsqrt', Real.sqrt_sq (inv_pos.mpr hr).le] at hscale
    have hback : ENNReal.ofReal ((1 - ε) * modelVolume (-(r ^ 2)⁻¹) 3 (r * s)) ≤
        ballVolume gU y (r * s) := by
      apply (ENNReal.mul_le_mul_iff_right
        (pow_ne_zero 3 (ENNReal.ofReal_pos.mpr (inv_pos.mpr hr)).ne')
        (ENNReal.pow_ne_top ENNReal.ofReal_ne_top)).mp
      rw [← hscale]
      convert hyv using 1
      rw [← ENNReal.ofReal_pow (inv_pos.mpr hr).le,
        ← ENNReal.ofReal_mul (by positivity), modelVolume_scale_O3 hr s]
      congr 1
      field_simp
    rw [hvolU] at hback
    apply le_trans (ENNReal.ofReal_le_ofReal ?_) hback
    have hV : 0 ≤ modelVolume (-(r ^ 2)⁻¹) 3 (r * s) := by
      rw [modelVolume_scale_O3 hr s]
      exact mul_nonneg (by positivity) (modelVolume_neg_one_pos_O3 hspos).le
    exact mul_le_mul_of_nonneg_right (by linarith) hV

/-- **KL83.1 (G1)**, with no additional core hypothesis. -/
theorem almost_euclidean_subball_CX7 :
    ∀ w : ℝ, 0 < w → ∀ ε : ℝ, 0 < ε → ∃ θ : ℝ, 0 < θ ∧
      ∀ (X : Type u) [TopologicalSpace X] [ChartedSpace ThreeSpace X]
        [IsManifold ThreeModel ∞ X] [T2Space X] [CompactSpace X]
        (g : SmoothRiemannianMetric ThreeModel X) (p : X) (r : ℝ), 0 < r →
        (∀ q ∈ riemannianBallOf g p r, SectionalBoundedBelowAt g q (-(r ^ 2)⁻¹)) →
        ENNReal.ofReal (w * r ^ 3) ≤ ballVolume g p r →
        ∃ y : X, riemannianBallOf g y (θ * r) ⊆ riemannianBallOf g p r ∧
          ∀ z ∈ riemannianBallOf g y (θ * r), ∀ b : ℝ, 0 < b → b ≤ θ * r →
            ENNReal.ofReal ((1 - ε) * euclideanUnitBallVolume 3 * b ^ 3) ≤ ballVolume g z b :=
  almost_euclidean_subball_of_core_O6 hcore_CX7

end GC.LongTime.Ch12
