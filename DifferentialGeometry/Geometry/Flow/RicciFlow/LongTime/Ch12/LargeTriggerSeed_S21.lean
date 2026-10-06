import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch12.MicroGlueVolumeTest

/-!
# CH12-S21 / T3, group S: Bishop--Gromov scale-down of a test ball

A ball `B(p, r)` with `sec ≥ -r⁻²` and `vol ≥ w r³` has, at every smaller scale `a ≤ r`,
`sec ≥ -a⁻²` on `B(p, a)` and `vol B(p, a) ≥ c w a³` with a numerical `c` (independent of `w`,
`a`, `r` and the manifold).
-/

set_option autoImplicit false
noncomputable section
open Set
open DifferentialGeometry DifferentialGeometry.Topology DifferentialGeometry.Geometry.Riemannian
open DifferentialGeometry.Geometry.Riemannian.VolumeComparison
open DifferentialGeometry.Geometry.Collapse
open DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
open scoped Manifold ContDiff ENNReal
namespace GC.LongTime.Ch12
universe u

theorem seed_scale_down_S21 :
    ∃ c : ℝ, 0 < c ∧
      ∀ (X : Type u) [TopologicalSpace X] [ChartedSpace ThreeSpace X]
        [IsManifold ThreeModel ∞ X] [T2Space X] [CompactSpace X]
        (g : SmoothRiemannianMetric ThreeModel X) (p : X) (w r a : ℝ), 0 < w → 0 < a → a ≤ r →
        (∀ q ∈ riemannianBallOf g p r, SectionalBoundedBelowAt g q (-(r ^ 2)⁻¹)) →
        ENNReal.ofReal (w * r ^ 3) ≤
          Integral.Measure.riemannianVolumeMeasure ThreeModel X g (riemannianBallOf g p r) →
        (∀ q ∈ riemannianBallOf g p a, SectionalBoundedBelowAt g q (-(a ^ 2)⁻¹)) ∧
          ENNReal.ofReal (c * w * a ^ 3) ≤
            Integral.Measure.riemannianVolumeMeasure ThreeModel X g (riemannianBallOf g p a) := by
  set V1 : ℝ := modelVolume (-((1 : ℝ) ^ 2)) 3 1 with hV1
  have hV1pos : 0 < V1 := modelVolume_neg_one_pos_O3 one_pos
  have hω := euclideanUnitBallVolume_pos 3
  refine ⟨euclideanUnitBallVolume 3 / V1, by positivity, ?_⟩
  intro X _ _ _ _ _ g p w r a hw ha har hsec hvol
  have hr : 0 < r := ha.trans_le har
  refine ⟨fun q hq => ?_, ?_⟩
  · refine (hsec q ?_).mono ?_
    · have hq' : riemannianEDistOf g p q < ENNReal.ofReal a := hq
      exact hq'.trans_le (ENNReal.ofReal_le_ofReal har)
    · have : a ^ 2 ≤ r ^ 2 := by nlinarith
      have h2 : (r ^ 2)⁻¹ ≤ (a ^ 2)⁻¹ := inv_anti₀ (by positivity) this
      linarith
  · have hΛ : (0 : ℝ) ≤ (r ^ 2)⁻¹ := by positivity
    have hcross := FILL910.localBishopGromov_cross_of_compact_three g p hΛ ha har hsec
    have hVr : modelVolume (-(r ^ 2)⁻¹) 3 r = r ^ 3 * V1 := by
      have h := modelVolume_scale_O3 hr 1
      rw [mul_one] at h
      exact h
    have hVa : euclideanUnitBallVolume 3 * a ^ 3 ≤ modelVolume (-(r ^ 2)⁻¹) 3 a := by
      have h := euclid_le_modelVolume_neg_sq_three_FXC1 (q := 1 / r) (by positivity) ha.le
      have hq : (1 / r) ^ 2 = (r ^ 2)⁻¹ := by field_simp
      rwa [hq] at h
    rw [hVr] at hcross
    set Va := Integral.Measure.riemannianVolumeMeasure ThreeModel X g (riemannianBallOf g p a)
      with hVa'
    have hkey : ENNReal.ofReal (r ^ 3 * V1) * ENNReal.ofReal (euclideanUnitBallVolume 3 / V1 * w * a ^ 3) ≤
        ENNReal.ofReal (r ^ 3 * V1) * Va := by
      have hmul : ENNReal.ofReal (w * r ^ 3) * ENNReal.ofReal (euclideanUnitBallVolume 3 * a ^ 3) ≤
          ballVolume g p r * ENNReal.ofReal (modelVolume (-(r ^ 2)⁻¹) 3 a) := by
        gcongr
        exact hvol
      have heq : r ^ 3 * V1 * (euclideanUnitBallVolume 3 / V1 * w * a ^ 3) =
          w * r ^ 3 * (euclideanUnitBallVolume 3 * a ^ 3) := by
        field_simp
      rw [← ENNReal.ofReal_mul (by positivity), heq, ENNReal.ofReal_mul (by positivity)]
      exact hmul.trans hcross
    exact (ENNReal.mul_le_mul_iff_right (ENNReal.ofReal_pos.mpr (by positivity)).ne'
      ENNReal.ofReal_ne_top).mp hkey

end GC.LongTime.Ch12
