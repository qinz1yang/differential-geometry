import DifferentialGeometry.Geometry.Comparison.Volume.AllCentreSeedVolume
import DifferentialGeometry.Geometry.Collapse.FixtureC1.TorusCircleMultiplicity

/-!
# CH12-O3, group 2: the local volume test from the `w`-volume test of a test ball

`local_volume_of_volume_test_O3`: on a closed three-manifold, the test-ball hypotheses of the
whole-ball target (`sec ≥ -r⁻²` on `B(p, r)` and `vol B(p, r) ≥ w r³`) give, for every centre
`y ∈ B(p, r/8)`, exactly the local terminal volume premise of
`exists_scalar_bound_at_distance_local_O3` at scale `ρ = r/8`:
`∀ z, d(y, z) < r/8 → ∀ b ∈ (0, r/8], vol B(z, b) ≥ κ b³`, with `κ = κ(w)` chosen before the
manifold and the radius.

Proof: relative Bishop–Gromov at `p` (`localBishopGromov_cross_of_compact_three`) gives a seed
`vol B(p, r/4) ≥ w₁ (r/4)³`; then the all-centre lemma `FILL910.A13_all_centre_volume_of_seed_explicit`
(buffer `B(p, 3r/4)`), and the scale-free bounds `V_{-r⁻²}(b) ≥ ω₃ b³`,
`V_{-r⁻²}(c r) = r³ V_{-1}(c)`.
-/

set_option autoImplicit false

noncomputable section

open Set
open DifferentialGeometry DifferentialGeometry.Geometry.Riemannian
open DifferentialGeometry.Geometry.Riemannian.VolumeComparison
open DifferentialGeometry.Geometry.Collapse
open DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
open scoped Manifold ContDiff ENNReal

namespace GC.LongTime.Ch12

universe u

/-- The model volume `V_{-r⁻²}(c r) = r³ V_{-1}(c)`. -/
theorem modelVolume_scale_O3 {r : ℝ} (hr : 0 < r) (c : ℝ) :
    modelVolume (-(r ^ 2)⁻¹) 3 (r * c) = r ^ 3 * modelVolume (-((1 : ℝ) ^ 2)) 3 c := by
  have h := modelVolume_neg_sq_scale 1 r c 3 zero_le_one hr (by norm_num)
  have hq : (1 / r) ^ 2 = (r ^ 2)⁻¹ := by field_simp
  rw [hq] at h
  exact h

theorem modelVolume_neg_one_pos_O3 {c : ℝ} (hc : 0 < c) :
    0 < modelVolume (-((1 : ℝ) ^ 2)) 3 c :=
  lt_of_lt_of_le (by have := euclideanUnitBallVolume_pos 3; positivity)
    (euclid_le_modelVolume_neg_sq_three_FXC1 zero_le_one hc.le)

/-- **G2.** The `w`-volume test of a test ball supplies the local terminal volume premise of the
local KL70.2 kernel at scale `r/8` about every centre of `B(p, r/8)`, with `κ = κ(w)`. -/
theorem local_volume_of_volume_test_O3 (w : ℝ) (hw : 0 < w) :
    ∃ κ : ℝ, 0 < κ ∧
      ∀ (X : Type u) [TopologicalSpace X] [ChartedSpace ThreeSpace X]
        [IsManifold ThreeModel ∞ X] [T2Space X] [CompactSpace X]
        (g : SmoothRiemannianMetric ThreeModel X) (p : X) (r : ℝ), 0 < r →
        (∀ q ∈ riemannianBallOf g p r, SectionalBoundedBelowAt g q (-(r ^ 2)⁻¹)) →
        ENNReal.ofReal (w * r ^ 3) ≤
          Integral.Measure.riemannianVolumeMeasure ThreeModel X g (riemannianBallOf g p r) →
        ∀ y ∈ riemannianBallOf g p (r / 8), ∀ z : X,
          riemannianEDistOf g y z < ENNReal.ofReal (r / 8) → ∀ b : ℝ, 0 < b → b ≤ r / 8 →
            ENNReal.ofReal κ * ENNReal.ofReal b ^ 3 ≤
              Integral.Measure.riemannianVolumeMeasure ThreeModel X g
                (riemannianBallOf g z b) := by
  set V1 := fun c : ℝ => modelVolume (-((1 : ℝ) ^ 2)) 3 c with hV1
  have hV14 : 0 < V1 (1 / 4) := modelVolume_neg_one_pos_O3 (by norm_num)
  have hV11 : 0 < V1 1 := modelVolume_neg_one_pos_O3 (by norm_num)
  have hV12 : 0 < V1 (1 / 2) := modelVolume_neg_one_pos_O3 (by norm_num)
  have hω := euclideanUnitBallVolume_pos 3
  set w₁ : ℝ := 64 * w * V1 (1 / 4) / V1 1 with hw₁
  have hw₁pos : 0 < w₁ := by positivity
  refine ⟨w₁ * euclideanUnitBallVolume 3 / (64 * V1 (1 / 2)), by positivity, ?_⟩
  intro X _ _ _ _ _ g p r hr hsec hvol y hy z hz b hb hbr
  have hΛ : (0 : ℝ) ≤ (r ^ 2)⁻¹ := by positivity
  -- the seed `vol B(p, r/4) ≥ w₁ (r/4)³`
  have hcross := FILL910.localBishopGromov_cross_of_compact_three g p hΛ
    (by positivity : (0 : ℝ) < r / 4) (by linarith : r / 4 ≤ r) hsec
  have hVr4 : modelVolume (-(r ^ 2)⁻¹) 3 (r / 4) = r ^ 3 * V1 (1 / 4) := by
    rw [show r / 4 = r * (1 / 4) by ring]; exact modelVolume_scale_O3 hr _
  have hVr : modelVolume (-(r ^ 2)⁻¹) 3 r = r ^ 3 * V1 1 := by
    have h := modelVolume_scale_O3 hr 1
    rw [mul_one] at h
    exact h
  rw [hVr4, hVr] at hcross
  have hseed : ENNReal.ofReal (w₁ * (r / 4) ^ 3) ≤
      Integral.Measure.riemannianVolumeMeasure ThreeModel X g (riemannianBallOf g p (r / 4)) := by
    have hr3 : 0 < r ^ 3 := by positivity
    have hkey : ENNReal.ofReal (r ^ 3 * V1 1) * ENNReal.ofReal (w₁ * (r / 4) ^ 3) ≤
        ENNReal.ofReal (r ^ 3 * V1 1) *
          Integral.Measure.riemannianVolumeMeasure ThreeModel X g
            (riemannianBallOf g p (r / 4)) := by
      have heq : r ^ 3 * V1 1 * (w₁ * (r / 4) ^ 3) = w * r ^ 3 * (r ^ 3 * V1 (1 / 4)) := by
        rw [hw₁]; field_simp; ring
      rw [← ENNReal.ofReal_mul (by positivity), heq, ENNReal.ofReal_mul (by positivity)]
      calc ENNReal.ofReal (w * r ^ 3) * ENNReal.ofReal (r ^ 3 * V1 (1 / 4))
          ≤ ballVolume g p r * ENNReal.ofReal (r ^ 3 * V1 (1 / 4)) := by
            gcongr
            exact hvol
        _ ≤ ENNReal.ofReal (r ^ 3 * V1 1) * ballVolume g p (r / 4) := hcross
        _ = _ := rfl
    exact (ENNReal.mul_le_mul_iff_right (ENNReal.ofReal_pos.mpr (by positivity)).ne'
      ENNReal.ofReal_ne_top).mp hkey
  -- all centres of `B̄(p, r/4)`
  obtain ⟨-, hall⟩ := FILL910.A13_all_centre_volume_of_seed_explicit.{u}
    (r₀ := r / 4) (w := w₁) (Λ := (r ^ 2)⁻¹) (R := r / 4) (a := b)
    (by positivity) hw₁pos hΛ le_rfl hb (by linarith)
  have hsec' : ∀ q ∈ riemannianBallOf g p (3 * (r / 4)),
      SectionalBoundedBelowAt g q (-(r ^ 2)⁻¹) := by
    intro q hq
    apply hsec q
    have hq' : riemannianEDistOf g p q < ENNReal.ofReal (3 * (r / 4)) := hq
    exact hq'.trans_le (ENNReal.ofReal_le_ofReal (by linarith))
  have hzp : z ∈ riemannianClosedBallOf g p (r / 4) := by
    have hy' : riemannianEDistOf g p y < ENNReal.ofReal (r / 8) := hy
    change riemannianEDistOf g p z ≤ ENNReal.ofReal (r / 4)
    calc riemannianEDistOf g p z ≤ riemannianEDistOf g p y + riemannianEDistOf g y z :=
          riemannianEDistOf_triangle g p y z
      _ ≤ ENNReal.ofReal (r / 8) + ENNReal.ofReal (r / 8) := add_le_add hy'.le hz.le
      _ = ENNReal.ofReal (r / 4) := by
          rw [← ENNReal.ofReal_add (by positivity) (by positivity)]; ring_nf
  have hmain := hall X g p hseed hsec' z hzp
  -- the constant is uniform in `b` and `r`
  have hVb : euclideanUnitBallVolume 3 * b ^ 3 ≤ modelVolume (-(r ^ 2)⁻¹) 3 b := by
    have h := euclid_le_modelVolume_neg_sq_three_FXC1 (q := 1 / r) (by positivity) hb.le
    have hq : (1 / r) ^ 2 = (r ^ 2)⁻¹ := by field_simp
    rwa [hq] at h
  have hV2R : modelVolume (-(r ^ 2)⁻¹) 3 (2 * (r / 4)) = r ^ 3 * V1 (1 / 2) := by
    rw [show 2 * (r / 4) = r * (1 / 2) by ring]; exact modelVolume_scale_O3 hr _
  rw [hV2R] at hmain
  refine le_trans ?_ hmain
  rw [← ENNReal.ofReal_pow hb.le, ← ENNReal.ofReal_mul (by positivity)]
  apply ENNReal.ofReal_le_ofReal
  have hb3 : 0 < b ^ 3 := by positivity
  have hr3 : 0 < r ^ 3 := by positivity
  have hR : w₁ * (r / 4) ^ 3 * modelVolume (-(r ^ 2)⁻¹) 3 b / (b ^ 3 * (r ^ 3 * V1 (1 / 2))) *
      b ^ 3 = w₁ * (r / 4) ^ 3 * modelVolume (-(r ^ 2)⁻¹) 3 b / (r ^ 3 * V1 (1 / 2)) := by
    field_simp
  rw [hR]
  have hlhs : w₁ * euclideanUnitBallVolume 3 / (64 * V1 (1 / 2)) * b ^ 3 =
      w₁ * (r / 4) ^ 3 * (euclideanUnitBallVolume 3 * b ^ 3) / (r ^ 3 * V1 (1 / 2)) := by
    field_simp; ring
  rw [hlhs]
  have hden : 0 < r ^ 3 * V1 (1 / 2) := by positivity
  have hfinal : w₁ * (r / 4) ^ 3 * (euclideanUnitBallVolume 3 * b ^ 3) / (r ^ 3 * V1 (1 / 2)) ≤
      w₁ * (r / 4) ^ 3 * modelVolume (-(r ^ 2)⁻¹) 3 b / (r ^ 3 * V1 (1 / 2)) := by
    apply div_le_div_of_nonneg_right _ hden.le
    exact mul_le_mul_of_nonneg_left hVb (by positivity)
  refine hfinal.trans (le_of_eq ?_)
  field_simp

end GC.LongTime.Ch12
