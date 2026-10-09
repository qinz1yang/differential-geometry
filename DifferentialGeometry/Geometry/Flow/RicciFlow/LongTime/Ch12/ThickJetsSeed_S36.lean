import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch12.ThickLimitCenterMain_CX8
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch12.ThickLimitCurvHI_S20
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch12.ThickLimitSeedReduce_O5
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch12.ThickLimitVolumeAlgebra_O5
import DifferentialGeometry.Geometry.Curvature.Metric.DerivativeNormBridge

set_option autoImplicit false

/-! # CH12-S36: seed gives derivative bound (W2); small Ricci defect gives scalar `≤ 0` -/

noncomputable section
open DifferentialGeometry DifferentialGeometry.Geometry.Collapse DifferentialGeometry.Geometry.Riemannian
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.PDE.RicciFlow DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
open GC.LongTime Set Filter
open scoped Manifold ContDiff ENNReal Topology

namespace GC.LongTime.Ch12
universe u
variable {P : OrientedThreeStage.{u}} {g : P.Metric} {F : GC.Interface.RawSurgery P g} {δ : ℝ → ℝ}

/-- A normalized seed `(b, w)` at `q` of a late slice gives a uniform bound of `|∇^m Rm|` of the
normalized metric at `q` (W2 + traced region + whole ball Shi, rescaled). -/
theorem curvDeriv_of_seed_S36 (Hp : AnalyticSurgeryProfile F δ)
    (hW2 : ∀ w : ℝ, 0 < w → ∃ T Λ b τ C : ℝ, 0 < T ∧ 1 ≤ Λ ∧ 0 < b ∧ 0 < τ ∧ 0 < C ∧
      τ * b ^ 2 < 1 / 2 ∧
      ∀ s : GC.LongTime.RegularSlice F.observation, T ≤ s.time →
      ∀ (p : (s.history.stageAt (sliceTop_S8 s)).Carrier) (r : ℝ), 0 < r →
        r ≤ b * Real.sqrt s.time →
        (∀ q ∈ riemannianBallOf (s.history.stageMetric (s.history.activeStage (sliceTop_S8 s))
            s.time) p r,
          SectionalBoundedBelowAt (s.history.stageMetric (s.history.activeStage (sliceTop_S8 s))
            s.time) q (-(r ^ 2)⁻¹)) →
        ENNReal.ofReal (w * r ^ 3) ≤ ballVolume (s.history.stageMetric
          (s.history.activeStage (sliceTop_S8 s)) s.time) p r →
        (∀ n (i : Fin (F.tower.history n).eventCount),
          (F.tower.history n).time i.succ ∈ Icc (s.time / 2) s.time →
          ∀ h, Λ * (Hp.records n i).nominalRadius h ≤ r) →
        s.history.isTracedRegion (sliceTop_S8 s) p (2 * r) (τ * r ^ 2) (C / r ^ 2))
    {b w : ℝ} (hb : 0 < b) (hw : 0 < w) (m : ℕ) :
    ∃ T C : ℝ, 0 ≤ C ∧ ∀ s : RegularSlice F.observation, T ≤ s.time → ∀ q : s.stage.Carrier,
      HasNormalizedSeed_S13 s q b w → curvatureDerivativeNorm s.normalizedMetric m q ≤ C := by
  obtain ⟨b1, θ, K, T, hb1, -, hθ, -, hK, hT, hwin⟩ := traced_window_of_seed_CX8 Hp hW2 hb hw
  set τ : ℝ := θ / b1 ^ 2 with hτdef
  set C0 : ℝ := K * b1 ^ 2 with hC0def
  have hτ : 0 < τ := by positivity
  have hC0 : 0 < C0 := by positivity
  set Am : ℝ := shiLocalUniformBound 3 m (C0 * τ / 2)
      (Real.sqrt C0 / (8 * Real.exp ((3 : ℝ) ^ 2 * (C0 * τ / 2)))) * C0 / Real.sqrt (τ / 2) ^ m
    with hAm
  refine ⟨T, max 0 (Am / b1 ^ (m + 2)), le_max_left _ _, ?_⟩
  intro s hs q hq
  have ht := s.positive
  have hu : 0 < Real.sqrt s.time := Real.sqrt_pos.mpr ht
  have hu2 : Real.sqrt s.time ^ 2 = s.time := Real.sq_sqrt ht.le
  have htr : ∀ p' : (s.history.stageAt (sliceTop_S8 s)).Carrier, HEq p' q →
      s.history.isTracedRegion (sliceTop_S8 s) p' (2 * (b1 * Real.sqrt s.time))
        (τ * (b1 * Real.sqrt s.time) ^ 2) (C0 / (b1 * Real.sqrt s.time) ^ 2) := by
    intro p' hp'
    have h1 := hwin s hs q hq p' hp'
    have e1 : τ * (b1 * Real.sqrt s.time) ^ 2 = θ * s.time := by
      rw [hτdef, mul_pow, hu2]; field_simp
    have e2 : C0 / (b1 * Real.sqrt s.time) ^ 2 = K / s.time := by
      rw [hC0def, mul_pow, hu2]; field_simp
    rw [e1, e2]; exact h1
  have hwb := wholeBall_of_traced_S8 s (Fin.last _) s.history.activeStage_at_horizon q hτ
    (mul_pos hb1 hu) hC0 htr m q (by
      change riemannianEDistOf _ q q < _
      rw [riemannianEDistOf_self]; exact ENNReal.ofReal_pos.mpr (mul_pos hb1 hu))
  have hnorm : curvatureDerivativeNorm s.normalizedMetric m q =
      curvatureDerivativeNorm s.metric m q / (s.time⁻¹ * Real.sqrt s.time⁻¹ ^ m) := by
    exact curvatureDerivativeNorm_scaleMetric_div s.metric s.time⁻¹ (inv_pos.mpr ht) m q
  rw [hnorm]
  have hden : s.time⁻¹ * Real.sqrt s.time⁻¹ ^ m = (Real.sqrt s.time ^ (m + 2))⁻¹ := by
    have ht' : s.time⁻¹ = (Real.sqrt s.time ^ 2)⁻¹ := by rw [hu2]
    rw [Real.sqrt_inv, ht', inv_pow, ← mul_inv]
    congr 1
    ring
  rw [hden, div_inv_eq_mul]
  have hD : curvatureDerivativeNorm s.metric m q ≤ Am * ((b1 * Real.sqrt s.time) ^ (m + 2))⁻¹ := hwb
  have hu' : 0 < Real.sqrt s.time ^ (m + 2) := pow_pos hu _
  calc curvatureDerivativeNorm s.metric m q * Real.sqrt s.time ^ (m + 2)
      ≤ Am * ((b1 * Real.sqrt s.time) ^ (m + 2))⁻¹ * Real.sqrt s.time ^ (m + 2) :=
        mul_le_mul_of_nonneg_right hD hu'.le
    _ = Am / b1 ^ (m + 2) := by
        rw [mul_pow]; field_simp
    _ ≤ _ := le_max_right _ _

end GC.LongTime.Ch12
