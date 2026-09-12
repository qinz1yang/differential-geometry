import DifferentialGeometry.Geometry.Flow.RicciFlow.Extinction.Families.Flow
import DifferentialGeometry.Geometry.Flow.RicciFlow.Extinction.CurveShortening.LocalRegularity
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic



noncomputable section

open Bundle Manifold Set MeasureTheory
open scoped Manifold ContDiff Topology
open DifferentialGeometry.Geometry.Curvature

namespace DifferentialGeometry.PDE.RicciFlow.Extinction.Families

open CurveShortening

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [CompleteSpace E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {Q : Type*} [TopologicalSpace Q] [ChartedSpace H Q] [IsManifold I ∞ Q]
    [SigmaCompactSpace Q] [hT2 : T2Space Q] [hCompact : CompactSpace Q]
    [hConnected : ConnectedSpace Q] [hBoundary : I.Boundaryless]
    {D : RealTimeInterval} {a b : ℝ}

include hT2 hCompact hConnected hBoundary

theorem rfs_ramp_small_angle (g : SmoothRiemannianMetric I Q)
    (c : ProductCurve Q) (lambda t ell K : ℝ) (hlambda : 0 < lambda)
    (hell : 0 < ell) (hK : 0 < K) (hdegree : c.degree = 1)
    (hsmooth : c.SmoothOn (I := I) {t})
    (hramp : c.IsRampOn (fun _ => g) lambda {t})
    (hlength : ell ≤ c.length (fun _ => g) lambda t)
    (hcurvature : ∀ x, c.curvature (fun _ => g) lambda x t ≤ K) :
    ∀ x, c.angle (fun _ => g) lambda x t ≤ 2 * lambda / ell + 2 * Real.sqrt (K * lambda) := by
  sorry


def localRegularityDelta (B : RicciBackground (I := I) (M := Q) D a b) (L₀ Theta₀ : ℝ)
    (K : CurveShorteningRegularityInput B L₀ Theta₀) : ℝ :=
  K.delta

def localRegularityRadius (B : RicciBackground (I := I) (M := Q) D a b) (L₀ Theta₀ : ℝ)
    (K : CurveShorteningRegularityInput B L₀ Theta₀) : ℝ :=
  K.radius

def localRegularityCoefficient (B : RicciBackground (I := I) (M := Q) D a b) (L₀ Theta₀ : ℝ)
    (K : CurveShorteningRegularityInput B L₀ Theta₀) : ℕ → ℝ :=
  K.coefficient


def goodWindowUnion (starts : Finset ℝ) (d : ℝ) : Set ℝ :=
  {t | ∃ w ∈ starts, t ∈ Icc (w + 5 * d / 8) (w + 7 * d / 8)}

theorem rfs_finite_good_windows (B : RicciBackground (I := I) (M := Q) D a b)
    (L₀ Theta₀ : ℝ) (K : CurveShorteningRegularityInput B L₀ Theta₀) :
    let delta := localRegularityDelta B L₀ Theta₀ K
    let r₀ := localRegularityRadius B L₀ Theta₀ K
    let areg := localRegularityCoefficient B L₀ Theta₀ K 0
    let C_E := Real.exp (B.B₀ * (b - a)) * L₀
    ∀ ell threshold : ℝ, 0 < ell → 0 < threshold →
      let r := min r₀ (min (ell / 2) (delta ^ 2 / threshold))
      let d := delta * r ^ 2
      d < b - a →
      ∀ lambda : ℝ, 0 < lambda → lambda ≤ 1 → ∀ c : ProductCurve Q,
        c.IsSolutionOn B.family.metric lambda (Icc a b) →
        c.IsRampOn B.family.metric lambda (Icc a b) → c.degree = 1 →
        c.length B.family.metric lambda a ≤ L₀ →
        c.totalCurvature B.family.metric lambda a ≤ Theta₀ →
        (∀ t ∈ Icc a b, ell ≤ c.length B.family.metric lambda t) →
        ∃ starts : Finset ℝ,
          (∀ w ∈ starts, w ∈ Icc a (b - d) ∧ c.energy B.family.metric lambda w ≤ threshold) ∧
          goodWindowUnion starts d ⊆ Ioo a b ∧
          volume (Icc a b \ goodWindowUnion starts d) ≤ ENNReal.ofReal (d + C_E / threshold) ∧
          (∀ x t, t ∈ goodWindowUnion starts d →
            c.curvature B.family.metric lambda x t ≤ Real.sqrt (2 * areg / d)) ∧
          ∀ w ∈ starts, Icc (w + 5 * d / 8) (w + 7 * d / 8) ⊆ Ioo (w + d / 2) (w + d) := by
  sorry

omit [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
  [TopologicalSpace H] [TopologicalSpace Q] [ChartedSpace H Q] [IsManifold I ∞ Q]
  hT2 hCompact hConnected hBoundary in
theorem le_of_lipschitz_integral_bound {u : ℝ → ℝ} {L K lam : ℝ} (hL : 0 < L) (hK : 0 < K)
    (hcont : ContinuousOn u (Icc (0 : ℝ) L))
    (hnonneg : ∀ s ∈ Icc (0 : ℝ) L, 0 ≤ u s)
    (hlip : ∀ s ∈ Icc (0 : ℝ) L, u 0 - K * s ≤ u s)
    (hint : (∫ s in (0 : ℝ)..L, u s) = lam) :
    u 0 ≤ 2 * lam / L + 2 * Real.sqrt (K * lam) := by
  have h0 : (0 : ℝ) ∈ Icc (0 : ℝ) L := ⟨le_rfl, hL.le⟩
  have hlam : 0 ≤ lam := by
    rw [← hint]
    exact intervalIntegral.integral_nonneg hL.le fun s hs => hnonneg s hs
  have ha : 0 ≤ u 0 := hnonneg 0 h0
  have hUi : IntervalIntegrable u volume (0 : ℝ) L := hcont.intervalIntegrable_of_Icc hL.le
  have hsqrt : 0 ≤ Real.sqrt (K * lam) := Real.sqrt_nonneg _
  rcases eq_or_lt_of_le ha with hzero | hapos
  · have hdiv : 0 ≤ 2 * lam / L := div_nonneg (by linarith) hL.le
    rw [← hzero]
    linarith
  rcases lt_or_ge (K * L) (u 0) with hcase | hcase
  · have hcalc : (∫ s in (0 : ℝ)..L, (u 0 - K * s)) = u 0 * L - K * (L ^ 2 / 2) := by
      have h1 : (∫ s in (0 : ℝ)..L, (u 0 : ℝ)) = u 0 * L := by
        rw [intervalIntegral.integral_const]
        simp only [sub_zero, smul_eq_mul]
        ring
      have h2 : (∫ s in (0 : ℝ)..L, K * s) = K * (L ^ 2 / 2) := by
        rw [intervalIntegral.integral_const_mul, integral_id]
        ring
      rw [intervalIntegral.integral_sub (f := fun _ : ℝ => u 0) (g := fun s : ℝ => K * s)
          intervalIntegrable_const ((continuous_const.mul continuous_id).intervalIntegrable _ _),
        h1, h2]
    have hlow : u 0 * L - K * (L ^ 2 / 2) ≤ lam := by
      rw [← hcalc, ← hint]
      exact intervalIntegral.integral_mono_on hL.le
        ((continuous_const.sub (continuous_const.mul continuous_id)).intervalIntegrable _ _)
        hUi fun s hs => hlip s hs
    have hkey : u 0 ≤ lam / L + K * L / 2 := by
      have hsplit : lam / L + K * L / 2 = (lam + K * (L ^ 2 / 2)) / L := by
        field_simp
      rw [hsplit, le_div_iff₀ hL]
      linarith
    have hbig : K * L / 2 < lam / L := by
      rw [lt_div_iff₀ hL]
      nlinarith [hlow, hcase]
    have hterm : u 0 ≤ 2 * lam / L := by
      have htwo : lam / L + lam / L = 2 * lam / L := by ring
      linarith
    linarith [hterm, hsqrt]
  · set s₀ : ℝ := u 0 / K with hs₀def
    have hs₀pos : 0 < s₀ := by
      rw [hs₀def]
      exact div_pos hapos hK
    have hs₀le : s₀ ≤ L := by
      rw [hs₀def, div_le_iff₀ hK]
      linarith
    have hcont' : ContinuousOn u (Icc (0 : ℝ) s₀) := hcont.mono (Icc_subset_Icc le_rfl hs₀le)
    have hcalc : (∫ s in (0 : ℝ)..s₀, (u 0 - K * s)) = u 0 ^ 2 / (2 * K) := by
      have h1 : (∫ s in (0 : ℝ)..s₀, (u 0 : ℝ)) = u 0 * s₀ := by
        rw [intervalIntegral.integral_const]
        simp only [sub_zero, smul_eq_mul]
        ring
      have h2 : (∫ s in (0 : ℝ)..s₀, K * s) = K * (s₀ ^ 2 / 2) := by
        rw [intervalIntegral.integral_const_mul, integral_id]
        ring
      rw [intervalIntegral.integral_sub (f := fun _ : ℝ => u 0) (g := fun s : ℝ => K * s)
          intervalIntegrable_const ((continuous_const.mul continuous_id).intervalIntegrable _ _),
        h1, h2, hs₀def]
      field_simp
      ring
    have hle1 : (∫ s in (0 : ℝ)..s₀, (u 0 - K * s)) ≤ ∫ s in (0 : ℝ)..s₀, u s :=
      intervalIntegral.integral_mono_on hs₀pos.le
        ((continuous_const.sub (continuous_const.mul continuous_id)).intervalIntegrable _ _)
        (hcont'.intervalIntegrable_of_Icc hs₀pos.le)
        fun s hs => hlip s ⟨hs.1, hs.2.trans hs₀le⟩
    have hle2 : (∫ s in (0 : ℝ)..s₀, u s) ≤ ∫ s in (0 : ℝ)..L, u s := by
      have hsplit : (∫ s in (0 : ℝ)..s₀, u s) + (∫ s in s₀..L, u s) =
          ∫ s in (0 : ℝ)..L, u s :=
        intervalIntegral.integral_add_adjacent_intervals
          (hcont'.intervalIntegrable_of_Icc hs₀pos.le)
          ((hcont.mono (Icc_subset_Icc hs₀pos.le le_rfl)).intervalIntegrable_of_Icc hs₀le)
      have hnn : 0 ≤ ∫ s in s₀..L, u s :=
        intervalIntegral.integral_nonneg hs₀le fun s hs => hnonneg s ⟨hs₀pos.le.trans hs.1, hs.2⟩
      linarith
    have hkey : u 0 ^ 2 ≤ 2 * K * lam := by
      have h := hle1.trans hle2
      rw [hint, hcalc] at h
      rw [div_le_iff₀ (by linarith : (0 : ℝ) < 2 * K)] at h
      linarith
    have hstep : u 0 ≤ Real.sqrt (2 * K * lam) :=
      (Real.le_sqrt (by linarith) (by positivity)).mpr hkey
    have hmono : Real.sqrt (2 * K * lam) ≤ Real.sqrt (4 * (K * lam)) := by
      apply Real.sqrt_le_sqrt
      nlinarith [hK, hlam]
    have hfour : Real.sqrt (4 * (K * lam)) = 2 * Real.sqrt (K * lam) := by
      have hsq : (4 : ℝ) = 2 ^ 2 := by norm_num
      rw [Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 4), hsq,
        Real.sqrt_sq (by norm_num : (0 : ℝ) ≤ 2)]
    have hterm : 0 ≤ 2 * lam / L := div_nonneg (by linarith) hL.le
    linarith [hstep, hmono, hfour.le, hterm]

end DifferentialGeometry.PDE.RicciFlow.Extinction.Families
