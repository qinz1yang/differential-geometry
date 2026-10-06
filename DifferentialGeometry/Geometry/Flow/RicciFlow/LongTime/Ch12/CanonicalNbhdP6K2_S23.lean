import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch12.CanonicalNbhdP6Seed_S23
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch12.EnhancedProfileHypotheses

/-!
# CH12-S23 / K2: KL84.1(b) at `R ≥ C(L)/t` from P6 and the W2 seed supplier

Order of constants (K2a, no circularity): `(a, v)` ⟶ `r = min a b · √t` (from `hW2`, `c_sd` of the
Bishop–Gromov scale-down) ⟶ parabolic seed radius `r₀ = c₃ r = c₂ √t` with `c₂` independent of `A`
⟶ `A = max (1/(c_sd² v)) (L/c₂)` ⟶ `(K₁, T_A)` of P6 ⟶ `C = max 1 (K₁/c₂²)`.
Only KL84.1(c) carries `r ≤ r̄(A)√t`; P6 contains only (b).
-/

set_option autoImplicit false
noncomputable section
open DifferentialGeometry DifferentialGeometry.Geometry.Collapse DifferentialGeometry.Geometry.Riemannian
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
open DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn
open GC.LongTime Set
open scoped Manifold ContDiff ENNReal
namespace GC.LongTime.Ch12
universe u

theorem hK2_of_P6_S23 {P : OrientedThreeStage.{u}} {g : P.Metric}
    {F : GC.Interface.RawSurgery P g} {δ : ℝ → ℝ} (Hp : AnalyticSurgeryProfile F δ)
    (hP6 : P6_S23 Hp)
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
        s.history.isTracedRegion (sliceTop_S8 s) p (2 * r) (τ * r ^ 2) (C / r ^ 2)) :
    ∀ a v L : ℝ, 0 < a → 0 < v → 0 < L → ∃ C T : ℝ, 1 ≤ C ∧ 0 < T ∧
      ∀ s : RegularSlice F.observation, T ≤ s.time → ∀ p : s.stage.Carrier,
        HasNormalizedSeed_S13 s p a v →
        ∀ y ∈ riemannianBallOf s.metric p (L * Real.sqrt s.time),
          C / s.time ≤ metricScalarAt s.metric y →
          ∃ W : SpatialCanonicalWitness s.metric Hp.epsilon Hp.C1 Hp.C2 y,
            W.capTubeHasNeckChart Hp.epsilon := by
  intro a v L ha hv hL
  obtain ⟨csd, hcsd, hsd⟩ := seed_scale_down_S21.{u}
  obtain ⟨T1, Λ, b, τ, C, hT1, hΛ, hb, hτ, hC, hτb, hW⟩ := hW2 (csd * v) (mul_pos hcsd hv)
  set b1 : ℝ := min a b with hb1
  have hb1pos : 0 < b1 := lt_min ha hb
  have hb1a : b1 ≤ a := min_le_left _ _
  have hb1b : b1 ≤ b := min_le_right _ _
  set q : ℝ := min (min 1 τ) (1 / (3 * C)) with hq
  have hqpos : 0 < q := lt_min (lt_min one_pos hτ) (by positivity)
  have hq1 : q ≤ 1 := (min_le_left _ _).trans (min_le_left _ _)
  have hqτ : q ≤ τ := (min_le_left _ _).trans (min_le_right _ _)
  have hqC : q ≤ 1 / (3 * C) := min_le_right _ _
  have hqC' : 3 * q * C ≤ 1 := by
    have := mul_le_mul_of_nonneg_right hqC (by positivity : (0 : ℝ) ≤ 3 * C)
    rw [one_div, inv_mul_cancel₀ (by positivity)] at this
    nlinarith
  set c3 : ℝ := Real.sqrt q with hc3
  have hc3pos : 0 < c3 := Real.sqrt_pos.mpr hqpos
  have hc3sq : c3 ^ 2 = q := Real.sq_sqrt hqpos.le
  have hc3le : c3 ≤ 1 := by
    rw [hc3]; calc Real.sqrt q ≤ Real.sqrt 1 := Real.sqrt_le_sqrt hq1
      _ = 1 := Real.sqrt_one
  -- recent surgery smallness
  set N0 : ℝ := Hp.parameters.neckRadius 0 with hN0
  have hN0pos : 0 < N0 := Hp.parameters.neckRadius_pos 0 le_rfl
  set ε : ℝ := b1 / (Λ * N0) with hε
  have hΛ0 : 0 < Λ := by linarith
  have hεpos : 0 < ε := by positivity
  obtain ⟨T2, hT2, hrecent⟩ := Hp.recent_cutoff_smallness ε hεpos
  -- the enlargement
  set c2 : ℝ := c3 * b1 with hc2
  have hc2pos : 0 < c2 := mul_pos hc3pos hb1pos
  set A : ℝ := max (1 / (csd * (csd * v))) (L / c2) with hA
  have hApos : 0 < A := lt_max_of_lt_left (by positivity)
  obtain ⟨K1, TA, hK1, hTA, hP⟩ := hP6 A hApos
  refine ⟨max 1 (K1 / (q * b1 ^ 2)), max (max T1 T2) (max TA 1), le_max_left _ _,
    lt_max_of_lt_right (lt_max_of_lt_right one_pos), ?_⟩
  intro s hsT p hseed y hy hRy
  have ht := s.positive
  have hT1s : T1 ≤ s.time := ((le_max_left _ _).trans (le_max_left _ _)).trans hsT
  have hT2s : T2 ≤ s.time := ((le_max_right _ _).trans (le_max_left _ _)).trans hsT
  have hTAs : TA ≤ s.time := ((le_max_left _ _).trans (le_max_right _ _)).trans hsT
  have h1s : 1 ≤ s.time := ((le_max_right _ _).trans (le_max_right _ _)).trans hsT
  have hst : 1 ≤ Real.sqrt s.time := by
    rw [show (1 : ℝ) = Real.sqrt 1 from Real.sqrt_one.symm]; exact Real.sqrt_le_sqrt h1s
  have hstpos : 0 < Real.sqrt s.time := by linarith
  have hsq : Real.sqrt s.time ^ 2 = s.time := Real.sq_sqrt ht.le
  obtain ⟨hsec0, hvol0⟩ := physSeed_S23 s p ha hseed
  set ρ : ℝ := a * Real.sqrt s.time with hρ
  set r : ℝ := b1 * Real.sqrt s.time with hr
  set r0 : ℝ := c3 * r with hr0
  have hrpos : 0 < r := by positivity
  have hr0pos : 0 < r0 := by positivity
  have hrρ : r ≤ ρ := mul_le_mul_of_nonneg_right hb1a hstpos.le
  have hr0r : r0 ≤ r := by
    calc r0 = c3 * r := rfl
      _ ≤ 1 * r := mul_le_mul_of_nonneg_right hc3le hrpos.le
      _ = r := one_mul r
  have hrb : r ≤ b * Real.sqrt s.time := mul_le_mul_of_nonneg_right hb1b hstpos.le
  have hr0sq : r0 ^ 2 = q * b1 ^ 2 * s.time := by
    rw [hr0, hr, mul_pow, mul_pow, hc3sq, hsq]; ring
  -- generic-stage argument
  have hgen : ∀ (j : Fin (s.history.eventCount + 1))
      (hj : s.history.activeStage (sliceTop_S8 s) = j) (p : (s.history.stage j).Carrier),
      (∀ q' ∈ riemannianBallOf (s.history.stageMetric j s.time) p ρ,
        SectionalBoundedBelowAt (s.history.stageMetric j s.time) q' (-(ρ ^ 2)⁻¹)) →
      ENNReal.ofReal (v * ρ ^ 3) ≤ ballVolume (s.history.stageMetric j s.time) p ρ →
      ∀ y ∈ riemannianBallOf (s.history.stageMetric j s.time) p (L * Real.sqrt s.time),
        max 1 (K1 / (q * b1 ^ 2)) / s.time ≤ metricScalarAt (s.history.stageMetric j s.time) y →
        ∃ W : SpatialCanonicalWitness (s.history.stageMetric j s.time) Hp.epsilon Hp.C1 Hp.C2 y,
          W.capTubeHasNeckChart Hp.epsilon := by
    intro j hj p hsec hvol y hy hRy
    -- two scale-downs, before `subst`
    obtain ⟨hs1, hv1⟩ := hsd _ (s.history.stageMetric j s.time) p v ρ r hv hrpos hrρ hsec hvol
    obtain ⟨hs2, hv2⟩ := hsd _ (s.history.stageMetric j s.time) p (csd * v) r r0
      (mul_pos hcsd hv) hr0pos hr0r hs1 hv1
    subst hj
    have hrec : ∀ n (i : Fin (F.tower.history n).eventCount),
        (F.tower.history n).time i.succ ∈ Icc (s.time / 2) s.time →
        ∀ h, Λ * (Hp.records n i).nominalRadius h ≤ r := by
      intro n i hi h
      have h1 := hrecent s.time hT2s n i hi h
      have h2 : Hp.parameters.neckRadius s.time ≤ N0 :=
        Hp.radius_antitone (Set.mem_Ici.mpr le_rfl)
          (show s.time ∈ Ici (0 : ℝ) from ht.le) ht.le
      have h3 : Λ * (Hp.records n i).nominalRadius h ≤ Λ * (ε * N0) :=
        mul_le_mul_of_nonneg_left (h1.trans (mul_le_mul_of_nonneg_left h2 hεpos.le)) hΛ0.le
      have h4 : Λ * (ε * N0) = b1 := by rw [hε]; field_simp
      calc Λ * (Hp.records n i).nominalRadius h ≤ b1 := h4 ▸ h3
        _ = b1 * 1 := (mul_one b1).symm
        _ ≤ b1 * Real.sqrt s.time := mul_le_mul_of_nonneg_left hst hb1pos.le
    have htr := hW s hT1s p r hrpos hrb hs1 hv1 hrec
    have hr0sq' : r0 ^ 2 = q * r ^ 2 := by rw [hr0, mul_pow, hc3sq]
    have hKinv : C / r ^ 2 ≤ ((Real.sqrt 3 * r0) ^ 2)⁻¹ := by
      have e : (Real.sqrt 3 * r0) ^ 2 = (3 * q) * r ^ 2 := by
        rw [mul_pow, Real.sq_sqrt (by norm_num), hr0sq']; ring
      have hCq : C ≤ (3 * q)⁻¹ := by
        rw [← one_div, le_div_iff₀ (by positivity)]
        nlinarith
      rw [e, mul_inv, div_eq_mul_inv]
      exact mul_le_mul_of_nonneg_right hCq (by positivity)
    have hsmall := hasSmall_of_traced_S23 htr hr0pos (hr0r.trans (by linarith))
      (by rw [hr0sq']; exact mul_le_mul_of_nonneg_right hqτ (by positivity)) (div_nonneg hC.le (by positivity)) hKinv
    have hlt : 2 * r0 ^ 2 < s.time := by
      rw [hr0sq]
      have : q * b1 ^ 2 ≤ τ * b ^ 2 := mul_le_mul hqτ (pow_le_pow_left₀ hb1pos.le hb1b 2)
        (by positivity) hτ.le
      have h2 : q * b1 ^ 2 < 1 / 2 := lt_of_le_of_lt this hτb
      calc 2 * (q * b1 ^ 2 * s.time) = (2 * (q * b1 ^ 2)) * s.time := by ring
        _ < 1 * s.time := mul_lt_mul_of_pos_right (by linarith) ht
        _ = s.time := one_mul _
    have hAinv : A⁻¹ ≤ csd * (csd * v) := by
      have h1 : 1 / (csd * (csd * v)) ≤ A := le_max_left _ _
      have := inv_anti₀ (by positivity : 0 < 1 / (csd * (csd * v))) h1
      rwa [one_div, inv_inv] at this
    have hvolA : ENNReal.ofReal (A⁻¹ * r0 ^ 3) ≤ ballVolume (s.history.stageMetric
        (s.history.activeStage (sliceTop_S8 s)) s.time) p r0 := by
      refine le_trans (ENNReal.ofReal_le_ofReal ?_) hv2
      exact mul_le_mul_of_nonneg_right hAinv (by positivity)
    have hr0c2 : r0 = c2 * Real.sqrt s.time := by rw [hr0, hr, hc2]; ring
    have hLA : L * Real.sqrt s.time ≤ A * r0 := by
      have h1 : L / c2 ≤ A := le_max_right _ _
      rw [hr0c2, ← mul_assoc]
      refine mul_le_mul_of_nonneg_right ?_ hstpos.le
      rw [div_le_iff₀ hc2pos] at h1; exact h1
    have hyA := riemannianBallOf_mono _ _ hLA hy
    have hscal : K1 * (r0 ^ 2)⁻¹ ≤ metricScalarAt (s.history.stageMetric
        (s.history.activeStage (sliceTop_S8 s)) s.time) y := by
      refine le_trans ?_ hRy
      rw [hr0sq]
      have : K1 * (q * b1 ^ 2 * s.time)⁻¹ = (K1 / (q * b1 ^ 2)) / s.time := by
        field_simp
      rw [this]
      exact div_le_div_of_nonneg_right (le_max_right _ _) ht.le
    exact hP s hTAs p r0 hlt hsmall hvolA y hyA hscal
  exact hgen (Fin.last _) s.history.activeStage_at_horizon p hsec0 hvol0 y hy hRy

end GC.LongTime.Ch12
