import DifferentialGeometry.Geometry.Flow.RicciFlow.Extinction.Families.AffineComparison
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.MeasureTheory.Measure.Typeclasses.NullSingletonClass



noncomputable section
open Bundle Manifold Set MeasureTheory Filter intervalIntegral
open scoped Manifold ContDiff Topology
open DifferentialGeometry.Geometry.Curvature

namespace DifferentialGeometry.PDE.RicciFlow.Extinction.Families
open CurveShortening

variable {g' g phi : ℝ → ℝ} {a b : ℝ}

private theorem sub_le_integral_of_upperDini_of_le_Ico (hab : a ≤ b)
    (hcont : ContinuousOn g (Icc a b)) (hDini : ∀ x ∈ Ico a b, ∀ r : ℝ, g' x < r →
      ∀ᶠ z in 𝓝[>] x, slope g x z < r)
    (phiint : IntegrableOn phi (Icc a b)) (hphig : ∀ x ∈ Ico a b, g' x ≤ phi x) :
    g b - g a ≤ ∫ y in a..b, phi y := by
  refine le_of_forall_pos_le_add fun ε εpos => ?_
  rcases exists_lt_lowerSemicontinuous_integral_lt phi phiint εpos with
    ⟨G', f_lt_G', G'cont, G'int, G'lt_top, hG'⟩
  set s := {t | g t - g a ≤ ∫ u in a..t, (G' u).toReal} ∩ Icc a b
  have s_closed : IsClosed s := by
    have : ContinuousOn (fun t => (g t - g a, ∫ u in a..t, (G' u).toReal)) (Icc a b) := by
      rw [← uIcc_of_le hab] at G'int hcont ⊢
      exact (hcont.sub continuousOn_const).prodMk (continuousOn_primitive_interval G'int)
    simp only [s, inter_comm]
    exact this.preimage_isClosed_of_isClosed isClosed_Icc OrderClosedTopology.isClosed_le'
  have main : Icc a b ⊆ {t | g t - g a ≤ ∫ u in a..t, (G' u).toReal} := by
    refine s_closed.Icc_subset_of_forall_exists_gt
      (by simp only [integral_same, mem_ofPred_eq, sub_self, le_rfl]) fun t ht v t_lt_v => ?_
    obtain ⟨y, g'_lt_y', y_lt_G'⟩ : ∃ y : ℝ, (g' t : EReal) < y ∧ (y : EReal) < G' t :=
      EReal.lt_iff_exists_real_btwn.1 ((EReal.coe_le_coe_iff.2 (hphig t ht.2)).trans_lt (f_lt_G' t))
    have I1 : ∀ᶠ u in 𝓝[>] t, (u - t) * y ≤ ∫ w in t..u, (G' w).toReal := by
      have B : ∀ᶠ u in 𝓝 t, (y : EReal) < G' u := G'cont.lowerSemicontinuousAt _ _ y_lt_G'
      rcases mem_nhds_iff_exists_Ioo_subset.1 B with ⟨m, M, ⟨hm, hM⟩, H⟩
      have : Ioo t (min M b) ∈ 𝓝[>] t := Ioo_mem_nhdsGT (lt_min hM ht.right.right)
      filter_upwards [this] with u hu
      have I : Icc t u ⊆ Icc a b := Icc_subset_Icc ht.2.1 (hu.2.le.trans (min_le_right _ _))
      calc
        (u - t) * y = ∫ _ in Icc t u, y := by
          simp only [MeasureTheory.integral_const, MeasurableSet.univ, measureReal_restrict_apply,
            univ_inter, hu.left.le, Real.volume_real_Icc_of_le, smul_eq_mul]
        _ ≤ ∫ w in t..u, (G' w).toReal := by
          rw [intervalIntegral.integral_of_le hu.1.le, ← integral_Icc_eq_integral_Ioc]
          apply setIntegral_mono_ae_restrict
          · simp
          · exact IntegrableOn.mono_set G'int I
          · have C1 : ∀ᵐ x : ℝ ∂volume.restrict (Icc t u), G' x < ⊤ :=
              ae_mono (Measure.restrict_mono I le_rfl) G'lt_top
            have C2 : ∀ᵐ x : ℝ ∂volume.restrict (Icc t u), x ∈ Icc t u :=
              ae_restrict_mem measurableSet_Icc
            filter_upwards [C1, C2] with x G'x hx
            apply EReal.coe_le_coe_iff.1
            have : x ∈ Ioo m M := by
              simp only [hm.trans_le hx.left,
                (hx.right.trans_lt hu.right).trans_le (min_le_left M b), mem_Ioo, and_self_iff]
            refine (H this).out.le.trans_eq ?_
            exact (EReal.coe_toReal G'x.ne (f_lt_G' x).ne_bot).symm
    have I2 : ∀ᶠ u in 𝓝[>] t, g u - g t ≤ (u - t) * y := by
      have g'_lt_y : g' t < y := EReal.coe_lt_coe_iff.1 g'_lt_y'
      filter_upwards [hDini t ⟨ht.2.1, ht.2.2⟩ y g'_lt_y,
        self_mem_nhdsWithin] with u hu t_lt_u
      have := mul_le_mul_of_nonneg_left hu.le (sub_pos.2 t_lt_u.out).le
      rwa [← smul_eq_mul, sub_smul_slope] at this
    have I3 : ∀ᶠ u in 𝓝[>] t, g u - g t ≤ ∫ w in t..u, (G' w).toReal := by
      filter_upwards [I1, I2] with u hu1 hu2 using hu2.trans hu1
    have I4 : ∀ᶠ u in 𝓝[>] t, u ∈ Ioc t (min v b) := Ioc_mem_nhdsGT <| lt_min t_lt_v ht.2.2
    rcases (I3.and I4).exists with ⟨x, hx, h'x⟩
    refine ⟨x, ?_, Ioc_subset_Ioc le_rfl (min_le_left _ _) h'x⟩
    calc
      g x - g a = g t - g a + (g x - g t) := by abel
      _ ≤ (∫ w in a..t, (G' w).toReal) + ∫ w in t..x, (G' w).toReal := add_le_add ht.1 hx
      _ = ∫ w in a..x, (G' w).toReal := by
        apply integral_add_adjacent_intervals
        · rw [intervalIntegrable_iff_integrableOn_Ioc_of_le ht.2.1]
          exact IntegrableOn.mono_set G'int
            (Ioc_subset_Icc_self.trans (Icc_subset_Icc le_rfl ht.2.2.le))
        · rw [intervalIntegrable_iff_integrableOn_Ioc_of_le h'x.1.le]
          apply IntegrableOn.mono_set G'int
          exact Ioc_subset_Icc_self.trans (Icc_subset_Icc ht.2.1 (h'x.2.trans (min_le_right _ _)))
  calc
    g b - g a ≤ ∫ y in a..b, (G' y).toReal := main (right_mem_Icc.2 hab)
    _ ≤ (∫ y in a..b, phi y) + ε := by
      convert! hG'.le <;>
        · rw [intervalIntegral.integral_of_le hab]
          simp only [integral_Icc_eq_integral_Ioc', Real.volume_singleton]

private theorem upperDini_mul_add {F f B : ℝ → ℝ} {x F' B' L : ℝ}
    (hF : HasDerivWithinAt F F' (Ioi x) x)
    (hB : HasDerivWithinAt B B' (Ioi x) x)
    (hf : ContinuousWithinAt f (Ioi x) x) (hpos : 0 < F x)
    (hDini : ∀ r : ℝ, L < r → ∀ᶠ y in 𝓝[>] x, slope f x y < r) :
    ∀ r : ℝ, F x * L + F' * f x + B' < r →
      ∀ᶠ y in 𝓝[>] x, slope (fun z => F z * f z + B z) x y < r := by
  intro r hr
  let epsilon := (r - (F x * L + F' * f x + B')) / 2
  have hepsilon : 0 < epsilon := by dsimp [epsilon]; linarith
  have hFt := (hasDerivWithinAt_iff_tendsto_slope' (lt_irrefl x)).mp hF
  have hBt := (hasDerivWithinAt_iff_tendsto_slope' (lt_irrefl x)).mp hB
  have haux : ∀ᶠ y in 𝓝[>] x,
      slope F x y * f y + slope B x y < F' * f x + B' + epsilon :=
    ((hFt.mul hf).add hBt).eventually_lt_const (by linarith)
  have hmain := hDini (L + epsilon / F x) (by
    exact lt_add_of_pos_right L (div_pos hepsilon hpos))
  filter_upwards [haux, hmain] with y hyaux hymain
  have hmul := mul_lt_mul_of_pos_left hymain hpos
  have hcancel : F x * (L + epsilon / F x) = F x * L + epsilon := by
    field_simp [hpos.ne']
  rw [hcancel] at hmul
  have heq : slope (fun z => F z * f z + B z) x y =
      F x * slope f x y + slope F x y * f y + slope B x y := by
    simp only [slope, vsub_eq_sub, smul_eq_mul]
    ring
  rw [heq]
  dsimp [epsilon] at hyaux hmul
  linarith

private theorem missing_time_Ico_eq_Icc (intervals : Finset (ℝ × ℝ)) (a b : ℝ) :
    volume (Icc a b \ {t | ∃ uv ∈ intervals, t ∈ Ico uv.1 uv.2}) =
      volume (Icc a b \ {t | ∃ uv ∈ intervals, t ∈ Icc uv.1 uv.2}) := by
  let ends : Set ℝ := Prod.snd '' (intervals : Set (ℝ × ℝ))
  have hfinite : ends.Finite := intervals.finite_toSet.image Prod.snd
  apply measure_congr
  filter_upwards [hfinite.countable.ae_notMem volume] with t ht
  have hgood : (∃ uv ∈ intervals, t ∈ Icc uv.1 uv.2) ↔
      (∃ uv ∈ intervals, t ∈ Ico uv.1 uv.2) := by
    constructor
    · rintro ⟨uv, huv, htu, htv⟩
      refine ⟨uv, huv, htu, ?_⟩
      rcases lt_or_eq_of_le htv with hlt | heq
      · exact hlt
      · exact False.elim (ht ⟨uv, huv, heq.symm⟩)
    · rintro ⟨uv, huv, htu, htv⟩
      exact ⟨uv, huv, htu, htv.le⟩
  apply propext
  change (t ∈ Icc a b ∧ ¬ (∃ uv ∈ intervals, t ∈ Ico uv.1 uv.2)) ↔
    (t ∈ Icc a b ∧ ¬ (∃ uv ∈ intervals, t ∈ Icc uv.1 uv.2))
  rw [hgood]

private theorem weighted_error_integral {F : ℝ → ℝ} {a b R error K mu : ℝ}
    {bad : Set ℝ} (hab : a ≤ b) (hF : ContinuousOn F (Icc a b))
    (hF0 : ∀ x ∈ Icc a b, 0 ≤ F x) (hFR : ∀ x ∈ Icc a b, F x ≤ R)
    (hR : 0 ≤ R) (he : 0 ≤ error) (hK : 0 ≤ K) (hmu : 0 ≤ mu)
    (hbad : MeasurableSet bad) (hsub : bad ⊆ Icc a b)
    (hm : volume bad ≤ ENNReal.ofReal mu) :
    IntegrableOn (fun x => error * F x + bad.indicator (fun y => K * F y) x) (Icc a b) ∧
    (∫ x in a..b, error * F x + bad.indicator (fun y => K * F y) x) ≤
      R * (error * (b - a) + K * mu) := by
  have hFi : IntegrableOn F (Icc a b) := hF.integrableOn_Icc
  have hei := hFi.const_mul error
  have hKi := (hFi.const_mul K).indicator hbad
  have heint : IntervalIntegrable (fun x => error * F x) volume a b :=
    (intervalIntegrable_iff_integrableOn_Icc_of_le hab).mpr hei
  have hKint : IntervalIntegrable (bad.indicator (fun x => K * F x)) volume a b :=
    (intervalIntegrable_iff_integrableOn_Icc_of_le hab).mpr hKi
  refine ⟨hei.add hKi, ?_⟩
  have hbase : (∫ x in a..b, error * F x) ≤ error * R * (b - a) := by
    have hc : IntervalIntegrable (fun _ : ℝ => error * R) volume a b :=
      continuous_const.intervalIntegrable a b
    have hh := intervalIntegral.integral_mono_on hab heint hc
      (fun x hx => mul_le_mul_of_nonneg_left (hFR x hx) he)
    simpa only [intervalIntegral.integral_const, smul_eq_mul, mul_comm (b - a)] using hh
  have hfinite : volume bad < ⊤ := hm.trans_lt ENNReal.ofReal_lt_top
  have hnorm : ‖∫ x in bad, K * F x‖ ≤ K * R * volume.real bad :=
    norm_setIntegral_le_of_norm_le_const hfinite (fun x hx => by
      rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg hK (hF0 x (hsub hx)))]
      exact mul_le_mul_of_nonneg_left (hFR x (hsub hx)) hK)
  have hreal : volume.real bad ≤ mu := by
    exact (ENNReal.toReal_mono ENNReal.ofReal_ne_top hm).trans_eq (ENNReal.toReal_ofReal hmu)
  have hbadIntegral : (∫ x in a..b, bad.indicator (fun y => K * F y) x) =
      ∫ x in bad, K * F x := by
    rw [intervalIntegral.integral_of_le hab, ← integral_Icc_eq_integral_Ioc,
      setIntegral_indicator hbad, inter_eq_right.mpr hsub]
  rw [intervalIntegral.integral_add heint hKint, hbadIntegral]
  have habsnorm : |∫ x in bad, K * F x| ≤ K * R * volume.real bad := by
    simpa only [Real.norm_eq_abs] using hnorm
  have hcost : (∫ x in bad, K * F x) ≤ K * R * mu :=
    (le_abs_self _).trans (habsnorm.trans
      (mul_le_mul_of_nonneg_left hreal (mul_nonneg hK hR)))
  nlinarith

private theorem upperDini_of_increments {f : ℝ → ℝ} {x b L : ℝ} (hxb : x < b)
    (hDini : ∀ epsilon > 0, ∃ delta > 0, ∀ h ∈ Ioo (0 : ℝ) delta,
      x + h ≤ b → (f (x + h) - f x) / h ≤ L + epsilon) :
    ∀ r : ℝ, L < r → ∀ᶠ y in 𝓝[>] x, slope f x y < r := by
  intro r hr
  obtain ⟨delta, hd, hh⟩ := hDini ((r - L) / 2) (by linarith)
  filter_upwards [Ioo_mem_nhdsGT (lt_min (by linarith : x < x + delta) hxb)] with y hy
  have hinc : y - x ∈ Ioo (0 : ℝ) delta := by
    exact ⟨sub_pos.mpr hy.1, by have := hy.2.trans_le (min_le_left _ _); linarith⟩
  have hbound := hh (y - x) hinc (by have := hy.2.trans_le (min_le_right _ _); linarith)
  rw [add_sub_cancel] at hbound
  have heq : slope f x y = (f y - f x) / (y - x) := by
    simp only [slope, vsub_eq_sub, smul_eq_mul, div_eq_mul_inv, mul_comm]
  rw [heq]
  linarith


private theorem upperDini_of_increment_bound {f : ℝ → ℝ} {a b x Cup : ℝ}
    (hx : x ∈ Ico a b)
    (hup : ∀ s ∈ Icc a b, ∀ t ∈ Icc s b, f t - f s ≤ Cup * (t - s)) :
    ∀ r : ℝ, Cup < r → ∀ᶠ y in 𝓝[>] x, slope f x y < r := by
  apply upperDini_of_increments hx.2
  intro epsilon hepsilon
  refine ⟨b - x, sub_pos.mpr hx.2, ?_⟩
  intro h hh hright
  have hbound := hup x ⟨hx.1, hx.2.le⟩ (x + h) ⟨by linarith [hh.1], hright⟩
  have hquot : (f (x + h) - f x) / h ≤ Cup := by
    apply (div_le_iff₀ hh.1).mpr
    simpa only [add_sub_cancel_left] using hbound
  linarith

private theorem rho_int {rho : ℝ → ℝ} {a b s t : ℝ}
    (hc : ContinuousOn rho (Icc a b)) (hs : s ∈ Icc a b) (ht : t ∈ Icc a b) :
    IntervalIntegrable rho volume s t :=
  (hc.mono (uIcc_subset_Icc hs ht)).intervalIntegrable

private theorem primitive_deriv {rho : ℝ → ℝ} {a b s t : ℝ}
    (hc : ContinuousOn rho (Icc a b)) (hs : s ∈ Icc a b) (ht : t ∈ Icc a b) :
    HasDerivWithinAt (fun v => ∫ w in s..v, rho w) (rho t) (Icc a b) t := by
  let : Fact (t ∈ Icc a b) := ⟨ht⟩
  have hm : StronglyMeasurableAtFilter rho (𝓝[Icc a b] t) volume :=
    ⟨Icc a b, self_mem_nhdsWithin, hc.aestronglyMeasurable measurableSet_Icc⟩
  exact intervalIntegral.integral_hasDerivWithinAt_right (rho_int hc hs ht) hm (hc t ht)

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [CompleteSpace E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {Q : Type*} [TopologicalSpace Q] [ChartedSpace H Q] [IsManifold I ∞ Q]
    [SigmaCompactSpace Q] [hT2 : T2Space Q] [hCompact : CompactSpace Q]
    [hConnected : ConnectedSpace Q] [hBoundary : I.Boundaryless]
    {D : RealTimeInterval} {a b : ℝ}

include hT2 hCompact hConnected hBoundary

theorem rfs_width_gap_comparison (B : RicciBackground (I := I) (M := Q) D a b)
    (f : ℝ → ℝ) (Abar Cup mu error : ℝ)
    (hAbar : 0 ≤ Abar) (hCup : 0 ≤ Cup) (hmu : 0 ≤ mu) (herror : 0 ≤ error)
    (hcontinuous : ContinuousOn f (Icc a b))
    (hrange : ∀ t ∈ Icc a b, 0 ≤ f t ∧ f t ≤ Abar)
    (hup : ∀ s ∈ Icc a b, ∀ t ∈ Icc s b, f t - f s ≤ Cup * (t - s))
    (intervals : Finset (ℝ × ℝ))
    (hintervals : ∀ uv ∈ intervals, a < uv.1 ∧ uv.1 ≤ uv.2 ∧ uv.2 < b)
    (hgap : volume (Icc a b \ {t | ∃ uv ∈ intervals, t ∈ Icc uv.1 uv.2}) ≤
      ENNReal.ofReal mu)
    (hDini : ∀ uv ∈ intervals, ∀ v ∈ Ico uv.1 uv.2,
      ∀ epsilon > 0, ∃ delta > 0, ∀ h ∈ Ioo (0 : ℝ) delta, v + h ≤ uv.2 →
        (f (v + h) - f v) / h ≤
          -2 * Real.pi - halfScalarMinimum B.family v * f v + error + epsilon) :
    f b ≤ affineComparison B.family a b (f a) +
      Real.exp (2 * scalarComparisonBound B.family a b * (b - a)) *
        (error * (b - a) + (Cup + scalarComparisonBound B.family a b * Abar + 2 * Real.pi) * mu) := by
  classical
  let _ := hintervals
  obtain ⟨hc, _, hM, hbound, _⟩ := rfs_width_flow_background B
  let rho := halfScalarMinimum B.family
  let M := scalarComparisonBound B.family a b
  let F := areaIntegratingFactor B.family a
  let P : ℝ → ℝ := fun t => ∫ x in a..t, F x
  let R := Real.exp (M * (b - a))
  let K := Cup + M * Abar + 2 * Real.pi
  let good : Set ℝ := {t | ∃ uv ∈ intervals, t ∈ Ico uv.1 uv.2}
  let bad := Icc a b \ good
  let L : ℝ → ℝ := fun t => if t ∈ good then -2 * Real.pi - rho t * f t + error else Cup
  let J : ℝ → ℝ := fun t => F t * f t + 2 * Real.pi * P t
  let jp : ℝ → ℝ := fun t => F t * L t + (rho t * F t) * f t + 2 * Real.pi * F t
  let phi : ℝ → ℝ := fun t => error * F t + bad.indicator (fun x => K * F x) t
  have ha : a ∈ Icc a b := ⟨le_rfl, B.lt.le⟩
  have hb : b ∈ Icc a b := ⟨B.lt.le, le_rfl⟩
  have hFc : ContinuousOn F (Icc a b) := areaIntegratingFactor_continuousOn B ha
  have hFp : ∀ t, 0 < F t := areaIntegratingFactor_pos B.family a
  have hFform : F = fun t => Real.exp (∫ x in a..t, rho x) := by
    funext t
    dsimp [F, areaIntegratingFactor, rho, halfScalarMinimum]
    rw [intervalIntegral.integral_div]
    congr 1
    ring
  have hFd : ∀ t ∈ Icc a b, HasDerivWithinAt F (rho t * F t) (Icc a b) t := by
    intro t ht
    rw [hFform]
    simpa only [mul_comm] using (primitive_deriv hc ha ht).exp
  have hPd : ∀ t ∈ Icc a b, HasDerivWithinAt P (F t) (Icc a b) t :=
    fun t ht => primitive_deriv hFc ha ht
  have hPc : ContinuousOn P (Icc a b) := fun t ht => (hPd t ht).continuousWithinAt
  have hJc : ContinuousOn J (Icc a b) :=
    (hFc.mul hcontinuous).add (continuousOn_const.mul hPc)
  have hgood : MeasurableSet good := by
    have heq : good = ⋃ uv ∈ intervals, Ico uv.1 uv.2 := by
      ext t
      simp only [good, mem_ofPred_eq, mem_iUnion, exists_prop]
    rw [heq]
    exact intervals.measurableSet_biUnion (fun _ _ => measurableSet_Ico)
  have hbad : MeasurableSet bad := measurableSet_Icc.diff hgood
  have hbadsub : bad ⊆ Icc a b := sdiff_subset
  have hbadmeasure : volume bad ≤ ENNReal.ofReal mu := by
    rw [missing_time_Ico_eq_Icc intervals a b]
    exact hgap
  have hRpos : 0 < R := Real.exp_pos _
  have hK : 0 ≤ K := by dsimp [K]; positivity
  have hFR : ∀ t ∈ Icc a b, F t ≤ R := by
    intro t ht
    have hft := (rfs_width_affine_comparison B).2.2.1 a ha t ht
    exact hft.2.trans (Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left
      (sub_le_sub_right ht.2 a) hM))
  have hforcing := weighted_error_integral B.lt.le hFc
    (fun t _ => (hFp t).le) hFR hRpos.le herror hK hmu hbad hbadsub hbadmeasure
  have hLd : ∀ t ∈ Ico a b, ∀ r : ℝ, L t < r →
      ∀ᶠ y in 𝓝[>] t, slope f t y < r := by
    intro t ht
    by_cases htg : t ∈ good
    · obtain ⟨uv, huv, htuv⟩ := htg
      have hd := upperDini_of_increments htuv.2 (hDini uv huv t htuv)
      simpa only [L, if_pos (show t ∈ good from ⟨uv, huv, htuv⟩), rho] using hd
    · simpa only [L, if_neg htg] using upperDini_of_increment_bound ht hup
  have hJd : ∀ t ∈ Ico a b, ∀ r : ℝ, jp t < r →
      ∀ᶠ y in 𝓝[>] t, slope J t y < r := by
    intro t ht
    have htc : t ∈ Icc a b := ⟨ht.1, ht.2.le⟩
    have hnhds : Icc a b ∈ 𝓝[>] t := by
      filter_upwards [Ioo_mem_nhdsGT ht.2] with y hy
      exact ⟨ht.1.trans hy.1.le, hy.2.le⟩
    have hft := (hFd t htc).mono_of_mem_nhdsWithin hnhds
    have hpt := ((hPd t htc).const_mul (2 * Real.pi)).mono_of_mem_nhdsWithin hnhds
    have hfc := (hcontinuous t htc).mono_of_mem_nhdsWithin hnhds
    exact upperDini_mul_add hft hpt hfc (hFp t) (hLd t ht)
  have hjphi : ∀ t ∈ Ico a b, jp t ≤ phi t := by
    intro t ht
    have htc : t ∈ Icc a b := ⟨ht.1, ht.2.le⟩
    by_cases htg : t ∈ good
    · have htb : t ∉ bad := fun h => h.2 htg
      simp only [jp, L, if_pos htg, phi, indicator_of_notMem htb]
      ring_nf
      exact le_rfl
    · have htb : t ∈ bad := ⟨htc, htg⟩
      have hrhof : rho t * f t ≤ M * Abar :=
        (mul_le_mul_of_nonneg_right (le_trans (le_abs_self _) (hbound t htc))
          (hrange t htc).1).trans (mul_le_mul_of_nonneg_left (hrange t htc).2 hM)
      simp only [jp, L, if_neg htg, phi, indicator_of_mem htb]
      have hh := mul_le_mul_of_nonneg_left hrhof (hFp t).le
      have he := mul_nonneg herror (hFp t).le
      dsimp [K]
      nlinarith
  have hmain := sub_le_integral_of_upperDini_of_le_Ico
    B.lt.le hJc hJd hforcing.1 hjphi
  have hmain' := hmain.trans hforcing.2
  have hFa : F a = 1 := by dsimp [F, areaIntegratingFactor]; simp
  have hPa : P a = 0 := by dsimp [P]; simp
  change F b * f b + 2 * Real.pi * P b - (F a * f a + 2 * Real.pi * P a) ≤
    R * (error * (b - a) + K * mu) at hmain'
  rw [hFa, hPa] at hmain'
  simp only [one_mul, mul_zero, add_zero] at hmain'
  have hlower := ((rfs_width_affine_comparison B).2.2.1 a ha b hb).1
  have hprod : 1 ≤ R * F b := by
    have hh := mul_le_mul_of_nonneg_left hlower hRpos.le
    have heq : R * Real.exp (-M * (b - a)) = 1 := by
      dsimp [R]
      rw [← Real.exp_add]
      have hexponent : M * (b - a) + -M * (b - a) = 0 := by ring
      rw [hexponent, Real.exp_zero]
    change R * Real.exp (-M * (b - a)) ≤ R * F b at hh
    rwa [heq] at hh
  have hEinv : (F b)⁻¹ ≤ R := (inv_le_iff_one_le_mul₀ (hFp b)).mpr hprod
  have hE : 0 ≤ error * (b - a) + K * mu :=
    add_nonneg (mul_nonneg herror (sub_nonneg.mpr B.lt.le)) (mul_nonneg hK hmu)
  have hscaled := mul_le_mul_of_nonneg_left hmain' (inv_pos.mpr (hFp b)).le
  have hcost := mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_right hEinv hRpos.le) hE
  have hcanc : (F b)⁻¹ * F b = 1 := inv_mul_cancel₀ (hFp b).ne'
  have hRR : R * R = Real.exp (2 * M * (b - a)) := by
    dsimp [R]
    rw [← Real.exp_add]
    congr 1
    ring
  change f b ≤ (F b)⁻¹ * (f a - 2 * Real.pi * P b) +
    Real.exp (2 * M * (b - a)) * (error * (b - a) + K * mu)
  rw [← hRR]
  have hleft : (F b)⁻¹ * (F b * f b + 2 * Real.pi * P b - f a) =
      f b - (F b)⁻¹ * (f a - 2 * Real.pi * P b) := by
    rw [mul_sub, mul_add, ← mul_assoc, hcanc, one_mul]
    ring
  rw [hleft, ← mul_assoc] at hscaled
  simpa only [add_comm] using (sub_le_iff_le_add.mp (hscaled.trans hcost))

end DifferentialGeometry.PDE.RicciFlow.Extinction.Families
