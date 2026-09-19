import DifferentialGeometry.Geometry.Flow.RicciFlow.Extinction.CurveShortening.Evolution
import DifferentialGeometry.Geometry.Flow.RicciFlow.Evolution.Scalar.JointRegularity
import DifferentialGeometry.Geometry.Flow.RicciFlow.Extinction.Width.LeastArea
import DifferentialGeometry.Geometry.Flow.RicciFlow.Extinction.Width.ClassWidth
import DifferentialGeometry.Geometry.Flow.RicciFlow.Extinction.CurveShortening.LocalExistence
import DifferentialGeometry.Geometry.Flow.RicciFlow.Extinction.CurveShortening.LoopFamilyVelocityExtension
import DifferentialGeometry.Geometry.Flow.RicciFlow.Extinction.CurveShortening.VelocityExtensionChartReading
import DifferentialGeometry.Analysis.ODE.TimeDependentFlow.SmoothDependence.GlobalClosedManifold
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.ODE.Gronwall
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

noncomputable section

open Bundle Manifold Set MeasureTheory Filter
open scoped Manifold ContDiff Topology
open DifferentialGeometry.Geometry.Curvature

namespace DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening

open Surgery.Topology
private theorem integral_slope_ge {g : ℝ → ℝ} {a b x : ℝ} (hg : ContinuousOn g (Icc a b))
    (hx : x ∈ Icc a b) (hxb : x < b) {ε : ℝ} (hε : 0 < ε) :
    ∃ δ > 0, ∀ h ∈ Ioo (0 : ℝ) δ, x + h ≤ b →
      g x - ε ≤ h⁻¹ * ∫ y in x..(x + h), g y := by
  obtain ⟨δ, hδpos, hδ⟩ := (Metric.continuousWithinAt_iff.mp (hg x hx)) ε hε
  refine ⟨min δ (b - x), lt_min hδpos (sub_pos.mpr hxb), ?_⟩
  intro h hh hB
  have hh0 : 0 < h := hh.1
  have hδ₁ : h < δ := lt_of_lt_of_le hh.2 (min_le_left _ _)
  have hδ₂ : h < b - x := lt_of_lt_of_le hh.2 (min_le_right _ _)
  have hz : x + h ≤ b := by linarith
  have hxle : x ≤ x + h := by linarith
  have hsub : Icc x (x + h) ⊆ Icc a b := by
    intro y hy
    exact ⟨le_trans hx.1 hy.1, le_trans hy.2 hz⟩
  have hgi : IntervalIntegrable g volume x (x + h) := by
    have hcont : ContinuousOn g (uIcc x (x + h)) := by
      rw [uIcc_of_le hxle]
      exact hg.mono hsub
    exact hcont.intervalIntegrable
  have hci : IntervalIntegrable (fun _ : ℝ => g x - ε) volume x (x + h) := intervalIntegrable_const
  have hle : ∀ y ∈ Icc x (x + h), g x - ε ≤ g y := by
    intro y hy
    have hyd : dist y x < δ := by
      rw [Real.dist_eq, abs_of_nonneg (by linarith [hy.1])]
      linarith [hy.2]
    have hyε : dist (g y) (g x) < ε := hδ (hsub hy) hyd
    rw [Real.dist_eq, abs_lt] at hyε
    linarith [hyε.1]
  have hconst : (∫ y in x..(x + h), (fun _ : ℝ => g x - ε) y) = h * (g x - ε) := by
    rw [intervalIntegral.integral_const, smul_eq_mul]
    ring
  have hineq : h * (g x - ε) ≤ ∫ y in x..(x + h), g y := by
    rw [← hconst]
    exact intervalIntegral.integral_mono_on hxle hci hgi hle
  calc g x - ε = h⁻¹ * (h * (g x - ε)) := by field_simp
    _ ≤ h⁻¹ * ∫ y in x..(x + h), g y :=
      mul_le_mul_of_nonneg_left hineq (inv_nonneg.mpr hh0.le)

private theorem sub_sub_sub_swap (a b c d : ℝ) : (a - b) - (c - d) = (a - c) - (b - d) := by
  ring

private theorem inv_mul_sub (t a c : ℝ) : t⁻¹ * (a - c) = a * t⁻¹ - c * t⁻¹ := by
  ring

private theorem slope_neg_eq (f : ℝ → ℝ) (x z : ℝ) : slope (-f) x z = - slope f x z := by
  simp only [slope, Pi.neg_apply, vsub_eq_sub, smul_eq_mul]
  ring

private theorem slope_eq_div (f : ℝ → ℝ) (x z : ℝ) : slope f x z = (f z - f x) / (z - x) := by
  rw [slope, smul_eq_mul, vsub_eq_sub, div_eq_mul_inv, mul_comm]

private theorem exists_delta_of_eventually_sdiff {P : ℝ → Prop} {a b x : ℝ}
    (h : ∀ᶠ z in 𝓝[Icc a b \ {x}] x, P z) (hax : a ≤ x) :
    ∃ δ > 0, ∀ h' ∈ Ioo (0 : ℝ) δ, x + h' ≤ b → P (x + h') := by
  rw [eventually_nhdsWithin_iff] at h
  obtain ⟨B, hB, hsub⟩ := Filter.eventually_iff_exists_mem.mp h
  obtain ⟨δ, hδpos, hball⟩ := Metric.mem_nhds_iff.mp hB
  refine ⟨δ, hδpos, fun h' hh' hb => hsub (x + h') (hball ?_) ?_⟩
  · rw [Metric.mem_ball, Real.dist_eq, add_sub_cancel_left, abs_of_pos hh'.1]
    exact hh'.2
  · refine ⟨⟨by linarith [hh'.1], hb⟩, ?_⟩
    simp only [Set.mem_singleton_iff]
    linarith [hh'.1]

private theorem exp_integral_deriv_bound {rho : ℝ → ℝ} {s t x : ℝ}
    (hrho : ContinuousOn rho (Icc s t)) (hx : x ∈ Ioo s t) {ε : ℝ} (hε : 0 < ε) :
    ∃ δ > 0, ∀ h ∈ Ioo (0 : ℝ) δ, x + h ≤ t →
      |(Real.exp (∫ w in s..(x + h), rho w) - Real.exp (∫ w in s..x, rho w)) / h
        - Real.exp (∫ w in s..x, rho w) * rho x| < ε := by
  have hxIcc : x ∈ Icc s t := ⟨hx.1.le, hx.2.le⟩
  have hix : IntervalIntegrable rho volume s x := by
    have hcont : ContinuousOn rho (uIcc s x) := by
      rw [uIcc_of_le hx.1.le]
      exact hrho.mono (Icc_subset_Icc le_rfl hx.2.le)
    exact hcont.intervalIntegrable
  have hFTC : HasDerivWithinAt (fun u => ∫ w in s..u, rho w) (rho x) (Icc s t) x := by
    have := Fact.mk hxIcc
    exact intervalIntegral.integral_hasDerivWithinAt_right (s := Icc s t) (t := Icc s t) hix
      (hrho.stronglyMeasurableAtFilter_nhdsWithin measurableSet_Icc x) (hrho x hxIcc)
  have hφ : HasDerivWithinAt (fun u => Real.exp (∫ w in s..u, rho w))
      (Real.exp (∫ w in s..x, rho w) * rho x) (Icc s t) x := hFTC.exp
  have hup := hφ.limsup_slope_le
    (r := Real.exp (∫ w in s..x, rho w) * rho x + ε) (by linarith)
  have hdn := hφ.neg.limsup_slope_le
    (r := -(Real.exp (∫ w in s..x, rho w) * rho x) + ε) (by linarith)
  have hev : ∀ᶠ z in 𝓝[Icc s t \ {x}] x,
      |(Real.exp (∫ w in s..z, rho w) - Real.exp (∫ w in s..x, rho w)) / (z - x)
        - Real.exp (∫ w in s..x, rho w) * rho x| < ε := by
    filter_upwards [hup, hdn, self_mem_nhdsWithin] with z hzup hzdn hzS
    have hzx : z ≠ x := by
      have h1 := hzS.2
      simpa only [Set.mem_singleton_iff] using h1
    rw [slope_neg_eq] at hzdn
    rw [slope_eq_div] at hzup hzdn
    rw [abs_lt]
    exact ⟨by linarith, by linarith⟩
  obtain ⟨δ, hδpos, hδ⟩ := exists_delta_of_eventually_sdiff
    (P := fun z => |(Real.exp (∫ w in s..z, rho w) - Real.exp (∫ w in s..x, rho w)) / (z - x)
      - Real.exp (∫ w in s..x, rho w) * rho x| < ε) hev hx.1.le
  refine ⟨δ, hδpos, fun h hh hb => ?_⟩
  simpa only [add_sub_cancel_left] using hδ h hh hb

private theorem areaExpansion (h φz φx Az Ax Iz Ix P : ℝ) (hIP : Iz - Ix = P) :
    ((φz * Az - Iz) - (φx * Ax - Ix)) * h⁻¹ =
      φz * ((Az - Ax) / h) + Ax * ((φz - φx) / h) - P * h⁻¹ := by
  have h1 : (φz * Az - Iz) - (φx * Ax - Ix) = (φz * Az - φx * Ax) - (Iz - Ix) := by ring
  rw [h1, hIP]
  ring

private theorem le_integral_of_dini_right {f g : ℝ → ℝ} {a b : ℝ} (hab : a ≤ b)
    (hf : ContinuousOn f (Icc a b)) (hg : ContinuousOn g (Icc a b))
    (h : ∀ x ∈ Ico a b, ∀ ε > 0, ∃ δ > 0, ∀ h' ∈ Ioo (0 : ℝ) δ, x + h' ≤ b →
      (f (x + h') - f x) / h' ≤ g x + ε) :
    f b - f a ≤ ∫ x in a..b, g x := by
  have hPc : ContinuousOn (fun v : ℝ => ∫ y in a..v, g y) (Icc a b) := by
    have hgu : IntegrableOn g (uIcc a b) volume := by
      rw [uIcc_of_le hab]
      exact hg.integrableOn_compact isCompact_Icc
    simpa [uIcc_of_le hab] using intervalIntegral.continuousOn_primitive_interval hgu
  have hlim : ∀ x ∈ Ico a b, ∀ r : ℝ, (0 : ℝ) < r → ∃ᶠ z in 𝓝[>] x,
      (z - x)⁻¹ * ((f z - ∫ y in a..z, g y) - (f x - ∫ y in a..x, g y)) < r := by
    intro x hx r hr
    have hxab : x ∈ Icc a b := ⟨hx.1, hx.2.le⟩
    have hxb : x < b := hx.2
    obtain ⟨δ₁, hδ₁pos, hδ₁⟩ := h x hx (r / 4) (by linarith)
    obtain ⟨δ₂, hδ₂pos, hδ₂⟩ := integral_slope_ge hg hxab hxb (by linarith : (0 : ℝ) < r / 4)
    have hδpos : 0 < min (min δ₁ δ₂) (b - x) := lt_min (lt_min hδ₁pos hδ₂pos) (sub_pos.mpr hxb)
    have hx1 : x - 1 < x := by linarith
    have hx2 : x < x + min (min δ₁ δ₂) (b - x) := by linarith
    have hev : ∀ᶠ z in 𝓝[>] x,
        (z - x)⁻¹ * ((f z - ∫ y in a..z, g y) - (f x - ∫ y in a..x, g y)) < r := by
      rw [eventually_nhdsWithin_iff]
      filter_upwards [Ioo_mem_nhds hx1 hx2] with z hz hzx
      have hh0 : 0 < z - x := sub_pos.mpr hzx
      have hxz : x + (z - x) = z := by ring
      have hzδ : z - x < min (min δ₁ δ₂) (b - x) := by linarith [hz.2]
      have hz₁ : z - x < δ₁ := lt_of_lt_of_le hzδ (le_trans (min_le_left _ _) (min_le_left _ _))
      have hz₂ : z - x < δ₂ := lt_of_lt_of_le hzδ (le_trans (min_le_left _ _) (min_le_right _ _))
      have hzb : z ≤ b := by linarith [lt_of_lt_of_le hzδ (min_le_right _ _)]
      have hfbound : (f z - f x) / (z - x) ≤ g x + r / 4 :=
        (by have h := hδ₁ (z - x) ⟨hh0, hz₁⟩ (by linarith); rwa [hxz] at h)
      have hgbound : g x - r / 4 ≤ (z - x)⁻¹ * ∫ y in x..z, g y :=
        (by have h := hδ₂ (z - x) ⟨hh0, hz₂⟩ (by linarith); rwa [hxz] at h)
      have hzab : z ∈ Icc a b := ⟨le_trans hx.1 hzx.le, hzb⟩
      have hiz : IntervalIntegrable g volume a z := by
        have hcont : ContinuousOn g (uIcc a z) := by
          rw [uIcc_of_le (le_trans hx.1 hzx.le)]
          exact hg.mono (fun y hy => ⟨hy.1, le_trans hy.2 hzb⟩)
        exact hcont.intervalIntegrable
      have hix : IntervalIntegrable g volume a x := by
        have hcont : ContinuousOn g (uIcc a x) := by
          rw [uIcc_of_le hx.1]
          exact hg.mono (Icc_subset_Icc_right hx.2.le)
        exact hcont.intervalIntegrable
      have hPsub : (∫ y in a..z, g y) - (∫ y in a..x, g y) = ∫ y in x..z, g y :=
        intervalIntegral.integral_interval_sub_left hiz hix
      rw [sub_sub_sub_swap (f z) (∫ y in a..z, (g y)) (f x) (∫ y in a..x, (g y))]
      rw [inv_mul_sub (z - x) (f z - f x) ((∫ y in a..z, (g y)) - ∫ y in a..x, (g y)), hPsub]
      have hA : (f z - f x) * (z - x)⁻¹ ≤ g x + r / 4 := by
        rw [div_eq_mul_inv] at hfbound
        exact hfbound
      have hB : g x - r / 4 ≤ (∫ y in x..z, g y) * (z - x)⁻¹ := by
        rw [mul_comm]
        exact hgbound
      linarith
    exact hev.frequently
  have hgron := le_gronwallBound_of_liminf_deriv_right_le
    (f := fun v : ℝ => f v - ∫ y in a..v, g y) (f' := fun _ => (0 : ℝ))
    (δ := f a) (K := 0) (ε := 0) (hf.sub hPc) (fun x hx r hr => hlim x hx r hr)
    (by simp [intervalIntegral.integral_same])
    (fun x _ => by norm_num)
  have hb := hgron b ⟨hab, le_rfl⟩
  rw [gronwallBound_K0] at hb
  simp only [zero_mul, add_zero] at hb
  linarith

private theorem le_of_dini_interior {C : ℝ → ℝ} {a b : ℝ} (hab : a ≤ b)
    (hC : ContinuousOn C (Icc a b))
    (h : ∀ x ∈ Ioo a b, ∀ ε > 0, ∃ δ > 0, ∀ h' ∈ Ioo (0 : ℝ) δ, x + h' ≤ b →
      (C (x + h') - C x) / h' ≤ ε) :
    C b ≤ C a := by
  rcases eq_or_lt_of_le hab with hEq | hLt
  · rw [← hEq]
  have hkey : ∀ c ∈ Ioo a b, C b ≤ C c := by
    intro c hc
    have hsub : Icc c b ⊆ Icc a b := Icc_subset_Icc hc.1.le le_rfl
    have h1 := le_integral_of_dini_right (f := C) (g := fun _ : ℝ => (0 : ℝ)) hc.2.le
      (hC.mono hsub) continuousOn_const ?_
    · simp only [intervalIntegral.integral_zero, sub_nonpos] at h1
      exact h1
    · intro y hy ε hε
      obtain ⟨δ, hδpos, hδ⟩ := h y ⟨lt_of_lt_of_le hc.1 hy.1, hy.2⟩ ε hε
      exact ⟨δ, hδpos, fun h' hh' hb' => by simpa using hδ h' hh' hb'⟩
  refine le_of_forall_pos_le_add fun ε hε => ?_
  obtain ⟨δ, hδpos, hδ⟩ :=
    (Metric.continuousWithinAt_iff.mp (hC a ⟨le_rfl, hLt.le⟩)) ε hε
  have hpos : (0 : ℝ) < min (δ / 2) ((b - a) / 2) :=
    lt_min (by linarith) (by linarith)
  have hle : min (δ / 2) ((b - a) / 2) ≤ (b - a) / 2 := min_le_right _ _
  have hle' : min (δ / 2) ((b - a) / 2) ≤ δ / 2 := min_le_left _ _
  have hmem : a + min (δ / 2) ((b - a) / 2) ∈ Icc a b := ⟨by linarith, by linarith⟩
  have hltb : a + min (δ / 2) ((b - a) / 2) < b := by linarith
  have hgta : a < a + min (δ / 2) ((b - a) / 2) := by linarith
  have hnear : C (a + min (δ / 2) ((b - a) / 2)) < C a + ε := by
    have hd : dist (a + min (δ / 2) ((b - a) / 2)) a < δ := by
      rw [Real.dist_eq, abs_of_nonneg (by linarith)]
      linarith
    have h1 := hδ hmem hd
    rw [Real.dist_eq, abs_lt] at h1
    linarith [h1.2]
  have h2 := hkey (a + min (δ / 2) ((b - a) / 2)) ⟨hgta, hltb⟩
  linarith

private theorem le_of_dini_off_finset : ∀ (n : ℕ) (a b : ℝ) (C : ℝ → ℝ) (E : Finset ℝ),
    a ≤ b → ContinuousOn C (Icc a b) → E.card ≤ n →
    (∀ x ∈ Ioo a b, x ∉ E → ∀ ε > 0, ∃ δ > 0, ∀ h' ∈ Ioo (0 : ℝ) δ, x + h' ≤ b →
      (C (x + h') - C x) / h' ≤ ε) → C b ≤ C a := by
  intro n
  induction n with
  | zero =>
    intro a b C E hab hC hcard h
    have hE : E = ∅ := Finset.card_eq_zero.mp (Nat.le_zero.mp hcard)
    subst hE
    exact le_of_dini_interior hab hC fun x hx => h x hx (by simp)
  | succ n ih =>
    intro a b C E hab hC hcard h
    by_cases hemp : E.filter (fun x => a < x ∧ x < b) = ∅
    · refine le_of_dini_interior hab hC fun x hx => h x hx fun hxE => ?_
      have hm : x ∈ E.filter (fun y => a < y ∧ y < b) := Finset.mem_filter.mpr ⟨hxE, hx⟩
      rw [hemp] at hm
      exact Finset.notMem_empty x hm
    · obtain ⟨e, he⟩ := Finset.nonempty_iff_ne_empty.mpr hemp
      rw [Finset.mem_filter] at he
      obtain ⟨heE, hae, heb⟩ := he
      have hcard₁ : (E.filter (fun x => a < x ∧ x < e)).card ≤ n := by
        have hsub : E.filter (fun x => a < x ∧ x < e) ⊆ E.erase e := by
          intro y hy
          rw [Finset.mem_filter] at hy
          exact Finset.mem_erase.mpr ⟨ne_of_lt hy.2.2, hy.1⟩
        have h1 : (E.filter (fun x => a < x ∧ x < e)).card ≤ (E.erase e).card :=
          Finset.card_le_card hsub
        rw [Finset.card_erase_of_mem heE] at h1
        omega
      have hcard₂ : (E.filter (fun x => e < x ∧ x < b)).card ≤ n := by
        have hsub : E.filter (fun x => e < x ∧ x < b) ⊆ E.erase e := by
          intro y hy
          rw [Finset.mem_filter] at hy
          exact Finset.mem_erase.mpr ⟨ne_of_gt hy.2.1, hy.1⟩
        have h1 : (E.filter (fun x => e < x ∧ x < b)).card ≤ (E.erase e).card :=
          Finset.card_le_card hsub
        rw [Finset.card_erase_of_mem heE] at h1
        omega
      have h1 : C e ≤ C a := ih a e C (E.filter (fun x => a < x ∧ x < e)) hae.le
        (hC.mono (Icc_subset_Icc le_rfl heb.le)) hcard₁
        (fun x hx hxE ε hε => by
          obtain ⟨δ, hδpos, hδ⟩ := h x ⟨hx.1, lt_trans hx.2 heb⟩
            (fun hxE' => hxE (Finset.mem_filter.mpr ⟨hxE', hx⟩)) ε hε
          exact ⟨δ, hδpos, fun h' hh' hxe => hδ h' hh' (le_trans hxe heb.le)⟩)
      have h2 : C b ≤ C e := ih e b C (E.filter (fun x => e < x ∧ x < b)) heb.le
        (hC.mono (Icc_subset_Icc hae.le le_rfl)) hcard₂
        (fun x hx hxE => h x ⟨lt_trans hae hx.1, hx.2⟩
          (fun hxE' => hxE (Finset.mem_filter.mpr ⟨hxE', hx⟩)))
      linarith


private theorem exists_integral_ratio_bounds {rho : ℝ → ℝ} {a b t : ℝ}
    (hrho : ContinuousOn rho (Icc a b)) (ht : t ∈ Ico a b) {η : ℝ} (hη : 0 < η) :
    ∃ δ > 0, ∀ h ∈ Ioo (0 : ℝ) δ, t + h ≤ b →
      |h⁻¹ * (∫ w in t..(t + h), rho w) - rho t| ≤ η ∧
      |∫ w in t..(t + h), rho w| ≤ h * (|rho t| + 1) := by
  have htb : t ≤ b := ht.2.le
  have htIcc : t ∈ Icc a b := ⟨ht.1, htb⟩
  obtain ⟨δ₀, hδ₀pos, hδ₀⟩ :=
    (Metric.continuousWithinAt_iff.mp (hrho.continuousWithinAt htIcc)) (min η 1)
      (lt_min hη one_pos)
  refine ⟨min δ₀ (b - t), lt_min hδ₀pos (sub_pos.mpr ht.2), ?_⟩
  intro h hh hb
  have hh0 : 0 < h := hh.1
  have hδ₀h : h < δ₀ := lt_of_lt_of_le hh.2 (min_le_left _ _)
  have hth : t ≤ t + h := by linarith
  have hsub : Icc t (t + h) ⊆ Icc a b := fun y hy =>
    ⟨le_trans ht.1 hy.1, le_trans hy.2 hb⟩
  have hcont1 : ContinuousOn rho (uIcc t (t + h)) := by
    rw [uIcc_of_le hth]
    exact hrho.mono hsub
  have hInt1 : IntervalIntegrable rho volume t (t + h) := hcont1.intervalIntegrable
  have hpoint : ∀ w ∈ uIoc t (t + h), ‖rho w - rho t‖ ≤ min η 1 := by
    intro w hw
    rw [uIoc_of_le hth] at hw
    have hwt : dist w t < δ₀ := by
      rw [Real.dist_eq, abs_of_nonneg (sub_nonneg.mpr hw.1.le)]
      linarith [hw.2]
    have h1 := hδ₀ (hsub ⟨hw.1.le, hw.2⟩) hwt
    rw [Real.dist_eq] at h1
    rw [Real.norm_eq_abs]
    exact le_of_lt h1
  have hbound := intervalIntegral.norm_integral_le_of_norm_le_const (a := t) (b := t + h)
    (C := min η 1) (f := fun w => rho w - rho t) hpoint
  have hb' : |∫ w in t..(t + h), (rho w - rho t)| ≤ min η 1 * h := by
    rw [Real.norm_eq_abs, add_sub_cancel_left, abs_of_pos hh0] at hbound
    exact hbound
  have hcdiff : (∫ w in t..(t + h), (fun _ : ℝ => rho t) w) = h * rho t := by
    rw [intervalIntegral.integral_const, smul_eq_mul]
    ring
  have hdiff : (∫ w in t..(t + h), rho w) - h * rho t = ∫ w in t..(t + h), (rho w - rho t) := by
    rw [← hcdiff, ← intervalIntegral.integral_sub hInt1 intervalIntegrable_const]
  have hminη : min η 1 ≤ η := min_le_left _ _
  have hmin1 : min η 1 ≤ 1 := min_le_right _ _
  constructor
  · have h2 : h⁻¹ * (∫ w in t..(t + h), rho w) - rho t
        = h⁻¹ * ((∫ w in t..(t + h), rho w) - h * rho t) := by
      rw [mul_sub, ← mul_assoc, inv_mul_cancel₀ (ne_of_gt hh0), one_mul]
    rw [h2, abs_mul, abs_of_pos (inv_pos.mpr hh0), hdiff]
    have hthis := mul_le_mul_of_nonneg_left hb' (le_of_lt (inv_pos.mpr hh0))
    have hcalc : h⁻¹ * (min η 1 * h) = min η 1 := by field_simp
    linarith [hthis, hcalc.le, hcalc.ge, hminη]
  · have h3 : |∫ w in t..(t + h), (rho w - rho t)| ≤ h := by
      have h4 : min η 1 * h ≤ 1 * h := mul_le_mul_of_nonneg_right hmin1 hh0.le
      linarith [hb', h4]
    have h5 : |∫ w in t..(t + h), rho w|
        ≤ |(∫ w in t..(t + h), rho w) - h * rho t| + h * |rho t| := by
      have h6 : (∫ w in t..(t + h), rho w)
          = ((∫ w in t..(t + h), rho w) - h * rho t) + h * rho t := by ring
      calc |∫ w in t..(t + h), rho w|
          = |((∫ w in t..(t + h), rho w) - h * rho t) + h * rho t| := congrArg abs h6
        _ ≤ |(∫ w in t..(t + h), rho w) - h * rho t| + |h * rho t| := abs_add_le _ _
        _ = |(∫ w in t..(t + h), rho w) - h * rho t| + h * |rho t| := by
            rw [abs_mul, abs_of_pos hh0]
    rw [hdiff] at h5
    nlinarith [h5, h3]

private theorem exp_sub_one_sub_id_abs_le (u : ℝ) (hu : |u| ≤ 1) :
    |Real.exp u - 1 - u| ≤ u ^ 2 := by
  have hu1 : ‖(u : ℂ)‖ ≤ 1 := by
    rw [Complex.norm_real, Real.norm_eq_abs]
    exact hu
  have h3 : ((Real.exp u - 1 - u : ℝ) : ℂ) = Complex.exp (u : ℂ) - 1 - (u : ℂ) := by
    rw [Complex.ofReal_sub, Complex.ofReal_sub, Complex.ofReal_exp, Complex.ofReal_one]
  have h4 : ‖((Real.exp u - 1 - u : ℝ) : ℂ)‖ ≤ u ^ 2 := by
    rw [h3]
    calc ‖Complex.exp (u : ℂ) - 1 - (u : ℂ)‖ ≤ ‖(u : ℂ)‖ ^ 2 :=
          Complex.norm_exp_sub_one_sub_id_le hu1
      _ = u ^ 2 := by rw [Complex.norm_real, Real.norm_eq_abs, sq_abs]
  simpa only [Complex.norm_real, Real.norm_eq_abs] using h4

private theorem exists_exp_integral_slope_bound {rho : ℝ → ℝ} {a b t : ℝ}
    (hrho : ContinuousOn rho (Icc a b)) (ht : t ∈ Ico a b) {η : ℝ} (hη : 0 < η) :
    ∃ δ > 0, ∀ h ∈ Ioo (0 : ℝ) δ, t + h ≤ b →
      |(Real.exp (∫ w in t..(t + h), rho w) - 1) / h - rho t| ≤ η := by
  set R : ℝ := |rho t| + 1 with hR
  have hRpos : 0 < R := by rw [hR]; positivity
  obtain ⟨δ₁, hδ₁pos, hδ₁⟩ := exists_integral_ratio_bounds hrho ht (η := η / 2) (by linarith)
  refine ⟨min (min δ₁ (1 / R)) ((η / 2) / R ^ 2), ?_, ?_⟩
  · have h1 : 0 < R ^ 2 := pow_pos hRpos 2
    have h2 : 0 < (η / 2) / R ^ 2 := div_pos (by linarith) h1
    exact lt_min (lt_min hδ₁pos (div_pos one_pos hRpos)) h2
  intro h hh hb
  have hh0 : 0 < h := hh.1
  have hδ₁h : h < δ₁ := lt_of_lt_of_le hh.2 (le_trans (min_le_left _ _) (min_le_left _ _))
  have h1R : h < 1 / R := lt_of_lt_of_le hh.2 (le_trans (min_le_left _ _) (min_le_right _ _))
  have hηR : h < (η / 2) / R ^ 2 := lt_of_lt_of_le hh.2 (min_le_right _ _)
  obtain ⟨hratio, hbnd⟩ := hδ₁ h ⟨hh.1, hδ₁h⟩ hb
  set u : ℝ := ∫ w in t..(t + h), rho w with hu
  have hu_bnd : |u| ≤ h * R := by
    simpa only [hR] using hbnd
  have hu1 : |u| ≤ 1 := by
    have h2 := mul_lt_mul_of_pos_right h1R hRpos
    have h3 : (1 / R) * R = 1 := by field_simp
    have h4 : h * R < 1 := by linarith [h2, h3.le, h3.ge]
    exact le_of_lt (lt_of_le_of_lt hu_bnd h4)
  have hexp := exp_sub_one_sub_id_abs_le u hu1
  have hfirst : |u / h - rho t| ≤ η / 2 := by
    have h2 : h⁻¹ * (∫ w in t..(t + h), rho w) = u / h := by
      rw [hu, div_eq_mul_inv, mul_comm]
    rw [← h2]
    exact hratio
  have hsecond : |(Real.exp u - 1 - u) / h| ≤ η / 2 := by
    have h2 : |(Real.exp u - 1 - u) / h| = |Real.exp u - 1 - u| / h := by
      rw [abs_div, abs_of_pos hh0]
    have h3 : |Real.exp u - 1 - u| / h ≤ u ^ 2 / h :=
      div_le_div_of_nonneg_right hexp hh0.le
    have h4 : u ^ 2 ≤ (h * R) ^ 2 := by
      have h5 := abs_le.mp hu_bnd
      nlinarith [h5.1, h5.2]
    have h5 : u ^ 2 / h ≤ h * R ^ 2 := by
      have h6 : u ^ 2 ≤ h ^ 2 * R ^ 2 := by nlinarith [h4]
      rw [div_le_iff₀ hh0]
      nlinarith [h6]
    have h7 : h * R ^ 2 ≤ η / 2 := by
      rw [div_eq_mul_inv] at hηR
      have h8 : h * R ^ 2 < (η / 2 / R ^ 2) * R ^ 2 := mul_lt_mul_of_pos_right hηR (pow_pos hRpos 2)
      have h9 : (η / 2 / R ^ 2) * R ^ 2 = η / 2 := by field_simp
      linarith [h8, h9.le]
    linarith [h2.le, h2.ge, h3, h5, h7]
  have hkey : (Real.exp u - 1) / h - rho t
      = (u / h - rho t) + (Real.exp u - 1 - u) / h := by
    rw [← sub_add_cancel (Real.exp u - 1) u, add_div]
    ring
  rw [hkey]
  calc |(u / h - rho t) + (Real.exp u - 1 - u) / h|
      ≤ |u / h - rho t| + |(Real.exp u - 1 - u) / h| := abs_add_le _ _
    _ ≤ η / 2 + η / 2 := add_le_add hfirst hsecond
    _ = η := by ring


private theorem exists_exp_integral_product_slope_bound {rho F : ℝ → ℝ} {a b t : ℝ}
    (hrho : ContinuousOn rho (Icc a b)) (hF : ContinuousOn F (Icc a b))
    (ht : t ∈ Ico a b) {ε : ℝ} (hε : 0 < ε) :
    ∃ δ > 0, ∀ h ∈ Ioo (0 : ℝ) δ, t + h ≤ b →
      |h⁻¹ * (∫ w in t..(t + h), Real.exp (∫ z in t..w, rho z) * F w) - F t| ≤ ε := by
  have htb : t ≤ b := ht.2.le
  have htIcc : t ∈ Icc a b := ⟨ht.1, htb⟩
  have hIntOn : IntegrableOn rho (uIcc t b) volume := by
    rw [uIcc_of_le htb]
    exact (hrho.mono (Icc_subset_Icc ht.1 le_rfl)).integrableOn_compact isCompact_Icc
  have hprimCont : ContinuousOn (fun w : ℝ => ∫ z in t..w, rho z) (uIcc t b) :=
    intervalIntegral.continuousOn_primitive_interval hIntOn
  have hprimCont' : ContinuousOn (fun w : ℝ => ∫ z in t..w, rho z) (Icc t b) := by
    rw [← uIcc_of_le htb]
    exact hprimCont
  have hgcont : ContinuousOn (fun w : ℝ => Real.exp (∫ z in t..w, rho z) * F w) (Icc t b) :=
    (Real.continuous_exp.comp_continuousOn hprimCont').mul
      (hF.mono (Icc_subset_Icc ht.1 le_rfl))
  obtain ⟨δ₁, hδ₁pos, hδ₁⟩ :=
    (Metric.continuousWithinAt_iff.mp (hgcont.continuousWithinAt ⟨le_rfl, htb⟩)) ε hε
  refine ⟨min δ₁ (b - t), lt_min hδ₁pos (sub_pos.mpr ht.2), ?_⟩
  intro h hh hb
  have hh0 : 0 < h := hh.1
  have hδ₁h : h < δ₁ := lt_of_lt_of_le hh.2 (min_le_left _ _)
  have hth : t ≤ t + h := by linarith
  have hsub : Icc t (t + h) ⊆ Icc t b := fun y hy => ⟨hy.1, le_trans hy.2 hb⟩
  have hgInt : IntervalIntegrable (fun w : ℝ => Real.exp (∫ z in t..w, rho z) * F w)
      volume t (t + h) :=
    (show ContinuousOn (fun w : ℝ => Real.exp (∫ z in t..w, rho z) * F w) (uIcc t (t + h)) from by
      rw [uIcc_of_le hth]
      exact hgcont.mono hsub).intervalIntegrable
  have hgt : Real.exp (∫ z in t..t, rho z) * F t = F t := by
    simp
  have hpoint : ∀ w ∈ uIoc t (t + h), ‖Real.exp (∫ z in t..w, rho z) * F w - F t‖ ≤ ε := by
    intro w hw
    rw [uIoc_of_le hth] at hw
    have hwt : dist w t < δ₁ := by
      rw [Real.dist_eq, abs_of_nonneg (sub_nonneg.mpr hw.1.le)]
      linarith [hw.2]
    have h1 := hδ₁ (hsub ⟨hw.1.le, hw.2⟩) hwt
    rw [Real.dist_eq, hgt] at h1
    rw [Real.norm_eq_abs]
    exact le_of_lt h1
  have hbound := intervalIntegral.norm_integral_le_of_norm_le_const (a := t) (b := t + h)
    (C := ε) (f := fun w : ℝ => Real.exp (∫ z in t..w, rho z) * F w - F t) hpoint
  have hb' : |∫ w in t..(t + h), (Real.exp (∫ z in t..w, rho z) * F w - F t)| ≤ ε * h := by
    rw [Real.norm_eq_abs, add_sub_cancel_left, abs_of_pos hh0] at hbound
    exact hbound
  have hcdiff : (∫ w in t..(t + h), (fun _ : ℝ => F t) w) = h * F t := by
    rw [intervalIntegral.integral_const, smul_eq_mul]
    ring
  have hdiff : (∫ w in t..(t + h), Real.exp (∫ z in t..w, rho z) * F w) - h * F t
      = ∫ w in t..(t + h), (Real.exp (∫ z in t..w, rho z) * F w - F t) := by
    rw [← hcdiff, ← intervalIntegral.integral_sub hgInt intervalIntegrable_const]
  have h2 : h⁻¹ * (∫ w in t..(t + h), Real.exp (∫ z in t..w, rho z) * F w) - F t
      = h⁻¹ * ((∫ w in t..(t + h), Real.exp (∫ z in t..w, rho z) * F w) - h * F t) := by
    rw [mul_sub, ← mul_assoc, inv_mul_cancel₀ (ne_of_gt hh0), one_mul]
  rw [h2, abs_mul, abs_of_pos (inv_pos.mpr hh0), hdiff]
  have hthis := mul_le_mul_of_nonneg_left hb' (le_of_lt (inv_pos.mpr hh0))
  have hcalc : h⁻¹ * (ε * h) = ε := by field_simp
  linarith [hthis, hcalc.le, hcalc.ge]


private theorem neg_mul_le_abs_mul (x y : ℝ) : -x * y ≤ |x| * |y| := by
  calc -x * y = -(x * y) := by ring
    _ ≤ |x * y| := neg_le_abs _
    _ = |x| * |y| := abs_mul x y

private theorem exists_slope_le_of_exp_integral_comparison {A rho F : ℝ → ℝ} {a b : ℝ}
    (hA : ContinuousOn A (Icc a b)) (hrho : ContinuousOn rho (Icc a b))
    (hF : ContinuousOn F (Icc a b))
    (hint : ∀ s ∈ Icc a b, ∀ u ∈ Icc s b,
      Real.exp (∫ w in s..u, rho w) * A u ≤
        A s + ∫ v in s..u, Real.exp (∫ w in s..v, rho w) * F v)
    {t : ℝ} (ht : t ∈ Ico a b) {ε : ℝ} (hε : 0 < ε) :
    ∃ δ > 0, ∀ h ∈ Ioo (0 : ℝ) δ, t + h ≤ b →
      (A (t + h) - A t) / h ≤ -rho t * A t + F t + ε := by
  have htb : t ≤ b := ht.2.le
  have htIcc : t ∈ Icc a b := ⟨ht.1, htb⟩
  set R : ℝ := |rho t| + 1 with hR
  have hRpos : 0 < R := by rw [hR]; positivity
  set η : ℝ := min (ε / (3 * (|A t| + 1))) (min (ε / (3 * R)) 1) with hη
  have hA1pos : 0 < |A t| + 1 := by positivity
  have hηA : η ≤ ε / (3 * (|A t| + 1)) := by
    rw [hη]
    exact min_le_left _ _
  have hηR : η ≤ ε / (3 * R) := by
    rw [hη]
    exact le_trans (min_le_right _ _) (min_le_left _ _)
  have hη1 : η ≤ 1 := by
    rw [hη]
    exact le_trans (min_le_right _ _) (min_le_right _ _)
  have hηpos : 0 < η := by
    rw [hη]
    have h1 : 0 < ε / (3 * (|A t| + 1)) := div_pos hε (by linarith)
    have h2 : 0 < ε / (3 * R) := div_pos hε (by linarith)
    exact lt_min h1 (lt_min h2 one_pos)
  obtain ⟨δ₁, hδ₁pos, hδ₁⟩ := exists_exp_integral_slope_bound hrho ht (η := η) hηpos
  obtain ⟨δ₂, hδ₂pos, hδ₂⟩ :=
    exists_exp_integral_product_slope_bound hrho hF ht (ε := ε / 3) (by linarith)
  obtain ⟨δ₃, hδ₃pos, hδ₃⟩ := (Metric.continuousWithinAt_iff.mp (hA.continuousWithinAt htIcc)) η hηpos
  refine ⟨min (min δ₁ δ₂) δ₃, lt_min (lt_min hδ₁pos hδ₂pos) hδ₃pos, ?_⟩
  intro h hh hb
  have hh0 : 0 < h := hh.1
  have hδ₁h : h < δ₁ := lt_of_lt_of_le hh.2 (le_trans (min_le_left _ _) (min_le_left _ _))
  have hδ₂h : h < δ₂ := lt_of_lt_of_le hh.2 (le_trans (min_le_left _ _) (min_le_right _ _))
  have hδ₃h : h < δ₃ := lt_of_lt_of_le hh.2 (min_le_right _ _)
  have hth : t ≤ t + h := by linarith
  have htIcc' : t + h ∈ Icc a b := ⟨by linarith [ht.1], hb⟩
  set u : ℝ := ∫ w in t..(t + h), rho w with hu
  set P : ℝ := ∫ w in t..(t + h), Real.exp (∫ z in t..w, rho z) * F w with hP
  have hratio : |(Real.exp u - 1) / h - rho t| ≤ η := by
    have h := hδ₁ h ⟨hh.1, hδ₁h⟩ hb
    rwa [← hu] at h
  have hprod : |h⁻¹ * P - F t| ≤ ε / 3 := by
    have h := hδ₂ h ⟨hh.1, hδ₂h⟩ hb
    rwa [← hP] at h
  have hAdist : |A (t + h) - A t| < η := by
    have h := hδ₃ htIcc' (by rw [Real.dist_eq, add_sub_cancel_left, abs_of_pos hh0]; exact hδ₃h)
    rwa [Real.dist_eq] at h
  have hAineq : |A (t + h)| ≤ |A t| + 1 := by
    have h2 : |A (t + h)| ≤ |A t| + |A (t + h) - A t| := by
      calc |A (t + h)| = |A t + (A (t + h) - A t)| := congrArg abs (by ring)
        _ ≤ |A t| + |A (t + h) - A t| := abs_add_le _ _
    linarith [h2, hAdist, hη1]
  have hineq := hint t htIcc (t + h) ⟨hth, hb⟩
  have hle : (Real.exp u * A (t + h) - A t) / h ≤ P / h := by
    rw [div_le_div_iff_of_pos_right hh0]
    rw [hP, hu]
    linarith [hineq]
  have hPle : P / h ≤ F t + ε / 3 := by
    have h6 := (abs_le.mp hprod).2
    have h2 : h⁻¹ * P = P / h := by rw [div_eq_mul_inv, mul_comm]
    linarith [h6, h2.le, h2.ge]
  have hsplit : (A (t + h) - A t) / h
      = (Real.exp u * A (t + h) - A t) / h - ((Real.exp u - 1) / h) * A (t + h) := by
    rw [div_mul_eq_mul_div, ← sub_div]
    ring
  have htail : -(((Real.exp u - 1) / h) * A (t + h))
      ≤ -rho t * A t + |rho t| * η + η * (|A t| + 1) := by
    have h1 : -(((Real.exp u - 1) / h) - rho t) * A (t + h)
        ≤ |((Real.exp u - 1) / h) - rho t| * |A (t + h)| := neg_mul_le_abs_mul _ _
    have h2 : |((Real.exp u - 1) / h) - rho t| * |A (t + h)| ≤ η * |A (t + h)| :=
      mul_le_mul_of_nonneg_right hratio (abs_nonneg _)
    have h3 : η * |A (t + h)| ≤ η * (|A t| + 1) :=
      mul_le_mul_of_nonneg_left hAineq hηpos.le
    have h4 : -rho t * (A (t + h) - A t) ≤ |rho t| * η := by
      have h5 : -rho t * (A (t + h) - A t) ≤ |rho t| * |A (t + h) - A t| := neg_mul_le_abs_mul _ _
      have h6 : |rho t| * |A (t + h) - A t| ≤ |rho t| * η :=
        mul_le_mul_of_nonneg_left hAdist.le (abs_nonneg _)
      linarith [h5, h6]
    have h7 : -(((Real.exp u - 1) / h) * A (t + h))
        = -rho t * A (t + h) + (-(((Real.exp u - 1) / h) - rho t) * A (t + h)) := by ring
    have h8 : -rho t * A (t + h) = -rho t * A t + (-rho t * (A (t + h) - A t)) := by ring
    linarith [h1, h2, h3, h4, h7.le, h7.ge, h8.le, h8.ge]
  have hnum1 : |rho t| * η ≤ ε / 3 := by
    have h1 : R * η ≤ R * (ε / (3 * R)) := mul_le_mul_of_nonneg_left hηR hRpos.le
    have h2 : R * (ε / (3 * R)) = ε / 3 := by field_simp
    have h3 : |rho t| ≤ R := by rw [hR]; linarith [abs_nonneg (rho t)]
    have h4 : |rho t| * η ≤ R * η := mul_le_mul_of_nonneg_right h3 hηpos.le
    linarith [h1, h2.le, h2.ge, h4]
  have hnum2 : η * (|A t| + 1) ≤ ε / 3 := by
    have h1 : (|A t| + 1) * η ≤ (|A t| + 1) * (ε / (3 * (|A t| + 1))) :=
      mul_le_mul_of_nonneg_left hηA hA1pos.le
    have h2 : (|A t| + 1) * (ε / (3 * (|A t| + 1))) = ε / 3 := by field_simp
    linarith [h1, h2.le, h2.ge]
  have h1 := hsplit.le
  linarith [h1, hle, hPle, htail, hnum1, hnum2]


variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [CompleteSpace E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

theorem continuousOn_intervalIntegral_of_continuousOn_rectangle {f : ℝ → ℝ → ℝ} {a b : ℝ}
    (hab : a ≤ b)
    (h : ContinuousOn (fun p : ℝ × ℝ => f p.1 p.2) (Icc (0 : ℝ) 1 ×ˢ Icc a b)) :
    ContinuousOn (fun t : ℝ => ∫ x in (0 : ℝ)..1, f x t) (Icc a b) := by
  have hproj : Continuous (fun p : ℝ × ℝ =>
      ((max 0 (min p.2 1), max a (min p.1 b)) : ℝ × ℝ)) := by fun_prop
  have hmaps : ∀ p : ℝ × ℝ,
      ((max 0 (min p.2 1), max a (min p.1 b)) : ℝ × ℝ) ∈ Icc (0 : ℝ) 1 ×ˢ Icc a b := by
    rintro ⟨u, v⟩
    exact ⟨⟨le_max_left _ _, max_le zero_le_one (min_le_right _ _)⟩,
      ⟨le_max_left _ _, max_le hab (min_le_right _ _)⟩⟩
  have hcont : Continuous
      (Function.uncurry fun s u => f (max 0 (min u 1)) (max a (min s b))) :=
    h.comp_continuous hproj hmaps
  have hc := intervalIntegral.continuous_parametric_intervalIntegral_of_continuous'
    (μ := volume) (f := fun s u => f (max 0 (min u 1)) (max a (min s b))) hcont 0 1
  refine hc.continuousOn.congr fun t ht => intervalIntegral.integral_congr fun x hx => ?_
  rw [uIcc_of_le zero_le_one] at hx
  have hx1 : max 0 (min x 1) = x := by rw [min_eq_left hx.2, max_eq_right hx.1]
  have ht1 : max a (min t b) = t := by rw [min_eq_left ht.2, max_eq_right ht.1]
  simp only [hx1, ht1]

namespace CurveMap

omit [FiniteDimensional ℝ E] [CompleteSpace E] in
theorem unitTangent_inner_self (c : CurveMap M)
    (g : ℝ → SmoothRiemannianMetric I M) {J : Set ℝ}
    (hi : c.ImmersedOn (I := I) J) (x t : ℝ) (ht : t ∈ J) :
    (g t).inner (c.lift x t) (c.unitTangent g x t) (c.unitTangent g x t) = 1 := by
  have hs := c.speed_pos g hi x t ht
  have hsquare : c.speed g x t ^ 2 = (g t).inner (c.lift x t) (c.X x t) (c.X x t) :=
    Real.sq_sqrt ((g t).pos (c.lift x t) (c.X x t) (hi x t ht)).le
  simp only [unitTangent, map_smul, smul_apply, smul_eq_mul]
  rw [← hsquare]
  field_simp [ne_of_gt hs]

omit [FiniteDimensional ℝ E] [CompleteSpace E] in
theorem normal_component_add_tangent (g : SmoothRiemannianMetric I M) (p : M)
    (V T : TangentSpace I p) (alpha : ℝ) (hT : g.inner p T T = 1) :
    (V + alpha • T) - g.inner p (V + alpha • T) T • T =
      V - g.inner p V T • T := by
  have hinner : g.inner p (V + alpha • T) T = g.inner p V T + alpha := by
    simp [map_add, map_smul, hT]
  rw [hinner, add_smul]
  abel

def normalVelocityError (c : CurveMap M) (g : ℝ → SmoothRiemannianMetric I M)
    (J : Set ℝ) : c.Field (I := I) := fun x t =>
  let W := c.velocity (I := I) J x t - c.curvatureVector g x t
  W - (g t).inner (c.lift x t) W (c.unitTangent g x t) • c.unitTangent g x t

def areaError (c : CurveMap M) (g : ℝ → SmoothRiemannianMetric I M)
    (J : Set ℝ) : ℝ → ℝ :=
  c.integral g (fun x t => Real.sqrt (c.normSq g (c.normalVelocityError g J) x t))

omit [CompleteSpace E] in
theorem areaError_nonneg (c : CurveMap M) (g : ℝ → SmoothRiemannianMetric I M)
    (J : Set ℝ) (t : ℝ) : 0 ≤ c.areaError g J t := by
  apply intervalIntegral.integral_nonneg_of_forall (by norm_num : (0 : ℝ) ≤ 1)
  intro x
  exact mul_nonneg (Real.sqrt_nonneg _) (c.speed_nonneg g x t)

omit [CompleteSpace E] in
theorem normalVelocityError_eq_zero (c : CurveMap M) (g : ℝ → SmoothRiemannianMetric I M)
    {J : Set ℝ} (hc : c.IsSolutionOn g J) (x t : ℝ) (ht : t ∈ J) :
    c.normalVelocityError g J x t = 0 := by
  simp [normalVelocityError, hc.equation x t ht]

omit [CompleteSpace E] in
theorem areaError_eq_zero (c : CurveMap M) (g : ℝ → SmoothRiemannianMetric I M)
    {J : Set ℝ} (hc : c.IsSolutionOn g J) (t : ℝ) (ht : t ∈ J) :
    c.areaError g J t = 0 := by
  simp [areaError, integral, normSq, c.normalVelocityError_eq_zero g hc _ t ht]

end CurveMap


def loopFamilyLeastArea (g : ℝ → SmoothRiemannianMetric I M)
    (γ : ℝ → ContinuousFreeLoop M) (t : ℝ) : ℝ :=
  sInf (Width.competitorAreas (g t) (γ t))

variable [hBoundary : I.Boundaryless] [hT2 : T2Space M]
    [hCompact : CompactSpace M] [hNonempty : Nonempty M]

omit [FiniteDimensional ℝ E] [CompleteSpace E] hBoundary hT2 hCompact hNonempty in
theorem loopFamilyLeastArea_eq (g : ℝ → SmoothRiemannianMetric I M)
    (γ : ℝ → ContinuousFreeLoop M) (t : ℝ) (hctr : IsContractibleLoop (γ t))
    (hlip : Width.IsLipschitzLoop (g t) (γ t)) :
    loopFamilyLeastArea g γ t = Width.leastArea (g t) (γ t) hctr hlip := rfl


def regularLoopSlice (γ : ℝ → ContinuousFreeLoop M) {J : Set ℝ}
    (hγ : (curveOfLoopFamily γ).SmoothOn (I := I) J) (t : ℝ) (ht : t ∈ J) :
    Width.RegularLoop I M where
  toContinuousLoop := γ t
  contMDiff_lift := ((curveOfLoopFamily γ).smooth_slice hγ ht).of_le (by simp)

omit [CompleteSpace E] hNonempty in
theorem loopFamilyLeastArea_nonneg (g : ℝ → SmoothRiemannianMetric I M)
    (γ : ℝ → ContinuousFreeLoop M) {J : Set ℝ}
    (hγ : (curveOfLoopFamily γ).SmoothOn (I := I) J)
    (hctr : ∀ t ∈ J, IsContractibleLoop (γ t)) (t : ℝ) (ht : t ∈ J) :
    0 ≤ loopFamilyLeastArea g γ t :=
  Width.leastArea_nonneg (g t) (γ t) (hctr t ht)
    ((regularLoopSlice γ hγ t ht).isLipschitz (g t))

omit [FiniteDimensional ℝ E] [CompleteSpace E] hBoundary hT2 hCompact hNonempty in
theorem loopFamilyLeastArea_eq_regularLeastAreaSlice
    (g : ℝ → SmoothRiemannianMetric I M) (γ : ℝ → ContinuousFreeLoop M)
    {J : Set ℝ} (hγ : (curveOfLoopFamily γ).SmoothOn (I := I) J)
    (hctr : ∀ t ∈ J, IsContractibleLoop (γ t)) (t : ℝ) (ht : t ∈ J) :
    loopFamilyLeastArea g γ t =
      Width.regularLeastArea (g t) ⟨regularLoopSlice γ hγ t ht, hctr t ht⟩ := rfl

omit [FiniteDimensional ℝ E] [CompleteSpace E] hBoundary hT2 hCompact hNonempty in
theorem loopFamily_spacetimeMap_injective
    (γ : ℝ → ContinuousFreeLoop M) {J : Set ℝ}
    (hemb : ∀ t ∈ J, Topology.IsEmbedding (γ t)) :
    Set.InjOn (fun p : ℝ × Surgery.Topology.Circle => (p.1, γ p.1 p.2))
      (J ×ˢ univ) := by
  intro p hp p' hp' h
  obtain ⟨t, z⟩ := p
  obtain ⟨t', z'⟩ := p'
  have htt : t = t' := congrArg Prod.fst h
  have hz : γ t z = γ t' z' := congrArg Prod.snd h
  have hz' : γ t z = γ t z' := by rw [← htt] at hz; exact hz
  exact Prod.ext htt ((hemb t (Set.mem_prod.mp hp).1).injective hz')

variable [SigmaCompactSpace M]
variable {D : RealTimeInterval} {a b : ℝ}

include hBoundary hT2 hCompact hNonempty


def scalarMinimum (G : SolutionFamily (I := I) (M := M)) (t : ℝ) : ℝ :=
  sInf (Set.range (G.scalar t))


def areaIntegratingFactor (G : SolutionFamily (I := I) (M := M)) (s v : ℝ) : ℝ :=
  Real.exp ((1 / 2 : ℝ) * ∫ w in s..v, scalarMinimum G w)

omit hBoundary hNonempty [SigmaCompactSpace M] in
theorem continuousOn_scalarMinimum_of_isSolutionOn (S : SolutionOn (I := I) (M := M) D)
    (hS : IsSolutionOn (I := I) S) (hreg : Icc a b ⊆ D.regular) :
    ContinuousOn (scalarMinimum S.base) (Icc a b) := by
  have hj := scalar_joint (I := I) S hS
  have hincl : ContinuousOn (fun p : Set.Icc a b × M => ((p.1 : ℝ), p.2)) univ := by
    fun_prop
  have hmaps : MapsTo (fun p : Set.Icc a b × M => ((p.1 : ℝ), p.2))
      univ (D.regular ×ˢ (univ : Set M)) :=
    fun p _ => ⟨hreg p.1.2, mem_univ _⟩
  have hcomp : ContinuousOn ((fun p : ℝ × M => S.scalar p.1 p.2) ∘
      fun p : Set.Icc a b × M => ((p.1 : ℝ), p.2)) univ :=
    hj.continuousOn.comp hincl hmaps
  have hcont : Continuous (fun p : Set.Icc a b × M => S.scalar (p.1 : ℝ) p.2) := by
    rw [← continuousOn_univ]
    refine hcomp.congr fun p _ => ?_
    rfl
  have hsinf : Continuous (fun t : Set.Icc a b => sInf
      ((fun x : M => S.scalar (t : ℝ) x) '' (univ : Set M))) :=
    isCompact_univ.continuous_sInf hcont
  apply continuousOn_iff_continuous_domRestrict.mpr
  refine hsinf.congr fun t => ?_
  simp only [scalarMinimum, SolutionOn.scalar, Set.image_univ, Set.domRestrict_apply]

omit hBoundary hNonempty [SigmaCompactSpace M] in
theorem RicciBackground.continuousOn_scalarMinimum
    (B : RicciBackground (I := I) (M := M) D a b) :
    ContinuousOn (scalarMinimum B.family) (Icc a b) :=
  continuousOn_scalarMinimum_of_isSolutionOn (I := I)
    (show SolutionOn (I := I) (M := M) D from ⟨B.family⟩) B.equation B.regular

omit [SigmaCompactSpace M] in
theorem continuousOn_loopFamilyLeastArea_of_continuousRegularFamily
    (B : RicciBackground (I := I) (M := M) D a b)
    (γ : ℝ → ContinuousFreeLoop M)
    (Γ : ℝ → Width.ContractibleRegularLoop (I := I) (Q := M))
    (hΓ : ContinuousOn Γ (Icc a b))
    (hagree : ∀ t ∈ Icc a b, (Γ t).1.toContinuousLoop = γ t) :
    ContinuousOn (loopFamilyLeastArea B.family.metric γ) (Icc a b) :=
  (Width.continuousOn_regularLeastArea_family (I := I) (Q := M) D B.family.metric B.smooth
    B.regular Γ hΓ).congr fun t ht => by
      simp only [Width.regularLeastArea, Width.leastArea, loopFamilyLeastArea,
        hagree t ht]

theorem rfs_csf_boundary_isotopy (γ : ℝ → ContinuousFreeLoop M)
    (hγ : (curveOfLoopFamily γ).SmoothOn (I := I) (Icc a b))
    (hi : (curveOfLoopFamily γ).ImmersedOn (I := I) (Icc a b))
    (hemb : ∀ t ∈ Icc a b, Topology.IsEmbedding (γ t))
    (t₀ : ℝ) (ht₀ : t₀ ∈ Icc a b) (hab : a < b) :
    ∃ ε > 0, ∃ Φ : ℝ → Diffeomorph I I M M ∞,
      ContMDiffOn (I.prod 𝓘(ℝ, ℝ)) I ∞ (fun p : M × ℝ => Φ p.2 p.1)
        (univ ×ˢ (Icc a b ∩ Ioo (t₀ - ε) (t₀ + ε))) ∧
      (∀ p, Φ t₀ p = p) ∧
      ∀ t ∈ Icc a b ∩ Ioo (t₀ - ε) (t₀ + ε), ∀ z, Φ t (γ t₀ z) = γ t z := by
  let _ : CompleteSpace E := inferInstance
  let _ := hNonempty
  exact rfs_csf_boundary_isotopy_of_hasBoundaryIsotopyVelocityExtension (I := I) (M := M)
    (fun _ hγ hi hemb => loopFamilyVelocityExtension_of_smoothOn (I := I) hγ hi hemb)
    γ hγ hi hemb t₀ ht₀ hab

omit hBoundary hCompact hNonempty [SigmaCompactSpace M] in
theorem rfs_csf_area_error (B : RicciBackground (I := I) (M := M) D a b)
    (c : CurveMap M) (hc : c.SmoothOn (I := I) (Icc a b))
    (hi : c.ImmersedOn (I := I) (Icc a b))
    (hintegrand : ContinuousOn (fun p : ℝ × ℝ =>
      Real.sqrt (c.normSq B.family.metric
          (c.normalVelocityError B.family.metric (Icc a b)) p.1 p.2) *
        c.speed B.family.metric p.1 p.2)
      (Icc (0 : ℝ) 1 ×ˢ Icc a b)) :
    ContinuousOn (c.areaError B.family.metric (Icc a b)) (Icc a b) ∧
      ∀ α : ℝ → ℝ → ℝ, c.IsGeometricSolutionOn B.family.metric (Icc a b) α →
        ∀ t ∈ Icc a b, c.areaError B.family.metric (Icc a b) t = 0 := by
  let _ := hc
  let _ := hi
  refine ⟨continuousOn_intervalIntegral_of_continuousOn_rectangle B.lt.le ?_, ?_⟩
  · simpa only [CurveMap.areaError, CurveMap.integral] using hintegrand
  · intro α hg t ht
    have hW : ∀ x, c.normalVelocityError B.family.metric (Icc a b) x t = 0 := by
      intro x
      have hT := c.unitTangent_inner_self B.family.metric hg.immersed x t ht
      have h0 : c.velocity (I := I) (Icc a b) x t - c.curvatureVector B.family.metric x t =
          α x t • c.unitTangent B.family.metric x t := by
        rw [hg.equation x t ht]
        abel
      simp only [CurveMap.normalVelocityError, h0, map_smul, smul_apply, smul_eq_mul, hT,
        mul_one, sub_self]
    simp [CurveMap.areaError, CurveMap.integral, CurveMap.normSq, hW]


omit [CompleteSpace E] hBoundary hT2 hCompact hNonempty [SigmaCompactSpace M] in
theorem continuousOn_areaError_of_smoothOn_curvatureVector {D : RealTimeInterval}
    (g : ℝ → SmoothRiemannianMetric I M)
    (hG : MetricFamilySmoothOn (I := I) (M := M) D g) {J : Set ℝ} (hJreg : J ⊆ D.regular)
    (hJuniq : UniqueDiffOn ℝ J) (c : CurveMap M) (hc : c.SmoothOn (I := I) J)
    (hi : c.ImmersedOn (I := I) J)
    (hκ : CurveMap.Field.SmoothOn (I := I) (c.curvatureVector g) J)
    (hab : a < b) (hJab : Icc a b ⊆ J) :
    ContinuousOn (fun t => c.areaError g J t) (Icc a b) := by
  have hv : CurveMap.Field.SmoothOn (I := I) (c.velocity (I := I) J) J :=
    CurveMap.Field.smoothOn_velocity c hc hJuniq
  have hW : CurveMap.Field.SmoothOn (I := I)
      (fun x t => c.velocity (I := I) J x t - c.curvatureVector g x t) J :=
    CurveMap.Field.smoothOn_sub hc _ _ hv hκ
  have hT : CurveMap.Field.SmoothOn (I := I) (c.unitTangent g) J :=
    CurveMap.Field.smoothOn_unitTangent g hG hJreg c hc hi
  have hinner : ContDiffOn ℝ ∞ (fun p : ℝ × ℝ => (g p.2).inner (c.lift p.1 p.2)
      (c.velocity (I := I) J p.1 p.2 - c.curvatureVector g p.1 p.2)
      (c.unitTangent g p.1 p.2)) (univ ×ˢ J) :=
    CurveMap.Field.smoothOn_inner g hG hJreg c hc _ _ hW hT
  have hsmul : CurveMap.Field.SmoothOn (I := I)
      (fun x t => ((g t).inner (c.lift x t)
        (c.velocity (I := I) J x t - c.curvatureVector g x t)
        (c.unitTangent g x t)) • c.unitTangent g x t) J :=
    CurveMap.Field.smoothOn_const_smul c hc
      (fun x t => (g t).inner (c.lift x t)
        (c.velocity (I := I) J x t - c.curvatureVector g x t)
        (c.unitTangent g x t)) hinner (c.unitTangent g) hT
  have hNVE : CurveMap.Field.SmoothOn (I := I) (c.normalVelocityError g J) J :=
    (CurveMap.Field.smoothOn_sub hc _ _ hW hsmul).congr fun p hp => by
      simp only [CurveMap.normalVelocityError]
  have hnorm : ContDiffOn ℝ ∞ (fun p : ℝ × ℝ =>
      c.normSq g (c.normalVelocityError g J) p.1 p.2) (univ ×ˢ J) :=
    CurveMap.Field.smoothOn_inner g hG hJreg c hc (c.normalVelocityError g J)
      (c.normalVelocityError g J) hNVE hNVE
  have hsqrt : ContinuousOn (fun p : ℝ × ℝ =>
      Real.sqrt (c.normSq g (c.normalVelocityError g J) p.1 p.2)) (univ ×ˢ J) :=
    hnorm.continuousOn.sqrt
  have hspeed : ContinuousOn (fun p : ℝ × ℝ => c.speed g p.1 p.2) (univ ×ˢ J) :=
    (CurveMap.Field.smoothOn_speed g hG hJreg c hc hi).continuousOn
  have hint : ContinuousOn (fun p : ℝ × ℝ =>
      Real.sqrt (c.normSq g (c.normalVelocityError g J) p.1 p.2) * c.speed g p.1 p.2)
      (univ ×ˢ J) := hsqrt.mul hspeed
  have hrect : ContinuousOn (fun p : ℝ × ℝ =>
      Real.sqrt (c.normSq g (c.normalVelocityError g J) p.1 p.2) * c.speed g p.1 p.2)
      (Icc (0 : ℝ) 1 ×ˢ Icc a b) :=
    hint.mono (Set.prod_mono (subset_univ _) hJab)
  simpa only [CurveMap.areaError, CurveMap.integral] using
    continuousOn_intervalIntegral_of_continuousOn_rectangle hab.le hrect


omit hBoundary hNonempty [SigmaCompactSpace M] in
theorem rfs_csf_slope_le_of_window_comparison (B : RicciBackground (I := I) (M := M) D a b)
    (γ : ℝ → ContinuousFreeLoop M)
    (hA : ContinuousOn (loopFamilyLeastArea B.family.metric γ) (Icc a b))
    (hF : ContinuousOn (fun t => (curveOfLoopFamily γ).areaError B.family.metric (Icc a b) t)
      (Icc a b))
    (hwindow : ∀ s ∈ Icc a b, ∀ u ∈ Icc s b,
      Real.exp (∫ w in s..u, scalarMinimum B.family w / 2) *
          loopFamilyLeastArea B.family.metric γ u ≤
        loopFamilyLeastArea B.family.metric γ s +
          ∫ v in s..u, Real.exp (∫ w in s..v, scalarMinimum B.family w / 2) *
            (-2 * Real.pi + (curveOfLoopFamily γ).areaError B.family.metric (Icc a b) v)) :
    ∀ t ∈ Ico a b, ∀ ε > 0, ∃ δ > 0, ∀ h ∈ Ioo (0 : ℝ) δ, t + h ≤ b →
      (loopFamilyLeastArea B.family.metric γ (t + h) -
          loopFamilyLeastArea B.family.metric γ t) / h ≤
        -2 * Real.pi - scalarMinimum B.family t * loopFamilyLeastArea B.family.metric γ t / 2 +
          (curveOfLoopFamily γ).areaError B.family.metric (Icc a b) t + ε := by
  intro t ht ε hε
  have hrho : ContinuousOn (fun w => scalarMinimum B.family w / 2) (Icc a b) :=
    (RicciBackground.continuousOn_scalarMinimum B).div_const 2
  obtain ⟨δ, hδpos, hδ⟩ := exists_slope_le_of_exp_integral_comparison hA hrho
    (continuousOn_const.add hF) hwindow ht hε
  refine ⟨δ, hδpos, fun h hh hb => ?_⟩
  have h2 : -(scalarMinimum B.family t / 2) * loopFamilyLeastArea B.family.metric γ t +
      (-2 * Real.pi + (curveOfLoopFamily γ).areaError B.family.metric (Icc a b) t) + ε
      = -2 * Real.pi - scalarMinimum B.family t * loopFamilyLeastArea B.family.metric γ t / 2 +
        (curveOfLoopFamily γ).areaError B.family.metric (Icc a b) t + ε := by ring
  exact (hδ h hh hb).trans_eq h2


omit hBoundary hT2 hCompact hNonempty in
theorem rfs_csf_area_comparison_ode (A rho F : ℝ → ℝ) (s t : ℝ) (hst : s ≤ t)
    (hA : ContinuousOn A (Icc s t)) (hrho : ContinuousOn rho (Icc s t))
    (hF : ContinuousOn F (Icc s t)) (exceptional : Finset ℝ)
    (hDini : ∀ v ∈ Ico s t, v ∉ exceptional → ∀ ε > 0, ∃ δ > 0,
      ∀ h ∈ Ioo (0 : ℝ) δ, v + h ≤ t →
        (A (v + h) - A v) / h ≤ -rho v * A v + F v + ε) :
    Real.exp (∫ w in s..t, rho w) * A t ≤ A s +
      ∫ v in s..t, Real.exp (∫ w in s..v, rho w) * F v := by
  have hφc : ContinuousOn (fun v : ℝ => Real.exp (∫ w in s..v, rho w)) (Icc s t) := by
    have hpr : ContinuousOn (fun v : ℝ => ∫ w in s..v, rho w) (Icc s t) := by
      have hgu : IntegrableOn rho (uIcc s t) volume := by
        rw [uIcc_of_le hst]
        exact hrho.integrableOn_compact isCompact_Icc
      simpa [uIcc_of_le hst] using intervalIntegral.continuousOn_primitive_interval hgu
    exact Real.continuous_exp.comp_continuousOn hpr
  have hWF : ContinuousOn (fun v : ℝ => Real.exp (∫ w in s..v, rho w) * F v) (Icc s t) :=
    hφc.mul hF
  have hPPc : ContinuousOn (fun v : ℝ => ∫ w in s..v,
      Real.exp (∫ z in s..w, rho z) * F w) (Icc s t) := by
    have hgu : IntegrableOn (fun w : ℝ => Real.exp (∫ z in s..w, rho z) * F w)
        (uIcc s t) volume := by
      rw [uIcc_of_le hst]
      exact hWF.integrableOn_compact isCompact_Icc
    simpa [uIcc_of_le hst] using intervalIntegral.continuousOn_primitive_interval hgu
  have hCc : ContinuousOn (fun v : ℝ => Real.exp (∫ w in s..v, rho w) * A v
      - ∫ w in s..v, Real.exp (∫ z in s..w, rho z) * F w) (Icc s t) :=
    (hφc.mul hA).sub hPPc
  have hDiniC : ∀ x ∈ Ioo s t, x ∉ exceptional → ∀ target > 0, ∃ δ > 0,
      ∀ h ∈ Ioo (0 : ℝ) δ, x + h ≤ t →
        ((fun v : ℝ => Real.exp (∫ w in s..v, rho w) * A v
            - ∫ w in s..v, Real.exp (∫ z in s..w, rho z) * F w) (x + h)
          - (fun v : ℝ => Real.exp (∫ w in s..v, rho w) * A v
            - ∫ w in s..v, Real.exp (∫ z in s..w, rho z) * F w) x) / h ≤ target := by
    intro x hx hxE target htarget
    have hxIcc : x ∈ Icc s t := ⟨hx.1.le, hx.2.le⟩
    set φx : ℝ := Real.exp (∫ w in s..x, rho w) with hφx
    set B : ℝ := -rho x * A x + F x with hB
    set K : ℝ := |φx| + |B| + |A x| + 1 with hK
    set ε : ℝ := min (target / (10 * K)) 1 with hε
    have hK1 : 1 ≤ K := by
      rw [hK]
      have h1 := abs_nonneg φx
      have h2 := abs_nonneg B
      have h3 := abs_nonneg (A x)
      linarith
    have hKpos : 0 < K := lt_of_lt_of_le zero_lt_one hK1
    have hεpos : 0 < ε := by
      rw [hε]
      exact lt_min (div_pos htarget (by linarith)) one_pos
    have hε1 : ε ≤ 1 := by rw [hε]; exact min_le_right _ _
    have hε2 : ε ≤ target / (10 * K) := by rw [hε]; exact min_le_left _ _
    obtain ⟨δa, hδapos, hδa⟩ := hDini x ⟨hx.1.le, hx.2⟩ hxE ε hεpos
    obtain ⟨δb, hδbpos, hδb⟩ := (Metric.continuousWithinAt_iff.mp (hφc x hxIcc)) ε hεpos
    obtain ⟨δc, hδcpos, hδc⟩ := exp_integral_deriv_bound hrho hx hεpos
    obtain ⟨δd, hδdpos, hδd⟩ := integral_slope_ge hWF hxIcc hx.2 hεpos
    refine ⟨min δa (min δb (min δc δd)),
      lt_min hδapos (lt_min hδbpos (lt_min hδcpos hδdpos)), ?_⟩
    intro h hh hb
    have hha : h < δa := lt_of_lt_of_le hh.2 (min_le_left _ _)
    have hhb : h < δb := lt_of_lt_of_le hh.2 (le_trans (min_le_right _ _) (min_le_left _ _))
    have hhc : h < δc :=
      lt_of_lt_of_le hh.2 (le_trans (min_le_right _ _) (le_trans (min_le_right _ _) (min_le_left _ _)))
    have hhd : h < δd :=
      lt_of_lt_of_le hh.2 (le_trans (min_le_right _ _) (le_trans (min_le_right _ _) (min_le_right _ _)))
    have hS : (A (x + h) - A x) / h ≤ B + ε := hδa h ⟨hh.1, hha⟩ hb
    have hφdist : |Real.exp (∫ w in s..(x + h), rho w) - φx| ≤ ε := by
      have hzh : x + h ∈ Icc s t := ⟨by linarith [hx.1, hh.1], hb⟩
      have hd : dist (x + h) x < δb := by
        rw [Real.dist_eq, add_sub_cancel_left, abs_of_pos hh.1]
        exact hhb
      have h1 := hδb hzh hd
      rw [Real.dist_eq, ← hφx] at h1
      exact le_of_lt h1
    have hder : |(Real.exp (∫ w in s..(x + h), rho w) - φx) / h - φx * rho x| ≤ ε := by
      have h1 := hδc h ⟨hh.1, hhc⟩ hb
      rw [← hφx] at h1
      exact le_of_lt h1
    have hIge : φx * F x - ε ≤ h⁻¹ * ∫ w in x..(x + h),
        (Real.exp (∫ z in s..w, rho z) * F w) := by
      have h1 := hδd h ⟨hh.1, hhd⟩ hb
      rw [← hφx] at h1
      exact h1
    have hIzx : IntervalIntegrable (fun w : ℝ => Real.exp (∫ z in s..w, rho z) * F w)
        volume s (x + h) := by
      have hcont : ContinuousOn (fun w : ℝ => Real.exp (∫ z in s..w, rho z) * F w)
          (uIcc s (x + h)) := by
        rw [uIcc_of_le (by linarith [hx.1, hh.1])]
        exact hWF.mono (fun y hy => ⟨hy.1, le_trans hy.2 hb⟩)
      exact hcont.intervalIntegrable
    have hIx : IntervalIntegrable (fun w : ℝ => Real.exp (∫ z in s..w, rho z) * F w)
        volume s x := by
      have hcont : ContinuousOn (fun w : ℝ => Real.exp (∫ z in s..w, rho z) * F w)
          (uIcc s x) := by
        rw [uIcc_of_le hx.1.le]
        exact hWF.mono (Icc_subset_Icc le_rfl hx.2.le)
      exact hcont.intervalIntegrable
    have hIsub : (∫ w in s..(x + h), (Real.exp (∫ z in s..w, rho z) * F w))
        - (∫ w in s..x, (Real.exp (∫ z in s..w, rho z) * F w))
        = ∫ w in x..(x + h), (Real.exp (∫ z in s..w, rho z) * F w) :=
      intervalIntegral.integral_interval_sub_left hIzx hIx
    rw [div_eq_mul_inv]
    dsimp only
    rw [areaExpansion h (Real.exp (∫ w in s..(x + h), rho w)) φx (A (x + h)) (A x)
      (∫ w in s..(x + h), (Real.exp (∫ z in s..w, rho z) * F w))
      (∫ w in s..x, (Real.exp (∫ z in s..w, rho z) * F w))
      (∫ w in x..(x + h), (Real.exp (∫ z in s..w, rho z) * F w)) hIsub]
    have hterm1 : Real.exp (∫ w in s..(x + h), rho w) * ((A (x + h) - A x) / h)
        ≤ φx * (B + ε) + ε * |B + ε| := by
      have h1 : Real.exp (∫ w in s..(x + h), rho w) * ((A (x + h) - A x) / h)
          ≤ Real.exp (∫ w in s..(x + h), rho w) * (B + ε) :=
        mul_le_mul_of_nonneg_left hS (Real.exp_pos _).le
      have h3 : Real.exp (∫ w in s..(x + h), rho w) * (B + ε) - φx * (B + ε)
          = (Real.exp (∫ w in s..(x + h), rho w) - φx) * (B + ε) := by ring
      have h4 : (Real.exp (∫ w in s..(x + h), rho w) - φx) * (B + ε)
          ≤ |Real.exp (∫ w in s..(x + h), rho w) - φx| * |B + ε| := by
        calc (Real.exp (∫ w in s..(x + h), rho w) - φx) * (B + ε)
            ≤ |(Real.exp (∫ w in s..(x + h), rho w) - φx) * (B + ε)| := le_abs_self _
          _ = |Real.exp (∫ w in s..(x + h), rho w) - φx| * |B + ε| := abs_mul _ _
      have h5 : |Real.exp (∫ w in s..(x + h), rho w) - φx| * |B + ε| ≤ ε * |B + ε| :=
        mul_le_mul_of_nonneg_right hφdist (abs_nonneg _)
      linarith
    have hterm2 : A x * ((Real.exp (∫ w in s..(x + h), rho w) - φx) / h)
        ≤ A x * (φx * rho x) + |A x| * ε := by
      have h3 : A x * ((Real.exp (∫ w in s..(x + h), rho w) - φx) / h)
          - A x * (φx * rho x)
          = A x * ((Real.exp (∫ w in s..(x + h), rho w) - φx) / h - φx * rho x) := by ring
      have h4 : A x * ((Real.exp (∫ w in s..(x + h), rho w) - φx) / h - φx * rho x)
          ≤ |A x * ((Real.exp (∫ w in s..(x + h), rho w) - φx) / h - φx * rho x)| :=
        le_abs_self _
      have h5 : |A x * ((Real.exp (∫ w in s..(x + h), rho w) - φx) / h - φx * rho x)|
          = |A x| * |(Real.exp (∫ w in s..(x + h), rho w) - φx) / h - φx * rho x| :=
        abs_mul _ _
      have h6 : |A x| * |(Real.exp (∫ w in s..(x + h), rho w) - φx) / h - φx * rho x|
          ≤ |A x| * ε := mul_le_mul_of_nonneg_left hder (abs_nonneg _)
      linarith
    have htotal : Real.exp (∫ w in s..(x + h), rho w) * ((A (x + h) - A x) / h)
        + A x * ((Real.exp (∫ w in s..(x + h), rho w) - φx) / h)
        - (∫ w in x..(x + h), (Real.exp (∫ z in s..w, rho z) * F w)) * h⁻¹
        ≤ φx * ε + ε * |B + ε| + |A x| * ε + ε := by
      have h3 : -(∫ w in x..(x + h), (Real.exp (∫ z in s..w, rho z) * F w)) * h⁻¹
          ≤ -(φx * F x) + ε := by
        have h4 : φx * F x - ε ≤ (∫ w in x..(x + h),
            (Real.exp (∫ z in s..w, rho z) * F w)) * h⁻¹ := by
          have h5 : h⁻¹ * (∫ w in x..(x + h), (Real.exp (∫ z in s..w, rho z) * F w))
              = (∫ w in x..(x + h), (Real.exp (∫ z in s..w, rho z) * F w)) * h⁻¹ :=
            mul_comm _ _
          rw [← h5]
          exact hIge
        linarith
      nlinarith [hterm1, hterm2, h3, hB]
    have h4 : φx ≤ K := by
      rw [hK]
      have h1 := abs_nonneg B
      have h2 := abs_nonneg (A x)
      have h3 : φx ≤ |φx| := le_abs_self φx
      linarith
    have h5 : |B + ε| ≤ K := by
      rw [hK]
      have h1 : |B + ε| ≤ |B| + |ε| := abs_add_le B ε
      have h2 : |ε| = ε := abs_of_pos hεpos
      have h3 := abs_nonneg φx
      have h4 := abs_nonneg (A x)
      linarith
    have h6 : |A x| ≤ K := by
      rw [hK]
      have h1 := abs_nonneg φx
      have h2 := abs_nonneg B
      linarith
    have hKε : K * ε ≤ target / 10 := by
      have h1 : K * ε ≤ K * (target / (10 * K)) := mul_le_mul_of_nonneg_left hε2 hKpos.le
      have h2 : K * (target / (10 * K)) = target / 10 := by
        field_simp
      linarith [h1, h2.le, h2.ge]
    have heps : ε ≤ K * ε := le_mul_of_one_le_left hεpos.le hK1
    have h4' : φx * ε ≤ K * ε := mul_le_mul_of_nonneg_right h4 hεpos.le
    have h5' : ε * |B + ε| ≤ ε * K := mul_le_mul_of_nonneg_left h5 hεpos.le
    have h6' : |A x| * ε ≤ K * ε := mul_le_mul_of_nonneg_right h6 hεpos.le
    linarith [htotal, h4', h5', h6', hKε, heps]
  have hmain := le_of_dini_off_finset exceptional.card s t (fun v : ℝ =>
      Real.exp (∫ w in s..v, rho w) * A v
        - ∫ w in s..v, Real.exp (∫ z in s..w, rho z) * F w)
    exceptional hst hCc le_rfl hDiniC
  have h0 : (∫ w in s..s, Real.exp (∫ z in s..w, rho z) * F w) = 0 :=
    intervalIntegral.integral_same
  have hs : Real.exp (∫ w in s..s, rho w) = 1 := by rw [intervalIntegral.integral_same, Real.exp_zero]
  simp only [hs, h0, sub_zero] at hmain
  linarith

omit hCompact hNonempty [SigmaCompactSpace M] in
theorem continuousOn_loopFamily_areaError (B : RicciBackground (I := I) (M := M) D a b)
    (γ : ℝ → ContinuousFreeLoop M)
    (hγ : (curveOfLoopFamily γ).SmoothOn (I := I) (Icc a b))
    (hi : (curveOfLoopFamily γ).ImmersedOn (I := I) (Icc a b)) :
    ContinuousOn (fun t => (curveOfLoopFamily γ).areaError B.family.metric (Icc a b) t)
      (Icc a b) := by
  have hκ : CurveMap.Field.SmoothOn (I := I)
      ((curveOfLoopFamily γ).curvatureVector B.family.metric) (Icc a b) :=
    CurveMap.Field.smoothOn_curvatureVector B.family.metric B.smooth B.regular
      (uniqueDiffOn_Icc B.lt) (curveOfLoopFamily γ) hγ hi
  exact continuousOn_areaError_of_smoothOn_curvatureVector B.family.metric B.smooth B.regular
    (uniqueDiffOn_Icc B.lt) (curveOfLoopFamily γ) hγ hi hκ B.lt subset_rfl

omit hNonempty [SigmaCompactSpace M] in
theorem rfs_csf_immersed_area_of_continuousOn_leastArea_of_slope
    (B : RicciBackground (I := I) (M := M) D a b)
    (γ : ℝ → ContinuousFreeLoop M)
    (hγ : (curveOfLoopFamily γ).SmoothOn (I := I) (Icc a b))
    (hi : (curveOfLoopFamily γ).ImmersedOn (I := I) (Icc a b))
    (hA : ContinuousOn (loopFamilyLeastArea B.family.metric γ) (Icc a b))
    (hslope : ∀ t ∈ Ico a b, ∀ ε > 0, ∃ δ > 0, ∀ h ∈ Ioo (0 : ℝ) δ, t + h ≤ b →
      (loopFamilyLeastArea B.family.metric γ (t + h) -
          loopFamilyLeastArea B.family.metric γ t) / h ≤
        -2 * Real.pi - scalarMinimum B.family t * loopFamilyLeastArea B.family.metric γ t / 2 +
          (curveOfLoopFamily γ).areaError B.family.metric (Icc a b) t + ε) :
    ContinuousOn (loopFamilyLeastArea B.family.metric γ) (Icc a b) ∧
      (∀ s ∈ Icc a b, ∀ t ∈ Icc s b,
        areaIntegratingFactor B.family s t * loopFamilyLeastArea B.family.metric γ t ≤
          loopFamilyLeastArea B.family.metric γ s +
            ∫ v in s..t, areaIntegratingFactor B.family s v *
              (-2 * Real.pi + (curveOfLoopFamily γ).areaError B.family.metric (Icc a b) v)) ∧
      (∀ t ∈ Ico a b, ∀ ε > 0, ∃ δ > 0, ∀ h ∈ Ioo (0 : ℝ) δ, t + h ≤ b →
        (loopFamilyLeastArea B.family.metric γ (t + h) -
            loopFamilyLeastArea B.family.metric γ t) / h ≤
          -2 * Real.pi - scalarMinimum B.family t * loopFamilyLeastArea B.family.metric γ t / 2 +
            (curveOfLoopFamily γ).areaError B.family.metric (Icc a b) t + ε) := by
  have hF := continuousOn_loopFamily_areaError (I := I) (M := M) B γ hγ hi
  refine ⟨hA, ?_, hslope⟩
  intro s hs t ht
  have hst : s ≤ t := ht.1
  have hAsub : Icc s t ⊆ Icc a b := Icc_subset_Icc hs.1 ht.2
  have hA' : ContinuousOn (loopFamilyLeastArea B.family.metric γ) (Icc s t) :=
    hA.mono hAsub
  have hrho : ContinuousOn (fun v => scalarMinimum B.family v / 2) (Icc s t) :=
    ((RicciBackground.continuousOn_scalarMinimum B).div_const 2).mono hAsub
  have hF' : ContinuousOn (fun v => -2 * Real.pi +
      (curveOfLoopFamily γ).areaError B.family.metric (Icc a b) v) (Icc s t) :=
    (continuousOn_const.add hF).mono hAsub
  have hDini : ∀ v ∈ Ico s t, v ∉ (∅ : Finset ℝ) → ∀ ε > 0, ∃ δ > 0,
      ∀ h ∈ Ioo (0 : ℝ) δ, v + h ≤ t →
        (loopFamilyLeastArea B.family.metric γ (v + h) -
            loopFamilyLeastArea B.family.metric γ v) / h ≤
          -(scalarMinimum B.family v / 2) * loopFamilyLeastArea B.family.metric γ v +
            (-2 * Real.pi + (curveOfLoopFamily γ).areaError B.family.metric (Icc a b) v) + ε := by
    intro v hv _ ε hε
    obtain ⟨δ, hδpos, hδ⟩ := hslope v ⟨le_trans hs.1 hv.1, lt_of_lt_of_le hv.2 ht.2⟩ ε hε
    refine ⟨δ, hδpos, fun h hh hb => ?_⟩
    have h1 := hδ h hh (le_trans hb ht.2)
    have h2 : -2 * Real.pi - scalarMinimum B.family v *
          loopFamilyLeastArea B.family.metric γ v / 2 +
          (curveOfLoopFamily γ).areaError B.family.metric (Icc a b) v + ε =
        -(scalarMinimum B.family v / 2) * loopFamilyLeastArea B.family.metric γ v +
          (-2 * Real.pi + (curveOfLoopFamily γ).areaError B.family.metric (Icc a b) v) + ε := by
      ring
    linarith [h1, h2.le, h2.ge]
  have hmain := rfs_csf_area_comparison_ode (A := loopFamilyLeastArea B.family.metric γ)
    (rho := fun v => scalarMinimum B.family v / 2)
    (F := fun v => -2 * Real.pi + (curveOfLoopFamily γ).areaError B.family.metric (Icc a b) v)
    s t hst hA' hrho hF' (∅ : Finset ℝ) hDini
  have hrho' : (fun w => scalarMinimum B.family w / 2) =
      fun w => (1 / 2 : ℝ) * scalarMinimum B.family w := by
    funext w; ring
  rw [hrho'] at hmain
  simpa only [areaIntegratingFactor, intervalIntegral.integral_const_mul] using hmain


omit hNonempty [SigmaCompactSpace M] in
theorem rfs_csf_immersed_area_of_continuousOn_leastArea_of_window
    (B : RicciBackground (I := I) (M := M) D a b)
    (γ : ℝ → ContinuousFreeLoop M)
    (hγ : (curveOfLoopFamily γ).SmoothOn (I := I) (Icc a b))
    (hi : (curveOfLoopFamily γ).ImmersedOn (I := I) (Icc a b))
    (hA : ContinuousOn (loopFamilyLeastArea B.family.metric γ) (Icc a b))
    (hwindow : ∀ s ∈ Icc a b, ∀ u ∈ Icc s b,
      Real.exp (∫ w in s..u, scalarMinimum B.family w / 2) *
          loopFamilyLeastArea B.family.metric γ u ≤
        loopFamilyLeastArea B.family.metric γ s +
          ∫ v in s..u, Real.exp (∫ w in s..v, scalarMinimum B.family w / 2) *
            (-2 * Real.pi + (curveOfLoopFamily γ).areaError B.family.metric (Icc a b) v)) :
    ContinuousOn (loopFamilyLeastArea B.family.metric γ) (Icc a b) ∧
      (∀ s ∈ Icc a b, ∀ t ∈ Icc s b,
        areaIntegratingFactor B.family s t * loopFamilyLeastArea B.family.metric γ t ≤
          loopFamilyLeastArea B.family.metric γ s +
            ∫ v in s..t, areaIntegratingFactor B.family s v *
              (-2 * Real.pi + (curveOfLoopFamily γ).areaError B.family.metric (Icc a b) v)) ∧
      (∀ t ∈ Ico a b, ∀ ε > 0, ∃ δ > 0, ∀ h ∈ Ioo (0 : ℝ) δ, t + h ≤ b →
        (loopFamilyLeastArea B.family.metric γ (t + h) -
            loopFamilyLeastArea B.family.metric γ t) / h ≤
          -2 * Real.pi - scalarMinimum B.family t * loopFamilyLeastArea B.family.metric γ t / 2 +
            (curveOfLoopFamily γ).areaError B.family.metric (Icc a b) t + ε) := by
  have hF := continuousOn_loopFamily_areaError (I := I) (M := M) B γ hγ hi
  have hrho' : (fun w => scalarMinimum B.family w / 2) =
      fun w => (1 / 2 : ℝ) * scalarMinimum B.family w := by
    funext w; ring
  refine ⟨hA, ?_, rfs_csf_slope_le_of_window_comparison B γ hA hF ?_⟩
  · intro s hs t ht
    have h := hwindow s hs t ht
    rw [hrho'] at h
    simpa only [areaIntegratingFactor, intervalIntegral.integral_const_mul] using h
  · intro s hs u hu
    exact hwindow s hs u hu




end DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening
