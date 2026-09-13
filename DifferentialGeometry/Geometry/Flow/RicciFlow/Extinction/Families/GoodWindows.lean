import DifferentialGeometry.Geometry.Flow.RicciFlow.Extinction.Families.Flow
import DifferentialGeometry.Geometry.Flow.RicciFlow.Extinction.CurveShortening.LocalRegularity
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Periodic
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.Topology.Order.IntermediateValue
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

omit [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
  [TopologicalSpace H] [TopologicalSpace Q] [ChartedSpace H Q] [IsManifold I ∞ Q]
  [SigmaCompactSpace Q] hT2 hCompact hConnected hBoundary in
theorem le_of_arclength_lipschitz_integral_bound {u v : ℝ → ℝ} {x₀ K ell lam : ℝ}
    (hK : 0 < K) (hell : 0 < ell)
    (hucont : ContinuousOn u (Icc x₀ (x₀ + 1)))
    (hvcont : ContinuousOn v (Icc x₀ (x₀ + 1)))
    (hvnn : ∀ x ∈ Icc x₀ (x₀ + 1), 0 ≤ v x)
    (hunonneg : ∀ x ∈ Icc x₀ (x₀ + 1), 0 ≤ u x)
    (hslope : ∀ x, x₀ ≤ x → x ≤ x₀ + 1 →
      |u x - u x₀| ≤ K * ∫ z in x₀..x, v z)
    (hmass : (∫ z in x₀..(x₀ + 1), u z * v z) = lam)
    (hL : ell ≤ ∫ z in x₀..(x₀ + 1), v z) :
    u x₀ ≤ 2 * lam / ell + 2 * Real.sqrt (K * lam) := by
  have hx1 : x₀ ≤ x₀ + 1 := by linarith
  have hlam : 0 ≤ lam := by
    rw [← hmass]
    exact intervalIntegral.integral_nonneg hx1 fun z hz =>
      mul_nonneg (hunonneg z hz) (hvnn z hz)
  have hLu : uIcc x₀ (x₀ + 1) = Icc x₀ (x₀ + 1) := uIcc_of_le hx1
  have hvcont' : ContinuousOn v (uIcc x₀ (x₀ + 1)) := by rw [hLu]; exact hvcont
  have hucont' : ContinuousOn u (uIcc x₀ (x₀ + 1)) := by rw [hLu]; exact hucont
  have hLint : IntervalIntegrable v volume x₀ (x₀ + 1) := hvcont'.intervalIntegrable
  have hFc : ContinuousOn (fun x => ∫ z in x₀..x, v z) (Icc x₀ (x₀ + 1)) := by
    rw [← hLu]
    exact intervalIntegral.continuousOn_primitive_interval' hLint left_mem_uIcc
  rcases le_or_gt (u x₀) 0 with hm | hm
  · have h1 : 0 ≤ 2 * lam / ell := by positivity
    have h2 : 0 ≤ 2 * Real.sqrt (K * lam) := by
      have : 0 ≤ K * lam := mul_nonneg hK.le hlam
      positivity
    linarith
  set L := ∫ z in x₀..(x₀ + 1), v z with hLdef
  have hLpos : 0 < L := lt_of_lt_of_le hell hL
  have hmem : min L (u x₀ / (2 * K)) ∈
      Icc ((fun x => ∫ z in x₀..x, v z) x₀) ((fun x => ∫ z in x₀..x, v z) (x₀ + 1)) := by
    have h0 : (fun x => ∫ z in x₀..x, v z) x₀ = 0 := intervalIntegral.integral_same
    have h1 : (fun x => ∫ z in x₀..x, v z) (x₀ + 1) = L := rfl
    rw [h0, h1]
    exact ⟨le_min hLpos.le (by positivity), min_le_left _ _⟩
  obtain ⟨ξ, hξ, hξeq⟩ := intermediate_value_Icc hx1 hFc hmem
  have hξeq' : (∫ w in x₀..ξ, v w) = min L (u x₀ / (2 * K)) := hξeq
  have hξ1 : x₀ ≤ ξ := hξ.1
  have hξ2 : ξ ≤ x₀ + 1 := hξ.2
  have hsub : Icc x₀ ξ ⊆ Icc x₀ (x₀ + 1) := Icc_subset_Icc le_rfl hξ2
  have hmono : ∀ (f : ℝ → ℝ), ContinuousOn f (Icc x₀ (x₀ + 1)) →
      IntervalIntegrable f volume x₀ ξ := by
    intro f hf
    have : ContinuousOn f (uIcc x₀ ξ) := by rw [uIcc_of_le hξ1]; exact hf.mono hsub
    exact this.intervalIntegrable
  have hFmono : ∀ z ∈ Icc x₀ ξ, (∫ w in x₀..z, v w) ≤ min L (u x₀ / (2 * K)) := by
    intro z hz
    have hle : (∫ w in x₀..z, v w) ≤ ∫ w in x₀..ξ, v w :=
      intervalIntegral.integral_mono_interval le_rfl hz.1 hz.2
        ((ae_restrict_iff' measurableSet_Ioc).mpr
          (ae_of_all _ (fun w hw => hvnn w ⟨hw.1.le, hw.2.trans hξ2⟩)))
        (hmono v hvcont)
    rw [hξeq'] at hle
    exact hle
  have hpt : ∀ z ∈ Icc x₀ ξ, u x₀ - K * min L (u x₀ / (2 * K)) ≤ u z := by
    intro z hz
    have h := hslope z hz.1 (hz.2.trans hξ2)
    have h2 : K * (∫ w in x₀..z, v w) ≤ K * min L (u x₀ / (2 * K)) :=
      mul_le_mul_of_nonneg_left (hFmono z hz) hK.le
    have habs : |u x₀ - u z| ≤ K * min L (u x₀ / (2 * K)) := by
      rw [abs_sub_comm]; exact h.trans h2
    linarith [le_abs_self (u x₀ - u z)]
  have hhalf : u x₀ / 2 ≤ u x₀ - K * min L (u x₀ / (2 * K)) := by
    have hq := min_le_right L (u x₀ / (2 * K))
    have h2K : (0 : ℝ) < 2 * K := by positivity
    have h1 : min L (u x₀ / (2 * K)) * (2 * K) ≤ u x₀ := by
      calc min L (u x₀ / (2 * K)) * (2 * K) ≤ (u x₀ / (2 * K)) * (2 * K) :=
            mul_le_mul_of_nonneg_right hq h2K.le
        _ = u x₀ := by field_simp
    nlinarith [h1]
  have hint_uv : IntervalIntegrable (fun z => u z * v z) volume x₀ ξ :=
    hmono _ (hucont.mul hvcont)
  have hint_tail : IntervalIntegrable (fun z => u z * v z) volume ξ (x₀ + 1) := by
    have hsub' : Icc ξ (x₀ + 1) ⊆ Icc x₀ (x₀ + 1) := Icc_subset_Icc hξ1 le_rfl
    have : ContinuousOn (fun z => u z * v z) (uIcc ξ (x₀ + 1)) := by
      rw [uIcc_of_le hξ2]
      exact (hucont.mul hvcont).mono hsub'
    exact this.intervalIntegrable
  have hsplit : (∫ z in x₀..ξ, u z * v z) + (∫ z in ξ..(x₀ + 1), u z * v z) = lam := by
    rw [intervalIntegral.integral_add_adjacent_intervals hint_uv hint_tail, hmass]
  have htail : 0 ≤ ∫ z in ξ..(x₀ + 1), u z * v z :=
    intervalIntegral.integral_nonneg hξ2 (fun z hz =>
      mul_nonneg (hunonneg z (Icc_subset_Icc hξ1 le_rfl hz))
        (hvnn z (Icc_subset_Icc hξ1 le_rfl hz)))
  have hmain : (u x₀ / 2) * min L (u x₀ / (2 * K)) ≤ lam := by
    have hc : IntervalIntegrable (fun z => (u x₀ - K * min L (u x₀ / (2 * K))) * v z)
        volume x₀ ξ := hmono _ (continuousOn_const.mul hvcont)
    have hmono1 : (∫ z in x₀..ξ, (u x₀ - K * min L (u x₀ / (2 * K))) * v z) ≤
        ∫ z in x₀..ξ, u z * v z :=
      intervalIntegral.integral_mono_on hξ1 hc hint_uv
        (fun z hz => mul_le_mul_of_nonneg_right (hpt z hz) (hvnn z (hsub hz)))
    have hconst : (∫ z in x₀..ξ, (u x₀ - K * min L (u x₀ / (2 * K))) * v z) =
        (u x₀ - K * min L (u x₀ / (2 * K))) * min L (u x₀ / (2 * K)) := by
      rw [intervalIntegral.integral_const_mul, hξeq']
    have hstep : (u x₀ - K * min L (u x₀ / (2 * K))) * min L (u x₀ / (2 * K)) ≤
        ∫ z in x₀..ξ, u z * v z := by rw [← hconst]; exact hmono1
    have hfin : (∫ z in x₀..ξ, u z * v z) ≤ lam := by linarith [hsplit, htail]
    nlinarith [hm, hhalf, hstep, hfin]
  rcases le_or_gt L (u x₀ / (2 * K)) with hcase | hcase
  · have hq : min L (u x₀ / (2 * K)) = L := min_eq_left hcase
    rw [hq] at hmain
    have hle1 : (u x₀ / 2) * ell ≤ lam :=
      (mul_le_mul_of_nonneg_left hL (by positivity)).trans hmain
    have hle2 : u x₀ ≤ 2 * lam / ell := by
      rw [le_div_iff₀ hell]
      nlinarith
    have h2 : 0 ≤ 2 * Real.sqrt (K * lam) := by
      have : 0 ≤ K * lam := mul_nonneg hK.le hlam
      positivity
    linarith
  · have hq : min L (u x₀ / (2 * K)) = u x₀ / (2 * K) := min_eq_right hcase.le
    rw [hq] at hmain
    have hval : (u x₀ / 2) * (u x₀ / (2 * K)) = u x₀ ^ 2 / (4 * K) := by
      field_simp
      ring
    have hfin : u x₀ ^ 2 / (4 * K) ≤ lam := hval ▸ hmain
    have hsq : u x₀ ^ 2 ≤ 4 * K * lam := by
      rw [div_le_iff₀ (by positivity : (0 : ℝ) < 4 * K)] at hfin
      linarith
    have hroot : u x₀ ≤ Real.sqrt (4 * K * lam) := by
      rw [← Real.sqrt_sq hm.le]
      exact Real.sqrt_le_sqrt hsq
    have hres : Real.sqrt (4 * K * lam) = 2 * Real.sqrt (K * lam) := by
      rw [show (4 : ℝ) * K * lam = 2 ^ 2 * (K * lam) by ring,
        Real.sqrt_mul (by positivity : (0 : ℝ) ≤ (2 : ℝ) ^ 2),
        Real.sqrt_sq (by norm_num : (0 : ℝ) ≤ 2)]
    rw [hres] at hroot
    have hl : 0 ≤ 2 * lam / ell := by positivity
    linarith

omit [SigmaCompactSpace Q] hT2 hCompact hConnected hBoundary in
theorem rfs_ramp_small_angle (g : SmoothRiemannianMetric I Q)
    (c : ProductCurve Q) (lambda t ell K : ℝ) (hlambda : 0 < lambda)
    (hell : 0 < ell) (hK : 0 < K) (hdegree : c.degree = 1)
    (hsmooth : c.SmoothOn (I := I) {t})
    (hramp : c.IsRampOn (fun _ => g) lambda {t})
    (hlength : ell ≤ c.length (fun _ => g) lambda t)
    (hcurvature : ∀ x, c.curvature (fun _ => g) lambda x t ≤ K) :
    ∀ x, c.angle (fun _ => g) lambda x t ≤ 2 * lambda / ell + 2 * Real.sqrt (K * lambda) := by
  intro x
  have ht : t ∈ ({t} : Set ℝ) := mem_singleton t
  have hucont : ContinuousOn (fun z => c.angle (fun _ => g) lambda z t) (Icc x (x + 1)) :=
    ((c.angle_contDiff_of_immersedOn (fun _ => g) lambda hlambda hsmooth hramp.1 t
      ht).continuous).continuousOn
  have hvcont : ContinuousOn (fun z => c.speed (fun _ => g) lambda z t) (Icc x (x + 1)) :=
    ((c.speed_contDiff_of_immersedOn (fun _ => g) lambda hlambda hsmooth hramp.1 t
      ht).continuous).continuousOn
  have hvnn : ∀ z ∈ Icc x (x + 1), 0 ≤ c.speed (fun _ => g) lambda z t :=
    fun z _ => Real.sqrt_nonneg _
  have hunonneg : ∀ z ∈ Icc x (x + 1), 0 ≤ c.angle (fun _ => g) lambda z t :=
    fun z _ => (hramp.2 z t ht).le
  have hslope : ∀ y, x ≤ y → y ≤ x + 1 →
      |c.angle (fun _ => g) lambda y t - c.angle (fun _ => g) lambda x t| ≤
        K * ∫ z in x..y, c.speed (fun _ => g) lambda z t := by
    intro y hy1 _
    simpa [ProductCurve.arcLength] using
      c.abs_angle_sub_le_mul_arcLength (fun _ => g) lambda hlambda hsmooth hramp.1 ht
        hcurvature hy1
  have hmass : (∫ z in x..(x + 1),
      c.angle (fun _ => g) lambda z t * c.speed (fun _ => g) lambda z t) = lambda := by
    have hshift := (c.angle_mul_speed_periodic (fun _ => g) lambda hsmooth t ht).intervalIntegral_add_eq x 0
    rw [zero_add] at hshift
    have hbase := productCurve_integral_angle_of_smoothOn c (fun _ => g) lambda hlambda hsmooth ht
    rw [ProductCurve.integral, hdegree, Int.cast_one, one_mul] at hbase
    calc (∫ z in x..(x + 1),
          c.angle (fun _ => g) lambda z t * c.speed (fun _ => g) lambda z t)
        = ∫ z in (0 : ℝ)..1,
          c.angle (fun _ => g) lambda z t * c.speed (fun _ => g) lambda z t := hshift
      _ = lambda := hbase
  have hlen : ell ≤ ∫ z in x..(x + 1), c.speed (fun _ => g) lambda z t := by
    have hlen_eq : (∫ z in x..(x + 1), c.speed (fun _ => g) lambda z t) =
        c.length (fun _ => g) lambda t :=
      c.arcLength_period_eq_length (fun _ => g) lambda hsmooth t ht x
    rw [hlen_eq]
    exact hlength
  exact le_of_arclength_lipschitz_integral_bound (u := fun z => c.angle (fun _ => g) lambda z t)
    (v := fun z => c.speed (fun _ => g) lambda z t) (x₀ := x) (K := K) (ell := ell)
    (lam := lambda) hK hell hucont hvcont hvnn hunonneg hslope hmass hlen


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

omit [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
  [TopologicalSpace H] [TopologicalSpace Q] [ChartedSpace H Q] [IsManifold I ∞ Q]
  hT2 hCompact hConnected hBoundary in
theorem volume_lt_le_of_integral_le {f : ℝ → ℝ} {s t B C : ℝ}
    (hst : s ≤ t) (hB : 0 < B)
    (hint : IntervalIntegrable f volume s t)
    (hnn : ∀ v ∈ Icc s t, 0 ≤ f v)
    (hE : (∫ v in s..t, f v) ≤ C) :
    volume {v : ℝ | v ∈ Icc s t ∧ B < f v} ≤ ENNReal.ofReal (C / B) := by
  have hintI : IntegrableOn f (Icc s t) volume :=
    (intervalIntegrable_iff_integrableOn_Icc_of_le hst).mp hint
  have hnn' : 0 ≤ᵐ[volume.restrict (Icc s t)] f :=
    (ae_restrict_iff' measurableSet_Icc).mpr (Filter.Eventually.of_forall hnn)
  have hmeas : AEMeasurable f (volume.restrict (Icc s t)) := hintI.aestronglyMeasurable.aemeasurable
  have hmeas' : AEMeasurable (fun v => ENNReal.ofReal (f v)) (volume.restrict (Icc s t)) :=
    hmeas.ennreal_ofReal
  have hmark := MeasureTheory.meas_ge_le_lintegral_div (μ := volume.restrict (Icc s t)) hmeas'
    (ε := ENNReal.ofReal B) (by rw [ne_eq, ENNReal.ofReal_eq_zero, not_le]; exact hB)
    ENNReal.ofReal_ne_top
  have hsub : {v : ℝ | v ∈ Icc s t ∧ B < f v} ⊆
      Icc s t ∩ {v : ℝ | ENNReal.ofReal B ≤ ENNReal.ofReal (f v)} := fun v hv =>
    ⟨hv.1, ENNReal.ofReal_le_ofReal hv.2.le⟩
  have hnull : NullMeasurableSet {v : ℝ | ENNReal.ofReal B ≤ ENNReal.ofReal (f v)}
      (volume.restrict (Icc s t)) := hmeas'.nullMeasurableSet_preimage measurableSet_Ici
  have hres : (volume.restrict (Icc s t)) {v : ℝ | ENNReal.ofReal B ≤ ENNReal.ofReal (f v)} =
      volume (Icc s t ∩ {v : ℝ | ENNReal.ofReal B ≤ ENNReal.ofReal (f v)}) := by
    rw [Measure.restrict_apply₀ hnull, Set.inter_comm]
  have hIcc : (∫ x, f x ∂(volume.restrict (Icc s t))) = ∫ v in s..t, f v :=
    integral_Icc_eq_integral_Ioc.trans (intervalIntegral.integral_of_le hst).symm
  have hlint : (∫⁻ v, ENNReal.ofReal (f v) ∂(volume.restrict (Icc s t))) =
      ENNReal.ofReal (∫ v in s..t, f v) := by
    rw [← hIcc, ← MeasureTheory.ofReal_integral_eq_lintegral_ofReal hintI hnn']
  calc volume {v : ℝ | v ∈ Icc s t ∧ B < f v}
      ≤ volume (Icc s t ∩ {v : ℝ | ENNReal.ofReal B ≤ ENNReal.ofReal (f v)}) :=
        measure_mono hsub
    _ = (volume.restrict (Icc s t)) {v : ℝ | ENNReal.ofReal B ≤ ENNReal.ofReal (f v)} := hres.symm
    _ ≤ (∫⁻ v, ENNReal.ofReal (f v) ∂(volume.restrict (Icc s t))) / ENNReal.ofReal B := hmark
    _ = ENNReal.ofReal (∫ v in s..t, f v) / ENNReal.ofReal B := by rw [hlint]
    _ ≤ ENNReal.ofReal C / ENNReal.ofReal B :=
        ENNReal.div_le_div_right (ENNReal.ofReal_le_ofReal hE) _
    _ = ENNReal.ofReal (C / B) := (ENNReal.ofReal_div_of_pos hB).symm

omit [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
  [TopologicalSpace H] [TopologicalSpace Q] [ChartedSpace H Q] [IsManifold I ∞ Q]
  hT2 hCompact hConnected hBoundary in
theorem volume_image_add_right (c : ℝ) (B : Set ℝ) :
    volume ((fun v : ℝ => v + c) '' B) = volume B := by
  have hfun : (fun v : ℝ => v + c) '' B = (fun v : ℝ => v + (-c)) ⁻¹' B := by
    ext v; constructor
    · rintro ⟨u, hu, rfl⟩
      simpa only [Set.mem_preimage, add_assoc, add_neg_cancel, add_zero] using hu
    · intro hv
      exact ⟨v + -c, hv, by ring⟩
  rw [hfun]
  exact measure_preimage_add_right volume (-c) B


omit [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
  [TopologicalSpace H] [TopologicalSpace Q] [ChartedSpace H Q] [IsManifold I ∞ Q]
  hT2 hCompact hConnected hBoundary in
theorem exists_goodWindow_finset_of_energy_bound {a b d C threshold : ℝ} (hd : 0 < d) (hab : a ≤ b)
    {f : ℝ → ℝ} (hfint : IntervalIntegrable f volume a b)
    (hfnn : ∀ t ∈ Icc a b, 0 ≤ f t) (hfb : (∫ t in a..b, f t) ≤ C)
    (hth : 0 < threshold) :
    ∃ starts : Finset ℝ,
      (∀ w ∈ starts, w ∈ Icc a (b - d) ∧ f w ≤ threshold) ∧
      goodWindowUnion starts d ⊆ Ioo a b ∧
      volume (Icc a b \ goodWindowUnion starts d) ≤ ENNReal.ofReal (d + C / threshold) ∧
      ∀ w ∈ starts, Icc (w + 5 * d / 8) (w + 7 * d / 8) ⊆ Ioo (w + d / 2) (w + d) := by
  classical
  have hCnn : 0 ≤ C := le_trans (intervalIntegral.integral_nonneg hab hfnn) hfb
  have hCdiv : 0 ≤ C / threshold := div_nonneg hCnn hth.le
  have hof : ENNReal.ofReal (d + C / threshold) =
      ENNReal.ofReal d + ENNReal.ofReal (C / threshold) :=
    ENNReal.ofReal_add (le_of_lt hd) hCdiv
  have hMarkov : volume {v : ℝ | v ∈ Icc a b ∧ threshold < f v} ≤
      ENNReal.ofReal (C / threshold) :=
    volume_lt_le_of_integral_le hab hth hfint hfnn hfb
  by_cases hsmall : b - a ≤ d
  · refine ⟨∅, ?_, ?_, ?_, ?_⟩
    · intro w hw; simp at hw
    · intro t ht
      simp only [goodWindowUnion, Set.mem_ofPred_eq] at ht
      obtain ⟨w, hw, -⟩ := ht
      simp at hw
    · have hset : Icc a b \ goodWindowUnion (∅ : Finset ℝ) d = Icc a b := by
        ext t
        simp only [goodWindowUnion, Set.mem_ofPred_eq, mem_sdiff, mem_Icc]
        constructor
        · rintro ⟨h, -⟩; exact h
        · intro h; exact ⟨h, fun hcon => by obtain ⟨w, hw, -⟩ := hcon; simp at hw⟩
      rw [hset, Real.volume_Icc, hof]
      exact le_trans (ENNReal.ofReal_le_ofReal hsmall) (le_add_of_nonneg_right bot_le)
    · intro w hw; simp at hw
  · have hgt : d < b - a := lt_of_not_ge hsmall
    set h : ℝ := d / 8 with hh
    have hhpos : 0 < h := by rw [hh]; positivity
    have hdh : 8 * h = d := by rw [hh]; ring
    have h5 : (5 : ℝ) * d / 8 = 5 * h := by rw [hh]; ring
    have h7 : (7 : ℝ) * d / 8 = 7 * h := by rw [hh]; ring
    have hbann : 0 ≤ b - a := by linarith
    set m : ℕ := ⌊(b - a) / h⌋₊ with hm
    have hmge : 8 ≤ m := by
      have h1 : (8 : ℝ) ≤ (b - a) / h := by
        rw [le_div_iff₀ hhpos]; linarith [hdh, hgt]
      simpa [hm] using Nat.le_floor h1
    set K : ℕ := m - 8 with hK
    set r : ℝ := b - a - (m : ℝ) * h with hr
    have hKr : (K : ℝ) = (m : ℝ) - 8 := by rw [hK]; exact Nat.cast_sub hmge
    have hm0 : 0 ≤ (b - a) / h := div_nonneg hbann hhpos.le
    have hmh_le : (m : ℝ) * h ≤ b - a := by
      have h1 : ((m : ℝ)) ≤ (b - a) / h := by simpa [hm] using Nat.floor_le hm0
      have h2 : ((m : ℝ)) * h ≤ ((b - a) / h) * h := mul_le_mul_of_nonneg_right h1 hhpos.le
      rwa [div_mul_cancel₀ _ (ne_of_gt hhpos)] at h2
    have hmh_lt : b - a < ((m : ℝ) + 1) * h := by
      have h1 : ((b - a) / h) < ((m : ℝ) + 1) := by
        simpa [hm] using Nat.lt_floor_add_one ((b - a) / h)
      have h2 : ((b - a) / h) * h < ((m : ℝ) + 1) * h := mul_lt_mul_of_pos_right h1 hhpos
      rwa [div_mul_cancel₀ _ (ne_of_gt hhpos)] at h2
    have hrnn : 0 ≤ r := by rw [hr]; linarith
    have hrlt : r < h := by
      have h3 : b - a < (m : ℝ) * h + h := by linarith [hmh_lt]
      rw [hr]; linarith
    set p : ℕ → ℝ := fun j => a + (j : ℝ) * h with hp
    have hp_apply : ∀ j : ℕ, p j = a + (j : ℝ) * h := fun j => rfl
    have hp_add : ∀ j k : ℕ, p (j + k) = p j + (k : ℝ) * h := by
      intro j k; rw [hp_apply, hp_apply]; push_cast; ring
    have hp_succ : ∀ j, p (j + 1) = p j + h := by intro j; simpa using hp_add j 1
    have hpa : ∀ j, a ≤ p j := by
      intro j; rw [hp_apply]
      exact le_add_of_nonneg_right (mul_nonneg (Nat.cast_nonneg j) hhpos.le)
    have hp_mono : Monotone p := by
      intro i j hij
      rw [hp_apply, hp_apply]
      have h1 : (i : ℝ) ≤ (j : ℝ) := Nat.cast_le.mpr hij
      nlinarith [hhpos]
    have hpK_le : p K ≤ b - d := by
      rw [hp_apply, hKr, ← hdh]; nlinarith [hmh_le]
    have hbd : b - d = p K + r := by
      rw [hp_apply, hr, hKr, ← hdh]; ring
    set cell : ℕ → Set ℝ := fun j => if j < K then Icc (p j) (p (j + 1)) else Icc (p K) (b - d)
      with hcell
    have hcell_lt : ∀ j, j < K → cell j = Icc (p j) (p (j + 1)) := by
      intro j hj; simp only [hcell, if_pos hj]
    have hcell_ge : ∀ j, K ≤ j → cell j = Icc (p K) (b - d) := by
      intro j hj; simp only [hcell, if_neg (not_lt.mpr hj)]
    have hcell_sub : ∀ j, cell j ⊆ Icc a (b - d) := by
      intro j
      rcases lt_or_ge j K with hlt | hge
      · rw [hcell_lt j hlt]
        exact Icc_subset_Icc (hpa j) (le_trans (hp_mono (by omega)) hpK_le)
      · rw [hcell_ge j hge]; exact Icc_subset_Icc (hpa K) le_rfl
    have hcell_ab : ∀ j, cell j ⊆ Icc a b := by
      intro j
      exact Subset.trans (hcell_sub j) (Icc_subset_Icc le_rfl (by linarith [hd, hdh]))
    set good : ℕ → Prop := fun j => ∃ x : ℝ, x ∈ cell j ∧ f x ≤ threshold with hgood
    set wfun : ℕ → ℝ := fun j => if hj : good j then Classical.choose hj else a with hwfun
    have hwfun_spec : ∀ j, good j → wfun j ∈ cell j ∧ f (wfun j) ≤ threshold := by
      intro j hj
      have h1 : wfun j = Classical.choose hj := by rw [hwfun]; simp only [dif_pos hj]
      rw [h1]; exact Classical.choose_spec hj
    have hxlo : ∀ j ≤ K, ∀ x ∈ cell j, p j ≤ x := by
      intro j hj x hx
      rcases lt_or_eq_of_le hj with hlt | heq
      · rw [hcell_lt j hlt] at hx; exact hx.1
      · subst heq; rw [hcell_ge K le_rfl] at hx; exact hx.1
    have hxhi_lt : ∀ j, j < K → ∀ x ∈ cell j, x ≤ p j + h := by
      intro j hj x hx
      rw [hcell_lt j hj, hp_succ j] at hx
      exact hx.2
    have hxhi_K : ∀ x ∈ cell K, x ≤ p K + r := by
      intro x hx
      rw [hcell_ge K le_rfl, hbd] at hx
      exact hx.2
    have hcover : ∀ j ≤ K, ∀ x ∈ cell j,
        Icc (p (j + 6)) (p (j + 7)) ⊆ Icc (x + 5 * h) (x + 7 * h) := by
      intro j hj x hx
      rcases lt_or_eq_of_le hj with hlt | heq
      · have h1 : x + 5 * h ≤ p (j + 6) := by
          have hA := hxhi_lt j hlt x hx
          have hB : p (j + 6) = p j + 6 * h := hp_add j 6
          linarith
        have h2 : p (j + 7) ≤ x + 7 * h := by
          have hA := hxlo j hj x hx
          have hB : p (j + 7) = p j + 7 * h := hp_add j 7
          linarith
        exact Icc_subset_Icc h1 h2
      · subst heq
        have h1 : x + 5 * h ≤ p (K + 6) := by
          have hA := hxhi_K x hx
          have hB : p (K + 6) = p K + 6 * h := hp_add K 6
          linarith
        have h2 : p (K + 7) ≤ x + 7 * h := by
          have hA := hxlo K le_rfl x hx
          have hB : p (K + 7) = p K + 7 * h := hp_add K 7
          linarith
        exact Icc_subset_Icc h1 h2
    set starts : Finset ℝ := ((Finset.range (K + 1)).filter good).image wfun with hstarts
    have hmem : ∀ w ∈ starts, w ∈ Icc a (b - d) ∧ f w ≤ threshold := by
      intro w hw
      rw [hstarts] at hw
      obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp hw
      obtain ⟨hjr, hjg⟩ := Finset.mem_filter.mp hj
      have hjle : j ≤ K := Nat.lt_succ_iff.mp (Finset.mem_range.mp hjr)
      exact ⟨hcell_sub j (hwfun_spec j hjg).1, (hwfun_spec j hjg).2⟩
    refine ⟨starts, hmem, ?_, ?_, ?_⟩
    · rintro t ⟨w, hw, ht⟩
      obtain ⟨hwd, -⟩ := hmem w hw
      have h1 : a < t := by
        have h2 : a + 5 * d / 8 ≤ t := by linarith [ht.1, hwd.1]
        linarith [hd]
      have h2 : t < b := by
        have h3 : w + 7 * d / 8 ≤ b - d + 7 * d / 8 := by linarith [hwd.2]
        linarith [ht.2, h3, hd]
      exact ⟨h1, h2⟩
    · have hbad : ∀ j, ¬ good j → cell j ⊆ {v : ℝ | v ∈ Icc a b ∧ threshold < f v} := by
        intro j hnj x hx
        exact ⟨hcell_ab j hx, lt_of_not_ge (fun hle => hnj ⟨x, hx, hle⟩)⟩
      set X : Set ℝ := Icc a (p 6) with hX
      set Y : Set ℝ := Icc (p (K + 7)) b with hY
      set D : Set ℝ := Icc (p (K + 6) + r) (p (K + 7)) with hD
      set Btr : Set ℝ := (fun v : ℝ => v + 6 * h) ''
        {v : ℝ | v ∈ Icc a b ∧ threshold < f v} with hBtr
      have hvX : volume X = ENNReal.ofReal (6 * h) := by
        rw [hX, Real.volume_Icc]; congr 1
        rw [hp_apply]; push_cast; ring
      have hvY : volume Y = ENNReal.ofReal (h + r) := by
        rw [hY, Real.volume_Icc]; congr 1
        have hA : p (K + 7) = a + ((m : ℝ) - 1) * h := by
          rw [hp_add K 7, hp_apply, hKr]; push_cast; ring
        rw [hA, hr]; ring
      have hvD : volume D = ENNReal.ofReal (h - r) := by
        rw [hD, Real.volume_Icc]; congr 1
        have hA : p (K + 7) = p (K + 6) + h := by rw [hp_add K 7, hp_add K 6]; ring
        rw [hA]; ring
      have hvB : volume Btr ≤ ENNReal.ofReal (C / threshold) := by
        rw [hBtr, volume_image_add_right]; exact hMarkov
      have hfind : ∀ t : ℝ, p 6 ≤ t → t < p (K + 7) →
          ∃ j ≤ K, t ∈ Icc (p (j + 6)) (p (j + 7)) := by
        intro t ht6 htK7
        have hpa6 : a ≤ t := le_trans (hpa 6) ht6
        have hx0 : 0 ≤ (t - a) / h := div_nonneg (by linarith) hhpos.le
        set n : ℕ := ⌊(t - a) / h⌋₊ with hn
        have hgrid : t ∈ Icc (p n) (p (n + 1)) := by
          have hn_le : (n : ℝ) ≤ (t - a) / h := by
            have h := Nat.floor_le hx0; simpa [hn] using h
          have hn_lt : (t - a) / h < (n : ℝ) + 1 := by
            have h := Nat.lt_floor_add_one ((t - a) / h); simpa [hn] using h
          rw [mem_Icc, hp_apply, hp_apply]; push_cast
          constructor
          · have hA := mul_le_mul_of_nonneg_right hn_le hhpos.le
            rw [div_mul_cancel₀ _ (ne_of_gt hhpos)] at hA
            linarith
          · have hA := mul_lt_mul_of_pos_right hn_lt hhpos
            rw [div_mul_cancel₀ _ (ne_of_gt hhpos)] at hA
            linarith
        have hn6 : 6 ≤ n := by
          have hA : (6 : ℝ) ≤ (t - a) / h := by
            rw [le_div_iff₀ hhpos]
            have hB : p 6 = a + 6 * h := by rw [hp_apply]; push_cast; ring
            linarith
          simpa [hn] using Nat.le_floor hA
        have hnK : n ≤ K + 6 := by
          by_contra hcon
          have hKn : K + 7 ≤ n := by omega
          have hA : p (K + 7) ≤ p n := hp_mono hKn
          linarith [hgrid.1]
        refine ⟨n - 6, by omega, ?_⟩
        have hna : n - 6 + 6 = n := Nat.sub_add_cancel hn6
        have hnb : n - 6 + 7 = n + 1 := by omega
        rw [hna, hnb]
        exact hgrid
      have hcov : Icc a b \ goodWindowUnion starts d ⊆ (X ∪ Y ∪ D) ∪ Btr := by
        intro t ht
        obtain ⟨htab, htU⟩ := ht
        by_cases h1t : t ≤ p 6
        · exact Or.inl (Or.inl (Or.inl ⟨htab.1, h1t⟩))
        · have h1t' : p 6 < t := lt_of_not_ge h1t
          by_cases h2t : p (K + 7) ≤ t
          · exact Or.inl (Or.inl (Or.inr ⟨h2t, htab.2⟩))
          · have h2t' : t < p (K + 7) := lt_of_not_ge h2t
            obtain ⟨j, hjle, hjt⟩ := hfind t h1t'.le h2t'
            have hnj : ¬ good j := by
              intro hg
              have hspec := hwfun_spec j hg
              have hwmem : wfun j ∈ starts := by
                rw [hstarts]
                exact Finset.mem_image.mpr ⟨j,
                  Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (Nat.lt_succ_of_le hjle), hg⟩, rfl⟩
              have hwin : t ∈ Icc (wfun j + 5 * h) (wfun j + 7 * h) :=
                hcover j hjle (wfun j) hspec.1 hjt
              have hwin' : t ∈ Icc (wfun j + 5 * d / 8) (wfun j + 7 * d / 8) := by
                rw [h5, h7]; exact hwin
              exact htU ⟨wfun j, hwmem, hwin'⟩
            have hbj := hbad j hnj
            rcases lt_or_eq_of_le hjle with hlt | heq
            · refine Or.inr ?_
              rw [hBtr]
              have hmemcell : t - 6 * h ∈ cell j := by
                rw [hcell_lt j hlt, hp_succ j]
                rw [hp_add j 6, hp_add j 7] at hjt
                push_cast at hjt
                exact ⟨by linarith [hjt.1], by linarith [hjt.2]⟩
              exact ⟨t - 6 * h, hbj hmemcell, by ring⟩
            · subst heq
              rw [hp_add K 6, hp_add K 7] at hjt
              push_cast at hjt
              by_cases ht4 : t ≤ p K + r + 6 * h
              · refine Or.inr ?_
                rw [hBtr]
                have hmemcell : t - 6 * h ∈ cell K := by
                  rw [hcell_ge K le_rfl, hbd]
                  exact ⟨by linarith [hjt.1], by linarith [ht4]⟩
                exact ⟨t - 6 * h, hbj hmemcell, by ring⟩
              · have ht4' : p K + r + 6 * h < t := lt_of_not_ge ht4
                refine Or.inl (Or.inr ⟨?_, ?_⟩)
                · rw [hp_add K 6]; push_cast; linarith [ht4']
                · rw [hp_add K 7]; exact hjt.2
      have e1 : ENNReal.ofReal (6 * h) + ENNReal.ofReal (h + r) + ENNReal.ofReal (h - r)
          = ENNReal.ofReal d := by
        have h1 : ENNReal.ofReal (6 * h) + ENNReal.ofReal (h + r) =
            ENNReal.ofReal (6 * h + (h + r)) :=
          (ENNReal.ofReal_add (by positivity) (by linarith)).symm
        have h2 : ENNReal.ofReal (6 * h + (h + r)) + ENNReal.ofReal (h - r) =
            ENNReal.ofReal ((6 * h + (h + r)) + (h - r)) :=
          (ENNReal.ofReal_add (by linarith) (by linarith)).symm
        rw [h1, h2]
        have h3 : (6 * h + (h + r)) + (h - r) = d := by rw [← hdh]; ring
        rw [h3]
      calc volume (Icc a b \ goodWindowUnion starts d)
          ≤ volume ((X ∪ Y ∪ D) ∪ Btr) := measure_mono hcov
        _ ≤ volume (X ∪ Y ∪ D) + volume Btr := measure_union_le _ _
        _ ≤ (volume (X ∪ Y) + volume D) + volume Btr :=
            add_le_add (measure_union_le (X ∪ Y) D) le_rfl
        _ ≤ ((volume X + volume Y) + volume D) + volume Btr :=
            add_le_add (add_le_add (measure_union_le X Y) le_rfl) le_rfl
        _ ≤ ((ENNReal.ofReal (6 * h) + ENNReal.ofReal (h + r)) +
              ENNReal.ofReal (h - r)) + ENNReal.ofReal (C / threshold) := by
            refine add_le_add (add_le_add (add_le_add ?_ ?_) ?_) ?_
            · rw [hvX]
            · rw [hvY]
            · rw [hvD]
            · exact hvB
        _ = ENNReal.ofReal d + ENNReal.ofReal (C / threshold) := by rw [e1]
        _ = ENNReal.ofReal (d + C / threshold) := hof.symm
    · intro w hw t ht
      exact ⟨by linarith [hd, ht.1], by linarith [hd, ht.2]⟩

omit [SigmaCompactSpace Q] hCompact hConnected hBoundary in
theorem rfs_finite_good_windows_of_energy_input (B : RicciBackground (I := I) (M := Q) D a b)
    (L₀ Theta₀ : ℝ) (K : CurveShorteningRegularityInput B L₀ Theta₀)
    (E : CurveShorteningEnergyInput (I := I) (M := Q) (D := D) (a := a) (b := b) B L₀) :
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
  dsimp only [localRegularityDelta, localRegularityRadius, localRegularityCoefficient]
  intro ell threshold hell hth _hdlt lambda hlambda hlambda_one c hsol hramp hdeg hlen hcurv hlenlower
  set r : ℝ := min K.radius (min (ell / 2) (K.delta ^ 2 / threshold)) with hrdef
  set d : ℝ := K.delta * r ^ 2 with hddef
  have hdpos : 0 < d := by
    rw [hddef]
    exact mul_pos K.delta_pos (pow_pos (lt_min K.radius_pos
      (lt_min (half_pos hell) (div_pos (pow_pos K.delta_pos 2) hth))) 2)
  obtain ⟨hintE, hboundE⟩ := E.energy_product lambda hlambda hlambda_one b B.lt le_rfl
    (Icc a b) (Or.inr rfl) c hsol hlen a b le_rfl B.lt.le ⟨B.lt.le, le_rfl⟩
  have hEint : IntervalIntegrable (c.energy B.family.metric lambda) volume a b :=
    (intervalIntegrable_iff_integrableOn_Icc_of_le B.lt.le).mpr hintE
  have hEnn : ∀ t ∈ Icc a b, 0 ≤ c.energy B.family.metric lambda t :=
    fun t _ => productCurve_energy_nonneg c B.family.metric lambda t
  obtain ⟨starts, hmem, hsub, hvol, hwin⟩ :=
    exists_goodWindow_finset_of_energy_bound hdpos B.lt.le hEint hEnn hboundE hth
  refine ⟨starts, hmem, hsub, hvol, ?_, hwin⟩
  intro x t ht
  obtain ⟨w, hw, htw⟩ := ht
  obtain ⟨hwIcc, hwenergy⟩ := hmem w hw
  have hwIccab : w ∈ Icc a b := ⟨hwIcc.1, le_trans hwIcc.2 (by linarith [hdpos])⟩
  have hslice := E.slice_product lambda hlambda hlambda_one b B.lt le_rfl (Icc a b) (Or.inr rfl)
    c hsol hlen w hwIccab
  have hrpos : 0 < r := by
    rw [hrdef]
    exact lt_min K.radius_pos (lt_min (half_pos hell) (div_pos (pow_pos K.delta_pos 2) hth))
  have hrle : r ≤ K.radius := by rw [hrdef]; exact min_le_left _ _
  have hreth : r * threshold ≤ K.delta ^ 2 := by
    have h1 : r ≤ K.delta ^ 2 / threshold := by
      rw [hrdef]
      exact le_trans (min_le_right _ _) (min_le_right _ _)
    calc r * threshold ≤ (K.delta ^ 2 / threshold) * threshold :=
          mul_le_mul_of_nonneg_right h1 hth.le
      _ = K.delta ^ 2 := div_mul_cancel₀ _ hth.ne'
  have hwlen : r ≤ c.length B.family.metric lambda w := by
    have h1 : r ≤ ell / 2 := by
      rw [hrdef]
      exact le_trans (min_le_right _ _) (min_le_left _ _)
    exact le_trans (le_trans h1 (by linarith)) (hlenlower w hwIccab)
  have harc : ∀ p q : ℝ, p ≤ q → q ≤ p + 1 →
      c.arcLength B.family.metric lambda p q w = r →
      c.arcTotalCurvature B.family.metric lambda p q w ≤ K.delta := by
    intro p q hpq hqp hlen_eq
    obtain ⟨h1, h2⟩ := productCurve_arcTotalCurvature_le_sqrt B.family.metric lambda c
      hsol.smooth hsol.immersed p q w hpq hqp hwIccab (fun _ _ _ => hslice)
    calc c.arcTotalCurvature B.family.metric lambda p q w
        ≤ Real.sqrt (c.arcLength B.family.metric lambda p q w *
            c.arcEnergy B.family.metric lambda p q w) := h1
      _ = Real.sqrt (r * c.arcEnergy B.family.metric lambda p q w) := by rw [hlen_eq]
      _ ≤ Real.sqrt (r * threshold) :=
          Real.sqrt_le_sqrt (mul_le_mul_of_nonneg_left (h2.trans hwenergy) hrpos.le)
      _ ≤ K.delta := Real.sqrt_le_iff.2 ⟨K.delta_pos.le, hreth⟩
  have hwtmem : w ∈ Ico a b := ⟨hwIccab.1, lt_of_le_of_lt hwIcc.2 (by linarith [hdpos])⟩
  have htmem : t ∈ Icc a b :=
    ⟨by linarith [htw.1, hdpos, hwIcc.1], by linarith [htw.2, hdpos, hwIcc.2]⟩
  have hwt : w < t := by linarith [htw.1, hdpos]
  have htle : t ≤ w + K.delta * r ^ 2 := by
    rw [← hddef]
    linarith [htw.2, hdpos]
  have hkey := K.product lambda hlambda hlambda_one b B.lt le_rfl (Icc a b) (Or.inr rfl) c hsol
    hlen hcurv w hwtmem r hrpos hrle hwlen harc 0 x t htmem hwt htle
  have hbound : c.normSq B.family.metric lambda (c.curvatureVector B.family.metric lambda) x t ≤
      K.coefficient 0 * (t - w) ^ (-(1 : ℤ)) := by
    rw [productCurve_iteratedDs_zero] at hkey
    exact hkey
  exact productCurve_curvature_le_of_window B.family.metric lambda x t w (K.coefficient 0) d
    hdpos (K.coefficient_pos 0).le (by linarith [htw.1, hdpos]) hbound

omit [SigmaCompactSpace Q] hCompact hConnected hBoundary in
theorem rfs_finite_good_windows_of_energy_bound (B : RicciBackground (I := I) (M := Q) D a b)
    (L₀ Theta₀ : ℝ) (K : CurveShorteningRegularityInput B L₀ Theta₀)
    (henergy : ∀ (lambda : ℝ), 0 < lambda → lambda ≤ 1 → ∀ c : ProductCurve Q,
      c.IsSolutionOn B.family.metric lambda (Icc a b) →
      c.length B.family.metric lambda a ≤ L₀ →
      IntegrableOn (c.energy B.family.metric lambda) (Icc a b) ∧
        (∫ v in a..b, c.energy B.family.metric lambda v) ≤ Real.exp (B.B₀ * (b - a)) * L₀)
    (hslice : ∀ (lambda : ℝ), 0 < lambda → lambda ≤ 1 → ∀ c : ProductCurve Q,
      c.IsSolutionOn B.family.metric lambda (Icc a b) →
      c.length B.family.metric lambda a ≤ L₀ →
      ∀ t ∈ Icc a b, c.SliceRegularity B.family.metric lambda t) :
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
  dsimp only [localRegularityDelta, localRegularityRadius, localRegularityCoefficient]
  intro ell threshold hell hth _hdlt lambda hlambda hlambda_one c hsol hramp hdeg hlen hcurv hlenlower
  set r : ℝ := min K.radius (min (ell / 2) (K.delta ^ 2 / threshold)) with hrdef
  set d : ℝ := K.delta * r ^ 2 with hddef
  have hdpos : 0 < d := by
    rw [hddef]
    exact mul_pos K.delta_pos (pow_pos (lt_min K.radius_pos
      (lt_min (half_pos hell) (div_pos (pow_pos K.delta_pos 2) hth))) 2)
  obtain ⟨hintE, hboundE⟩ := henergy lambda hlambda hlambda_one c hsol hlen
  have hEint : IntervalIntegrable (c.energy B.family.metric lambda) volume a b :=
    (intervalIntegrable_iff_integrableOn_Icc_of_le B.lt.le).mpr hintE
  have hEnn : ∀ t ∈ Icc a b, 0 ≤ c.energy B.family.metric lambda t :=
    fun t _ => productCurve_energy_nonneg c B.family.metric lambda t
  obtain ⟨starts, hmem, hsub, hvol, hwin⟩ :=
    exists_goodWindow_finset_of_energy_bound hdpos B.lt.le hEint hEnn hboundE hth
  refine ⟨starts, hmem, hsub, hvol, ?_, hwin⟩
  intro x t ht
  obtain ⟨w, hw, htw⟩ := ht
  obtain ⟨hwIcc, hwenergy⟩ := hmem w hw
  have hwIccab : w ∈ Icc a b := ⟨hwIcc.1, le_trans hwIcc.2 (by linarith [hdpos])⟩
  have hslice_w := hslice lambda hlambda hlambda_one c hsol hlen w hwIccab
  have hrpos : 0 < r := by
    rw [hrdef]
    exact lt_min K.radius_pos (lt_min (half_pos hell) (div_pos (pow_pos K.delta_pos 2) hth))
  have hrle : r ≤ K.radius := by rw [hrdef]; exact min_le_left _ _
  have hreth : r * threshold ≤ K.delta ^ 2 := by
    have h1 : r ≤ K.delta ^ 2 / threshold := by
      rw [hrdef]
      exact le_trans (min_le_right _ _) (min_le_right _ _)
    calc r * threshold ≤ (K.delta ^ 2 / threshold) * threshold :=
          mul_le_mul_of_nonneg_right h1 hth.le
      _ = K.delta ^ 2 := div_mul_cancel₀ _ hth.ne'
  have hwlen : r ≤ c.length B.family.metric lambda w := by
    have h1 : r ≤ ell / 2 := by
      rw [hrdef]
      exact le_trans (min_le_right _ _) (min_le_left _ _)
    exact le_trans (le_trans h1 (by linarith)) (hlenlower w hwIccab)
  have harc : ∀ p q : ℝ, p ≤ q → q ≤ p + 1 →
      c.arcLength B.family.metric lambda p q w = r →
      c.arcTotalCurvature B.family.metric lambda p q w ≤ K.delta := by
    intro p q hpq hqp hlen_eq
    obtain ⟨h1, h2⟩ := productCurve_arcTotalCurvature_le_sqrt B.family.metric lambda c
      hsol.smooth hsol.immersed p q w hpq hqp hwIccab (fun _ _ _ => hslice_w)
    calc c.arcTotalCurvature B.family.metric lambda p q w
        ≤ Real.sqrt (c.arcLength B.family.metric lambda p q w *
            c.arcEnergy B.family.metric lambda p q w) := h1
      _ = Real.sqrt (r * c.arcEnergy B.family.metric lambda p q w) := by rw [hlen_eq]
      _ ≤ Real.sqrt (r * threshold) :=
          Real.sqrt_le_sqrt (mul_le_mul_of_nonneg_left (h2.trans hwenergy) hrpos.le)
      _ ≤ K.delta := Real.sqrt_le_iff.2 ⟨K.delta_pos.le, hreth⟩
  have hwtmem : w ∈ Ico a b := ⟨hwIccab.1, lt_of_le_of_lt hwIcc.2 (by linarith [hdpos])⟩
  have htmem : t ∈ Icc a b :=
    ⟨by linarith [htw.1, hdpos, hwIcc.1], by linarith [htw.2, hdpos, hwIcc.2]⟩
  have hwt : w < t := by linarith [htw.1, hdpos]
  have htle : t ≤ w + K.delta * r ^ 2 := by
    rw [← hddef]
    linarith [htw.2, hdpos]
  have hkey := K.product lambda hlambda hlambda_one b B.lt le_rfl (Icc a b) (Or.inr rfl) c hsol
    hlen hcurv w hwtmem r hrpos hrle hwlen harc 0 x t htmem hwt htle
  have hbound : c.normSq B.family.metric lambda (c.curvatureVector B.family.metric lambda) x t ≤
      K.coefficient 0 * (t - w) ^ (-(1 : ℤ)) := by
    rw [productCurve_iteratedDs_zero] at hkey
    exact hkey
  exact productCurve_curvature_le_of_window B.family.metric lambda x t w (K.coefficient 0) d
    hdpos (K.coefficient_pos 0).le (by linarith [htw.1, hdpos]) hbound



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
