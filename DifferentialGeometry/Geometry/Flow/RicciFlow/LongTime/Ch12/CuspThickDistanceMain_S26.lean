import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch12.CuspThickDistanceWindow_S26
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch12.CuspThickDistanceVolume_S26
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch12.CuspThickDistanceDist_S26
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch12.CuspThickDistanceRadius_S26

set_option autoImplicit false
noncomputable section
open Set Function Manifold DifferentialGeometry DifferentialGeometry.Geometry
  DifferentialGeometry.Geometry.Hyperbolic DifferentialGeometry.Geometry.Collapse
open DifferentialGeometry.Integral.Measure MeasureTheory
open scoped Manifold ContDiff ENNReal
universe u
namespace GC.LongTime.Ch12

variable {H : FiniteVolumeHyperbolicModel.{u}}

/-- Deep cusp points: the window bound turns thickness into a depth bound. -/
theorem height_le_of_thick_S26 (T : HyperbolicTruncation H) (i : Fin T.count) {A : ℝ} (hA : 0 ≤ A)
    (hvol : ∀ a b : ℝ, 0 ≤ a → a ≤ b → riemannianVolumeMeasure (𝓡 3) H.Carrier H.metric
      (T.cuspMap i '' {q : CuspHalfSpace | a < q.2.val 0 ∧ q.2.val 0 < b}) ≤
        ENNReal.ofReal (A * Real.exp (-a) * (b - a)))
    (q : CuspHalfSpace) (hq : 3 < q.2.val 0) {w : ℝ} (hw : 0 < w)
    (hth : ENNReal.ofReal w ≤ ballVolume H.metric (T.cuspMap i q) 2) :
    q.2.val 0 ≤ 2 + Real.log (4 * A + 1) + Real.log (1 / w) := by
  set h := q.2.val 0 with hh
  have hball := ball_subset_window_S26 T i q (r := 2) (by norm_num) (by linarith)
  have hsub : riemannianBallOf H.metric (T.cuspMap i q) 2 ⊆
      T.cuspMap i '' {q' : CuspHalfSpace | h - 2 < q'.2.val 0 ∧ q'.2.val 0 < h + 2} := by
    refine hball.trans (image_mono fun q' hq' => ?_)
    have := abs_lt.mp (show |q'.2.val 0 - h| < 2 from hq')
    exact ⟨by linarith [this.1], by linarith [this.2]⟩
  have h1 : ENNReal.ofReal w ≤ ENNReal.ofReal (A * Real.exp (-(h - 2)) * (h + 2 - (h - 2))) :=
    hth.trans ((measure_mono hsub).trans (hvol (h - 2) (h + 2) (by linarith) (by linarith)))
  have h2 : w ≤ A * Real.exp (-(h - 2)) * (h + 2 - (h - 2)) :=
    (ENNReal.ofReal_le_ofReal_iff (by have := Real.exp_pos (-(h-2)); nlinarith)).mp h1
  have h3 : w ≤ 4 * A * Real.exp (-(h - 2)) := by nlinarith
  have hApos : 0 < A := by
    by_contra hne
    have : A = 0 := le_antisymm (not_lt.mp hne) hA
    rw [this] at h3
    linarith
  have h4 : Real.exp (h - 2) ≤ 4 * A / w := by
    rw [le_div_iff₀ hw]
    have : Real.exp (h - 2) * Real.exp (-(h - 2)) = 1 := by rw [← Real.exp_add]; simp
    nlinarith [Real.exp_pos (h - 2), Real.exp_pos (-(h - 2))]
  have h5 : h - 2 ≤ Real.log (4 * A / w) := (Real.le_log_iff_exp_le (by positivity)).mpr h4
  have h6 : Real.log (4 * A / w) = Real.log (4 * A) + Real.log (1 / w) := by
    rw [show 4 * A / w = 4 * A * (1 / w) by ring, Real.log_mul (by positivity) (by positivity)]
  have h7 : Real.log (4 * A) ≤ Real.log (4 * A + 1) :=
    Real.log_le_log (by positivity) (by linarith)
  linarith

/-- **HPI07, logarithmic form.** -/
theorem hpi07_log_bound_S26 (T : HyperbolicTruncation H) (x : H.Carrier) :
    ∃ C₀ C₁ : ℝ, 0 ≤ C₀ ∧ 0 ≤ C₁ ∧ ∀ w : ℝ, 0 < w → w ≤ 1 → ∀ y : H.Carrier,
      ENNReal.ofReal w ≤ ballVolume H.metric y 2 →
      riemannianEDistOf H.metric x y ≤ ENNReal.ofReal (C₀ + C₁ * Real.log (1 / w)) := by
  obtain ⟨D0, hD0⟩ := exists_edist_core_le_S26 T x
  have hV : ∀ i : Fin T.count, ∃ A : ℝ, 0 ≤ A ∧ ∀ a b : ℝ, 0 ≤ a → a ≤ b →
      riemannianVolumeMeasure (𝓡 3) H.Carrier H.metric
        (T.cuspMap i '' {q : CuspHalfSpace | a < q.2.val 0 ∧ q.2.val 0 < b}) ≤
        ENNReal.ofReal (A * Real.exp (-a) * (b - a)) := fun i => cusp_window_volume_le_S26 T i
  have hDd : ∀ i : Fin T.count, ∃ D : ℝ, 0 ≤ D ∧ ∀ q : CuspHalfSpace,
      riemannianEDistOf H.metric x (T.cuspMap i q) ≤ ENNReal.ofReal (D + q.2.val 0) :=
    fun i => exists_edist_cusp_le_S26 T x i
  choose A hA hAv using hV
  choose D hD hDv using hDd
  set As : ℝ := ∑ i, A i with hAs
  set Ds : ℝ := ∑ i, D i with hDs
  have hAs0 : 0 ≤ As := Finset.sum_nonneg fun i _ => hA i
  have hDs0 : 0 ≤ Ds := Finset.sum_nonneg fun i _ => hD i
  have hAle : ∀ i, A i ≤ As := fun i =>
    Finset.single_le_sum (f := A) (fun j _ => hA j) (Finset.mem_univ i)
  have hDle : ∀ i, D i ≤ Ds := fun i =>
    Finset.single_le_sum (f := D) (fun j _ => hD j) (Finset.mem_univ i)
  have hlogA : 0 ≤ Real.log (4 * As + 1) := Real.log_nonneg (by linarith)
  refine ⟨max D0 0 + Ds + 5 + Real.log (4 * As + 1), 1, by positivity, zero_le_one,
    fun w hw hw1 y hth => ?_⟩
  have hlw : 0 ≤ Real.log (1 / w) := Real.log_nonneg (by rw [le_div_iff₀ hw]; linarith)
  have hfin : ∀ X : ℝ, X ≤ max D0 0 + Ds + 5 + Real.log (4 * As + 1) + 1 * Real.log (1 / w) →
      ENNReal.ofReal X ≤ ENNReal.ofReal (max D0 0 + Ds + 5 + Real.log (4 * As + 1) +
        1 * Real.log (1 / w)) := fun X hX => ENNReal.ofReal_le_ofReal hX
  rcases (Set.ext_iff.mp T.exhausts y).mpr (mem_univ y) with hy | hy
  · refine (hD0 y hy).trans (hfin _ ?_)
    have := le_max_left D0 0
    linarith
  · obtain ⟨i, ⟨q, rfl⟩⟩ := mem_iUnion.mp hy
    refine (hDv i q).trans (hfin _ ?_)
    rcases le_or_gt (q.2.val 0) 3 with h3 | h3
    · have := hDle i
      have := le_max_right D0 0
      linarith
    · have hb := height_le_of_thick_S26 T i (hA i) (hAv i) q h3 hw hth
      have hl : Real.log (4 * A i + 1) ≤ Real.log (4 * As + 1) :=
        Real.log_le_log (by have := hA i; positivity) (by linarith [hAle i])
      have := hDle i
      have := le_max_right D0 0
      linarith

/-- **HPI07, matching radius.** `Θ_H(y) ≥ w/2` (i.e. `vol B(y,2) ≥ 4w`) forces `d(x,y) < 1/(2w)`. -/
theorem hpi07_matching_radius_S26 (T : HyperbolicTruncation H) (x : H.Carrier) :
    ∃ w₀ : ℝ, 0 < w₀ ∧ ∀ w : ℝ, 0 < w → w ≤ w₀ → ∀ y : H.Carrier,
      ENNReal.ofReal (4 * w) ≤ ballVolume H.metric y 2 →
      y ∈ riemannianBallOf H.metric x (1 / (2 * w)) := by
  obtain ⟨C₀, C₁, hC₀, hC₁, hmain⟩ := hpi07_log_bound_S26 T x
  set K : ℝ := 4 * (C₁ + 1) with hK
  have hK0 : 0 < K := by rw [hK]; positivity
  set u₀ : ℝ := 4 + 4 * (C₀ + C₁ * |Real.log K|) with hu₀
  have hu₀4 : 4 ≤ u₀ := by
    rw [hu₀]
    have h1 : 0 ≤ C₁ * |Real.log K| := mul_nonneg hC₁ (abs_nonneg _)
    linarith
  refine ⟨1 / u₀, by positivity, fun w hw hwle y hth => ?_⟩
  have hu : u₀ ≤ 1 / w := by
    rw [le_div_iff₀ hw]
    have := (le_div_iff₀ (by linarith : (0:ℝ) < u₀)).mp hwle
    linarith
  have hw4 : 4 * w ≤ 1 := by
    have : w ≤ 1 / 4 := hwle.trans (by rw [div_le_div_iff₀ (by linarith) (by norm_num)]; linarith)
    linarith
  have hd := hmain (4 * w) (by positivity) hw4 y hth
  set u : ℝ := 1 / w with hudef
  have hu0 : 0 < u := by rw [hudef]; positivity
  have hlog : Real.log (1 / (4 * w)) ≤ Real.log u :=
    Real.log_le_log (by positivity) (by rw [hudef]; rw [div_le_div_iff₀ (by positivity) hw]; linarith)
  have hKl : Real.log u ≤ u / K - 1 + Real.log K := by
    have := Real.log_le_sub_one_of_pos (div_pos hu0 hK0)
    rw [Real.log_div hu0.ne' hK0.ne'] at this
    linarith
  have hC1K : C₁ / K ≤ 1 / 4 := by
    rw [div_le_iff₀ hK0, hK]; nlinarith
  have hkey : C₀ + C₁ * Real.log (1 / (4 * w)) < 1 / (2 * w) := by
    have hlogK := le_abs_self (Real.log K)
    have h1 : C₁ * Real.log (1 / (4 * w)) ≤ C₁ * (u / K - 1 + Real.log K) :=
      mul_le_mul_of_nonneg_left (hlog.trans hKl) hC₁
    have h2 : C₁ * (u / K) ≤ u / 4 := by
      have : C₁ * (u / K) = (C₁ / K) * u := by ring
      rw [this]; nlinarith
    have h3 : C₁ * Real.log K ≤ C₁ * |Real.log K| := mul_le_mul_of_nonneg_left hlogK hC₁
    have h4 : 1 / (2 * w) = u / 2 := by rw [hudef]; field_simp
    rw [h4]
    nlinarith
  change riemannianEDistOf H.metric x y < ENNReal.ofReal (1 / (2 * w))
  exact lt_of_le_of_lt hd ((ENNReal.ofReal_lt_ofReal_iff (by positivity)).mpr hkey)

/-- **HPI07, thick form.** For `w`-thick points (`curvatureRadius = r`, `vol B(y,r) ≥ w r³`). -/
theorem hpi07_thick_S26 (T : HyperbolicTruncation H) (x : H.Carrier) :
    ∃ w₀ : ℝ, 0 < w₀ ∧ ∀ w : ℝ, 0 < w → w ≤ w₀ → ∀ (y : H.Carrier) (r : ℝ), 0 < r →
      curvatureRadius H.metric y = ENNReal.ofReal r →
      ENNReal.ofReal (w * r ^ 3) ≤ ballVolume H.metric y r →
      y ∈ riemannianBallOf H.metric x (1 / (2 * w)) := by
  obtain ⟨w₀, hw₀, h⟩ := hpi07_matching_radius_S26 T x
  refine ⟨w₀, hw₀, fun w hw hwle y r hr hcr hth => h w hw hwle y ?_⟩
  rw [curvatureRadius_eq_two_S26 H y] at hcr
  have hr2 : r = 2 := ((ENNReal.ofReal_eq_ofReal_iff hr.le (by norm_num)).mp hcr.symm)
  subst hr2
  refine le_trans (ENNReal.ofReal_le_ofReal ?_) hth
  nlinarith

end GC.LongTime.Ch12
