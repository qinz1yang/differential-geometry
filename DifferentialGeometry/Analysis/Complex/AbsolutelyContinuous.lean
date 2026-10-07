import DifferentialGeometry.Analysis.Complex.DiskPacking
import DifferentialGeometry.Analysis.Integration.Measure.ComplexImageStrip
import Mathlib.MeasureTheory.Function.AbsolutelyContinuous
import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.Floor.Ring

namespace Homeomorph

private theorem horizontal_dist (u v y : ℝ) :
    dist (⟨u, y⟩ : ℂ) (⟨v, y⟩ : ℂ) = |u - v| := by
  rw [dist_eq_norm]
  have he : (⟨u, y⟩ : ℂ) - (⟨v, y⟩ : ℂ) = ((u - v : ℝ) : ℂ) := by
    apply Complex.ext <;> simp
  rw [he, Complex.norm_real, Real.norm_eq_abs]

private theorem diameter_ball_coordinates {l u y : ℝ} {z : ℂ}
    (hz : z ∈ Metric.ball (⟨(l + u) / 2, y⟩ : ℂ) ((u - l) / 2)) :
    z.re ∈ Set.Ioo l u ∧ |z.im - y| < (u - l) / 2 := by
  have hr := (Complex.abs_re_le_norm (z - (⟨(l + u) / 2, y⟩ : ℂ))).trans_lt
    (by simpa only [Metric.mem_ball, dist_eq_norm] using hz)
  have hi := (Complex.abs_im_le_norm (z - (⟨(l + u) / 2, y⟩ : ℂ))).trans_lt
    (by simpa only [Metric.mem_ball, dist_eq_norm] using hz)
  change |z.re - (l + u) / 2| < (u - l) / 2 at hr
  change |z.im - y| < (u - l) / 2 at hi
  refine ⟨?_, hi⟩
  have hh := abs_lt.mp hr
  constructor <;> linarith [hh.1, hh.2]

private theorem exists_mesh {ι : Type*} (s : Finset ι) (l : ι → ℝ)
    (hl : ∀ i ∈ s, 0 < l i) {δ : ℝ} (hδ : 0 < δ) :
    ∃ ε : ℝ, 0 < ε ∧ ε < δ ∧ ε < 1 ∧ ∀ i ∈ s, ε ≤ l i := by
  classical
  induction s using Finset.induction_on with
  | empty =>
      refine ⟨min δ 1 / 2, by positivity, ?_, ?_, by simp⟩
      · have h := min_le_left δ 1
        have hp : 0 < min δ 1 := lt_min hδ zero_lt_one
        linarith
      · have h := min_le_right δ 1
        have hp : 0 < min δ 1 := lt_min hδ zero_lt_one
        linarith
  | @insert i s his ih =>
      obtain ⟨ε, hε, hεδ, hε1, hεl⟩ := ih (fun j hj => hl j (Finset.mem_insert_of_mem hj))
      refine ⟨min ε (l i), lt_min hε (hl i (Finset.mem_insert_self _ _)),
        (min_le_left _ _).trans_lt hεδ, (min_le_left _ _).trans_lt hε1, ?_⟩
      intro j hj
      rcases Finset.mem_insert.mp hj with rfl | hj
      · exact min_le_right _ _
      · exact (min_le_left _ _).trans (hεl j hj)

private theorem comparable_horizontal_oscillation_le
    {ι : Type*} (h : ℂ ≃ₜ ℂ) (s : Finset ι) (l u : ι → ℝ)
    (a b y N ε κ : ℝ) (hN : 0 < N) (hε : 0 < ε)
    (hl : ∀ i ∈ s, a ≤ l i) (hu : ∀ i ∈ s, u i ≤ b)
    (hgap : ∀ i ∈ s, ε / 2 ≤ u i - l i ∧ u i - l i ≤ ε)
    (hdisj : (s : Set ι).PairwiseDisjoint (fun i => Set.Ioc (l i) (u i)))
    (hdisks : ∀ z : ℂ, ∀ r : ℝ, 0 < r → ∃ ρ R : ℝ, 0 < ρ ∧
      Metric.closedBall (h z) ρ ⊆ h '' Metric.ball z r ∧
      h '' Metric.closedBall z r ⊆ Metric.closedBall (h z) R ∧ R ≤ κ * ρ)
    (hstrip : MeasureTheory.volume
      (h '' {z : ℂ | z.re ∈ Set.Icc (a - 1) (b + 1) ∧
        z.im ∈ Set.Icc (y - ε) (y + ε)}) ≤ ENNReal.ofReal (2 * N * ε)) :
    (∑ i ∈ s, dist (h (⟨l i, y⟩ : ℂ)) (h (⟨u i, y⟩ : ℂ))) ^ 2 ≤
      (16 * κ ^ 2 * N / Real.pi) * ∑ i ∈ s, (u i - l i) := by
  classical
  let centers (i : ι) : ℂ := ⟨(l i + u i) / 2, y⟩
  let radii (i : ι) := (u i - l i) / 2
  let K : Set ℂ := {z | z.re ∈ Set.Icc (a - 1) (b + 1) ∧
    z.im ∈ Set.Icc (y - ε) (y + ε)}
  have hK : IsCompact K :=
    (isCompact_Icc : IsCompact (Set.Icc (a - 1) (b + 1))).reProdIm isCompact_Icc
  have hpos (i : ι) (hi : i ∈ s) : 0 < radii i := by
    have hh := (hgap i hi).1
    dsimp [radii]
    linarith
  have hballs : (s : Set ι).PairwiseDisjoint (fun i => Metric.ball (centers i) (radii i)) := by
    intro i hi j hj hij
    apply Set.disjoint_left.mpr
    intro z hzi hzj
    have hri := (diameter_ball_coordinates hzi).1
    have hrj := (diameter_ball_coordinates hzj).1
    exact Set.disjoint_left.mp (hdisj hi hj hij) ⟨hri.1, hri.2.le⟩ ⟨hrj.1, hrj.2.le⟩
  have hcontains (i : ι) (hi : i ∈ s) : Metric.ball (centers i) (radii i) ⊆ K := by
    intro z hz
    obtain ⟨hr, him⟩ := diameter_ball_coordinates hz
    have him' := abs_lt.mp him
    have hlength := (hgap i hi).2
    change (a - 1 ≤ z.re ∧ z.re ≤ b + 1) ∧ (y - ε ≤ z.im ∧ z.im ≤ y + ε)
    constructor
    · constructor <;> linarith [hl i hi, hu i hi, hr.1, hr.2]
    · constructor <;> linarith [him'.1, him'.2]
  have hleft (i : ι) (hi : i ∈ s) : (⟨l i, y⟩ : ℂ) ∈ Metric.closedBall (centers i) (radii i) := by
    rw [Metric.mem_closedBall]
    change dist (⟨l i, y⟩ : ℂ) (⟨(l i + u i) / 2, y⟩ : ℂ) ≤ radii i
    rw [horizontal_dist]
    have hh := (hgap i hi).1
    rw [abs_of_nonpos (by linarith)]
    dsimp [radii]
    linarith
  have hright (i : ι) (hi : i ∈ s) : (⟨u i, y⟩ : ℂ) ∈ Metric.closedBall (centers i) (radii i) := by
    rw [Metric.mem_closedBall]
    change dist (⟨u i, y⟩ : ℂ) (⟨(l i + u i) / 2, y⟩ : ℂ) ≤ radii i
    rw [horizontal_dist]
    have hh := (hgap i hi).1
    rw [abs_of_nonneg (by linarith)]
    dsimp [radii]
    linarith
  have hpack := h.sum_sq_dist_apply_le_volume_image s centers
    (fun i => (⟨l i, y⟩ : ℂ)) (fun i => (⟨u i, y⟩ : ℂ)) radii hK
    hballs hcontains hleft hright (fun i hi => hdisks _ _ (hpos i hi))
  have harea : (MeasureTheory.volume (h '' K)).toReal ≤ 2 * N * ε := by
    have h := ENNReal.toReal_mono ENNReal.ofReal_ne_top hstrip
    simpa only [ENNReal.toReal_ofReal (by positivity : 0 ≤ 2 * N * ε)] using h
  let osc (i : ι) := dist (h (⟨l i, y⟩ : ℂ)) (h (⟨u i, y⟩ : ℂ))
  have hsq : ∑ i ∈ s, osc i ^ 2 ≤ (8 * κ ^ 2 * N / Real.pi) * ε := by
    calc
      _ ≤ (4 * κ ^ 2 / Real.pi) * (MeasureTheory.volume (h '' K)).toReal := hpack
      _ ≤ (4 * κ ^ 2 / Real.pi) * (2 * N * ε) :=
        mul_le_mul_of_nonneg_left harea (by positivity)
      _ = _ := by ring
  have hcount : (s.card : ℝ) * ε ≤ 2 * ∑ i ∈ s, (u i - l i) := by
    have hh := Finset.sum_le_sum (s := s) (fun i hi => (hgap i hi).1)
    simp only [Finset.sum_const, nsmul_eq_mul] at hh
    linarith
  have hcs : (∑ i ∈ s, osc i) ^ 2 ≤ (s.card : ℝ) * ∑ i ∈ s, osc i ^ 2 := by
    simpa only [one_mul, one_pow, Finset.sum_const, nsmul_eq_mul, mul_one] using
      Finset.sum_mul_sq_le_sq_mul_sq s (fun _ => (1 : ℝ)) osc
  calc
    _ ≤ (s.card : ℝ) * ∑ i ∈ s, osc i ^ 2 := hcs
    _ ≤ (s.card : ℝ) * ((8 * κ ^ 2 * N / Real.pi) * ε) :=
      mul_le_mul_of_nonneg_left hsq (Nat.cast_nonneg _)
    _ = (8 * κ ^ 2 * N / Real.pi) * ((s.card : ℝ) * ε) := by ring
    _ ≤ (8 * κ ^ 2 * N / Real.pi) * (2 * ∑ i ∈ s, (u i - l i)) :=
      mul_le_mul_of_nonneg_left hcount (by positivity)
    _ = _ := by ring

private theorem sq_sum_dist_horizontal_le_of_image_strip_bound
    (h : ℂ ≃ₜ ℂ) (κ : ℝ)
    (hdisks : ∀ z : ℂ, ∀ r : ℝ, 0 < r → ∃ ρ R : ℝ, 0 < ρ ∧
      Metric.closedBall (h z) ρ ⊆ h '' Metric.ball z r ∧
      h '' Metric.closedBall z r ⊆ Metric.closedBall (h z) R ∧ R ≤ κ * ρ)
    (a b y N δ : ℝ) (hab : a ≤ b) (hN : 0 < N) (hδ : 0 < δ)
    (hstrip : ∀ ε : ℝ, 0 < ε → ε < δ → MeasureTheory.volume
      (h '' {z : ℂ | z.re ∈ Set.Icc (a - 1) (b + 1) ∧
        z.im ∈ Set.Icc (y - ε) (y + ε)}) ≤ ENNReal.ofReal (2 * N * ε))
    (P : ℕ × (ℕ → ℝ × ℝ)) (hP : P ∈ AbsolutelyContinuousOnInterval.disjWithin a b) :
    (∑ i ∈ Finset.range P.1,
      dist (h (⟨(P.2 i).1, y⟩ : ℂ)) (h (⟨(P.2 i).2, y⟩ : ℂ))) ^ 2 ≤
      (16 * κ ^ 2 * N / Real.pi) *
        ∑ i ∈ Finset.range P.1, dist (P.2 i).1 (P.2 i).2 := by
  classical
  let l (i : ℕ) := min (P.2 i).1 (P.2 i).2
  let u (i : ℕ) := max (P.2 i).1 (P.2 i).2
  let S := (Finset.range P.1).filter (fun i => l i < u i)
  have hmem {i : ℕ} (hi : i ∈ S) : i ∈ Finset.range P.1 ∧ l i < u i := Finset.mem_filter.mp hi
  have hlength (i : ℕ) : u i - l i = dist (P.2 i).1 (P.2 i).2 := by
    simpa only [u, l, Real.dist_eq, max_sub_min_eq_abs] using abs_sub_comm (P.2 i).2 (P.2 i).1
  have hoscnorm (i : ℕ) :
      dist (h (⟨l i, y⟩ : ℂ)) (h (⟨u i, y⟩ : ℂ)) =
        dist (h (⟨(P.2 i).1, y⟩ : ℂ)) (h (⟨(P.2 i).2, y⟩ : ℂ)) := by
    rcases le_total (P.2 i).1 (P.2 i).2 with hi | hi
    · simp only [l, u, min_eq_left hi, max_eq_right hi]
    · simp only [l, u, min_eq_right hi, max_eq_left hi, dist_comm]
  have hzero (i : ℕ) (hi : ¬l i < u i) : (P.2 i).1 = (P.2 i).2 := by
    have hmin : l i ≤ (P.2 i).1 := min_le_left _ _
    have hmin' : l i ≤ (P.2 i).2 := min_le_right _ _
    have hmax : (P.2 i).1 ≤ u i := le_max_left _ _
    have hmax' : (P.2 i).2 ≤ u i := le_max_right _ _
    have hh := le_of_not_gt hi
    linarith
  have hsumLength : ∑ i ∈ S, (u i - l i) =
      ∑ i ∈ Finset.range P.1, dist (P.2 i).1 (P.2 i).2 := by
    rw [Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro i hi
    by_cases hlt : l i < u i
    · simp only [hlt, ite_true, hlength]
    · simp only [hlt, ite_false, hzero i hlt, dist_self]
  have hsumOsc : ∑ i ∈ S, dist (h (⟨l i, y⟩ : ℂ)) (h (⟨u i, y⟩ : ℂ)) =
      ∑ i ∈ Finset.range P.1, dist (h (⟨(P.2 i).1, y⟩ : ℂ))
        (h (⟨(P.2 i).2, y⟩ : ℂ)) := by
    rw [Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro i hi
    by_cases hlt : l i < u i
    · simp only [hlt, ite_true, hoscnorm]
    · simp only [hlt, ite_false, hzero i hlt, dist_self]
  obtain ⟨ε, hε, hεδ, _, hεlength⟩ := exists_mesh S (fun i => u i - l i)
    (fun i hi => sub_pos.mpr (hmem hi).2) hδ
  let n (i : ℕ) := ⌈(u i - l i) / ε⌉₊
  let Δ (i : ℕ) := (u i - l i) / n i
  let p (i j : ℕ) := l i + j * Δ i
  have hnpos (i : ℕ) (hi : i ∈ S) : 0 < n i :=
    Nat.ceil_pos.mpr (div_pos (sub_pos.mpr (hmem hi).2) hε)
  have hnreal (i : ℕ) (hi : i ∈ S) : 0 < (n i : ℝ) := by exact_mod_cast hnpos i hi
  have hnΔ (i : ℕ) (hi : i ∈ S) : (n i : ℝ) * Δ i = u i - l i := by
    dsimp only [Δ]
    field_simp [(hnreal i hi).ne']
  have hΔ (i : ℕ) (hi : i ∈ S) : ε / 2 ≤ Δ i ∧ Δ i ≤ ε := by
    have hlo : (u i - l i) / ε ≤ (n i : ℝ) := Nat.le_ceil _
    have hhi : (n i : ℝ) ≤ (u i - l i) / ε + 1 :=
      (Nat.ceil_lt_add_one (div_nonneg (sub_nonneg.mpr (hmem hi).2.le) hε.le)).le
    have h1 : 1 ≤ (u i - l i) / ε := (le_div_iff₀ hε).mpr (by simpa using hεlength i hi)
    have hhigh : (n i : ℝ) ≤ 2 * ((u i - l i) / ε) := by linarith
    have hmul : (n i : ℝ) * ε ≤ 2 * (u i - l i) :=
      (le_div_iff₀ hε).mp (by simpa only [mul_div_assoc] using hhigh)
    have hlow := (div_le_iff₀ hε).mp hlo
    have heq := hnΔ i hi
    constructor <;> nlinarith
  have hΔpos (i : ℕ) (hi : i ∈ S) : 0 < Δ i := lt_of_lt_of_le (by positivity) (hΔ i hi).1
  have hp0 (i : ℕ) : p i 0 = l i := by simp [p]
  have hpn (i : ℕ) (hi : i ∈ S) : p i (n i) = u i := by dsimp [p]; linarith [hnΔ i hi]
  have hpdiff (i j : ℕ) : p i (j + 1) - p i j = Δ i := by dsimp [p]; push_cast; ring
  have hpbetween (i j : ℕ) (hi : i ∈ S) (hj : j ≤ n i) : p i j ∈ Set.Icc (l i) (u i) := by
    have hmul := mul_le_mul_of_nonneg_right (show (j : ℝ) ≤ n i by exact_mod_cast hj) (hΔpos i hi).le
    have hnonneg : 0 ≤ (j : ℝ) * Δ i := mul_nonneg (Nat.cast_nonneg j) (hΔpos i hi).le
    dsimp [p]
    constructor <;> linarith [hnΔ i hi]
  let T : Finset (Σ _ : ℕ, ℕ) := S.sigma (fun i => Finset.range (n i))
  let A (v : Σ _ : ℕ, ℕ) := p v.1 v.2
  let B (v : Σ _ : ℕ, ℕ) := p v.1 (v.2 + 1)
  have htmem {v : Σ _ : ℕ, ℕ} (hv : v ∈ T) : v.1 ∈ S ∧ v.2 < n v.1 := by
    simpa only [T, Finset.mem_sigma, Finset.mem_range] using hv
  have hdomain (i : ℕ) (hi : i ∈ S) : a ≤ l i ∧ u i ≤ b := by
    have hh := hP.1 i (hmem hi).1
    rw [Set.uIcc_of_le hab] at hh
    dsimp [l, u]
    exact ⟨le_min hh.1.1 hh.2.1, max_le hh.1.2 hh.2.2⟩
  have hdisj : (T : Set (Σ _ : ℕ, ℕ)).PairwiseDisjoint (fun v => Set.Ioc (A v) (B v)) := by
    intro v hv w hw hvw
    obtain ⟨hvi, hvj⟩ := htmem hv
    obtain ⟨hwi, hwj⟩ := htmem hw
    by_cases hparent : v.1 = w.1
    · apply Set.disjoint_left.mpr
      intro z hzv hzw
      have hindex : v.2 ≠ w.2 := by
        intro heq
        apply hvw
        cases v
        cases w
        cases hparent
        cases heq
        rfl
      rcases lt_or_gt_of_ne hindex with hj | hj
      · have hle : B v ≤ A w := by
          have hm := mul_le_mul_of_nonneg_right
            (show ((v.2 + 1 : ℕ) : ℝ) ≤ w.2 by exact_mod_cast hj) (hΔpos w.1 hwi).le
          dsimp [A, B, p]
          rw [hparent]
          linarith
        linarith [hzv.2, hzw.1]
      · have hle : B w ≤ A v := by
          have hm := mul_le_mul_of_nonneg_right
            (show ((w.2 + 1 : ℕ) : ℝ) ≤ v.2 by exact_mod_cast hj) (hΔpos v.1 hvi).le
          dsimp [A, B, p]
          rw [← hparent]
          linarith
        linarith [hzw.2, hzv.1]
    · have hold := hP.2 (hmem hvi).1 (hmem hwi).1 hparent
      change Disjoint (Set.Ioc (l v.1) (u v.1)) (Set.Ioc (l w.1) (u w.1)) at hold
      apply hold.mono
      · intro z hz
        exact ⟨lt_of_le_of_lt (hpbetween v.1 v.2 hvi hvj.le).1 hz.1,
          hz.2.trans (hpbetween v.1 (v.2 + 1) hvi hvj).2⟩
      · intro z hz
        exact ⟨lt_of_le_of_lt (hpbetween w.1 w.2 hwi hwj.le).1 hz.1,
          hz.2.trans (hpbetween w.1 (w.2 + 1) hwi hwj).2⟩
  have htotal : ∑ v ∈ T, (B v - A v) = ∑ i ∈ S, (u i - l i) := by
    rw [Finset.sum_sigma]
    apply Finset.sum_congr rfl
    intro i hi
    simp only [A, B, hpdiff, Finset.sum_const, Finset.card_range, nsmul_eq_mul, hnΔ i hi]
  have hosc : (∑ i ∈ S, dist (h (⟨l i, y⟩ : ℂ)) (h (⟨u i, y⟩ : ℂ))) ≤
      ∑ v ∈ T, dist (h (⟨A v, y⟩ : ℂ)) (h (⟨B v, y⟩ : ℂ)) := by
    rw [Finset.sum_sigma]
    apply Finset.sum_le_sum
    intro i hi
    have hh := dist_le_range_sum_dist (f := fun j => h (⟨p i j, y⟩ : ℂ)) (n i)
    simpa only [hp0, hpn i hi, A, B] using hh
  have hbound := comparable_horizontal_oscillation_le h T A B a b y N ε κ hN hε
    (fun v hv => (hdomain v.1 (htmem hv).1).1.trans (hpbetween v.1 v.2 (htmem hv).1 (htmem hv).2.le).1)
    (fun v hv => (hpbetween v.1 (v.2 + 1) (htmem hv).1 (htmem hv).2).2.trans (hdomain v.1 (htmem hv).1).2)
    (fun v hv => by simpa only [A, B, hpdiff] using hΔ v.1 (htmem hv).1)
    hdisj hdisks (hstrip ε hε hεδ)
  rw [htotal, hsumLength] at hbound
  rw [← hsumOsc]
  exact ((sq_le_sq₀ (Finset.sum_nonneg (fun _ _ => dist_nonneg))
    (Finset.sum_nonneg (fun _ _ => dist_nonneg))).mpr hosc).trans hbound

theorem ae_absolutelyContinuousOnInterval_horizontal
    (h : ℂ ≃ₜ ℂ) (κ : ℝ)
    (hdisks : ∀ z : ℂ, ∀ r : ℝ, 0 < r → ∃ ρ R : ℝ, 0 < ρ ∧
      Metric.closedBall (h z) ρ ⊆ h '' Metric.ball z r ∧
      h '' Metric.closedBall z r ⊆ Metric.closedBall (h z) R ∧ R ≤ κ * ρ)
    (a b c d : ℝ) :
    ∀ᵐ y : ℝ ∂MeasureTheory.volume.restrict (Set.Ioo c d),
      AbsolutelyContinuousOnInterval (fun t : ℝ => h (⟨t, y⟩ : ℂ)) a b := by
  have hordered (a b : ℝ) (hab : a ≤ b) :
      ∀ᵐ y : ℝ ∂MeasureTheory.volume.restrict (Set.Ioo c d),
        AbsolutelyContinuousOnInterval (fun t : ℝ => h (⟨t, y⟩ : ℂ)) a b := by
    filter_upwards [h.ae_exists_volume_image_strip_le (a - 1) (b + 1) c d,
      MeasureTheory.ae_restrict_mem isOpen_Ioo.measurableSet] with y hy hycd
    obtain ⟨N, hN, hstrip⟩ := hy
    have hδ : 0 < min (y - c) (d - y) := lt_min (sub_pos.mpr hycd.1) (sub_pos.mpr hycd.2)
    let Q := 16 * κ ^ 2 * N / Real.pi
    have hQ : 0 ≤ Q := by dsimp [Q]; positivity
    rw [absolutelyContinuousOnInterval_iff]
    intro τ hτ
    refine ⟨τ ^ 2 / (Q + 1), by positivity, ?_⟩
    intro P hP hlength
    have hsq := sq_sum_dist_horizontal_le_of_image_strip_bound h κ hdisks a b y N
      (min (y - c) (d - y)) hab hN hδ hstrip P hP
    have hlength0 : 0 ≤ ∑ i ∈ Finset.range P.1, dist (P.2 i).1 (P.2 i).2 :=
      Finset.sum_nonneg (fun _ _ => dist_nonneg)
    have hscaled := mul_lt_mul_of_pos_left hlength (by linarith : 0 < Q + 1)
    have hcancel : (Q + 1) * (τ ^ 2 / (Q + 1)) = τ ^ 2 := by field_simp
    rw [hcancel] at hscaled
    change (∑ i ∈ Finset.range P.1,
      dist (h (⟨(P.2 i).1, y⟩ : ℂ)) (h (⟨(P.2 i).2, y⟩ : ℂ))) ^ 2 ≤
      Q * ∑ i ∈ Finset.range P.1, dist (P.2 i).1 (P.2 i).2 at hsq
    nlinarith
  rcases le_total a b with hab | hba
  · exact hordered a b hab
  · filter_upwards [hordered b a hba] with y hy
    exact hy.symm

end Homeomorph
