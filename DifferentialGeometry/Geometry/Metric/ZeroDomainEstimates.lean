import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Analysis.Calculus.FDeriv.Mul
import Mathlib.Topology.MetricSpace.Pseudo.Lemmas
import Mathlib.Topology.Compactness.Compact

/-! ZSP02 (master207B, B:6374): estimates for the actual compact zero domains.
(ZR) radial localization of the adjusted marker/ratio set; the enclosing annulus lies strictly
inside it; (ZC) the quotient-rule estimate for the adjusted ratio; and the point-set facts:
the core-ball union is closed, compact, and the domains are pairwise disjoint. All quantities are
in `R` units where the blueprint uses them. -/

set_option autoImplicit false
open Set Metric

namespace GC.MetricGeometry

/-- (ZR): marker at least `.9R` forces the original cutoff above `.899`; ratio at most `.4` forces
`η < .402`; ratio exactly `.4` forces `|η - .4| < .002`. Block errors are `< δR`. -/
theorem zero_domain_radial_bounds {R ζ η u v δ : ℝ} (hR : 0 < R) (hδ : δ < 1 / 1000)
    (hu : |u - R * ζ * η| < δ * R) (hv : |v - R * ζ| < δ * R)
    (hv9 : 9 / 10 * R ≤ v) :
    899 / 1000 < ζ ∧ (u ≤ 4 / 10 * v → η < 402 / 1000) ∧
      (u = 4 / 10 * v → |η - 4 / 10| < 2 / 1000) := by
  obtain ⟨hv1, hv2⟩ := abs_lt.mp hv
  obtain ⟨hu1, hu2⟩ := abs_lt.mp hu
  have hδR : δ * R < R / 1000 := by nlinarith
  have hζ : 899 / 1000 < ζ := by
    by_contra h
    have : R * ζ ≤ R * (899 / 1000) := mul_le_mul_of_nonneg_left (le_of_not_gt h) hR.le
    linarith
  have hupper (hle : u ≤ 4 / 10 * v) : η < 402 / 1000 := by
    by_contra h
    have h1 : R * ζ * (402 / 1000) ≤ R * ζ * η :=
      mul_le_mul_of_nonneg_left (le_of_not_gt h) (by nlinarith)
    nlinarith
  refine ⟨hζ, hupper, fun heq => ?_⟩
  rw [abs_lt]
  constructor
  · by_contra h
    have h1 : R * ζ * η ≤ R * ζ * (398 / 1000) :=
      mul_le_mul_of_nonneg_left (by linarith) (by nlinarith)
    nlinarith
  · linarith [hupper heq.le]

/-- The enclosing annulus `.32 ≤ d ≤ .38` (where `η < .381` and the cutoff is one) lies in the
interior of the marker/ratio set: marker above `.999R`, ratio strictly below `.4`. -/
theorem zero_domain_annulus_ratio_lt {R η u v δ : ℝ} (hR : 0 < R) (hδ : δ < 1 / 1000)
    (hη : η < 381 / 1000) (hu : |u - R * η| < δ * R) (hv : |v - R| < δ * R) :
    999 / 1000 * R < v ∧ u < 4 / 10 * v := by
  obtain ⟨hv1, -⟩ := abs_lt.mp hv
  obtain ⟨-, hu2⟩ := abs_lt.mp hu
  have hδR : δ * R < R / 1000 := by nlinarith
  have hRη : R * η < R * (381 / 1000) := mul_lt_mul_of_pos_left hη hR
  constructor <;> linarith

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- (ZC): with `|v - 1| < δ ≤ c₃`, `‖Du - Dη‖ < c₃`, `‖Dv‖ < c₃`, `‖Dη‖ ≤ 1 + ε₀` and
`|u/v| < .502`, the ratio `u/v` has derivative within `3 c₃` of `Dη`. -/
theorem hasFDerivAt_div_and_norm_sub_lt {u v : E → ℝ} {Du Dv Dη : E →L[ℝ] ℝ} {x : E}
    {c₃ δ ε₀ : ℝ} (hu : HasFDerivAt u Du x) (hv : HasFDerivAt v Dv x)
    (hDu : ‖Du - Dη‖ < c₃) (hDv : ‖Dv‖ < c₃) (hDη : ‖Dη‖ ≤ 1 + ε₀)
    (hvx : |v x - 1| < δ) (hδ : δ < 1 / 1000) (hδc : δ ≤ c₃) (hε₀ : ε₀ < 1 / 100)
    (hr : |u x / v x| < 502 / 1000) :
    HasFDerivAt (fun y => u y / v y) ((v x)⁻¹ • Du - (u x / v x ^ 2) • Dv) x ∧
      ‖((v x)⁻¹ • Du - (u x / v x ^ 2) • Dv) - Dη‖ < 3 * c₃ := by
  have hvpos : 999 / 1000 < v x := by linarith [(abs_lt.mp hvx).1]
  have hv0 : v x ≠ 0 := by linarith
  have hinv : HasFDerivAt (fun y => (v y)⁻¹)
      ((ContinuousLinearMap.toSpanSingleton ℝ (-(v x ^ 2)⁻¹)).comp Dv) x :=
    (hasFDerivAt_inv hv0).comp x hv
  have hmul := hu.mul hinv
  have hderiv : HasFDerivAt (fun y => u y / v y) ((v x)⁻¹ • Du - (u x / v x ^ 2) • Dv) x := by
    have hfun : (fun y => u y / v y) = fun y => u y * (v y)⁻¹ := by
      funext y
      rw [div_eq_mul_inv]
    rw [hfun]
    convert hmul using 1
    ext y
    simp only [sub_apply, smul_apply, smul_eq_mul,
      add_apply, ContinuousLinearMap.comp_apply,
      ContinuousLinearMap.toSpanSingleton_apply]
    field_simp
    ring
  refine ⟨hderiv, ?_⟩
  have hc₃ : 0 < c₃ := lt_of_le_of_lt (norm_nonneg _) hDv
  set r := u x / v x with hr_def
  have hsplit : ((v x)⁻¹ • Du - (u x / v x ^ 2) • Dv) - Dη =
      (v x)⁻¹ • ((Du - Dη) + (1 - v x) • Dη - r • Dv) := by
    ext y
    simp only [sub_apply, smul_apply, smul_eq_mul,
      add_apply, hr_def]
    field_simp
    ring
  rw [hsplit, norm_smul, Real.norm_eq_abs, abs_inv, abs_of_pos (by linarith : 0 < v x)]
  have hX : ‖(Du - Dη) + (1 - v x) • Dη - r • Dv‖ < c₃ + δ * (1 + ε₀) + 502 / 1000 * c₃ := by
    have h1 := norm_sub_le ((Du - Dη) + (1 - v x) • Dη) (r • Dv)
    have h2 := norm_add_le (Du - Dη) ((1 - v x) • Dη)
    have h3 : ‖(1 - v x) • Dη‖ ≤ δ * (1 + ε₀) := by
      rw [norm_smul, Real.norm_eq_abs, abs_sub_comm]
      exact mul_le_mul hvx.le hDη (norm_nonneg _) (by linarith [abs_nonneg (v x - 1)])
    have h4 : ‖r • Dv‖ ≤ 502 / 1000 * c₃ := by
      rw [norm_smul, Real.norm_eq_abs]
      exact mul_le_mul hr.le hDv.le (norm_nonneg _) (by norm_num)
    linarith
  rw [inv_mul_lt_iff₀ (by linarith)]
  have hε : δ * (1 + ε₀) ≤ c₃ * (101 / 100) := by
    have hδ0 : 0 ≤ δ := lt_of_le_of_lt (abs_nonneg _) hvx |>.le
    nlinarith
  nlinarith

/-- The core-ball union is the closed-ball union when the annulus `[t, s)` lies in `C`. -/
theorem ball_union_eq_closedBall_union {X : Type*} [PseudoMetricSpace X] {p : X} {t s : ℝ}
    (hts : t < s) {C : Set X} (hann : ∀ y, t ≤ dist y p → dist y p < s → y ∈ C) :
    ball p s ∪ C = closedBall p t ∪ C := by
  ext y
  simp only [mem_union, mem_ball, mem_closedBall]
  constructor
  · rintro (h | h)
    · by_cases hy : dist y p ≤ t
      · exact Or.inl hy
      · exact Or.inr (hann y (le_of_not_ge hy) h)
    · exact Or.inr h
  · rintro (h | h)
    · exact Or.inl (lt_of_le_of_lt h hts)
    · exact Or.inr h

theorem isCompact_closedBall_union_of_isClosed {X : Type*} [PseudoMetricSpace X]
    [CompactSpace X] (p : X) (t : ℝ) {C : Set X} (hC : IsClosed C) :
    IsCompact (closedBall p t ∪ C) :=
  (isClosed_closedBall.union hC).isCompact

/-- Disjointness of the zero domains from their inclusion in disjoint balls. -/
theorem pairwise_disjoint_of_subset_ball {X ι : Type*} [PseudoMetricSpace X] (Z : ι → Set X)
    (p : ι → X) (R : ι → ℝ) (hZ : ∀ i, Z i ⊆ ball (p i) (42 / 100 * R i))
    (hR : ∀ i, 0 ≤ R i)
    (hdisj : Pairwise fun i j => Disjoint (ball (p i) (R i)) (ball (p j) (R j))) :
    Pairwise fun i j => Disjoint (Z i) (Z j) := by
  intro i j hij
  have hi : ball (p i) (42 / 100 * R i) ⊆ ball (p i) (R i) :=
    ball_subset_ball (by nlinarith [hR i])
  have hj : ball (p j) (42 / 100 * R j) ⊆ ball (p j) (R j) :=
    ball_subset_ball (by nlinarith [hR j])
  exact (hdisj hij).mono ((hZ i).trans hi) ((hZ j).trans hj)

end GC.MetricGeometry
