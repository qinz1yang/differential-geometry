import DifferentialGeometry.Geometry.Compactness.CheegerGromov.ApproximateIsometry.MetricApproximation.BallImage

set_option autoImplicit false

noncomputable section

universe u uE uH

namespace DifferentialGeometry
namespace HCGCompactness

open scoped Manifold ContDiff Topology BigOperators ENNReal
open Bundle Manifold

variable {E : Type uE} [NormedAddCommGroup E] [NormedSpace Real E]
variable [FiniteDimensional Real E]
variable [NeZero (Module.finrank Real E)] [CompleteSpace E]
variable {H : Type uH} [TopologicalSpace H]
variable {I : ModelWithCorners Real E H} [I.Boundaryless]

section DirectedRadii

theorem two_pow_lt_openRad (j l : ℕ) :
    (2 : ℝ) ^ j < (2 : ℝ) ^ j * (1 + (1 / 2 : ℝ) ^ (l + 1)) := by
  have hpow : 0 < (2 : ℝ) ^ j := by positivity
  have htail : 0 < (1 / 2 : ℝ) ^ (l + 1) := by positivity
  calc
    (2 : ℝ) ^ j = (2 : ℝ) ^ j * 1 := by ring
    _ < (2 : ℝ) ^ j * (1 + (1 / 2 : ℝ) ^ (l + 1)) :=
      mul_lt_mul_of_pos_left (by linarith) hpow

theorem openRad_pos (j l : ℕ) :
    0 < (2 : ℝ) ^ j * (1 + (1 / 2 : ℝ) ^ (l + 1)) := by
  have hpow : 0 < (2 : ℝ) ^ j := by positivity
  have htail : 0 < (1 / 2 : ℝ) ^ (l + 1) := by positivity
  nlinarith [mul_pos hpow (by linarith : (0 : ℝ) < 1 + (1 / 2 : ℝ) ^ (l + 1))]

theorem openRad_succ_lt (j l : ℕ) :
    (2 : ℝ) ^ j * (1 + (1 / 2 : ℝ) ^ (l + 2))
      < (2 : ℝ) ^ j * (1 + (1 / 2 : ℝ) ^ (l + 1)) := by
  have hpow : 0 < (2 : ℝ) ^ j := by positivity
  have htail : 0 < (1 / 2 : ℝ) ^ (l + 1) := by positivity
  have hsplit : (1 / 2 : ℝ) ^ (l + 2) = (1 / 2 : ℝ) ^ (l + 1) * (1 / 2) := by
    rw [show l + 2 = l + 1 + 1 by omega, pow_succ]
  refine mul_lt_mul_of_pos_left ?_ hpow
  rw [hsplit]
  nlinarith

def midRad (j l : ℕ) : ℝ :=
  (2 : ℝ) ^ j * (1 + (((1 / 2 : ℝ) ^ (l + 1) + (1 / 2 : ℝ) ^ (l + 2)) / 2))

theorem openRad_next_lt_mid (j l : ℕ) :
    (2 : ℝ) ^ j * (1 + (1 / 2 : ℝ) ^ (l + 2)) < midRad j l := by
  have hpow : 0 < (2 : ℝ) ^ j := by positivity
  have htail : 0 < (1 / 2 : ℝ) ^ (l + 1) := by positivity
  have hsplit : (1 / 2 : ℝ) ^ (l + 2) = (1 / 2 : ℝ) ^ (l + 1) * (1 / 2) := by
    rw [show l + 2 = l + 1 + 1 by omega, pow_succ]
  dsimp [midRad]
  refine mul_lt_mul_of_pos_left ?_ hpow
  rw [hsplit]
  nlinarith

theorem midRad_lt_openRad (j l : ℕ) :
    midRad j l < (2 : ℝ) ^ j * (1 + (1 / 2 : ℝ) ^ (l + 1)) := by
  have hpow : 0 < (2 : ℝ) ^ j := by positivity
  have htail : 0 < (1 / 2 : ℝ) ^ (l + 1) := by positivity
  have hsplit : (1 / 2 : ℝ) ^ (l + 2) = (1 / 2 : ℝ) ^ (l + 1) * (1 / 2) := by
    rw [show l + 2 = l + 1 + 1 by omega, pow_succ]
  dsimp [midRad]
  refine mul_lt_mul_of_pos_left ?_ hpow
  rw [hsplit]
  nlinarith

theorem midRad_le_step (j l : ℕ) :
    midRad j l ≤ (2 : ℝ) ^ (j + 1) := by
  have hpow : 0 < (2 : ℝ) ^ j := by positivity
  have htail₁ : (1 / 2 : ℝ) ^ (l + 1) ≤ 1 :=
    pow_le_one₀ (by norm_num) (by norm_num)
  have htail₂ : (1 / 2 : ℝ) ^ (l + 2) ≤ 1 :=
    pow_le_one₀ (by norm_num) (by norm_num)
  calc
    midRad j l = (2 : ℝ) ^ j *
        (1 + ((1 / 2 : ℝ) ^ (l + 1) + (1 / 2 : ℝ) ^ (l + 2)) / 2) := by
      rfl
    _ ≤ (2 : ℝ) ^ j * (1 + (1 + 1) / 2) := by
      have hinner :
          1 + ((1 / 2 : ℝ) ^ (l + 1) + (1 / 2 : ℝ) ^ (l + 2)) / 2
            ≤ 1 + (1 + 1) / 2 := by
        linarith
      exact mul_le_mul_of_nonneg_left hinner hpow.le
    _ = (2 : ℝ) ^ (j + 1) := by
      rw [pow_succ']
      ring

theorem midRad_le_mid0 (j l : ℕ) :
    midRad j l ≤ midRad j 0 := by
  have hpow : 0 ≤ (2 : ℝ) ^ j := by positivity
  have htail₁ : (1 / 2 : ℝ) ^ (l + 1) ≤ (1 / 2 : ℝ) ^ 1 :=
    pow_le_pow_of_le_one (by norm_num) (by norm_num) (by omega)
  have htail₂ : (1 / 2 : ℝ) ^ (l + 2) ≤ (1 / 2 : ℝ) ^ 2 :=
    pow_le_pow_of_le_one (by norm_num) (by norm_num) (by omega)
  dsimp [midRad]
  refine mul_le_mul_of_nonneg_left ?_ hpow
  nlinarith

theorem half_pow_succ_le_half (j : ℕ) :
    (1 / 2 : ℝ) ^ (j + 1) ≤ 1 / 2 := by
  have hpow : (1 / 2 : ℝ) ^ (j + 1) ≤ (1 / 2 : ℝ) ^ 1 :=
    pow_le_pow_of_le_one (by norm_num) (by norm_num) (by omega)
  simpa using hpow

omit [I.Boundaryless] in
omit [NeZero (Module.finrank ℝ E)] [CompleteSpace E] in
theorem properMetric_isOpen_ball
    (Y : PointedRiemannianManifold.{u, uE, uH} (I := I))
    (P : ProperMetricOn (I := I) Y) (x : Y.M) (r : ℝ) :
    @IsOpen Y.M Y.topology
      (letI : MetricSpace Y.M := P.ms
       Metric.ball x r) := by
  have hb :
      @IsOpen Y.M P.ms.toPseudoMetricSpace.toUniformSpace.toTopologicalSpace
        (letI : MetricSpace Y.M := P.ms
         Metric.ball x r) := by
    let : MetricSpace Y.M := P.ms
    exact Metric.isOpen_ball
  rw [ProperMetricOn.top_eq Y P] at hb
  exact hb

omit [NeZero (Module.finrank ℝ E)] [CompleteSpace E] [I.Boundaryless] in
theorem properMetric_mem_ball_self
    (Y : PointedRiemannianManifold.{u, uE, uH} (I := I))
    (P : ProperMetricOn (I := I) Y) (x : Y.M) {r : ℝ} (hr : 0 < r) :
    x ∈
      (letI : MetricSpace Y.M := P.ms
       Metric.ball x r) := by
  let : MetricSpace Y.M := P.ms
  exact Metric.mem_ball_self hr

omit [NeZero (Module.finrank ℝ E)] [CompleteSpace E] [I.Boundaryless] in
theorem properMetric_ball_nonempty
    (Y : PointedRiemannianManifold.{u, uE, uH} (I := I))
    (P : ProperMetricOn (I := I) Y) (x : Y.M) {r : ℝ} (hr : 0 < r) :
    Nonempty
      (letI : MetricSpace Y.M := P.ms
       Metric.ball x r) :=
  ⟨⟨x, properMetric_mem_ball_self (I := I) Y P x hr⟩⟩

theorem nonempty_opens_mk {M : Type u} {t : TopologicalSpace M}
    {s : Set M} (hs : @IsOpen M t s) (hne : Nonempty s) :
    Nonempty (⟨s, hs⟩ : @TopologicalSpace.Opens M t) :=
  hne

def properMetricOpenBall
    (Y : PointedRiemannianManifold.{u, uE, uH} (I := I))
    (P : ProperMetricOn (I := I) Y) (x : Y.M) (r : ℝ) :
    @TopologicalSpace.Opens Y.M Y.topology :=
  letI : TopologicalSpace Y.M := Y.topology
  ⟨(letI : MetricSpace Y.M := P.ms
    Metric.ball x r),
    properMetric_isOpen_ball (I := I) Y P x r⟩

omit [NeZero (Module.finrank ℝ E)] [CompleteSpace E] [I.Boundaryless] in
theorem properMetricOpenBall_nonempty
    (Y : PointedRiemannianManifold.{u, uE, uH} (I := I))
    (P : ProperMetricOn (I := I) Y) (x : Y.M) {r : ℝ} (hr : 0 < r) :
    Nonempty (properMetricOpenBall (I := I) Y P x r) := by
  let : TopologicalSpace Y.M := Y.topology
  dsimp [properMetricOpenBall]
  exact nonempty_opens_mk (properMetric_isOpen_ball (I := I) Y P x r)
    (properMetric_ball_nonempty (I := I) Y P x hr)

theorem imageRad_lt_step {a : ℝ} (j l : ℕ) (ha0 : 0 < a) (ha2 : a ≤ 1 / 2) :
    Real.sqrt (1 + a) * ((2 : ℝ) ^ j * (1 + (1 / 2 : ℝ) ^ (l + 2)))
      < (2 : ℝ) ^ (j + l + 1) := by
  have harg_nonneg : 0 ≤ 1 + a := by linarith
  have hsqrt_lt : Real.sqrt (1 + a) < 3 / 2 := by
    have hlt : 1 + a < (3 / 2 : ℝ) ^ 2 := by nlinarith
    have hs := Real.sqrt_lt_sqrt harg_nonneg hlt
    have hsqrt_sq : Real.sqrt ((3 / 2 : ℝ) ^ 2) = 3 / 2 := by
      rw [Real.sqrt_sq]
      norm_num
    simpa [hsqrt_sq] using hs
  have htail_le : (1 / 2 : ℝ) ^ (l + 2) ≤ (1 / 2 : ℝ) ^ 2 :=
    pow_le_pow_of_le_one (by norm_num) (by norm_num) (by omega)
  have hpow_pos : 0 < (2 : ℝ) ^ j := by positivity
  have hR_pos : 0 < (2 : ℝ) ^ j * (1 + (1 / 2 : ℝ) ^ (l + 2)) := by positivity
  have hR_le :
      (2 : ℝ) ^ j * (1 + (1 / 2 : ℝ) ^ (l + 2)) ≤ (5 / 4 : ℝ) * (2 : ℝ) ^ j := by
    nlinarith
  have hpow_mono : (2 : ℝ) ^ (j + 1) ≤ (2 : ℝ) ^ (j + l + 1) :=
    pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 2) (by omega)
  calc
    Real.sqrt (1 + a) * ((2 : ℝ) ^ j * (1 + (1 / 2 : ℝ) ^ (l + 2)))
        < (3 / 2 : ℝ) * ((2 : ℝ) ^ j * (1 + (1 / 2 : ℝ) ^ (l + 2))) :=
          mul_lt_mul_of_pos_right hsqrt_lt hR_pos
    _ ≤ (3 / 2 : ℝ) * ((5 / 4 : ℝ) * (2 : ℝ) ^ j) :=
          mul_le_mul_of_nonneg_left hR_le (by norm_num)
    _ = (15 / 8 : ℝ) * (2 : ℝ) ^ j := by ring
    _ < 2 * (2 : ℝ) ^ j := by nlinarith
    _ = (2 : ℝ) ^ (j + 1) := by rw [pow_succ']
    _ ≤ (2 : ℝ) ^ (j + l + 1) := hpow_mono

theorem imageMid_lt_step {a : ℝ} (j l : ℕ) (ha0 : 0 < a) (ha2 : a ≤ 1 / 2) :
    Real.sqrt (1 + a) * midRad j l < (2 : ℝ) ^ (j + l + 1) := by
  have harg_nonneg : 0 ≤ 1 + a := by linarith
  have hsqrt_lt : Real.sqrt (1 + a) < 5 / 4 := by
    have hlt : 1 + a < (5 / 4 : ℝ) ^ 2 := by nlinarith
    have hs := Real.sqrt_lt_sqrt harg_nonneg hlt
    have hsqrt_sq : Real.sqrt ((5 / 4 : ℝ) ^ 2) = 5 / 4 := by
      rw [Real.sqrt_sq]
      norm_num
    simpa [hsqrt_sq] using hs
  have htail₁ : (1 / 2 : ℝ) ^ (l + 1) ≤ (1 / 2 : ℝ) ^ 1 :=
    pow_le_pow_of_le_one (by norm_num) (by norm_num) (by omega)
  have htail₂ : (1 / 2 : ℝ) ^ (l + 2) ≤ (1 / 2 : ℝ) ^ 2 :=
    pow_le_pow_of_le_one (by norm_num) (by norm_num) (by omega)
  have hmid_pos : 0 < midRad j l := by
    dsimp [midRad]
    positivity
  have hmid_le : midRad j l ≤ (11 / 8 : ℝ) * (2 : ℝ) ^ j := by
    dsimp [midRad]
    nlinarith [show 0 ≤ (2 : ℝ) ^ j by positivity]
  have hpow_mono : (2 : ℝ) ^ (j + 1) ≤ (2 : ℝ) ^ (j + l + 1) :=
    pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 2) (by omega)
  calc
    Real.sqrt (1 + a) * midRad j l
        < (5 / 4 : ℝ) * midRad j l := mul_lt_mul_of_pos_right hsqrt_lt hmid_pos
    _ ≤ (5 / 4 : ℝ) * ((11 / 8 : ℝ) * (2 : ℝ) ^ j) :=
          mul_le_mul_of_nonneg_left hmid_le (by norm_num)
    _ = (55 / 32 : ℝ) * (2 : ℝ) ^ j := by ring
    _ < 2 * (2 : ℝ) ^ j := by nlinarith [show 0 < (2 : ℝ) ^ j by positivity]
    _ = (2 : ℝ) ^ (j + 1) := by rw [pow_succ']
    _ ≤ (2 : ℝ) ^ (j + l + 1) := hpow_mono

theorem imageMid_lt_openRad {a : ℝ} (j l : ℕ) (ha0 : 0 < a) (ha2 : a ≤ 1 / 2) :
    Real.sqrt (1 + a) * midRad j l
      < (2 : ℝ) ^ (j + 1) * (1 + (1 / 2 : ℝ) ^ (l + 1)) := by
  have hsqrt_nonneg : 0 ≤ Real.sqrt (1 + a) := Real.sqrt_nonneg _
  have hle_mid0 : Real.sqrt (1 + a) * midRad j l ≤ Real.sqrt (1 + a) * midRad j 0 :=
    mul_le_mul_of_nonneg_left (midRad_le_mid0 j l) hsqrt_nonneg
  have hlt_step : Real.sqrt (1 + a) * midRad j 0 < (2 : ℝ) ^ (j + 1) := by
    simpa using imageMid_lt_step j 0 ha0 ha2
  exact lt_trans (lt_of_le_of_lt hle_mid0 hlt_step) (two_pow_lt_openRad (j + 1) l)

end DirectedRadii

end HCGCompactness
end DifferentialGeometry
