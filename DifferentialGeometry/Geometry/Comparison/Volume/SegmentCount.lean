import DifferentialGeometry.Geometry.Comparison.Volume.SegmentPolar
import DifferentialGeometry.Geometry.Comparison.Volume.Packing
import DifferentialGeometry.Analysis.Integration.Measure.Properties

set_option autoImplicit false
set_option linter.unusedSectionVars false

/-!
# Member-level Bishop–Gromov packing count

This file assembles brick **B6** of the A0′ `VolumeComparisonInput` producer lane
(`HCGCompactness/C4/A0PRIME_VOLUME_PLAN.md`).  For one complete member `(M, g)`
with `Ric ≥ -(n-1)q²` it turns the capped relative Bishop–Gromov comparison
(`segBall_vol_rel`, `SegmentPolar.lean`) into an explicit, member-independent
bound on how many `r`-separated centers can crowd within `m·r` of a point.

## Main results

* `segImult` — the explicit intersection multiplicity `⌈e^{8q(n-1)r0}(8m+4)ⁿ⌉ + 1`,
  depending only on the dimension `n`, the Ricci scale `q`, and the containing
  cap `r0` (not on the member, the radius `r`, the point, or the centers).
* `segBall_card` — the counting theorem B7 instantiates per member: for an
  `r`-separated finite family with `m·r ≤ r0`, at most `segImult n q r0 m`
  centers lie within `m·r` of any fixed point `z`, in `riemannianEDist` terms.

The theorem consumes `segBall_vol_rel` and `segBall_vol_fin` **as stated**; the
only frontier `sorry`s in the import chain remain the two in `SegmentPolar.lean`.

The model-volume ratio inputs (`hypRadVol_ratio_le` and the elementary `hypSn`
bounds it rests on) are proved from scratch here.  Positivity of member balls
uses the open-positive-measure property of `riemannianVolumeMeasure` (no
`CompactSpace`); finiteness comes from `segBall_vol_fin`.  The abstract counting
chain (`mul_lower_le_upper`, `card_le_of_mul_lt`) is reused from `Packing.lean`
against raw `riemannianEDist`-balls, since members carry no real-distance
`PseudoMetricSpace` structure.
-/

noncomputable section

open Set Function Filter Bundle Manifold MeasureTheory
open scoped Topology Manifold ContDiff ENNReal

namespace DifferentialGeometry.Geometry.Riemannian.VolumeComparison

open DifferentialGeometry.Geometry.Riemannian.Exponential
open DifferentialGeometry.Geometry.Riemannian.BonnetMyers
open DifferentialGeometry.Integral.Measure

/-! ## Model-volume ratio bound (geometry-free) -/

/-- `sinh x ≤ x · eˣ` — the elementary upper bound behind the model-density
estimate.  Equivalent to `e^{2x}(1-2x) ≤ 1`, i.e. `Real.add_one_le_exp (-2x)`. -/
theorem sinh_le_mul_exp (x : ℝ) : Real.sinh x ≤ x * Real.exp x := by
  have ha : (0 : ℝ) < Real.exp x := Real.exp_pos x
  have hab : Real.exp x * Real.exp (-x) = 1 := by rw [← Real.exp_add]; simp
  have hbb : Real.exp (-(2 * x)) = Real.exp (-x) * Real.exp (-x) := by
    rw [← Real.exp_add]; ring_nf
  have h := Real.add_one_le_exp (-(2 * x))
  rw [hbb] at h
  have key : Real.exp x * (1 - 2 * x) ≤ Real.exp (-x) := by
    calc Real.exp x * (1 - 2 * x)
        = Real.exp x * (-(2 * x) + 1) := by ring
      _ ≤ Real.exp x * (Real.exp (-x) * Real.exp (-x)) :=
          mul_le_mul_of_nonneg_left h ha.le
      _ = (Real.exp x * Real.exp (-x)) * Real.exp (-x) := by ring
      _ = Real.exp (-x) := by rw [hab, one_mul]
  rw [Real.sinh_eq, div_le_iff₀ (by norm_num : (0 : ℝ) < 2)]
  nlinarith [key]

/-- The hyperbolic warping function is bounded above by `τ · e^{qτ}`. -/
theorem hypSn_le_mul_exp {q τ : ℝ} (hq : 0 ≤ q) :
    hypSn q τ ≤ τ * Real.exp (q * τ) := by
  by_cases hq0 : q = 0
  · subst hq0; simp [hypSn]
  · have hqpos : 0 < q := hq.lt_of_ne (Ne.symm hq0)
    rw [hypSn, if_neg hq0, div_le_iff₀ hqpos]
    calc Real.sinh (q * τ) ≤ (q * τ) * Real.exp (q * τ) := sinh_le_mul_exp (q * τ)
      _ = τ * Real.exp (q * τ) * q := by ring

/-- The hyperbolic warping function dominates the Euclidean radius. -/
theorem hypSn_ge_self {q τ : ℝ} (hq : 0 ≤ q) (hτ : 0 ≤ τ) : τ ≤ hypSn q τ := by
  by_cases hq0 : q = 0
  · subst hq0; simp [hypSn]
  · have hqpos : 0 < q := hq.lt_of_ne (Ne.symm hq0)
    rw [hypSn, if_neg hq0, le_div_iff₀ hqpos]
    calc τ * q = q * τ := by ring
      _ ≤ Real.sinh (q * τ) := Real.self_le_sinh_iff.mpr (mul_nonneg hq hτ)

/-- Pointwise upper bound on the hyperbolic area density. -/
theorem hypDen_le {q τ : ℝ} (d : ℕ) (hq : 0 ≤ q) (hτ : 0 ≤ τ) :
    hypDensity q d τ ≤ τ ^ d * Real.exp (q * (d : ℝ) * τ) := by
  have h1 : hypSn q τ ≤ τ * Real.exp (q * τ) := hypSn_le_mul_exp hq
  have h0 : 0 ≤ hypSn q τ := le_trans hτ (hypSn_ge_self hq hτ)
  have hexp : Real.exp (q * τ) ^ d = Real.exp (q * (d : ℝ) * τ) := by
    rw [← Real.exp_nat_mul]; congr 1; ring
  calc hypDensity q d τ = hypSn q τ ^ d := rfl
    _ ≤ (τ * Real.exp (q * τ)) ^ d := pow_le_pow_left₀ h0 h1 d
    _ = τ ^ d * Real.exp (q * (d : ℝ) * τ) := by rw [mul_pow, hexp]

/-- The model radial volume is at most `R^{d+1} · e^{qdR}`, from the constant
upper bound `hypDensity q d τ ≤ (R · e^{qR})^d` on `[0,R]`. -/
theorem hypRadVol_le (d : ℕ) {q R : ℝ} (hq : 0 ≤ q) (hR : 0 ≤ R) :
    hypRadVol q d R ≤ R ^ (d + 1) * Real.exp (q * (d : ℝ) * R) := by
  have hqd : (0 : ℝ) ≤ q * (d : ℝ) := mul_nonneg hq (Nat.cast_nonneg d)
  calc hypRadVol q d R
      = ∫ τ in (0 : ℝ)..R, hypDensity q d τ := rfl
    _ ≤ ∫ _τ in (0 : ℝ)..R, R ^ d * Real.exp (q * (d : ℝ) * R) := by
        refine intervalIntegral.integral_mono_on hR
          ((hypDen_continuous q d).intervalIntegrable _ _)
          (continuous_const.intervalIntegrable _ _) ?_
        intro τ hτ
        have hτ0 : 0 ≤ τ := hτ.1
        calc hypDensity q d τ ≤ τ ^ d * Real.exp (q * (d : ℝ) * τ) := hypDen_le d hq hτ0
          _ ≤ R ^ d * Real.exp (q * (d : ℝ) * R) :=
              mul_le_mul (pow_le_pow_left₀ hτ0 hτ.2 d)
                (Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left hτ.2 hqd))
                (Real.exp_pos _).le (pow_nonneg hR d)
    _ = R ^ (d + 1) * Real.exp (q * (d : ℝ) * R) := by
        rw [intervalIntegral.integral_const, sub_zero, smul_eq_mul, ← mul_assoc, ← pow_succ']

/-- The model radial volume dominates `(s/2)^{d+1}`, from the constant lower
bound `hypDensity q d τ ≥ (s/2)^d` on the subinterval `[s/2, s]`. -/
theorem hypRadVol_ge (d : ℕ) {q s : ℝ} (hq : 0 ≤ q) (hs : 0 < s) :
    (s / 2) ^ (d + 1) ≤ hypRadVol q d s := by
  have hs2 : (0 : ℝ) ≤ s / 2 := by linarith
  have hss : s / 2 ≤ s := by linarith
  have hlow_sub : (s / 2) * (s / 2) ^ d ≤ ∫ τ in (s / 2)..s, hypDensity q d τ := by
    have hmono : ∫ _τ in (s / 2)..s, (s / 2) ^ d ≤ ∫ τ in (s / 2)..s, hypDensity q d τ := by
      refine intervalIntegral.integral_mono_on hss
        (continuous_const.intervalIntegrable _ _)
        ((hypDen_continuous q d).intervalIntegrable _ _) ?_
      intro τ hτ
      exact pow_le_pow_left₀ hs2 (le_trans hτ.1 (hypSn_ge_self hq (le_trans hs2 hτ.1))) d
    rwa [intervalIntegral.integral_const, smul_eq_mul,
      show s - s / 2 = s / 2 from by ring] at hmono
  have hnn : 0 ≤ ∫ τ in (0 : ℝ)..(s / 2), hypDensity q d τ :=
    intervalIntegral.integral_nonneg hs2
      (fun τ hτ => pow_nonneg (le_trans hτ.1 (hypSn_ge_self hq hτ.1)) d)
  have hsplit : (∫ τ in (0 : ℝ)..(s / 2), hypDensity q d τ)
        + ∫ τ in (s / 2)..s, hypDensity q d τ
      = ∫ τ in (0 : ℝ)..s, hypDensity q d τ :=
    intervalIntegral.integral_add_adjacent_intervals
      ((hypDen_continuous q d).intervalIntegrable _ _)
      ((hypDen_continuous q d).intervalIntegrable _ _)
  calc (s / 2) ^ (d + 1) = (s / 2) * (s / 2) ^ d := by rw [pow_succ']
    _ ≤ ∫ τ in (s / 2)..s, hypDensity q d τ := hlow_sub
    _ ≤ (∫ τ in (0 : ℝ)..(s / 2), hypDensity q d τ)
          + ∫ τ in (s / 2)..s, hypDensity q d τ := by linarith
    _ = hypRadVol q d s := hsplit

/-- **Capped model-volume ratio.**  For `0 < s ≤ R`,
`v(R) ≤ e^{qdR} · (R/(s/2))^{d+1} · v(s)` where `v = hypRadVol q d`.  This is the
member-independent packing ratio (the `(s/2)` reflects the crude constant lower
bound; sharpness is irrelevant to the counting constant). -/
theorem hypRadVol_ratio_le (d : ℕ) {q s R : ℝ} (hq : 0 ≤ q) (hs : 0 < s)
    (hsR : s ≤ R) :
    hypRadVol q d R ≤
      Real.exp (q * (d : ℝ) * R) * (R / (s / 2)) ^ (d + 1) * hypRadVol q d s := by
  have hub := hypRadVol_le d hq (hs.le.trans hsR)
  have hlb := hypRadVol_ge d hq hs
  have hs2 : (0 : ℝ) < s / 2 := by linarith
  have hRnn : 0 ≤ R := hs.le.trans hsR
  have hcoef : 0 ≤ Real.exp (q * (d : ℝ) * R) * (R / (s / 2)) ^ (d + 1) :=
    mul_nonneg (Real.exp_pos _).le (pow_nonneg (div_nonneg hRnn hs2.le) _)
  calc hypRadVol q d R
      ≤ R ^ (d + 1) * Real.exp (q * (d : ℝ) * R) := hub
    _ = Real.exp (q * (d : ℝ) * R) * (R / (s / 2)) ^ (d + 1) * (s / 2) ^ (d + 1) := by
        have hs2ne : (s / 2) ^ (d + 1) ≠ 0 := pow_ne_zero _ hs2.ne'
        rw [div_pow]; field_simp
    _ ≤ Real.exp (q * (d : ℝ) * R) * (R / (s / 2)) ^ (d + 1) * hypRadVol q d s :=
        mul_le_mul_of_nonneg_left hlb hcoef

/-! ## The explicit multiplicity constant -/

/-- **Explicit intersection multiplicity** for the segment-ball packing count.
`n` is the manifold dimension, `q` the Ricci scale, `r0` the containing-scale
cap; the value `⌈e^{8q(n-1)r0}(16m+8)ⁿ⌉ + 1` is independent of the member, the
radius, the point, and the centers.  The `+1` makes it `≥ 1` uniformly, covering
the degenerate `m < 1/2` case. -/
def segImult (n : ℕ) (q r0 m : ℝ) : ℕ :=
  ⌈Real.exp (8 * q * ((n - 1 : ℕ) : ℝ) * r0) * (16 * m + 8) ^ n⌉₊ + 1

/-- The multiplicity constant dominates the capped model-volume ratio. -/
theorem le_segImult (n : ℕ) (q r0 m : ℝ) :
    Real.exp (8 * q * ((n - 1 : ℕ) : ℝ) * r0) * (16 * m + 8) ^ n
      ≤ (segImult n q r0 m : ℝ) := by
  have h := Nat.le_ceil
    (Real.exp (8 * q * ((n - 1 : ℕ) : ℝ) * r0) * (16 * m + 8) ^ n)
  unfold segImult
  push_cast
  linarith

/-- The multiplicity constant is always at least one. -/
theorem one_le_segImult (n : ℕ) (q r0 m : ℝ) : 1 ≤ segImult n q r0 m := by
  unfold segImult; omega

/-! ## Geometric setup -/

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [I.Boundaryless]
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M] [T2Space M] [T2Space (TangentBundle I M)] [SigmaCompactSpace M]
variable [RiemannianBundle (fun (x : M) ↦ TangentSpace I x)]

private local instance : MeasurableSpace E := borel E
private local instance : BorelSpace E := ⟨rfl⟩
private local instance : MeasurableSpace M := borel M
private local instance : BorelSpace M := ⟨rfl⟩

-- All geometric declarations below use the Riemannian tangent-fibre norm, so
-- that `riemannianEDist` matches across the helpers and the counting theorem.
attribute [-instance] Tensor0SBundle.tangentSpace_normedAddCommGroup
  Tensor0SBundle.tangentSpace_normedSpace

/-- The open `riemannianEDist`-ball is open. -/
theorem edistBall_open
    [IsContinuousRiemannianBundle E (fun (x : M) ↦ TangentSpace I x)]
    (x : M) (R : ℝ) :
    IsOpen {y : M | riemannianEDist I x y < ENNReal.ofReal R} :=
  isOpen_lt
    ((continuous_riemannianEDist_to (I := I) x).congr
      (fun _ => Manifold.riemannianEDist_comm))
    continuous_const

/-- Radius monotonicity of the `riemannianEDist`-ball. -/
theorem edistBall_mono (x : M) {ρ₁ ρ₂ : ℝ} (h : ρ₁ ≤ ρ₂) :
    {y : M | riemannianEDist I x y < ENNReal.ofReal ρ₁} ⊆
      {y : M | riemannianEDist I x y < ENNReal.ofReal ρ₂} :=
  fun _ hy => lt_of_lt_of_le hy (ENNReal.ofReal_le_ofReal h)

/-- Center-shift containment: if `d(a,b) ≤ t` then the `ρ`-ball at `a` sits
inside the `(t+ρ)`-ball at `b`. -/
theorem edistBall_shift {a b : M} {t ρ : ℝ}
    (hab : riemannianEDist I a b ≤ ENNReal.ofReal t) (ht : 0 ≤ t) (hρ : 0 ≤ ρ) :
    {y : M | riemannianEDist I a y < ENNReal.ofReal ρ} ⊆
      {y : M | riemannianEDist I b y < ENNReal.ofReal (t + ρ)} := by
  intro y hy
  simp only [Set.mem_setOf_eq] at hy ⊢
  calc riemannianEDist I b y
      ≤ riemannianEDist I b a + riemannianEDist I a y := riemannianEDist_triangle
    _ = riemannianEDist I a b + riemannianEDist I a y := by
        rw [show riemannianEDist I b a = riemannianEDist I a b from
          Manifold.riemannianEDist_comm]
    _ ≤ ENNReal.ofReal t + riemannianEDist I a y := by gcongr
    _ < ENNReal.ofReal t + ENNReal.ofReal ρ :=
        ENNReal.add_lt_add_left ENNReal.ofReal_ne_top hy
    _ = ENNReal.ofReal (t + ρ) := (ENNReal.ofReal_add ht hρ).symm

/-- Balls of radius `r/2` about an `r`-separated family are pairwise disjoint. -/
theorem edistBall_disj {ι : Type*} {J : Finset ι} {centers : ι → M} {r : ℝ}
    (hsep : ∀ i ∈ J, ∀ j ∈ J, i ≠ j →
      ENNReal.ofReal r ≤ riemannianEDist I (centers i) (centers j)) (hr : 0 ≤ r) :
    (↑J : Set ι).PairwiseDisjoint
      (fun i => {y : M | riemannianEDist I (centers i) y < ENNReal.ofReal (r / 2)}) := by
  intro i hi j hj hij
  simp only [Function.onFun, Set.disjoint_left, Set.mem_setOf_eq]
  intro y hyi hyj
  have hsep_ij := hsep i (Finset.mem_coe.mp hi) j (Finset.mem_coe.mp hj) hij
  have hlt : riemannianEDist I (centers i) (centers j) < ENNReal.ofReal r := by
    calc riemannianEDist I (centers i) (centers j)
        ≤ riemannianEDist I (centers i) y + riemannianEDist I y (centers j) :=
          riemannianEDist_triangle
      _ = riemannianEDist I (centers i) y + riemannianEDist I (centers j) y := by
          rw [show riemannianEDist I y (centers j) = riemannianEDist I (centers j) y from
            Manifold.riemannianEDist_comm]
      _ < ENNReal.ofReal (r / 2) + ENNReal.ofReal (r / 2) := ENNReal.add_lt_add hyi hyj
      _ = ENNReal.ofReal r := by
          rw [← ENNReal.ofReal_add (by linarith) (by linarith)]; norm_num
  exact absurd hsep_ij (not_le.mpr hlt)

/-! ## The counting theorem -/

/-- **Member-level Bishop–Gromov packing count** (A0′ brick B6).

For a complete member `(M, g)` with `Ric ≥ -(n-1)q²`, `0 ≤ q`, `0 < r`,
`m·r ≤ r0`, `0 < r0`: in any `r`-separated finite center family, at most
`segImult n q r0 m` centers can lie within `m·r` (in `riemannianEDist`) of a
fixed point `z`.  The bound is `member/point/radius/family-independent`.

Mirrors the `ballMult` field of `VolumeComparisonInput` in `riemannianEDist`
terms; brick B7 transports the supplied real distance through `RealizesEdist`. -/
theorem segBall_card [ConnectedSpace M] [PseudoEMetricSpace M]
    [IsRiemannianManifold I M] [CompleteSpace M]
    [IsContinuousRiemannianBundle E (fun (x : M) ↦ TangentSpace I x)]
    (g : SmoothRiemannianMetric I M)
    (hEnorm : ∀ (y : M) (w : TangentSpace I y),
      ‖w‖ₑ = ENNReal.ofReal (Real.sqrt (g.inner y w w)))
    {q r0 : ℝ} (hq : 0 ≤ q) (_hr0 : 0 < r0)
    (hRic : RicciBoundedBelow (I := I) g
      (-(((Module.finrank ℝ E - 1 : ℕ) : ℝ) * q ^ 2)))
    {m r : ℝ} (hr : 0 < r) (hcap : m * r ≤ r0)
    {α : Type*} (centers : α → M)
    (hsep : ∀ i j : α, i ≠ j →
      ENNReal.ofReal r ≤ riemannianEDist I (centers i) (centers j))
    (z : M) (J : Finset α)
    (hJz : ∀ j : α, j ∈ J →
      riemannianEDist I (centers j) z ≤ ENNReal.ofReal (m * r)) :
    J.card ≤ segImult (Module.finrank ℝ E) q r0 m := by
  by_cases hm : m < 1 / 2
  · -- Degenerate case `m < 1/2`: at most one center.
    refine le_trans ?_ (one_le_segImult (Module.finrank ℝ E) q r0 m)
    rw [Finset.card_le_one]
    intro a ha b hb
    by_contra hab
    have htri : riemannianEDist I (centers a) (centers b)
        ≤ ENNReal.ofReal (m * r) + ENNReal.ofReal (m * r) := by
      calc riemannianEDist I (centers a) (centers b)
          ≤ riemannianEDist I (centers a) z + riemannianEDist I z (centers b) :=
            riemannianEDist_triangle
        _ = riemannianEDist I (centers a) z + riemannianEDist I (centers b) z := by
            rw [show riemannianEDist I z (centers b)
              = riemannianEDist I (centers b) z from Manifold.riemannianEDist_comm]
        _ ≤ ENNReal.ofReal (m * r) + ENNReal.ofReal (m * r) :=
            add_le_add (hJz a ha) (hJz b hb)
    have hle := le_trans (hsep a b hab) htri
    have hrpos : 0 < ENNReal.ofReal r := ENNReal.ofReal_pos.mpr hr
    have hmrpos : 0 < ENNReal.ofReal (m * r) := by
      by_contra hnp
      rw [not_lt] at hnp
      rw [le_antisymm hnp (zero_le _), add_zero] at hle
      exact absurd hle (not_le.mpr hrpos)
    have hmr : 0 < m * r := ENNReal.ofReal_pos.mp hmrpos
    have hle2 : ENNReal.ofReal r ≤ ENNReal.ofReal (2 * (m * r)) := by
      rw [show (2 : ℝ) * (m * r) = m * r + m * r by ring,
        ENNReal.ofReal_add hmr.le hmr.le]
      exact hle
    have hr2 : r ≤ 2 * (m * r) :=
      (ENNReal.ofReal_le_ofReal_iff (by linarith [hmr])).mp hle2
    nlinarith [hr2, mul_pos (show (0 : ℝ) < 1 / 2 - m by linarith) hr]
  · -- Main case `1/2 ≤ m`.
    rw [not_lt] at hm
    rcases J.eq_empty_or_nonempty with hJe | hJne
    · subst hJe; simp
    have hm0 : 0 < m := by linarith
    have hs_pos : (0 : ℝ) < r / 2 := by linarith
    have hR'_pos : (0 : ℝ) < (4 * m + 2) * r := by nlinarith
    have hbigR_pos : (0 : ℝ) < (m + 1 / 2) * r := by nlinarith
    have hsR' : r / 2 ≤ (4 * m + 2) * r := by nlinarith
    have hvs_pos : 0 < hypRadVol q (Module.finrank ℝ E - 1) (r / 2) :=
      hypRadVol_pos hq hs_pos
    have hvR'_pos : 0 < hypRadVol q (Module.finrank ℝ E - 1) ((4 * m + 2) * r) :=
      hypRadVol_pos hq hR'_pos
    set μ := riemannianVolumeMeasure (I := I) (M := M) g with hμ
    haveI : μ.IsOpenPosMeasure :=
      riemannianVolumeMeasure_isOpenPosMeasure (I := I) (M := M) g
    -- The containing ball around `z` and the small balls around the centers.
    set big : Set M := {y : M | riemannianEDist I z y < ENNReal.ofReal ((m + 1 / 2) * r)}
      with hbig
    set small : α → Set M :=
      fun j => {y : M | riemannianEDist I (centers j) y < ENNReal.ofReal (r / 2)}
      with hsmall
    have hbig_open : IsOpen big := by rw [hbig]; exact edistBall_open (I := I) z _
    have hbig_ne : big.Nonempty := by
      rw [hbig]
      exact ⟨z, by
        simp only [Set.mem_setOf_eq, Manifold.riemannianEDist_self]
        exact ENNReal.ofReal_pos.mpr hbigR_pos⟩
    have hbig_pos : 0 < μ big := hbig_open.measure_pos μ hbig_ne
    have hbig_fin : μ big ≠ ⊤ := by
      rw [hbig]; exact (segBall_vol_fin (I := I) g hEnorm z hq hbigR_pos hRic).ne
    have hU_pos : 0 < (μ big).toReal := ENNReal.toReal_pos hbig_pos.ne' hbig_fin
    -- The uniform per-ball lower mass.
    set L : ℝ :=
      (μ big).toReal * hypRadVol q (Module.finrank ℝ E - 1) (r / 2)
        / hypRadVol q (Module.finrank ℝ E - 1) ((4 * m + 2) * r) with hL
    have hL_pos : 0 < L := by
      rw [hL]; exact div_pos (mul_pos hU_pos hvs_pos) hvR'_pos
    -- Lower bound on each small ball via capped Bishop–Gromov at the center.
    have hLj : ∀ j ∈ J, L ≤ μ.real (small j) := by
      intro j hj
      have hrel := segBall_vol_rel (I := I) g hEnorm (centers j) hq hs_pos hsR' hRic
      have hsub_big : big ⊆
          {y : M | riemannianEDist I (centers j) y < ENNReal.ofReal ((4 * m + 2) * r)} := by
        rw [hbig]
        refine (edistBall_shift (I := I) (a := z) (b := centers j) (t := m * r)
          (ρ := (m + 1 / 2) * r)
          (by
            rw [show riemannianEDist I z (centers j)
              = riemannianEDist I (centers j) z from Manifold.riemannianEDist_comm]
            exact hJz j hj)
          (mul_nonneg hm0.le hr.le) hbigR_pos.le).trans
          (edistBall_mono (I := I) (centers j) ?_)
        nlinarith
      have hmono_big : μ big
          ≤ μ {y : M | riemannianEDist I (centers j) y < ENNReal.ofReal ((4 * m + 2) * r)} :=
        measure_mono hsub_big
      have hcomb :
          μ big * ENNReal.ofReal (hypRadVol q (Module.finrank ℝ E - 1) (r / 2))
            ≤ ENNReal.ofReal (hypRadVol q (Module.finrank ℝ E - 1) ((4 * m + 2) * r))
              * μ (small j) := by
        calc μ big * ENNReal.ofReal (hypRadVol q (Module.finrank ℝ E - 1) (r / 2))
            ≤ μ {y : M | riemannianEDist I (centers j) y < ENNReal.ofReal ((4 * m + 2) * r)}
                * ENNReal.ofReal (hypRadVol q (Module.finrank ℝ E - 1) (r / 2)) := by
              gcongr
          _ ≤ ENNReal.ofReal (hypRadVol q (Module.finrank ℝ E - 1) ((4 * m + 2) * r))
                * μ (small j) := by simp only [hsmall]; exact hrel
      have hfin_small : μ (small j) ≠ ⊤ := by
        rw [hsmall]
        exact (segBall_vol_fin (I := I) g hEnorm (centers j) hq hs_pos hRic).ne
      have hreal := (ENNReal.toReal_le_toReal
        (ENNReal.mul_ne_top hbig_fin ENNReal.ofReal_ne_top)
        (ENNReal.mul_ne_top ENNReal.ofReal_ne_top hfin_small)).mpr hcomb
      rw [ENNReal.toReal_mul, ENNReal.toReal_mul,
        ENNReal.toReal_ofReal hvs_pos.le, ENNReal.toReal_ofReal hvR'_pos.le] at hreal
      simp only [Measure.real]
      rw [hL, div_le_iff₀ hvR'_pos]
      calc (μ big).toReal * hypRadVol q (Module.finrank ℝ E - 1) (r / 2)
          ≤ hypRadVol q (Module.finrank ℝ E - 1) ((4 * m + 2) * r) * (μ (small j)).toReal :=
            hreal
        _ = (μ (small j)).toReal * hypRadVol q (Module.finrank ℝ E - 1) ((4 * m + 2) * r) := by
            ring
    -- Disjointness, containment, measurability for the packing lemma.
    have hdisj : (↑J : Set α).PairwiseDisjoint small := by
      simp only [hsmall]
      exact edistBall_disj (I := I) (fun i _ j _ hij => hsep i j hij) hr.le
    have hsub : ∀ j ∈ J, small j ⊆ big := by
      intro j hj
      simp only [hsmall, hbig]
      have hle : m * r + r / 2 ≤ (m + 1 / 2) * r := le_of_eq (by ring)
      exact (edistBall_shift (I := I) (a := centers j) (b := z) (t := m * r) (ρ := r / 2)
        (hJz j hj) (mul_nonneg hm0.le hr.le) hs_pos.le).trans
        (edistBall_mono (I := I) z hle)
    have hmeas : ∀ j ∈ J, MeasurableSet (small j) := by
      intro j hj
      rw [hsmall]
      exact (edistBall_open (I := I) (centers j) _).measurableSet
    have hpack : (J.card : ℝ) * L ≤ μ.real big :=
      mul_lower_le_upper μ J small big hmeas hdisj hsub hbig_fin hLj
    have hle : (J.card : ℝ) * L ≤ (μ big).toReal := hpack
    -- The ratio bound: `v(R') ≤ segImult · v(s)`.
    have hn1 : 1 ≤ Module.finrank ℝ E :=
      Nat.one_le_iff_ne_zero.mpr (NeZero.ne _)
    have hdn : Module.finrank ℝ E - 1 + 1 = Module.finrank ℝ E := Nat.sub_add_cancel hn1
    have hratio : hypRadVol q (Module.finrank ℝ E - 1) ((4 * m + 2) * r)
        ≤ (segImult (Module.finrank ℝ E) q r0 m : ℝ)
          * hypRadVol q (Module.finrank ℝ E - 1) (r / 2) := by
      have hbase := hypRadVol_ratio_le (Module.finrank ℝ E - 1) hq hs_pos hsR'
      have hRs : (4 * m + 2) * r / (r / 2 / 2) = 16 * m + 8 := by
        field_simp; ring
      have hcap8 : (4 * m + 2) * r ≤ 8 * r0 := by
        nlinarith [hcap, mul_nonneg (show (0 : ℝ) ≤ m - 1 / 2 by linarith) hr.le]
      have hqfr : (0 : ℝ) ≤ q * ((Module.finrank ℝ E - 1 : ℕ) : ℝ) :=
        mul_nonneg hq (Nat.cast_nonneg _)
      have hexp_le :
          Real.exp (q * ((Module.finrank ℝ E - 1 : ℕ) : ℝ) * ((4 * m + 2) * r))
            ≤ Real.exp (8 * q * ((Module.finrank ℝ E - 1 : ℕ) : ℝ) * r0) := by
        apply Real.exp_le_exp.mpr
        nlinarith [mul_le_mul_of_nonneg_left hcap8 hqfr]
      have hcoef_le :
          Real.exp (q * ((Module.finrank ℝ E - 1 : ℕ) : ℝ) * ((4 * m + 2) * r))
              * ((4 * m + 2) * r / (r / 2 / 2)) ^ (Module.finrank ℝ E - 1 + 1)
            ≤ (segImult (Module.finrank ℝ E) q r0 m : ℝ) := by
        rw [hRs, hdn]
        calc Real.exp (q * ((Module.finrank ℝ E - 1 : ℕ) : ℝ) * ((4 * m + 2) * r))
              * (16 * m + 8) ^ Module.finrank ℝ E
            ≤ Real.exp (8 * q * ((Module.finrank ℝ E - 1 : ℕ) : ℝ) * r0)
                * (16 * m + 8) ^ Module.finrank ℝ E :=
              mul_le_mul_of_nonneg_right hexp_le (pow_nonneg (by linarith) _)
          _ ≤ (segImult (Module.finrank ℝ E) q r0 m : ℝ) := le_segImult _ _ _ _
      calc hypRadVol q (Module.finrank ℝ E - 1) ((4 * m + 2) * r)
          ≤ Real.exp (q * ((Module.finrank ℝ E - 1 : ℕ) : ℝ) * ((4 * m + 2) * r))
              * ((4 * m + 2) * r / (r / 2 / 2)) ^ (Module.finrank ℝ E - 1 + 1)
              * hypRadVol q (Module.finrank ℝ E - 1) (r / 2) := hbase
        _ ≤ (segImult (Module.finrank ℝ E) q r0 m : ℝ)
              * hypRadVol q (Module.finrank ℝ E - 1) (r / 2) :=
            mul_le_mul_of_nonneg_right hcoef_le hvs_pos.le
    -- Assemble the cardinality bound.
    have hNvs : hypRadVol q (Module.finrank ℝ E - 1) ((4 * m + 2) * r)
        < ((segImult (Module.finrank ℝ E) q r0 m : ℝ) + 1)
          * hypRadVol q (Module.finrank ℝ E - 1) (r / 2) := by
      nlinarith [hvs_pos, hratio]
    have hlt : (μ big).toReal <
        ((segImult (Module.finrank ℝ E) q r0 m + 1 : ℕ) : ℝ) * L := by
      have hexp : ((segImult (Module.finrank ℝ E) q r0 m + 1 : ℕ) : ℝ) * L
          = ((segImult (Module.finrank ℝ E) q r0 m : ℝ) + 1)
              * (μ big).toReal * hypRadVol q (Module.finrank ℝ E - 1) (r / 2)
              / hypRadVol q (Module.finrank ℝ E - 1) ((4 * m + 2) * r) := by
        rw [hL]; push_cast; ring
      rw [hexp, lt_div_iff₀ hvR'_pos]
      nlinarith [mul_lt_mul_of_pos_left hNvs hU_pos]
    exact card_le_of_mul_lt hL_pos hle hlt

end DifferentialGeometry.Geometry.Riemannian.VolumeComparison
