import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Seifert.PantsBridges

/-!
# The radial profile shared by the families of the cone fold

Lane A4, tier 1 (design `docs/geometrization/handoffs/20261004-design-a4-cone-fold.md`, §3).
For `K > 0`, `coneProfile K t = 1/2 + 2t²/(t² + K)` is smooth, strictly increasing on `t ≥ 0`, with
values in `[1/2, 5/2)`, and satisfies the inversion identity
`coneProfile K t + coneProfile K (K/t) = 3` (`coneProfile_add_inv`); the canonical height `√K` is
its fixed point, `coneProfile K √K = 3/2`. Differences factor explicitly
(`coneProfile_sub`, `coneProfile_add_sub_three`), which turns the second-order defects of the
virtual heights into the vanishing Heron factors of the bridges. For `K = 1/4` it recovers K16f's
profiles: `3/2 + coneProfile (1/4) y = bridgeRho y` and
`coneProfile (1/4) (1/(4h)) = bridgeSigma h`.
-/

set_option autoImplicit false

noncomputable section

open scoped ContDiff

namespace GC.Seifert

def coneProfile (K t : ℝ) : ℝ := 1 / 2 + 2 * t ^ 2 / (t ^ 2 + K)

variable {K : ℝ}

theorem coneProfile_add_inv (hK : 0 < K) {t : ℝ} (ht : 0 < t) :
    coneProfile K t + coneProfile K (K / t) = 3 := by
  unfold coneProfile
  have h1 : 0 < t ^ 2 + K := by positivity
  have h2 : 0 < (K / t) ^ 2 + K := by positivity
  field_simp
  ring

theorem coneProfile_sub (hK : 0 < K) (a b : ℝ) :
    coneProfile K a - coneProfile K b =
      2 * K * (a - b) * (a + b) / ((a ^ 2 + K) * (b ^ 2 + K)) := by
  unfold coneProfile
  have h1 : 0 < a ^ 2 + K := by positivity
  have h2 : 0 < b ^ 2 + K := by positivity
  field_simp
  ring

theorem coneProfile_add_sub_three (hK : 0 < K) (a b : ℝ) :
    coneProfile K a + coneProfile K b - 3 =
      2 * (a * b - K) * (a * b + K) / ((a ^ 2 + K) * (b ^ 2 + K)) := by
  unfold coneProfile
  have h1 : 0 < a ^ 2 + K := by positivity
  have h2 : 0 < b ^ 2 + K := by positivity
  field_simp
  ring

theorem half_le_coneProfile (hK : 0 < K) (t : ℝ) : 1 / 2 ≤ coneProfile K t := by
  unfold coneProfile
  have : 0 ≤ 2 * t ^ 2 / (t ^ 2 + K) := by positivity
  linarith

theorem half_lt_coneProfile (hK : 0 < K) {t : ℝ} (ht : t ≠ 0) : 1 / 2 < coneProfile K t := by
  unfold coneProfile
  have : 0 < 2 * t ^ 2 / (t ^ 2 + K) := by positivity
  linarith

theorem coneProfile_lt (hK : 0 < K) (t : ℝ) : coneProfile K t < 5 / 2 := by
  unfold coneProfile
  have h1 : 0 < t ^ 2 + K := by positivity
  have : 2 * t ^ 2 / (t ^ 2 + K) < 2 := by
    rw [div_lt_iff₀ h1]
    linarith
  linarith

theorem coneProfile_sqrt (hK : 0 < K) : coneProfile K (Real.sqrt K) = 3 / 2 := by
  unfold coneProfile
  rw [Real.sq_sqrt hK.le]
  field_simp
  ring

theorem coneProfile_lt_iff (hK : 0 < K) {s t : ℝ} (hs : 0 ≤ s) (ht : 0 ≤ t) :
    coneProfile K s < coneProfile K t ↔ s < t := by
  have h := coneProfile_sub hK t s
  have h1 : 0 < s ^ 2 + K := by positivity
  have h2 : 0 < t ^ 2 + K := by positivity
  constructor
  · intro hst
    by_contra hle
    push Not at hle
    have : 0 ≤ 2 * K * (s - t) * (s + t) / ((s ^ 2 + K) * (t ^ 2 + K)) := by
      apply div_nonneg _ (by positivity)
      have : 0 ≤ s - t := by linarith
      have : 0 ≤ s + t := by linarith
      positivity
    have h' := coneProfile_sub hK s t
    linarith
  · intro hst
    have : 0 < 2 * K * (t - s) * (t + s) / ((t ^ 2 + K) * (s ^ 2 + K)) := by
      apply div_pos _ (by positivity)
      have : 0 < t - s := by linarith
      have : 0 < t + s := by linarith
      positivity
    linarith

theorem coneProfile_le_iff (hK : 0 < K) {s t : ℝ} (hs : 0 ≤ s) (ht : 0 ≤ t) :
    coneProfile K s ≤ coneProfile K t ↔ s ≤ t := by
  rw [← not_lt, coneProfile_lt_iff hK ht hs, not_lt]

theorem strictMonoOn_coneProfile (hK : 0 < K) : StrictMonoOn (coneProfile K) (Set.Ici 0) :=
  fun _ hs _ ht hst => (coneProfile_lt_iff hK hs ht).2 hst

theorem coneProfile_lt_three_halves_iff (hK : 0 < K) {t : ℝ} (ht : 0 ≤ t) :
    coneProfile K t < 3 / 2 ↔ t < Real.sqrt K := by
  rw [← coneProfile_sqrt hK, coneProfile_lt_iff hK ht (Real.sqrt_nonneg K)]

theorem contDiff_coneProfile (hK : 0 < K) : ContDiff ℝ ∞ (coneProfile K) := by
  unfold coneProfile
  refine contDiff_const.add ?_
  refine (contDiff_const.mul (contDiff_id.pow 2)).div (contDiff_id.pow 2 |>.add contDiff_const)
    fun t => ?_
  have : 0 < t ^ 2 + K := by positivity
  exact this.ne'

theorem hasDerivAt_coneProfile (hK : 0 < K) (t : ℝ) :
    HasDerivAt (coneProfile K) (4 * K * t / (t ^ 2 + K) ^ 2) t := by
  have h1 : 0 < t ^ 2 + K := by positivity
  have hn : HasDerivAt (fun s : ℝ => 2 * s ^ 2) (2 * (2 * t)) t := by
    simpa using ((hasDerivAt_pow 2 t).const_mul 2)
  have hd : HasDerivAt (fun s : ℝ => s ^ 2 + K) (2 * t) t := by
    simpa using (hasDerivAt_pow 2 t).add_const K
  have h := (hn.div hd h1.ne').const_add (1 / 2)
  have e : 4 * K * t / (t ^ 2 + K) ^ 2 =
      (2 * (2 * t) * (t ^ 2 + K) - 2 * t ^ 2 * (2 * t)) / (t ^ 2 + K) ^ 2 := by
    congr 1
    ring
  rw [e]
  exact h

theorem bridgeRho_eq_coneProfile (y : ℝ) : bridgeRho y = 3 / 2 + coneProfile (1 / 4) y := by
  unfold bridgeRho coneProfile
  have h1 : 0 < 1 + 4 * y ^ 2 := by positivity
  have h2 : 0 < y ^ 2 + 1 / 4 := by positivity
  field_simp
  ring

theorem bridgeSigma_eq_coneProfile {h : ℝ} (hh : 0 < h) :
    bridgeSigma h = coneProfile (1 / 4) (1 / (4 * h)) := by
  unfold bridgeSigma coneProfile
  have h1 : 0 < 1 + 4 * h ^ 2 := by positivity
  have h2 : 0 < (1 / (4 * h)) ^ 2 + 1 / 4 := by positivity
  field_simp

end GC.Seifert
