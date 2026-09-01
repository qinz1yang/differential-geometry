import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith

set_option autoImplicit false

open Filter Topology

namespace DifferentialGeometry.PDE.RicciFlow

theorem false_of_hamiltonIvey_lower_bound_for_all_ages
    (scalar q : Real)
    (hq : 0 < q)
    (hbound : ∀ age : Real, 0 < age →
      scalar ≥ q * (Real.log (age * q) - 3)) :
    False := by
  let age : Real := Real.exp (scalar / q + 4) / q
  have hage : 0 < age := by
    dsimp [age]
    positivity
  have harg : age * q = Real.exp (scalar / q + 4) := by
    dsimp [age]
    field_simp
  have hlog : Real.log (age * q) = scalar / q + 4 := by
    rw [harg, Real.log_exp]
  have hmain := hbound age hage
  rw [hlog] at hmain
  have hquot : q * (scalar / q) = scalar := by
    field_simp
  have hrewrite : q * (scalar / q + 4 - 3) = scalar + q := by
    rw [show scalar / q + 4 - 3 = scalar / q + 1 by ring]
    rw [mul_add, hquot]
    ring
  rw [hrewrite] at hmain
  linarith

theorem nonnegative_of_hamiltonIvey_lower_bound_for_all_ages
    (scalar leastEigenvalue : Real → Real)
    (hbound : ∀ age : Real, 0 < age →
      ∀ x, leastEigenvalue x < 0 →
        scalar x ≥ (-leastEigenvalue x) *
          (Real.log (age * (-leastEigenvalue x)) - 3)) :
    ∀ x, 0 ≤ leastEigenvalue x := by
  intro x
  by_contra hnonneg
  have hnegative : leastEigenvalue x < 0 := lt_of_not_ge hnonneg
  let q : Real := -leastEigenvalue x
  have hq : 0 < q := by
    dsimp [q]
    linarith
  apply false_of_hamiltonIvey_lower_bound_for_all_ages
    (scalar x) q hq
  intro age hage
  simpa [q] using hbound age hage x hnegative

theorem nonnegative_of_hamilton_ivey_rescaled_limit
    (scalarLimit leastLimit T : Real)
    (scalarSeq leastSeq scaleSeq timeSeq : Nat → Real)
    (hscalar : Tendsto scalarSeq atTop (𝓝 scalarLimit))
    (hleast : Tendsto leastSeq atTop (𝓝 leastLimit))
    (hscale : Tendsto scaleSeq atTop atTop)
    (htime : Tendsto timeSeq atTop (𝓝 T))
    (hT : 0 < T)
    (hbound : ∀ᶠ i in atTop, leastSeq i < 0 →
      scalarSeq i ≥ (-leastSeq i) *
        (Real.log (timeSeq i * scaleSeq i * (-leastSeq i)) - 3)) :
    0 ≤ leastLimit := by
  by_contra hnonneg
  have hnegative : leastLimit < 0 := lt_of_not_ge hnonneg
  let q : Real := -leastLimit
  have hq : 0 < q := by
    dsimp [q]
    linarith
  have htimeHalf : ∀ᶠ i in atTop, T / 2 < timeSeq i := by
    have hnhds : Set.Ioi (T / 2) ∈ 𝓝 T := Ioi_mem_nhds (by linarith)
    exact htime hnhds
  have hleastHalf : ∀ᶠ i in atTop, q / 2 < -leastSeq i := by
    have hnhds : Set.Iio (leastLimit / 2) ∈ 𝓝 leastLimit := Iio_mem_nhds (by linarith)
    have h' := hleast hnhds
    change ∀ᶠ i in atTop, leastSeq i < leastLimit / 2 at h'
    filter_upwards [h'] with i hi
    linarith
  have hscalarUpper : ∀ᶠ i in atTop, scalarSeq i < scalarLimit + 1 := by
    have hnhds : Set.Iio (scalarLimit + 1) ∈ 𝓝 scalarLimit := Iio_mem_nhds (by linarith)
    exact hscalar hnhds
  have hnegEventually : ∀ᶠ i in atTop, leastSeq i < 0 := by
    filter_upwards [hleastHalf] with i hi
    linarith
  have hevent : ∀ᶠ i in atTop, scalarSeq i < scalarLimit + 1 ∧
      leastSeq i < 0 ∧ T / 2 < timeSeq i ∧ q / 2 < -leastSeq i := by
    filter_upwards [hscalarUpper, hnegEventually, htimeHalf, hleastHalf] with i hi hs ht hq'
    exact ⟨hi, hs, ht, hq'⟩
  have hscaleLarge : ∀ C : Real, 0 < C → ∀ᶠ i in atTop, C < scaleSeq i := by
    intro C hC
    exact hscale (eventually_gt_atTop C)
  let A : Real := max ((scalarLimit + 1) / (q / 2) + 4) 4
  have hAleft : (scalarLimit + 1) / (q / 2) + 4 ≤ A := by
    exact le_max_left _ _
  have hAright : 4 ≤ A := by
    exact le_max_right _ _
  let B : Real := Real.exp A / ((T / 2) * (q / 2))
  have hBpos : 0 < B := by
    dsimp [B]
    positivity
  have hlarge := hscaleLarge B hBpos
  have hi : ∃ i, scalarSeq i < scalarLimit + 1 ∧ leastSeq i < 0 ∧
      T / 2 < timeSeq i ∧ q / 2 < -leastSeq i ∧ B < scaleSeq i ∧
      (leastSeq i < 0 → scalarSeq i ≥ (-leastSeq i) *
        (Real.log (timeSeq i * scaleSeq i * (-leastSeq i)) - 3)) := by
    rcases (hbound.and (hevent.and hlarge)).exists with ⟨i, hboundi, hi, hBi⟩
    exact ⟨i, hi.1, hi.2.1, hi.2.2.1, hi.2.2.2, hBi, hboundi⟩
  obtain ⟨i, hsi, hli, hti, hqi, hscalei, hboundi⟩ := hi
  have hprod : Real.exp A < timeSeq i * scaleSeq i * (-leastSeq i) := by
    have hconst : 0 < (T / 2) * (q / 2) := by positivity
    have hprod0 : Real.exp A < (T / 2) * (q / 2) * scaleSeq i := by
      calc
        Real.exp A = ((T / 2) * (q / 2)) * B := by
          dsimp [B]
          field_simp
        _ < ((T / 2) * (q / 2)) * scaleSeq i :=
          mul_lt_mul_of_pos_left hscalei hconst
    have hscalePos : 0 < scaleSeq i := lt_trans hBpos hscalei
    have hleastPos : 0 < -leastSeq i := lt_trans (by positivity) hqi
    have hprod1 : (T / 2) * scaleSeq i < timeSeq i * scaleSeq i :=
      mul_lt_mul_of_pos_right hti hscalePos
    have hprod2 : (T / 2) * scaleSeq i * (q / 2) <
        (timeSeq i * scaleSeq i) * (-leastSeq i) := by
      calc
        (T / 2) * scaleSeq i * (q / 2) <
            (T / 2) * scaleSeq i * (-leastSeq i) :=
          mul_lt_mul_of_pos_left hqi (by positivity)
        _ < (timeSeq i * scaleSeq i) * (-leastSeq i) :=
          mul_lt_mul_of_pos_right hprod1 hleastPos
    have hprod0' : Real.exp A < (T / 2) * scaleSeq i * (q / 2) := by
      nlinarith [hprod0]
    exact hprod0'.trans hprod2
  have htimePos : 0 < timeSeq i := lt_trans (by positivity) hti
  have hscalePos : 0 < scaleSeq i := lt_trans hBpos hscalei
  have hleastPos : 0 < -leastSeq i := lt_trans (by positivity) hqi
  have hlog : A < Real.log (timeSeq i * scaleSeq i * (-leastSeq i)) := by
    have hprodPos : 0 < timeSeq i * scaleSeq i * (-leastSeq i) := by positivity
    exact Real.lt_log_iff_exp_lt hprodPos |>.2 hprod
  have hineq : scalarSeq i ≥ (-leastSeq i) *
      (Real.log (timeSeq i * scaleSeq i * (-leastSeq i)) - 3) :=
    hboundi hli
  have hlogPos : 0 < Real.log (timeSeq i * scaleSeq i * (-leastSeq i)) - 3 := by
    nlinarith [hlog, hAright]
  have hmulLog : scalarLimit + 1 + 4 * (q / 2) <
      (q / 2) * Real.log (timeSeq i * scaleSeq i * (-leastSeq i)) := by
    have hm := mul_lt_mul_of_pos_left hlog (by positivity : 0 < q / 2)
    have hAm := mul_le_mul_of_nonneg_left hAleft (by positivity : 0 ≤ q / 2)
    have hqa : (q / 2) * ((scalarLimit + 1) / (q / 2)) = scalarLimit + 1 := by
      field_simp
    have hAm' : scalarLimit + 1 + (q / 2) * 4 ≤ q / 2 * A := by
      calc
        scalarLimit + 1 + (q / 2) * 4 =
            (q / 2) * ((scalarLimit + 1) / (q / 2) + 4) := by
              rw [mul_add, hqa]
        _ ≤ q / 2 * A := hAm
    simpa [mul_comm] using hAm'.trans_lt hm
  have hmulTarget : scalarLimit + 1 < (q / 2) *
      (Real.log (timeSeq i * scaleSeq i * (-leastSeq i)) - 3) := by
    nlinarith [hmulLog, hq]
  have hmulLeast : (q / 2) *
      (Real.log (timeSeq i * scaleSeq i * (-leastSeq i)) - 3) <
      (-leastSeq i) * (Real.log (timeSeq i * scaleSeq i * (-leastSeq i)) - 3) :=
    mul_lt_mul_of_pos_right hqi hlogPos
  nlinarith

end DifferentialGeometry.PDE.RicciFlow
