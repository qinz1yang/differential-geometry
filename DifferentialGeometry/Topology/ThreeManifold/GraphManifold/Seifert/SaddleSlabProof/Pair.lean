import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Seifert.SaddleSlabProof.Components

/-!
# Two one-saddle strips with the same model

Lane RG03c. Let `D`, `D'` be one-saddle strips with index-one charts of the same small radius
`r₀` and model radius at least `8 r₀`. Then the two flows are the same model flow in the charts:
`flow_chart_pair` follows a hyperbola `saddleK = const` through the annulus
`r₀ < |y| < 8 r₀` simultaneously in both strips and ends at the same model point.
`good_of_bounds` checks the annulus condition from bounds on `saddleQ` and `saddleK`.
-/

set_option autoImplicit false

noncomputable section

open Set Filter Function
open scoped Manifold ContDiff Topology
open DifferentialGeometry.Topology DifferentialGeometry.Topology.Morse
open DifferentialGeometry.Topology.Morse.CellAttachment (morseNorm morseNormalForm)

namespace GC.Seifert.SaddleSlabProof

theorem good_of_bounds {r : ℝ} (hr : 0 < r) {w : MorseModel 2}
    (hlo : r ^ 2 < 2 * |saddleQ w| ∨ r ^ 2 < 2 * |saddleK w|)
    (hhi : |saddleQ w| + |saddleK w| < 32 * r ^ 2) :
    r < morseNorm 2 w ∧ morseNorm 2 w < 8 * r := by
  have hq := two_abs_saddleQ_le w
  have hk := two_abs_saddleK_le w
  have hn := normSq_le_two_mul w
  constructor
  · by_contra h
    push Not at h
    rw [morseNorm_le_iff hr.le] at h
    rcases hlo with h' | h' <;> linarith
  · rw [morseNorm_lt_iff (by linarith)]
    nlinarith

theorem coord_zero_ne {w : MorseModel 2} (h : saddleK w ≠ 0 ∨ saddleQ w < 0) : w 0 ≠ 0 := by
  intro h0
  rcases h with h | h
  · apply h
    simp [saddleK, h0]
  · simp only [saddleQ, h0] at h
    nlinarith [sq_nonneg (w 1)]

theorem coord_one_ne {w : MorseModel 2} (h : saddleK w ≠ 0 ∨ 0 < saddleQ w) : w 1 ≠ 0 := by
  intro h1
  rcases h with h | h
  · apply h
    simp [saddleK, h1]
  · simp only [saddleQ, h1] at h
    nlinarith [sq_nonneg (w 0)]

variable {H H' : Type} [TopologicalSpace H] [TopologicalSpace H'] {M M' : Type*}
  [TopologicalSpace M] [ChartedSpace H M] [TopologicalSpace M'] [ChartedSpace H' M']
  {I : ModelWithCorners ℝ (MorseModel 2) H} {I' : ModelWithCorners ℝ (MorseModel 2) H'}
  [IsManifold I ∞ M] [IsManifold I' ∞ M'] [T2Space M] [T2Space M'] [I.Boundaryless]
  [I'.Boundaryless] {f : M → ℝ} {f' : M' → ℝ} {a b a' b' : ℝ} {p : M} {p' : M'}

omit [T2Space M] [I.Boundaryless] in
theorem annulus_of_good (D : GradientLikeStrip I f a b {p}) (hrm : 8 * (ch D).r₀ ≤ rmD D)
    {w : MorseModel 2} (hw : (ch D).r₀ < morseNorm 2 w ∧ morseNorm 2 w < 8 * (ch D).r₀) :
    w ∈ annulus D :=
  ⟨hw.1, hw.2.trans_le hrm⟩

theorem flow_chart_pair (D : GradientLikeStrip I f a b {p})
    (D' : GradientLikeStrip I' f' a' b' {p'})
    (hk : (ch D).k = 1) (hk' : (ch D').k = 1) (hr : (ch D').r₀ = (ch D).r₀)
    (hrm : 8 * (ch D).r₀ ≤ rmD D) (hrm' : 8 * (ch D').r₀ ≤ rmD D') {y : MorseModel 2} {T : ℝ}
    (i : Fin 2)
    (hgood : ∀ w : MorseModel 2, saddleK w = saddleK y →
      saddleQ w ∈ uIcc (saddleQ y) (saddleQ y - T) →
      ((ch D).r₀ < morseNorm 2 w ∧ morseNorm 2 w < 8 * (ch D).r₀) ∧ w i ≠ 0) :
    ∃ z, D.flow T ((ch D).χ y) = (ch D).χ z ∧ D'.flow T ((ch D').χ y) = (ch D').χ z ∧
      saddleQ z = saddleQ y - T ∧ saddleK z = saddleK y ∧ 0 < z i * y i := by
  obtain ⟨z, hz, hzq, hzk, hzs⟩ := flow_chart_eq D hk i fun w hk1 hq1 =>
    ⟨annulus_of_good D hrm (hgood w hk1 hq1).1, (hgood w hk1 hq1).2⟩
  obtain ⟨z', hz', hzq', hzk', hzs'⟩ := flow_chart_eq D' hk' i fun w hk1 hq1 =>
    ⟨annulus_of_good D' hrm' (by rw [hr]; exact (hgood w hk1 hq1).1), (hgood w hk1 hq1).2⟩
  have hyi : y i ≠ 0 := (hgood y rfl left_mem_uIcc).2
  have hsame : 0 < z i * z' i := by
    have h1 : 0 < (z i * y i) * (z' i * y i) := mul_pos hzs hzs'
    have h2 : 0 < y i * y i := mul_self_pos.mpr hyi
    nlinarith [mul_pos h1 h2]
  have hzz : z' = z := by
    fin_cases i
    · exact eq_of_saddle_zero (hzq'.trans hzq.symm) (hzk'.trans hzk.symm) (by
        simpa [mul_comm] using hsame)
    · exact eq_of_saddle_one (hzq'.trans hzq.symm) (hzk'.trans hzk.symm) (by
        simpa [mul_comm] using hsame)
  exact ⟨z, hz, hzz ▸ hz', hzq, hzk, hzs⟩

end GC.Seifert.SaddleSlabProof
