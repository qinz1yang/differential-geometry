import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Topology.Order.IntermediateValue
import Mathlib.Topology.Order.Compact
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas

/-!
# Cones over planar curves avoiding the origin (kernel of S-SHAPE2)

In a real normed space of dimension two, let `c : [a, b] → E` be a continuous curve that never
passes through `0` and whose endpoints are linearly independent. Then the cone
`{λ • c s | s ∈ [a, b], λ ∈ [0, 1]}` contains a nonempty open set
(`exists_isOpen_subset_cone_of_finrank_two`).

Route (review of the finite soul design, §5: a positive radial lower bound and one sweep of
directions, not only continuity of an angle):
* the radial lower bound `m = min ‖c‖ > 0` comes from compactness;
* in the basis `(c a, c b)` let `s₁` be the last time at which the second coordinate is `≤ 0`;
  it vanishes there, so `c s₁ = α • c a` with `α ≠ 0`;
* on `[s₁, b]` the second coordinate is positive, and the intermediate value theorem for the
  functional `f₀ - k f₁` hits every ray of slope `k` with `α k > 0` beyond radius `m`;
* hence the open set `{α f₀ > 0, f₁ > 0, ‖·‖ < m}` lies in the cone.
-/

set_option autoImplicit false

noncomputable section

open Set Metric

namespace DifferentialGeometry.Geometry.FiniteSoul

/-- **Planar cone lemma.** A continuous curve in a two-dimensional space that avoids the origin
and has linearly independent endpoints spans, by radial segments from the origin, a set with
nonempty interior. -/
theorem exists_isOpen_subset_cone_of_finrank_two {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] (hdim : Module.finrank ℝ E = 2) {c : ℝ → E} {a b : ℝ} (hab : a ≤ b)
    (hc : ContinuousOn c (Icc a b)) (hne : ∀ s ∈ Icc a b, c s ≠ 0)
    (hind : LinearIndependent ℝ ![c a, c b]) :
    ∃ U : Set E, IsOpen U ∧ U.Nonempty ∧
      U ⊆ {y | ∃ s ∈ Icc a b, ∃ t ∈ Icc (0 : ℝ) 1, y = t • c s} := by
  have : FiniteDimensional ℝ E := Module.finite_of_finrank_pos (by rw [hdim]; norm_num)
  set B : Module.Basis (Fin 2) ℝ E :=
    basisOfLinearIndependentOfCardEqFinrank hind (by simp [hdim]) with hBdef
  have hB0 : B 0 = c a := by simp [B]
  have hB1 : B 1 = c b := by simp [B]
  set f₀ : E →L[ℝ] ℝ := LinearMap.toContinuousLinearMap (B.coord 0) with hf₀def
  set f₁ : E →L[ℝ] ℝ := LinearMap.toContinuousLinearMap (B.coord 1) with hf₁def
  have hf₀ : ∀ y, f₀ y = B.repr y 0 := fun y => rfl
  have hf₁ : ∀ y, f₁ y = B.repr y 1 := fun y => rfl
  have hrepr : ∀ y : E, y = f₀ y • c a + f₁ y • c b := by
    intro y
    have h := B.sum_repr y
    rw [Fin.sum_univ_two, hB0, hB1] at h
    rw [hf₀, hf₁]
    exact h.symm
  have hf₀a : f₀ (c a) = 1 := by rw [hf₀, ← hB0, B.repr_self]; simp
  have hf₀b : f₀ (c b) = 0 := by rw [hf₀, ← hB1, B.repr_self]; simp
  have hf₁a : f₁ (c a) = 0 := by rw [hf₁, ← hB0, B.repr_self]; simp
  have hf₁b : f₁ (c b) = 1 := by rw [hf₁, ← hB1, B.repr_self]; simp
  -- the last time at which the second coordinate is `≤ 0`
  set h : ℝ → ℝ := fun s => f₁ (c s) with hhdef
  have hh : ContinuousOn h (Icc a b) := f₁.continuous.comp_continuousOn hc
  set T : Set ℝ := Icc a b ∩ h ⁻¹' Iic 0 with hTdef
  have hTcl : IsClosed T := hh.preimage_isClosed_of_isClosed isClosed_Icc isClosed_Iic
  have haT : a ∈ T := ⟨left_mem_Icc.2 hab, by simp [h, hf₁a]⟩
  have hTbdd : BddAbove T := ⟨b, fun s hs => hs.1.2⟩
  set s₁ := sSup T with hs₁def
  have hs₁T : s₁ ∈ T := hTcl.csSup_mem ⟨a, haT⟩ hTbdd
  have hgt : ∀ s ∈ Icc a b, s₁ < s → 0 < h s := by
    intro s hs hlt
    by_contra hle
    push Not at hle
    exact absurd (le_csSup hTbdd ⟨hs, hle⟩) (not_le.2 hlt)
  have hs₁ab : s₁ ∈ Icc a b := hs₁T.1
  have hs₁b : s₁ ≤ b := hs₁ab.2
  have hhs₁ : h s₁ = 0 := by
    have hcont : ContinuousOn h (Icc s₁ b) := hh.mono (Icc_subset_Icc hs₁ab.1 le_rfl)
    have h0 : (0 : ℝ) ∈ Icc (h s₁) (h b) := ⟨hs₁T.2, by simp [h, hf₁b]⟩
    obtain ⟨s, hs, hs0⟩ := intermediate_value_Icc hs₁b hcont h0
    have hsab : s ∈ Icc a b := ⟨hs₁ab.1.trans hs.1, hs.2⟩
    have hle : s ≤ s₁ := le_csSup hTbdd ⟨hsab, by simp [hs0]⟩
    rw [← le_antisymm hle hs.1]
    exact hs0
  set α : ℝ := f₀ (c s₁) with hαdef
  have hcs₁ : c s₁ = α • c a := by
    have h1 := hrepr (c s₁)
    have h2 : f₁ (c s₁) = 0 := hhs₁
    rw [h2, zero_smul, add_zero] at h1
    exact h1
  have hα : α ≠ 0 := by
    intro h0
    apply hne s₁ hs₁ab
    rw [hcs₁, h0, zero_smul]
  -- the radial lower bound
  obtain ⟨sm, hsm, hmin⟩ := isCompact_Icc.exists_isMinOn (nonempty_Icc.2 hab)
    (continuous_norm.comp_continuousOn hc)
  set m : ℝ := ‖c sm‖ with hmdef
  have hm : 0 < m := norm_pos_iff.2 (hne sm hsm)
  have hmle : ∀ s ∈ Icc a b, m ≤ ‖c s‖ := fun s hs => hmin hs
  refine ⟨{p | 0 < α * f₀ p} ∩ {p | 0 < f₁ p} ∩ ball 0 m, ?_, ?_, ?_⟩
  · exact ((isOpen_lt continuous_const (continuous_const.mul f₀.continuous)).inter
      (isOpen_lt continuous_const f₁.continuous)).inter isOpen_ball
  · set w : E := α • c a + c b with hwdef
    set t : ℝ := m / (2 * (‖w‖ + 1)) with htdef
    have hN : 0 < ‖w‖ + 1 := by positivity
    have ht : 0 < t := by positivity
    have hf₀w : f₀ w = α := by simp [w, hf₀a, hf₀b]
    have hf₁w : f₁ w = 1 := by simp [w, hf₁a, hf₁b]
    refine ⟨t • w, ⟨⟨?_, ?_⟩, ?_⟩⟩
    · change 0 < α * f₀ (t • w)
      rw [map_smul, hf₀w, smul_eq_mul]
      have : 0 < α * α := mul_self_pos.2 hα
      nlinarith
    · change 0 < f₁ (t • w)
      rw [map_smul, hf₁w, smul_eq_mul, mul_one]
      exact ht
    · rw [mem_ball_zero_iff, norm_smul, Real.norm_of_nonneg ht.le]
      have h1 : t * ‖w‖ ≤ t * (‖w‖ + 1) := by nlinarith
      have h2 : t * (‖w‖ + 1) = m / 2 := by
        rw [htdef]
        field_simp
      linarith
  · rintro p ⟨⟨hp0, hp1⟩, hpm⟩
    change 0 < α * f₀ p at hp0
    change 0 < f₁ p at hp1
    rw [mem_ball_zero_iff] at hpm
    set k : ℝ := f₀ p / f₁ p with hkdef
    have hαk : 0 < α * k := by
      rw [hkdef, ← mul_div_assoc]
      exact div_pos hp0 hp1
    set F : ℝ → ℝ := fun s => α * (f₀ (c s) - k * f₁ (c s)) with hFdef
    have hF : ContinuousOn F (Icc s₁ b) := by
      have h1 : ContinuousOn (fun s => f₀ (c s) - k * f₁ (c s)) (Icc a b) :=
        (f₀.continuous.comp_continuousOn hc).sub
          (continuousOn_const.mul (f₁.continuous.comp_continuousOn hc))
      exact (continuousOn_const.mul h1).mono (Icc_subset_Icc hs₁ab.1 le_rfl)
    have hFs₁ : F s₁ = α * α := by
      simp only [F]
      rw [show f₁ (c s₁) = 0 from hhs₁]
      ring
    have hFb : F b = -(α * k) := by
      simp only [F]
      rw [hf₀b, hf₁b]
      ring
    have h0 : (0 : ℝ) ∈ Icc (F b) (F s₁) := by
      rw [hFs₁, hFb]
      exact ⟨by linarith, (mul_self_pos.2 hα).le⟩
    obtain ⟨s, hs, hFs⟩ := intermediate_value_Icc' hs₁b hF h0
    have hsne : s ≠ s₁ := by
      rintro rfl
      rw [hFs₁] at hFs
      exact (mul_self_pos.2 hα).ne' hFs
    have hsab : s ∈ Icc a b := ⟨hs₁ab.1.trans hs.1, hs.2⟩
    have hhs : 0 < f₁ (c s) := hgt s hsab (lt_of_le_of_ne hs.1 (Ne.symm hsne))
    have hf₀s : f₀ (c s) = k * f₁ (c s) := by
      have h1 : α * (f₀ (c s) - k * f₁ (c s)) = 0 := hFs
      rcases mul_eq_zero.1 h1 with h2 | h2
      · exact absurd h2 hα
      · linarith
    set μ : ℝ := f₁ (c s) / f₁ p with hμdef
    have hμ : 0 < μ := div_pos hhs hp1
    have hcs : c s = μ • p := by
      have h1 := hrepr (c s)
      have h2 := hrepr p
      rw [h1, hf₀s]
      conv_rhs => rw [h2]
      rw [smul_add, smul_smul, smul_smul]
      congr 2
      · rw [hμdef, hkdef]
        field_simp
      · rw [hμdef]
        field_simp
    have hμ1 : 1 < μ := by
      by_contra hle
      push Not at hle
      have h1 : ‖c s‖ = μ * ‖p‖ := by
        rw [hcs, norm_smul, Real.norm_of_nonneg hμ.le]
      have h2 : μ * ‖p‖ ≤ ‖p‖ := by
        have := norm_nonneg p
        nlinarith
      linarith [hmle s hsab]
    refine ⟨s, hsab, μ⁻¹, ⟨inv_nonneg.2 hμ.le, inv_le_one_of_one_le₀ hμ1.le⟩, ?_⟩
    rw [hcs, smul_smul, inv_mul_cancel₀ hμ.ne', one_smul]

end DifferentialGeometry.Geometry.FiniteSoul
