import DifferentialGeometry.Geometry.Curvature.DimensionThree.HamiltonIvey.Region

noncomputable section

open DifferentialGeometry.Geometry.Curvature.DimensionThree

namespace DifferentialGeometry.Geometry.Curvature

def fixedHamiltonIveyBarrier (a X : ℝ) : ℝ :=
  X * (Real.log (a * X) - 3)

def fixedHamiltonIveyRegion (a : ℝ) : Set (ℝ × ℝ) :=
  {p | 0 ≤ p.2 ∨ fixedHamiltonIveyBarrier a (-p.2) ≤ p.1}

theorem fixedHamiltonIveyBarrier_eq_hamiltonIveyBarrier (a X : ℝ) :
    fixedHamiltonIveyBarrier a X = hamiltonIveyBarrier a⁻¹ 0 X := by
  simp only [fixedHamiltonIveyBarrier, hamiltonIveyBarrier, div_inv_eq_mul,
    mul_zero, add_zero, Real.log_one]
  rw [mul_comm X a]

theorem fixedHamiltonIveyBarrier_monotoneOn {a : ℝ} (ha : 0 < a) :
    MonotoneOn (fixedHamiltonIveyBarrier a) (Set.Ici (Real.exp 2 / a)) := by
  intro x hx y hy hxy
  have hthreshold : a⁻¹ * Real.exp 2 / (1 + 2 * a⁻¹ * 0) = Real.exp 2 / a := by
    simp only [mul_zero, add_zero, div_eq_mul_inv]
    ring
  rw [fixedHamiltonIveyBarrier_eq_hamiltonIveyBarrier,
    fixedHamiltonIveyBarrier_eq_hamiltonIveyBarrier]
  apply hamiltonIveyBarrier_monotoneOn_of_exp_two_le (inv_pos.mpr ha) (le_refl 0)
  · simpa only [hthreshold] using hx
  · simpa only [hthreshold] using hy
  · exact hxy

theorem mem_fixedHamiltonIveyRegion_of_le
    {a R₀ ν₀ R₁ ν₁ : ℝ} (ha : 0 < a)
    (hR : R₀ ≤ R₁) (hν : ν₀ ≤ ν₁) (hR₁ : 0 ≤ R₁)
    (hmem : (R₀, ν₀) ∈ fixedHamiltonIveyRegion a) :
    (R₁, ν₁) ∈ fixedHamiltonIveyRegion a := by
  change 0 ≤ ν₁ ∨ fixedHamiltonIveyBarrier a (-ν₁) ≤ R₁
  by_cases hν₁ : 0 ≤ ν₁
  · exact Or.inl hν₁
  right
  have hX₁ : 0 < -ν₁ := neg_pos.mpr (lt_of_not_ge hν₁)
  have hXX : -ν₁ ≤ -ν₀ := neg_le_neg hν
  have hbar₀ : fixedHamiltonIveyBarrier a (-ν₀) ≤ R₀ := by
    rcases hmem with hnonneg | hbar
    · exact False.elim (hν₁ (hnonneg.trans hν))
    · exact hbar
  by_cases hbar₁ : fixedHamiltonIveyBarrier a (-ν₁) ≤ 0
  · exact hbar₁.trans hR₁
  have hpos : 0 < fixedHamiltonIveyBarrier a (-ν₁) := lt_of_not_ge hbar₁
  have hlog : 3 < Real.log (a * (-ν₁)) := by
    have h := (mul_pos_iff_of_pos_left hX₁).mp hpos
    linarith
  have hthreshold : Real.exp 2 / a ≤ -ν₁ := by
    rw [div_le_iff₀ ha]
    rw [mul_comm (-ν₁) a]
    exact (Real.le_log_iff_exp_le (mul_pos ha hX₁)).mp (by linarith)
  exact ((fixedHamiltonIveyBarrier_monotoneOn ha) hthreshold
    (hthreshold.trans hXX) hXX).trans (hbar₀.trans hR)

theorem mem_fixedHamiltonIveyRegion_and_scalar_lower_bound_of_le
    {a L R₀ ν₀ R₁ ν₁ : ℝ} (ha : 0 < a)
    (hR : R₀ ≤ R₁) (hν : ν₀ ≤ ν₁) (hR₁ : 0 ≤ R₁)
    (hmem : (R₀, ν₀) ∈ fixedHamiltonIveyRegion a) (hL : L ≤ R₀) :
    (R₁, ν₁) ∈ fixedHamiltonIveyRegion a ∧ L ≤ R₁ :=
  ⟨mem_fixedHamiltonIveyRegion_of_le ha hR hν hR₁ hmem, hL.trans hR⟩

theorem fixedHamiltonIveyBarrier_scale {c : ℝ} (hc : 0 < c) (a X : ℝ) :
    fixedHamiltonIveyBarrier (c * a) (X / c) = fixedHamiltonIveyBarrier a X / c := by
  have harg : (c * a) * (X / c) = a * X := by field_simp [hc.ne']
  simp only [fixedHamiltonIveyBarrier, harg]
  ring

theorem mem_fixedHamiltonIveyRegion_scale_iff
    {c : ℝ} (hc : 0 < c) (a R ν : ℝ) :
    (R / c, ν / c) ∈ fixedHamiltonIveyRegion (c * a) ↔
      (R, ν) ∈ fixedHamiltonIveyRegion a := by
  change (0 ≤ ν / c ∨ fixedHamiltonIveyBarrier (c * a) (-(ν / c)) ≤ R / c) ↔ _
  rw [← neg_div, fixedHamiltonIveyBarrier_scale hc]
  rw [div_le_div_iff_of_pos_right hc, le_div_iff₀ hc, zero_mul]
  rfl

theorem two_mul_hamiltonIveyBarrier_eq_fixedHamiltonIveyBarrier
    {K t X : ℝ} (hK : 0 < K) (ht : 0 ≤ t) (hX : 0 < X) :
    2 * hamiltonIveyBarrier K t (X / 2) =
      fixedHamiltonIveyBarrier ((2 * K)⁻¹ + t) X := by
  have hD : 0 < 1 + 2 * K * t := by positivity
  have harg : (X / 2 / K) * (1 + 2 * K * t) = ((2 * K)⁻¹ + t) * X := by
    field_simp [hK.ne']
  unfold hamiltonIveyBarrier fixedHamiltonIveyBarrier
  rw [← Real.log_mul (by positivity : X / 2 / K ≠ 0) hD.ne', harg]
  ring

end DifferentialGeometry.Geometry.Curvature

open Filter Set
open scoped Topology

namespace DifferentialGeometry.Geometry.Curvature

theorem mem_fixedHamiltonIveyRegion_of_tendsto
    {ι : Type*} {l : Filter ι} [NeBot l] {a R ν : ι → ℝ} {a₀ R₀ ν₀ : ℝ}
    (ha₀ : 0 < a₀) (ha : Tendsto a l (𝓝 a₀)) (hR : Tendsto R l (𝓝 R₀))
    (hν : Tendsto ν l (𝓝 ν₀))
    (hregion : ∀ᶠ i in l, (R i, ν i) ∈ fixedHamiltonIveyRegion (a i)) :
    (R₀, ν₀) ∈ fixedHamiltonIveyRegion a₀ := by
  by_cases hnonneg : 0 ≤ ν₀
  · exact Or.inl hnonneg
  have hnegative : ν₀ < 0 := lt_of_not_ge hnonneg
  have harg : a₀ * (-ν₀) ≠ 0 := (mul_pos ha₀ (neg_pos.mpr hnegative)).ne'
  have hbar : Tendsto (fun i => fixedHamiltonIveyBarrier (a i) (-(ν i))) l
      (𝓝 (fixedHamiltonIveyBarrier a₀ (-ν₀))) :=
    hν.neg.mul (((ha.mul hν.neg).log harg).sub_const 3)
  apply Or.inr
  apply le_of_tendsto_of_tendsto hbar hR
  filter_upwards [hregion, hν.eventually_lt_const hnegative] with i hi hni
  rcases hi with hpos | hbound
  · exact False.elim ((not_le_of_gt hni) hpos)
  · exact hbound

end DifferentialGeometry.Geometry.Curvature

namespace DifferentialGeometry.Geometry.Curvature

theorem neg_le_max_of_mem_fixedHamiltonIveyRegion
    {a₀ a R ν B : ℝ} (ha₀ : 0 < a₀) (ha : a₀ ≤ a)
    (h : (R, ν) ∈ fixedHamiltonIveyRegion a) (hR : R ≤ B) :
    -ν ≤ max B (Real.exp 4 / a₀) := by
  by_cases hsmall : -ν ≤ Real.exp 4 / a₀
  · exact hsmall.trans (le_max_right _ _)
  have hlarge : Real.exp 4 / a₀ < -ν := lt_of_not_ge hsmall
  have hX : 0 < -ν := (div_pos (Real.exp_pos 4) ha₀).trans hlarge
  have hbar : fixedHamiltonIveyBarrier a (-ν) ≤ R := by
    rcases h with h | h
    · exact (not_lt_of_ge h (neg_pos.mp hX)).elim
    · exact h
  have hexp : Real.exp 4 ≤ a * (-ν) := by
    have hmul := (div_lt_iff₀ ha₀).mp hlarge
    have hm := mul_le_mul_of_nonneg_right ha hX.le
    nlinarith
  have hlog : 4 ≤ Real.log (a * (-ν)) :=
    (Real.le_log_iff_exp_le (mul_pos (ha₀.trans_le ha) hX)).mpr hexp
  have hlin : -ν ≤ fixedHamiltonIveyBarrier a (-ν) := by
    dsimp only [fixedHamiltonIveyBarrier]
    nlinarith
  exact (hlin.trans (hbar.trans hR)).trans (le_max_left _ _)

end DifferentialGeometry.Geometry.Curvature
