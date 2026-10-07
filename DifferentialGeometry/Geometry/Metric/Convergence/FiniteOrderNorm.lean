import DifferentialGeometry.Geometry.Metric.Convergence.Defs
import Mathlib.Basic.ENNReal.BigOperators
import Mathlib.Data.Nat.Factorial.Basic

set_option autoImplicit false

noncomputable section

namespace DifferentialGeometry.CheegerGromovCompactness

open scoped Manifold ContDiff ENNReal BigOperators

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]

local instance : CompleteSpace E := FiniteDimensional.complete ℝ E

variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [T2Space M] [IsManifold I ∞ M]

def metricCkENormOn (K : Set M) (p : ℕ)
    (g₁ g₂ gRef : SmoothRiemannianMetric I M) : ℝ≥0∞ :=
  ∑ a ∈ Finset.range (p + 1),
    (a.factorial : ℝ≥0∞)⁻¹ *
      ⨆ x ∈ K, ENNReal.ofReal (metricDerivNorm (I := I) a g₁ g₂ gRef x)

@[simp] theorem metricCkENormOn_empty (p : ℕ)
    (g₁ g₂ gRef : SmoothRiemannianMetric I M) :
    metricCkENormOn (I := I) ∅ p g₁ g₂ gRef = 0 := by
  simp [metricCkENormOn]

@[simp] theorem metricCkENormOn_self (K : Set M) (p : ℕ)
    (g gRef : SmoothRiemannianMetric I M) :
    metricCkENormOn (I := I) K p g g gRef = 0 := by
  have hzero (a : ℕ) (x : M) : metricDerivNorm (I := I) a g g gRef x = 0 := by
    unfold metricDerivNorm metricDiffCovDerivAt
    rw [sub_self, (Tensor0SBundle.normSq0S_eq_zero_iff gRef x (a + 2) 0).mpr rfl,
      Real.sqrt_zero]
  simp [metricCkENormOn, hzero]

theorem metricCkENormOn_mono_set {K L : Set M} (hKL : K ⊆ L) (p : ℕ)
    (g₁ g₂ gRef : SmoothRiemannianMetric I M) :
    metricCkENormOn (I := I) K p g₁ g₂ gRef ≤
      metricCkENormOn (I := I) L p g₁ g₂ gRef := by
  apply Finset.sum_le_sum
  intro a _
  apply mul_le_mul_right
  exact iSup_le fun x => iSup_le fun hx => le_iSup_of_le x (le_iSup_of_le (hKL hx) le_rfl)

theorem metricCkENormOn_mono_order (K : Set M) {p q : ℕ} (hpq : p ≤ q)
    (g₁ g₂ gRef : SmoothRiemannianMetric I M) :
    metricCkENormOn (I := I) K p g₁ g₂ gRef ≤
      metricCkENormOn (I := I) K q g₁ g₂ gRef := by
  apply Finset.sum_le_sum_of_subset_of_nonneg
  · exact Finset.range_mono (Nat.add_le_add_right hpq 1)
  · intro _ _ _
    exact zero_le

theorem weighted_metricDerivNorm_le_metricCkENormOn
    (K : Set M) (p : ℕ) (g₁ g₂ gRef : SmoothRiemannianMetric I M)
    {a : ℕ} (ha : a ≤ p) {x : M} (hx : x ∈ K) :
    (a.factorial : ℝ≥0∞)⁻¹ * ENNReal.ofReal (metricDerivNorm (I := I) a g₁ g₂ gRef x) ≤
      metricCkENormOn (I := I) K p g₁ g₂ gRef := by
  have hsup : ENNReal.ofReal (metricDerivNorm (I := I) a g₁ g₂ gRef x) ≤
      ⨆ y ∈ K, ENNReal.ofReal (metricDerivNorm (I := I) a g₁ g₂ gRef y) :=
    le_iSup_of_le x (le_iSup_of_le hx le_rfl)
  unfold metricCkENormOn
  apply (mul_le_mul_right hsup _).trans
  apply Finset.single_le_sum
    (f := fun b : ℕ => (b.factorial : ℝ≥0∞)⁻¹ *
      ⨆ y ∈ K, ENNReal.ofReal (metricDerivNorm (I := I) b g₁ g₂ gRef y))
    (a := a) (s := Finset.range (p + 1))
  · intro _ _
    exact zero_le
  · exact Finset.mem_range.mpr (Nat.lt_succ_of_le ha)

theorem metricDerivNorm_zero_le_metricCkENormOn
    (K : Set M) (p : ℕ) (g₁ g₂ gRef : SmoothRiemannianMetric I M)
    {x : M} (hx : x ∈ K) :
    ENNReal.ofReal (metricDerivNorm (I := I) 0 g₁ g₂ gRef x) ≤
      metricCkENormOn (I := I) K p g₁ g₂ gRef := by
  simpa using weighted_metricDerivNorm_le_metricCkENormOn K p g₁ g₂ gRef (Nat.zero_le p) hx

theorem metricDerivNorm_zero_lt_of_metricCkENormOn_lt
    (K : Set M) (p : ℕ) (g₁ g₂ gRef : SmoothRiemannianMetric I M)
    {ε : ℝ}
    (hsmall : metricCkENormOn (I := I) K p g₁ g₂ gRef < ENNReal.ofReal ε)
    {x : M} (hx : x ∈ K) :
    metricDerivNorm (I := I) 0 g₁ g₂ gRef x < ε := by
  have hε : 0 < ε := ENNReal.ofReal_pos.mp (lt_of_le_of_lt zero_le hsmall)
  exact (ENNReal.ofReal_lt_ofReal_iff hε).mp
    ((metricDerivNorm_zero_le_metricCkENormOn K p g₁ g₂ gRef hx).trans_lt hsmall)

end DifferentialGeometry.CheegerGromovCompactness
