import DifferentialGeometry.Geometry.Curvature.Coordinates.MetricJet.UniformConvergence
import DifferentialGeometry.Geometry.Curvature.Riemann.FiniteMetric
import DifferentialGeometry.Geometry.Geodesic.FiniteMetric.Speed

/-!
# The sectional curvature of a finite-order metric is bounded on compact sets

* `exists_abs_coefficientSectional_le` (kernel): for a `C²` symmetric positive coefficient field `c`
  on an open set `U` and a compact `L ⊆ U`, `|coefficientSectional c y v w| ≤ Λ` on `L`, for ALL pairs
  `(v, w)` (the degenerate pairs give `0`). Route: orthogonalize the pair inside its span
  (`coefficientSectional_eq_of_span_eq`), bound the numerator by `C |v|² |w|²`
  (`exists_eventually_abs_coefficientRm04_le` for the constant sequence) and the denominator from
  below by uniform coercivity.
* `exists_abs_sectionalCurvature_le_of_isCompact` (binding): the same for
  `Bundle.ContMDiffRiemannianMetric.sectionalCurvature` of a `C^(r+1)` metric, `2 ≤ r`, on a compact
  subset of the manifold (finite cover by chart balls, `IsCompact.induction_on`).
-/

set_option autoImplicit false

noncomputable section

open Set Filter Metric Bundle
open scoped Topology ContDiff Manifold

namespace DifferentialGeometry.Analysis

open DifferentialGeometry.CheegerGromovCompactness (MapCPConvergenceOn mapDerivNorm)

/-- A constant sequence converges to its value in every `C^p` sense. -/
theorem mapCPConvergenceOn_const {V F : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    [NormedAddCommGroup F] [NormedSpace ℝ F] (K : Set V) (p : ℕ) (c : V → F) :
    MapCPConvergenceOn K p (fun _ => c) c := by
  intro ε hε
  refine ⟨0, fun k _ r _ x _ => ?_⟩
  have h0 : (fun y => c y - c y) = fun _ => (0 : F) := funext fun y => sub_self (c y)
  simp only [mapDerivNorm, h0, iteratedFDeriv_fun_zero, Pi.zero_apply, norm_zero]
  exact hε.le

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

/-- **Kernel.** The coefficient sectional curvature of a `C²` positive symmetric field is bounded on
a compact subset of its domain, uniformly in the pair. -/
theorem exists_abs_coefficientSectional_le {U L : Set E} {c : E → E →L[ℝ] E →L[ℝ] ℝ}
    (hU : IsOpen U) (hL : IsCompact L) (hLU : L ⊆ U) (hc : ContDiffOn ℝ 2 c U)
    (hsymm : ∀ y ∈ U, ∀ u v, c y u v = c y v u) (hpos : ∀ y ∈ U, ∀ v, v ≠ 0 → 0 < c y v v) :
    ∃ Λ : ℝ, 0 ≤ Λ ∧ ∀ y ∈ L, ∀ v w : E, |coefficientSectional c y v w| ≤ Λ := by
  obtain ⟨C, hC0, hCev⟩ := exists_eventually_abs_coefficientRm04_le hU hL hLU (fun _ => hc) hc
    hpos (mapCPConvergenceOn_const L 2 c)
  obtain ⟨k, hC⟩ := hCev.exists
  obtain ⟨lam, hlam, hco⟩ := exists_uniform_coercive_of_continuousOn hL (hc.continuousOn.mono hLU)
    (fun y hy => hpos y (hLU hy))
  refine ⟨C / lam ^ 2, by positivity, fun y hy v w => ?_⟩
  have hyU := hLU hy
  have hs := hsymm y hyU
  by_cases hgram : c y v v * c y w w - (c y v w) ^ 2 = 0
  · rw [coefficientSectional_def, hgram, div_zero, abs_zero]
    positivity
  have hv : v ≠ 0 := by
    rintro rfl
    apply hgram
    simp
  have hvv : 0 < c y v v := hpos y hyU v hv
  set a : ℝ := c y v w / c y v v with ha
  set w' : E := w - a • v with hw'
  have hvw' : c y v w' = 0 := by
    rw [hw', map_sub, map_smul, smul_eq_mul, ha]
    field_simp
    ring
  have hw'w' : c y w' w' = (c y v v * c y w w - (c y v w) ^ 2) / c y v v := by
    rw [hw']
    simp only [map_sub, map_smul, sub_apply, smul_apply,
      smul_eq_mul]
    rw [hs w v, ha]
    field_simp
    ring
  have hgram_pos : 0 < c y v v * c y w w - (c y v w) ^ 2 :=
    lt_of_le_of_ne (bilin_gram_nonneg hs (fun z => by
      by_cases hz : z = 0
      · rw [hz]; simp
      · exact (hpos y hyU z hz).le) v w) (Ne.symm hgram)
  have hw'pos : 0 < c y w' w' := by
    rw [hw'w']
    exact div_pos hgram_pos hvv
  have hli : LinearIndependent ℝ ![v, w'] := by
    rw [LinearIndependent.pair_iff]
    intro s t hst
    have h1 := congrArg (fun z => c y v z) hst
    simp only [map_add, map_smul, smul_eq_mul, map_zero, hvw', mul_zero, add_zero] at h1
    have hs0 : s = 0 := by
      rcases mul_eq_zero.mp h1 with h | h
      · exact h
      · exact absurd h hvv.ne'
    refine ⟨hs0, ?_⟩
    rw [hs0, zero_smul, zero_add] at hst
    rcases smul_eq_zero.mp hst with h | h
    · exact h
    · rw [h] at hw'pos
      simp at hw'pos
  have hspan : Submodule.span ℝ ({v, w'} : Set E) = Submodule.span ℝ ({v, w} : Set E) := by
    apply le_antisymm
    · rw [Submodule.span_le]
      intro z hz
      rcases hz with rfl | rfl
      · exact Submodule.subset_span (by simp)
      · rw [hw']
        exact Submodule.sub_mem _ (Submodule.subset_span (by simp))
          (Submodule.smul_mem _ _ (Submodule.subset_span (by simp)))
    · rw [Submodule.span_le]
      intro z hz
      rcases hz with rfl | rfl
      · exact Submodule.subset_span (by simp)
      · have : z = w' + a • v := by rw [hw']; abel
        rw [this]
        exact Submodule.add_mem _ (Submodule.subset_span (by simp))
          (Submodule.smul_mem _ _ (Submodule.subset_span (by simp)))
  have hcoy : IsCoercive (c y) := (c y).isCoercive_of_posDef (hpos y hyU)
  have heq := coefficientSectional_eq_of_span_eq (hc.contDiffAt (hU.mem_nhds hyU))
    (eventually_of_mem (hU.mem_nhds hyU) hsymm) hcoy hli hspan
  rw [← heq, coefficientSectional_def, hvw']
  have hden : 0 < c y v v * c y w' w' := mul_pos hvv hw'pos
  have hnum := hC y hy v w'
  have hv2 : lam * ‖v‖ ^ 2 ≤ c y v v := hco y hy v
  have hw2 : lam * ‖w'‖ ^ 2 ≤ c y w' w' := hco y hy w'
  rw [show c y v v * c y w' w' - (0 : ℝ) ^ 2 = c y v v * c y w' w' by ring, abs_div,
    abs_of_pos hden, div_le_div_iff₀ hden (by positivity)]
  have hprod : lam ^ 2 * (‖v‖ ^ 2 * ‖w'‖ ^ 2) ≤ c y v v * c y w' w' := by
    have := mul_le_mul hv2 hw2 (by positivity) hvv.le
    nlinarith
  calc |coefficientRm04 c y v w' w' v| * lam ^ 2 ≤ C * ‖v‖ ^ 2 * ‖w'‖ ^ 2 * lam ^ 2 :=
        mul_le_mul_of_nonneg_right hnum (by positivity)
    _ = C * (lam ^ 2 * (‖v‖ ^ 2 * ‖w'‖ ^ 2)) := by ring
    _ ≤ C * (c y v v * c y w' w') := mul_le_mul_of_nonneg_left hprod hC0

end DifferentialGeometry.Analysis

namespace Bundle.ContMDiffRiemannianMetric

variable {E H M : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

/-- **Sectional curvature is bounded on compact sets** (finite-order metric, `2 ≤ r`). -/
theorem exists_abs_sectionalCurvature_le_of_isCompact {r : ℕ∞}
    (g : ContMDiffRiemannianMetric I ((r : ℕ∞ω) + 1) E (TangentSpace I : M → Type _))
    (hr : 2 ≤ r) {K : Set M} (hK : IsCompact K) :
    ∃ Λ : ℝ, 0 ≤ Λ ∧ ∀ q ∈ K, ∀ v w : TangentSpace I q, |g.sectionalCurvature q v w| ≤ Λ := by
  have h2 : ((2 : ℕ∞) : ℕ∞ω) ≤ (r : ℕ∞ω) := by exact_mod_cast hr
  have hn : (2 : ℕ∞ω) ≤ (r : ℕ∞ω) + 1 :=
    calc (2 : ℕ∞ω) = ((2 : ℕ∞) : ℕ∞ω) := by norm_num
      _ ≤ (r : ℕ∞ω) := h2
      _ ≤ (r : ℕ∞ω) + 1 := le_self_add
  refine hK.induction_on (p := fun s => ∃ Λ : ℝ, 0 ≤ Λ ∧ ∀ q ∈ s, ∀ v w : TangentSpace I q,
      |g.sectionalCurvature q v w| ≤ Λ) ⟨0, le_rfl, fun q hq => absurd hq (notMem_empty q)⟩
    (fun s t hst ⟨Λ, hΛ, h⟩ => ⟨Λ, hΛ, fun q hq => h q (hst hq)⟩)
    (fun s t ⟨Λ₁, h₁0, h₁⟩ ⟨Λ₂, h₂0, h₂⟩ => ⟨max Λ₁ Λ₂, le_max_of_le_left h₁0, fun q hq v w => by
      rcases hq with hq | hq
      · exact (h₁ q hq v w).trans (le_max_left _ _)
      · exact (h₂ q hq v w).trans (le_max_right _ _)⟩) ?_
  intro q₀ _
  set y₀ := extChartAt I q₀ q₀
  have hT : IsOpen (extChartAt I q₀).target := isOpen_extChartAt_target q₀
  obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.mp hT y₀ (mem_extChartAt_target q₀)
  have hLsub : closedBall y₀ (ε / 2) ⊆ (extChartAt I q₀).target :=
    (closedBall_subset_ball (by linarith)).trans hball
  have hc : ContDiffOn ℝ 2 (g.chartInner q₀) (extChartAt I q₀).target :=
    (g.contDiffOn_chartInner q₀).of_le (by
      calc (2 : ℕ∞ω) = ((2 : ℕ∞) : ℕ∞ω) := by norm_num
        _ ≤ (r : ℕ∞ω) := h2)
  have hpos : ∀ y ∈ (extChartAt I q₀).target, ∀ v : E, v ≠ 0 → 0 < g.chartInner q₀ y v v := by
    intro y hy v hv
    obtain ⟨C, hC, hCv⟩ := g.isCoercive_chartInner q₀ hy
    exact lt_of_lt_of_le (mul_pos (mul_pos hC (norm_pos_iff.mpr hv)) (norm_pos_iff.mpr hv))
      (hCv v)
  obtain ⟨Λ, hΛ, hbound⟩ := DifferentialGeometry.Analysis.exists_abs_coefficientSectional_le hT
    (isCompact_closedBall y₀ (ε / 2)) hLsub hc (fun y _ u v => g.chartInner_symm q₀ y u v) hpos
  refine ⟨(extChartAt I q₀).source ∩ extChartAt I q₀ ⁻¹' closedBall y₀ (ε / 2),
    mem_nhdsWithin_of_mem_nhds (inter_mem (extChartAt_source_mem_nhds q₀)
      ((continuousAt_extChartAt q₀).preimage_mem_nhds
        (closedBall_mem_nhds y₀ (by linarith : (0 : ℝ) < ε / 2)))), Λ, hΛ, ?_⟩
  intro q hq v w
  rw [sectionalCurvature_eq_coefficientSectional g hn
    (DifferentialGeometry.PartialDiffeomorph.extChartAt I 3 q₀) hq.1 v w]
  exact hbound _ hq.2 _ _

end Bundle.ContMDiffRiemannianMetric
