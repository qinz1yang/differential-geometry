import DifferentialGeometry.Geometry.Flow.RicciFlow.Estimates.Distance.Regularity
import DifferentialGeometry.Geometry.Flow.RicciFlow.Estimates.Distance.LocalRicciBound
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.EventData

/-!
# 首出时刻的时间连续性（USC）：紧 stage 上的全局 `|Ric|` 界（O-CH11-P6ANCH4 G1，后缀 `_P6L4`）

首出时刻论证（`firstExit_distance_P6M4`）的"左延拓"一步：在 `s₀` 处 `d_{s₀}(p, q) < X` ⇒ `s₀` 左侧一小段
`[s₁, s₀]` 上仍 `d_s(p, q) < X`。只用**有限性**：stage carrier 紧 + `[a, s₀]` 紧且在 regular 内 ⇒ 全局
`|Ric| ≤ K₀ g`（`exists_tensor_quadratic_bound_on_compact`，`K₀` 不进任何估计）⇒
`riemannianEDistOf_exp_bounds_of_abs_ricciTensor_le`：`d_s ≤ e^{K₀ |s − s₀|} d_{s₀}`。
* `exists_abs_ricci_bound_P6L4`：紧时间段上的全局 `|Ric| ≤ K₀ g`；
* **`edist_lt_near_left_P6L4`**：USC 的左侧形。
-/

set_option autoImplicit false

noncomputable section

open Set Filter
open DifferentialGeometry.Geometry.Curvature DifferentialGeometry.Geometry.Riemannian
open DifferentialGeometry.Tensor0SBundle
open scoped Manifold ContDiff Topology ENNReal NNReal

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

universe u

/-- **紧时间段上的全局 `|Ric|` 界（`_P6L4`）**：stage carrier 紧、`[a, b] ⊆ D.carrier` ⇒
`∃ K₀ ≥ 0, |Ric_q(ξ, ξ)| ≤ K₀ g_q(ξ, ξ)`。 -/
theorem exists_abs_ricci_bound_P6L4 {P : OrientedThreeStage.{u}} {D : RealTimeInterval}
    (S : SolutionOn (I := ThreeModel) (M := P.Carrier) D) (hS : IsSolutionOn S)
    {a b : ℝ} (hab : Icc a b ⊆ D.carrier) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ q ∈ Icc a b, ∀ z : P.Carrier, ∀ ξ : TangentSpace ThreeModel z,
      |ricciTensor (S.base.metric q) z ξ ξ| ≤ K * (S.base.metric q).inner z ξ ξ := by
  obtain ⟨K, hK, hbound⟩ := exists_tensor_quadratic_bound_on_compact
    S.base.metric (fun t y => S.ricci t y) isCompact_Icc isCompact_univ
    (hS.smoothMetric.metricTensor_cont.mono hab) (hS.ricciCont.mono hab)
  refine ⟨K, hK, fun q hq z ξ => ?_⟩
  have hquad : quad02 (S.ricci q z) ξ = ricciTensor (S.base.metric q) z ξ ξ := by
    simp only [quad02, SolutionOn.ricci, SolutionFamily.ricci_apply, SolutionFamily.ricciAt]
    convert metricRicciAt_apply_eq_ricciTensor (S.base.metric q) z ξ ξ using 2
    funext i
    fin_cases i <;> rfl
  rw [← hquad]
  exact hbound q hq z (mem_univ z) ξ

/-- **USC 左侧形（`_P6L4`）**：`a < s₀`、`[a, s₀] ⊆ D.regular`、`d_{s₀}(p, q) < X` ⇒
`∃ s₁ ∈ [a, s₀)`，`[s₁, s₀]` 上 `d_s(p, q) < X`。 -/
theorem edist_lt_near_left_P6L4 {P : OrientedThreeStage.{u}} {D : RealTimeInterval}
    (S : SolutionOn (I := ThreeModel) (M := P.Carrier) D) (hS : IsSolutionOn S)
    {a s₀ : ℝ} (has : a < s₀) (hreg : Icc a s₀ ⊆ D.regular) (p q : P.Carrier) {X : ℝ≥0∞}
    (hX : riemannianEDistOf (S.base.metric s₀) p q < X) :
    ∃ s₁ : ℝ, a ≤ s₁ ∧ s₁ < s₀ ∧
      ∀ s ∈ Icc s₁ s₀, riemannianEDistOf (S.base.metric s) p q < X := by
  obtain ⟨K, -, hric⟩ := exists_abs_ricci_bound_P6L4 S hS
    (hreg.trans D.regular_subset)
  have hpde : ∀ r ∈ Icc a s₀, ∀ z : P.Carrier, ∀ v : TangentSpace ThreeModel z,
      HasDerivWithinAt (fun u => (S.base.metric u).inner z v v)
        (-2 * ricciTensor (S.base.metric r) z v v) (Icc a s₀) r := by
    intro r hr z v
    have hraw := metricDerivAt S hS ⟨r, hreg hr⟩ z v v
    simpa [SolutionFamily.ricciAt, metricRicciAt_apply_eq_ricciTensor] using
      hraw.hasDerivWithinAt (s := Icc a s₀)
  have hd : riemannianEDistOf (S.base.metric s₀) p q ≠ ⊤ := ne_top_of_lt hX
  have hcont : Continuous fun s : ℝ => ENNReal.ofReal (Real.exp (K * |s - s₀|)) :=
    ENNReal.continuous_ofReal.comp
      (Real.continuous_exp.comp (continuous_const.mul (continuous_id.sub continuous_const).abs))
  have hT : Tendsto (fun s : ℝ => ENNReal.ofReal (Real.exp (K * |s - s₀|)) *
      riemannianEDistOf (S.base.metric s₀) p q) (𝓝 s₀)
      (𝓝 (ENNReal.ofReal (Real.exp (K * |s₀ - s₀|)) *
        riemannianEDistOf (S.base.metric s₀) p q)) :=
    ENNReal.Tendsto.mul_const (hcont.tendsto s₀) (Or.inr hd)
  have h1 : ENNReal.ofReal (Real.exp (K * |s₀ - s₀|)) *
      riemannianEDistOf (S.base.metric s₀) p q = riemannianEDistOf (S.base.metric s₀) p q := by
    simp
  rw [h1] at hT
  obtain ⟨ε, hε, hball⟩ := Metric.eventually_nhds_iff.1 (hT.eventually_lt_const hX)
  refine ⟨max a (s₀ - ε / 2), le_max_left _ _, max_lt has (by linarith), fun s hs => ?_⟩
  have hsI : s ∈ Icc a s₀ := ⟨(le_max_left _ _).trans hs.1, hs.2⟩
  have hs0 : s₀ ∈ Icc a s₀ := ⟨has.le, le_rfl⟩
  have hexp := (riemannianEDistOf_exp_bounds_of_abs_ricciTensor_le (fun u => S.base.metric u)
    hpde hric hsI hs0 p q).2
  refine lt_of_le_of_lt hexp (hball ?_)
  have h2 : s₀ - ε / 2 ≤ s := (le_max_right _ _).trans hs.1
  rw [Real.dist_eq, abs_of_nonpos (by linarith [hs.2])]
  linarith

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
