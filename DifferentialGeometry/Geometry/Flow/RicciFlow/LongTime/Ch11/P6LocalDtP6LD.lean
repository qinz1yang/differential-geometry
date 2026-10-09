import DifferentialGeometry.Geometry.Flow.RicciFlow.Estimates.Shi.LaplacianInputRegularWindow
import DifferentialGeometry.Geometry.Flow.RicciFlow.Estimates.ScalarLaplacian
import DifferentialGeometry.Geometry.Flow.RicciFlow.Estimates.Shi.PositiveTimeUniform
import DifferentialGeometry.Geometry.Flow.RicciFlow.Evolution.Scalar.IntrinsicDerivation
import DifferentialGeometry.Geometry.Flow.RicciFlow.Uniqueness.Forward.Data.UniformBounds
import DifferentialGeometry.Geometry.Flow.RicciFlow.Solution.Restriction
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.EventData
import DifferentialGeometry.Geometry.Metric.Distance.LocalBall

set_option autoImplicit false

/-!
# 局部 Dt 生产：零阶抛物窗 + 尺度不变局部 Shi + scalar 演化方程（O-CH11-LOCALDT G1，后缀 `_P6LD`）

**更正（G0）**：NATIVE-NR state:80 说"树内 `IsSolutionOn.scalarTime` 只给 `R` 的时间可微性，**没有**
`∂ₜR = ΔR + 2|Ric|²`"——这是只看了 `structure IsSolutionOn` 的字段表。发展方程不是字段，而是由
`equation : MetricVariationEquationOn` 推出的**定理** `scalarEvolution_of_isSolution`
（`Evolution/Scalar/IntrinsicDerivation:682`，打包为 `scalar_curvature_evolution` :736，亦入
`IsSmoothSolutionOn.scalarEvolution`）。stage flow 的桥是零行：`IncomingSlab.equation : IsSolutionOn flow`。

本文件（PROVED，无新前提）：
* `abs_derivWithin_scalar_le_jets_P6LD`：regular 时刻 `t`，`|∂ₜ⁻R(t, x)| ≤ 3⁶·√|∇²Rm|² + 2·3⁴·|Rm|²`
  （`scalar_curvature_evolution` + `abs_laplacian_scalar_le_second_curvature` + `ricciSq_le_rm04`）。
* `localDt_of_curvature_window_P6LD`（**G1 主定理**，尺度不变）：对任意 `c, r > 0` 存在 `C = C(c, r)`：
  若 `|Rm| ≤ K` 于 `B_{g(t − c/K)}(p, r/√K) × [t − c/K, t]`，且 flow 在 `t − c/K` 之前、`t` 之后都还有
  regular 余量（`Ico lo hi ⊆ carrier`、`Ioo lo hi ⊆ regular`、`lo < t − c/K`、`t < hi`），则在半径 `r/(2√K)`
  的球上 `|∂ₜ⁻R(t, x)| ≤ C·K²`。常数只依赖 `(c, r)`
  （`shi_local_all_orders_curvature_scale_of_solution_uniform`，
  `Estimates/Shi/LaplacianInputRegularWindow:456`，时间平移 + `timeRestrict` 到 `closedOpen`）。
* `localDt_of_scalar_window_P6LD`：再加点态 `K ≤ A·R(t, x)` ⇒ `|∂ₜ⁻R| ≤ C·A²·R²`
  （X / `hslabsLoc` 的 `C·R²` 形）。
* `IncomingSlab.localDt_P6LD`：stage slab flow（`flow / equation`）上的实例化：窗口在 slab 内部
  （`a < t − c/K`、`t < s`）即可。
**正深度版**：窗口下端严格在 slab birth 之后；newborn（深度 `< c/K`）情形不在本文件。
-/

noncomputable section

open Set Bundle
open DifferentialGeometry DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.CheegerGromovCompactness
open DifferentialGeometry.PDE.RicciFlow DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
open scoped Manifold ContDiff Topology ENNReal

namespace GC.LongTime.Ch11

universe u

private local instance : NeZero (Module.finrank ℝ ThreeSpace) := ⟨by simp [ThreeSpace]⟩

/-- `dim ThreeSpace = 3`（常数换算用）。 -/
theorem finrank_threeSpace_P6LD : (Module.finrank ℝ ThreeSpace : ℝ) = 3 := by
  simp [ThreeSpace]

/-- **点态核（PROVED）**：regular 时刻上 `|∂ₜ⁻R| ≤ 3⁶·|∇²Rm| + 2·3⁴·|Rm|²`，全部写成 `curvDerivNormSq`。 -/
theorem abs_derivWithin_scalar_le_jets_P6LD {P : OrientedThreeStage.{u}} {D : RealTimeInterval}
    (S : SolutionOn (I := ThreeModel) (M := P.Carrier) D) (hS : IsSolutionOn S)
    {t : ℝ} (ht : t ∈ D.regular) (x : P.Carrier) :
    |derivWithin (fun v => S.scalar v x) (Iic t) t| ≤
      3 ^ 6 * Real.sqrt (curvDerivNormSq 2 (S.base.metric t) x) +
        2 * 3 ^ 4 * curvDerivNormSq 0 (S.base.metric t) x := by
  have hd := (scalar_curvature_evolution S hS ⟨t, ht⟩ x).hasDerivAt (D.regular_mem_nhds ht)
  rw [hd.hasDerivWithinAt.derivWithin (uniqueDiffWithinAt_Iic t)]
  have hlap := Perelman.CanonicalNeighborhood.abs_laplacian_scalar_le_second_curvature S t x
  have hric := ricciSq_le_rm04 (I := ThreeModel) (S.base.metric t) (S.base.metric t) x
  have hric0 := Tensor0SBundle.normSq0S_nonneg (I := ThreeModel) (S.family.metric t) x 2
    (S.ricci t x)
  rw [finrank_threeSpace_P6LD] at hlap hric
  rw [nablaKRm04NormSqIntrinsic_eq_curvDerivNormSq] at hlap
  have h0 : nablaKRm04NormSqIntrinsic (I := ThreeModel) S 0 t x =
      curvDerivNormSq 0 (S.base.metric t) x :=
    nablaKRm04NormSqIntrinsic_eq_curvDerivNormSq S 0 t x
  have hric' : Tensor0SBundle.normSq0S (I := ThreeModel) (S.family.metric t) x 2 (S.ricci t x) ≤
      3 ^ 4 * curvDerivNormSq 0 (S.base.metric t) x := by
    rw [← h0]
    exact hric
  calc
    _ ≤ |laplacianAt (I := ThreeModel) (flowG S) t (S.scalar t) x| +
        |2 * Tensor0SBundle.normSq0S (I := ThreeModel) (S.family.metric t) x 2 (S.ricci t x)| :=
      abs_add_le _ _
    _ ≤ _ := by
      rw [abs_of_nonneg (mul_nonneg (by norm_num) hric0)]
      linarith

/-- **G1 主定理（PROVED，尺度不变）**：`|Rm| ≤ K` 于 `B_{g(t − c/K)}(p, r/√K) × [t − c/K, t]`（正深度、
`t` 之后有余量）⇒ 半径 `r/(2√K)` 球上 `|∂ₜ⁻R(t, x)| ≤ C(c, r)·K²`。 -/
theorem localDt_of_curvature_window_P6LD (c r : ℝ) (hc : 0 < c) (hr : 0 < r) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ {P : OrientedThreeStage.{u}} {D : RealTimeInterval}
      (S : SolutionOn (I := ThreeModel) (M := P.Carrier) D), IsSolutionOn S →
      ∀ (K lo hi t : ℝ), 0 < K → lo < t - c / K → t < hi →
      Ico lo hi ⊆ D.carrier → Ioo lo hi ⊆ D.regular → ∀ p : P.Carrier,
      (∀ s ∈ Icc (t - c / K) t, ∀ y : P.Carrier,
        riemannianEDistOf (S.base.metric (t - c / K)) p y ≤
            ENNReal.ofReal (r / Real.sqrt K) →
          curvDerivNormSq 0 (S.base.metric s) y ≤ K ^ 2) →
      ∀ x : P.Carrier,
        riemannianEDistOf (S.base.metric (t - c / K)) p x ≤
            ENNReal.ofReal (r / (2 * Real.sqrt K)) →
        |derivWithin (fun v => S.scalar v x) (Iic t) t| ≤ C * K ^ 2 := by
  set U := shiLocalUniformBound (Module.finrank ℝ ThreeSpace) 2 c r with hU
  have hU0 : 0 ≤ U := shiLocalUniformBound_nonneg _ _ _ _
  refine ⟨3 ^ 6 * U / c + 2 * 3 ^ 4, by positivity, ?_⟩
  intro P D S hS K lo hi t hK hlo hhi hcar hreg p hu x hx
  set t₀ := t - c / K with ht₀
  have hτ : 0 < c / K := div_pos hc hK
  have hlohi : lo - t₀ < hi - t₀ := by linarith
  let S' : SolutionOn (I := ThreeModel) (M := P.Carrier)
      (RealTimeInterval.closedOpen (lo - t₀) (hi - t₀) hlohi) :=
    (S.timeShift t₀).timeRestrict _
  have hS' : IsSolutionOn S' := by
    apply isSolutionOn_timeRestrict (isSolutionOn_timeShift hS t₀)
    · intro s hs
      change s ∈ Ico (lo - t₀) (hi - t₀) at hs
      change s + t₀ ∈ D.carrier
      exact hcar ⟨by linarith [hs.1], by linarith [hs.2]⟩
    · intro s hs
      change s ∈ Ioo (lo - t₀) (hi - t₀) at hs
      change s + t₀ ∈ D.regular
      exact hreg ⟨by linarith [hs.1], by linarith [hs.2]⟩
  have hm : ∀ s, S'.base.metric s = S.base.metric (s + t₀) := fun s => rfl
  have hm0 : S'.base.metric 0 = S.base.metric t₀ := by rw [hm, zero_add]
  have h0mem : (0 : ℝ) ∈ (RealTimeInterval.closedOpen (lo - t₀) (hi - t₀) hlohi).carrier := by
    change (0 : ℝ) ∈ Ico (lo - t₀) (hi - t₀)
    exact ⟨by linarith, by linarith⟩
  have hball : IsCompact {y : P.Carrier |
      riemannianEDistOf (S'.base.metric 0) p y ≤ ENNReal.ofReal (r / Real.sqrt K)} :=
    (Geometry.Metric.isClosed_riemannianClosedBallOf (S'.base.metric 0) p
      (r / Real.sqrt K)).isCompact
  have hu' : ∀ s ∈ Icc (0 : ℝ) (c / K), ∀ y : P.Carrier,
      riemannianEDistOf (S'.base.metric 0) p y ≤ ENNReal.ofReal (r / Real.sqrt K) →
        nablaKRm04NormSqIntrinsic (I := ThreeModel) S' 0 s y ≤ K ^ 2 := by
    intro s hs y hy
    rw [nablaKRm04NormSqIntrinsic_eq_curvDerivNormSq, hm]
    rw [hm0] at hy
    exact hu (s + t₀) ⟨by linarith [hs.1], by linarith [hs.2]⟩ y hy
  have hx' : riemannianEDistOf (S'.base.metric 0) p x ≤
      ENNReal.ofReal (r / (2 * Real.sqrt K)) := by
    rw [hm0]
    exact hx
  have hshi := (shi_local_all_orders_curvature_scale_of_solution_uniform (I := ThreeModel) S' hS'
    p (T := c / K) (K := K) (R := r) (by linarith) hK hτ (by linarith) hr h0mem hball hu'
    2 (c / K) ⟨hτ, le_rfl⟩ x hx').2
  have hKc : K * (c / K) = c := by field_simp
  have htt : c / K + t₀ = t := by rw [ht₀]; ring
  rw [hKc, ← hU, nablaKRm04NormSqIntrinsic_eq_curvDerivNormSq, hm, htt,
    Real.sq_sqrt hτ.le] at hshi
  have h2 : Real.sqrt (curvDerivNormSq 2 (S.base.metric t) x) ≤ U / c * K ^ 2 := by
    have hrw : U * K / (c / K) = U / c * K ^ 2 := by field_simp
    rw [hrw] at hshi
    exact hshi
  have hrK : r / (2 * Real.sqrt K) ≤ r / Real.sqrt K := by
    have hsK : 0 < Real.sqrt K := Real.sqrt_pos.2 hK
    gcongr
    linarith
  have h0 : curvDerivNormSq 0 (S.base.metric t) x ≤ K ^ 2 :=
    hu t ⟨by linarith, le_rfl⟩ x (hx.trans (ENNReal.ofReal_le_ofReal hrK))
  have htreg : t ∈ D.regular := hreg ⟨by linarith, hhi⟩
  calc
    _ ≤ 3 ^ 6 * Real.sqrt (curvDerivNormSq 2 (S.base.metric t) x) +
        2 * 3 ^ 4 * curvDerivNormSq 0 (S.base.metric t) x :=
      abs_derivWithin_scalar_le_jets_P6LD S hS htreg x
    _ ≤ 3 ^ 6 * (U / c * K ^ 2) + 2 * 3 ^ 4 * K ^ 2 :=
      add_le_add (mul_le_mul_of_nonneg_left h2 (by norm_num))
        (mul_le_mul_of_nonneg_left h0 (by norm_num))
    _ = (3 ^ 6 * U / c + 2 * 3 ^ 4) * K ^ 2 := by ring

/-- `C·R²` 形（PROVED）：G1 主定理 + 点态 `K ≤ A·R(t, x)` ⇒ `|∂ₜ⁻R(t, x)| ≤ C·A²·R(t, x)²`。 -/
theorem localDt_of_scalar_window_P6LD (c r : ℝ) (hc : 0 < c) (hr : 0 < r) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ {P : OrientedThreeStage.{u}} {D : RealTimeInterval}
      (S : SolutionOn (I := ThreeModel) (M := P.Carrier) D), IsSolutionOn S →
      ∀ (K lo hi t A : ℝ), 0 < K → lo < t - c / K → t < hi →
      Ico lo hi ⊆ D.carrier → Ioo lo hi ⊆ D.regular → ∀ p : P.Carrier,
      (∀ s ∈ Icc (t - c / K) t, ∀ y : P.Carrier,
        riemannianEDistOf (S.base.metric (t - c / K)) p y ≤
            ENNReal.ofReal (r / Real.sqrt K) →
          curvDerivNormSq 0 (S.base.metric s) y ≤ K ^ 2) →
      ∀ x : P.Carrier,
        riemannianEDistOf (S.base.metric (t - c / K)) p x ≤
            ENNReal.ofReal (r / (2 * Real.sqrt K)) →
        K ≤ A * S.scalar t x →
        |derivWithin (fun v => S.scalar v x) (Iic t) t| ≤ C * A ^ 2 * S.scalar t x ^ 2 := by
  obtain ⟨C, hC, hb⟩ := localDt_of_curvature_window_P6LD.{u} c r hc hr
  refine ⟨C, hC, ?_⟩
  intro P D S hS K lo hi t A hK hlo hhi hcar hreg p hu x hx hKR
  have hsq : K ^ 2 ≤ (A * S.scalar t x) ^ 2 := pow_le_pow_left₀ hK.le hKR 2
  calc
    _ ≤ C * K ^ 2 := hb S hS K lo hi t hK hlo hhi hcar hreg p hu x hx
    _ ≤ C * (A * S.scalar t x) ^ 2 := mul_le_mul_of_nonneg_left hsq hC
    _ = C * A ^ 2 * S.scalar t x ^ 2 := by ring

/-- stage slab 实例化（PROVED）：`IncomingSlab` 的 `flow / equation` 上，窗口严格在 slab 内部
（`a < t − c/K`、`t < s`）即可；`Ico a s` / `Ioo a s` 就是 slab 的 carrier / regular。 -/
theorem IncomingSlab.localDt_P6LD (c r : ℝ) (hc : 0 < c) (hr : 0 < r) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ {P : OrientedThreeStage.{u}} {a s : ℝ} (G : P.IncomingSlab a s)
      (K t : ℝ), 0 < K → a < t - c / K → t < s → ∀ p : P.Carrier,
      (∀ v ∈ Icc (t - c / K) t, ∀ y : P.Carrier,
        riemannianEDistOf (G.flow.base.metric (t - c / K)) p y ≤
            ENNReal.ofReal (r / Real.sqrt K) →
          curvDerivNormSq 0 (G.flow.base.metric v) y ≤ K ^ 2) →
      ∀ x : P.Carrier,
        riemannianEDistOf (G.flow.base.metric (t - c / K)) p x ≤
            ENNReal.ofReal (r / (2 * Real.sqrt K)) →
        |derivWithin (fun v => G.flow.scalar v x) (Iic t) t| ≤ C * K ^ 2 := by
  obtain ⟨C, hC, hb⟩ := localDt_of_curvature_window_P6LD.{u} c r hc hr
  refine ⟨C, hC, ?_⟩
  intro P a s G K t hK hat hts p hu x hx
  exact hb G.flow G.equation K a s t hK hat hts (fun _ h => h) (fun _ h => h) p hu x hx

end GC.LongTime.Ch11
