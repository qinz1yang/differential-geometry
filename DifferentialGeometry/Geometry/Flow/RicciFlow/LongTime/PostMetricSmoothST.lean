import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.PostStageStaticST

set_option autoImplicit false
noncomputable section

open DifferentialGeometry DifferentialGeometry.Topology
open DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
open DifferentialGeometry.PDE.RicciFlow DifferentialGeometry.Geometry.Curvature
open Set Filter Bundle
open scoped Manifold ContDiff Topology

/-!
# `postMetric` 关于 `t` 光滑（lane S-A14-STATIC，G2）

G1（`PostStageStaticST`）把无事件区间 `Ioo a b` 上的 `postMetric` 拉回成同一流形
`postStage O t₀` 上的 Ricci flow 解 `S`。本文件由 `S` 的 `MetricSmoothUpTo` 与
`IsSolutionOn.equation` 得到：

* `postMetric_smooth_in_time_ST`：固定 `x` 与 `v w : TangentSpace ThreeModel x`，
  `t ↦ (postMetricAt_ST O t₀ t).inner x v w` 在 `Ioo a b` 上 `C^∞`；
* `postMetric_hasDerivAt_ricci_ST`：同一个函数的导数是 `-2 * Ric`（`S.ricciAt`）；
* `contDiffAt_inner_of_metricSmoothUpTo_ST`：通用引理，从 `OrientedThreeStage.MetricSmoothUpTo`
  （chart frame 内联合光滑的系数 `A (s, x) i j`）得到固定 `x v w` 的 `C^∞` in `t`。

consumer：`postMetric_pointwise_comparison_ST`（固定 `x v` 的 `e^ε` comparison，`t₁` 附近）。
-/

namespace GC.LongTime

universe u

variable {P : OrientedThreeStage.{u}} {g : P.Metric}

/-- trivialization 的 `symmL` 作用在 `c : ThreeSpace` 上等于 chart frame 的线性组合。 -/
theorem symmL_eq_sum_chartVector_ST (Q : OrientedThreeStage.{u}) (p x : Q.Carrier)
    (c : ThreeSpace) :
    (trivializationAt ThreeSpace (TangentSpace ThreeModel) p).symmL ℝ x c =
      ∑ i : Fin 3, c i • Q.chartVector p x i := by
  have hc : c = ∑ i : Fin 3, c i • EuclideanSpace.single i (1 : ℝ) := by
    have := (EuclideanSpace.basisFun (Fin 3) ℝ).sum_repr c
    simpa [EuclideanSpace.basisFun_apply, EuclideanSpace.basisFun_repr] using this.symm
  conv_lhs => rw [hc]
  simp only [map_sum, map_smul]
  rfl

/-- `x ∈ baseSet(trivializationAt p)` 时，`m.inner x v w` 展开成 chart frame 系数的双线性和。 -/
theorem inner_eq_sum_chartVector_ST (Q : OrientedThreeStage.{u}) (p x : Q.Carrier)
    (hx : x ∈ (trivializationAt ThreeSpace (TangentSpace ThreeModel) p).baseSet)
    (m : Q.Metric) (v w : TangentSpace ThreeModel x) :
    m.inner x v w = ∑ i : Fin 3, ∑ j : Fin 3,
      ((trivializationAt ThreeSpace (TangentSpace ThreeModel) p).continuousLinearMapAt ℝ x v i) *
      ((trivializationAt ThreeSpace (TangentSpace ThreeModel) p).continuousLinearMapAt ℝ x w j) *
        m.inner x (Q.chartVector p x i) (Q.chartVector p x j) := by
  have hv : v = ∑ i : Fin 3,
      ((trivializationAt ThreeSpace (TangentSpace ThreeModel) p).continuousLinearMapAt ℝ x v i) •
        Q.chartVector p x i := by
    rw [← symmL_eq_sum_chartVector_ST, Trivialization.symmL_continuousLinearMapAt _ hx]
  have hw : w = ∑ j : Fin 3,
      ((trivializationAt ThreeSpace (TangentSpace ThreeModel) p).continuousLinearMapAt ℝ x w j) •
        Q.chartVector p x j := by
    rw [← symmL_eq_sum_chartVector_ST, Trivialization.symmL_continuousLinearMapAt _ hx]
  conv_lhs => rw [hv, hw]
  simp only [map_sum, map_smul, sum_apply, smul_apply, smul_eq_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  ring

/-- 通用引理：`MetricSmoothUpTo m J` 且 `J ∈ 𝓝 t₁` ⇒ 固定 `x v w`，`s ↦ (m s).inner x v w`
在 `t₁` 处 `C^∞`。 -/
theorem contDiffAt_inner_of_metricSmoothUpTo_ST (Q : OrientedThreeStage.{u})
    (m : ℝ → Q.Metric) (J : Set ℝ) (hsm : Q.MetricSmoothUpTo m J) {t₁ : ℝ} (hJ : J ∈ 𝓝 t₁)
    (x : Q.Carrier) (v w : TangentSpace ThreeModel x) :
    ContDiffAt ℝ ∞ (fun s : ℝ => (m s).inner x v w) t₁ := by
  obtain ⟨U, hU, hxU, hbase, V, hV, ht₁V, A, hA, heq⟩ := hsm x t₁ (mem_of_mem_nhds hJ)
  have hA' : ∀ i j : Fin 3, ContDiffAt ℝ ∞ (fun s : ℝ => A (s, x) i j) t₁ := by
    intro i j
    have h1 : ContMDiffAt (𝓘(ℝ, ℝ).prod ThreeModel) 𝓘(ℝ, ℝ) ∞ (fun z => A z i j) (t₁, x) :=
      (hA i j).contMDiffAt ((hV.prod hU).mem_nhds ⟨ht₁V, hxU⟩)
    have h2 : ContMDiffAt 𝓘(ℝ, ℝ) (𝓘(ℝ, ℝ).prod ThreeModel) ∞ (fun s : ℝ => (s, x)) t₁ :=
      contMDiffAt_id.prodMk contMDiffAt_const
    exact contMDiffAt_iff_contDiffAt.mp (h1.comp t₁ h2)
  have hev : (fun s : ℝ => (m s).inner x v w) =ᶠ[𝓝 t₁] fun s : ℝ => ∑ i : Fin 3, ∑ j : Fin 3,
      ((trivializationAt ThreeSpace (TangentSpace ThreeModel) x).continuousLinearMapAt ℝ x v i) *
      ((trivializationAt ThreeSpace (TangentSpace ThreeModel) x).continuousLinearMapAt ℝ x w j) *
        A (s, x) i j := by
    filter_upwards [inter_mem (hV.mem_nhds ht₁V) hJ] with s hs
    rw [inner_eq_sum_chartVector_ST Q x x (hbase hxU) (m s) v w]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    rw [heq s hs x hxU i j]
  refine ContDiffAt.congr_of_eventuallyEq ?_ hev
  exact ContDiffAt.sum fun i _ => ContDiffAt.sum fun j _ => contDiffAt_const.mul (hA' i j)

/-- G2：`t₁ ∈ Ioo a b` 处 `C^∞`（pointwise 版）。 -/
theorem postMetric_contDiffAt_ST (O : ObservationTower P g) {a b : ℝ} (ha : 0 ≤ a)
    (hno : ∀ s ∈ O.eventTimes, s ∉ Ioo a b) {t₀ t₁ : ℝ} (ht₀ : t₀ ∈ Ioo a b)
    (ht₁ : t₁ ∈ Ioo a b) (x : (postStage O t₀).Carrier) (v w : TangentSpace ThreeModel x) :
    ContDiffAt ℝ ∞ (fun s : ℝ => (postMetricAt_ST O t₀ s).inner x v w) t₁ := by
  obtain ⟨D, S, _, hsm, hreg, hmeq⟩ := exists_stageFlow_of_no_event_ST O ha hno ht₀
  have hat := contDiffAt_inner_of_metricSmoothUpTo_ST (postStage O t₀) S.base.metric D.carrier
    hsm (D.regular_mem_nhds (hreg ht₁)) x v w
  refine hat.congr_of_eventuallyEq ?_
  filter_upwards [isOpen_Ioo.mem_nhds ht₁] with s hs
  rw [hmeq s hs]

/-- **G2 主定理**：无事件区间 `Ioo a b` 上，固定 `x` 与 `v w`，
`t ↦ (postMetricAt_ST O t₀ t).inner x v w`（`postMetric O t` 经 `postStageEquiv_ST` 拉回）是 `C^∞`。 -/
theorem postMetric_smooth_in_time_ST (O : ObservationTower P g) {a b : ℝ} (ha : 0 ≤ a)
    (hno : ∀ s ∈ O.eventTimes, s ∉ Ioo a b) {t₀ : ℝ} (ht₀ : t₀ ∈ Ioo a b)
    (x : (postStage O t₀).Carrier) (v w : TangentSpace ThreeModel x) :
    ContDiffOn ℝ ∞ (fun s : ℝ => (postMetricAt_ST O t₀ s).inner x v w) (Ioo a b) :=
  fun _ ht₁ => (postMetric_contDiffAt_ST O ha hno ht₀ ht₁ x v w).contDiffWithinAt

/-- G2：无事件区间上的 Ricci flow 方程：存在该段的 flow `S`（`IsSolutionOn S`，metric 就是
`postMetricAt_ST O t₀`），且 `∂ₜ g(x; X, Y) = -2 * Ric_S(x; X, Y)`（`HasDerivAt`）。 -/
theorem postMetric_hasDerivAt_ricci_ST (O : ObservationTower P g) {a b : ℝ} (ha : 0 ≤ a)
    (hno : ∀ s ∈ O.eventTimes, s ∉ Ioo a b) {t₀ : ℝ} (ht₀ : t₀ ∈ Ioo a b) :
    ∃ (D : RealTimeInterval) (S : SolutionOn (I := ThreeModel) (M := (postStage O t₀).Carrier) D),
      IsSolutionOn S ∧ (∀ s ∈ Ioo a b, S.base.metric s = postMetricAt_ST O t₀ s) ∧
      ∀ s ∈ Ioo a b, ∀ (x : (postStage O t₀).Carrier) (X Y : TangentSpace ThreeModel x),
        HasDerivAt (fun r : ℝ => (postMetricAt_ST O t₀ r).inner x X Y)
          ((-2 : ℝ) * S.ricciAt s x (vec2 X Y)) s := by
  obtain ⟨D, S, hS, _, hreg, hmeq⟩ := exists_stageFlow_of_no_event_ST O ha hno ht₀
  refine ⟨D, S, hS, hmeq, fun s hs x X Y => ?_⟩
  have hd := hS.equation ⟨s, hreg hs⟩ x X Y
  have hd' : HasDerivAt (fun r : ℝ => (S.base.metric r).inner x X Y)
      ((-2 : ℝ) * S.ricciAt s x (vec2 X Y)) s :=
    hd.hasDerivAt (D.regular_mem_nhds (hreg hs))
  refine hd'.congr_of_eventuallyEq ?_
  filter_upwards [isOpen_Ioo.mem_nhds hs] with r hr
  rw [hmeq r hr]

/-- G2 consumer：固定 `x v`，`t₁` 附近 `g_s(v,v) ≤ e^ε g_{t₁}(v,v)`（由 `C^∞` ⇒ 连续）。 -/
theorem postMetric_pointwise_comparison_ST (O : ObservationTower P g) {a b : ℝ} (ha : 0 ≤ a)
    (hno : ∀ s ∈ O.eventTimes, s ∉ Ioo a b) {t₀ t₁ : ℝ} (ht₀ : t₀ ∈ Ioo a b)
    (ht₁ : t₁ ∈ Ioo a b) (x : (postStage O t₀).Carrier) (v : TangentSpace ThreeModel x)
    {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ s in 𝓝 t₁, (postMetricAt_ST O t₀ s).inner x v v ≤
      Real.exp ε * (postMetricAt_ST O t₀ t₁).inner x v v := by
  by_cases hv : v = 0
  · subst hv
    simp
  · have hpos : 0 < (postMetricAt_ST O t₀ t₁).inner x v v := (postMetricAt_ST O t₀ t₁).pos x v hv
    have hcont := (postMetric_contDiffAt_ST O ha hno ht₀ ht₁ x v v).continuousAt
    have hlt : (postMetricAt_ST O t₀ t₁).inner x v v <
        Real.exp ε * (postMetricAt_ST O t₀ t₁).inner x v v := by
      have h1 : 1 < Real.exp ε := Real.one_lt_exp_iff.mpr hε
      nlinarith
    filter_upwards [hcont.eventually (gt_mem_nhds hlt)] with s hs
    exact hs.le

end GC.LongTime
