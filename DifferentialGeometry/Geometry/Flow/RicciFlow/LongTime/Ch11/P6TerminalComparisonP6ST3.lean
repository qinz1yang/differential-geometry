import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.P6BufferedTransferP6ST2
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.StaticMetricApproximation
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.ComparisonComposition
import DifferentialGeometry.Geometry.Compactness.CheegerGromov.ApproximateIsometry.MetricApproximation.OfMetricDerivNorm
import DifferentialGeometry.Geometry.Metric.Convergence.CovariantDerivative.Norm.Comparison
import DifferentialGeometry.Geometry.Metric.Convergence.DerivativeNorm.Locality
import DifferentialGeometry.Geometry.Metric.Pullback.PartialDiffeomorph.CompactExtension
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.TerminalScalarDerivativeBounds
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.TerminalCurvatureConvergence
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.CrossingScalar
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.SurvivorChartMetric
import DifferentialGeometry.Topology.Manifold.CurveTransversality

/-!
# S-c P-C / P-S：terminal `C^k` 收敛 ⇒ `MetricComparisonOn`（O-CH11-STAB3 G1，后缀 `_P6ST3`）

STAB2 合同 `BufferedFootprintData_P6ST2` 的 `comparison` / `scalar_tendsto` / `gradient_tendsto`
三个字段的 producer。

* **P-C**（`eventually_comparison_of_terminal_P6ST3`）：`TerminalMetricConverges`
  （`metricDerivNorm j (g t|Ω) ḡ ḡ`，以 terminal limit `ḡ` 为参照）+ 紧集 `K ⊆ J.source ∩ Ω` 上的
  survivor 等距 `J*g⁺ = ḡ`（`hiso`）⇒ 对任意阶 `k`、任意 `δ > 0`，`t → s⁻` eventually 有
  `MetricComparisonOn (g t) g⁺ J U {0} k δ`（`g t`-参照）。证明三步：
  (i) 树内 reference change `metric_deriv_norm_reference_change_le`（`ḡ` 参照 → `g t|Ω` 参照）；
  (ii) `J*g⁺` 的全局延拓 `G`（`exists_smooth_riemannian_metric_eq_pullback_on_compact`），
  在开集 `U ⊆ K` 上 `G|Ω = ḡ`，局部性 `metricDerivNorm_eq_of_metric_eventuallyEq`；
  (iii) `metricDerivNorm_restrictOpen` 回到 `P.Carrier`，再 `MapMetricApproximationOn.ofMetricDerivNorm`
  + `MetricComparisonOn.ofMapMetricApproximation`。
  序列版 `comparison_seq_of_terminal_P6ST3` 正是合同字段形（`v n ∈ (a, s)`，`v n → s`）。
* **P-S**（点态，`RegularCrossing p q`）：`scalar_tendsto_of_regularCrossing_P6ST3`
  （`R_{g(v n)}(p) → R⁺(q)`，树内 `tendsto_metricScalarAt` + `RegularCrossing.scalar_eq`）与
  `gradient_tendsto_of_regularCrossing_P6ST3`（取 `u := dF⁻¹_q w`，`F` = survivor；
  `tendsto_scalar_differential` + `tendsto_inner` + 等距）。
* consumer `BufferedFootprintData_P6ST2.ofTerminal_P6ST3`：合同结构由上述 producer 填三个字段。
-/

set_option autoImplicit false

noncomputable section

open Set Filter TopologicalSpace
open DifferentialGeometry DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.CheegerGromovCompactness
open DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn
open scoped Manifold ContDiff Topology

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

universe u

namespace OrientedThreeStage.IncomingSlab

variable {P : OrientedThreeStage.{u}} {a s : ℝ}

/-- `dR` 在 `restrictOpen Ω` 下不变（树内同名引理是 private，重证）。 -/
theorem scalar_differential_restrictOpen_P6ST3 (G : P.IncomingSlab a s) (g : P.Metric)
    (x : G.terminalRegularOpen) (v : TangentSpace ThreeModel x) :
    (show ℝ from mfderiv ThreeModel 𝓘(ℝ, ℝ)
      (metricScalarAt (g.restrictOpen G.terminalRegularOpen)) x v) =
      (show ℝ from mfderiv ThreeModel 𝓘(ℝ, ℝ) (metricScalarAt g) x.val v) := by
  have : IsManifold ThreeModel 1 G.terminalRegularOpen := IsManifold.of_le (n := ∞) (by decide)
  have heq : metricScalarAt (g.restrictOpen G.terminalRegularOpen) =
      (metricScalarAt g) ∘ (Subtype.val : G.terminalRegularOpen → P.Carrier) := by
    funext y
    exact metricScalarAt_restrictOpen g G.terminalRegularOpen y
  rw [heq, mfderiv_comp x ((metricScalar_smooth g).mdifferentiableAt (by simp))
    ((contMDiff_subtype_val : ContMDiff ThreeModel ThreeModel ∞
      (Subtype.val : G.terminalRegularOpen → P.Carrier)).mdifferentiableAt (by simp)),
    ContinuousLinearMap.comp_apply, DifferentialGeometry.mfderiv_subtype_val_apply]

end OrientedThreeStage.IncomingSlab

namespace MetricCutCapEvent

variable {P Q : OrientedThreeStage.{u}} {a s : ℝ}

/-- `v n ∈ (a, s)`、`v n → s` ⇒ `v → s⁻`（`𝓝[<] s`）。 -/
theorem tendsto_nhdsLT_of_slab_P6ST3 {v : ℕ → ℝ} (hv : ∀ n, v n ∈ Ioo a s)
    (hvt : Tendsto v atTop (𝓝 s)) : Tendsto v atTop (𝓝[<] s) :=
  tendsto_nhdsWithin_iff.mpr ⟨hvt, Eventually.of_forall fun n => (hv n).2⟩

/-- **P-C（`P.Carrier` 层）**：terminal `C^k` 收敛 + 紧集 `K`（`U ⊆ K ⊆ J.source`，`K ⊆ Ω`）上的 survivor 等距
`J*g⁺ = ḡ` ⇒ 对任意阶 `k` 与 `δ > 0`，`t → s⁻` eventually `MetricComparisonOn (g t) g⁺ J U {0} k δ`
（`g t`-联络与范数）。 -/
theorem eventually_comparison_of_terminal_P6ST3 (E : MetricCutCapEvent P Q a s)
    (J : PartialDiffeomorph ThreeModel ThreeModel P.Carrier Q.Carrier ∞)
    (U : Opens P.Carrier) {K : Set P.Carrier} (hK : IsCompact K)
    (hUK : (U : Set P.Carrier) ⊆ K) (hKJ : K ⊆ J.source)
    (hKΩ : K ⊆ E.incoming.terminalRegularOpen)
    (hiso : ∀ (x : P.Carrier) (hx : x ∈ E.incoming.terminalRegularOpen), x ∈ K →
      ∀ v w : TangentSpace ThreeModel x,
        E.outputMetric.inner (J x) (mfderiv ThreeModel ThreeModel J x v)
          (mfderiv ThreeModel ThreeModel J x w) = E.terminal.metric.inner ⟨x, hx⟩ v w)
    (k : ℕ) {δ : ℝ} (hδ : 0 < δ) :
    ∀ᶠ t in 𝓝[<] s, Nonempty (MetricComparisonOn (fun _ => E.incoming.flow.base.metric t)
      (fun _ => E.outputMetric) J U {0} k δ) := by
  classical
  have : SigmaCompactSpace E.incoming.terminalRegularOpen :=
    isSigmaCompact_iff_sigmaCompactSpace.mp
      (DifferentialGeometry.Geometry.isSigmaCompact_of_isOpen ThreeModel
        E.incoming.terminalRegularOpen.isOpen)
  have : IsManifold ThreeModel 1 P.Carrier := IsManifold.of_le (n := ∞) (by decide)
  have hδ'0 : 0 < min δ (1 / 2) := lt_min hδ (by norm_num)
  have hδ'1 : min δ (1 / 2) < 1 := (min_le_right _ _).trans_lt (by norm_num)
  obtain ⟨η, hη, hη1, hηdim, hηbud⟩ :=
    exists_metric_reference_change_delta (E := ThreeSpace) k hδ'0
  let K' : Set E.incoming.terminalRegularOpen := Subtype.val ⁻¹' K
  have hK' : IsCompact K' := by
    rw [Subtype.isCompact_iff]
    change IsCompact (Subtype.val '' (Subtype.val ⁻¹' K))
    rw [image_preimage_eq_of_subset (fun x hx => ⟨⟨x, hKΩ hx⟩, rfl⟩)]
    exact hK
  have hconv : ∀ᶠ t in 𝓝[<] s, ∀ j : Fin (k + 1), ∀ y ∈ K',
      metricDerivNorm j ((E.incoming.flow.base.metric t).restrictOpen
        E.incoming.terminalRegularOpen) E.terminal.metric E.terminal.metric y < η := by
    refine eventually_all.mpr fun j => ?_
    obtain ⟨d, hd, hb⟩ := E.terminal.converges K' hK' j η hη
    filter_upwards [Ioo_mem_nhdsLT hd.2] with t ht
    exact hb t ht
  obtain ⟨G, hG⟩ := exists_smooth_riemannian_metric_eq_pullback_on_compact (I := ThreeModel) J
    hK hKJ E.outputMetric (E.incoming.flow.base.metric a)
  filter_upwards [hconv] with t ht
  have hderiv : ∀ j : ℕ, j ≤ k → ∀ x ∈ (U : Set P.Carrier),
      metricDerivNorm j G (E.incoming.flow.base.metric t) (E.incoming.flow.base.metric t) x ≤
        min δ (1 / 2) := by
    intro j hj x hx
    have hxΩ : x ∈ E.incoming.terminalRegularOpen := hKΩ (hUK hx)
    let uu : Set E.incoming.terminalRegularOpen := Subtype.val ⁻¹' (U : Set P.Carrier)
    have hu : IsOpen uu := U.isOpen.preimage continuous_subtype_val
    have hxu : (⟨x, hxΩ⟩ : E.incoming.terminalRegularOpen) ∈ uu := hx
    have href := metric_deriv_norm_reference_change_le (I := ThreeModel) hu E.terminal.metric
      ((E.incoming.flow.base.metric t).restrictOpen E.incoming.terminalRegularOpen)
      E.terminal.metric k hη.le hη1.le hηdim hηbud
      (fun y _ q _ => by rw [metricDerivNorm_self]; exact hη.le)
      (fun y hy q hq => (ht ⟨q, Nat.lt_succ_of_le hq⟩ y (hUK hy)).le) ⟨x, hxΩ⟩ hxu j hj
    have hloc : metricDerivNorm j (G.restrictOpen E.incoming.terminalRegularOpen)
        ((E.incoming.flow.base.metric t).restrictOpen E.incoming.terminalRegularOpen)
        ((E.incoming.flow.base.metric t).restrictOpen E.incoming.terminalRegularOpen)
          ⟨x, hxΩ⟩ =
        metricDerivNorm j E.terminal.metric
        ((E.incoming.flow.base.metric t).restrictOpen E.incoming.terminalRegularOpen)
        ((E.incoming.flow.base.metric t).restrictOpen E.incoming.terminalRegularOpen)
          ⟨x, hxΩ⟩ := by
      apply metricDerivNorm_eq_of_metric_eventuallyEq
      filter_upwards [hu.mem_nhds hxu] with y hy v w
      change G.inner y.val v w = E.terminal.metric.inner y v w
      rw [hG y.val (hUK hy) v w]
      exact hiso y.val y.property (hUK hy) v w
    rw [← metricDerivNorm_restrictOpen G (E.incoming.flow.base.metric t)
      (E.incoming.flow.base.metric t) E.incoming.terminalRegularOpen j ⟨x, hxΩ⟩, hloc]
    exact href
  have happly : ∀ x ∈ (U : Set P.Carrier), ∀ v : Fin 2 → TangentSpace ThreeModel x,
      Tensor0SBundle.metricTensorField G x v = E.outputMetric.inner (J x)
        (mfderiv ThreeModel ThreeModel J x (v 0)) (mfderiv ThreeModel ThreeModel J x (v 1)) := by
    intro x hx v
    rw [Tensor0SBundle.metricTensorField_apply]
    exact hG x (hUK hx) (v 0) (v 1)
  let D := MapMetricApproximationOn.ofMetricDerivNorm (K := (U : Set P.Carrier)) (p := k)
    (F := (J : P.Carrier → Q.Carrier)) G (E.incoming.flow.base.metric t) E.outputMetric hδ'0 hδ'1
    (J.contMDiffOn_toFun.mono (hUK.trans hKJ)) happly hderiv
  exact ⟨(MetricComparisonOn.ofMapMetricApproximation D {0}).mono subset_rfl le_rfl
    (min_le_left _ _)⟩

/-- **P-C 序列版（合同字段形）**：`v n ∈ (a, s)`、`v n → s` ⇒ `comparison` 字段。 -/
theorem comparison_seq_of_terminal_P6ST3 (E : MetricCutCapEvent P Q a s)
    (J : PartialDiffeomorph ThreeModel ThreeModel P.Carrier Q.Carrier ∞)
    (U : Opens P.Carrier) {K : Set P.Carrier} (hK : IsCompact K)
    (hUK : (U : Set P.Carrier) ⊆ K) (hKJ : K ⊆ J.source)
    (hKΩ : K ⊆ E.incoming.terminalRegularOpen)
    (hiso : ∀ (x : P.Carrier) (hx : x ∈ E.incoming.terminalRegularOpen), x ∈ K →
      ∀ v w : TangentSpace ThreeModel x,
        E.outputMetric.inner (J x) (mfderiv ThreeModel ThreeModel J x v)
          (mfderiv ThreeModel ThreeModel J x w) = E.terminal.metric.inner ⟨x, hx⟩ v w)
    (k : ℕ) {v : ℕ → ℝ} (hv : ∀ n, v n ∈ Ioo a s) (hvt : Tendsto v atTop (𝓝 s)) :
    ∀ δ : ℝ, 0 < δ → ∀ᶠ n in atTop,
      Nonempty (MetricComparisonOn (fun _ => E.incoming.flow.base.metric (v n))
        (fun _ => E.outputMetric) J U {0} k δ) := fun _ hδ =>
  (tendsto_nhdsLT_of_slab_P6ST3 hv hvt).eventually
    (E.eventually_comparison_of_terminal_P6ST3 J U hK hUK hKJ hKΩ hiso k hδ)

/-- **P-S scalar（合同 `scalar_tendsto` 字段）**：`RegularCrossing p q` ⇒ `R_{g(v n)}(p) → R⁺(q)`。 -/
theorem scalar_tendsto_of_regularCrossing_P6ST3 (E : MetricCutCapEvent P Q a s)
    {p : P.Carrier} {q : Q.Carrier} (hcross : E.RegularCrossing p q) {v : ℕ → ℝ}
    (hv : ∀ n, v n ∈ Ioo a s) (hvt : Tendsto v atTop (𝓝 s)) :
    Tendsto (fun n => metricScalarAt (E.incoming.flow.base.metric (v n)) p) atTop
      (𝓝 (metricScalarAt E.outputMetric q)) := by
  have hp : p ∈ E.incoming.terminalRegularOpen := hcross.mem_terminalRegularRegion E
  have h := E.terminal.tendsto_metricScalarAt ⟨p, hp⟩
  rw [RegularCrossing.scalar_eq E (p := ⟨p, hp⟩) hcross] at h
  exact h.comp (tendsto_nhdsLT_of_slab_P6ST3 hv hvt)

/-- **P-S gradient（合同 `gradient_tendsto` 字段）**：`RegularCrossing p q` ⇒ 对每个 `w ∈ T_q`，取
`u := dF⁻¹_q w`（`F` = survivor partial diffeomorph），`dR_{g(v n)}(p) u → dR⁺(q) w` 且
`|u|²_{g(v n)} → |w|²_{g⁺}`。 -/
theorem gradient_tendsto_of_regularCrossing_P6ST3 (E : MetricCutCapEvent P Q a s)
    {p : P.Carrier} {q : Q.Carrier} (hcross : E.RegularCrossing p q) {v : ℕ → ℝ}
    (hv : ∀ n, v n ∈ Ioo a s) (hvt : Tendsto v atTop (𝓝 s)) :
    ∀ w : TangentSpace ThreeModel q, ∃ u : TangentSpace ThreeModel p,
      Tendsto (fun n => (show ℝ from mfderiv ThreeModel 𝓘(ℝ, ℝ)
          (metricScalarAt (E.incoming.flow.base.metric (v n))) p u)) atTop
        (𝓝 (show ℝ from mfderiv ThreeModel 𝓘(ℝ, ℝ) (metricScalarAt E.outputMetric) q w)) ∧
      Tendsto (fun n => (E.incoming.flow.base.metric (v n)).inner p u u) atTop
        (𝓝 (E.outputMetric.inner q w w)) := by
  intro w
  have hp : p ∈ E.incoming.terminalRegularOpen := hcross.mem_terminalRegularRegion E
  let p' : E.incoming.terminalRegularOpen := ⟨p, hp⟩
  obtain ⟨F, -, hpF, hFp, hqT, hcrossF, hmetric⟩ :=
    RegularCrossing.exists_survivor_partialDiffeomorph E (p := p') hcross
  let u : TangentSpace ThreeModel p' := mfderiv ThreeModel ThreeModel F.symm q w
  have hsymm : F.symm q = p' := by
    rw [← hFp]
    exact F.left_inv hpF
  have hFu : mfderiv ThreeModel ThreeModel F p' u = w := by
    have h := congrArg (fun L => L w)
      (PartialDiffeomorph.mfderiv_comp_mfderiv_symm F (by simp) hqT)
    change mfderiv ThreeModel ThreeModel F (F.symm q) (mfderiv ThreeModel ThreeModel F.symm q w) =
      w at h
    rw [hsymm] at h
    exact h
  have hscal : metricScalarAt E.terminal.metric =ᶠ[𝓝 p']
      (metricScalarAt E.outputMetric) ∘ (F : E.incoming.terminalRegularOpen → Q.Carrier) := by
    filter_upwards [F.open_source.mem_nhds hpF] with y hy
    exact RegularCrossing.scalar_eq E (hcrossF y hy)
  have hFd : MDifferentiableAt ThreeModel ThreeModel
      (F : E.incoming.terminalRegularOpen → Q.Carrier) p' :=
    (F.contMDiffOn_toFun.contMDiffAt (F.open_source.mem_nhds hpF)).mdifferentiableAt (by simp)
  have hdiff : (show ℝ from mfderiv ThreeModel 𝓘(ℝ, ℝ) (metricScalarAt E.terminal.metric) p' u) =
      (show ℝ from mfderiv ThreeModel 𝓘(ℝ, ℝ) (metricScalarAt E.outputMetric) q w) := by
    rw [hscal.mfderiv_eq]
    change (show ℝ from mfderiv ThreeModel 𝓘(ℝ, ℝ) ((metricScalarAt E.outputMetric) ∘
      (F : E.incoming.terminalRegularOpen → Q.Carrier)) p' u) = _
    rw [mfderiv_comp p' ((metricScalar_smooth E.outputMetric).mdifferentiableAt (by simp)) hFd,
      ContinuousLinearMap.comp_apply, hFu, hFp]
  have hinner : E.terminal.metric.inner p' u u = E.outputMetric.inner q w w := by
    rw [← hmetric p' hpF u u, hFu, hFp]
  refine ⟨u, ?_, ?_⟩
  · have h1 := E.terminal.tendsto_scalar_differential p' u
    rw [hdiff] at h1
    refine (h1.comp (tendsto_nhdsLT_of_slab_P6ST3 hv hvt)).congr fun n => ?_
    exact OrientedThreeStage.IncomingSlab.scalar_differential_restrictOpen_P6ST3 E.incoming _ p' u
  · have h2 := E.terminal.tendsto_inner p' u u
    rw [hinner] at h2
    exact h2.comp (tendsto_nhdsLT_of_slab_P6ST3 hv hvt)

/-- **consumer**：P-C / P-S 生产 STAB2 合同 `BufferedFootprintData_P6ST2` 的 `comparison`、
`scalar_tendsto`、`gradient_tendsto` 三个字段；剩余输入 = 合同的数值字段、`J`（G2 由 survivor
构造）与 `footprint`（G3）。 -/
def BufferedFootprintData_P6ST2.ofTerminal_P6ST3 {E : MetricCutCapEvent P Q a s} {p : P.Carrier}
    {q : Q.Carrier} {ηout C1 C2 m : ℝ} {k : ℕ} (hη : ηout < 1 / 11) (hC1 : 1 ≤ C1) (hC2 : 1 ≤ C2)
    (hm0 : 0 < m) (hm1 : m ≤ 1 / 2) (hk : max 2 ⌈ηout⁻¹⌉₊ ≤ k) (hcross : E.RegularCrossing p q)
    (J : PartialDiffeomorph ThreeModel ThreeModel P.Carrier Q.Carrier ∞) (hJ : J p = q)
    (U : Opens P.Carrier) {K : Set P.Carrier} (hK : IsCompact K)
    (hUK : (U : Set P.Carrier) ⊆ K) (hKJ : K ⊆ J.source)
    (hKΩ : K ⊆ E.incoming.terminalRegularOpen)
    (hiso : ∀ (x : P.Carrier) (hx : x ∈ E.incoming.terminalRegularOpen), x ∈ K →
      ∀ v w : TangentSpace ThreeModel x,
        E.outputMetric.inner (J x) (mfderiv ThreeModel ThreeModel J x v)
          (mfderiv ThreeModel ThreeModel J x w) = E.terminal.metric.inner ⟨x, hx⟩ v w)
    (v : ℕ → ℝ) (hv : ∀ n, v n ∈ Ioo a s) (hvt : Tendsto v atTop (𝓝 s))
    (hQ : 0 < metricScalarAt E.outputMetric q)
    (hfoot : ∀ᶠ n in atTop,
      riemannianClosedBallOf (I := I3) (E.incoming.flow.base.metric (v n)) p
        ((8 * C1 + 3 * ((ηout / 2)⁻¹ + 7) * Real.sqrt C2) /
          Real.sqrt (metricScalarAt (E.incoming.flow.base.metric (v n)) p)) ⊆ U) :
    E.BufferedFootprintData_P6ST2 p q ηout C1 C2 m k where
  ηout_lt := hη
  one_le_C1 := hC1
  one_le_C2 := hC2
  m_pos := hm0
  m_le := hm1
  order_le := hk
  J := J
  J_apply := hJ
  U := U
  U_sub := hUK.trans hKJ
  v := v
  v_mem := hv
  v_tendsto := hvt
  Q_pos := hQ
  scalar_tendsto := E.scalar_tendsto_of_regularCrossing_P6ST3 hcross hv hvt
  footprint := hfoot
  comparison := E.comparison_seq_of_terminal_P6ST3 J U hK hUK hKJ hKΩ hiso k hv hvt
  gradient_tendsto := E.gradient_tendsto_of_regularCrossing_P6ST3 hcross hv hvt

end MetricCutCapEvent

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
