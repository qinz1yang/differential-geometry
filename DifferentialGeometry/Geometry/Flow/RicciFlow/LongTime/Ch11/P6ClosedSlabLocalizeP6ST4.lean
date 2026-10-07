import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.P6SeedDistanceP6ST4
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.P6LeftBadLocalizationCXST
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.SlabTerminalConvergence
import DifferentialGeometry.Topology.Manifold.PartialDiffeomorph.Composition

/-!
# S-c 无 surgery 特例：闭 slab 端点的 localized bad points（O-CH11-STAB4 G5，后缀 `_P6ST4`）

HREST2 binder `hlocH`（final slab 闭端点 `σ = horizon`）= S-c 的 **`J = id`** 特例：没有 surgery，buffer =
整个（紧）流形，footprint 平凡，comparison = 闭 slab 光滑到端点的 `C^k` 连续。本文件（event-free，
`S : P.ClosedSlab u σ`，`g t := S.flow.base.metric t`）：
* `closedSlab_eventually_comparison_P6ST4`：`∀ k δ>0, t → σ⁻` eventually
  `MetricComparisonOn (g t) (g σ) id univ {0} k δ`（树内 `MetricSmoothUpTo.terminal_convergence` +
  reference change + `MapMetricApproximationOn.ofMetricDerivNorm`）。
* **`spatialWitness_of_closedSlab_P6ST4`**（D-10 局部扰动的 `J = id` 版，0 binder）：`t → σ⁻` eventually 的
  fine-margin witness `(ηfine, C1, C2, m)` at `(g t, y)` + `R_{g σ}(y) > 0` ⇒ `(g σ, y)` 处
  `(ηout, C1out, C2out)` witness（树内 `exists_uniform_comparison_transport_tolerance`，`F = id`、
  `U = univ`）。
* `closedSlab_eventually_edist_le_P6ST4`：`d_{g t}(o, y) ≤ d_{g σ}(o, y) + η` eventually（seed 点不动）。
* **`closedSlab_localizedBad_P6ST4`**：`(g σ, y)` 处 `¬witness(ηout, C1out, C2out)` ⇒ CX-STAGE
  `LeftLocalizedBadAt_CXST`（time = `t`，Bad = fine-margin 坏，scalar 比，seed distance `d_{g t}(o, ·)`，
  `z = y`）——HREST2 `hlocH` 的 event-free 核。
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

namespace OrientedThreeStage.ClosedSlab

variable {P : OrientedThreeStage.{u}} {u σ : ℝ}

/-- 闭 slab 端点的 `C^k` comparison（`F = id`、`U = univ`）。 -/
theorem closedSlab_eventually_comparison_P6ST4 (S : P.ClosedSlab u σ) (k : ℕ) {δ : ℝ}
    (hδ : 0 < δ) :
    ∀ᶠ t in 𝓝[<] σ, Nonempty (MetricComparisonOn (fun _ => S.flow.base.metric t)
      (fun _ => S.flow.base.metric σ) (DifferentialGeometry.PartialDiffeomorph.refl
        (I := ThreeModel) P.Carrier) univ {0} k δ) := by
  classical
  have : IsManifold ThreeModel 1 P.Carrier := IsManifold.of_le (n := ∞) (by decide)
  have hδ'0 : 0 < min δ (1 / 2) := lt_min hδ (by norm_num)
  have hδ'1 : min δ (1 / 2) < 1 := (min_le_right _ _).trans_lt (by norm_num)
  obtain ⟨η, hη, hη1, hηdim, hηbud⟩ :=
    exists_metric_reference_change_delta (E := ThreeSpace) k hδ'0
  have hconv : ∀ᶠ t in 𝓝[<] σ, ∀ j : Fin (k + 1), ∀ y : P.Carrier,
      metricDerivNorm j (S.flow.base.metric t) (S.flow.base.metric σ) (S.flow.base.metric σ) y <
        η := by
    refine eventually_all.mpr fun j => ?_
    obtain ⟨d, hd, hb⟩ := S.smoothUpTo.terminal_convergence P S.lt isCompact_univ j hη
    filter_upwards [Ioo_mem_nhdsLT hd.2] with t ht
    exact fun y => hb t ht y (mem_univ y)
  filter_upwards [hconv] with t ht
  have hderiv : ∀ j : ℕ, j ≤ k → ∀ x ∈ (univ : Set P.Carrier),
      metricDerivNorm j (S.flow.base.metric σ) (S.flow.base.metric t) (S.flow.base.metric t) x ≤
        min δ (1 / 2) := by
    intro j hj x _
    exact metric_deriv_norm_reference_change_le (I := ThreeModel) isOpen_univ
      (S.flow.base.metric σ) (S.flow.base.metric t) (S.flow.base.metric σ) k hη.le hη1.le hηdim
      hηbud (fun y _ q _ => by rw [metricDerivNorm_self]; exact hη.le)
      (fun y _ q hq => (ht ⟨q, Nat.lt_succ_of_le hq⟩ y).le) x (mem_univ x) j hj
  have happly : ∀ x ∈ (univ : Set P.Carrier), ∀ v : Fin 2 → TangentSpace ThreeModel x,
      Tensor0SBundle.metricTensorField (S.flow.base.metric σ) x v =
        (S.flow.base.metric σ).inner
          ((DifferentialGeometry.PartialDiffeomorph.refl (I := ThreeModel) P.Carrier) x)
          (mfderiv ThreeModel ThreeModel
            (DifferentialGeometry.PartialDiffeomorph.refl (I := ThreeModel) P.Carrier) x (v 0))
          (mfderiv ThreeModel ThreeModel
            (DifferentialGeometry.PartialDiffeomorph.refl (I := ThreeModel) P.Carrier) x
              (v 1)) := by
    intro x _ v
    rw [Tensor0SBundle.metricTensorField_apply]
    have hid : ((DifferentialGeometry.PartialDiffeomorph.refl (I := ThreeModel) P.Carrier :
        PartialDiffeomorph ThreeModel ThreeModel P.Carrier P.Carrier ∞) : P.Carrier → P.Carrier) =
        id := rfl
    rw [hid, mfderiv_id]
    rfl
  let D := MapMetricApproximationOn.ofMetricDerivNorm (K := (univ : Set P.Carrier)) (p := k)
    (F := ((DifferentialGeometry.PartialDiffeomorph.refl (I := ThreeModel) P.Carrier :
      PartialDiffeomorph ThreeModel ThreeModel P.Carrier P.Carrier ∞) : P.Carrier → P.Carrier))
    (S.flow.base.metric σ) (S.flow.base.metric t) (S.flow.base.metric σ) hδ'0 hδ'1
    contMDiffOn_id happly hderiv
  exact ⟨(MetricComparisonOn.ofMapMetricApproximation D {0}).mono subset_rfl le_rfl
    (min_le_left _ _)⟩

/-- 闭 slab 中 `y` 属于 restrict 后的 incoming slab 的 terminal regular open（region = univ）。 -/
theorem mem_terminalRegularOpen_P6ST4 (S : P.ClosedSlab u σ) (y : P.Carrier) :
    y ∈ (S.restrictIncoming le_rfl S.lt le_rfl).terminalRegularOpen := by
  change y ∈ (S.restrictIncoming le_rfl S.lt le_rfl).terminalRegularRegion
  rw [S.terminalRegularRegion_eq_univ P]
  trivial

/-- 端点处 scalar 左连续：`R_{g t}(y) → R_{g σ}(y)`（`t → σ⁻`）。 -/
theorem tendsto_scalar_P6ST4 (S : P.ClosedSlab u σ) (y : P.Carrier) :
    Tendsto (fun t => metricScalarAt (S.flow.base.metric t) y) (𝓝[<] σ)
      (𝓝 (metricScalarAt (S.flow.base.metric σ) y)) := by
  have h := (S.endpointTerminalLimitMetric P).tendsto_metricScalarAt
    ⟨y, S.mem_terminalRegularOpen_P6ST4 y⟩
  have he : metricScalarAt (S.endpointTerminalLimitMetric P).metric
      ⟨y, S.mem_terminalRegularOpen_P6ST4 y⟩ = metricScalarAt (S.flow.base.metric σ) y :=
    metricScalarAt_restrictOpen _ _ _
  rw [he] at h
  exact h

/-- 端点处梯度界的真极限：`t → σ⁻` eventually `|dR_{g t}(y) u| ≤ C2 R √R |u|` ⇒ 端点同式
（`C2 ≤ C2'`）。 -/
theorem gradient_bound_of_eventually_P6ST4 (S : P.ClosedSlab u σ) (y : P.Carrier) {C2 C2' : ℝ}
    (hC : C2 ≤ C2') (hQ : 0 ≤ metricScalarAt (S.flow.base.metric σ) y)
    (hev : ∀ u' : TangentSpace ThreeModel y, ∀ᶠ t in 𝓝[<] σ,
      |(show ℝ from mfderiv ThreeModel 𝓘(ℝ, ℝ) (metricScalarAt (S.flow.base.metric t)) y u')| ≤
        C2 * metricScalarAt (S.flow.base.metric t) y *
          Real.sqrt (metricScalarAt (S.flow.base.metric t) y) *
          Real.sqrt ((S.flow.base.metric t).inner y u' u'))
    (w : TangentSpace ThreeModel y) :
    |(show ℝ from mfderiv ThreeModel 𝓘(ℝ, ℝ) (metricScalarAt (S.flow.base.metric σ)) y w)| ≤
      C2' * metricScalarAt (S.flow.base.metric σ) y *
        Real.sqrt (metricScalarAt (S.flow.base.metric σ) y) *
        Real.sqrt ((S.flow.base.metric σ).inner y w w) := by
  set G := S.restrictIncoming le_rfl S.lt le_rfl
  set y' : G.terminalRegularOpen := ⟨y, S.mem_terminalRegularOpen_P6ST4 y⟩
  have h1 := (S.endpointTerminalLimitMetric P).tendsto_scalar_differential y' w
  have h1' : Tendsto (fun t => (show ℝ from mfderiv ThreeModel 𝓘(ℝ, ℝ)
      (metricScalarAt (S.flow.base.metric t)) y w)) (𝓝[<] σ)
      (𝓝 (show ℝ from mfderiv ThreeModel 𝓘(ℝ, ℝ) (metricScalarAt (S.flow.base.metric σ)) y w)) := by
    have hl := OrientedThreeStage.IncomingSlab.scalar_differential_restrictOpen_P6ST3 G
      (S.flow.base.metric σ) y' w
    have hlim : (show ℝ from mfderiv ThreeModel 𝓘(ℝ, ℝ)
        (metricScalarAt (S.endpointTerminalLimitMetric P).metric) y' w) =
        (show ℝ from mfderiv ThreeModel 𝓘(ℝ, ℝ) (metricScalarAt (S.flow.base.metric σ)) y w) :=
      hl
    rw [hlim] at h1
    refine h1.congr fun t => ?_
    exact OrientedThreeStage.IncomingSlab.scalar_differential_restrictOpen_P6ST3 G _ y' w
  have h2 := (S.endpointTerminalLimitMetric P).tendsto_inner y' w w
  have h2' : Tendsto (fun t => (S.flow.base.metric t).inner y w w) (𝓝[<] σ)
      (𝓝 ((S.flow.base.metric σ).inner y w w)) := h2
  have hsc := S.tendsto_scalar_P6ST4 y
  have hR := ((tendsto_const_nhds (x := C2)).mul hsc).mul hsc.sqrt
  have hlim := le_of_tendsto_of_tendsto h1'.abs (hR.mul h2'.sqrt) (hev w)
  exact hlim.trans (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_right hC hQ) (Real.sqrt_nonneg _)) (Real.sqrt_nonneg _))

/-- **`J = id` 局部扰动 transfer**：eventually 的 fine-margin witness ⇒ 端点 witness。 -/
theorem spatialWitness_of_closedSlab_P6ST4 (S : P.ClosedSlab u σ) {y : P.Carrier}
    {ηfine ηout C1 C2 m : ℝ} (hle : ηfine ≤ neckModelTolerance (ηout / 2))
    (hηout : ηout < 1 / 11) (hC1 : 1 ≤ C1) (hC2 : 1 ≤ C2) (hm0 : 0 < m) (hm1 : m ≤ 1 / 2)
    (hQ : 0 < metricScalarAt (S.flow.base.metric σ) y)
    (hfine : ∀ᶠ t in 𝓝[<] σ, ∃ W : SpatialCanonicalWitness (S.flow.base.metric t) ηfine C1 C2 y,
      W.capTubeHasNeckChart ηfine ∧ W.HasMargins m)
    {C1out C2out : ℝ} (h1 : 2 * C1 ≤ C1out) (h2 : 1000 * C2 ≤ C2out) :
    ∃ W : SpatialCanonicalWitness (S.flow.base.metric σ) ηout C1out C2out y,
      W.capTubeHasNeckChart ηout := by
  obtain ⟨t₀, W₀, -, -⟩ := hfine.exists
  have hf0 : 0 < ηfine := W₀.eps_pos
  have hfo : ηfine ≤ ηout / 2 := hle.trans (neckModelTolerance_le _)
  have hα : 0 < ηout / 2 := by linarith
  have hsmall : 2 * (ηout / 2) < 1 / 11 := by linarith
  obtain ⟨δ, hδ, hT⟩ :=
    SpatialCanonicalWitness.exists_uniform_comparison_transport_tolerance (P := P.Carrier) hα
      hsmall hm0 hm1 hC1 hC2 (half_pos hQ)
  have hlow : ∀ᶠ t in 𝓝[<] σ, metricScalarAt (S.flow.base.metric σ) y / 2 ≤
      metricScalarAt (S.flow.base.metric t) y :=
    (S.tendsto_scalar_P6ST4 y).eventually (eventually_ge_nhds (half_lt_self hQ))
  have hC2o : C2 ≤ C2out := by linarith
  have hgrad := S.gradient_bound_of_eventually_P6ST4 y hC2o hQ.le fun u' => by
    filter_upwards [hfine] with t ht
    obtain ⟨W, -, -⟩ := ht
    exact W.gradient u'
  obtain ⟨t, ⟨W, hWc, hWm⟩, ⟨Cmp⟩, hQt⟩ :=
    (hfine.and ((S.closedSlab_eventually_comparison_P6ST4
      (max 2 ⌈(2 * (ηout / 2))⁻¹⌉₊) hδ).and hlow)).exists
  have hnt : neckModelTolerance (ηout / 2) < 1 / 11 :=
    (neckModelTolerance_le _).trans_lt (by linarith)
  have hW'c := hWc.mono_eps hle hnt hle hnt
  have hW'm := hasMargins_monoEps_P6ST2 hWm hle hnt
  have hcpt := (Geometry.Metric.isClosed_riemannianClosedBallOf
    (S.flow.base.metric t) y
    ((8 * C1 + 3 * ((ηout / 2)⁻¹ + 7) * Real.sqrt C2) /
      Real.sqrt (metricScalarAt (S.flow.base.metric t) y))).isCompact
  obtain ⟨Wo, hWo, -⟩ := hT (S.flow.base.metric t) y (W.monoEps hle hnt) hW'c hW'm hQt ⊤ hcpt
    (subset_univ _) P.Carrier (S.flow.base.metric σ)
    (DifferentialGeometry.PartialDiffeomorph.refl (I := ThreeModel) P.Carrier) (subset_univ _)
    Cmp C2out h2 hgrad
  have h2α : 2 * (ηout / 2) = ηout := by ring
  rw [← h2α]
  exact ⟨Wo.enlargeConstants h1 le_rfl, hWo.enlarge_constants h1 le_rfl⟩

/-- seed 点不动时的距离左上半连续：`d_{g t}(o, y) ≤ d_{g σ}(o, y) + η` eventually。 -/
theorem closedSlab_eventually_edist_le_P6ST4 (S : P.ClosedSlab u σ) (o y : P.Carrier) {η : ℝ}
    (hη : 0 < η) :
    ∀ᶠ t in 𝓝[<] σ, riemannianEDistOf (I := ThreeModel) (S.flow.base.metric t) o y ≤
      riemannianEDistOf (I := ThreeModel) (S.flow.base.metric σ) o y + ENNReal.ofReal η := by
  by_cases htop : riemannianEDistOf (I := ThreeModel) (S.flow.base.metric σ) o y = ⊤
  · exact Eventually.of_forall fun t => by rw [htop, top_add]; exact le_top
  set d := (riemannianEDistOf (I := ThreeModel) (S.flow.base.metric σ) o y).toReal with hddef
  have hd0 : 0 ≤ d := ENNReal.toReal_nonneg
  have hd : riemannianEDistOf (I := ThreeModel) (S.flow.base.metric σ) o y = ENNReal.ofReal d :=
    (ENNReal.ofReal_toReal htop).symm
  set ε := min (1 / 2) (η / (2 * (d + 1))) with hεdef
  have hε0 : 0 < ε := lt_min (by norm_num) (by positivity)
  have hε1 : ε ≤ 1 / 2 := min_le_left _ _
  set L := Real.sqrt ((1 - ε)⁻¹) with hLdef
  have hL0 : 0 < L := Real.sqrt_pos.mpr (inv_pos.mpr (by linarith))
  have hL2 : L ^ 2 = (1 - ε)⁻¹ := Real.sq_sqrt (inv_nonneg.mpr (by linarith))
  have hLd : L * d < d + η := MetricCutCapEvent.seed_eps_real_P6ST4 hd0 hη
  filter_upwards [S.closedSlab_eventually_comparison_P6ST4 0 hε0] with t ⟨C⟩
  have hR : 0 < d + η := by positivity
  have hlower : ∀ z ∈ riemannianClosedBallOf (I := ThreeModel) (S.flow.base.metric t) o (d + η),
      ∀ v : TangentSpace ThreeModel z, (S.flow.base.metric t).inner z v v ≤
        L ^ 2 * (S.flow.base.metric σ).inner
          ((DifferentialGeometry.PartialDiffeomorph.refl (I := ThreeModel) P.Carrier) z)
          (mfderiv ThreeModel ThreeModel
            (DifferentialGeometry.PartialDiffeomorph.refl (I := ThreeModel) P.Carrier) z v)
          (mfderiv ThreeModel ThreeModel
            (DifferentialGeometry.PartialDiffeomorph.refl (I := ThreeModel) P.Carrier) z v) := by
    intro z _ v
    have heq := C.pullback_eq 0 z (mem_univ z) (fun _ => v)
    have hcm := (C.equivalence 0 rfl z (mem_univ z) v).1
    rw [heq] at hcm
    rw [hL2, ← div_eq_inv_mul, le_div_iff₀ (by linarith)]
    linarith
  have hcap := DifferentialGeometry.PartialDiffeomorph.ball_subset_image_closedBall_of_metric_lower
    (S.flow.base.metric t) (S.flow.base.metric σ)
    (DifferentialGeometry.PartialDiffeomorph.refl (I := ThreeModel) P.Carrier) o hR hL0
    (Geometry.Metric.isClosed_riemannianClosedBallOf _ _ _).isCompact (fun _ _ => mem_univ _)
    hlower
  have hy : y ∈ riemannianBallOf (I := ThreeModel) (S.flow.base.metric σ)
      ((DifferentialGeometry.PartialDiffeomorph.refl (I := ThreeModel) P.Carrier) o)
      ((d + η) / L) := by
    change riemannianEDistOf (I := ThreeModel) (S.flow.base.metric σ) o y <
      ENNReal.ofReal ((d + η) / L)
    rw [hd, ENNReal.ofReal_lt_ofReal_iff (by positivity), lt_div_iff₀ hL0]
    linarith
  obtain ⟨z, hz, hzy⟩ := hcap hy
  have hzy' : z = y := hzy
  have hz' : riemannianEDistOf (I := ThreeModel) (S.flow.base.metric t) o y ≤
      ENNReal.ofReal (d + η) := hzy' ▸ hz
  refine hz'.trans ?_
  rw [hd, ENNReal.ofReal_add hd0 hη.le]

/-- **`hlocH` 的 event-free 核**：`(g σ, y)` 处 `¬witness(ηout, C1out, C2out)`、`R_{g σ}(y) > 0` ⇒
`LeftLocalizedBadAt_CXST`（time = `t`，fine-margin 坏 `(ηfine, C1, C2, m)`，scalar 比，seed distance
`d_{g t}(o, ·)`，余量 `L/(4√R)`；局部化点取 `z = y`）。 -/
theorem closedSlab_localizedBad_P6ST4 (S : P.ClosedSlab u σ) {y o : P.Carrier}
    {ηfine ηout C1 C2 m : ℝ} (hle : ηfine ≤ neckModelTolerance (ηout / 2))
    (hηout : ηout < 1 / 11) (hC1 : 1 ≤ C1) (hC2 : 1 ≤ C2) (hm0 : 0 < m) (hm1 : m ≤ 1 / 2)
    (hQ : 0 < metricScalarAt (S.flow.base.metric σ) y) {C1out C2out : ℝ}
    (h1 : 2 * C1 ≤ C1out) (h2 : 1000 * C2 ≤ C2out)
    (hnot : ¬ ∃ W : SpatialCanonicalWitness (S.flow.base.metric σ) ηout C1out C2out y,
      W.capTubeHasNeckChart ηout) (L : ℝ) (hL : 0 < L) :
    LeftLocalizedBadAt_CXST (X := fun _ : ℝ => P.Carrier) (fun t : ℝ => t)
      (fun t z => ¬ ∃ W : SpatialCanonicalWitness (S.flow.base.metric t) ηfine C1 C2 z,
        W.capTubeHasNeckChart ηfine ∧ W.HasMargins m)
      (fun t z => metricScalarAt (S.flow.base.metric t) z)
      (fun t z => riemannianEDistOf (I := ThreeModel) (S.flow.base.metric t) o z)
      σ (metricScalarAt (S.flow.base.metric σ) y) L
      (riemannianEDistOf (I := ThreeModel) (S.flow.base.metric σ) o y) := by
  intro δ hδ ε hε
  have hbad : ∃ᶠ t in 𝓝[<] σ, ¬ ∃ W : SpatialCanonicalWitness (S.flow.base.metric t) ηfine C1 C2 y,
      W.capTubeHasNeckChart ηfine ∧ W.HasMargins m := by
    intro h
    exact hnot (S.spatialWitness_of_closedSlab_P6ST4 hle hηout hC1 hC2 hm0 hm1 hQ
      (h.mono fun _ hn => not_not.mp hn) h1 h2)
  have hwin : ∀ᶠ t in 𝓝[<] σ, t ∈ Ioo (σ - δ) σ := Ioo_mem_nhdsLT (by linarith)
  have hratio : ∀ᶠ t in 𝓝[<] σ,
      |metricScalarAt (S.flow.base.metric t) y / metricScalarAt (S.flow.base.metric σ) y - 1| <
        ε := by
    have h := (S.tendsto_scalar_P6ST4 y).div_const (metricScalarAt (S.flow.base.metric σ) y)
    rw [div_self hQ.ne'] at h
    exact (Metric.tendsto_nhds.mp h ε hε).mono fun t ht => by
      rw [Real.dist_eq] at ht
      exact ht
  have hdist := S.closedSlab_eventually_edist_le_P6ST4 o y
    (by positivity : 0 < L / (4 * Real.sqrt (metricScalarAt (S.flow.base.metric σ) y)))
  obtain ⟨t, hb, ⟨hw, hr⟩, hdi⟩ := (hbad.and_eventually ((hwin.and hratio).and hdist)).exists
  exact ⟨t, y, hw.1, hw.2, hb, hr, hdi⟩

end OrientedThreeStage.ClosedSlab

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
