import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.P6LimitNoncollapseP6B
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.TracedRegionAncientLimitTimeControl

/-!
# TimeControl 的局部化副本：time-Lipschitz survivor-map 古代极限（O-CH11-P6D G2，后缀 `_P6L`）

原定理：private
`ObservedHistory.exists_ancient_pointed_flow_limit_of_isTracedRegion_of_admissible_times`
（`ST/TracedRegionAncientLimitTimeControl.lean:345`）及其包装
`exists_ancient_pointed_flow_limit_with_time_lipschitz_survivor_maps_of_noncollapsed_before`
（`:781`），合并成一个公开定理（名字照 P6B L8c 用 `…_of_traced_seed_P6L`：原名 + `_P6L` 超
100 列）。它是 `TracedRegionAncientLimitScalarBound:42` 的输入（`hlip` / `hscal` / `hlow`）。

**改动的前提（只有两类，与 P6B 的 M8 装配 `exists_local_ancient_limit_kappa_noncollapsed_P6B`
逐字同形）**：
* 全局 `hnc`（`∀ v < t₀`, `∀ p`）→ 基点种子体积 `hseed` + trace-local `hkappa`（尺度 `≤ ρnc n`，
  `ρnc n √R n → ∞`）。原证明用 `hnc` 的三处：(1) `hvolX` → 树内 `FILL910.hvol_of_traced_seed`（照
  P6B L8c）；(2) 输出 block 的局部 `hnc` 与 (3) `hncW`（`κ/250` 用）→ P6B 单步
  `volume_ball_ge_of_survivor_maps_of_traced_kappa_P6B`；`κ/250` 结论按 P6B M8 走
  `isKappaNoncollapsed_of_local_flow_limit_of_time_lt`（`radii = ρnc n √R n`）。
* 全局 `hpinch`（`∀ v ≤ t n`, `∀ x`）→ trace-local `hpinch`：原证明只在 survivor 点 `f j x` 用
  （`hpinchW`），成员关系 = survivor maps 本身给出的 backward trace（`tr0.restrictFirst`），
  `x ∈ W k n = B(y n, (k+3)/√R n)`，`v ≥ t n − 2(k+2)/R n`。
`t₀` / admissible-times 参数 `A` 消失（输出 block 的 `t n + σ/R n < t₀ n` 子句随之删去，同 P6B L8c）。
`hlipW` / `hscalW` / `hlowW` 证明体逐字照抄（只用 survivor data 的曲率界与上面的 `hpinchW`）。
-/

set_option autoImplicit false

noncomputable section

open Set Filter TopologicalSpace
open DifferentialGeometry.Geometry.Curvature DifferentialGeometry.Tensor0SBundle
open DifferentialGeometry.CheegerGromovCompactness
open scoped Manifold ContDiff Topology NNReal ENNReal

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

open private ObservedHistory.isScaledSurvivorData
  ObservedHistory.exists_isScaledSurvivorData_of_isTracedRegion from
  DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.TracedRegionAncientLimitData

open private ObservedHistory.scaleMetric_restrictOpenOfSubset
  ObservedHistory.comp_inclusion_eq_of_backward_maps ObservedHistory.mem_Icc_of_mem_window
  ObservedHistory.isCompact_riemannianClosedBallOf_restrictOpen
  ObservedHistory.exists_curvDerivNorm_bound_of_window
  ObservedHistory.riemannianBallOf_scaleMetric_eq from
  DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.TracedRegionAncientLimit

namespace ObservedHistory

open Perelman.CanonicalNeighborhood.FiniteHorn
  (neg_two_mul_inner_le_metricRicciAt_of_curvatureOperatorLowerBoundAt
    isKappaNoncollapsed_of_local_flow_limit_of_time_lt)

universe u

private local instance : NeZero (Module.finrank ℝ ThreeSpace) := ⟨by simp⟩

attribute [local instance] PointedRiemannianManifold.topology PointedRiemannianManifold.charted
  PointedRiemannianManifold.smooth PointedRiemannianManifold.t2
  PointedRiemannianManifold.sigmaCompact

private local instance {M : Type u} [TopologicalSpace M] [ChartedSpace ThreeSpace M]
    [SigmaCompactSpace M] (U : Opens M) : SigmaCompactSpace U :=
  isSigmaCompact_iff_sigmaCompactSpace.mp
    (Geometry.isSigmaCompact_of_isOpen ThreeModel U.isOpen)

private theorem metricScalarAt_le_of_curvDerivNormSq_zero_le_P6L {M : Type*} [TopologicalSpace M]
    [ChartedSpace ThreeSpace M] [IsManifold ThreeModel ∞ M] [T2Space M]
    (g : SmoothRiemannianMetric ThreeModel M) (x : M) {K : ℝ}
    (h : curvDerivNormSq 0 g x ≤ K ^ 2) :
    metricScalarAt g x ≤ (Module.finrank ℝ ThreeSpace : ℝ) ^ 2 * |K| := by
  have hsq : Real.sqrt (normSq0S g x 4 (metricRm04At g x)) ≤ |K| := by
    rw [← Real.sqrt_sq_eq_abs]
    exact Real.sqrt_le_sqrt h
  exact (le_abs_self _).trans ((scalar_abs_le_rm g x).trans
    (mul_le_mul_of_nonneg_left hsq (by positivity)))


/-- TimeControl:345 + :781 的局部化（`_P6L`）：traced regions + 基点种子体积 + trace-local κ +
trace-local pinching ⇒ 带 survivor maps、局部 `hnc`、时间 Lipschitz / 标量 / 度量比较界的古代
pointed 极限，且极限流对每个 `ρ' > 0` 是 `κ/250`-noncollapsed。无任何全局假设。 -/
theorem exists_ancient_pointed_flow_limit_with_time_lipschitz_survivor_maps_of_traced_seed_P6L
    (H : ℕ → ObservedHistory.{u}) (t : ∀ n, Icc (0 : ℝ) (H n).horizon)
    (y : ∀ n, ((H n).stageAt (t n)).Carrier) (R : ℕ → ℝ) (hR : ∀ n, 0 < R n)
    (hRlim : Tendsto R atTop atTop)
    (htraced : ∀ A T : ℝ, 0 < A → 0 < T → ∃ K : ℝ, 0 ≤ K ∧ ∀ᶠ n in atTop,
      (H n).isTracedRegion (t n) (y n) (A / Real.sqrt (R n)) (T / R n) (K * R n))
    {r₀ w : ℝ} (hr₀ : 0 < r₀) (hw : 0 < w)
    (hseed : ∀ᶠ n in atTop,
      ENNReal.ofReal (w * (r₀ / Real.sqrt (R n)) ^ 3) ≤
        Integral.Measure.riemannianVolumeMeasure ThreeModel ((H n).stageAt (t n)).Carrier
          ((H n).stageMetric ((H n).activeStage (t n)) (t n))
          (riemannianBallOf ((H n).stageMetric ((H n).activeStage (t n)) (t n)) (y n)
            (r₀ / Real.sqrt (R n))))
    {κ : ℝ} (hκ : 0 < κ) (ρnc : ℕ → ℝ)
    (hradii : Tendsto (fun n => ρnc n * Real.sqrt (R n)) atTop atTop)
    (hkappa : ∀ D T : ℝ, 0 < D → 0 < T → ∀ᶠ n in atTop,
      ∀ x ∈ riemannianBallOf ((H n).stageMetric ((H n).activeStage (t n)) (t n)) (y n)
          (D / Real.sqrt (R n)),
      ∀ (v : Icc (0 : ℝ) (H n).horizon) (hvt : v ≤ t n), (t n : ℝ) - T / R n ≤ v →
      ∀ tr : BackwardPointTrace (H n) ((H n).activeStage v) ((H n).activeStage (t n))
        ((H n).activeStage_mono hvt) x,
      ∀ r'' : ℝ, 0 < r'' → r'' ≤ ρnc n →
        (H n).isParabolicallyRmControlledBall v
          (tr.point ((H n).activeStage v) le_rfl ((H n).activeStage_mono hvt)) r'' →
        ENNReal.ofReal (κ * r'' ^ 3) ≤
          Geometry.Collapse.ballVolume ((H n).stageMetric ((H n).activeStage v) v)
            (tr.point ((H n).activeStage v) le_rfl ((H n).activeStage_mono hvt)) r'')
    {Phi : ℝ → ℝ} (hPhi : Perelman.AdmissiblePinchingFunction Phi)
    (hpinch : ∀ D T : ℝ, 0 < D → 0 < T → ∀ᶠ n in atTop,
      ∀ x ∈ riemannianBallOf ((H n).stageMetric ((H n).activeStage (t n)) (t n)) (y n)
          (D / Real.sqrt (R n)),
      ∀ (v : Icc (0 : ℝ) (H n).horizon) (hvt : v ≤ t n), (t n : ℝ) - T / R n ≤ v →
      ∀ tr : BackwardPointTrace (H n) ((H n).activeStage v) ((H n).activeStage (t n))
        ((H n).activeStage_mono hvt) x,
        curvatureOperatorLowerBoundAt ((H n).stageMetric ((H n).activeStage v) v)
          (tr.point ((H n).activeStage v) le_rfl ((H n).activeStage_mono hvt))
          (metricAlgebraicCurvatureTensorAt ((H n).stageMetric ((H n).activeStage v) v)
            (tr.point ((H n).activeStage v) le_rfl ((H n).activeStage_mono hvt)))
          (Phi (metricScalarAt ((H n).stageMetric ((H n).activeStage v) v)
            (tr.point ((H n).activeStage v) le_rfl ((H n).activeStage_mono hvt))))) :
    let X : PointedRiemannianSeq.{u, 0, 0} ThreeModel :=
      { obj := fun n =>
          { M := ((H n).stageAt (t n)).Carrier
            basepoint := y n
            metric := scaleMetric (R n) (hR n)
              ((H n).stageMetric ((H n).activeStage (t n)) (t n)) } }
    ∃ (W : ∀ (_ : ℕ) (n : ℕ), Opens (X.obj n).M)
      (h : ∀ k n, ℝ → SmoothRiemannianMetric ThreeModel (W k n)),
      (∀ k : ℕ, ∀ᶠ n in atTop,
        (W k n : Set (X.obj n).M) =
          riemannianBallOf (X.obj n).metric (X.obj n).basepoint ((k + 3 : ℕ) : ℝ) ∧
        IsSolutionOn ({ base.metric := h k n } : SolutionOn (I := ThreeModel) (M := W k n)
          (RealTimeInterval.closed (-((k + 2 : ℕ) : ℝ)) 0
            (neg_nonpos.mpr (Nat.cast_nonneg _)))) ∧
        (∀ s ∈ Icc (-((k + 2 : ℕ) : ℝ)) 0,
          (t n : ℝ) + s / R n ∈ (H n).stageDomain ((H n).activeStage (t n)) →
          h k n s = scaleMetric (R n) (hR n)
            (((H n).stageMetric ((H n).activeStage (t n)) ((t n : ℝ) + s / R n)).restrictOpen
              (W k n))) ∧
        (∃ (a : Icc (0 : ℝ) (H n).horizon) (hat : a ≤ t n),
          (a : ℝ) = t n - 2 * ((k + 2 : ℕ) : ℝ) / R n ∧
          ∃ f : (j : (H n).StageInterval ((H n).activeStage a) ((H n).activeStage (t n))) →
              W k n → ((H n).stage j.val).Carrier,
            ∃ hf : ∀ j, IsLocalDiffeomorph ThreeModel ThreeModel ∞ (f j),
              (∀ j, Function.Injective (f j)) ∧
              (∀ (i : Fin (H n).eventCount) (hi : (H n).activeStage a ≤ i.castSucc)
                  (hl : i.succ ≤ (H n).activeStage (t n)), ∀ x : W k n,
                ((H n).event i).RegularCrossing
                  (f ⟨i.castSucc, hi, i.castSucc_lt_succ.le.trans hl⟩ x)
                  (f ⟨i.succ, hi.trans i.castSucc_lt_succ.le, hl⟩ x)) ∧
              (∀ x : W k n,
                f ⟨(H n).activeStage (t n), (H n).activeStage_mono hat, le_rfl⟩ x = x.val) ∧
              ∀ s ∈ Icc (-(2 * ((k + 2 : ℕ) : ℝ))) 0,
                ∀ j : (H n).StageInterval ((H n).activeStage a) ((H n).activeStage (t n)),
                  (t n : ℝ) + s / R n ∈ (H n).stageDomain j.val →
                    h k n s = scaleMetric (R n) (hR n)
                      (localPullMetric ((H n).stageMetric j.val ((t n : ℝ) + s / R n)) (f j)
                        (hf j))) ∧
        ∀ σ ∈ Icc (-((k + 1 : ℕ) : ℝ)) 0, ∀ z : W k n, ∀ r : ℝ, 0 < r →
          r ≤ ρnc n * Real.sqrt (R n) → Icc (σ - r ^ 2) σ ⊆ Icc (-((k + 2 : ℕ) : ℝ)) 0 →
          IsCompact (riemannianClosedBallOf (h k n σ) z r) →
          (∀ s ∈ Icc (σ - r ^ 2) σ, ∀ w ∈ riemannianBallOf (h k n σ) z r,
            r ^ 4 * curvDerivNormSq 0 (h k n s) w ≤ 1) →
          ENNReal.ofReal (κ * r ^ 3) ≤
            Integral.Measure.riemannianVolumeMeasure ThreeModel (W k n) (h k n σ)
              (riemannianBallOf (h k n σ) z r)) ∧
      (∀ k p : ℕ, ∃ L : ℝ, ∀ᶠ n in atTop, ∀ σ ∈ Icc (-((k + 1 : ℕ) : ℝ)) 0,
        ∀ σ' ∈ Icc (-((k + 1 : ℕ) : ℝ)) 0, ∀ z : W k n, (z : (X.obj n).M) ∈
            riemannianClosedBallOf (X.obj n).metric (X.obj n).basepoint ((k + 2 : ℕ) : ℝ) →
          ∀ a : ℕ, a ≤ p → metricDerivNorm a (h k n σ) (h k n σ') (h k n 0) z ≤ L * |σ - σ'|) ∧
      (∀ k : ℕ, ∃ B : ℝ, ∀ᶠ n in atTop, ∀ s ∈ Icc (-((k + 2 : ℕ) : ℝ)) 0, ∀ x : W k n,
        metricScalarAt (h k n s) x ≤ B) ∧
      (∀ k : ℕ, ∀ᶠ n in atTop, ∀ s ∈ Icc (-((k + 1 : ℕ) : ℝ)) 0, ∀ (x : W k n)
        (u : TangentSpace ThreeModel x),
        (h k n 0).inner x u u ≤ Real.exp 2 * (h k n s).inner x u u) ∧
      ∃ (f : ℕ → ℕ), StrictMono f ∧
        ∃ (P : PointedRiemannianManifold.{u, 0, 0} ThreeModel)
          (F : PointedRiemannianConvergenceMaps X P f),
          (∃ C : MetricConvergenceData F,
            ∀ n, C.domain n = CanonicalMetricCompactness.canonicalSourceData F n) ∧
          MetricComplete P ∧ ConnectedSpace P.M ∧
          (∀ R : ℝ, 0 < R → ∀ᶠ n in atTop,
            riemannianClosedBallOf (X.obj (f n)).metric (X.obj (f n)).basepoint R ⊆
              F.target n) ∧
          ∃ (V : ℕ → Opens P.M) (N : ℕ → ℕ),
            (∀ k, (V k : Set P.M) =
              riemannianBallOf P.metric P.basepoint (((k + 1 : ℕ) : ℝ) / 2)) ∧
            (∀ k j, N k ≤ j → (V k : Set P.M) ⊆ F.source j) ∧
            ∃ (φ : ∀ k j, N k ≤ j → V k → W k (f j))
              (hφ : ∀ k j (hj : N k ≤ j),
                IsLocalDiffeomorph ThreeModel ThreeModel ∞ (φ k j hj)),
              (∀ k j (hj : N k ≤ j) (z : V k), ((φ k j hj z : W k (f j)) : (X.obj (f j)).M) =
                F.map j z) ∧
              ∃ G : ℝ → SmoothRiemannianMetric ThreeModel P.M,
                G 0 = P.metric ∧
                IsSolutionOn ({ base.metric := G } : SolutionOn (I := ThreeModel) (M := P.M)
                  (RealTimeInterval.infiniteClosed 0 0 le_rfl)) ∧
                ∃ ψ : ℕ → ℕ, StrictMono ψ ∧
                  (∀ k (K : Set (V k)), IsCompact K → ∀ p : ℕ, ∀ η : ℝ, 0 < η →
                    ∃ j₀ : ℕ, ∀ i ≥ j₀, ∃ hi : N k ≤ ψ i,
                      ∀ t ∈ Icc (-((k + 1 : ℕ) : ℝ)) 0,
                        metricDerivNormSupOn K p
                          (localPullMetric (h k (f (ψ i)) t) (φ k (ψ i) hi) (hφ k (ψ i) hi))
                          ((G t).restrictOpen (V k)) (P.metric.restrictOpen (V k)) < η) ∧
                  ∀ ρ' : ℝ, 0 < ρ' → Perelman.ParabolicallyKappaNoncollapsedBelowScale
                    ({ base.metric := G } : SolutionOn (I := ThreeModel) (M := P.M)
                      (RealTimeInterval.infiniteClosed 0 0 le_rfl)) (κ / 250) ρ' := by
  intro X
  have hθ (k : ℕ) : 0 < 2 * ((k + 2 : ℕ) : ℝ) := by positivity
  choose K hK0 hKev using fun k : ℕ => htraced ((k + 3 : ℕ) : ℝ) (2 * ((k + 2 : ℕ) : ℝ))
    (by positivity) (hθ k)
  have hex : ∀ k n, ∃ (Wk : Opens (X.obj n).M) (g : ℝ → SmoothRiemannianMetric ThreeModel Wk),
      (H n).isTracedRegion (t n) (y n) (((k + 3 : ℕ) : ℝ) / Real.sqrt (R n))
          (2 * ((k + 2 : ℕ) : ℝ) / R n) (K k * R n) →
        ObservedHistory.isScaledSurvivorData (H n) (t n) (y n) (R n)
          (((k + 3 : ℕ) : ℝ) / Real.sqrt (R n)) (2 * ((k + 2 : ℕ) : ℝ)) (K k) (hR n) Wk g := by
    intro k n
    by_cases htr : (H n).isTracedRegion (t n) (y n) (((k + 3 : ℕ) : ℝ) / Real.sqrt (R n))
        (2 * ((k + 2 : ℕ) : ℝ) / R n) (K k * R n)
    · obtain ⟨Wk, g, hg⟩ :=
        ObservedHistory.exists_isScaledSurvivorData_of_isTracedRegion (H n) (t n) (y n) (hR n)
          (hθ k) htr
      exact ⟨Wk, g, fun _ => hg⟩
    · exact ⟨⊤, fun _ => (X.obj n).metric.restrictOpen ⊤, fun hh => absurd hh htr⟩
  choose W h hWh using hex
  have hsurv (k : ℕ) : ∀ᶠ n in atTop,
      ObservedHistory.isScaledSurvivorData (H n) (t n) (y n) (R n)
        (((k + 3 : ℕ) : ℝ) / Real.sqrt (R n))
        (2 * ((k + 2 : ℕ) : ℝ)) (K k) (hR n) (W k n) (h k n) :=
    (hKev k).mono fun n hn => hWh k n hn
  have hWset (k n : ℕ) (hn : ObservedHistory.isScaledSurvivorData (H n) (t n) (y n) (R n)
      (((k + 3 : ℕ) : ℝ) / Real.sqrt (R n)) (2 * ((k + 2 : ℕ) : ℝ)) (K k) (hR n) (W k n)
      (h k n)) :
      (W k n : Set (X.obj n).M) =
        riemannianBallOf (X.obj n).metric (X.obj n).basepoint ((k + 3 : ℕ) : ℝ) := by
    rw [hn.1]
    exact (ObservedHistory.riemannianBallOf_scaleMetric_eq _ (hR n) _ _).symm
  have hcompact : ∀ r : ℝ, 0 < r → ∀ᶠ n in atTop,
      IsCompact (riemannianClosedBallOf (X.obj n).metric (X.obj n).basepoint r) :=
    fun r _ => Eventually.of_forall fun n =>
      (Geometry.Metric.isClosed_riemannianClosedBallOf (X.obj n).metric _ r).isCompact
  have hsubW (k n : ℕ) (hn : ObservedHistory.isScaledSurvivorData (H n) (t n) (y n) (R n)
      (((k + 3 : ℕ) : ℝ) / Real.sqrt (R n)) (2 * ((k + 2 : ℕ) : ℝ)) (K k) (hR n) (W k n)
      (h k n)) :
      riemannianClosedBallOf (X.obj n).metric (X.obj n).basepoint ((k + 2 : ℕ) : ℝ) ⊆
        W k n := by
    intro z hz
    rw [hWset k n hn]
    exact lt_of_le_of_lt hz ((ENNReal.ofReal_lt_ofReal_iff (by positivity)).mpr
      (by push_cast; linarith))
  have hball : ∀ k : ℕ, ∀ᶠ n in atTop,
      riemannianClosedBallOf (X.obj n).metric (X.obj n).basepoint ((k + 1 : ℕ) : ℝ) ⊆
        W k n := by
    intro k
    filter_upwards [hsurv k] with n hn
    exact (riemannianClosedBallOf_mono _ _ (by push_cast; linarith)).trans (hsubW k n hn)
  have hsol : ∀ k : ℕ, ∀ᶠ n in atTop, IsSolutionOn ({ base.metric := h k n } :
      SolutionOn (I := ThreeModel) (M := W k n)
        (RealTimeInterval.closed (-((k + 2 : ℕ) : ℝ)) 0
          (neg_nonpos.mpr (Nat.cast_nonneg _)))) := by
    intro k
    filter_upwards [hsurv k] with n hn
    exact hn.2.1 ((k + 2 : ℕ) : ℝ) (Nat.cast_nonneg _)
      (by have := (Nat.cast_nonneg (k + 2) : (0 : ℝ) ≤ _); linarith)
  have hzero : ∀ k : ℕ, ∀ᶠ n in atTop, h k n 0 = (X.obj n).metric.restrictOpen (W k n) := by
    intro k
    filter_upwards [hsurv k] with n hn
    exact hn.2.2.1
  have hjets : ∀ k m : ℕ, ∃ B : ℝ, 0 ≤ B ∧ ∀ᶠ n in atTop,
      ∀ s ∈ Icc (-((k + 1 : ℕ) : ℝ)) 0, ∀ x : W k n,
        (x : (X.obj n).M) ∈
          riemannianClosedBallOf (X.obj n).metric (X.obj n).basepoint ((k + 1 : ℕ) : ℝ) →
        curvDerivNorm m (h k n s) x ≤ B := by
    intro k m
    obtain ⟨B, hB0, hB⟩ := ObservedHistory.exists_curvDerivNorm_bound_of_window (hθ k) (K := K k)
    refine ⟨B m, hB0 m, ?_⟩
    filter_upwards [hsurv k] with n hn s hs x hx
    have hcpt : IsCompact (riemannianClosedBallOf (h k n 0) x 1) := by
      rw [hn.2.2.1]
      apply ObservedHistory.isCompact_riemannianClosedBallOf_restrictOpen
      refine (riemannianClosedBallOf_subset_of_add_radius_le _ (Nat.cast_nonneg _) zero_le_one
        ?_ hx).trans (hsubW k n hn)
      push_cast
      linarith
    refine hB (h k n) (hn.2.1 _ (hθ k).le le_rfl) hn.2.2.2.1 x hcpt m s ⟨?_, hs.2⟩
    have := hs.1
    push_cast at this ⊢
    linarith
  have hcompat : ∀ k l : ℕ, ∀ᶠ n in atTop, ∀ s ∈ Icc (-((min k l + 1 : ℕ) : ℝ)) 0,
      (h k n s).restrictOpenOfSubset (inf_le_left : W k n ⊓ W l n ≤ W k n) =
        (h l n s).restrictOpenOfSubset (inf_le_right : W k n ⊓ W l n ≤ W l n) := by
    intro k l
    filter_upwards [hsurv k, hsurv l] with n hk hl s hs
    obtain ⟨a₁, hat₁, ha₁, f₁, hf₁, -, hc₁, hl₁, hp₁⟩ := hk.2.2.2.2.2
    obtain ⟨a₂, hat₂, ha₂, f₂, hf₂, -, hc₂, hl₂, hp₂⟩ := hl.2.2.2.2.2
    have hkl := min_le_left (k : ℝ) (l : ℝ)
    have hlk := min_le_right (k : ℝ) (l : ℝ)
    have hs1 := hs.1
    push_cast at hs1
    have hsk : s ∈ Icc (-(2 * ((k + 2 : ℕ) : ℝ))) 0 := ⟨by push_cast; linarith, hs.2⟩
    have hsl : s ∈ Icc (-(2 * ((l + 2 : ℕ) : ℝ))) 0 := ⟨by push_cast; linarith, hs.2⟩
    have hv₁ := ObservedHistory.mem_Icc_of_mem_window (hR n) ha₁ hsk
    have hv₂ := ObservedHistory.mem_Icc_of_mem_window (hR n) ha₂ hsl
    let v : Icc (0 : ℝ) (H n).horizon :=
      ⟨(t n : ℝ) + s / R n, a₁.2.1.trans hv₁.1, hv₁.2.trans (t n).2.2⟩
    have hja₁ : (H n).activeStage a₁ ≤ (H n).activeStage v :=
      (H n).activeStage_mono (show a₁ ≤ v from hv₁.1)
    have hja₂ : (H n).activeStage a₂ ≤ (H n).activeStage v :=
      (H n).activeStage_mono (show a₂ ≤ v from hv₂.1)
    have hjt : (H n).activeStage v ≤ (H n).activeStage (t n) :=
      (H n).activeStage_mono (show v ≤ t n from hv₁.2)
    have hdom := (H n).activeStage_mem v
    rw [hp₁ s hsk ⟨_, hja₁, hjt⟩ hdom, hp₂ s hsl ⟨_, hja₂, hjt⟩ hdom,
      ObservedHistory.scaleMetric_restrictOpenOfSubset,
      ObservedHistory.scaleMetric_restrictOpenOfSubset]
    congr 1
    exact localPullMetric_restrictOpenOfSubset_eq_of_comp_eq _ _ _ _ _ _ _
      (ObservedHistory.comp_inclusion_eq_of_backward_maps (H n) hat₁ hat₂ f₁ hc₁ hl₁ f₂ hc₂ hl₂ _
        hja₁ hja₂
        hjt)
  -- (1) 局部化：终端体积由基点种子 + traced region 给出（A13b 的 L3）
  have hvolX := FILL910.hvol_of_traced_seed H t y R hR (fun k => 2 * ((k + 2 : ℕ) : ℝ)) K
    (fun k => hKev k) hr₀ hw hseed
  have hlipW : ∀ k p : ℕ, ∃ L : ℝ, ∀ᶠ n in atTop, ∀ σ ∈ Icc (-((k + 1 : ℕ) : ℝ)) 0,
      ∀ σ' ∈ Icc (-((k + 1 : ℕ) : ℝ)) 0, ∀ z : W k n, (z : (X.obj n).M) ∈
          riemannianClosedBallOf (X.obj n).metric (X.obj n).basepoint ((k + 2 : ℕ) : ℝ) →
        ∀ a : ℕ, a ≤ p → metricDerivNorm a (h k n σ) (h k n σ') (h k n 0) z ≤ L * |σ - σ'| := by
    intro k p
    obtain ⟨L, -, hL⟩ := exists_metricDerivNorm_time_lipschitz_of_curvature_bound_on_open.{u}
      (I := ThreeModel) p (T := ((k + 1 : ℕ) : ℝ)) (T₂ := ((k + 2 : ℕ) : ℝ)) (r := 1 / 4)
      (K := K k) (by positivity) (by push_cast; linarith) (by norm_num)
    refine ⟨L, ?_⟩
    filter_upwards [hsurv k] with n hn σ hσ σ' hσ' z hz a ha
    let _ : SigmaCompactSpace (W k n) := isSigmaCompact_iff_sigmaCompactSpace.mp
      (Geometry.isSigmaCompact_of_isOpen ThreeModel (W k n).isOpen)
    have hopen : IsOpen (riemannianBallOf (X.obj n).metric (X.obj n).basepoint
        (((k + 2 : ℕ) : ℝ) + 1 / 2)) :=
      isOpen_lt (Geometry.Riemannian.continuous_riemannianEDist _ _) continuous_const
    let U : Opens (W k n) := ⟨Subtype.val ⁻¹' riemannianBallOf (X.obj n).metric
      (X.obj n).basepoint (((k + 2 : ℕ) : ℝ) + 1 / 2), hopen.preimage continuous_subtype_val⟩
    refine hL (h k n) (hn.2.1 _ (by positivity) le_rfl) hn.2.2.2.1 U ?_ σ hσ σ' hσ' z ?_ a ha
    · intro x hx
      rw [hn.2.2.1]
      apply ObservedHistory.isCompact_riemannianClosedBallOf_restrictOpen
      intro w hw
      rw [hWset k n hn]
      have hx' : riemannianEDistOf (X.obj n).metric (X.obj n).basepoint (x : (X.obj n).M) <
          ENNReal.ofReal (((k + 2 : ℕ) : ℝ) + 1 / 2) := hx
      have hw' : riemannianEDistOf (X.obj n).metric (x : (X.obj n).M) w ≤
          ENNReal.ofReal (1 / 4) := hw
      change riemannianEDistOf (X.obj n).metric (X.obj n).basepoint w <
        ENNReal.ofReal ((k + 3 : ℕ) : ℝ)
      calc riemannianEDistOf (X.obj n).metric (X.obj n).basepoint w
          ≤ riemannianEDistOf (X.obj n).metric (X.obj n).basepoint (x : (X.obj n).M) +
              riemannianEDistOf (X.obj n).metric (x : (X.obj n).M) w :=
            riemannianEDistOf_triangle _ _ _ _
        _ < ENNReal.ofReal (((k + 2 : ℕ) : ℝ) + 1 / 2) + ENNReal.ofReal (1 / 4) :=
            ENNReal.add_lt_add_of_lt_of_le (ne_top_of_le_ne_top ENNReal.ofReal_ne_top hw')
              hx' hw'
        _ = ENNReal.ofReal (((k + 2 : ℕ) : ℝ) + 1 / 2 + 1 / 4) :=
            (ENNReal.ofReal_add (by positivity) (by norm_num)).symm
        _ < ENNReal.ofReal ((k + 3 : ℕ) : ℝ) :=
            (ENNReal.ofReal_lt_ofReal_iff (by positivity)).mpr (by push_cast; linarith)
    · change riemannianEDistOf (X.obj n).metric (X.obj n).basepoint (z : (X.obj n).M) <
        ENNReal.ofReal (((k + 2 : ℕ) : ℝ) + 1 / 2)
      exact lt_of_le_of_lt hz ((ENNReal.ofReal_lt_ofReal_iff (by positivity)).mpr (by linarith))
  have hscalW : ∀ k : ℕ, ∃ B : ℝ, ∀ᶠ n in atTop, ∀ s ∈ Icc (-((k + 2 : ℕ) : ℝ)) 0,
      ∀ x : W k n, metricScalarAt (h k n s) x ≤ B := by
    intro k
    refine ⟨(Module.finrank ℝ ThreeSpace : ℝ) ^ 2 * |K k|, ?_⟩
    filter_upwards [hsurv k] with n hn s hs x
    exact metricScalarAt_le_of_curvDerivNormSq_zero_le_P6L (h k n s) x
      (hn.2.2.2.1 s ⟨by have := hs.1; push_cast at this ⊢; linarith, hs.2⟩ x)
  -- 局部化：pinching 只在 survivor maps 给出的 backward trace 点上用
  have hpinchW : ∀ k : ℕ, ∀ᶠ n in atTop, ∀ q ∈ Icc (-(2 * ((k + 2 : ℕ) : ℝ))) 0,
      ∀ x : W k n, curvatureOperatorLowerBoundAt (h k n q) x
        (metricAlgebraicCurvatureTensorAt (h k n q) x)
        (Perelman.rescalePinchingFunction (R n) Phi (metricScalarAt (h k n q) x)) := by
    intro k
    filter_upwards [hsurv k, hpinch ((k + 3 : ℕ) : ℝ) (2 * ((k + 2 : ℕ) : ℝ)) (by positivity)
      (hθ k)] with n hn hpn q hqθ x
    obtain ⟨a, hat, ha, fs, hfs, -, hcs, hls, hp⟩ := hn.2.2.2.2.2
    have hv := ObservedHistory.mem_Icc_of_mem_window (hR n) ha hqθ
    let v : Icc (0 : ℝ) (H n).horizon :=
      ⟨(t n : ℝ) + q / R n, a.2.1.trans hv.1, hv.2.trans (t n).2.2⟩
    have hav : a ≤ v := hv.1
    have hvt : v ≤ t n := hv.2
    let j : (H n).StageInterval ((H n).activeStage a) ((H n).activeStage (t n)) :=
      ⟨(H n).activeStage v, (H n).activeStage_mono hav, (H n).activeStage_mono hvt⟩
    have hq' := hp q hqθ j ((H n).activeStage_mem v)
    let tr0 : BackwardPointTrace (H n) ((H n).activeStage a) ((H n).activeStage (t n))
        ((H n).activeStage_mono hat) x.val :=
      { point := fun i hi hl => fs ⟨i, hi, hl⟩ x
        endpoint_eq := hls x
        crossing := fun i hi hl => hcs i hi hl x }
    let tr := tr0.restrictFirst ((H n).activeStage_mono hav) ((H n).activeStage_mono hvt)
    have hxW : (x : ((H n).stageAt (t n)).Carrier) ∈
        riemannianBallOf ((H n).stageMetric ((H n).activeStage (t n)) (t n)) (y n)
          (((k + 3 : ℕ) : ℝ) / Real.sqrt (R n)) := by
      rw [← hn.1]
      exact x.property
    have hav' : (t n : ℝ) - 2 * ((k + 2 : ℕ) : ℝ) / R n ≤ v := by rw [← ha]; exact hav
    have hpt := hpn x hxW v hvt hav' tr
    have htrpt : tr.point ((H n).activeStage v) le_rfl ((H n).activeStage_mono hvt) =
        fs j x := rfl
    rw [htrpt] at hpt
    have hpull := (curvatureOperatorLowerBoundAt_localPullMetric_iff _ (fs j) (hfs j) x _).mpr
      hpt
    rw [hq', curvatureOperatorLowerBoundAt_scaleMetric_iff, metricScalarAt_scaleMetric,
      metricScalarAt_localPull]
    unfold Perelman.rescalePinchingFunction
    simp only [mul_inv_cancel_left₀ (hR n).ne']
    exact hpull
  have hlowW : ∀ k : ℕ, ∀ᶠ n in atTop, ∀ s ∈ Icc (-((k + 1 : ℕ) : ℝ)) 0, ∀ (x : W k n)
      (u : TangentSpace ThreeModel x),
      (h k n 0).inner x u u ≤ Real.exp 2 * (h k n s).inner x u u := by
    intro k
    have hk1 : (0 : ℝ) < ((k + 1 : ℕ) : ℝ) := by positivity
    filter_upwards [hsurv k, Perelman.exists_forall_rescalePinchingFunction_le_of_tendsto hPhi
      hRlim ((Module.finrank ℝ ThreeSpace : ℝ) ^ 2 * |K k|) (1 / (2 * ((k + 1 : ℕ) : ℝ)))
      (by positivity), hpinchW k] with n hn hδ hpw s hs x u
    have hsk : -((k + 2 : ℕ) : ℝ) < s := by have := hs.1; push_cast at this ⊢; linarith
    let S : SolutionOn (I := ThreeModel) (M := W k n)
        (RealTimeInterval.closed (-((k + 2 : ℕ) : ℝ)) 0 (neg_nonpos.mpr (Nat.cast_nonneg _))) :=
      { base.metric := h k n }
    have hS : IsSolutionOn S :=
      hn.2.1 ((k + 2 : ℕ) : ℝ) (Nat.cast_nonneg _) (by push_cast; linarith)
    have hRic : ∀ q ∈ Ioo s 0, -(1 / ((k + 1 : ℕ) : ℝ)) * (S.base.metric q).inner x u u ≤
        S.ricciAt q x (vec2 u u) := by
      intro q hq
      have hqθ : q ∈ Icc (-(2 * ((k + 2 : ℕ) : ℝ))) 0 :=
        ⟨by have := hs.1; push_cast at this ⊢; linarith [hq.1], hq.2.le⟩
      have hscal := hpw q hqθ x
      have hric := neg_two_mul_inner_le_metricRicciAt_of_curvatureOperatorLowerBoundAt
        (h k n q) x hscal u
      have hle := hδ _ (metricScalarAt_le_of_curvDerivNormSq_zero_le_P6L (h k n q) x
        (hn.2.2.2.1 q hqθ x))
      have hn0 := metric_inner_self_nonneg (h k n q) x u
      have hδeq : 2 * (1 / (2 * ((k + 1 : ℕ) : ℝ))) = 1 / ((k + 1 : ℕ) : ℝ) := by
        field_simp
      change -(1 / ((k + 1 : ℕ) : ℝ)) * (h k n q).inner x u u ≤
        metricRicciAt (h k n q) x (vec2 u u)
      have hmono : -(1 / ((k + 1 : ℕ) : ℝ)) * (h k n q).inner x u u ≤
          -(2 * Perelman.rescalePinchingFunction (R n) Phi (metricScalarAt (h k n q) x)) *
            (h k n q).inner x u u := by
        rw [← hδeq]
        exact mul_le_mul_of_nonneg_right (by linarith) hn0
      exact hmono.trans hric
    have hB2 := metric_inner_le_exp_mul_of_ricci_lower_bound S hS hs.2
      (fun r hr => ⟨by linarith [hr.1], hr.2⟩) (fun r hr => ⟨by linarith [hr.1], hr.2⟩) x u hRic
    refine hB2.trans (mul_le_mul_of_nonneg_right (Real.exp_le_exp.mpr ?_)
      (metric_inner_self_nonneg _ _ _))
    have hs1 : -s ≤ ((k + 1 : ℕ) : ℝ) := by linarith [hs.1]
    rw [show 2 * (1 / ((k + 1 : ℕ) : ℝ)) * (0 - s) = 2 * (-s / ((k + 1 : ℕ) : ℝ)) by ring]
    have : -s / ((k + 1 : ℕ) : ℝ) ≤ 1 := (div_le_one hk1).mpr hs1
    linarith
  -- 局部化：输出 `hnc`（及 `κ/250` 用的 `hncW`）由 trace-local κ 给出（P6B M8 单步）
  have hncW : ∀ k : ℕ, ∀ᶠ n in atTop, ∀ σ ∈ Icc (-((k + 1 : ℕ) : ℝ)) 0, ∀ z : W k n,
      ∀ r : ℝ, 0 < r → r ≤ ρnc n * Real.sqrt (R n) →
      Icc (σ - r ^ 2) σ ⊆ Icc (-((k + 2 : ℕ) : ℝ)) 0 →
      IsCompact (riemannianClosedBallOf (h k n σ) z r) →
      (∀ s ∈ Icc (σ - r ^ 2) σ, ∀ w ∈ riemannianBallOf (h k n σ) z r,
        r ^ 4 * curvDerivNormSq 0 (h k n s) w ≤ 1) →
      ENNReal.ofReal (κ * r ^ 3) ≤
        Integral.Measure.riemannianVolumeMeasure ThreeModel (W k n) (h k n σ)
          (riemannianBallOf (h k n σ) z r) := by
    intro k
    filter_upwards [hsurv k, hkappa ((k + 3 : ℕ) : ℝ) (2 * ((k + 2 : ℕ) : ℝ)) (by positivity)
      (hθ k)] with n hn hkn
    intro σ hσ z r hr hrρ hsub hcpt hcurv
    have hlow := (hsub ⟨le_rfl, by nlinarith⟩).1
    obtain ⟨a, hat, ha, f, hf, hinj, hc, hlast, hp⟩ := hn.2.2.2.2.2
    refine ObservedHistory.volume_ball_ge_of_survivor_maps_of_traced_kappa_P6B (H n) (t n) (hR n)
      a hat ha f hf hinj hc hlast hp hκ.le ?_ hr hrρ ?_ hσ.2 z hcpt hcurv
    · intro x v hvt hav tr r'' hr'' hρ hpc
      have hxW : (x : ((H n).stageAt (t n)).Carrier) ∈
          riemannianBallOf ((H n).stageMetric ((H n).activeStage (t n)) (t n)) (y n)
            (((k + 3 : ℕ) : ℝ) / Real.sqrt (R n)) := by
        rw [← hn.1]
        exact x.property
      have hav' : (t n : ℝ) - 2 * ((k + 2 : ℕ) : ℝ) / R n ≤ v := by rw [← ha]; exact hav
      exact hkn x hxW v hvt hav' tr r'' hr'' hρ hpc
    · push_cast at hlow ⊢
      linarith
  obtain ⟨f, hf, P, F, hCd, hPc, hconn, hballF, V, N, hV, hVF, φ, hφ, hφF, G, hG0, hG, ψ, hψ,
    hconv⟩ := exists_ancient_pointed_flow_limit_of_local_solutions X hcompact hvolX W h hball
      hsol hzero hjets hcompat
  refine ⟨W, h, fun k => ?_, hlipW, hscalW, hlowW, f, hf, P, F, hCd, hPc, hconn, hballF, V, N,
    hV, hVF, φ, hφ, hφF, G, hG0, hG, ψ, hψ, hconv, fun ρ' hρ' => ?_⟩
  swap
  · -- `κ/250`：照 P6B M8（`radii = ρnc n √R n`）
    have hmono : Monotone V := by
      intro k l hkl z hz
      change z ∈ (V l : Set P.M)
      have hz' : z ∈ (V k : Set P.M) := hz
      rw [hV] at hz' ⊢
      refine riemannianBallOf_mono _ _ ?_ hz'
      have : ((k + 1 : ℕ) : ℝ) ≤ ((l + 1 : ℕ) : ℝ) := by
        exact_mod_cast Nat.add_le_add_right hkl 1
      linarith
    have hcover : ∀ x : P.M, ∃ k, x ∈ V k := by
      intro x
      have hne := riemannianEDistOf_ne_top P.metric P.basepoint x
      obtain ⟨k, hk⟩ := exists_nat_gt (2 * (riemannianEDistOf P.metric P.basepoint x).toReal)
      refine ⟨k, ?_⟩
      change x ∈ (V k : Set P.M)
      rw [hV]
      refine (ENNReal.lt_ofReal_iff_toReal_lt hne).mpr ?_
      push_cast
      linarith
    have hcomplete := (ancient_pointed_flow_limit_curvatureOperator_nonnegative_and_complete hf
      hPc hconn hV hG0 hG hψ hconv hRlim hPhi (fun k => (hpinchW k).mono fun n hn q hq x => hn q
        ⟨by have := hq.1; push_cast at this ⊢; linarith, hq.2⟩ x)).2
    refine Perelman.parabolicallyKappaNoncollapsedBelowScale_of_forall_time_lt hG ?_ hρ'
      (fun _ hs => hs)
      fun time B htime _ hB => isKappaNoncollapsed_of_local_flow_limit_of_time_lt hsol hκ hradii
        (fun k σ hσ _ => (hncW k).mono fun _ hn => hn σ hσ) hf F hmono hcover hVF φ hφ hφF hG
        hcomplete hψ hconv B hB htime
    change interior (Iic (0 : ℝ)) ⊆ Iio 0
    rw [interior_Iic]
  filter_upwards [hsurv k, hncW k] with n hn hnc
  refine ⟨hWset k n hn, hn.2.1 ((k + 2 : ℕ) : ℝ) (Nat.cast_nonneg _) (by push_cast; linarith),
    fun s hs hdom => hn.2.2.2.2.1 s ⟨?_, hs.2⟩ hdom, hn.2.2.2.2.2, hnc⟩
  have := hs.1
  push_cast at this ⊢
  linarith

end ObservedHistory

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
