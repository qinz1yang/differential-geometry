import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.P6LimitKappaP6B
import DifferentialGeometry.Geometry.Flow.RicciFlow.Compactness.Limits.A13bSeedVolume

/-!
# P6 / L8c：只用局部 κ 的古代 pointed 极限（带 survivor maps）（O-CH11-P6B G2，后缀 `_P6B`）

树内 `exists_ancient_pointed_flow_limit_with_survivor_maps_of_isTracedRegion`
（`ST/TracedRegionAncientLimitData.lean:321`）要**全局** noncollapse `hnc`（任意点、任意 `v ≤ t n`）。
它只在两处用到 `hnc`：(1) 终端时刻的 `hvolX`；(2) 输出的局部流 `hnc` 合取。这里把两处都局部化：

* (1) 换成**基点处一个种子体积** `vol B(y n, r₀/√R n) ≥ w (r₀/√R n)³`，经树内
  `FILL910.hvol_of_traced_seed`（A13b 的 L3，Bishop–Gromov + traced region 曲率界）给出 `hvolX`；
* (2) 换成 **trace-local κ**：只要求 `B_{t n}(y n, D/√R n)` 中点的 backward trace（深度 `T/R n`）上
  scale `≤ ρnc n` 的 controlled 球有 `κ r³ ≤ vol`，经 M8 单步
  `volume_ball_ge_of_survivor_maps_of_traced_kappa_P6B` 给出输出 `hnc`（`radii = ρnc n √R n`）。

结论与树内定理逐字相同（`ρ * √R n` 换成 `ρnc n * √R n`）：局部流 `W, h`、survivor maps、局部 `hnc`、
完备连通 pointed 极限 `P`、古代流 `G`（`(−∞, 0]`）与光滑局部收敛。证明照抄树内证明，只改 (1)(2)。
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

universe u

attribute [local instance] PointedRiemannianManifold.topology PointedRiemannianManifold.charted
  PointedRiemannianManifold.smooth PointedRiemannianManifold.t2
  PointedRiemannianManifold.sigmaCompact

private local instance {M : Type u} [TopologicalSpace M] [ChartedSpace ThreeSpace M]
    [SigmaCompactSpace M] (U : Opens M) : SigmaCompactSpace U :=
  isSigmaCompact_iff_sigmaCompactSpace.mp
    (Geometry.isSigmaCompact_of_isOpen ThreeModel U.isOpen)

/-- **L8c**：traced regions（所有 `A, T`）+ 基点种子体积 + trace-local κ ⇒ 带 survivor maps 与局部
`hnc` 的古代 pointed 极限（树内 `:321` 的局部版，无全局 noncollapse）。 -/
theorem exists_ancient_pointed_flow_limit_with_survivor_maps_of_traced_seed_P6B
    (H : ℕ → ObservedHistory.{u}) (t : ∀ n, Icc (0 : ℝ) (H n).horizon)
    (y : ∀ n, ((H n).stageAt (t n)).Carrier) (R : ℕ → ℝ) (hR : ∀ n, 0 < R n)
    (htraced : ∀ A T : ℝ, 0 < A → 0 < T → ∃ K : ℝ, 0 ≤ K ∧ ∀ᶠ n in atTop,
      (H n).isTracedRegion (t n) (y n) (A / Real.sqrt (R n)) (T / R n) (K * R n))
    {r₀ w : ℝ} (hr₀ : 0 < r₀) (hw : 0 < w)
    (hseed : ∀ᶠ n in atTop,
      ENNReal.ofReal (w * (r₀ / Real.sqrt (R n)) ^ 3) ≤
        Integral.Measure.riemannianVolumeMeasure ThreeModel ((H n).stageAt (t n)).Carrier
          ((H n).stageMetric ((H n).activeStage (t n)) (t n))
          (riemannianBallOf ((H n).stageMetric ((H n).activeStage (t n)) (t n)) (y n)
            (r₀ / Real.sqrt (R n))))
    {κ : ℝ} (hκ : 0 ≤ κ) (ρnc : ℕ → ℝ)
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
            (tr.point ((H n).activeStage v) le_rfl ((H n).activeStage_mono hvt)) r'') :
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
                  ∀ k (K : Set (V k)), IsCompact K → ∀ p : ℕ, ∀ η : ℝ, 0 < η →
                    ∃ j₀ : ℕ, ∀ i ≥ j₀, ∃ hi : N k ≤ ψ i,
                      ∀ t ∈ Icc (-((k + 1 : ℕ) : ℝ)) 0,
                        metricDerivNormSupOn K p
                          (localPullMetric (h k (f (ψ i)) t) (φ k (ψ i) hi) (hφ k (ψ i) hi))
                          ((G t).restrictOpen (V k)) (P.metric.restrictOpen (V k)) < η := by
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
  refine ⟨W, h, fun k => ?_, exists_ancient_pointed_flow_limit_of_local_solutions X hcompact
    hvolX W h hball hsol hzero hjets hcompat⟩
  filter_upwards [hsurv k, hkappa ((k + 3 : ℕ) : ℝ) (2 * ((k + 2 : ℕ) : ℝ)) (by positivity)
    (hθ k)] with n hn hkn
  refine ⟨hWset k n hn, hn.2.1 ((k + 2 : ℕ) : ℝ) (Nat.cast_nonneg _) (by push_cast; linarith),
    fun s hs hdom => hn.2.2.2.2.1 s ⟨?_, hs.2⟩ hdom, hn.2.2.2.2.2, ?_⟩
  · have := hs.1
    push_cast at this ⊢
    linarith
  -- (2) 局部化：输出 `hnc` 由 trace-local κ 给出（M8 单步）
  intro σ hσ z r hr hrρ hsub hcpt hcurv
  have hlow := (hsub ⟨le_rfl, by nlinarith⟩).1
  obtain ⟨a, hat, ha, f, hf, hinj, hc, hlast, hp⟩ := hn.2.2.2.2.2
  refine ObservedHistory.volume_ball_ge_of_survivor_maps_of_traced_kappa_P6B (H n) (t n) (hR n)
    a hat ha f hf hinj hc hlast hp hκ ?_ hr hrρ ?_ hσ.2 z hcpt hcurv
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

end ObservedHistory

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
