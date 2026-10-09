import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.Local.CrossingWindowAnchorBoundBlock_P6L2
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.Local.TracedRegionLocalLimitDepthSchedule_P6L

/-!
# window anchor（`:555_P6L`）的 **条件形**（O-CH11-P6ANCH2 G2，后缀 `_P6L2`）

`exists_subseq_windowAnchorBound_of_depthExtendable_P6L` 的逐字副本，唯一改动：trace-local `hwit` /
`hderiv` 换成**条件形** `hwitC` / `hderivC`——沿任一子列 `φ`，只要 `(2D, T, K)` 的 traced region
eventually 成立，就给 `(D, T)` 的 witness / 导数界（深度自举，设计段 1a / B2）。证明里它们只在 block
`(k + 3, τ k)`、`τ k = Tstar·(k+1)/(k+2) < Tstar` 上取值，traced region 由 `hext`（深度 `< Tstar` 全部
depth-extendable，沿 `σ`）在半径 `2(k + 3)` 给出；下层用 block 形 `_P6L2`
（`CrossingWindowAnchorBoundBlock_P6L2`）。D-9.5 不变：没有任何一步在深度 `≥ Tstar` 取 witness。
-/

set_option autoImplicit false

noncomputable section

open Set Filter
open DifferentialGeometry.Geometry.Curvature DifferentialGeometry.Geometry.Metric
open DifferentialGeometry.CheegerGromovCompactness
open scoped Manifold NNReal Topology ContDiff

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

universe u

private theorem depth_schedule_facts_P6L2 {T : ℝ} (hT : 0 < T) :
    (∀ k : ℕ, 0 < T * ((k + 1 : ℕ) : ℝ) / ((k + 2 : ℕ) : ℝ)) ∧
    (∀ k : ℕ, T * ((k + 1 : ℕ) : ℝ) / ((k + 2 : ℕ) : ℝ) < T) ∧
    (∀ k : ℕ, 0 < ((k + 1 : ℕ) : ℝ) / ((k + 2 : ℕ) : ℝ) *
      (T * ((k + 1 : ℕ) : ℝ) / ((k + 2 : ℕ) : ℝ))) ∧
    (∀ k : ℕ, ((k + 1 : ℕ) : ℝ) / ((k + 2 : ℕ) : ℝ) *
      (T * ((k + 1 : ℕ) : ℝ) / ((k + 2 : ℕ) : ℝ)) < T * ((k + 1 : ℕ) : ℝ) / ((k + 2 : ℕ) : ℝ)) ∧
    Monotone (fun k : ℕ => ((k + 1 : ℕ) : ℝ) / ((k + 2 : ℕ) : ℝ) *
      (T * ((k + 1 : ℕ) : ℝ) / ((k + 2 : ℕ) : ℝ))) ∧
    (∀ s < T, ∃ k : ℕ, s < ((k + 1 : ℕ) : ℝ) / ((k + 2 : ℕ) : ℝ) *
      (T * ((k + 1 : ℕ) : ℝ) / ((k + 2 : ℕ) : ℝ))) := by
  have hβ (n : ℕ) : ((n + 1 : ℕ) : ℝ) / ((n + 2 : ℕ) : ℝ) = 1 - 1 / ((n + 2 : ℕ) : ℝ) := by
    have : (0 : ℝ) < ((n + 2 : ℕ) : ℝ) := by positivity
    field_simp
    push_cast
    ring
  have hβ1 (n : ℕ) : ((n + 1 : ℕ) : ℝ) / ((n + 2 : ℕ) : ℝ) < 1 := by
    rw [div_lt_one (by positivity)]
    push_cast
    linarith
  have hβ0 (n : ℕ) : 0 < ((n + 1 : ℕ) : ℝ) / ((n + 2 : ℕ) : ℝ) := by positivity
  have hτ (n : ℕ) : 0 < T * ((n + 1 : ℕ) : ℝ) / ((n + 2 : ℕ) : ℝ) := by positivity
  have hτT (n : ℕ) : T * ((n + 1 : ℕ) : ℝ) / ((n + 2 : ℕ) : ℝ) < T := by
    rw [mul_div_assoc]
    nlinarith [hβ1 n]
  refine ⟨hτ, hτT, fun n => mul_pos (hβ0 n) (hτ n), fun n => ?_, fun n m hnm => ?_,
    fun s hs => ?_⟩
  · nlinarith [hβ1 n, hτ n]
  · have h1 : 1 / ((m + 2 : ℕ) : ℝ) ≤ 1 / ((n + 2 : ℕ) : ℝ) :=
      one_div_le_one_div_of_le (by positivity) (by exact_mod_cast Nat.add_le_add_right hnm 2)
    have h3 : 0 ≤ 1 - 1 / ((n + 2 : ℕ) : ℝ) := by
      rw [← hβ]
      positivity
    have h4 : 1 - 1 / ((n + 2 : ℕ) : ℝ) ≤ 1 - 1 / ((m + 2 : ℕ) : ℝ) := by linarith
    change ((n + 1 : ℕ) : ℝ) / ((n + 2 : ℕ) : ℝ) * (T * ((n + 1 : ℕ) : ℝ) / ((n + 2 : ℕ) : ℝ)) ≤
      ((m + 1 : ℕ) : ℝ) / ((m + 2 : ℕ) : ℝ) * (T * ((m + 1 : ℕ) : ℝ) / ((m + 2 : ℕ) : ℝ))
    rw [mul_div_assoc, mul_div_assoc, hβ, hβ]
    exact mul_le_mul h4 (mul_le_mul_of_nonneg_left h4 hT.le) (mul_nonneg hT.le h3) (h3.trans h4)
  · by_cases hs0 : s < 0
    · exact ⟨0, hs0.trans (mul_pos (hβ0 0) (hτ 0))⟩
    push Not at hs0
    obtain ⟨n, hn⟩ := exists_nat_gt (2 * T / (T - s))
    refine ⟨n, ?_⟩
    have hTs : 0 < T - s := by linarith
    have hn2 : 2 * T / (T - s) < ((n + 2 : ℕ) : ℝ) := by push_cast; linarith
    have hx : 2 * T * (1 / ((n + 2 : ℕ) : ℝ)) < T - s := by
      rw [div_lt_iff₀ hTs] at hn2
      rw [mul_one_div, div_lt_iff₀ (by positivity)]
      linarith
    have hx0 : 0 ≤ 1 / ((n + 2 : ℕ) : ℝ) := by positivity
    rw [mul_div_assoc, hβ]
    nlinarith [mul_nonneg hT.le (sq_nonneg (1 / ((n + 2 : ℕ) : ℝ)))]

open Perelman.CanonicalNeighborhood.FiniteHorn

private local instance opensSigmaCompactAnchor_P6L2 {Y : Type*} [TopologicalSpace Y]
    [ChartedSpace ThreeSpace Y] [SigmaCompactSpace Y] (U : TopologicalSpace.Opens Y) :
    SigmaCompactSpace U :=
  isSigmaCompact_iff_sigmaCompactSpace.mp (Geometry.isSigmaCompact_of_isOpen ThreeModel U.isOpen)

namespace ObservedHistory

attribute [local instance] CheegerGromovCompactness.PointedRiemannianManifold.topology
  CheegerGromovCompactness.PointedRiemannianManifold.charted
  CheegerGromovCompactness.PointedRiemannianManifold.smooth
  CheegerGromovCompactness.PointedRiemannianManifold.t2
  CheegerGromovCompactness.PointedRiemannianManifold.sigmaCompact

/-- **window anchor（局部化，`:555_P6L`）**：深度 `< Tstar` 全部 depth-extendable（沿 `σ`）+ 基点种子
体积 + trace-local κ / pinching / witness / 时间导数 / BCAD ⇒ 子列 `ψ` 与常数 `M`，使对每个
`T' < Tstar`、`A`，eventually 从 `B(ys, A/√R)` 出发、到时刻 `ts − T'/R` 的所有 backward trace 上
`R ≤ M · R`（`CrossingDepthExtension:16` 的 anchor 形）。 -/
theorem exists_subseq_windowAnchorBound_of_depthExtendable_P6L2
    (Hs : ℕ → ObservedHistory.{u}) (ts : ∀ n, Icc (0 : ℝ) (Hs n).horizon)
    (ys : ∀ n, ((Hs n).stageAt (ts n)).Carrier) (R : ℕ → ℝ) (hR : ∀ n, 0 < R n)
    (hRlim : Tendsto R atTop atTop) {σ : ℕ → ℕ} (hσ : StrictMono σ) {Tstar : ℝ}
    (hT : 0 < Tstar)
    (hext : ∀ T : ℝ, 0 < T → T < Tstar → DepthExtendable Hs ts ys R σ T)
    {r₀ w : ℝ} (hr₀ : 0 < r₀) (hw : 0 < w)
    (hseed : ∀ᶠ n in atTop,
        ENNReal.ofReal (w * (r₀ / Real.sqrt (R n)) ^ 3) ≤
          Integral.Measure.riemannianVolumeMeasure ThreeModel ((Hs n).stageAt (ts n)).Carrier
            ((Hs n).stageMetric ((Hs n).activeStage (ts n)) (ts n))
            (riemannianBallOf ((Hs n).stageMetric ((Hs n).activeStage (ts n)) (ts n)) (ys n)
              (r₀ / Real.sqrt (R n))))
    {κ : ℝ} (hκ : 0 < κ) (ρnc : ℕ → ℝ)
    (hradii : Tendsto (fun n => ρnc n * Real.sqrt (R n)) atTop atTop)
    (hkappa : ∀ D T : ℝ, 0 < D → 0 < T → ∀ᶠ n in atTop,
        ∀ x ∈ riemannianBallOf ((Hs n).stageMetric ((Hs n).activeStage (ts n)) (ts n)) (ys n)
            (D / Real.sqrt (R n)),
        ∀ (v : Icc (0 : ℝ) (Hs n).horizon) (hvt : v ≤ ts n), (ts n : ℝ) - T / R n ≤ v →
        ∀ tr : BackwardPointTrace (Hs n) ((Hs n).activeStage v) ((Hs n).activeStage (ts n))
          ((Hs n).activeStage_mono hvt) x,
        ∀ r'' : ℝ, 0 < r'' → r'' ≤ ρnc n →
          (Hs n).isParabolicallyRmControlledBall v
            (tr.point ((Hs n).activeStage v) le_rfl ((Hs n).activeStage_mono hvt)) r'' →
          ENNReal.ofReal (κ * r'' ^ 3) ≤
            Geometry.Collapse.ballVolume ((Hs n).stageMetric ((Hs n).activeStage v) v)
              (tr.point ((Hs n).activeStage v) le_rfl ((Hs n).activeStage_mono hvt)) r'')
    {Phi : ℝ → ℝ} (hPhi : Perelman.AdmissiblePinchingFunction Phi)
    (hpinch : ∀ D T : ℝ, 0 < D → 0 < T → ∀ᶠ n in atTop,
        ∀ x ∈ riemannianBallOf ((Hs n).stageMetric ((Hs n).activeStage (ts n)) (ts n)) (ys n)
            (D / Real.sqrt (R n)),
        ∀ (v : Icc (0 : ℝ) (Hs n).horizon) (hvt : v ≤ ts n), (ts n : ℝ) - T / R n ≤ v →
        ∀ tr : BackwardPointTrace (Hs n) ((Hs n).activeStage v) ((Hs n).activeStage (ts n))
          ((Hs n).activeStage_mono hvt) x,
          curvatureOperatorLowerBoundAt ((Hs n).stageMetric ((Hs n).activeStage v) v)
            (tr.point ((Hs n).activeStage v) le_rfl ((Hs n).activeStage_mono hvt))
            (metricAlgebraicCurvatureTensorAt ((Hs n).stageMetric ((Hs n).activeStage v) v)
              (tr.point ((Hs n).activeStage v) le_rfl ((Hs n).activeStage_mono hvt)))
            (Phi (metricScalarAt ((Hs n).stageMetric ((Hs n).activeStage v) v)
              (tr.point ((Hs n).activeStage v) le_rfl ((Hs n).activeStage_mono hvt)))))
    {ε : ℝ} (hε : 0 < ε) (hεX : ε ≤ crossingWindowNeckAccuracy.{u}) {C1s C2s Cs : ℝ}
    {qs : ℕ → ℝ} (hqs : ∀ n, qs n ≤ Cs * R n)
    (hwitC : ∀ φ : ℕ → ℕ, StrictMono φ → ∀ D T K : ℝ, 0 < D → 0 < T → 0 ≤ K →
        (∀ᶠ n in map φ atTop, (Hs n).isTracedRegion (ts n) (ys n) (2 * D / Real.sqrt (R n))
          (T / R n) (K * R n)) → ∀ᶠ n in map φ atTop,
        ∀ x ∈ riemannianBallOf ((Hs n).stageMetric ((Hs n).activeStage (ts n)) (ts n)) (ys n)
            (D / Real.sqrt (R n)),
        ∀ (v : Icc (0 : ℝ) (Hs n).horizon) (hvt : v ≤ ts n), (ts n : ℝ) - T / R n ≤ v →
        (v : ℝ) < ts n → (Hs n).time ((Hs n).activeStage v) < v →
        ∀ tr : BackwardPointTrace (Hs n) ((Hs n).activeStage v) ((Hs n).activeStage (ts n))
          ((Hs n).activeStage_mono hvt) x,
          qs n < metricScalarAt ((Hs n).stageMetric ((Hs n).activeStage v) v)
            (tr.point ((Hs n).activeStage v) le_rfl ((Hs n).activeStage_mono hvt)) →
          ∃ Wt : SpatialCanonicalWitness ((Hs n).stageMetric ((Hs n).activeStage v) v) ε C1s C2s
              (tr.point ((Hs n).activeStage v) le_rfl ((Hs n).activeStage_mono hvt)),
            Wt.capTubeHasNeckChart ε)
    {Ctime : ℝ≥0} {Cq : ℝ} {qcan : ℕ → ℝ} (hqcan : ∀ n, qcan n ≤ Cq * R n)
    (hderivC : ∀ φ : ℕ → ℕ, StrictMono φ → ∀ D T K : ℝ, 0 < D → 0 < T → 0 ≤ K →
        (∀ᶠ n in map φ atTop, (Hs n).isTracedRegion (ts n) (ys n) (2 * D / Real.sqrt (R n))
          (T / R n) (K * R n)) → ∀ᶠ n in map φ atTop,
        ∀ x ∈ riemannianBallOf ((Hs n).stageMetric ((Hs n).activeStage (ts n)) (ts n)) (ys n)
            (D / Real.sqrt (R n)),
        ∀ (v : Icc (0 : ℝ) (Hs n).horizon) (hvt : v ≤ ts n), (ts n : ℝ) - T / R n ≤ v →
        (v : ℝ) < ts n → (Hs n).time ((Hs n).activeStage v) < v →
        ∀ tr : BackwardPointTrace (Hs n) ((Hs n).activeStage v) ((Hs n).activeStage (ts n))
          ((Hs n).activeStage_mono hvt) x,
          qcan n < metricScalarAt ((Hs n).stageMetric ((Hs n).activeStage v) v)
            (tr.point ((Hs n).activeStage v) le_rfl ((Hs n).activeStage_mono hvt)) →
          |derivWithin (fun v' => metricScalarAt ((Hs n).stageMetric ((Hs n).activeStage v) v')
              (tr.point ((Hs n).activeStage v) le_rfl ((Hs n).activeStage_mono hvt)))
            (Iic (v : ℝ)) v| ≤
            Ctime * metricScalarAt ((Hs n).stageMetric ((Hs n).activeStage v) v)
              (tr.point ((Hs n).activeStage v) le_rfl ((Hs n).activeStage_mono hvt)) ^ 2)
    (hbcad : ∀ A Dd : ℝ, 0 < A → 0 < Dd → ∃ C : ℝ, ∀ σ' : ℝ, σ' < 0 → ∀ Dw : ℝ, 0 < Dw →
        ∀ᶠ n in atTop,
        ∀ x₁ ∈ riemannianBallOf ((Hs n).stageMetric ((Hs n).activeStage (ts n)) (ts n)) (ys n)
            (Dw / Real.sqrt (R n)),
        ∀ x₂ ∈ riemannianBallOf ((Hs n).stageMetric ((Hs n).activeStage (ts n)) (ts n)) (ys n)
            (Dw / Real.sqrt (R n)),
        ∀ (v : Icc (0 : ℝ) (Hs n).horizon) (hvt : v ≤ ts n), (v : ℝ) = ts n + σ' / R n →
        ∀ (tr₁ : BackwardPointTrace (Hs n) ((Hs n).activeStage v) ((Hs n).activeStage (ts n))
            ((Hs n).activeStage_mono hvt) x₁)
          (tr₂ : BackwardPointTrace (Hs n) ((Hs n).activeStage v) ((Hs n).activeStage (ts n))
            ((Hs n).activeStage_mono hvt) x₂),
          metricScalarAt ((Hs n).stageMetric ((Hs n).activeStage v) v)
              (tr₁.point ((Hs n).activeStage v) le_rfl ((Hs n).activeStage_mono hvt)) ≤ A * R n →
          riemannianEDistOf ((Hs n).stageMetric ((Hs n).activeStage v) v)
              (tr₁.point ((Hs n).activeStage v) le_rfl ((Hs n).activeStage_mono hvt))
              (tr₂.point ((Hs n).activeStage v) le_rfl ((Hs n).activeStage_mono hvt)) <
            ENNReal.ofReal (Dd / Real.sqrt (R n)) →
          metricScalarAt ((Hs n).stageMetric ((Hs n).activeStage v) v)
              (tr₂.point ((Hs n).activeStage v) le_rfl ((Hs n).activeStage_mono hvt)) ≤ C * R n) :
    ∃ ψ : ℕ → ℕ, StrictMono ψ ∧ ∃ M : ℝ, 0 ≤ M ∧
      ∀ T' : ℝ, 0 < T' → T' < Tstar → ∀ A : ℝ, 0 < A → ∀ᶠ i in atTop,
      ∀ x ∈ riemannianBallOf ((Hs (σ (ψ i))).stageMetric
          ((Hs (σ (ψ i))).activeStage (ts (σ (ψ i)))) (ts (σ (ψ i)))) (ys (σ (ψ i)))
          (A / Real.sqrt (R (σ (ψ i)))),
      ∀ (w : Icc (0 : ℝ) (Hs (σ (ψ i))).horizon),
        (w : ℝ) = ts (σ (ψ i)) - T' / R (σ (ψ i)) →
      ∀ (hwt : w ≤ ts (σ (ψ i)))
        (Bt : BackwardPointTrace (Hs (σ (ψ i))) ((Hs (σ (ψ i))).activeStage w)
          ((Hs (σ (ψ i))).activeStage (ts (σ (ψ i))))
          ((Hs (σ (ψ i))).activeStage_mono hwt) x),
        metricScalarAt ((Hs (σ (ψ i))).stageMetric ((Hs (σ (ψ i))).activeStage w) w)
          (Bt.point ((Hs (σ (ψ i))).activeStage w) le_rfl
            ((Hs (σ (ψ i))).activeStage_mono hwt)) ≤
          M * R (σ (ψ i)) := by
  have hRσ : Tendsto (fun m => R (σ m)) atTop atTop := hRlim.comp hσ.tendsto_atTop
  have hRpos : ∀ m, 0 < R (σ m) := fun m => hR (σ m)
  obtain ⟨hτs0, hτsT, hc0, hcτ, hcmono, hcex⟩ := depth_schedule_facts_P6L2 hT
  have hcT' : ∀ k : ℕ, ((k + 1 : ℕ) : ℝ) / ((k + 2 : ℕ) : ℝ) *
      (Tstar * ((k + 1 : ℕ) : ℝ) / ((k + 2 : ℕ) : ℝ)) < Tstar := fun k => (hcτ k).trans (hτsT k)
  have hcT : ∀ s ∈ Ioc (-Tstar) 0, ∃ k : ℕ, -(((k + 1 : ℕ) : ℝ) / ((k + 2 : ℕ) : ℝ) *
      (Tstar * ((k + 1 : ℕ) : ℝ) / ((k + 2 : ℕ) : ℝ))) < s := fun s hs =>
    (hcex (-s) (by linarith [hs.1])).imp fun _ hk => by linarith
  obtain ⟨W, h, hblock, hlip, -, hlow, hpinchW, hncW, f, hf, P, F, ⟨Cd, hcan⟩, hPc, hconn,
      hballF, V, N, hV, hVF, φ, hφ, hφF, Gloc, hG0, hGsol, hGcompat, ψ₁, hψ₁, hconv⟩ :=
    exists_local_pointed_flow_limits_of_depth_schedule_P6L
      (fun m => Hs (σ m)) (fun m => ts (σ m)) (fun m => ys (σ m)) (fun m => R (σ m)) hRpos hRσ
      (fun k => Tstar * ((k + 1 : ℕ) : ℝ) / ((k + 2 : ℕ) : ℝ)) hτs0
      (fun k => hext _ (hτs0 k) (hτsT k) _ (by positivity))
      hr₀ hw (hσ.tendsto_atTop.eventually hseed) hκ (fun m => ρnc (σ m))
      (fun D T hD hT => hσ.tendsto_atTop.eventually (hkappa D T hD hT)) hPhi
      (fun D T hD hT => hσ.tendsto_atTop.eventually (hpinch D T hD hT))
  let _ : ConnectedSpace P.M := hconn
  obtain ⟨hVmono, hVcover⟩ := monotone_and_cover_of_riemannianBallOf_eq hconn hV
  obtain ⟨Gl, hGlsol, hGlres⟩ :=
    exists_openClosed_solution_of_compatible_open_cover_of_depth_schedule hT V hVmono hVcover
      Gloc hGsol hGcompat
  have hGl0 : Gl 0 = P.metric := by
    apply SmoothRiemannianMetric.ext_inner
    intro x v w
    obtain ⟨k, hk⟩ := hVcover x
    have heq := (hGlres k 0 ⟨by linarith [hc0 k], le_rfl⟩).trans (hG0 k)
    exact congrArg (fun q : SmoothRiemannianMetric ThreeModel (V k) => q.inner ⟨x, hk⟩ v w) heq
  have hconvG : ∀ k (K' : Set (V k)), IsCompact K' → ∀ p : ℕ, ∀ η : ℝ, 0 < η →
      ∃ j₀ : ℕ, ∀ i ≥ j₀, ∃ hi : N k ≤ ψ₁ i,
        ∀ s ∈ Icc (-(((k + 1 : ℕ) : ℝ) / ((k + 2 : ℕ) : ℝ) *
          (Tstar * ((k + 1 : ℕ) : ℝ) / ((k + 2 : ℕ) : ℝ)))) 0,
        metricDerivNormSupOn K' p
          (localPullMetric (h k (f (ψ₁ i)) s) (φ k (ψ₁ i) hi) (hφ k (ψ₁ i) hi))
          ((Gl s).restrictOpen (V k)) (P.metric.restrictOpen (V k)) < η := by
    intro k K' hK' p η hη
    obtain ⟨j₀, hj₀⟩ := hconv k K' hK' p η hη
    refine ⟨j₀, fun i hi => ?_⟩
    obtain ⟨hi', hb⟩ := hj₀ i hi
    refine ⟨hi', fun s hs => ?_⟩
    rw [hGlres k s hs]
    exact hb s hs
  have hsol : ∀ k : ℕ, ∀ᶠ n in atTop, IsSolutionOn ({ base.metric := h k n } :
      SolutionOn (I := ThreeModel) (M := W k n)
        (RealTimeInterval.closed (-(Tstar * ((k + 1 : ℕ) : ℝ) / ((k + 2 : ℕ) : ℝ))) 0
          (neg_nonpos.mpr (hτs0 k).le))) := fun k => (hblock k).mono fun _ hn => hn.2.1
  -- 局部化：`t₀ := t n`，例外时刻集 = `{0}` ∪ event 时刻（`ζ = 0`）
  let E' : ℕ → Set ℝ := fun m => Iic 0 ∩
    ({s | (ts (σ m) : ℝ) ≤ (ts (σ m) : ℝ) + s / R (σ m)} ∪
      {s | ∃ i, (ts (σ m) : ℝ) + s / R (σ m) = (Hs (σ m)).time i})
  have hEs : ∀ m s, s ≤ 0 → s ∉ E' m →
      (ts (σ m) : ℝ) + s / R (σ m) < ts (σ m) ∧
        ∀ i, (ts (σ m) : ℝ) + s / R (σ m) ≠ (Hs (σ m)).time i := by
    intro m s hs hsE
    simp only [E', mem_inter_iff, mem_Iic, mem_union, mem_ofPred_eq, not_and, not_or,
      not_exists] at hsE
    obtain ⟨h1, h2⟩ := hsE hs
    exact ⟨not_le.mp h1, h2⟩
  have hE' : ∀ m, (E' m \ Icc (-(0 : ℝ)) 0).Finite := by
    intro m
    refine (Set.finite_range fun i : Fin ((Hs (σ m)).eventCount + 1) =>
      R (σ m) * ((Hs (σ m)).time i - ts (σ m))).subset ?_
    rintro s ⟨⟨hs0, hs⟩, hsI⟩
    have hs0 : s ≤ 0 := hs0
    have hRm := hRpos m
    rcases hs with hs | ⟨i, hi⟩
    · refine absurd ⟨?_, hs0⟩ hsI
      have hs' : (ts (σ m) : ℝ) ≤ (ts (σ m) : ℝ) + s / R (σ m) := hs
      have hsR : 0 ≤ s / R (σ m) := by linarith
      have hsn : 0 ≤ s := by
        by_contra hneg
        have := div_neg_of_neg_of_pos (not_le.mp hneg) hRm
        linarith
      linarith
    · refine ⟨i, ?_⟩
      have hi' : (ts (σ m) : ℝ) + s / R (σ m) = (Hs (σ m)).time i := hi
      have : s / R (σ m) = (Hs (σ m)).time i - ts (σ m) := by
        linarith
      change R (σ m) * ((Hs (σ m)).time i - ts (σ m)) = s
      rw [← this, mul_div_assoc']
      exact mul_div_cancel_left₀ s hRm.ne'
  obtain ⟨D, hD, hL1⟩ := exists_eventually_neckAlternatives_or_isCompact_of_survivor_blocks_P6L2.{u}
  obtain ⟨C, hC⟩ : ∃ C : ℝ, C = max 1 (max (2 * |C1s|) C2s) := ⟨_, rfl⟩
  have hC1 : 1 ≤ C := hC ▸ le_max_left _ _
  have hC0 : max (2 * |C1s|) C2s ≤ C := hC ▸ le_max_right _ _
  obtain ⟨qW, hqW⟩ : ∃ qW : ℝ,
      qW = max Cs ((Real.exp 1 * (C + (D + 2 * ε⁻¹) * Real.sqrt C)) ^ 2) := ⟨_, rfl⟩
  have hqWsq : (Real.exp 1 * (C + (D + 2 * ε⁻¹) * Real.sqrt C)) ^ 2 ≤ qW :=
    hqW ▸ le_max_right _ _
  have hqWs : Cs ≤ qW := hqW ▸ le_max_left _ _
  have hqs' : ∀ m, qs (σ m) ≤ R (σ m) * qW := fun m =>
    (hqs (σ m)).trans ((mul_le_mul_of_nonneg_right hqWs (hRpos m).le).trans_eq (mul_comm _ _))
  -- 局部化：witness / 导数 / BCAD 都是 trace-local（G1 的 `_P6L`）
  have hW := hL1 (Hs := fun m => Hs (σ m)) (ts := fun m => ts (σ m)) (ys := fun m => ys (σ m))
    (hR := hRpos) (W := W) (h := h)
    (c := fun k => ((k + 1 : ℕ) : ℝ) / ((k + 2 : ℕ) : ℝ) *
      (Tstar * ((k + 1 : ℕ) : ℝ) / ((k + 2 : ℕ) : ℝ))) hτs0 (fun k => (hcτ k).le)
    (fun k => (hblock k).mono fun _ hn => hn.1) (fun k => (hblock k).mono fun _ hn => hn.2.2.1)
    (fun k => (hblock k).mono fun _ hn => hn.2.2.2.1) hlow (qs := fun m => qs (σ m)) (E := E')
    hε hC1 hC0 hqs' hqWsq
    (fun k => by
      obtain ⟨K, hK, htrK⟩ := hext _ (hτs0 k) (hτsT k) (2 * ((k + 3 : ℕ) : ℝ)) (by positivity)
      exact Filter.eventually_map.mp (hwitC σ hσ ((k + 3 : ℕ) : ℝ)
        (Tstar * ((k + 1 : ℕ) : ℝ) / ((k + 2 : ℕ) : ℝ)) K (by positivity) (hτs0 k) hK
        (Filter.eventually_map.mpr htrK))) hEs
  have hderivB := eventually_abs_derivWithin_scalar_le_of_survivor_blocks_P6L2
    (Hs := fun m => Hs (σ m)) (ts := fun m => ts (σ m)) (ys := fun m => ys (σ m))
    (hR := hRpos) (W := W) (h := h) (τ := (fun k => Tstar * ((k + 1 : ℕ) : ℝ) / ((k + 2 : ℕ) : ℝ)))
    (fun k => (hblock k).mono fun _ hn => hn.1) (fun k => (hblock k).mono fun _ hn => hn.2.2.2.1)
    (E := E') (Ct := (Ctime : ℝ)) (qD := Cq) (NNReal.coe_nonneg _)
    (qst := fun m => qcan (σ m)) (fun m => (hqcan (σ m)).trans_eq (mul_comm _ _))
    (fun k => by
      obtain ⟨K, hK, htrK⟩ := hext _ (hτs0 k) (hτsT k) (2 * ((k + 3 : ℕ) : ℝ)) (by positivity)
      exact Filter.eventually_map.mp (hderivC σ hσ ((k + 3 : ℕ) : ℝ)
        (Tstar * ((k + 1 : ℕ) : ℝ) / ((k + 2 : ℕ) : ℝ)) K (by positivity) (hτs0 k) hK
        (Filter.eventually_map.mpr htrK)))
    (fun m s hs hsE => (hEs m s hs hsE).2)
  have happrox := survivor_blocks_scalar_le_at_distance_P6L
    (Hs := fun m => Hs (σ m)) (ts := fun m => ts (σ m)) (ys := fun m => ys (σ m))
    (hR := hRpos) (W := W) (h := h) (τ := (fun k => Tstar * ((k + 1 : ℕ) : ℝ) / ((k + 2 : ℕ) : ℝ)))
    (fun k => (hblock k).mono fun _ hn => hn.1) (fun k => (hblock k).mono fun _ hn => hn.2.2.2.1)
    (c := fun k => ((k + 1 : ℕ) : ℝ) / ((k + 2 : ℕ) : ℝ) *
      (Tstar * ((k + 1 : ℕ) : ℝ) / ((k + 2 : ℕ) : ℝ))) (fun k => (hcτ k).le)
    (fun A Dd hA hDd => (hbcad A Dd hA hDd).imp fun _ hC' σ' hσ' Dw hDw =>
      hσ.tendsto_atTop.eventually (hC' σ' hσ' Dw hDw))
  have hradiiσ : Tendsto (fun m => ρnc (σ m) * Real.sqrt (R (σ m))) atTop atTop :=
    hradii.comp hσ.tendsto_atTop
  obtain ⟨C₀, hC₀⟩ := exists_uniform_scalar_bound_of_local_flow_limit_on_window hf F Cd hcan hPc
    hconn hV hVF hφF
    (fun k => by
      filter_upwards [hf.tendsto_atTop.eventually (hblock k),
        hballF ((k + 3 : ℕ) : ℝ) (by positivity)] with j hj hb x hx
      have hx' : x ∈ (W k (f j) : Set _) := hx
      rw [hj.1] at hx'
      exact hb (show riemannianEDistOf _ _ _ ≤ _ from le_of_lt hx'))
    hT hτs0 hcτ hcmono hcT hGl0 hGlsol hψ₁ hconvG hsol hRσ hPhi
    (fun k => (hpinchW k).mono fun _ hn s hs x => hn s ⟨by linarith [hs.1, hcτ k], hs.2⟩ x)
    hlip (ζ := fun _ => (0 : ℝ)) tendsto_const_nhds hE' hεX hC1
    (by positivity : (0 : ℝ) < κ / 250) hW hderivB
    (fun hcomplete =>
      parabolicallyKappaNoncollapsedBelowScale_of_local_flow_limit_on_openClosed
        hT (fun k => Tstar * ((k + 1 : ℕ) : ℝ) / ((k + 2 : ℕ) : ℝ))
        (fun k => ((k + 1 : ℕ) : ℝ) / ((k + 2 : ℕ) : ℝ) *
          (Tstar * ((k + 1 : ℕ) : ℝ) / ((k + 2 : ℕ) : ℝ))) hc0 hcτ hcT' hcmono hcex hsol hκ
        hradiiσ hncW hf F hVmono hVcover hVF φ hφ hφF hGlsol hcomplete hψ₁ hconvG 1 one_pos)
    happrox
  refine ⟨fun i => f (ψ₁ i), hf.comp hψ₁, max C₀ 0 + 1, by positivity,
    fun T' hT' hT'T A hA => ?_⟩
  exact eventually_scalar_backwardPointTrace_le_of_window_limit
    (Hs := fun m => Hs (σ m)) (ts := fun m => ts (σ m)) (ys := fun m => ys (σ m))
    (hR := hRpos) (W := W) (h := h) (τ := (fun k => Tstar * ((k + 1 : ℕ) : ℝ) / ((k + 2 : ℕ) : ℝ)))
    (fun k => (hblock k).mono fun _ hn => hn.2.2.2.1) hf F Cd hcan hPc hV hφF
    (fun k => (hcτ k).le) hcmono hcT hψ₁ hconvG hC₀ hT' hT'T hA

end ObservedHistory

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
