import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.Local.TracedRegionAncientLimitTimeControl_P6L
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.Local.TracedRegionAncientLimitNeckAlternatives_P6L
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.Local.TracedRegionAncientLimitDerivativeCutoff_P6L
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.TracedRegionAncientLimitScalarBound

/-!
# `TracedRegionAncientLimitScalarBound:42` 的局部化副本（O-CH11-P6D G2，后缀 `_P6L`）

原定理：`ObservedHistory.exists_bounded_ancient_pointed_flow_limit_of_spatially_canonical_before`
（`ST/TracedRegionAncientLimitScalarBound.lean:42`）：古代极限的**有界曲率**
`∃ C, ∀ s ≤ 0, R(G s) ≤ C`（P6 L8 余项的核心）。

**改动的前提**（常数 `epsW` 仍在序列 / 历史之前取；其余量词顺序不变）：
* `hnc` / `hpinch` → P6B 形（`hseed` + trace-local `hkappa`、trace-local `hpinch`），经下层
  `exists_ancient_pointed_flow_limit_with_time_lipschitz_survivor_maps_of_traced_seed_P6L`；
* `hwit` / `hderiv`（全局 `∀ v < t₀`, `∀ p`）→ **trace-local**：只对
  `B_{t n}(y n, D/√R n)` 中点的 backward trace 在 `v ∈ [t n − T/R n, t n)`（非 event 时刻）的
  点要求 witness / `|∂ₜ⁻R| ≤ Ctime R²`。原证明只在 survivor 点 `fs j z` 用它们（经下层
  `exists_neckAlternatives_of_survivor_maps_P6L` /
  `abs_derivWithin_scalar_le_of_survivor_maps_of_lt_P6L`），
  survivor maps 本身给出 trace（`tr0.restrictFirst`），成员关系 `z ∈ W k n = B(y n, (k+3)/√R n)`；
* `t₀ := t`（sliver 恒为 0），`ρ` → `ρnc`（`ρnc n √R n → ∞`）。
结论形与原定理相同（输出 block 的 `hnc` 子句同 P6B L8c：无 `t₀` 子句，半径 `ρnc n √R n`）。
-/

set_option autoImplicit false

noncomputable section

open Set Filter TopologicalSpace
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.CheegerGromovCompactness
open scoped Manifold ContDiff Topology NNReal ENNReal

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

open private ObservedHistory.scaleMetric_restrictOpen ObservedHistory.mem_Icc_of_mem_window
  ObservedHistory.isCompact_riemannianClosedBallOf_restrictOpen
  ObservedHistory.riemannianBallOf_scaleMetric_eq from
  DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.TracedRegionAncientLimit

namespace ObservedHistory

open Perelman.CanonicalNeighborhood.FiniteHorn (SpatialCanonicalWitness SpatialNeck
  exists_scalar_bound_of_ancient_pointed_flow_limit_of_approximants_of_time_lipschitz)

universe u

private local instance {M : Type u} [TopologicalSpace M] [ChartedSpace ThreeSpace M]
    [SigmaCompactSpace M] (U : Opens M) : SigmaCompactSpace U :=
  isSigmaCompact_iff_sigmaCompactSpace.mp
    (Geometry.isSigmaCompact_of_isOpen ThreeModel U.isOpen)

attribute [local instance] PointedRiemannianManifold.topology PointedRiemannianManifold.charted
  PointedRiemannianManifold.smooth PointedRiemannianManifold.t2
  PointedRiemannianManifold.sigmaCompact

/-- `:42` 的局部化（`_P6L`）：局部 κ / pinching / witness / 时间导数（全部 trace-local）⇒
带 survivor maps 的古代 pointed 极限，`κ/250`-noncollapsed 且**曲率有界**。 -/
theorem exists_bounded_ancient_pointed_flow_limit_of_spatially_canonical_before_P6L :
    ∃ epsW : ℝ, 0 < epsW ∧
    ∀ (H : ℕ → ObservedHistory.{u}) (t : ∀ n, Icc (0 : ℝ) (H n).horizon)
    (y : ∀ n, ((H n).stageAt (t n)).Carrier) (R : ℕ → ℝ) (hR : ∀ n, 0 < R n),
    Tendsto R atTop atTop →
    (∀ A T : ℝ, 0 < A → 0 < T → ∃ K : ℝ, 0 ≤ K ∧ ∀ᶠ n in atTop,
      (H n).isTracedRegion (t n) (y n) (A / Real.sqrt (R n)) (T / R n) (K * R n)) →
    ∀ {r₀ w : ℝ}, 0 < r₀ → 0 < w →
    (∀ᶠ n in atTop,
      ENNReal.ofReal (w * (r₀ / Real.sqrt (R n)) ^ 3) ≤
        Integral.Measure.riemannianVolumeMeasure ThreeModel ((H n).stageAt (t n)).Carrier
          ((H n).stageMetric ((H n).activeStage (t n)) (t n))
          (riemannianBallOf ((H n).stageMetric ((H n).activeStage (t n)) (t n)) (y n)
            (r₀ / Real.sqrt (R n)))) →
    ∀ {κ : ℝ}, 0 < κ → ∀ ρnc : ℕ → ℝ,
    Tendsto (fun n => ρnc n * Real.sqrt (R n)) atTop atTop →
    (∀ D T : ℝ, 0 < D → 0 < T → ∀ᶠ n in atTop,
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
            (tr.point ((H n).activeStage v) le_rfl ((H n).activeStage_mono hvt)) r'') →
    ∀ {Phi : ℝ → ℝ}, Perelman.AdmissiblePinchingFunction Phi →
    (∀ D T : ℝ, 0 < D → 0 < T → ∀ᶠ n in atTop,
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
            (tr.point ((H n).activeStage v) le_rfl ((H n).activeStage_mono hvt))))) →
    ∀ {eps C1 C2 Cs Cq : ℝ} {Ctime : ℝ≥0} {qs qcan : ℕ → ℝ}, 0 < eps → eps ≤ epsW →
    (∀ n, qs n ≤ Cs * R n) → (∀ n, qcan n ≤ Cq * R n) →
    (∀ D T : ℝ, 0 < D → 0 < T → ∀ᶠ n in atTop,
      ∀ x ∈ riemannianBallOf ((H n).stageMetric ((H n).activeStage (t n)) (t n)) (y n)
          (D / Real.sqrt (R n)),
      ∀ (v : Icc (0 : ℝ) (H n).horizon) (hvt : v ≤ t n), (t n : ℝ) - T / R n ≤ v →
      (v : ℝ) < t n → (H n).time ((H n).activeStage v) < v →
      ∀ tr : BackwardPointTrace (H n) ((H n).activeStage v) ((H n).activeStage (t n))
        ((H n).activeStage_mono hvt) x,
        qs n < metricScalarAt ((H n).stageMetric ((H n).activeStage v) v)
          (tr.point ((H n).activeStage v) le_rfl ((H n).activeStage_mono hvt)) →
        ∃ Wt : SpatialCanonicalWitness ((H n).stageMetric ((H n).activeStage v) v) eps C1 C2
            (tr.point ((H n).activeStage v) le_rfl ((H n).activeStage_mono hvt)),
          Wt.capTubeHasNeckChart eps) →
    (∀ D T : ℝ, 0 < D → 0 < T → ∀ᶠ n in atTop,
      ∀ x ∈ riemannianBallOf ((H n).stageMetric ((H n).activeStage (t n)) (t n)) (y n)
          (D / Real.sqrt (R n)),
      ∀ (v : Icc (0 : ℝ) (H n).horizon) (hvt : v ≤ t n), (t n : ℝ) - T / R n ≤ v →
      (v : ℝ) < t n → (H n).time ((H n).activeStage v) < v →
      ∀ tr : BackwardPointTrace (H n) ((H n).activeStage v) ((H n).activeStage (t n))
        ((H n).activeStage_mono hvt) x,
        qcan n < metricScalarAt ((H n).stageMetric ((H n).activeStage v) v)
          (tr.point ((H n).activeStage v) le_rfl ((H n).activeStage_mono hvt)) →
        |derivWithin (fun v' => metricScalarAt ((H n).stageMetric ((H n).activeStage v) v')
            (tr.point ((H n).activeStage v) le_rfl ((H n).activeStage_mono hvt)))
          (Iic (v : ℝ)) v| ≤
          Ctime * metricScalarAt ((H n).stageMetric ((H n).activeStage v) v)
            (tr.point ((H n).activeStage v) le_rfl ((H n).activeStage_mono hvt)) ^ 2) →
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
                  (∀ ρ' : ℝ, 0 < ρ' → Perelman.ParabolicallyKappaNoncollapsedBelowScale
                    ({ base.metric := G } : SolutionOn (I := ThreeModel) (M := P.M)
                      (RealTimeInterval.infiniteClosed 0 0 le_rfl)) (κ / 250) ρ') ∧
                  ∃ C : ℝ, ∀ s ≤ 0, ∀ x : P.M, metricScalarAt (G s) x ≤ C := by
  obtain ⟨epsW, hepsW, hB11⟩ :=
    exists_scalar_bound_of_ancient_pointed_flow_limit_of_approximants_of_time_lipschitz.{u}
  obtain ⟨D, hD, hB6⟩ := exists_neckAlternatives_of_survivor_maps_P6L.{u}
  refine ⟨epsW, hepsW, ?_⟩
  intro H t y R hR hRlim htraced r₀ w hr₀ hw hseed κ hκ ρnc hradii hkappa Phi hPhi hpinch eps C1
    C2 Cs Cq Ctime qs qcan heps hepsW' hqs hqcan hwit hderiv X
  obtain ⟨W, h, hblock, hlip, hscal, hlow, f, hf, P, F, ⟨Cd, hcan⟩, hPc, hconn, hballF, V, N, hV,
    hVF, φ, hφ, hφF, G, hG0, hG, ψ, hψ, hconv, hκG⟩ :=
    exists_ancient_pointed_flow_limit_with_time_lipschitz_survivor_maps_of_traced_seed_P6L H t y
      R hR hRlim htraced hr₀ hw hseed hκ ρnc hradii hkappa hPhi hpinch
  refine ⟨W, h, hblock, hlip, hscal, hlow, f, hf, P, F, ⟨Cd, hcan⟩, hPc, hconn, hballF, V, N, hV,
    hVF, φ, hφ, hφF, G, hG0, hG, ψ, hψ, hconv, hκG, ?_⟩
  -- 局部化：`t₀ := t`（trace-local `hwit` / `hderiv` 只在 `v < t n` 要求），sliver 恒为 0
  let t₀ : ℕ → ℝ := fun n => (t n : ℝ)
  have hsliver : Tendsto (fun n => R n * ((t n : ℝ) - t₀ n)) atTop (𝓝 0) := by
    simp only [t₀, sub_self, mul_zero]
    exact tendsto_const_nhds
  have hθ (k : ℕ) : 0 < 2 * ((k + 2 : ℕ) : ℝ) := by positivity
  obtain ⟨C, hC⟩ : ∃ C : ℝ, C = max 1 (max (2 * |C1|) C2) := ⟨_, rfl⟩
  have hC1 : 1 ≤ C := hC ▸ le_max_left _ _
  have hC0 : max (2 * |C1|) C2 ≤ C := hC ▸ le_max_right _ _
  have hC00 : 0 ≤ max (2 * |C1|) C2 := le_max_of_le_left (by positivity)
  have hDe : 0 ≤ D + 2 * eps⁻¹ := by have := inv_pos.mpr heps; linarith
  obtain ⟨qW, hqW⟩ : ∃ qW : ℝ,
      qW = max Cs ((Real.exp 1 * (C + (D + 2 * eps⁻¹) * Real.sqrt C)) ^ 2) := ⟨_, rfl⟩
  have hxnn : 0 ≤ Real.exp 1 * (C + (D + 2 * eps⁻¹) * Real.sqrt C) :=
    mul_nonneg (Real.exp_pos 1).le
      (add_nonneg (by linarith) (mul_nonneg hDe (Real.sqrt_nonneg _)))
  have hqWsq : (Real.exp 1 * (C + (D + 2 * eps⁻¹) * Real.sqrt C)) ^ 2 ≤ qW :=
    hqW ▸ le_max_right _ _
  have hqWs : Cs ≤ qW := hqW ▸ le_max_left _ _
  have hqW0 : 0 ≤ qW := (sq_nonneg _).trans hqWsq
  let E : ℕ → Set ℝ := fun n => Iic 0 ∩ ({s | t₀ n ≤ (t n : ℝ) + s / R n} ∪
    {s | ∃ i, (t n : ℝ) + s / R n = (H n).time i})
  have hEs : ∀ n s, s ≤ 0 → s ∉ E n →
      (t n : ℝ) + s / R n < t₀ n ∧ ∀ i, (t n : ℝ) + s / R n ≠ (H n).time i := by
    intro n s hs hsE
    simp only [E, mem_inter_iff, mem_Iic, mem_union, mem_ofPred_eq, not_and, not_or,
      not_exists] at hsE
    obtain ⟨h1, h2⟩ := hsE hs
    exact ⟨not_le.mp h1, h2⟩
  have hE : ∀ n, (E n \ Icc (-(R n * (t n - t₀ n))) 0).Finite := by
    intro n
    refine (Set.finite_range fun i : Fin ((H n).eventCount + 1) =>
      R n * ((H n).time i - t n)).subset ?_
    rintro s ⟨⟨hs0, hs⟩, hsI⟩
    have hs0 : s ≤ 0 := hs0
    rcases hs with hs | ⟨i, hi⟩
    · refine absurd ⟨?_, hs0⟩ hsI
      have hs' : (t₀ n - t n) * R n ≤ s :=
        (le_div_iff₀ (hR n)).mp (show t₀ n - t n ≤ s / R n by
          have : t₀ n ≤ (t n : ℝ) + s / R n := hs
          linarith)
      linarith
    · refine ⟨i, ?_⟩
      have : s / R n = (H n).time i - t n := by linarith
      change R n * ((H n).time i - t n) = s
      rw [← this, mul_div_assoc']
      exact mul_div_cancel_left₀ s (hR n).ne'
  have hreg : ∀ n s, (∀ i, (t n : ℝ) + s / R n ≠ (H n).time i) →
      ∀ hv : (t n : ℝ) + s / R n ∈ Icc (0 : ℝ) (H n).horizon,
        (H n).time ((H n).activeStage ⟨_, hv⟩) < (t n : ℝ) + s / R n :=
    fun n s hne hv => lt_of_le_of_ne ((H n).activeStage_time_le _) fun heq => hne _ heq.symm
  -- 局部化：pinching 只在 survivor maps 的 backward trace 点上用（照 P6B M8）
  have hpinchW : ∀ k : ℕ, ∀ᶠ n in atTop, ∀ q ∈ Icc (-((k + 1 : ℕ) : ℝ)) 0,
      ∀ x : W k n, curvatureOperatorLowerBoundAt (h k n q) x
        (metricAlgebraicCurvatureTensorAt (h k n q) x)
        (Perelman.rescalePinchingFunction (R n) Phi (metricScalarAt (h k n q) x)) := by
    intro k
    filter_upwards [hblock k, hpinch ((k + 3 : ℕ) : ℝ) (2 * ((k + 2 : ℕ) : ℝ))
      (by positivity) (hθ k)] with n hn hpn q hq x
    obtain ⟨hWset, -, -, ⟨a, hat, ha, fs, hfs, -, hcs, hls, hp⟩, -⟩ := hn
    have hqθ : q ∈ Icc (-(2 * ((k + 2 : ℕ) : ℝ))) 0 :=
      ⟨by have := hq.1; push_cast at this ⊢; linarith, hq.2⟩
    have hv := ObservedHistory.mem_Icc_of_mem_window (hR n) ha hqθ
    let v : Icc (0 : ℝ) (H n).horizon :=
      ⟨(t n : ℝ) + q / R n, a.2.1.trans hv.1, hv.2.trans (t n).2.2⟩
    have hav : a ≤ v := hv.1
    have hvt : v ≤ t n := hv.2
    let j : (H n).StageInterval ((H n).activeStage a) ((H n).activeStage (t n)) :=
      ⟨(H n).activeStage v, (H n).activeStage_mono hav, (H n).activeStage_mono hvt⟩
    have hq' := hp q hqθ j ((H n).activeStage_mem v)
    -- the actual backward trace of `x` carried by the survivor maps
    let tr0 : BackwardPointTrace (H n) ((H n).activeStage a) ((H n).activeStage (t n))
        ((H n).activeStage_mono hat) x.val :=
      { point := fun i hi hl => fs ⟨i, hi, hl⟩ x
        endpoint_eq := hls x
        crossing := fun i hi hl => hcs i hi hl x }
    let tr := tr0.restrictFirst ((H n).activeStage_mono hav) ((H n).activeStage_mono hvt)
    have hxW : (x : ((H n).stageAt (t n)).Carrier) ∈
        riemannianBallOf ((H n).stageMetric ((H n).activeStage (t n)) (t n)) (y n)
          (((k + 3 : ℕ) : ℝ) / Real.sqrt (R n)) := by
      have hx := x.property
      change (x : (X.obj n).M) ∈ (W k n : Set (X.obj n).M) at hx
      rw [hWset] at hx
      change (x : ((H n).stageAt (t n)).Carrier) ∈
        riemannianBallOf (scaleMetric (R n) (hR n)
          ((H n).stageMetric ((H n).activeStage (t n)) (t n))) (y n) ((k + 3 : ℕ) : ℝ) at hx
      rwa [ObservedHistory.riemannianBallOf_scaleMetric_eq] at hx
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
  have he2 : Real.exp 1 ^ 2 = Real.exp 2 := by
    rw [← Real.exp_nat_mul]
    norm_num
  have hW : ∀ k : ℕ, ∀ᶠ n in atTop, ∀ s ∈ Icc (-((k + 1 : ℕ) : ℝ)) 0, s ∉ E n →
      ∀ z : W k n, (z : (X.obj n).M) ∈
        riemannianClosedBallOf (X.obj n).metric (X.obj n).basepoint ((k + 1 : ℕ) : ℝ) →
      qW < metricScalarAt (h k n s) z →
      Nonempty (SpatialNeck (h k n s) eps z) ∨
        (∃ w : W k n, Nonempty (SpatialNeck (h k n s) eps w) ∧
          metricScalarAt (h k n s) z ≤ C * metricScalarAt (h k n s) w ∧
          metricScalarAt (h k n s) w ≤ C * metricScalarAt (h k n s) z ∧
          riemannianEDistOf (h k n s) z w <
            ENNReal.ofReal (C / Real.sqrt (metricScalarAt (h k n s) z))) ∨
        ∀ y ∈ connectedComponent z,
          metricScalarAt (h k n s) y ≤ C * metricScalarAt (h k n s) z := by
    intro k
    filter_upwards [hblock k, hlow k, hwit ((k + 3 : ℕ) : ℝ) (2 * ((k + 2 : ℕ) : ℝ))
      (by positivity) (hθ k)] with n hn hlown hwn s hs hsE z hz hqz
    obtain ⟨hWset, -, h0eq, ⟨a, hat, ha, fs, hfs, hinj, hcs, hls, hp⟩, -⟩ := hn
    -- 局部化：survivor 点 witness 由 trace-local `hwit` 给出（trace = survivor maps 本身）
    have hwitS : ∀ v : Icc (0 : ℝ) (H n).horizon, (v : ℝ) < t₀ n →
        (H n).time ((H n).activeStage v) < v → ∀ (hav : a ≤ v) (hvt : v ≤ t n) (x : W k n),
          qs n < metricScalarAt ((H n).stageMetric ((H n).activeStage v) v)
            (fs ⟨(H n).activeStage v, (H n).activeStage_mono hav, (H n).activeStage_mono hvt⟩
              x) →
          ∃ Wt : SpatialCanonicalWitness ((H n).stageMetric ((H n).activeStage v) v) eps C1 C2
              (fs ⟨(H n).activeStage v, (H n).activeStage_mono hav, (H n).activeStage_mono hvt⟩
                x),
            Wt.capTubeHasNeckChart eps := by
      intro v hvt₀ hreg hav hvt x hq
      let tr0 : BackwardPointTrace (H n) ((H n).activeStage a) ((H n).activeStage (t n))
          ((H n).activeStage_mono hat) x.val :=
        { point := fun i hi hl => fs ⟨i, hi, hl⟩ x
          endpoint_eq := hls x
          crossing := fun i hi hl => hcs i hi hl x }
      have hxW : (x : ((H n).stageAt (t n)).Carrier) ∈
          riemannianBallOf ((H n).stageMetric ((H n).activeStage (t n)) (t n)) (y n)
            (((k + 3 : ℕ) : ℝ) / Real.sqrt (R n)) := by
        have hx := x.property
        change (x : (X.obj n).M) ∈ (W k n : Set (X.obj n).M) at hx
        rw [hWset] at hx
        change (x : ((H n).stageAt (t n)).Carrier) ∈
          riemannianBallOf (scaleMetric (R n) (hR n)
            ((H n).stageMetric ((H n).activeStage (t n)) (t n))) (y n) ((k + 3 : ℕ) : ℝ) at hx
        rwa [ObservedHistory.riemannianBallOf_scaleMetric_eq] at hx
      have hav' : (t n : ℝ) - 2 * ((k + 2 : ℕ) : ℝ) / R n ≤ v := by rw [← ha]; exact hav
      exact hwn x hxW v hvt hav' hvt₀ hreg
        (tr0.restrictFirst ((H n).activeStage_mono hav) ((H n).activeStage_mono hvt)) hq
    obtain ⟨hst₀, hne⟩ := hEs n s hs.2 hsE
    have hs' : s ∈ Icc (-(2 * ((k + 2 : ℕ) : ℝ))) 0 :=
      ⟨by have := hs.1; push_cast at this ⊢; linarith, hs.2⟩
    have hzpos : 0 < metricScalarAt (h k n s) z := hqW0.trans_lt hqz
    have hcpt : IsCompact (riemannianClosedBallOf (h k n 0) z 1) := by
      have hdom : (t n : ℝ) + 0 / R n ∈ (H n).stageDomain ((H n).activeStage (t n)) := by
        simpa using (H n).activeStage_mem (t n)
      rw [h0eq 0 ⟨neg_nonpos.mpr (Nat.cast_nonneg _), le_rfl⟩ hdom, zero_div, add_zero,
        ObservedHistory.scaleMetric_restrictOpen]
      apply ObservedHistory.isCompact_riemannianClosedBallOf_restrictOpen
      intro w hw
      rw [hWset]
      have hz' : riemannianEDistOf (X.obj n).metric (X.obj n).basepoint (z : (X.obj n).M) ≤
          ENNReal.ofReal ((k + 1 : ℕ) : ℝ) := hz
      have hw' : riemannianEDistOf (X.obj n).metric (z : (X.obj n).M) w ≤ ENNReal.ofReal 1 := hw
      change riemannianEDistOf (X.obj n).metric (X.obj n).basepoint w <
        ENNReal.ofReal ((k + 3 : ℕ) : ℝ)
      calc riemannianEDistOf (X.obj n).metric (X.obj n).basepoint w
          ≤ riemannianEDistOf (X.obj n).metric (X.obj n).basepoint (z : (X.obj n).M) +
              riemannianEDistOf (X.obj n).metric (z : (X.obj n).M) w :=
            riemannianEDistOf_triangle _ _ _ _
        _ ≤ ENNReal.ofReal ((k + 1 : ℕ) : ℝ) + ENNReal.ofReal 1 := add_le_add hz' hw'
        _ = ENNReal.ofReal (((k + 1 : ℕ) : ℝ) + 1) :=
            (ENNReal.ofReal_add (by positivity) (by norm_num)).symm
        _ < ENNReal.ofReal ((k + 3 : ℕ) : ℝ) :=
            (ENNReal.ofReal_lt_ofReal_iff (by positivity)).mpr (by push_cast; linarith)
    have hsmall : Real.exp 1 * (max (2 * |C1|) C2 + (D + 2 * eps⁻¹) *
        Real.sqrt (max (2 * |C1|) C2)) < Real.sqrt (metricScalarAt (h k n s) z) := by
      refine lt_of_le_of_lt ?_ ((Real.lt_sqrt hxnn).mpr (hqWsq.trans_lt hqz))
      gcongr
    have key := hB6 (H n) (t n) (hR n)
      ((hqs n).trans (by rw [mul_comm Cs]; exact mul_le_mul_of_nonneg_left hqWs (hR n).le))
      (Real.exp_pos 1) a ha fs hfs hinj hp hwitS hs' hst₀ (hreg n s hne) z hcpt
      (fun y _ u => by rw [he2]; exact hlown s hs y u) hqz hsmall
    rcases key with h1 | ⟨w, hw, h2, h3, h4⟩ | h5
    · exact Or.inl h1
    · have hw0 : 0 < metricScalarAt (h k n s) w := by
        by_contra hneg
        have := mul_nonpos_of_nonneg_of_nonpos hC00 (not_lt.mp hneg)
        linarith
      refine Or.inr (Or.inl ⟨w, hw, h2.trans (mul_le_mul_of_nonneg_right hC0 hw0.le),
        h3.trans (mul_le_mul_of_nonneg_right hC0 hzpos.le), h4.trans_le ?_⟩)
      exact ENNReal.ofReal_le_ofReal (div_le_div_of_nonneg_right hC0 (Real.sqrt_nonneg _))
    · exact Or.inr (Or.inr fun y hy => (h5 y hy).trans (mul_le_mul_of_nonneg_right hC0 hzpos.le))
  have hder : ∀ k : ℕ, ∀ᶠ n in atTop, ∀ s ∈ Ioo (-((k + 2 : ℕ) : ℝ)) 0, s ∉ E n →
      ∀ z : W k n, Cq < metricScalarAt (h k n s) z →
        |derivWithin (fun v => metricScalarAt (h k n v) z) (Iic s) s| ≤
          (Ctime : ℝ) * metricScalarAt (h k n s) z ^ 2 := by
    intro k
    filter_upwards [hblock k, hderiv ((k + 3 : ℕ) : ℝ) (2 * ((k + 2 : ℕ) : ℝ))
      (by positivity) (hθ k)] with n hn hdn s hs hsE z hz
    obtain ⟨hWset, -, -, ⟨a, hat, ha, fs, hfs, -, hcs, hls, hp⟩, -⟩ := hn
    obtain ⟨hst₀, hne⟩ := hEs n s hs.2.le hsE
    -- 局部化：survivor 点导数界由 trace-local `hderiv` 给出
    have hderS : ∀ v : Icc (0 : ℝ) (H n).horizon, (v : ℝ) < t₀ n →
        (H n).time ((H n).activeStage v) < v → ∀ (hav : a ≤ v) (hvt : v ≤ t n) (x : W k n),
          qcan n < metricScalarAt ((H n).stageMetric ((H n).activeStage v) v)
            (fs ⟨(H n).activeStage v, (H n).activeStage_mono hav, (H n).activeStage_mono hvt⟩
              x) →
          |derivWithin (fun v' => metricScalarAt ((H n).stageMetric ((H n).activeStage v) v')
              (fs ⟨(H n).activeStage v, (H n).activeStage_mono hav, (H n).activeStage_mono hvt⟩
                x)) (Iic (v : ℝ)) v| ≤
            (Ctime : ℝ) * metricScalarAt ((H n).stageMetric ((H n).activeStage v) v)
              (fs ⟨(H n).activeStage v, (H n).activeStage_mono hav, (H n).activeStage_mono hvt⟩
                x) ^ 2 := by
      intro v hvt₀ hreg hav hvt x hq
      let tr0 : BackwardPointTrace (H n) ((H n).activeStage a) ((H n).activeStage (t n))
          ((H n).activeStage_mono hat) x.val :=
        { point := fun i hi hl => fs ⟨i, hi, hl⟩ x
          endpoint_eq := hls x
          crossing := fun i hi hl => hcs i hi hl x }
      have hxW : (x : ((H n).stageAt (t n)).Carrier) ∈
          riemannianBallOf ((H n).stageMetric ((H n).activeStage (t n)) (t n)) (y n)
            (((k + 3 : ℕ) : ℝ) / Real.sqrt (R n)) := by
        have hx := x.property
        change (x : (X.obj n).M) ∈ (W k n : Set (X.obj n).M) at hx
        rw [hWset] at hx
        change (x : ((H n).stageAt (t n)).Carrier) ∈
          riemannianBallOf (scaleMetric (R n) (hR n)
            ((H n).stageMetric ((H n).activeStage (t n)) (t n))) (y n) ((k + 3 : ℕ) : ℝ) at hx
        rwa [ObservedHistory.riemannianBallOf_scaleMetric_eq] at hx
      have hav' : (t n : ℝ) - 2 * ((k + 2 : ℕ) : ℝ) / R n ≤ v := by rw [← ha]; exact hav
      exact hdn x hxW v hvt hav' hvt₀ hreg
        (tr0.restrictFirst ((H n).activeStage_mono hav) ((H n).activeStage_mono hvt)) hq
    exact abs_derivWithin_scalar_le_of_survivor_maps_of_lt_P6L (H n) (t n) (hR n) Ctime.2
      (by rw [mul_comm]; exact hqcan n) a ha fs hfs hp hderS
      ⟨by have := hs.1; push_cast at this ⊢; linarith, hs.2.le⟩ hst₀ (hreg n s hne) z hz
  exact hB11 hf F Cd hcan hPc hconn hV hVF hφF hG0 hG hψ hconv
    (fun k => (hblock k).mono fun n hn => hn.2.1) hRlim hPhi hpinchW hlip hsliver hE heps hepsW'
    hC1 hW hder

/-- consumer（G1 内）：局部化 `:42` 的常数 `epsW` 在序列之前取出；真正的下游 consumer 是 G2 的
`_P6D` 装配（`IsAncientKappaSolution` + EXT2 witness + time control）。 -/
example : ∃ epsW : ℝ, 0 < epsW :=
  exists_bounded_ancient_pointed_flow_limit_of_spatially_canonical_before_P6L.{0}.imp
    fun _ h => h.1

end ObservedHistory

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
