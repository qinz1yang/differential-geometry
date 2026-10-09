import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.P6GuardFlowCmpC11SP
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.P6TriangularMappedJetsCXSP
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.P6StagePointedSeedCXSP
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.P6StageCompactnessCXSP
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.P6TracedInnerJetsCXSP
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.P6SeedVolumeBaseCXSP
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.P6ScalarAnchorCXSP
import DifferentialGeometry.Geometry.Compactness.CheegerGromov.Pointed.Convergence.ScalarRescaling

/-!
# SPINE-A1 G4：guard 分支 cone 端点高曲率点列处的二次 blow-up 反向极限（(A-2)）

CODEX-C §3.3 路线 2 的 (A-2)：第一层（原 guard 坏序列在 anchor 处、尺度 `Q = Hbase/r²` 的
pointed limit `Pl`）上任给高曲率点列 `xW`（`2 ≤ R_Pl`、`R_Pl → ∞`、shrinking 球 compact），
在**同一原 history** 的 mapped 中心处做二次 blow-up，产出
`RetainedCoreHistory.exists_local_backward_limit_at_final_slab_end_of_eventual_traces_P6L`
（`Local/BoundedCurvatureAtDistanceTracedCone_P6L.lean:444`）结论的史无关形（= SPINE-A2
`hflowA1` 的 per-Pl clause）。链：
1. G64 `exists_prepared_time_triangular_mapped_jets_CXSP`（`Afac = 2A+3`、`d0 = 2A+1`、
   `Δ = γ = 1`、`χ = Hbase/H0`）：三角子列 `ψ`，任意 strict `k` 的行 `ψ (k m)` 付 `xW m` 的
   mapped 中心 traced region `(√R)⁻¹ / θ/R / K0 R`（F8 的 `T₀(L)` 由三角形支付）；
2. G50 seed 距离尾段 + 前缀和 `η`（`Nm ≤ η m`）：mapped 中心落在 `B(p, Afac r)`；
3. `exists_scalar_rescaled_source_comparison`（ScalarRescaling:129）于 `Phi.compSubseq (ψ∘η)`
   选 `k`、给第一层比较 `q / G / F`；物理 scalar `R₂ = q·Q`，`t·R₂ ≥ 2 Hbase q → ∞`；
4. TimeCore `hb Afac` + `exists_seed_volume_base_CXSP` 付 canonical witness 与低 scalar 点
   （seed `p` 本身）；G46 `exists_inner_jets_of_traced_region_CXSP` 付 jets；
   G45 `exists_stage_pointed_convergence_of_jets_CXSP` 得二次 limit `P₂`（base scalar 1）；
5. G3 `guard_stageLocalFlow_endComparison_C11SP` 产 flow + end 比较，重索引成 P6L:444 形。
不消费 hw / κ'' / Budget / SCRS⁺ / RegularSlice；TimeCore 只经 `hb Afac`（G64 内部与第 4 步）。
-/

set_option autoImplicit false

noncomputable section

open Set Filter DifferentialGeometry DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Geometry.Collapse
open DifferentialGeometry.CheegerGromovCompactness
open DifferentialGeometry.PDE.RicciFlow
open DifferentialGeometry.PDE.RicciFlow.Perelman
open DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
open DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn
open GC.GeneralFlow
open scoped Manifold ContDiff Topology ENNReal NNReal

namespace GC.LongTime.Ch11

universe u

attribute [local instance] PointedRiemannianManifold.topology PointedRiemannianManifold.charted
  PointedRiemannianManifold.smooth PointedRiemannianManifold.t2
  PointedRiemannianManifold.sigmaCompact PointedRiemannianManifold.t2TangentBundle

/-- 两次放缩合并（`c = a·b`）。 -/
theorem scaleMetric_mul_eq_C11SP {M : Type*} [TopologicalSpace M] [ChartedSpace ThreeSpace M]
    [IsManifold ThreeModel ∞ M] (g : SmoothRiemannianMetric ThreeModel M) {a b c : ℝ}
    (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (habc : c = a * b) :
    scaleMetric c hc g = scaleMetric a ha (scaleMetric b hb g) := by
  apply SmoothRiemannianMetric.ext_inner
  intro z v w
  simp only [scaleMetric_inner]
  rw [habc]
  ring

/-- 前缀和严格递增子列：`N m ≤ η n`（`m ≤ n`）。 -/
theorem exists_strictMono_ge_prefix_C11SP (N : ℕ → ℕ) :
    ∃ η : ℕ → ℕ, StrictMono η ∧ ∀ m n, m ≤ n → N m ≤ η n := by
  let η : ℕ → ℕ := fun n => n + ∑ m ∈ Finset.range (n + 1), N m
  have hη : StrictMono η := strictMono_nat_of_lt_succ fun n => by
    change n + ∑ m ∈ Finset.range (n + 1), N m < n + 1 + ∑ m ∈ Finset.range (n + 1 + 1), N m
    rw [Finset.sum_range_succ _ (n + 1)]
    omega
  refine ⟨η, hη, fun m n hmn => ?_⟩
  have h1 : N m ≤ ∑ i ∈ Finset.range (n + 1), N i :=
    Finset.single_le_sum (f := N) (fun _ _ => Nat.zero_le _)
      (Finset.mem_range.mpr (Nat.lt_succ_of_le hmn))
  change N m ≤ n + ∑ i ∈ Finset.range (n + 1), N i
  omega

/-- G4 kernel：二次序列（m 索引）的 traced regions + canonical witness + 第一层比较数据 ⇒
二次 limit `P₂`（base scalar 1）上的反向非负 flow 与 end 比较（P6L:444 结论史无关形）。 -/
theorem secondBlowup_flow_of_traced_C11SP
    {P : OrientedThreeStage.{u}} {g : P.Metric}
    {pBase : CutoffParameters} {Γ : ClosedBirthConstants}
    (chain : PreparedSpatialChain pBase Γ P g) (F : GC.Interface.RawSurgery P g)
    (hTower : F.tower = chain.tower) (θ K0 : ℝ) (hθ : 0 < θ) (hK0 : 0 < K0)
    (ε C1 C2 : ℝ)
    (idx : ℕ → ℕ)
    (t : ∀ n, Icc (0 : ℝ) (F.tower.history (idx n)).toHistory.horizon)
    (y : ∀ n, ((F.tower.history (idx n)).toHistory.stageAt (t n)).Carrier)
    (R : ℕ → ℝ) (hR : ∀ n, 0 < R n)
    (hRy : ∀ n, metricScalarAt ((F.tower.history (idx n)).toHistory.stageMetric
      ((F.tower.history (idx n)).toHistory.activeStage (t n)) (t n)) (y n) = R n)
    (htrace : ∀ n, (F.tower.history (idx n)).toHistory.isTracedRegion (t n) (y n)
      (Real.sqrt (R n))⁻¹ (θ / R n) (K0 * R n))
    (hage : Tendsto (fun n => (t n : ℝ) * R n) atTop atTop)
    (hcan : ∀ᶠ n in atTop,
      ∃ Wc : SpatialCanonicalWitness ((F.tower.history (idx n)).toHistory.stageMetric
          ((F.tower.history (idx n)).toHistory.activeStage (t n)) (t n)) ε C1 C2 (y n),
        Wc.capTubeHasNeckChart ε ∧ ∃ z ∈ connectedComponent (y n),
          C2 * metricScalarAt ((F.tower.history (idx n)).toHistory.stageMetric
            ((F.tower.history (idx n)).toHistory.activeStage (t n)) (t n)) z <
          metricScalarAt ((F.tower.history (idx n)).toHistory.stageMetric
            ((F.tower.history (idx n)).toHistory.activeStage (t n)) (t n)) (y n))
    (Pl : PointedRiemannianManifold.{u, 0, 0} ThreeModel) (W : TopologicalSpace.Opens Pl.M)
    (xW : ℕ → W) (qc : ℕ → ℝ) (hqc : ∀ n, 0 < qc n)
    (hratio : Tendsto (fun n => qc n / metricScalarAt Pl.metric (xW n : Pl.M)) atTop (𝓝 1))
    (B : ∀ n, PartialDiffeomorph ThreeModel ThreeModel W
      ((F.tower.history (idx n)).toHistory.stageAt (t n)).Carrier ∞)
    {R₀ : ℝ} (hR₀ : 0 < R₀)
    (hBsource : ∀ n, riemannianClosedBallOf (scaleMetric (qc n) (hqc n)
      (Pl.metric.restrictOpen W)) (xW n) R₀ ⊆ (B n).source)
    (hBbase : ∀ n, B n (xW n) = y n)
    (hcapture : ∀ n, riemannianClosedBallOf (scaleMetric (R n) (hR n)
        ((F.tower.history (idx n)).toHistory.stageMetric
          ((F.tower.history (idx n)).toHistory.activeStage (t n)) (t n)))
        (y n) (R₀ / 4) ⊆ (B n) '' riemannianClosedBallOf (scaleMetric (qc n) (hqc n)
          (Pl.metric.restrictOpen W)) (xW n) R₀)
    (hBconv : ∀ eta : ℝ, 0 < eta → ∀ᶠ n in atTop,
      ∀ z ∈ riemannianClosedBallOf (scaleMetric (qc n) (hqc n) (Pl.metric.restrictOpen W))
        (xW n) R₀, ∀ w : TangentSpace ThreeModel z,
        (1 - eta) * (scaleMetric (qc n) (hqc n) (Pl.metric.restrictOpen W)).inner z w w ≤
          (scaleMetric (R n) (hR n)
            ((F.tower.history (idx n)).toHistory.stageMetric
              ((F.tower.history (idx n)).toHistory.activeStage (t n)) (t n))).inner
          (B n z) (mfderiv ThreeModel ThreeModel (B n) z w)
          (mfderiv ThreeModel ThreeModel (B n) z w) ∧
        (scaleMetric (R n) (hR n)
            ((F.tower.history (idx n)).toHistory.stageMetric
              ((F.tower.history (idx n)).toHistory.activeStage (t n)) (t n))).inner
          (B n z) (mfderiv ThreeModel ThreeModel (B n) z w)
          (mfderiv ThreeModel ThreeModel (B n) z w) ≤
            (1 + eta) * (scaleMetric (qc n) (hqc n) (Pl.metric.restrictOpen W)).inner z w w) :
    ∃ (j : ℕ → ℕ) (_ : StrictMono j) (A₂ : ℕ → ℝ) (hA₂ : ∀ n, 0 < A₂ n),
      Tendsto (fun n => A₂ n / metricScalarAt Pl.metric (xW (j n) : Pl.M)) atTop (𝓝 1) ∧
      ∃ (P₂ : PointedRiemannianManifold.{u, 0, 0} ThreeModel)
        (V : TopologicalSpace.Opens P₂.M)
        (hp : P₂.basepoint ∈ V) (_ : PathConnectedSpace V) (tau : ℝ) (htau : 0 < tau)
        (gV : ℝ → SmoothRiemannianMetric ThreeModel V),
        gV 0 = P₂.metric.restrictOpen V ∧
        IsSolutionOn ({ base.metric := gV } : SolutionOn (I := ThreeModel) (M := V)
          (RealTimeInterval.closed (-tau) 0 (by linarith))) ∧
        (∀ s ∈ Icc (-tau) 0, ∀ z : V, metricAlgebraicCurvatureTensorAt (gV s) z ∈
          algebraicCurvatureOperatorNonnegativeCone (I := ThreeModel)) ∧
        metricScalarAt P₂.metric P₂.basepoint = 1 ∧
        ∃ C : ℕ → PartialDiffeomorph ThreeModel ThreeModel V W ∞,
          (∀ n, C n ⟨P₂.basepoint, hp⟩ = xW (j n)) ∧
          ∃ r : ℝ, 0 < r ∧ IsCompact (riemannianClosedBallOf (gV 0) ⟨P₂.basepoint, hp⟩ r) ∧
          (∀ᶠ n in atTop,
            riemannianClosedBallOf (gV 0) ⟨P₂.basepoint, hp⟩ r ⊆ (C n).source ∧
            riemannianClosedBallOf (scaleMetric (A₂ n) (hA₂ n) (Pl.metric.restrictOpen W))
              (xW (j n)) (r / 4) ⊆
                (C n) '' riemannianClosedBallOf (gV 0) ⟨P₂.basepoint, hp⟩ r) ∧
          ∀ eta : ℝ, 0 < eta → ∀ᶠ n in atTop,
            ∀ a ∈ riemannianClosedBallOf (gV 0) ⟨P₂.basepoint, hp⟩ r,
            ∀ b ∈ riemannianClosedBallOf (gV 0) ⟨P₂.basepoint, hp⟩ r,
              |(riemannianEDistOf
                  (scaleMetric (A₂ n) (hA₂ n) (Pl.metric.restrictOpen W))
                  (C n a) (C n b)).toReal -
                (riemannianEDistOf (gV 0) a b).toReal| < eta := by
  have hjets : ∀ Rr : ℝ, 0 < Rr → Rr < 1 → ∀ k : ℕ, ∃ J : ℝ, 0 ≤ J ∧
      ∀ᶠ n in atTop, HasLocalCurvDerivBound
        ({ M := ((F.tower.history (idx n)).toHistory.stageAt (t n)).Carrier
           basepoint := y n
           metric := scaleMetric (R n) (hR n)
            ((F.tower.history (idx n)).toHistory.stageMetric
              ((F.tower.history (idx n)).toHistory.activeStage (t n)) (t n)) } :
          PointedRiemannianManifold.{u, 0, 0} ThreeModel) (y n) Rr k J := by
    intro Rr hRr hRr1 k
    obtain ⟨J, hJ, hin⟩ := exists_inner_jets_of_traced_region_CXSP Rr 1 θ K0 hRr.le hRr1 hθ hK0
    refine ⟨J k, zero_le_one.trans (hJ k), Eventually.of_forall fun n => ?_⟩
    have htr : (F.tower.history (idx n)).toHistory.isTracedRegion (t n) (y n)
        (1 / Real.sqrt (R n)) (θ / R n) (K0 * R n) := by
      rw [one_div]
      exact htrace n
    intro w hw
    exact hin _ (t n) (y n) (R n) (hR n) htr k w hw
  have hconv := exists_stage_pointed_convergence_of_jets_CXSP
    (fun n => (F.tower.history (idx n)).toHistory.stageAt (t n))
    (fun n => (F.tower.history (idx n)).toHistory.stageMetric
      ((F.tower.history (idx n)).toHistory.activeStage (t n)) (t n))
    R hR y ε C1 C2 one_pos hcan hjets
  obtain ⟨j, hj, _rad, _hrad, _hradlim, P₂, maps2, M2, hcan2, _hradial2, _hcompact2,
    _hcapture2, _hmetric2⟩ := hconv
  have hscalarOne : metricScalarAt P₂.metric P₂.basepoint = 1 :=
    Perelman.KappaSolutions.pointedScalar_base_eq_of_metricCG_canonical_domains M2 hcan2 (by
      intro n
      change metricScalarAt (scaleMetric (R (j n)) (hR (j n))
        ((F.tower.history (idx (j n))).toHistory.stageMetric
          ((F.tower.history (idx (j n))).toHistory.activeStage (t (j n))) (t (j n))))
          (y (j n)) = 1
      rw [metricScalarAt_scaleMetric, hRy (j n), inv_mul_cancel₀ (hR (j n)).ne'])
  obtain ⟨V, hp, hpath, _hcptV, N₀, _hsrc, G, hG0, hsol, hnn, C, hC, r, hr, hcpt, hcap,
      hdist⟩ :=
    guard_stageLocalFlow_endComparison_C11SP chain F hTower θ K0 hθ hK0 idx t y R hR htrace
      hage j hj P₂ _ M2 hcan2
      (fun n => scaleMetric (qc (j n)) (hqc (j n)) (Pl.metric.restrictOpen W))
      (fun n => xW (j n)) (fun n => B (j n)) hR₀ (fun n => hBsource (j n))
      (fun n => hBbase (j n)) (fun n => hcapture (j n))
      (fun eta heta => hj.tendsto_atTop.eventually (hBconv eta heta))
  have hjN : StrictMono (fun n => j (n + N₀)) :=
    hj.comp fun a b hab => Nat.add_lt_add_right hab N₀
  refine ⟨fun n => j (n + N₀), hjN, fun n => qc (j (n + N₀)), fun n => hqc (j (n + N₀)),
    hratio.comp hjN.tendsto_atTop, P₂, V, hp, hpath, θ / 2, half_pos hθ, G, hG0, hsol, hnn,
    hscalarOne, C, hC, r, hr, hcpt, hcap, hdist⟩


/-- G4 装配：G64 行付款（`hpay`）+ G50 seed 尾段 + 前缀和 `η` + ScalarRescaling ⇒ 二次序列的
traced / canonical / 比较数据，喂 `secondBlowup_flow_of_traced_C11SP`；`xW` 先平移 `N`。 -/
theorem secondBlowup_assemble_C11SP
    {P : OrientedThreeStage.{u}} {g : P.Metric}
    {pBase : CutoffParameters} {Γf : ClosedBirthConstants} {ε C1 C2 : ℝ} {Ctime : ℝ≥0}
    (S : PreparedSpatialChain pBase Γf P g) (F : GC.Interface.RawSurgery P g)
    (hTower : F.tower = S.tower) (hb : CanonicalLateTimeCore_P6X F ε C1 C2 Ctime)
    (A : ℝ) (hA : 0 < A) (Hbase : ℝ) (hHpos : 0 < Hbase) (rho : ℝ)
    (hrhoH : rho / Real.sqrt Hbase ≤ A + 1 / 2)
    (idx : ℕ → ℕ)
    (t : ∀ i, Icc (0 : ℝ) (F.tower.history (idx i)).toHistory.horizon)
    (p anchor : ∀ i, ((F.tower.history (idx i)).toHistory.stageAt (t i)).Carrier)
    (r : ℕ → ℝ) (hr : ∀ i, 0 < r i)
    (htlim : Tendsto (fun i => (t i : ℝ)) atTop atTop)
    (htime : ∀ i, 2 * r i ^ 2 < (t i : ℝ))
    (hsmall : ∀ i, hasSmallParabolicCurvature (F.tower.history (idx i)).toHistory (t i) (p i)
      (r i))
    (hvolF : ∀ i, ENNReal.ofReal ((2 * A + 3)⁻¹ * r i ^ 3) ≤
      ballVolume ((F.tower.history (idx i)).toHistory.stageMetric
        ((F.tower.history (idx i)).toHistory.activeStage (t i)) (t i)) (p i) (r i))
    (hanchor : ∀ i, riemannianEDistOf ((F.tower.history (idx i)).toHistory.stageMetric
        ((F.tower.history (idx i)).toHistory.activeStage (t i)) (t i)) (p i) (anchor i) ≤
      ENNReal.ofReal (A * r i))
    (Q : ℕ → ℝ) (hQ : ∀ i, 0 < Q i) (hQeq : ∀ i, Q i = Hbase * (r i ^ 2)⁻¹)
    (f : ℕ → ℕ) (hf : StrictMono f)
    (Pl : PointedRiemannianManifold.{u, 0, 0} ThreeModel)
    (Phi : PointedRiemannianConvergenceMaps
      ({ obj := fun i =>
          { M := ((F.tower.history (idx i)).toHistory.stageAt (t i)).Carrier
            basepoint := anchor i
            metric := scaleMetric (Q i) (hQ i)
              ((F.tower.history (idx i)).toHistory.stageMetric
                ((F.tower.history (idx i)).toHistory.activeStage (t i)) (t i)) } } :
        PointedRiemannianSeq.{u, 0, 0} ThreeModel) Pl f)
    (M : MetricConvergenceData Phi)
    (hcanonical : ∀ n, M.domain n = CanonicalMetricCompactness.canonicalSourceData Phi n)
    (hradial : ∀ y : Pl.M, riemannianEDistOf Pl.metric Pl.basepoint y < ENNReal.ofReal rho)
    (W : TopologicalSpace.Opens Pl.M) (xW : ℕ → W) (R₀ : ℝ) (hR₀ : 0 < R₀)
    (hQW : ∀ n, 2 ≤ metricScalarAt Pl.metric (xW n : Pl.M))
    (hQWlim : Tendsto (fun n => metricScalarAt Pl.metric (xW n : Pl.M)) atTop atTop)
    (hcompactW : ∀ n, IsCompact (riemannianClosedBallOf (Pl.metric.restrictOpen W) (xW n)
      (4 * R₀ / Real.sqrt (metricScalarAt Pl.metric (xW n : Pl.M)))))
    (N : ℕ) (θ K0 : ℝ) (hθ : 0 < θ) (hK0 : 0 < K0) (ψ : ℕ → ℕ) (hψ : StrictMono ψ)
    (hpay : ∀ k : ℕ → ℕ, StrictMono k → ∀ m : ℕ,
      0 < metricScalarAt ((F.tower.history (idx (f (ψ (k m))))).toHistory.stageMetric
          ((F.tower.history (idx (f (ψ (k m))))).toHistory.activeStage (t (f (ψ (k m)))))
          (t (f (ψ (k m))))) (Phi.map (ψ (k m)) (xW (m + N) : Pl.M)) ∧
      (F.tower.history (idx (f (ψ (k m))))).toHistory.isTracedRegion (t (f (ψ (k m))))
        (Phi.map (ψ (k m)) (xW (m + N) : Pl.M))
        (Real.sqrt (metricScalarAt ((F.tower.history (idx (f (ψ (k m))))).toHistory.stageMetric
          ((F.tower.history (idx (f (ψ (k m))))).toHistory.activeStage (t (f (ψ (k m)))))
          (t (f (ψ (k m))))) (Phi.map (ψ (k m)) (xW (m + N) : Pl.M))))⁻¹
        (θ / metricScalarAt ((F.tower.history (idx (f (ψ (k m))))).toHistory.stageMetric
          ((F.tower.history (idx (f (ψ (k m))))).toHistory.activeStage (t (f (ψ (k m)))))
          (t (f (ψ (k m))))) (Phi.map (ψ (k m)) (xW (m + N) : Pl.M)))
        (K0 * metricScalarAt ((F.tower.history (idx (f (ψ (k m))))).toHistory.stageMetric
          ((F.tower.history (idx (f (ψ (k m))))).toHistory.activeStage (t (f (ψ (k m)))))
          (t (f (ψ (k m))))) (Phi.map (ψ (k m)) (xW (m + N) : Pl.M)))) :
    ∃ (j : ℕ → ℕ) (_ : StrictMono j) (A₂ : ℕ → ℝ) (hA₂ : ∀ n, 0 < A₂ n),
      Tendsto (fun n => A₂ n / metricScalarAt Pl.metric (xW (j n) : Pl.M)) atTop (𝓝 1) ∧
      ∃ (P₂ : PointedRiemannianManifold.{u, 0, 0} ThreeModel)
        (V : TopologicalSpace.Opens P₂.M)
        (hp : P₂.basepoint ∈ V) (_ : PathConnectedSpace V) (tau : ℝ) (htau : 0 < tau)
        (gV : ℝ → SmoothRiemannianMetric ThreeModel V),
        gV 0 = P₂.metric.restrictOpen V ∧
        IsSolutionOn ({ base.metric := gV } : SolutionOn (I := ThreeModel) (M := V)
          (RealTimeInterval.closed (-tau) 0 (by linarith))) ∧
        (∀ s ∈ Icc (-tau) 0, ∀ z : V, metricAlgebraicCurvatureTensorAt (gV s) z ∈
          algebraicCurvatureOperatorNonnegativeCone (I := ThreeModel)) ∧
        metricScalarAt P₂.metric P₂.basepoint = 1 ∧
        ∃ C : ℕ → PartialDiffeomorph ThreeModel ThreeModel V W ∞,
          (∀ n, C n ⟨P₂.basepoint, hp⟩ = xW (j n)) ∧
          ∃ r : ℝ, 0 < r ∧ IsCompact (riemannianClosedBallOf (gV 0) ⟨P₂.basepoint, hp⟩ r) ∧
          (∀ᶠ n in atTop,
            riemannianClosedBallOf (gV 0) ⟨P₂.basepoint, hp⟩ r ⊆ (C n).source ∧
            riemannianClosedBallOf (scaleMetric (A₂ n) (hA₂ n) (Pl.metric.restrictOpen W))
              (xW (j n)) (r / 4) ⊆
                (C n) '' riemannianClosedBallOf (gV 0) ⟨P₂.basepoint, hp⟩ r) ∧
          ∀ eta : ℝ, 0 < eta → ∀ᶠ n in atTop,
            ∀ a ∈ riemannianClosedBallOf (gV 0) ⟨P₂.basepoint, hp⟩ r,
            ∀ b ∈ riemannianClosedBallOf (gV 0) ⟨P₂.basepoint, hp⟩ r,
              |(riemannianEDistOf
                  (scaleMetric (A₂ n) (hA₂ n) (Pl.metric.restrictOpen W))
                  (C n a) (C n b)).toReal -
                (riemannianEDistOf (gV 0) a b).toReal| < eta := by
  obtain ⟨Kb, Tb, _hKb, _hTb, hcanTC⟩ := hb (2 * A + 3) (by linarith only [hA])
  have htail : ∀ m, ∀ᶠ n in atTop,
      riemannianEDistOf ((F.tower.history (idx (f n))).toHistory.stageMetric
        ((F.tower.history (idx (f n))).toHistory.activeStage (t (f n))) (t (f n)))
        (p (f n)) (Phi.map n (xW (m + N) : Pl.M)) ≤
      ENNReal.ofReal ((A + rho / Real.sqrt Hbase) * r (f n)) := fun m =>
    eventually_stage_pointed_seed_distance_CXSP
      (fun i => (F.tower.history (idx i)).toHistory.stageAt (t i))
      (fun i => (F.tower.history (idx i)).toHistory.stageMetric
        ((F.tower.history (idx i)).toHistory.activeStage (t i)) (t i))
      Q hQ anchor Pl Phi M hcanonical p r hr hHpos hA.le hQeq hanchor _ (hradial _)
  choose Nm hNm using fun m => eventually_atTop.mp (hψ.tendsto_atTop.eventually (htail m))
  obtain ⟨η, hη, hηN⟩ := exists_strictMono_ge_prefix_C11SP Nm
  have hδ : StrictMono (fun n => ψ (η n)) := hψ.comp hη
  have hcan' : ∀ n, (M.compSubseq (fun n => ψ (η n)) hδ).domain n =
      CanonicalMetricCompactness.canonicalSourceData (Phi.compSubseq (fun n => ψ (η n)) hδ) n := by
    intro n
    change (M.domain (ψ (η n))).compSubseq (fun n => ψ (η n)) hδ n = _
    rw [hcanonical (ψ (η n))]
    rfl
  obtain ⟨k, hk, hq1, hratio, hcmp⟩ := exists_scalar_rescaled_source_comparison _ _ Pl
    (Phi.compSubseq (fun n => ψ (η n)) hδ) (M.compSubseq (fun n => ψ (η n)) hδ) hcan' W
    (fun m => xW (m + N)) hR₀ (fun m => hQW (m + N)) (fun m => hcompactW (m + N))
  have hpay' := fun m => hpay (fun n => η (k n)) (hη.comp hk) m
  have hiMono : StrictMono (fun m => f (ψ (η (k m)))) := hf.comp (hδ.comp hk)
  let iF : ℕ → ℕ := fun m => f (ψ (η (k m)))
  let gS : ∀ m, ((F.tower.history (idx (iF m))).toHistory.stageAt (t (iF m))).Metric :=
    fun m => (F.tower.history (idx (iF m))).toHistory.stageMetric
      ((F.tower.history (idx (iF m))).toHistory.activeStage (t (iF m))) (t (iF m))
  let yF : ∀ m, ((F.tower.history (idx (iF m))).toHistory.stageAt (t (iF m))).Carrier :=
    fun m => Phi.map (ψ (η (k m))) (xW (m + N) : Pl.M)
  let R₂ : ℕ → ℝ := fun m => metricScalarAt (gS m) (yF m)
  let qc : ℕ → ℝ := fun m => metricScalarAt (scaleMetric (Q (iF m)) (hQ (iF m)) (gS m)) (yF m)
  have hR₂ : ∀ m, 0 < R₂ m := fun m => (hpay' m).1
  have hqc : ∀ m, 0 < qc m := fun m => lt_of_lt_of_le zero_lt_one (hq1 m)
  have hReq : ∀ m, R₂ m = qc m * Q (iF m) := by
    intro m
    change metricScalarAt (gS m) (yF m) =
      metricScalarAt (scaleMetric (Q (iF m)) (hQ (iF m)) (gS m)) (yF m) * Q (iF m)
    rw [metricScalarAt_scaleMetric, inv_mul_eq_div, div_mul_cancel₀ _ (hQ (iF m)).ne']
  have hmeq : ∀ m, scaleMetric (R₂ m) (hR₂ m) (gS m) =
      scaleMetric (qc m) (hqc m) (scaleMetric (Q (iF m)) (hQ (iF m)) (gS m)) := fun m =>
    scaleMetric_mul_eq_C11SP (gS m) (hqc m) (hQ (iF m)) (hR₂ m) (hReq m)
  have hQWN : Tendsto (fun m => metricScalarAt Pl.metric (xW (m + N) : Pl.M)) atTop atTop :=
    hQWlim.comp (tendsto_add_atTop_nat N)
  have hratio' : Tendsto (fun m => qc m / metricScalarAt Pl.metric (xW (m + N) : Pl.M))
      atTop (𝓝 1) := hratio
  have hqtop : Tendsto qc atTop atTop := by
    have hhalf : ∀ᶠ m in atTop,
        (1 / 2 : ℝ) < qc m / metricScalarAt Pl.metric (xW (m + N) : Pl.M) :=
      hratio'.eventually (eventually_gt_nhds (by norm_num))
    apply tendsto_atTop_mono' atTop _ (hQWN.atTop_div_const (by norm_num : (0 : ℝ) < 2))
    filter_upwards [hhalf] with m hm
    have hRp : 0 < metricScalarAt Pl.metric (xW (m + N) : Pl.M) := by
      linarith only [hQW (m + N)]
    have h := (lt_div_iff₀ hRp).mp hm
    linarith only [h]
  have htQ : ∀ i, 2 * Hbase ≤ (t i : ℝ) * Q i := by
    intro i
    have hr2 : 0 < r i ^ 2 := pow_pos (hr i) 2
    have h1 : 2 ≤ (t i : ℝ) * (r i ^ 2)⁻¹ := by
      rw [le_mul_inv_iff₀ hr2]
      linarith only [htime i]
    rw [hQeq i]
    calc 2 * Hbase = Hbase * 2 := by ring
      _ ≤ Hbase * ((t i : ℝ) * (r i ^ 2)⁻¹) := mul_le_mul_of_nonneg_left h1 hHpos.le
      _ = (t i : ℝ) * (Hbase * (r i ^ 2)⁻¹) := by ring
  have hage : Tendsto (fun m => (t (iF m) : ℝ) * R₂ m) atTop atTop := by
    apply tendsto_atTop_mono' atTop _ (hqtop.const_mul_atTop (by linarith only [hHpos] :
      (0 : ℝ) < 2 * Hbase))
    refine Eventually.of_forall fun m => ?_
    change 2 * Hbase * qc m ≤ (t (iF m) : ℝ) * R₂ m
    rw [hReq m]
    have h1 := htQ (iF m)
    have h2 := hq1 m
    have h3 : 0 ≤ qc m := (hqc m).le
    calc 2 * Hbase * qc m ≤ (t (iF m) : ℝ) * Q (iF m) * qc m :=
          mul_le_mul_of_nonneg_right h1 h3
      _ = (t (iF m) : ℝ) * (qc m * Q (iF m)) := by ring
  have hiT : Tendsto (fun m => (t (iF m) : ℝ)) atTop atTop :=
    htlim.comp hiMono.tendsto_atTop
  have hcan : ∀ᶠ m in atTop,
      ∃ Wc : SpatialCanonicalWitness (gS m) ε C1 C2 (yF m),
        Wc.capTubeHasNeckChart ε ∧ ∃ z ∈ connectedComponent (yF m),
          C2 * metricScalarAt (gS m) z < metricScalarAt (gS m) (yF m) := by
    filter_upwards [hiT.eventually_ge_atTop Tb,
      hqtop.eventually_ge_atTop (max Kb (4 * max C2 1) / Hbase)] with m hT hq
    have hyball : yF m ∈ riemannianBallOf (gS m) (p (iF m)) ((2 * A + 3) * r (iF m)) := by
      apply (hNm m (η (k m)) (hηN m (k m) (hk.id_le m))).trans_lt
      apply (ENNReal.ofReal_lt_ofReal_iff (mul_pos (by linarith only [hA]) (hr _))).mpr
      apply mul_lt_mul_of_pos_right _ (hr _)
      linarith only [hrhoH, hA]
    have hhigh : max Kb (4 * max C2 1) * (r (iF m) ^ 2)⁻¹ ≤
        metricScalarAt (gS m) (yF m) := by
      change _ ≤ R₂ m
      rw [hReq m, hQeq (iF m)]
      have h := (div_le_iff₀ hHpos).mp hq
      have hi : 0 ≤ (r (iF m) ^ 2)⁻¹ := by positivity
      calc max Kb (4 * max C2 1) * (r (iF m) ^ 2)⁻¹ ≤ (qc m * Hbase) * (r (iF m) ^ 2)⁻¹ :=
            mul_le_mul_of_nonneg_right h hi
        _ = qc m * (Hbase * (r (iF m) ^ 2)⁻¹) := by ring
    obtain ⟨Wc, hchart, hpcomp, hgap⟩ := exists_seed_volume_base_CXSP (hsmall (iF m)) hyball
      hhigh (fun z hz hzR => (hcanTC (idx (iF m)) (t (iF m)) (p (iF m)) (r (iF m)) hT
        (htime _) (hsmall _) (hvolF _) z hz hzR).1)
    exact ⟨Wc, hchart, p (iF m), hpcomp, hgap⟩
  let Bk : ∀ m, PartialDiffeomorph ThreeModel ThreeModel W
      ((F.tower.history (idx (iF m))).toHistory.stageAt (t (iF m))).Carrier ∞ :=
    fun m => (DifferentialGeometry.Topology.PartialDiffeomorph.subtypeVal (I := ThreeModel) W
      ⟨xW (0 + N)⟩).trans ((Phi.compSubseq (fun n => ψ (η n)) hδ).partialDiffeomorph (k m))
  have hlim : Tendsto (fun n : ℕ => 1 / ((n : ℝ) + 2)) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop
      (tendsto_atTop_add_const_right atTop 2 tendsto_natCast_atTop_atTop)
  obtain ⟨j, hj, A₂, hA₂, hrat, P₂, V, hp, hpath, tau, htau, gV, h1, h2, h3, h4, C, hC, rr, hrr,
      h5, h6, h7⟩ :=
    secondBlowup_flow_of_traced_C11SP S F hTower θ K0 hθ hK0 ε C1 C2
      (fun m => idx (iF m)) (fun m => t (iF m)) yF R₂ hR₂ (fun _ => rfl)
      (fun m => (hpay' m).2) hage hcan Pl W (fun m => xW (m + N)) qc hqc hratio' Bk hR₀
      (fun m => (hcmp m).2.1) (fun _ => rfl)
      (fun m => by
        rw [hmeq m]
        exact (hcmp m).2.2.2.1)
      (fun eta heta => by
        filter_upwards [hlim.eventually (eventually_lt_nhds heta)] with m hm
        intro z hz w
        rw [hmeq m]
        have hh := (hcmp m).2.2.1 z hz w
        have hg := metric_inner_self_nonneg
          (scaleMetric (qc m) (hqc m) (Pl.metric.restrictOpen W)) z w
        exact ⟨(mul_le_mul_of_nonneg_right (by linarith only [hm]) hg).trans hh.1,
          hh.2.trans (mul_le_mul_of_nonneg_right (by linarith only [hm]) hg)⟩)
  exact ⟨fun n => j n + N, fun a b hab => Nat.add_lt_add_right (hj hab) N, A₂, hA₂, hrat, P₂, V,
    hp, hpath, tau, htau, gV, h1, h2, h3, h4, C, hC, rr, hrr, h5, h6, h7⟩


/-- **SPINE-A1 G4**（(A-2)）：第一层 guard 数据（G60 证明体内的 anchor 子列、`Q = Hbase/r²`、
到 `Pl` 的 canonical convergence）⇒ `Pl` 中任意高曲率点列 `xW` 处的二次 blow-up 反向极限
（P6L:444 结论史无关形 = SPINE-A2 `hflowA1` per-Pl clause）。`ε₁` = G64 的 `ε₀`，在 S / A 之前。 -/
theorem guard_secondBlowupFlow_C11SP
    (P : OrientedThreeStage.{u}) (g : P.Metric) :
    ∃ ε₁ : ℝ, 0 < ε₁ ∧
      ∀ {pBase : CutoffParameters} {Γf : ClosedBirthConstants}
        {ε C1 C2 : ℝ} {Ctime : ℝ≥0}
        (S : PreparedSpatialChain pBase Γf P g) (F : GC.Interface.RawSurgery P g)
        (q : CutoffParameters), F.tower = S.tower →
        (∀ t : ℝ, 0 ≤ t → q.delta t = (chainDiagonal_C11A S).delta t ∧
          q.neckRadius t = (chainDiagonal_C11A S).neckRadius t) →
        pBase.modelAccuracy ≤ ε₁ → capWindowRadius_C11E + 1 ≤ pBase.modelRadius →
        2 ≤ pBase.modelOrder → CanonicalLateTimeCore_P6X F ε C1 C2 Ctime →
      ∀ A : ℝ, 0 < A → ∀ Hbase : ℝ, 4 ≤ Hbase → ∀ rho : ℝ, 0 < rho →
        rho + 2 ≤ A * Real.sqrt Hbase + 3 →
      ∀ (idx : ℕ → ℕ)
        (t : ∀ i, Icc (0 : ℝ) (F.tower.history (idx i)).toHistory.horizon)
        (p anchor : ∀ i, ((F.tower.history (idx i)).toHistory.stageAt (t i)).Carrier)
        (r : ℕ → ℝ), (∀ i, 0 < r i) →
        Tendsto (fun i => (t i : ℝ)) atTop atTop →
        (∀ i, 2 * r i ^ 2 < (t i : ℝ)) →
        (∀ i, hasSmallParabolicCurvature (F.tower.history (idx i)).toHistory (t i) (p i) (r i)) →
        (∀ i, ENNReal.ofReal (A⁻¹ * r i ^ 3) ≤
          ballVolume ((F.tower.history (idx i)).toHistory.stageMetric
            ((F.tower.history (idx i)).toHistory.activeStage (t i)) (t i)) (p i) (r i)) →
        (∀ i, q.neckRadius (t i) ≤ r i) →
        (∀ i, riemannianEDistOf ((F.tower.history (idx i)).toHistory.stageMetric
            ((F.tower.history (idx i)).toHistory.activeStage (t i)) (t i)) (p i) (anchor i) ≤
          ENNReal.ofReal (A * r i)) →
      ∀ (Q : ℕ → ℝ) (hQ : ∀ i, 0 < Q i), (∀ i, Q i = Hbase * (r i ^ 2)⁻¹) →
      ∀ (f : ℕ → ℕ), StrictMono f →
      ∀ (Pl : PointedRiemannianManifold.{u, 0, 0} ThreeModel)
        (Phi : PointedRiemannianConvergenceMaps
          ({ obj := fun i =>
              { M := ((F.tower.history (idx i)).toHistory.stageAt (t i)).Carrier
                basepoint := anchor i
                metric := scaleMetric (Q i) (hQ i)
                  ((F.tower.history (idx i)).toHistory.stageMetric
                    ((F.tower.history (idx i)).toHistory.activeStage (t i)) (t i)) } } :
            PointedRiemannianSeq.{u, 0, 0} ThreeModel) Pl f)
        (M : MetricConvergenceData Phi),
        (∀ n, M.domain n = CanonicalMetricCompactness.canonicalSourceData Phi n) →
        (∀ y : Pl.M, riemannianEDistOf Pl.metric Pl.basepoint y < ENNReal.ofReal rho) →
      ∀ W : TopologicalSpace.Opens Pl.M,
      ∀ (xW : ℕ → W) (R₀ : ℝ), 0 < R₀ →
        (∀ n, 2 ≤ metricScalarAt Pl.metric (xW n : Pl.M)) →
        Tendsto (fun n => metricScalarAt Pl.metric (xW n : Pl.M)) atTop atTop →
        (∀ n, IsCompact (riemannianClosedBallOf (Pl.metric.restrictOpen W) (xW n)
          (4 * R₀ / Real.sqrt (metricScalarAt Pl.metric (xW n : Pl.M))))) →
        ∃ (j : ℕ → ℕ) (_ : StrictMono j) (A₂ : ℕ → ℝ) (hA₂ : ∀ n, 0 < A₂ n),
          Tendsto (fun n => A₂ n / metricScalarAt Pl.metric (xW (j n) : Pl.M)) atTop (𝓝 1) ∧
          ∃ (P₂ : PointedRiemannianManifold.{u, 0, 0} ThreeModel)
            (V : TopologicalSpace.Opens P₂.M)
            (hp : P₂.basepoint ∈ V) (_ : PathConnectedSpace V) (tau : ℝ) (htau : 0 < tau)
            (g : ℝ → SmoothRiemannianMetric ThreeModel V),
            g 0 = P₂.metric.restrictOpen V ∧
            IsSolutionOn ({ base.metric := g } : SolutionOn (I := ThreeModel) (M := V)
              (RealTimeInterval.closed (-tau) 0 (by linarith))) ∧
            (∀ t ∈ Icc (-tau) 0, ∀ y : V, metricAlgebraicCurvatureTensorAt (g t) y ∈
              algebraicCurvatureOperatorNonnegativeCone (I := ThreeModel)) ∧
            metricScalarAt P₂.metric P₂.basepoint = 1 ∧
            ∃ C : ℕ → PartialDiffeomorph ThreeModel ThreeModel V W ∞,
              (∀ n, C n ⟨P₂.basepoint, hp⟩ = xW (j n)) ∧
              ∃ r : ℝ, 0 < r ∧ IsCompact (riemannianClosedBallOf (g 0) ⟨P₂.basepoint, hp⟩ r) ∧
              (∀ᶠ n in atTop,
                riemannianClosedBallOf (g 0) ⟨P₂.basepoint, hp⟩ r ⊆ (C n).source ∧
                riemannianClosedBallOf (scaleMetric (A₂ n) (hA₂ n) (Pl.metric.restrictOpen W))
                  (xW (j n)) (r / 4) ⊆
                    (C n) '' riemannianClosedBallOf (g 0) ⟨P₂.basepoint, hp⟩ r) ∧
              ∀ eta : ℝ, 0 < eta → ∀ᶠ n in atTop,
                ∀ a ∈ riemannianClosedBallOf (g 0) ⟨P₂.basepoint, hp⟩ r,
                ∀ b ∈ riemannianClosedBallOf (g 0) ⟨P₂.basepoint, hp⟩ r,
                  |(riemannianEDistOf
                      (scaleMetric (A₂ n) (hA₂ n) (Pl.metric.restrictOpen W))
                      (C n a) (C n b)).toReal -
                    (riemannianEDistOf (g 0) a b).toReal| < eta := by
  obtain ⟨ε₀, hε₀, hG64⟩ := exists_prepared_time_triangular_mapped_jets_CXSP P g
  refine ⟨ε₀, hε₀, ?_⟩
  intro pBase Γf ε C1 C2 Ctime S F q hTower hdiag hacc hrad hord hb A hA Hbase hHbase rho hrho
    hrhoB idx t p anchor r hr htlim htime hsmall hvol hguard hanchor Q hQ hQeq f hf Pl Phi M
    hcanonical hradial W xW R₀ hR₀ hQW hQWlim hcompactW
  have hAfac : (1 : ℝ) < 2 * A + 3 := by linarith only [hA]
  obtain ⟨H0, L0, hH0, _hL0, hG64A⟩ :=
    hG64 S F q hTower hdiag hacc hrad hord hb (2 * A + 3) hAfac
  obtain ⟨θ, K0, _J, hθ, hK0, _hJ, hG64B⟩ :=
    hG64A (2 * A + 1) 1 1 (by linarith only [hA]) one_pos one_pos (by linarith only)
  have hH0pos : 0 < H0 := by linarith only [hH0]
  have hHpos : 0 < Hbase := by linarith only [hHbase]
  have hχ : 0 < Hbase / H0 := div_pos hHpos hH0pos
  have hχH0 : Hbase / H0 * H0 = Hbase := div_mul_cancel₀ Hbase hH0pos.ne'
  have hsqrtH : 2 ≤ Real.sqrt Hbase := by
    have h4 : Real.sqrt 4 = 2 := by
      rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]
    rw [← h4]
    exact Real.sqrt_le_sqrt hHbase
  have hsqrtH0 : 2 ≤ Real.sqrt H0 := by
    have h4 : Real.sqrt 4 = 2 := by
      rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]
    rw [← h4]
    exact Real.sqrt_le_sqrt hH0
  have hrhoH : rho / Real.sqrt Hbase ≤ A + 1 / 2 := by
    rw [div_le_iff₀ (by linarith only [hsqrtH])]
    nlinarith only [hrhoB, hsqrtH, hA]
  have hfit : A + rho / Real.sqrt (Hbase / H0 * H0) + 1 / Real.sqrt H0 ≤ 2 * A + 1 := by
    rw [hχH0]
    have h2 : 1 / Real.sqrt H0 ≤ 1 / 2 :=
      one_div_le_one_div_of_le (by norm_num) hsqrtH0
    linarith only [hrhoH, h2]
  have hscale' : ∀ i, Q i = (Hbase / H0 * H0) * (r i ^ 2)⁻¹ := fun i => by
    rw [hχH0]
    exact hQeq i
  have hvolF : ∀ i, ENNReal.ofReal ((2 * A + 3)⁻¹ * r i ^ 3) ≤
      ballVolume ((F.tower.history (idx i)).toHistory.stageMetric
        ((F.tower.history (idx i)).toHistory.activeStage (t i)) (t i)) (p i) (r i) :=
    fun i => seed_volume_of_parameter_le_CXSP (hsmall i) hA (by linarith only [hA]) (hvol i)
  obtain ⟨N, hN⟩ := eventually_atTop.mp (hQWlim.eventually_ge_atTop (L0 / (Hbase / H0)))
  have hlevel : ∀ m, L0 ≤ Hbase / H0 * metricScalarAt Pl.metric (xW (m + N) : Pl.M) := by
    intro m
    have h := hN (m + N) (Nat.le_add_left N m)
    rw [div_le_iff₀ hχ] at h
    linarith only [h]
  obtain ⟨ψ, hψ, _htri, hpay⟩ := hG64B (Hbase / H0) hχ rho A hrho hA.le hfit idx t p r hr htlim
    htime hsmall hvolF hguard anchor hanchor Q hQ hscale' f hf Pl Phi M hcanonical
    (fun m => (xW (m + N) : Pl.M)) (fun m => hradial _) hlevel
  exact secondBlowup_assemble_C11SP S F hTower hb A hA Hbase hHpos rho hrhoH idx t p anchor r hr
    htlim htime hsmall hvolF hanchor Q hQ hQeq f hf Pl Phi M hcanonical hradial W xW R₀ hR₀ hQW
    hQWlim hcompactW N θ K0 hθ hK0 ψ hψ
    (fun k hk m => ⟨(hpay k hk m).1, (hpay k hk m).2.1⟩)

end GC.LongTime.Ch11
