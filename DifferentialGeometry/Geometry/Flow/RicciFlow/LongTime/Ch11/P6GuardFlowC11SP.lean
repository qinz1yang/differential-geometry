import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.P6TracedWindowJetsCXSP
import DifferentialGeometry.Geometry.Flow.RicciFlow.Compactness.Limits.PointedLocalFlow
import DifferentialGeometry.Geometry.Compactness.CheegerGromov.Pointed.Convergence.Distance
import DifferentialGeometry.Geometry.Compactness.CheegerGromov.Pointed.Subsequence
import DifferentialGeometry.Geometry.Flow.RicciFlow.Solution.LocalPullback
import DifferentialGeometry.Topology.Manifold.LocalDiffeomorph.OpenCodRestrict
import DifferentialGeometry.Topology.Manifold.OpenSubtype

/-!
# SPINE-A1 G2：guard 分支 traced stage 序列在固定 V 上的反向非负 flow

CODEX-C §3.3 路线 2。完成 Codex WIP `exists_prepared_stage_local_flow_CXSP`
（`P6StageLocalFlowCXSP.lean`，attempt5 仍 `unknown free variable`，报在主定理头）。
修法：陈述去掉 `let H` / `let X`（全部 inline），每 n 的 window 数据先作独立 `have`，
再 `exact` 进固定 V kernel；kernel 照 WIP 私有 kernel 逐字（只去掉一处 `<;>`）。

输入 = 同一 prepared `F` 的 unit traced regions（半径 `(√R)⁻¹`、深度 `θ/R`、`Rm ≤ K R`）、
`t·R → ∞`、以 traced 中心为 basepoint 按 `R` 归一化的二次 metric convergence（canonical）。
G59 `exists_prepared_traced_window_pinching_and_jets_CXSP` 付同一 B 的 pinching 与后半窗
jets；`Λ = (a₀ + t − θ/R)·R ≥ t·R − θ → ∞`，不要求 R 本身发散。
本叶不消费 TimeCore / hw / Budget / SCRS⁺；不经 RegularSlice。
-/

set_option autoImplicit false

noncomputable section

open Set Filter DifferentialGeometry DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.CheegerGromovCompactness
open DifferentialGeometry.PDE.RicciFlow
open DifferentialGeometry.PDE.RicciFlow.Perelman
open DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
open GC.GeneralFlow
open scoped Manifold ContDiff Topology ENNReal

namespace GC.LongTime.Ch11

universe u

attribute [local instance] PointedRiemannianManifold.topology PointedRiemannianManifold.charted
  PointedRiemannianManifold.smooth PointedRiemannianManifold.t2
  PointedRiemannianManifold.sigmaCompact PointedRiemannianManifold.t2TangentBundle

/-- 固定 V kernel：unit window solutions 的 localPullback 在 Pl 的固定 basepoint 邻域 V 上
抽出非负曲率算子的反向 flow（与 history carrier 无关；照 `P6StageLocalFlowCXSP` 私有 kernel）。 -/
theorem exists_local_flow_of_unit_windows_C11SP
    (X : PointedRiemannianSeq.{u, 0, 0} ThreeModel)
    (θ : ℝ) (hθ : 0 < θ) (Phi : ℝ → ℝ) (hPhi : AdmissiblePinchingFunction Phi)
    (Lambda : ℕ → ℝ) (hLambdaPos : ∀ n, 0 < Lambda n)
    (hLambdaTop : Tendsto Lambda atTop atTop)
    (J : ℕ → ℝ) (hJ : ∀ m, 1 ≤ J m)
    (hdata : ∀ n : ℕ,
      ∃ U : TopologicalSpace.Opens (X.obj n).M,
        (U : Set (X.obj n).M) =
          riemannianBallOf (X.obj n).metric (X.obj n).basepoint 1 ∧
      ∃ B : SolutionOn (I := ThreeModel) (M := U)
          (RealTimeInterval.closed (-θ) 0 (neg_nonpos.mpr hθ.le)),
        IsSolutionOn B ∧ B.base.metric 0 = (X.obj n).metric.restrictOpen U ∧
        (∀ s ∈ Icc (-θ) 0, ∀ x : U,
          curvatureOperatorLowerBoundAt (B.base.metric s) x
            (metricAlgebraicCurvatureTensorAt (B.base.metric s) x)
            (rescalePinchingFunction (Lambda n) Phi (metricScalarAt (B.base.metric s) x))) ∧
        ∀ m : ℕ, ∀ s ∈ Icc (-(θ / 2)) 0, ∀ x : U,
          x.val ∈ riemannianClosedBallOf (X.obj n).metric (X.obj n).basepoint (1 / 16) →
            curvDerivNorm m (B.base.metric s) x ≤ J m)
    (f : ℕ → ℕ) (hf : StrictMono f)
    (Pl : PointedRiemannianManifold.{u, 0, 0} ThreeModel)
    (maps : PointedRiemannianConvergenceMaps X Pl f) (M : MetricConvergenceData maps)
    (hcanonical : ∀ n, M.domain n =
      CanonicalMetricCompactness.canonicalSourceData maps n) :
    ∃ V : TopologicalSpace.Opens Pl.M, Pl.basepoint ∈ V ∧ PathConnectedSpace V ∧
      IsCompact (closure (V : Set Pl.M)) ∧
      ∃ N : ℕ, (∀ n, closure (V : Set Pl.M) ⊆ maps.source (n + N)) ∧
      ∃ G : ℝ → SmoothRiemannianMetric ThreeModel V,
        G 0 = Pl.metric.restrictOpen V ∧
        IsSolutionOn ({ base.metric := G } : SolutionOn (I := ThreeModel) (M := V)
          (RealTimeInterval.closed (-(θ / 2)) 0 (neg_nonpos.mpr (half_pos hθ).le))) ∧
        ∀ s ∈ Icc (-(θ / 2)) 0, ∀ x : V,
          metricAlgebraicCurvatureTensorAt (G s) x ∈
            algebraicCurvatureOperatorNonnegativeCone := by
  let U : ∀ n, TopologicalSpace.Opens (X.obj n).M := fun n => Classical.choose (hdata n)
  let B : ∀ n, SolutionOn (I := ThreeModel) (M := U n)
      (RealTimeInterval.closed (-θ) 0 (neg_nonpos.mpr hθ.le)) :=
    fun n => Classical.choose ((Classical.choose_spec (hdata n)).2)
  have hUnorm (n : ℕ) : (U n : Set (X.obj n).M) =
      riemannianBallOf (X.obj n).metric (X.obj n).basepoint 1 :=
    (Classical.choose_spec (hdata n)).1
  have hB (n : ℕ) : IsSolutionOn (B n) :=
    (Classical.choose_spec ((Classical.choose_spec (hdata n)).2)).1
  have hzero (n : ℕ) : (B n).base.metric 0 = (X.obj n).metric.restrictOpen (U n) :=
    (Classical.choose_spec ((Classical.choose_spec (hdata n)).2)).2.1
  have hwindowPinching (n : ℕ) (s : ℝ) (hs : s ∈ Icc (-θ) 0) (x : U n) :
      curvatureOperatorLowerBoundAt ((B n).base.metric s) x
        (metricAlgebraicCurvatureTensorAt ((B n).base.metric s) x)
        (rescalePinchingFunction (Lambda n) Phi (metricScalarAt ((B n).base.metric s) x)) :=
    (Classical.choose_spec ((Classical.choose_spec (hdata n)).2)).2.2.1 s hs x
  have hambient (n m : ℕ) (s : ℝ) (hs : s ∈ Icc (-(θ / 2)) 0) (x : U n)
      (hx : x.val ∈ riemannianClosedBallOf (X.obj n).metric (X.obj n).basepoint (1 / 16)) :
      curvDerivNorm m ((B n).base.metric s) x ≤ J m :=
    (Classical.choose_spec ((Classical.choose_spec (hdata n)).2)).2.2.2 m s hs x hx
  have href : ∀ n, (M.domain n).referenceMetric = (M.domain n).limitMetric := fun n => by
    rw [hcanonical n]
    rfl
  obtain ⟨V, hp, hpath, hcompact, hnear⟩ :=
    maps.exists_precompact_neighborhood_with_image_in_ball M href
      (r := 1 / 16) (by norm_num)
  obtain ⟨N, hN⟩ := eventually_atTop.mp hnear
  have hN' (n : ℕ) := hN (n + N) (Nat.le_add_left N n)
  let shift : ℕ → ℕ := fun n => n + N
  have hshift : StrictMono shift := fun i j hij => Nat.add_lt_add_right hij N
  let maps' := maps.compSubseq shift hshift
  let M' := M.compSubseq shift hshift
  have hcanonical' (n : ℕ) : M'.domain n =
      CanonicalMetricCompactness.canonicalSourceData maps' n := by
    change (M.domain (shift n)).compSubseq shift hshift n = _
    rw [hcanonical (shift n)]
    rfl
  have hsource (n : ℕ) : (V : Set Pl.M) ⊆ (maps'.partialDiffeomorph n).source :=
    fun x hx => (hN' n).1 (subset_closure hx)
  have hsmallImage (n : ℕ) (x : V) :
      riemannianEDistOf (X.obj (f (shift n))).metric (X.obj (f (shift n))).basepoint
        (maps'.map n x.val) < ENNReal.ofReal (1 / 16) := (hN' n).2 x.val x.property
  have hmem (n : ℕ) (x : V) : maps'.map n x.val ∈ U (f (shift n)) := by
    change maps'.map n x.val ∈ (U (f (shift n)) : Set (X.obj (f (shift n))).M)
    rw [hUnorm (f (shift n))]
    exact (hsmallImage n x).trans_le
      (ENNReal.ofReal_le_ofReal (by norm_num : (1 / 16 : ℝ) ≤ 1))
  let Ψ (n : ℕ) : V → U (f (shift n)) := fun x => ⟨maps'.map n x.val, hmem n x⟩
  have hΨ (n : ℕ) : IsLocalDiffeomorph ThreeModel ThreeModel ∞ (Ψ n) := by
    intro x
    apply isLocalDiffeomorphAt_subtypeCodRestrict (hmem n)
    exact isLocalDiffeomorph_restrict_open V
      (fun z => (maps'.partialDiffeomorph n).isLocalDiffeomorphAt
        ThreeModel ThreeModel ∞ (hsource n z.property)) x
  let S (n : ℕ) := (B (f (shift n))).localPullback (Ψ n) (hΨ n)
  have hS (n : ℕ) : IsSolutionOn (S n) := by
    let : SigmaCompactSpace (U (f (shift n))) := isSigmaCompact_iff_sigmaCompactSpace.mp
      (Geometry.isSigmaCompact_of_isOpen ThreeModel (U (f (shift n))).isOpen)
    exact (hB (f (shift n))).localPullback (Ψ n) (hΨ n)
  have hterminal (n : ℕ) (x : V) (v w : TangentSpace ThreeModel x) :
      ((S n).base.metric 0).inner x v w =
        (X.obj (f (shift n))).metric.inner (maps'.partialDiffeomorph n x)
          (mfderiv ThreeModel ThreeModel (maps'.partialDiffeomorph n) x v)
          (mfderiv ThreeModel ThreeModel (maps'.partialDiffeomorph n) x w) := by
    have hd : mfderiv ThreeModel ThreeModel (Ψ n) x =
        mfderiv ThreeModel ThreeModel (maps'.partialDiffeomorph n) x := by
      rw [← DifferentialGeometry.mfderiv_subtypeVal_comp
        (I := ThreeModel) (J := ThreeModel) (Ψ n) x]
      exact DifferentialGeometry.mfderiv_restrict_open (maps'.partialDiffeomorph n) V x
    change (localPullMetric ((B (f (shift n))).base.metric 0) (Ψ n) (hΨ n)).inner x v w = _
    rw [hzero (f (shift n)), localPullMetric_inner,
      SmoothRiemannianMetric.restrictOpen_inner, hd]
    rfl
  have hcurv : ∀ C : Set V, IsCompact C → ∀ m : ℕ,
      ∃ b : ℝ, 0 ≤ b ∧ ∀ᶠ n in atTop, ∀ s ∈ Icc (-(θ / 2)) 0, ∀ x ∈ C,
        curvDerivNorm m ((S n).base.metric s) x ≤ b := by
    intro C _hC m
    refine ⟨J m, zero_le_one.trans (hJ m), Eventually.of_forall ?_⟩
    intro n s hs x _hx
    change curvDerivNorm m
      (localPullMetric ((B (f (shift n))).base.metric s) (Ψ n) (hΨ n)) x ≤ J m
    rw [curvDerivNorm_localPullMetric]
    exact hambient (f (shift n)) m s hs (Ψ n x) (hsmallImage n x).le
  have hpinching : ∀ s ∈ Icc (-(θ / 2)) 0, ∀ᶠ n in atTop, ∀ x : V,
      curvatureOperatorLowerBoundAt ((S n).base.metric s) x
        (metricAlgebraicCurvatureTensorAt ((S n).base.metric s) x)
        (rescalePinchingFunction (Lambda (f (shift n))) Phi
          (metricScalarAt ((S n).base.metric s) x)) := by
    intro s hs
    refine Eventually.of_forall fun n x => ?_
    have hsFull : s ∈ Icc (-θ) 0 := ⟨by linarith [hs.1], hs.2⟩
    change curvatureOperatorLowerBoundAt
      (localPullMetric ((B (f (shift n))).base.metric s) (Ψ n) (hΨ n)) x
      (metricAlgebraicCurvatureTensorAt
        (localPullMetric ((B (f (shift n))).base.metric s) (Ψ n) (hΨ n)) x)
      (rescalePinchingFunction (Lambda (f (shift n))) Phi
        (metricScalarAt
          (localPullMetric ((B (f (shift n))).base.metric s) (Ψ n) (hΨ n)) x))
    rw [metricScalarAt_localPull]
    exact (curvatureOperatorLowerBoundAt_localPullMetric_iff
      ((B (f (shift n))).base.metric s) (Ψ n) (hΨ n) x _).mpr
      (hwindowPinching (f (shift n)) s hsFull (Ψ n x))
  have hLambdaSub : Tendsto (fun n => Lambda (f (shift n))) atTop atTop :=
    hLambdaTop.comp (hf.comp hshift).tendsto_atTop
  obtain ⟨_σ, _hσ, G, hGzero, hGsol, hGnonnegative, _hGconv⟩ :=
    exists_nonnegative_solution_subsequence_of_pointed_terminal_pullback
      maps' M' hcanonical' V hsource S hS
      (a := -(θ / 2)) (b := 0) (by linarith)
      (fun s hs => ⟨by linarith [hs.1], hs.2⟩)
      (fun s hs => ⟨by linarith [hs.1], hs.2⟩)
      hterminal hcurv hPhi (fun n => Lambda (f (shift n)))
      (fun n => hLambdaPos (f (shift n))) hLambdaSub hpinching
  exact ⟨V, hp, hpath, hcompact, N, fun n => (hN' n).1,
    G, hGzero, hGsol, hGnonnegative⟩

/-- **SPINE-A1 G2**：traced stage 序列的二次 metric limit 上，固定 basepoint 邻域 `V` 承载
匹配 terminal metric 的反向非负曲率 flow（`P6StageLocalFlowCXSP` 主定理的无 `let` 版）。 -/
theorem guard_stageLocalFlow_C11SP
    {P : OrientedThreeStage.{u}} {g : P.Metric}
    {pBase : CutoffParameters} {Γ : ClosedBirthConstants}
    (chain : PreparedSpatialChain pBase Γ P g) (F : GC.Interface.RawSurgery P g)
    (hTower : F.tower = chain.tower) (θ K : ℝ) (hθ : 0 < θ) (hK : 0 < K)
    (idx : ℕ → ℕ)
    (t : ∀ n, Icc (0 : ℝ) (F.tower.history (idx n)).toHistory.horizon)
    (y : ∀ n, ((F.tower.history (idx n)).toHistory.stageAt (t n)).Carrier)
    (R : ℕ → ℝ) (hR : ∀ n, 0 < R n)
    (htrace : ∀ n, (F.tower.history (idx n)).toHistory.isTracedRegion (t n) (y n)
      (Real.sqrt (R n))⁻¹ (θ / R n) (K * R n))
    (hage : Tendsto (fun n => (t n : ℝ) * R n) atTop atTop)
    (f : ℕ → ℕ) (hf : StrictMono f)
    (Pl : PointedRiemannianManifold.{u, 0, 0} ThreeModel)
    (maps : PointedRiemannianConvergenceMaps
      ({ obj := fun n =>
          { M := ((F.tower.history (idx n)).toHistory.stageAt (t n)).Carrier
            basepoint := y n
            metric := scaleMetric (R n) (hR n)
              ((F.tower.history (idx n)).toHistory.stageMetric
                ((F.tower.history (idx n)).toHistory.activeStage (t n)) (t n)) } } :
        PointedRiemannianSeq.{u, 0, 0} ThreeModel) Pl f)
    (M : MetricConvergenceData maps)
    (hcanonical : ∀ n, M.domain n = CanonicalMetricCompactness.canonicalSourceData maps n) :
    ∃ V : TopologicalSpace.Opens Pl.M, Pl.basepoint ∈ V ∧ PathConnectedSpace V ∧
      IsCompact (closure (V : Set Pl.M)) ∧
      ∃ N : ℕ, (∀ n, closure (V : Set Pl.M) ⊆ maps.source (n + N)) ∧
      ∃ G : ℝ → SmoothRiemannianMetric ThreeModel V,
        G 0 = Pl.metric.restrictOpen V ∧
        IsSolutionOn ({ base.metric := G } : SolutionOn (I := ThreeModel) (M := V)
          (RealTimeInterval.closed (-(θ / 2)) 0 (neg_nonpos.mpr (half_pos hθ).le))) ∧
        ∀ s ∈ Icc (-(θ / 2)) 0, ∀ x : V,
          metricAlgebraicCurvatureTensorAt (G s) x ∈
            algebraicCurvatureOperatorNonnegativeCone := by
  obtain ⟨a₀, Phi, ha₀, hPhi, hwindow⟩ :=
    exists_prepared_traced_window_pinching_and_jets_CXSP P g
  obtain ⟨J, hJ, hwindowN⟩ := hwindow θ K hθ hK
  have hLambdaPos (n : ℕ) : 0 < (a₀ + (t n : ℝ) - θ / R n) * R n :=
    (hwindowN chain F hTower (idx n) (t n) (y n) (R n) (hR n) (htrace n)).2.1
  have hLambdaLower (n : ℕ) : (t n : ℝ) * R n - θ ≤ (a₀ + (t n : ℝ) - θ / R n) * R n := by
    have ha := mul_nonneg ha₀.le (hR n).le
    have heq : (a₀ + (t n : ℝ) - θ / R n) * R n = a₀ * R n + (t n : ℝ) * R n - θ := by
      field_simp [(hR n).ne']
    rw [heq]
    linarith only [ha]
  have hLambdaTop : Tendsto (fun n => (a₀ + (t n : ℝ) - θ / R n) * R n) atTop atTop := by
    apply tendsto_atTop.mpr
    intro A
    filter_upwards [hage.eventually_ge_atTop (A + θ)] with n hn
    exact (by linarith only [hn] : A ≤ (t n : ℝ) * R n - θ).trans (hLambdaLower n)
  have hdata : ∀ n : ℕ,
      ∃ U : TopologicalSpace.Opens ((F.tower.history (idx n)).toHistory.stageAt (t n)).Carrier,
        (U : Set ((F.tower.history (idx n)).toHistory.stageAt (t n)).Carrier) =
          riemannianBallOf (scaleMetric (R n) (hR n)
            ((F.tower.history (idx n)).toHistory.stageMetric
              ((F.tower.history (idx n)).toHistory.activeStage (t n)) (t n))) (y n) 1 ∧
      ∃ B : SolutionOn (I := ThreeModel) (M := U)
          (RealTimeInterval.closed (-θ) 0 (neg_nonpos.mpr hθ.le)),
        IsSolutionOn B ∧ B.base.metric 0 = (scaleMetric (R n) (hR n)
            ((F.tower.history (idx n)).toHistory.stageMetric
              ((F.tower.history (idx n)).toHistory.activeStage (t n)) (t n))).restrictOpen U ∧
        (∀ s ∈ Icc (-θ) 0, ∀ x : U,
          curvatureOperatorLowerBoundAt (B.base.metric s) x
            (metricAlgebraicCurvatureTensorAt (B.base.metric s) x)
            (rescalePinchingFunction ((a₀ + (t n : ℝ) - θ / R n) * R n) Phi
              (metricScalarAt (B.base.metric s) x))) ∧
        ∀ m : ℕ, ∀ s ∈ Icc (-(θ / 2)) 0, ∀ x : U,
          x.val ∈ riemannianClosedBallOf (scaleMetric (R n) (hR n)
            ((F.tower.history (idx n)).toHistory.stageMetric
              ((F.tower.history (idx n)).toHistory.activeStage (t n)) (t n))) (y n) (1 / 16) →
            curvDerivNorm m (B.base.metric s) x ≤ J m := by
    intro n
    have hw := hwindowN chain F hTower (idx n) (t n) (y n) (R n) (hR n) (htrace n)
    obtain ⟨_hMin, _hLambda, U, _hU, hUnorm, B, hB, hzero, hcontrol,
      _pU, _hpU, _hinner, hambient⟩ := hw
    exact ⟨U, hUnorm, B, hB, hzero, fun s hs x => (hcontrol s hs x).2, hambient⟩
  exact exists_local_flow_of_unit_windows_C11SP _ θ hθ Phi hPhi
    (fun n => (a₀ + (t n : ℝ) - θ / R n) * R n) hLambdaPos hLambdaTop J hJ hdata
    f hf Pl maps M hcanonical

end GC.LongTime.Ch11

end
