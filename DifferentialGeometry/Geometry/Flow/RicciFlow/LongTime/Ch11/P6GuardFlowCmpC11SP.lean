import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.P6GuardFlowC11SP
import DifferentialGeometry.Geometry.Flow.RicciFlow.Compactness.Limits.LocalEndComparison

/-!
# SPINE-A1 G3：guard 分支固定 V flow + end 比较（P6L:444 结论中 history 无关的后半）

G2 的固定 `V` kernel（unit window solutions 的 localPullback）改喂树内
`exists_nonnegative_local_flow_with_end_comparison`
（`Compactness/Limits/LocalEndComparison.lean:31`）：
给定第一层比较数据 `(Hn, x, B, R₀)`（source / basepoint / capture / 二次型 `1 ± η`），
同时产出反向非负 flow 与 `C n : V ⇀ N`、半径 `r`、compact、capture、两点距离比较，即
`RetainedCoreHistory.exists_local_backward_limit_at_final_slab_end_of_eventual_traces_P6L`
（`Local/BoundedCurvatureAtDistanceTracedCone_P6L.lean:444`）结论里 `g / C / r` 的部分。
Codex 草稿 `CXSP-HANDOVER-20261007/pkg/drafts/P6StageLocalEndComparisonCXSP.lean`（未编）
有实例与 `mfderiv` 对齐问题，本文件不用它，改走树内已编的 LocalEndComparison。
第一层比较数据的 producer（二次 metric limit：G64 + ScalarRescaling + G45）不在本文件。
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

universe u v

attribute [local instance] PointedRiemannianManifold.topology PointedRiemannianManifold.charted
  PointedRiemannianManifold.smooth PointedRiemannianManifold.t2
  PointedRiemannianManifold.sigmaCompact PointedRiemannianManifold.t2TangentBundle

variable {Nc : Type v} [TopologicalSpace Nc] [ChartedSpace ThreeSpace Nc]
  [IsManifold ThreeModel ∞ Nc] [T2Space Nc]

/-- G3 kernel：G2 固定 V kernel 的 pullback solutions 改喂树内
`exists_nonnegative_local_flow_with_end_comparison`
（`Compactness/Limits/LocalEndComparison.lean:31`），
同时产 end 比较 `C / r / capture / dist`（第一层比较数据按同一 shift `n + N` 重索引）。 -/
theorem exists_local_flow_endComparison_of_unit_windows_C11SP
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
      CanonicalMetricCompactness.canonicalSourceData maps n)
    (Hc : ℕ → SmoothRiemannianMetric ThreeModel Nc) (xc : ℕ → Nc)
    (Bc : ∀ n, PartialDiffeomorph ThreeModel ThreeModel Nc (X.obj (f n)).M ∞)
    {R₀ : ℝ} (hR₀ : 0 < R₀)
    (hBsource : ∀ n, riemannianClosedBallOf (Hc n) (xc n) R₀ ⊆ (Bc n).source)
    (hBbase : ∀ n, Bc n (xc n) = (X.obj (f n)).basepoint)
    (hcapture : ∀ n,
      riemannianClosedBallOf (X.obj (f n)).metric (X.obj (f n)).basepoint (R₀ / 4) ⊆
        (Bc n) '' riemannianClosedBallOf (Hc n) (xc n) R₀)
    (hBconv : ∀ eta : ℝ, 0 < eta → ∀ᶠ n in atTop,
      ∀ y ∈ riemannianClosedBallOf (Hc n) (xc n) R₀, ∀ w : TangentSpace ThreeModel y,
        (1 - eta) * (Hc n).inner y w w ≤ (X.obj (f n)).metric.inner (Bc n y)
          (mfderiv ThreeModel ThreeModel (Bc n) y w)
          (mfderiv ThreeModel ThreeModel (Bc n) y w) ∧
        (X.obj (f n)).metric.inner (Bc n y)
          (mfderiv ThreeModel ThreeModel (Bc n) y w)
          (mfderiv ThreeModel ThreeModel (Bc n) y w) ≤ (1 + eta) * (Hc n).inner y w w) :
    ∃ (V : TopologicalSpace.Opens Pl.M) (hp : Pl.basepoint ∈ V), PathConnectedSpace V ∧
      IsCompact (closure (V : Set Pl.M)) ∧
      ∃ N₀ : ℕ, (∀ n, closure (V : Set Pl.M) ⊆ maps.source (n + N₀)) ∧
      ∃ G : ℝ → SmoothRiemannianMetric ThreeModel V,
        G 0 = Pl.metric.restrictOpen V ∧
        IsSolutionOn ({ base.metric := G } : SolutionOn (I := ThreeModel) (M := V)
          (RealTimeInterval.closed (-(θ / 2)) 0 (neg_nonpos.mpr (half_pos hθ).le))) ∧
        (∀ s ∈ Icc (-(θ / 2)) 0, ∀ z : V,
          metricAlgebraicCurvatureTensorAt (G s) z ∈
            algebraicCurvatureOperatorNonnegativeCone (I := ThreeModel)) ∧
        ∃ C : ℕ → PartialDiffeomorph ThreeModel ThreeModel V Nc ∞,
          (∀ n, C n ⟨Pl.basepoint, hp⟩ = xc (n + N₀)) ∧
          ∃ r : ℝ, 0 < r ∧ IsCompact (riemannianClosedBallOf (G 0) ⟨Pl.basepoint, hp⟩ r) ∧
            (∀ᶠ n in atTop, riemannianClosedBallOf (G 0) ⟨Pl.basepoint, hp⟩ r ⊆
                (C n).source ∧
              riemannianClosedBallOf (Hc (n + N₀)) (xc (n + N₀)) (r / 4) ⊆
                (C n) '' riemannianClosedBallOf (G 0) ⟨Pl.basepoint, hp⟩ r) ∧
            ∀ eta : ℝ, 0 < eta → ∀ᶠ n in atTop,
              ∀ a ∈ riemannianClosedBallOf (G 0) ⟨Pl.basepoint, hp⟩ r,
              ∀ b ∈ riemannianClosedBallOf (G 0) ⟨Pl.basepoint, hp⟩ r,
                |(riemannianEDistOf (Hc (n + N₀)) (C n a) (C n b)).toReal -
                  (riemannianEDistOf (G 0) a b).toReal| < eta := by
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
  let _ : PathConnectedSpace V := hpath
  obtain ⟨_ρ, _hρ, G, hGzero, hGsol, hGnonnegative, _hGconv, r, hr, hcpt, hcenter, hcap,
      hdist⟩ :=
    exists_nonnegative_local_flow_with_end_comparison
      maps' M' hcanonical' V hp hsource S hS
      (a := -(θ / 2)) (b := 0) (by linarith)
      (fun s hs => ⟨by linarith [hs.1], hs.2⟩)
      (fun s hs => ⟨by linarith [hs.1], hs.2⟩)
      hterminal hcurv hPhi (fun n => Lambda (f (shift n)))
      (fun n => hLambdaPos (f (shift n))) hLambdaSub hpinching
      (fun n => Hc (n + N)) (fun n => xc (n + N)) (fun n => Bc (n + N)) hR₀
      (fun n => hBsource (n + N)) (fun n => hBbase (n + N)) (fun n => hcapture (n + N))
      (fun eta heta => hshift.tendsto_atTop.eventually (hBconv eta heta))
  exact ⟨V, hp, hpath, hcompact, N, fun n => (hN' n).1, G, hGzero, hGsol, hGnonnegative,
    _, hcenter, r, hr, hcpt, hcap, hdist⟩

/-- **SPINE-A1 G3**：traced stage 序列（G2 的输入）+ 第一层比较数据 ⇒ 固定 `V` 上反向非负 flow
连同 end 比较 `C / r / capture / dist`（陈述无 `let`）。 -/
theorem guard_stageLocalFlow_endComparison_C11SP
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
    (hcanonical : ∀ n, M.domain n = CanonicalMetricCompactness.canonicalSourceData maps n)
    (Hn : ℕ → SmoothRiemannianMetric ThreeModel Nc) (x : ℕ → Nc)
    (B : ∀ n, PartialDiffeomorph ThreeModel ThreeModel Nc
      ((F.tower.history (idx (f n))).toHistory.stageAt (t (f n))).Carrier ∞)
    {R₀ : ℝ} (hR₀ : 0 < R₀)
    (hBsource : ∀ n, riemannianClosedBallOf (Hn n) (x n) R₀ ⊆ (B n).source)
    (hBbase : ∀ n, B n (x n) = y (f n))
    (hcapture : ∀ n, riemannianClosedBallOf (scaleMetric (R (f n)) (hR (f n))
        ((F.tower.history (idx (f n))).toHistory.stageMetric
          ((F.tower.history (idx (f n))).toHistory.activeStage (t (f n))) (t (f n))))
        (y (f n)) (R₀ / 4) ⊆ (B n) '' riemannianClosedBallOf (Hn n) (x n) R₀)
    (hBconv : ∀ eta : ℝ, 0 < eta → ∀ᶠ n in atTop,
      ∀ z ∈ riemannianClosedBallOf (Hn n) (x n) R₀, ∀ w : TangentSpace ThreeModel z,
        (1 - eta) * (Hn n).inner z w w ≤ (scaleMetric (R (f n)) (hR (f n))
            ((F.tower.history (idx (f n))).toHistory.stageMetric
              ((F.tower.history (idx (f n))).toHistory.activeStage (t (f n))) (t (f n)))).inner
          (B n z) (mfderiv ThreeModel ThreeModel (B n) z w)
          (mfderiv ThreeModel ThreeModel (B n) z w) ∧
        (scaleMetric (R (f n)) (hR (f n))
            ((F.tower.history (idx (f n))).toHistory.stageMetric
              ((F.tower.history (idx (f n))).toHistory.activeStage (t (f n))) (t (f n)))).inner
          (B n z) (mfderiv ThreeModel ThreeModel (B n) z w)
          (mfderiv ThreeModel ThreeModel (B n) z w) ≤ (1 + eta) * (Hn n).inner z w w) :
    ∃ (V : TopologicalSpace.Opens Pl.M) (hp : Pl.basepoint ∈ V), PathConnectedSpace V ∧
      IsCompact (closure (V : Set Pl.M)) ∧
      ∃ N₀ : ℕ, (∀ n, closure (V : Set Pl.M) ⊆ maps.source (n + N₀)) ∧
      ∃ G : ℝ → SmoothRiemannianMetric ThreeModel V,
        G 0 = Pl.metric.restrictOpen V ∧
        IsSolutionOn ({ base.metric := G } : SolutionOn (I := ThreeModel) (M := V)
          (RealTimeInterval.closed (-(θ / 2)) 0 (neg_nonpos.mpr (half_pos hθ).le))) ∧
        (∀ s ∈ Icc (-(θ / 2)) 0, ∀ z : V,
          metricAlgebraicCurvatureTensorAt (G s) z ∈
            algebraicCurvatureOperatorNonnegativeCone (I := ThreeModel)) ∧
        ∃ C : ℕ → PartialDiffeomorph ThreeModel ThreeModel V Nc ∞,
          (∀ n, C n ⟨Pl.basepoint, hp⟩ = x (n + N₀)) ∧
          ∃ r : ℝ, 0 < r ∧ IsCompact (riemannianClosedBallOf (G 0) ⟨Pl.basepoint, hp⟩ r) ∧
            (∀ᶠ n in atTop, riemannianClosedBallOf (G 0) ⟨Pl.basepoint, hp⟩ r ⊆
                (C n).source ∧
              riemannianClosedBallOf (Hn (n + N₀)) (x (n + N₀)) (r / 4) ⊆
                (C n) '' riemannianClosedBallOf (G 0) ⟨Pl.basepoint, hp⟩ r) ∧
            ∀ eta : ℝ, 0 < eta → ∀ᶠ n in atTop,
              ∀ a ∈ riemannianClosedBallOf (G 0) ⟨Pl.basepoint, hp⟩ r,
              ∀ b ∈ riemannianClosedBallOf (G 0) ⟨Pl.basepoint, hp⟩ r,
                |(riemannianEDistOf (Hn (n + N₀)) (C n a) (C n b)).toReal -
                  (riemannianEDistOf (G 0) a b).toReal| < eta := by
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
  exact exists_local_flow_endComparison_of_unit_windows_C11SP _ θ hθ Phi hPhi
    (fun n => (a₀ + (t n : ℝ) - θ / R n) * R n) hLambdaPos hLambdaTop J hJ hdata
    f hf Pl maps M hcanonical Hn x B hR₀ hBsource hBbase hcapture hBconv

end GC.LongTime.Ch11

end
