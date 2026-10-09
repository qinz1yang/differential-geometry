import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.Local.BoundedCurvatureAtDistanceCone2_P6L
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.Local.TracedTerminalCompactness2_P6L

/-!
# L6-B 第 3 层：`BoundedCurvatureAtDistanceCone:365` 的局部化（`_P6L`）

局部化合同 §2：原 `RetainedCoreHistory.exists_nonnegative_local_flow_with_comparison_of_final_slab_window`
（`ST/BoundedCurvatureAtDistanceCone.lean:365`）的 `hderiv`/`hfinal`/`htested` 只整体传给
`Cone:258` 与 `TTC:1576`（buffer 半径 `< 1`）；这里两者换成 `_P6L` 版，加
`U : ∀ n, Set ((H n).stage (Fin.last _)).Carrier`、`hU : ∀ n, B_{Q n·g}(x n, 1) ⊆ U n`（在 `hQlim` 之后），
`hderiv` footprint 形、`hfinal` 限于 `U n`、`htested` 中心限于 `U n`（`HEq` 形）。
pinching 全局。私有 `localPullMetric_restrict_inner`（`:38`）一并复制。证明体照抄。
-/

set_option autoImplicit false


noncomputable section

open Set Filter
open DifferentialGeometry.CheegerGromovCompactness DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Integral.Measure
open scoped Manifold ContDiff Topology NNReal ENNReal

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

open DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn

universe u v

attribute [local instance] PointedRiemannianManifold.topology PointedRiemannianManifold.charted
  PointedRiemannianManifold.smooth PointedRiemannianManifold.t2
  PointedRiemannianManifold.sigmaCompact PointedRiemannianManifold.t2TangentBundle

private local instance {P : OrientedThreeStage.{u}} {a s : ℝ} (G : P.IncomingSlab a s) :
    SigmaCompactSpace G.terminalRegularOpen :=
  isSigmaCompact_iff_sigmaCompactSpace.mp
    (DifferentialGeometry.Geometry.isSigmaCompact_of_isOpen ThreeModel G.terminalRegularOpen.isOpen)

private local instance pointedLimitRegular (L : PointedRiemannianManifold.{u, 0, 0} ThreeModel) :
    RegularSpace L.M := by
  let _ : LocallyCompactSpace L.M := ChartedSpace.locallyCompactSpace ThreeSpace L.M
  infer_instance

/-- **`_P6L` 私有副本**：原 private `localPullMetric_restrict_inner`（`Cone:38`），逐字。 -/
private theorem localPullMetric_restrict_inner_P6L {M N : Type*} [TopologicalSpace M]
    [ChartedSpace ThreeSpace M] [IsManifold ThreeModel ∞ M] [T2Space M]
    [TopologicalSpace N] [ChartedSpace ThreeSpace N] [IsManifold ThreeModel ∞ N]
    (g : SmoothRiemannianMetric ThreeModel N) (Φ : PartialDiffeomorph ThreeModel ThreeModel M N ∞)
    (V : TopologicalSpace.Opens M)
    (hf : IsLocalDiffeomorph ThreeModel ThreeModel ∞ (fun z : V => Φ z.val))
    (z : V) (v w : TangentSpace ThreeModel z) :
    (localPullMetric g (fun z : V => Φ z.val) hf).inner z v w =
      g.inner (Φ z) (mfderiv ThreeModel ThreeModel Φ z v)
        (mfderiv ThreeModel ThreeModel Φ z w) := by
  rw [localPullMetric_inner]
  have hd := DifferentialGeometry.mfderiv_restrict_open (I := ThreeModel) (J := ThreeModel) Φ V z
  rw [hd]
  rfl

/-- **`_P6L`**：原
`RetainedCoreHistory.exists_nonnegative_local_flow_with_comparison_of_final_slab_window`
（`Cone:365`）。改动：加 `U`（`hderiv` 之前）、`hU : ∀ n, B_{Q n·g}(x n, 1) ⊆ U n`（`hQlim` 之后）；
`hderiv` footprint 形、`hfinal` 限于 `U n`、`htested` 中心限于 `U n`（`HEq` 形）。结论逐字。 -/
theorem RetainedCoreHistory.exists_nonnegative_local_flow_with_comparison_of_final_slab_window_P6L
    (H : ℕ → RetainedCoreHistory.{u}) (s : ℕ → ℝ)
    (A : ∀ n, ((H n).stage (Fin.last (H n).eventCount)).ClosedSlab
      ((H n).time (Fin.last (H n).eventCount)) (s n))
    (hinit : ∀ n, (A n).flow.base.metric ((H n).time (Fin.last (H n).eventCount)) =
      (H n).initialMetric (Fin.last (H n).eventCount))
    (Ctime : ℝ≥0) (q : ℕ → ℝ) (hq : ∀ n, 0 < q n)
    (U : ∀ n, Set ((H n).stage (Fin.last (H n).eventCount)).Carrier)
    (hderiv : ∀ n, ∀ j : Fin (H n).eventCount,
      ∀ (first : Fin ((H n).eventCount + 1)) (hf : first ≤ j.castSucc),
      ∀ z ∈ U n, ∀ A : BackwardPointTrace (H n).toHistory first (Fin.last (H n).eventCount)
        (Fin.le_last first) z,
      ∀ t ∈ Ioo ((H n).time j.castSucc) ((H n).time j.succ),
      q n < ((H n).toHistory.event j).incoming.flow.scalar t
        (A.point j.castSucc hf (Fin.le_last _)) →
      |derivWithin (fun v => ((H n).toHistory.event j).incoming.flow.scalar v
        (A.point j.castSucc hf (Fin.le_last _))) (Iic t) t| ≤
        Ctime * ((H n).toHistory.event j).incoming.flow.scalar t
          (A.point j.castSucc hf (Fin.le_last _)) ^ 2)
    (hfinal : ∀ n, ∀ y ∈ U n, ∀ t ∈ Ioo ((H n).time (Fin.last (H n).eventCount)) (s n),
      q n < (A n).flow.scalar t y →
      |derivWithin (fun v => (A n).flow.scalar v y) (Iic t) t| ≤
        Ctime * (A n).flow.scalar t y ^ 2)
    (x : ∀ n, ((A n).restrictIncoming le_rfl (A n).lt le_rfl).terminalRegularOpen)
    (Q : ℕ → ℝ) (hQ : ∀ n, 1 ≤ Q n) (hqQ : ∀ n, q n ≤ Q n)
    (hQlim : Tendsto Q atTop atTop)
    (hU : ∀ n, ∀ y ∈ riemannianBallOf (scaleMetric (Q n) (zero_lt_one.trans_le (hQ n))
      ((A n).endpointTerminalLimitMetric ((H n).stage (Fin.last (H n).eventCount))).metric)
      (x n) 1, y.val ∈ U n)
    {Phi : ℝ → ℝ} (hPhi : Perelman.AdmissiblePinchingFunction Phi)
    (hpinch : ∀ n j, Perelman.PhiAlmostNonnegative ((H n).toHistory.event j).incoming.flow
      (Ico ((H n).time j.castSucc) ((H n).time j.succ)) Phi)
    (hpinchFinal : ∀ n, Perelman.PhiAlmostNonnegative
      ((A n).restrictIncoming le_rfl (A n).lt le_rfl).flow
      (Ico ((H n).time (Fin.last (H n).eventCount)) (s n)) Phi)
    (hbuffer : ∀ R : ℝ, 0 < R → R < 1 → ∃ r Amax θ : ℝ,
      0 < r ∧ R + r < 1 ∧ 1 ≤ Amax ∧ 0 < θ ∧ 6 * Ctime * (Amax * θ) ≤ 1 ∧
      ∀ᶠ n in atTop,
        IsCompact (riemannianClosedBallOf (scaleMetric (Q n) (zero_lt_one.trans_le (hQ n))
          ((A n).endpointTerminalLimitMetric ((H n).stage (Fin.last (H n).eventCount))).metric)
          (x n) (R + r)) ∧
        (∀ z ∈ riemannianClosedBallOf (scaleMetric (Q n) (zero_lt_one.trans_le (hQ n))
          ((A n).endpointTerminalLimitMetric ((H n).stage (Fin.last (H n).eventCount))).metric)
          (x n) (R + r), metricScalarAt
            ((A n).endpointTerminalLimitMetric ((H n).stage (Fin.last (H n).eventCount))).metric
            z ≤ 2 * (Amax * Q n)) ∧
        ∃ first : Fin ((H n).eventCount + 1),
          (∀ z ∈ riemannianClosedBallOf (scaleMetric (Q n) (zero_lt_one.trans_le (hQ n))
            ((A n).endpointTerminalLimitMetric ((H n).stage (Fin.last (H n).eventCount))).metric)
            (x n) (R + r), Nonempty (BackwardPointTrace (H n).toHistory first
              (Fin.last (H n).eventCount) (Fin.le_last first) z.val)) ∧
          (H n).time first ≤ s n - θ / Q n)
    (hs : ∀ n, (H n).horizon < s n)
    (hscale : ∀ n, Q n = metricScalarAt
      ((A n).endpointTerminalLimitMetric ((H n).stage (Fin.last (H n).eventCount))).metric (x n))
    {κ σ₀ : ℝ} (σ : ℕ → ℝ) (hκ : 0 < κ) (hσ₀ : 0 < σ₀)
    (hσQ : ∀ n, σ₀ ≤ σ n * Real.sqrt (Q n))
    (htested : ∀ n (t : ℝ) (ht : (H n).horizon < t) (hts : t < s n),
      let B := (H n).extendHorizon t ht.le
        (((A n).restrictIncoming le_rfl (A n).lt le_rfl).closedPrefix t
          ((H n).time_le_horizon.trans_lt ht) hts) (hinit n)
      let tm : Icc (0 : ℝ) B.horizon := ⟨t, (H n).horizon_nonneg.trans ht.le, le_rfl⟩
      ∀ z ∈ U n, ∀ (y : (B.toHistory.stageAt tm).Carrier), HEq y z →
      ∀ (b : ℝ), 0 < b → b ≤ σ n →
        B.toHistory.isParabolicallyRmControlledBall tm y b →
          ENNReal.ofReal κ * ENNReal.ofReal b ^ 3 ≤
            riemannianVolumeMeasure ThreeModel (B.toHistory.stageAt tm).Carrier
              (B.toHistory.stageMetric (B.toHistory.activeStage tm) tm)
              (riemannianBallOf (B.toHistory.stageMetric (B.toHistory.activeStage tm) tm) y b))
    {N : Type v} [TopologicalSpace N] [ChartedSpace ThreeSpace N] [IsManifold ThreeModel ∞ N]
    [T2Space N] (Hn : ℕ → SmoothRiemannianMetric ThreeModel N) (xN : ℕ → N)
    (B : ∀ n, PartialDiffeomorph ThreeModel ThreeModel N
      ((A n).restrictIncoming le_rfl (A n).lt le_rfl).terminalRegularOpen ∞)
    {R : ℝ} (hR : 0 < R)
    (hBsource : ∀ n, riemannianClosedBallOf (Hn n) (xN n) R ⊆ (B n).source)
    (hBbase : ∀ n, B n (xN n) = x n)
    (hcapture : ∀ n, riemannianClosedBallOf (scaleMetric (Q n) (zero_lt_one.trans_le (hQ n))
      ((A n).endpointTerminalLimitMetric ((H n).stage (Fin.last (H n).eventCount))).metric)
      (x n) (R / 4) ⊆ (B n) '' riemannianClosedBallOf (Hn n) (xN n) R)
    (hBconv : ∀ eta : ℝ, 0 < eta → ∀ᶠ n in atTop,
      ∀ y ∈ riemannianClosedBallOf (Hn n) (xN n) R, ∀ v : TangentSpace ThreeModel y,
        (1 - eta) * (Hn n).inner y v v ≤ (scaleMetric (Q n) (zero_lt_one.trans_le (hQ n))
          ((A n).endpointTerminalLimitMetric
            ((H n).stage (Fin.last (H n).eventCount))).metric).inner
            (B n y) (mfderiv ThreeModel ThreeModel (B n) y v)
            (mfderiv ThreeModel ThreeModel (B n) y v) ∧
        (scaleMetric (Q n) (zero_lt_one.trans_le (hQ n))
          ((A n).endpointTerminalLimitMetric
            ((H n).stage (Fin.last (H n).eventCount))).metric).inner
            (B n y) (mfderiv ThreeModel ThreeModel (B n) y v)
            (mfderiv ThreeModel ThreeModel (B n) y v) ≤ (1 + eta) * (Hn n).inner y v v) :
    ∃ (j : ℕ → ℕ) (_ : StrictMono j) (P₂ : PointedRiemannianManifold.{u, 0, 0} ThreeModel)
      (V : TopologicalSpace.Opens P₂.M)
      (hp : P₂.basepoint ∈ V) (_ : PathConnectedSpace V) (tau : ℝ) (htau : 0 < tau)
      (g : ℝ → SmoothRiemannianMetric ThreeModel V),
      g 0 = P₂.metric.restrictOpen V ∧ metricScalarAt P₂.metric P₂.basepoint = 1 ∧
      IsSolutionOn ({ base.metric := g } : SolutionOn (I := ThreeModel) (M := V)
        (RealTimeInterval.closed (-tau) 0 (by linarith))) ∧
      (∀ t ∈ Icc (-tau) 0, ∀ y : V, metricAlgebraicCurvatureTensorAt (g t) y ∈
        algebraicCurvatureOperatorNonnegativeCone (I := ThreeModel)) ∧
      ∃ C : ℕ → PartialDiffeomorph ThreeModel ThreeModel V N ∞,
        (∀ n, C n ⟨P₂.basepoint, hp⟩ = xN (j n)) ∧
        ∃ r : ℝ, 0 < r ∧ IsCompact (riemannianClosedBallOf (g 0) ⟨P₂.basepoint, hp⟩ r) ∧
        (∀ᶠ n in atTop, riemannianClosedBallOf (g 0) ⟨P₂.basepoint, hp⟩ r ⊆ (C n).source ∧
          riemannianClosedBallOf (Hn (j n)) (xN (j n)) (r / 4) ⊆
            (C n) '' riemannianClosedBallOf (g 0) ⟨P₂.basepoint, hp⟩ r) ∧
        ∀ eta : ℝ, 0 < eta → ∀ᶠ n in atTop,
          ∀ a ∈ riemannianClosedBallOf (g 0) ⟨P₂.basepoint, hp⟩ r,
          ∀ b ∈ riemannianClosedBallOf (g 0) ⟨P₂.basepoint, hp⟩ r,
            |(riemannianEDistOf (Hn (j n)) (C n a) (C n b)).toReal -
              (riemannianEDistOf (g 0) a b).toReal| < eta := by
  let G := fun n => (A n).restrictIncoming le_rfl (A n).lt le_rfl
  let L := fun n => (A n).endpointTerminalLimitMetric ((H n).stage (Fin.last (H n).eventCount))
  have hconv :=
    RetainedCoreHistory.exists_normalized_terminal_pointed_convergence_of_scaled_tests_P6L
    Phi hPhi H s G L hinit hs x q Q hscale hq hqQ hQ U hderiv hfinal hpinch hpinchFinal one_pos
    hU hbuffer σ hκ hσ₀ hσQ htested
  dsimp only at hconv
  obtain ⟨f₂, hf₂, _, _, _, P₂, F₂, M, hbase₂, hcanonical, hradial, hcompact, _, _⟩ := hconv
  let F := PointedRiemannianConvergenceMaps.liftTargetOpen
    (S := { obj := fun n =>
          { M := (G n).terminalRegularOpen
            basepoint := x n
            metric := scaleMetric (Q n) (zero_lt_one.trans_le (hQ n)) (L n).metric } })
    (fun i => connectedComponentOpen (I := ThreeModel) (x i))
    (fun i => (mem_connectedComponent : x i ∈ connectedComponentOpen (I := ThreeModel) (x i))) F₂
  let V : TopologicalSpace.Opens P₂.M := ⟨riemannianBallOf P₂.metric P₂.basepoint (1 / 2),
    isOpen_lt (Geometry.Riemannian.continuous_riemannianEDist _ _) continuous_const⟩
  have hp : P₂.basepoint ∈ V := by
    change riemannianEDistOf P₂.metric P₂.basepoint P₂.basepoint < ENNReal.ofReal (1 / 2)
    rw [riemannianEDistOf_self]
    exact ENNReal.ofReal_pos.mpr (by norm_num)
  have hpath : PathConnectedSpace V := isPathConnected_iff_pathConnectedSpace.mp
    (isPathConnected_riemannianBallOf P₂.metric P₂.basepoint (by norm_num))
  have hVc : IsCompact (closure (V : Set P₂.M)) := by
    apply (hcompact (1 / 2) (by norm_num) (by norm_num)).of_isClosed_subset isClosed_closure
    refine closure_minimal (fun z (hz : riemannianEDistOf P₂.metric P₂.basepoint z <
      ENNReal.ofReal (1 / 2)) => (le_of_lt hz : riemannianEDistOf P₂.metric P₂.basepoint z ≤
        ENNReal.ofReal (1 / 2))) ?_
    exact isClosed_le (Geometry.Riemannian.continuous_riemannianEDist _ _) continuous_const
  have hupper : ∀ K : Set P₂.M, IsCompact K → ∀ C : ℝ, 1 < C → ∀ᶠ i in atTop,
      ∀ z ∈ K, ∀ v : TangentSpace ThreeModel z,
        (scaleMetric (Q (f₂ i)) (zero_lt_one.trans_le (hQ (f₂ i)))
          (L (f₂ i)).metric).inner (F.map i z)
          (mfderiv ThreeModel ThreeModel (F.map i) z v)
          (mfderiv ThreeModel ThreeModel (F.map i) z v) ≤ C ^ 2 * P₂.metric.inner z v v := by
    intro K hK C hC
    have hconv : metricSourceConvergesOn F
        (CanonicalMetricCompactness.canonicalSourceData F) K 0 := by
      have heq : M.domain = CanonicalMetricCompactness.canonicalSourceData F := funext hcanonical
      rw [← heq]
      exact M.converges K hK 0
    filter_upwards [pointed_metric_eventually_quadratic_bounds hK hconv
      (by nlinarith : 0 < C ^ 2 - 1)] with i hi
    intro z hz v
    simpa only [add_sub_cancel] using (hi.2 z hz v).2
  have hbuffer' : ∀ R : ℝ, 0 < R → R < 1 → ∃ r Amax θ : ℝ,
      0 < r ∧ R + r < 1 ∧ 1 ≤ Amax ∧ 0 < θ ∧ 6 * Ctime * (Amax * θ) ≤ 1 ∧ ∀ᶠ i in atTop,
        IsCompact (riemannianClosedBallOf
          (scaleMetric (Q (f₂ i)) (zero_lt_one.trans_le (hQ (f₂ i))) (L (f₂ i)).metric)
          (x (f₂ i)) (R + r)) ∧
        (∀ z ∈ riemannianClosedBallOf
          (scaleMetric (Q (f₂ i)) (zero_lt_one.trans_le (hQ (f₂ i))) (L (f₂ i)).metric)
          (x (f₂ i)) (R + r), metricScalarAt (L (f₂ i)).metric z ≤ 2 * (Amax * Q (f₂ i))) ∧
        ∃ first : Fin ((H (f₂ i)).eventCount + 1),
          ∃ hle : first ≤ Fin.last (H (f₂ i)).eventCount,
          (∀ z ∈ riemannianClosedBallOf
            (scaleMetric (Q (f₂ i)) (zero_lt_one.trans_le (hQ (f₂ i))) (L (f₂ i)).metric)
            (x (f₂ i)) (R + r),
            Nonempty (BackwardPointTrace (H (f₂ i)).toHistory first
              (Fin.last (H (f₂ i)).eventCount) hle z.val)) ∧
          (H (f₂ i)).time first ≤ s (f₂ i) - θ / Q (f₂ i) := by
    intro R hR hR1
    obtain ⟨r, Amax, θ, hr, hRr, hA, hθ, hbud, hev⟩ := hbuffer R hR hR1
    refine ⟨r, Amax, θ, hr, hRr, hA, hθ, hbud, ?_⟩
    filter_upwards [hf₂.tendsto_atTop.eventually hev] with i hi
    obtain ⟨first, htr, hst⟩ := hi.2.2
    exact ⟨hi.1, hi.2.1, first, Fin.le_last first, htr, hst⟩
  open ObservedHistory in
  obtain ⟨Rr, rr, Amax, θ, hθ, Bd, _, _, _, _, _, hBd, hev⟩ :=
    exists_eventually_historical_solution_with_curvature_bounds_of_pointed_convergence_P6L
      (fun n => (H n).toHistory) (fun n => Fin.last (H n).eventCount) G x L hinit q Q hq hqQ hQ F
      one_pos hradial hcompact hupper Phi hPhi U hU (fun n j first _ hf _ => hderiv n j first hf)
      hfinal
      (fun n j _ => hpinch n j) hpinchFinal hbuffer' V hVc
  obtain ⟨N, hN⟩ := eventually_atTop.mp hev
  choose first hle Ψ hΨ hFv gflow S hsource _ _ _ hstart _ _ hS hzero hmetric hslabs hlast _
    hcurv using fun j : ℕ => hN (j + N) (Nat.le_add_left N j)
  have hsh : StrictMono (fun j : ℕ => j + N) := fun a b h => Nat.add_lt_add_right h N
  let F₃ := F.compSubseq (fun j => j + N) hsh
  let M₃ := M.compSubseq (fun j => j + N) hsh
  have hcan₃ (j : ℕ) : M₃.domain j = CanonicalMetricCompactness.canonicalSourceData F₃ j := by
    change (M.domain (j + N)).compSubseq _ hsh j = _
    rw [hcanonical (j + N)]
    rfl
  have hterm : ∀ j (z : V) (v w : TangentSpace ThreeModel z),
      ((S j).base.metric 0).inner z v w =
        (scaleMetric (Q (f₂ (j + N))) (zero_lt_one.trans_le (hQ (f₂ (j + N))))
          (L (f₂ (j + N))).metric).inner (F₃.partialDiffeomorph j z)
          (mfderiv ThreeModel ThreeModel (F₃.partialDiffeomorph j) z v)
          (mfderiv ThreeModel ThreeModel (F₃.partialDiffeomorph j) z w) := by
    intro j z v w
    refine (congrArg (fun g : SmoothRiemannianMetric ThreeModel V => g.inner z v w)
      (hzero j)).trans ?_
    exact localPullMetric_restrict_inner_P6L _ (F.partialDiffeomorph (j + N)) V (hFv j) z v w
  have hcurv' : ∀ K : Set V, IsCompact K → ∀ m : ℕ, ∃ B' : ℝ, 0 ≤ B' ∧ ∀ᶠ j in atTop,
      ∀ t ∈ Icc (-(θ / 2)) 0, ∀ z ∈ K, curvDerivNorm m ((S j).base.metric t) z ≤ B' :=
    fun _ _ m => ⟨Bd m, hBd m, Eventually.of_forall fun j t ht z _ => hcurv j m t ht z⟩
  have hpa (j : ℕ) : Perelman.PhiAlmostNonnegative (S j) (Icc (-θ) 0)
      (Perelman.rescalePinchingFunction (Q (f₂ (j + N))) Phi) :=
    ObservedHistory.phiAlmostNonnegative_parabolic_backwardSurvivorIncomingFootprint_localPullback
      (H (f₂ (j + N))).toHistory (first j) (Fin.last (H (f₂ (j + N))).eventCount)
      (hle j) (G (f₂ (j + N))) (L (f₂ (j + N)))
      (riemannianClosedBallOf (scaleMetric (Q (f₂ (j + N))) (zero_lt_one.trans_le (hQ _))
        (L (f₂ (j + N))).metric) (x (f₂ (j + N))) (Rr + rr))
      (gflow j) (hslabs j) (hlast j) hPhi.contDiff.continuous
      (fun jj _ _ => hpinch (f₂ (j + N)) jj) (hpinchFinal (f₂ (j + N)))
      (zero_lt_one.trans_le (hQ (f₂ (j + N)))) (hstart j) (Ψ j) (hΨ j) (S j)
      (fun v _ => hmetric j v)
  have hpinching : ∀ t ∈ Icc (-(θ / 2)) 0, ∀ᶠ j in atTop, ∀ z : V,
      curvatureOperatorLowerBoundAt ((S j).base.metric t) z
        (metricAlgebraicCurvatureTensorAt ((S j).base.metric t) z)
        (Perelman.rescalePinchingFunction (Q (f₂ (j + N))) Phi
          (metricScalarAt ((S j).base.metric t) z)) := by
    intro t ht
    exact Eventually.of_forall fun j z => hpa j t ⟨by linarith [ht.1], ht.2⟩ z
  have hBconv' : ∀ eta : ℝ, 0 < eta → ∀ᶠ j in atTop,
      ∀ y ∈ riemannianClosedBallOf (Hn (f₂ (j + N))) (xN (f₂ (j + N))) R,
      ∀ v : TangentSpace ThreeModel y,
        (1 - eta) * (Hn (f₂ (j + N))).inner y v v ≤
          (scaleMetric (Q (f₂ (j + N))) (zero_lt_one.trans_le (hQ (f₂ (j + N))))
            (L (f₂ (j + N))).metric).inner (B (f₂ (j + N)) y)
            (mfderiv ThreeModel ThreeModel (B (f₂ (j + N))) y v)
            (mfderiv ThreeModel ThreeModel (B (f₂ (j + N))) y v) ∧
        (scaleMetric (Q (f₂ (j + N))) (zero_lt_one.trans_le (hQ (f₂ (j + N))))
          (L (f₂ (j + N))).metric).inner (B (f₂ (j + N)) y)
          (mfderiv ThreeModel ThreeModel (B (f₂ (j + N))) y v)
          (mfderiv ThreeModel ThreeModel (B (f₂ (j + N))) y v) ≤
            (1 + eta) * (Hn (f₂ (j + N))).inner y v v :=
    fun eta heta => (hf₂.comp hsh).tendsto_atTop.eventually (hBconv eta heta)
  obtain ⟨_, _, g, hgb, hsol, hnonneg, _, r, hr, hcpt, hcenter, hcap, hdist⟩ :=
    DifferentialGeometry.PDE.RicciFlow.exists_nonnegative_local_flow_with_end_comparison
      F₃ M₃ hcan₃ V hp (fun j => hsource j) S hS (a := -(θ / 2)) (b := 0) (by linarith)
      (fun t ht => ⟨by linarith [ht.1], ht.2⟩) (fun t ht => ⟨by linarith [ht.1], ht.2⟩)
      hterm hcurv' hPhi (fun j => Q (f₂ (j + N))) (fun j => zero_lt_one.trans_le (hQ _))
      (hQlim.comp (hf₂.comp hsh).tendsto_atTop) hpinching
      (fun j => Hn (f₂ (j + N))) (fun j => xN (f₂ (j + N))) (fun j => B (f₂ (j + N))) hR
      (fun j => hBsource _) (fun j => hBbase _) (fun j => hcapture _) hBconv'
  exact ⟨fun j => f₂ (j + N), hf₂.comp hsh, P₂, V, hp, hpath, θ / 2, by positivity, g, hgb,
    hbase₂, hsol, hnonneg, _, hcenter, r, hr, hcpt, hcap, hdist⟩

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
