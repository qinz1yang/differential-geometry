import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.P6LocalAncientLimitP6B
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.AncientPointedFlowLimitTerminalNoncollapsing
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.TracedRegionAncientKappaLimit

/-!
# P6 / M8 装配：局部 κ + 局部 pinching ⇒ 古代极限 `κ/250`-noncollapsed（O-CH11-P6B G2）

后缀 `_P6B`。把 L8c（`exists_ancient_pointed_flow_limit_with_survivor_maps_of_traced_seed_P6B`）的
输出接到树内**局部**定理 `parabolicallyKappaNoncollapsedBelowScale_of_local_pinching_flow_limit_of_time_lt`
（`ST/AncientPointedFlowLimitTerminalNoncollapsing.lean:202`）：

* 输入全部是 history 级、**沿 traced 球的 backward trace 的局部**条件：traced regions（所有 `A, T`）、
  基点种子体积、trace-local κ（尺度 `≤ ρnc n`，只要 `ρnc n √R n → ∞`）、trace-local pinching（固定 admissible `Φ`）；
* 输出：完备连通 pointed 极限 `P` 上的古代 Ricci flow `G`，对每个 `ρ > 0` 都是
  `ParabolicallyKappaNoncollapsedBelowScale … (κ/250) ρ`。

这就是 digest M8"局部 κ ⇒ 极限 κ/250（接 `:213`）+ 局部序列结构"：树内全局版
`exists_ancientKappa_pointed_limit_of_isTracedRegion` 的 κ 部分要求全局 `hnc`，这里只要局部的。
pinching 的局部流转写照 `TracedRegionAncientKappaLimit` 的 `hpinchW`，只把全局前提换成 trace 点。
-/

set_option autoImplicit false

noncomputable section

open Set Filter TopologicalSpace
open DifferentialGeometry.Geometry.Curvature DifferentialGeometry.Tensor0SBundle
open DifferentialGeometry.CheegerGromovCompactness
open scoped Manifold ContDiff Topology NNReal ENNReal

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

open Perelman.CanonicalNeighborhood (ancientTimeInterval)
open Perelman.CanonicalNeighborhood.FiniteHorn
  (isKappaNoncollapsed_of_local_flow_limit_of_time_lt)

open private ObservedHistory.mem_Icc_of_mem_window
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

/-- **M8 装配**：traced regions + 基点种子体积 + trace-local κ（尺度 `≤ ρnc n`，`ρnc n √R n → ∞`）
+ trace-local pinching
⇒ 局部古代极限 `(P, G)`，`G` 对每个 `ρ > 0` 是 `κ/250`-noncollapsed（无任何全局假设）。 -/
theorem exists_local_ancient_limit_kappa_noncollapsed_P6B
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
    ∃ (f : ℕ → ℕ), StrictMono f ∧
      ∃ (P : PointedRiemannianManifold.{u, 0, 0} ThreeModel)
        (_ : PointedRiemannianConvergenceMaps X P f),
        MetricComplete P ∧ ConnectedSpace P.M ∧
        ∃ (G : ℝ → SmoothRiemannianMetric ThreeModel P.M)
          (_ : IsSolutionOn ({ base.metric := G } : SolutionOn (I := ThreeModel) (M := P.M)
            ancientTimeInterval)),
          G 0 = P.metric ∧
          ∀ ρ : ℝ, 0 < ρ → Perelman.ParabolicallyKappaNoncollapsedBelowScale
            ({ base.metric := G } : SolutionOn (I := ThreeModel) (M := P.M)
              ancientTimeInterval) (κ / 250) ρ := by
  intro X
  obtain ⟨W, h, hblock, f, hf, P, F, -, hPc, hconn, -, V, N, hV, hVF, φ, hφ, hφF, G, hG0, hG,
    ψ, hψ, hconv⟩ :=
    exists_ancient_pointed_flow_limit_with_survivor_maps_of_traced_seed_P6B H t y R hR htraced
      hr₀ hw hseed hκ.le ρnc hkappa
  have hsol : ∀ k : ℕ, ∀ᶠ n in atTop, IsSolutionOn ({ base.metric := h k n } :
      SolutionOn (I := ThreeModel) (M := W k n)
        (RealTimeInterval.closed (-((k + 2 : ℕ) : ℝ)) 0 (neg_nonpos.mpr (Nat.cast_nonneg _)))) :=
    fun k => (hblock k).mono fun _ hn => hn.2.1
  have hnc : ∀ k : ℕ, ∀ σ ∈ Icc (-((k + 1 : ℕ) : ℝ)) 0, σ < 0 → ∀ᶠ n in atTop,
      ∀ z : W k n, ∀ r : ℝ, 0 < r → r ≤ ρnc n * Real.sqrt (R n) →
      Icc (σ - r ^ 2) σ ⊆ Icc (-((k + 2 : ℕ) : ℝ)) 0 →
      IsCompact (riemannianClosedBallOf (h k n σ) z r) →
      (∀ s ∈ Icc (σ - r ^ 2) σ, ∀ w ∈ riemannianBallOf (h k n σ) z r,
        r ^ 4 * curvDerivNormSq 0 (h k n s) w ≤ 1) →
      ENNReal.ofReal (κ * r ^ 3) ≤
        Integral.Measure.riemannianVolumeMeasure ThreeModel (W k n) (h k n σ)
          (riemannianBallOf (h k n σ) z r) :=
    fun k σ hσ _ => (hblock k).mono fun _ hn => hn.2.2.2.2 σ hσ
  have hθ (k : ℕ) : 0 < 2 * ((k + 2 : ℕ) : ℝ) := by positivity
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
  -- `:202` 的证明，`ρ₀ √R n` 换成一般的 `radii n = ρnc n √R n → ∞`
  have hmono : Monotone V := by
    intro k l hkl z hz
    change z ∈ (V l : Set P.M)
    have hz' : z ∈ (V k : Set P.M) := hz
    rw [hV] at hz' ⊢
    refine riemannianBallOf_mono _ _ ?_ hz'
    have : ((k + 1 : ℕ) : ℝ) ≤ ((l + 1 : ℕ) : ℝ) := by exact_mod_cast Nat.add_le_add_right hkl 1
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
  have hcomplete := (ancient_pointed_flow_limit_curvatureOperator_nonnegative_and_complete hf hPc
    hconn hV hG0 hG hψ hconv hRlim hPhi hpinchW).2
  refine ⟨f, hf, P, F, hPc, hconn, G, hG, hG0, fun ρ hρ => ?_⟩
  refine Perelman.parabolicallyKappaNoncollapsedBelowScale_of_forall_time_lt hG ?_ hρ
    (fun _ hs => hs)
    fun time B htime _ hB => isKappaNoncollapsed_of_local_flow_limit_of_time_lt hsol hκ hradii
      hnc hf F hmono hcover hVF φ hφ hφF hG hcomplete hψ hconv B hB htime
  change interior (Iic (0 : ℝ)) ⊆ Iio 0
  rw [interior_Iic]

end ObservedHistory

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
