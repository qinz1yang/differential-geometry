import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.TracedRegionLocalLimitDepthSchedule
import DifferentialGeometry.Geometry.Flow.RicciFlow.Solution.OpenClosedGluing
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.LocalPointedFlowLimitNoncollapsing
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.LocalFlowLimitWindowTransfer
import DifferentialGeometry.Geometry.Curvature.CurvatureOperator.Derivatives.LocalPullbackScaling
import DifferentialGeometry.Geometry.Curvature.CurvatureOperator.Derivatives.Scaling
import DifferentialGeometry.Geometry.Metric.Convergence.Curvature.TensorConvergence
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.RetainedCrossingJets
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.LocalFlowLimitBaseScalar
import DifferentialGeometry.Geometry.Curvature.RicciRestriction

set_option autoImplicit false

noncomputable section

open Set Filter TopologicalSpace
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.CheegerGromovCompactness
open scoped Manifold ContDiff Topology NNReal ENNReal

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

open private ObservedHistory.riemannianBallOf_scaleMetric_eq ObservedHistory.mem_Icc_of_mem_window
  from DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.TracedRegionAncientLimit

namespace ObservedHistory

open Perelman.CanonicalNeighborhood.FiniteHorn (monotone_and_cover_of_riemannianBallOf_eq
  curvatureOperator_nonnegative_of_local_pinching_limit_on_window
  parabolicallyKappaNoncollapsedBelowScale_of_local_flow_limit_on_openClosed
  metricScalarAt_basepoint_eq_of_local_flow_limit_on_window)

universe u

private local instance {M : Type u} [TopologicalSpace M] [ChartedSpace ThreeSpace M]
    [SigmaCompactSpace M] (U : Opens M) : SigmaCompactSpace U :=
  isSigmaCompact_iff_sigmaCompactSpace.mp
    (Geometry.isSigmaCompact_of_isOpen ThreeModel U.isOpen)

private local instance {M : Type u} [TopologicalSpace M] (U : Opens M) : MeasurableSpace U :=
  borel U

private local instance {M : Type u} [TopologicalSpace M] (U : Opens M) : BorelSpace U := ⟨rfl⟩

private theorem curvDerivNormSq_zero_eq_normSq0S {M : Type u} [TopologicalSpace M]
    [ChartedSpace ThreeSpace M] [IsManifold ThreeModel ∞ M] [T2Space M]
    (g : SmoothRiemannianMetric ThreeModel M) (z : M) :
    curvDerivNormSq 0 g z = Tensor0SBundle.normSq0S g z 4 (metricRm04At g z) := by
  have h0 : curvCovDeriv (I := ThreeModel) (M := M) g 0 = metricRm04 g := rfl
  rw [curvDerivNormSq, h0, metricRm04_apply]

attribute [local instance] PointedRiemannianManifold.topology PointedRiemannianManifold.charted
  PointedRiemannianManifold.smooth PointedRiemannianManifold.t2
  PointedRiemannianManifold.sigmaCompact

private theorem depth_schedule_facts {T : ℝ} (hT : 0 < T) :
    (∀ k : ℕ, 0 < ((k + 1 : ℕ) : ℝ) / ((k + 2 : ℕ) : ℝ) * T) ∧
    (∀ k : ℕ, ((k + 1 : ℕ) : ℝ) / ((k + 2 : ℕ) : ℝ) * T < T) ∧
    Monotone (fun k : ℕ => ((k + 1 : ℕ) : ℝ) / ((k + 2 : ℕ) : ℝ) * T) ∧
    (∀ s < T, ∃ k : ℕ, s < ((k + 1 : ℕ) : ℝ) / ((k + 2 : ℕ) : ℝ) * T) := by
  refine ⟨fun k => by positivity, fun k => ?_, ?_, fun s hs => ?_⟩
  · have h1 : ((k + 1 : ℕ) : ℝ) / ((k + 2 : ℕ) : ℝ) < 1 := by
      rw [div_lt_one (by positivity)]
      push_cast
      linarith
    nlinarith
  · intro k l hkl
    have hkl' : (k : ℝ) ≤ l := by exact_mod_cast hkl
    refine mul_le_mul_of_nonneg_right ?_ hT.le
    rw [div_le_div_iff₀ (by positivity) (by positivity)]
    push_cast
    nlinarith
  · obtain ⟨k, hk⟩ := exists_nat_gt ((T - s)⁻¹ * T)
    refine ⟨k, ?_⟩
    have hTs : 0 < T - s := by linarith
    have hk' : (T - s)⁻¹ * T < k + 1 := by linarith
    have hk'' : T < (k + 1) * (T - s) := by
      rw [inv_mul_lt_iff₀ hTs] at hk'
      linarith
    have hpos : (0 : ℝ) < ((k + 2 : ℕ) : ℝ) := by positivity
    rw [div_mul_eq_mul_div, lt_div_iff₀ hpos]
    push_cast
    nlinarith

theorem curvDerivNormSq_zero_le_of_survivor_maps_of_isTracedRegion (H : ObservedHistory.{u})
    (t : Icc (0 : ℝ) H.horizon) (y : (H.stageAt t).Carrier) {R : ℝ} (hR : 0 < R) {T ρ K : ℝ}
    (htr : H.isTracedRegion t y ρ (T / R) (K * R))
    {W : Opens (H.stageAt t).Carrier}
    (hW : ∀ x : W, x.val ∈ riemannianBallOf (H.stageMetric (H.activeStage t) t) y ρ)
    {h : ℝ → SmoothRiemannianMetric ThreeModel W} (a : Icc (0 : ℝ) H.horizon) (hat : a ≤ t)
    (ha : (a : ℝ) = t - T / R)
    (f : (j : H.StageInterval (H.activeStage a) (H.activeStage t)) → W →
      (H.stage j.val).Carrier)
    (hf : ∀ j, IsLocalDiffeomorph ThreeModel ThreeModel ∞ (f j))
    (hcross : ∀ (i : Fin H.eventCount) (hi : H.activeStage a ≤ i.castSucc)
      (hl : i.succ ≤ H.activeStage t), ∀ x : W,
      (H.event i).RegularCrossing (f ⟨i.castSucc, hi, i.castSucc_lt_succ.le.trans hl⟩ x)
        (f ⟨i.succ, hi.trans i.castSucc_lt_succ.le, hl⟩ x))
    (hlast : ∀ x : W, f ⟨H.activeStage t, H.activeStage_mono hat, le_rfl⟩ x = x.val)
    (hp : ∀ s ∈ Icc (-T) 0, ∀ j : H.StageInterval (H.activeStage a) (H.activeStage t),
      (t : ℝ) + s / R ∈ H.stageDomain j.val →
        h s = scaleMetric R hR
          (localPullMetric (H.stageMetric j.val ((t : ℝ) + s / R)) (f j) (hf j))) :
    ∀ s ∈ Icc (-T) 0, ∀ x : W, curvDerivNormSq 0 (h s) x ≤ K ^ 2 := by
  intro s hs x
  obtain ⟨-, -, a', hat', ha', htrace⟩ := htr
  have haa : a' = a := Subtype.ext (by rw [ha', ha])
  subst haa
  obtain ⟨A, hA⟩ := htrace x.val (hW x)
  have hv := ObservedHistory.mem_Icc_of_mem_window hR ha hs
  let v : Icc (0 : ℝ) H.horizon := ⟨(t : ℝ) + s / R, a'.2.1.trans hv.1, hv.2.trans t.2.2⟩
  have hav : a' ≤ v := hv.1
  have hvt : v ≤ t := hv.2
  let j : H.StageInterval (H.activeStage a') (H.activeStage t) :=
    ⟨H.activeStage v, H.activeStage_mono hav, H.activeStage_mono hvt⟩
  have hs' := hp s hs j (H.activeStage_mem v)
  let B : BackwardPointTrace H (H.activeStage a') (H.activeStage t) (H.activeStage_mono hat)
      x.val :=
    { point := fun j' hf' hl => f ⟨j', hf', hl⟩ x
      endpoint_eq := hlast x
      crossing := fun i hf' hl => hcross i hf' hl x }
  have hAB : A = B := Subsingleton.elim _ _
  have hpt : A.point (H.activeStage v) (H.activeStage_mono hav) (H.activeStage_mono hvt) =
      f j x := by
    rw [hAB]
  have hbound := hA.1 v hav hvt
  rw [hpt] at hbound
  rw [hs', curvDerivNormSq_scaleMetric, curvDerivNormSq_localPullMetric,
    curvDerivNormSq_zero_eq_normSq0S]
  calc (R)⁻¹ ^ (0 + 2) * Tensor0SBundle.normSq0S (H.stageMetric (H.activeStage v) v) (f j x) 4
        (metricRm04At (H.stageMetric (H.activeStage v) v) (f j x))
      ≤ (R)⁻¹ ^ (0 + 2) * (K * R) ^ 2 := mul_le_mul_of_nonneg_left hbound (by positivity)
    _ = K ^ 2 := by
        rw [zero_add, mul_pow, inv_pow, ← mul_assoc, mul_comm ((R ^ 2)⁻¹), mul_assoc,
          inv_mul_cancel₀ (pow_ne_zero 2 hR.ne'), mul_one]

theorem normSq0S_metricRm04At_le_of_local_flow_limit_on_window
    {X : PointedRiemannianSeq.{u, 0, 0} ThreeModel}
    {P : PointedRiemannianManifold.{u, 0, 0} ThreeModel}
    {W : ∀ (_ : ℕ) (n : ℕ), Opens (X.obj n).M}
    {h : ∀ k n, ℝ → SmoothRiemannianMetric ThreeModel (W k n)} {f : ℕ → ℕ} (hf : StrictMono f)
    {V : ℕ → Opens P.M} (hVmono : Monotone V) (hVcover : ∀ x : P.M, ∃ k, x ∈ V k)
    {N : ℕ → ℕ} {φ : ∀ k j, N k ≤ j → V k → W k (f j)}
    {hφ : ∀ k j (hj : N k ≤ j), IsLocalDiffeomorph ThreeModel ThreeModel ∞ (φ k j hj)}
    {T : ℝ} {c : ℕ → ℝ} (hcmono : Monotone c) (hcT : ∀ s ∈ Ioc (-T) 0, ∃ k, -c k < s)
    {G : ℝ → SmoothRiemannianMetric ThreeModel P.M} {ψ : ℕ → ℕ} (hψ : StrictMono ψ)
    (hconv : ∀ k (K : Set (V k)), IsCompact K → ∀ p : ℕ, ∀ η : ℝ, 0 < η →
      ∃ j₀ : ℕ, ∀ i ≥ j₀, ∃ hi : N k ≤ ψ i, ∀ s ∈ Icc (-c k) 0,
        metricDerivNormSupOn K p
          (localPullMetric (h k (f (ψ i)) s) (φ k (ψ i) hi) (hφ k (ψ i) hi))
          ((G s).restrictOpen (V k)) (P.metric.restrictOpen (V k)) < η)
    {K : ℝ} (hbound : ∀ k : ℕ, ∀ᶠ n in atTop, ∀ s ∈ Icc (-c k) 0, ∀ x : W k n,
      curvDerivNormSq 0 (h k n s) x ≤ K ^ 2) :
    ∀ s ∈ Ioc (-T) 0, ∀ x : P.M,
      Tensor0SBundle.normSq0S (G s) x 4 (metricRm04At (G s) x) ≤ K ^ 2 := by
  intro s hs x
  rw [← curvDerivNormSq_zero_eq_normSq0S]
  obtain ⟨k, hxk⟩ := hVcover x
  obtain ⟨l, hl⟩ := hcT s hs
  set m := max k l with hm
  have hxm : x ∈ V m := hVmono (le_max_left k l) hxk
  have hsm : s ∈ Icc (-c m) 0 :=
    ⟨(neg_le_neg (hcmono (le_max_right k l))).trans hl.le, hs.2⟩
  have hfψ : Tendsto (fun i => f (ψ i)) atTop atTop := (hf.comp hψ).tendsto_atTop
  obtain ⟨i0, hi0⟩ := eventually_atTop.mp
    ((hψ.tendsto_atTop.eventually (eventually_ge_atTop (N m))).and
      (hfψ.eventually (hbound m)))
  let seq : ℕ → SmoothRiemannianMetric ThreeModel (V m) := fun i =>
    localPullMetric (h m (f (ψ (i + i0))) s) (φ m (ψ (i + i0)) (hi0 (i + i0) (by omega)).1)
      (hφ m (ψ (i + i0)) (hi0 (i + i0) (by omega)).1)
  have hconvU : MetricCInfConvergenceOnCompacts seq ((G s).restrictOpen (V m))
      (P.metric.restrictOpen (V m)) := by
    intro K' hK' p η hη
    obtain ⟨j₀, hj₀⟩ := hconv m K' hK' p η hη
    refine ⟨j₀, fun i hi => ?_⟩
    obtain ⟨hi', hb⟩ := hj₀ (i + i0) (by omega)
    exact hb s hsm
  have hKs : IsCompact ({⟨x, hxm⟩} : Set (V m)) := isCompact_singleton
  have hlim := (hconvU _ hKs 2).tendsto_normSq_metricRm04At hKs (mem_singleton _)
  have hterm : ∀ i, Tensor0SBundle.normSq0S (seq i) ⟨x, hxm⟩ 4
      (metricRm04At (seq i) ⟨x, hxm⟩) ≤ K ^ 2 := by
    intro i
    have h1 := (hi0 (i + i0) (by omega)).2 s hsm
      (φ m (ψ (i + i0)) (hi0 (i + i0) (by omega)).1 ⟨x, hxm⟩)
    rw [← curvDerivNormSq_localPullMetric (h m (f (ψ (i + i0))) s)
      (φ m (ψ (i + i0)) (hi0 (i + i0) (by omega)).1)
      (hφ m (ψ (i + i0)) (hi0 (i + i0) (by omega)).1)
      0 ⟨x, hxm⟩, curvDerivNormSq_zero_eq_normSq0S] at h1
    exact h1
  have hle := le_of_tendsto hlim (Eventually.of_forall hterm)
  rw [← curvDerivNormSq_zero_eq_normSq0S, curvDerivNormSq_restrictOpen] at hle
  exact hle

theorem exists_window_pointed_flow_limit_of_isTracedRegion
    (H : ℕ → ObservedHistory.{u}) (t : ∀ n, Icc (0 : ℝ) (H n).horizon)
    (y : ∀ n, ((H n).stageAt (t n)).Carrier) (R : ℕ → ℝ) (hR : ∀ n, 0 < R n)
    (hRlim : Tendsto R atTop atTop) {T : ℝ} (hT : 0 < T) {K : ℝ} (hK : 0 ≤ K)
    (htraced : ∀ A : ℝ, 0 < A → ∀ᶠ n in atTop,
      (H n).isTracedRegion (t n) (y n) (A / Real.sqrt (R n)) (T / R n) (K * R n))
    {κ ρ : ℝ} (hκ : 0 < κ) (hρ : 0 < ρ)
    {t₀ : ℕ → ℝ} (hsliver : Tendsto (fun n => R n * (t n - t₀ n)) atTop (𝓝 0))
    (hnc : ∀ n (v : Icc (0 : ℝ) (H n).horizon) (p : ((H n).stageAt v).Carrier) (r : ℝ),
      (v : ℝ) < t₀ n → r ≤ ρ → (H n).isParabolicallyRmControlledBall v p r →
      ENNReal.ofReal κ * ENNReal.ofReal r ^ 3 ≤
        Integral.Measure.riemannianVolumeMeasure ThreeModel ((H n).stageAt v).Carrier
          ((H n).stageMetric ((H n).activeStage v) v)
          (riemannianBallOf ((H n).stageMetric ((H n).activeStage v) v) p r))
    {Phi : ℝ → ℝ} (hPhi : Perelman.AdmissiblePinchingFunction Phi)
    (hpinch : ∀ n (v : Icc (0 : ℝ) (H n).horizon), (v : ℝ) ≤ t n →
      ∀ x : ((H n).stageAt v).Carrier,
        curvatureOperatorLowerBoundAt ((H n).stageMetric ((H n).activeStage v) v) x
          (metricAlgebraicCurvatureTensorAt ((H n).stageMetric ((H n).activeStage v) v) x)
          (Phi (metricScalarAt ((H n).stageMetric ((H n).activeStage v) v) x))) :
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
          (RealTimeInterval.closed (-T) 0 (neg_nonpos.mpr hT.le))) ∧
        (∀ s ∈ Icc (-T) 0,
          (t n : ℝ) + s / R n ∈ (H n).stageDomain ((H n).activeStage (t n)) →
          h k n s = scaleMetric (R n) (hR n)
            (((H n).stageMetric ((H n).activeStage (t n)) ((t n : ℝ) + s / R n)).restrictOpen
              (W k n))) ∧
        (∃ (a : Icc (0 : ℝ) (H n).horizon) (hat : a ≤ t n),
          (a : ℝ) = t n - T / R n ∧
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
              ∀ s ∈ Icc (-T) 0,
                ∀ j : (H n).StageInterval ((H n).activeStage a) ((H n).activeStage (t n)),
                  (t n : ℝ) + s / R n ∈ (H n).stageDomain j.val →
                    h k n s = scaleMetric (R n) (hR n)
                      (localPullMetric ((H n).stageMetric j.val ((t n : ℝ) + s / R n)) (f j)
                        (hf j))) ∧
        ∀ σ ∈ Icc (-(((k + 1 : ℕ) : ℝ) / ((k + 2 : ℕ) : ℝ) * T)) 0,
          (t n : ℝ) + σ / R n < t₀ n → ∀ z : W k n, ∀ r : ℝ, 0 < r →
          r ≤ ρ * Real.sqrt (R n) → Icc (σ - r ^ 2) σ ⊆ Icc (-T) 0 →
          IsCompact (riemannianClosedBallOf (h k n σ) z r) →
          (∀ s ∈ Icc (σ - r ^ 2) σ, ∀ w ∈ riemannianBallOf (h k n σ) z r,
            r ^ 4 * curvDerivNormSq 0 (h k n s) w ≤ 1) →
          ENNReal.ofReal (κ * r ^ 3) ≤
            Integral.Measure.riemannianVolumeMeasure ThreeModel (W k n) (h k n σ)
              (riemannianBallOf (h k n σ) z r)) ∧
      (∀ k p : ℕ, ∃ L : ℝ, ∀ᶠ n in atTop,
        ∀ σ ∈ Icc (-(((k + 1 : ℕ) : ℝ) / ((k + 2 : ℕ) : ℝ) * T)) 0,
        ∀ σ' ∈ Icc (-(((k + 1 : ℕ) : ℝ) / ((k + 2 : ℕ) : ℝ) * T)) 0, ∀ z : W k n,
          (z : (X.obj n).M) ∈
            riemannianClosedBallOf (X.obj n).metric (X.obj n).basepoint ((k + 2 : ℕ) : ℝ) →
          ∀ a : ℕ, a ≤ p → metricDerivNorm a (h k n σ) (h k n σ') (h k n 0) z ≤ L * |σ - σ'|) ∧
      (∀ k : ℕ, ∀ᶠ n in atTop, ∀ s ∈ Icc (-T) 0, ∀ x : W k n,
        curvDerivNormSq 0 (h k n s) x ≤ K ^ 2) ∧
      (∀ k : ℕ, ∀ᶠ n in atTop, ∀ s ∈ Icc (-(((k + 1 : ℕ) : ℝ) / ((k + 2 : ℕ) : ℝ) * T)) 0,
        ∀ (x : W k n) (u : TangentSpace ThreeModel x),
        (h k n 0).inner x u u ≤ Real.exp 2 * (h k n s).inner x u u) ∧
      (∀ k : ℕ, ∀ᶠ n in atTop, ∀ s ∈ Icc (-T) 0, ∀ x : W k n,
        curvatureOperatorLowerBoundAt (h k n s) x (metricAlgebraicCurvatureTensorAt (h k n s) x)
          (Perelman.rescalePinchingFunction (R n) Phi (metricScalarAt (h k n s) x))) ∧
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
                  (RealTimeInterval.openClosed (-T) 0 0 ⟨neg_lt_zero.mpr hT, le_rfl⟩)) ∧
                (∀ s ∈ Ioc (-T) 0, ∀ x : P.M, metricAlgebraicCurvatureTensorAt (G s) x ∈
                  algebraicCurvatureOperatorNonnegativeCone) ∧
                (∀ s ∈ Ioc (-T) 0, RiemannianMetricComplete (G s)) ∧
                (∀ s ∈ Ioc (-T) 0, ∀ x : P.M,
                  Tensor0SBundle.normSq0S (G s) x 4 (metricRm04At (G s) x) ≤ K ^ 2) ∧
                ((∀ n, metricScalarAt ((H n).stageMetric ((H n).activeStage (t n)) (t n)) (y n) =
                    R n) →
                  metricScalarAt P.metric P.basepoint = 1) ∧
                (∀ ρ' : ℝ, 0 < ρ' → Perelman.ParabolicallyKappaNoncollapsedBelowScale
                  ({ base.metric := G } : SolutionOn (I := ThreeModel) (M := P.M)
                    (RealTimeInterval.openClosed (-T) 0 0 ⟨neg_lt_zero.mpr hT, le_rfl⟩))
                  (κ / 250) ρ') ∧
                ∃ ψ : ℕ → ℕ, StrictMono ψ ∧
                  ∀ k (K : Set (V k)), IsCompact K → ∀ p : ℕ, ∀ η : ℝ, 0 < η →
                    ∃ j₀ : ℕ, ∀ i ≥ j₀, ∃ hi : N k ≤ ψ i,
                      ∀ s ∈ Icc (-(((k + 1 : ℕ) : ℝ) / ((k + 2 : ℕ) : ℝ) * T)) 0,
                        metricDerivNormSupOn K p
                          (localPullMetric (h k (f (ψ i)) s) (φ k (ψ i) hi) (hφ k (ψ i) hi))
                          ((G s).restrictOpen (V k)) (P.metric.restrictOpen (V k)) < η := by
  intro X
  obtain ⟨hc, hcT, hcmono, hcex⟩ := depth_schedule_facts hT
  obtain ⟨W, h, hblock, hlip, -, hlow, hpinchW, hncW, f, hf, P, F, hCd, hPc, hconn, hballF, V, N,
    hV, hVF, φ, hφ, hφF, Gloc, hG0, hG, hGcompat, ψ, hψ, hconv⟩ :=
    exists_local_pointed_flow_limits_with_time_lipschitz_survivor_maps_of_depth_schedule H t y R
      hR hRlim (fun _ => T) (fun _ => hT)
      (fun k => ⟨K, hK, htraced ((k + 3 : ℕ) : ℝ) (by positivity)⟩) hκ hρ hsliver hnc hPhi hpinch
  obtain ⟨hVmono, hVcover⟩ := monotone_and_cover_of_riemannianBallOf_eq hconn hV
  obtain ⟨G, hGsol, hGres⟩ := exists_openClosed_solution_of_compatible_open_cover hT V hVmono
    hVcover (fun k => ((k + 1 : ℕ) : ℝ) / ((k + 2 : ℕ) : ℝ) * T) (fun k => (hc k).le) hcmono
    hcex Gloc hG hGcompat
  have hG0' : G 0 = P.metric := by
    apply SmoothRiemannianMetric.ext_inner
    intro x v w
    obtain ⟨k, hk⟩ := hVcover x
    have heq := (hGres k 0 ⟨neg_nonpos.mpr (hc k).le, le_rfl⟩).trans (hG0 k)
    exact congrArg (fun q : SmoothRiemannianMetric ThreeModel (V k) => q.inner ⟨x, hk⟩ v w) heq
  have hconvG : ∀ k (K : Set (V k)), IsCompact K → ∀ p : ℕ, ∀ η : ℝ, 0 < η →
      ∃ j₀ : ℕ, ∀ i ≥ j₀, ∃ hi : N k ≤ ψ i,
        ∀ s ∈ Icc (-(((k + 1 : ℕ) : ℝ) / ((k + 2 : ℕ) : ℝ) * T)) 0,
          metricDerivNormSupOn K p
            (localPullMetric (h k (f (ψ i)) s) (φ k (ψ i) hi) (hφ k (ψ i) hi))
            ((G s).restrictOpen (V k)) (P.metric.restrictOpen (V k)) < η := by
    intro k K hK p η hη
    obtain ⟨j₀, hj₀⟩ := hconv k K hK p η hη
    refine ⟨j₀, fun i hi => ?_⟩
    obtain ⟨hi', hb⟩ := hj₀ i hi
    refine ⟨hi', fun s hs => ?_⟩
    rw [hGres k s hs]
    exact hb s hs
  have hcT' : ∀ s ∈ Ioc (-T) 0, ∃ k : ℕ, -(((k + 1 : ℕ) : ℝ) / ((k + 2 : ℕ) : ℝ) * T) < s := by
    intro s hs
    obtain ⟨k, hk⟩ := hcex (-s) (by linarith [hs.1])
    exact ⟨k, by linarith⟩
  have hpinchc : ∀ k : ℕ, ∀ᶠ n in atTop,
      ∀ s ∈ Icc (-(((k + 1 : ℕ) : ℝ) / ((k + 2 : ℕ) : ℝ) * T)) 0, ∀ x : W k n,
        curvatureOperatorLowerBoundAt (h k n s) x (metricAlgebraicCurvatureTensorAt (h k n s) x)
          (Perelman.rescalePinchingFunction (R n) Phi (metricScalarAt (h k n s) x)) := by
    intro k
    filter_upwards [hpinchW k] with n hn s hs x
    exact hn s ⟨by linarith [hs.1, hcT k], hs.2⟩ x
  have hcone := curvatureOperator_nonnegative_of_local_pinching_limit_on_window hf hVmono hVcover
    hcmono hcT' hψ hconvG hRlim hPhi hpinchc
  have hcompl0 : RiemannianMetricComplete (G 0) := by
    rw [hG0']
    exact ⟨CheegerGromovCompactness.MetricComplete.complete P hPc⟩
  have hcomplete : ∀ s ∈ Ioc (-T) 0, RiemannianMetricComplete (G s) := fun s hs =>
    complete_at_earlier_time_of_ricci_nonnegative
      ({ base.metric := G } : SolutionOn (I := ThreeModel) (M := P.M)
        (RealTimeInterval.openClosed (-T) 0 0 ⟨neg_lt_zero.mpr hT, le_rfl⟩)) hGsol
      (a := s) (b := 0) (fun r hr => ⟨hs.1.trans_le hr.1, hr.2⟩)
      (fun r hr => ⟨hs.1.trans hr.1, hr.2⟩)
      (fun r hr x v => metricRicciAt_nonnegative_of_curvatureOperator_nonnegative
        (G r) x (hcone r ⟨hs.1.trans hr.1, hr.2.le⟩ x) v) hcompl0 ⟨le_rfl, hs.2⟩
  have hRm : ∀ k : ℕ, ∀ᶠ n in atTop, ∀ s ∈ Icc (-T) 0, ∀ x : W k n,
      curvDerivNormSq 0 (h k n s) x ≤ K ^ 2 := by
    intro k
    filter_upwards [hblock k, htraced ((k + 3 : ℕ) : ℝ) (by positivity)] with n hn htr
    obtain ⟨hWset, -, -, ⟨a, hat, ha, fs, hfs, -, hcross, hlast, hp⟩, -⟩ := hn
    refine curvDerivNormSq_zero_le_of_survivor_maps_of_isTracedRegion (H n) (t n) (y n) (hR n)
      htr (fun x => ?_) a hat ha fs hfs hcross hlast hp
    have hx : x.val ∈ (W k n : Set (X.obj n).M) := x.2
    rw [hWset] at hx
    rwa [ObservedHistory.riemannianBallOf_scaleMetric_eq _ (hR n)] at hx
  have hRmG : ∀ s ∈ Ioc (-T) 0, ∀ x : P.M,
      Tensor0SBundle.normSq0S (G s) x 4 (metricRm04At (G s) x) ≤ K ^ 2 :=
    normSq0S_metricRm04At_le_of_local_flow_limit_on_window hf hVmono hVcover hcmono hcT' hψ
      hconvG fun k => (hRm k).mono fun n hn s hs x => hn s ⟨by linarith [hs.1, hcT k], hs.2⟩ x
  have hbase : (∀ n, metricScalarAt ((H n).stageMetric ((H n).activeStage (t n)) (t n)) (y n) =
      R n) → metricScalarAt P.metric P.basepoint = 1 := by
    intro hscal
    refine metricScalarAt_basepoint_eq_of_local_flow_limit_on_window hf F hV hφF
      (c := fun k => ((k + 1 : ℕ) : ℝ) / ((k + 2 : ℕ) : ℝ) * T) (hc 0).le hG0' hψ hconvG ?_ ?_
    · filter_upwards [hblock 0] with n hn z
      obtain ⟨-, -, h0eq, -⟩ := hn
      have hdom : (t n : ℝ) + 0 / R n ∈ (H n).stageDomain ((H n).activeStage (t n)) := by
        simpa using (H n).activeStage_mem (t n)
      have h0 := h0eq 0 ⟨neg_nonpos.mpr hT.le, le_rfl⟩ hdom
      rw [zero_div, add_zero] at h0
      rw [h0, metricScalarAt_scaleMetric, metricScalarAt_restrictOpen]
      change _ = metricScalarAt (scaleMetric (R n) (hR n) _) z.val
      rw [metricScalarAt_scaleMetric]
    · intro n
      change metricScalarAt (scaleMetric (R n) (hR n) _) (y n) = 1
      rw [metricScalarAt_scaleMetric, hscal, inv_mul_cancel₀ (hR n).ne']
  have hkappa : ∀ ρ' : ℝ, 0 < ρ' → Perelman.ParabolicallyKappaNoncollapsedBelowScale
      ({ base.metric := G } : SolutionOn (I := ThreeModel) (M := P.M)
        (RealTimeInterval.openClosed (-T) 0 0 ⟨neg_lt_zero.mpr hT, le_rfl⟩)) (κ / 250) ρ' := by
    intro ρ' hρ'
    refine parabolicallyKappaNoncollapsedBelowScale_of_local_flow_limit_on_openClosed hT
      (fun _ => T) (fun k => ((k + 1 : ℕ) : ℝ) / ((k + 2 : ℕ) : ℝ) * T) hc hcT hcT hcmono hcex
      (fun k => (hblock k).mono fun n hn => hn.2.1) hκ (radii := fun n => ρ * Real.sqrt (R n))
      ?_ hncW hf F hVmono hVcover hVF φ hφ hφF hGsol hcomplete hψ hconvG ρ' hρ'
    exact Tendsto.const_mul_atTop hρ (Real.tendsto_sqrt_atTop.comp hRlim)
  exact ⟨W, h, hblock, hlip, hRm, hlow, hpinchW, f, hf, P, F, hCd, hPc, hconn, hballF, V, N, hV,
    hVF, φ, hφ, hφF, G, hG0', hGsol, hcone, hcomplete, hRmG, hbase, hkappa, ψ, hψ, hconvG⟩

end ObservedHistory

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

end
