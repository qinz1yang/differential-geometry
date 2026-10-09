import Batteries.Tactic.OpenPrivate
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.CrossingAncientLimitSpatial
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.AncientLimitSurvivorCanonicalWitnessC11X

/-!
# CrossingAncientLimitSpatialC11X（S-CH11-EXT2，extension of 已跟踪宿主
`Topology/CrossingAncientLimitSpatial.lean`）

astra 新增 `exists_eventually_canonicalWitness_survivor_of_isTracedRegion_at_closed_time` 与
`exists_eventually_spatialCanonicalWitness_of_isTracedRegion_at_closed_time`（traced region
的闭终端面，
允许 ambient point 恰在 surgery birth 时间）。旧两个定理在 donor 里改写成它们的推论；W8 宿主保持
不变。本文件逐字抄写两个新增定理；它们用的 `eventually_exists_…_normalized_local_flow_limit` 来自
`AncientLimitSurvivorCanonicalWitnessC11X`。直接用户：`UniformBirthSpatialCanonicalWitness`
（EXT1 的 port）。
-/

set_option autoImplicit false

noncomputable section

open Set Filter TopologicalSpace
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.CheegerGromovCompactness
open scoped Manifold ContDiff Topology NNReal ENNReal

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

open Perelman.CanonicalNeighborhood.FiniteHorn (SpatialCanonicalWitness CanonicalWitness I3
  eventually_exists_canonicalWitness_survivor_of_normalized_local_flow_limit
  exists_spatialCanonicalWitness_of_canonicalWitness_restrictOpen
  isAncientKappaSolution_flowOfMetric_of_curvatureOperator_nonnegative)

open private ObservedHistory.mem_Icc_of_mem_window from
  DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.TracedRegionAncientLimit

namespace ObservedHistory

universe u

private local instance {M : Type u} [TopologicalSpace M] [ChartedSpace ThreeSpace M]
    [SigmaCompactSpace M] (U : Opens M) : SigmaCompactSpace U :=
  isSigmaCompact_iff_sigmaCompactSpace.mp
    (Geometry.isSigmaCompact_of_isOpen ThreeModel U.isOpen)

attribute [local instance] PointedRiemannianManifold.topology PointedRiemannianManifold.charted
  PointedRiemannianManifold.smooth PointedRiemannianManifold.t2
  PointedRiemannianManifold.sigmaCompact PointedRiemannianManifold.t2TangentBundle

/-- The traced local flows include their closed terminal face, so ambient
surgery-birth times are allowed. No backward existence of the whole post-event
stage is asserted or needed. -/
theorem exists_eventually_canonicalWitness_survivor_of_isTracedRegion_at_closed_time :
    ∃ epsW : ℝ, 0 < epsW ∧ ∀ ε : ℝ, 0 < ε → ε < 1 / 11 → ε ≤ epsW →
    ∃ C : ℝ, 1 ≤ C ∧
    ∀ (H : ℕ → ObservedHistory.{u}) (t : ∀ n, Icc (0 : ℝ) (H n).horizon)
      (y : ∀ n, ((H n).stageAt (t n)).Carrier) (R : ℕ → ℝ),
      (hR : ∀ n, 0 < R n) →
      (∀ n, metricScalarAt ((H n).stageMetric ((H n).activeStage (t n)) (t n)) (y n) = R n) →
      Tendsto R atTop atTop →
      (∀ A T : ℝ, 0 < A → 0 < T → ∃ K : ℝ, 0 ≤ K ∧ ∀ᶠ n in atTop,
        (H n).isTracedRegion (t n) (y n) (A / Real.sqrt (R n)) (T / R n) (K * R n)) →
      ∀ {κ ρ : ℝ}, 0 < κ → 0 < ρ → ∀ {t₀ : ℕ → ℝ},
      Tendsto (fun n => R n * ((t n : ℝ) - t₀ n)) atTop (𝓝 0) →
      (∀ n (v : Icc (0 : ℝ) (H n).horizon) (p : ((H n).stageAt v).Carrier) (r : ℝ),
        (v : ℝ) < t₀ n → r ≤ ρ → (H n).isParabolicallyRmControlledBall v p r →
        ENNReal.ofReal κ * ENNReal.ofReal r ^ 3 ≤
          Integral.Measure.riemannianVolumeMeasure ThreeModel ((H n).stageAt v).Carrier
            ((H n).stageMetric ((H n).activeStage v) v)
            (riemannianBallOf ((H n).stageMetric ((H n).activeStage v) v) p r)) →
      ∀ {Phi : ℝ → ℝ}, Perelman.AdmissiblePinchingFunction Phi →
      (∀ n (v : Icc (0 : ℝ) (H n).horizon), (v : ℝ) ≤ t n →
        ∀ x : ((H n).stageAt v).Carrier,
          curvatureOperatorLowerBoundAt ((H n).stageMetric ((H n).activeStage v) v) x
            (metricAlgebraicCurvatureTensorAt ((H n).stageMetric ((H n).activeStage v) v) x)
            (Phi (metricScalarAt ((H n).stageMetric ((H n).activeStage v) v) x))) →
      ∀ {C1s C2s Cs Cq : ℝ} {Ctime : ℝ≥0} {qs qcan : ℕ → ℝ},
      (∀ n, qs n ≤ Cs * R n) → (∀ n, qcan n ≤ Cq * R n) →
      (∀ n (v : Icc (0 : ℝ) (H n).horizon), (v : ℝ) < t₀ n →
        (H n).time ((H n).activeStage v) < v → ∀ p : ((H n).stageAt v).Carrier,
          qs n < metricScalarAt ((H n).stageMetric ((H n).activeStage v) v) p →
          ∃ W : SpatialCanonicalWitness ((H n).stageMetric ((H n).activeStage v) v) ε C1s C2s p,
            W.capTubeHasNeckChart ε) →
      (∀ n (v : Icc (0 : ℝ) (H n).horizon), (v : ℝ) < t₀ n →
        (H n).time ((H n).activeStage v) < v → ∀ p : ((H n).stageAt v).Carrier,
          qcan n < metricScalarAt ((H n).stageMetric ((H n).activeStage v) v) p →
          |derivWithin (fun v' => metricScalarAt ((H n).stageMetric ((H n).activeStage v) v') p)
            (Iic (v : ℝ)) v| ≤
            Ctime * metricScalarAt ((H n).stageMetric ((H n).activeStage v) v) p ^ 2) →
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
        ∀ σ ∈ Icc (-((k + 1 : ℕ) : ℝ)) 0, (t n : ℝ) + σ / R n < t₀ n → ∀ z : W k n,
          ∀ r : ℝ, 0 < r →
          r ≤ ρ * Real.sqrt (R n) → Icc (σ - r ^ 2) σ ⊆ Icc (-((k + 2 : ℕ) : ℝ)) 0 →
          IsCompact (riemannianClosedBallOf (h k n σ) z r) →
          (∀ s ∈ Icc (σ - r ^ 2) σ, ∀ w ∈ riemannianBallOf (h k n σ) z r,
            r ^ 4 * curvDerivNormSq 0 (h k n s) w ≤ 1) →
          ENNReal.ofReal (κ * r ^ 3) ≤
            Integral.Measure.riemannianVolumeMeasure ThreeModel (W k n) (h k n σ)
              (riemannianBallOf (h k n σ) z r)) ∧
      ∃ ψ : ℕ → ℕ, StrictMono ψ ∧ ∃ k : ℕ, 2 * C + 1 < ((k + 3 : ℕ) : ℝ) ∧ ∀ᶠ i in atTop,
        ∃ hy : (X.obj (ψ i)).basepoint ∈ W k (ψ i),
        ∃ K : CanonicalWitness ({ base.metric := h k (ψ i) } :
            SolutionOn (I := ThreeModel) (M := W k (ψ i))
              (RealTimeInterval.closed (-((k + 2 : ℕ) : ℝ)) 0 (neg_nonpos.mpr (Nat.cast_nonneg _))))
            ε C C ⟨_, hy⟩ 0, K.capTubeHasNeckChart ε := by
  obtain ⟨epsW, hepsW, hB13⟩ :=
    exists_bounded_ancient_pointed_flow_limit_of_spatially_canonical_before.{u}
  refine ⟨epsW, hepsW, fun ε hε hsmall hεW => ?_⟩
  obtain ⟨C, hC, hB8⟩ :=
    eventually_exists_canonicalWitness_survivor_of_normalized_local_flow_limit.{u} hε hsmall
  refine ⟨C, hC, ?_⟩
  intro H t y R hR hscal hRlim htraced κ ρ hκ hρ t₀ hsliver hnc Phi hPhi hpinch
    C1s C2s Cs Cq Ctime qs qcan hqs hqcan hwit hderiv X
  obtain ⟨W, h, hblock, -, -, -, f, hf, P, F, -, hPc, hconn, hballF, V, N, hV, hVF, φ, hφ, hφF, G,
    hG0, hG, ψ, hψ, hconv, hκG, CB, hCB⟩ :=
    hB13 H t y R hR hRlim htraced hκ hρ hsliver hnc hPhi hpinch hε hεW hqs hqcan hwit hderiv
  have hbaseX : ∀ n, metricScalarAt (X.obj n).metric (X.obj n).basepoint = 1 := by
    intro n
    change metricScalarAt (scaleMetric (R n) (hR n)
      ((H n).stageMetric ((H n).activeStage (t n)) (t n))) (y n) = 1
    rw [metricScalarAt_scaleMetric, hscal n, inv_mul_cancel₀ (hR n).ne']
  have hend : ∀ k : ℕ, ∀ᶠ n in atTop,
      (W k n : Set (X.obj n).M) =
        riemannianBallOf (X.obj n).metric (X.obj n).basepoint ((k + 3 : ℕ) : ℝ) ∧
      h k n 0 = (X.obj n).metric.restrictOpen (W k n) := by
    intro k
    filter_upwards [hblock k] with n hn
    refine ⟨hn.1, ?_⟩
    have hdom0 : (t n : ℝ) + 0 / R n ∈ (H n).stageDomain ((H n).activeStage (t n)) := by
      simpa using (H n).activeStage_mem (t n)
    have hm := hn.2.2.1 0 ⟨neg_nonpos.mpr (Nat.cast_nonneg _), le_rfl⟩ hdom0
    rw [zero_div, add_zero] at hm
    rw [hm]
    apply DifferentialGeometry.SmoothRiemannianMetric.ext_inner
    intro x v w
    rfl
  have hpinchW : ∀ k : ℕ, ∀ᶠ n in atTop, ∀ q ∈ Icc (-((k + 1 : ℕ) : ℝ)) 0,
      ∀ x : W k n, curvatureOperatorLowerBoundAt (h k n q) x
        (metricAlgebraicCurvatureTensorAt (h k n q) x)
        (Perelman.rescalePinchingFunction (R n) Phi (metricScalarAt (h k n q) x)) := by
    intro k
    filter_upwards [hblock k] with n hn q hq x
    obtain ⟨-, -, -, ⟨a, -, ha, fs, hfs, -, -, -, hp⟩, -⟩ := hn
    have hqθ : q ∈ Icc (-(2 * ((k + 2 : ℕ) : ℝ))) 0 :=
      ⟨by have := hq.1; push_cast at this ⊢; linarith, hq.2⟩
    have hv := ObservedHistory.mem_Icc_of_mem_window (hR n) ha hqθ
    let v : Icc (0 : ℝ) (H n).horizon :=
      ⟨(t n : ℝ) + q / R n, a.2.1.trans hv.1, hv.2.trans (t n).2.2⟩
    let j : (H n).StageInterval ((H n).activeStage a) ((H n).activeStage (t n)) :=
      ⟨(H n).activeStage v, (H n).activeStage_mono (show a ≤ v from hv.1),
        (H n).activeStage_mono (show v ≤ t n from hv.2)⟩
    have hq' := hp q hqθ j ((H n).activeStage_mem v)
    have hpull := (curvatureOperatorLowerBoundAt_localPullMetric_iff _ (fs j) (hfs j) x _).mpr
      (hpinch n v hv.2 (fs j x))
    rw [hq', curvatureOperatorLowerBoundAt_scaleMetric_iff, metricScalarAt_scaleMetric,
      metricScalarAt_localPull]
    unfold Perelman.rescalePinchingFunction
    simp only [mul_inv_cancel_left₀ (hR n).ne']
    exact hpull
  obtain ⟨hcone, hcomplete⟩ := ancient_pointed_flow_limit_curvatureOperator_nonnegative_and_complete
    hf hPc hconn hV hG0 hG hψ hconv hRlim hPhi hpinchW
  have hbaseP : metricScalarAt P.metric P.basepoint = 1 := by
    refine metricScalarAt_basepoint_eq_of_local_flow_limit hf F hV hφF hG0 hψ hconv ?_ ?_
    · intro k
      filter_upwards [hblock k] with n hn z
      have hdom0 : (t n : ℝ) + 0 / R n ∈ (H n).stageDomain ((H n).activeStage (t n)) := by
        simpa using (H n).activeStage_mem (t n)
      rw [hn.2.2.1 0 ⟨neg_nonpos.mpr (Nat.cast_nonneg _), le_rfl⟩ hdom0, zero_div, add_zero,
        metricScalarAt_scaleMetric, metricScalarAt_restrictOpen]
      exact (metricScalarAt_scaleMetric (R n) (hR n) _ _).symm
    · intro n
      change metricScalarAt (scaleMetric (R n) (hR n)
        ((H n).stageMetric ((H n).activeStage (t n)) (t n))) (y n) = 1
      rw [metricScalarAt_scaleMetric, hscal n, inv_mul_cancel₀ (hR n).ne']
  obtain ⟨o⟩ := haveI := hconn
    nonempty_tangentOrientationSection_of_pointedConvergence F
      (fun n => ((H n).stageAt (t n)).orientation) hV hVF
  obtain ⟨hanc, hbase⟩ := isAncientKappaSolution_flowOfMetric_of_curvatureOperator_nonnegative
    P hG hG0 hconn hcomplete hcone hCB (div_pos hκ (by norm_num)) hκG hbaseP
  obtain ⟨k, hk, hK⟩ := hB8 X hbaseX W h
    (fun k => (hblock k).mono fun n hn => hn.2.1) hend
    f hf P F hPc hballF V N hV hVF φ hφ hφF G hG hG0 ψ hψ hconv _ hanc hbase o
  exact ⟨W, h, hblock, f ∘ ψ, hf.comp hψ, k, hk, hK⟩


/-- Spatial canonicality from an actual traced region also holds at surgery
birth. The same postmetric is recovered from the local flow's zero slice. This
is conditional on traced regions of every required spatial and temporal size. -/
theorem exists_eventually_spatialCanonicalWitness_of_isTracedRegion_at_closed_time :
    ∃ epsW : ℝ, 0 < epsW ∧ ∀ ε : ℝ, 0 < ε → ε < 1 / 11 → ε ≤ epsW →
    ∃ C : ℝ, 1 ≤ C ∧
    ∀ (H : ℕ → ObservedHistory.{u}) (t : ∀ n, Icc (0 : ℝ) (H n).horizon)
      (y : ∀ n, ((H n).stageAt (t n)).Carrier) (R : ℕ → ℝ),
      (∀ n, 0 < R n) →
      (∀ n, metricScalarAt ((H n).stageMetric ((H n).activeStage (t n)) (t n)) (y n) = R n) →
      Tendsto R atTop atTop →
      (∀ A T : ℝ, 0 < A → 0 < T → ∃ K : ℝ, 0 ≤ K ∧ ∀ᶠ n in atTop,
        (H n).isTracedRegion (t n) (y n) (A / Real.sqrt (R n)) (T / R n) (K * R n)) →
      ∀ {κ ρ : ℝ}, 0 < κ → 0 < ρ → ∀ {t₀ : ℕ → ℝ},
      Tendsto (fun n => R n * ((t n : ℝ) - t₀ n)) atTop (𝓝 0) →
      (∀ n (v : Icc (0 : ℝ) (H n).horizon) (p : ((H n).stageAt v).Carrier) (r : ℝ),
        (v : ℝ) < t₀ n → r ≤ ρ → (H n).isParabolicallyRmControlledBall v p r →
        ENNReal.ofReal κ * ENNReal.ofReal r ^ 3 ≤
          Integral.Measure.riemannianVolumeMeasure ThreeModel ((H n).stageAt v).Carrier
            ((H n).stageMetric ((H n).activeStage v) v)
            (riemannianBallOf ((H n).stageMetric ((H n).activeStage v) v) p r)) →
      ∀ {Phi : ℝ → ℝ}, Perelman.AdmissiblePinchingFunction Phi →
      (∀ n (v : Icc (0 : ℝ) (H n).horizon), (v : ℝ) ≤ t n →
        ∀ x : ((H n).stageAt v).Carrier,
          curvatureOperatorLowerBoundAt ((H n).stageMetric ((H n).activeStage v) v) x
            (metricAlgebraicCurvatureTensorAt ((H n).stageMetric ((H n).activeStage v) v) x)
            (Phi (metricScalarAt ((H n).stageMetric ((H n).activeStage v) v) x))) →
      ∀ {C1s C2s Cs Cq : ℝ} {Ctime : ℝ≥0} {qs qcan : ℕ → ℝ},
      (∀ n, qs n ≤ Cs * R n) → (∀ n, qcan n ≤ Cq * R n) →
      (∀ n (v : Icc (0 : ℝ) (H n).horizon), (v : ℝ) < t₀ n →
        (H n).time ((H n).activeStage v) < v → ∀ p : ((H n).stageAt v).Carrier,
          qs n < metricScalarAt ((H n).stageMetric ((H n).activeStage v) v) p →
          ∃ W : SpatialCanonicalWitness ((H n).stageMetric ((H n).activeStage v) v) ε C1s C2s p,
            W.capTubeHasNeckChart ε) →
      (∀ n (v : Icc (0 : ℝ) (H n).horizon), (v : ℝ) < t₀ n →
        (H n).time ((H n).activeStage v) < v → ∀ p : ((H n).stageAt v).Carrier,
          qcan n < metricScalarAt ((H n).stageMetric ((H n).activeStage v) v) p →
          |derivWithin (fun v' => metricScalarAt ((H n).stageMetric ((H n).activeStage v) v') p)
            (Iic (v : ℝ)) v| ≤
            Ctime * metricScalarAt ((H n).stageMetric ((H n).activeStage v) v) p ^ 2) →
      ∃ ψ : ℕ → ℕ, StrictMono ψ ∧ ∀ᶠ i in atTop,
        ∃ Wt : SpatialCanonicalWitness
            ((H (ψ i)).stageMetric ((H (ψ i)).activeStage (t (ψ i))) (t (ψ i))) ε C C (y (ψ i)),
          Wt.capTubeHasNeckChart ε := by
  obtain ⟨epsW, hepsW, hmain⟩ := exists_eventually_canonicalWitness_survivor_of_isTracedRegion_at_closed_time.{u}
  refine ⟨epsW, hepsW, fun ε hε hsmall hεW => ?_⟩
  obtain ⟨C, hC, hmain⟩ := hmain ε hε hsmall hεW
  refine ⟨C, hC, ?_⟩
  intro H t y R hR hscal hRlim htraced κ ρ hκ hρ t₀ hsliver hnc Phi hPhi hpinch
    C1s C2s Cs Cq Ctime qs qcan hqs hqcan hwit hderiv
  obtain ⟨W, h, hblock, ψ, hψ, k, hk, hK⟩ := hmain H t y R hR hscal hRlim htraced hκ hρ hsliver
    hnc hPhi hpinch hqs hqcan hwit hderiv
  refine ⟨ψ, hψ, ?_⟩
  filter_upwards [hK, hψ.tendsto_atTop.eventually (hblock k)] with i hKi hn
  obtain ⟨hy, K, hKc⟩ := hKi
  have hdom0 : (t (ψ i) : ℝ) + 0 / R (ψ i) ∈
      (H (ψ i)).stageDomain ((H (ψ i)).activeStage (t (ψ i))) := by
    simpa using (H (ψ i)).activeStage_mem (t (ψ i))
  have hh0 := hn.2.2.1 0 ⟨neg_nonpos.mpr (Nat.cast_nonneg _), le_rfl⟩ hdom0
  rw [zero_div, add_zero] at hh0
  have hball : riemannianClosedBallOf
      (scaleMetric (R (ψ i)) (hR (ψ i))
        ((H (ψ i)).stageMetric ((H (ψ i)).activeStage (t (ψ i))) (t (ψ i)))) (y (ψ i))
      (2 * C + 1) ⊆ (W k (ψ i) : Set ((H (ψ i)).stageAt (t (ψ i))).Carrier) := by
    rw [hn.1]
    intro z hz
    exact lt_of_le_of_lt hz ((ENNReal.ofReal_lt_ofReal_iff (by positivity)).2 hk)
  obtain ⟨Wt, hWt, -⟩ := exists_spatialCanonicalWitness_of_canonicalWitness_restrictOpen
    ((H (ψ i)).stageMetric ((H (ψ i)).activeStage (t (ψ i))) (t (ψ i))) (hR (ψ i)) (W k (ψ i))
    ⟨y (ψ i), hy⟩ (hscal (ψ i)) (neg_nonpos.mpr (Nat.cast_nonneg _)) (h k (ψ i)) hh0 K hKc hball
  exact ⟨Wt, hWt⟩

end ObservedHistory

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
