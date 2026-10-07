import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.TracedRegionAncientLimitScalarBound
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.AncientLimitSurvivorCanonicalWitness
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.SurvivorBlockStrongNeck
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.AncientPointedFlowLimitCurvature
import DifferentialGeometry.Geometry.Flow.RicciFlow.Compactness.Limits.PointedLimitOrientation
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.AncientPointedFlowLimitBaseScalar
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.External.StrongNeckFullTransportC12X

/-!
# Crossing blow-up limit with full history necks (C12X, S16 G2d)

Untruncated `exists_eventually_strong_spatialCanonicalWitness_of_isTracedRegion`
(`Surgery/Topology/CrossingAncientLimitStrong`): the proof is the tree proof verbatim except the
last step, which uses `historyStrongNeckFull_of_survivor_strongNeck_C12X` (no truncation) and
therefore produces `HistoryStrongNeckFull_C12X` at the witness accuracy `ε` itself (no `ε₁`).
The accuracy threshold is the named constant `crossingStrongEpsW_C12X` (the `epsW` of
`exists_bounded_ancient_pointed_flow_limit_of_spatially_canonical_before`).
-/

set_option autoImplicit false

noncomputable section

open Set Filter TopologicalSpace
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.CheegerGromovCompactness
open scoped Manifold ContDiff Topology NNReal ENNReal

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

open Perelman.CanonicalNeighborhood.FiniteHorn (SpatialCanonicalWitness CanonicalWitness I3
  eventually_exists_canonicalWitness_survivor_of_ancient_pointed_flow_limit
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

/-- Accuracy threshold of the crossing blow-up (the `epsW` of
`exists_bounded_ancient_pointed_flow_limit_of_spatially_canonical_before`). -/
def crossingStrongEpsW_C12X : ℝ :=
  Classical.choose exists_bounded_ancient_pointed_flow_limit_of_spatially_canonical_before.{u}

theorem crossingStrongEpsW_C12X_pos : 0 < crossingStrongEpsW_C12X.{u} :=
  (Classical.choose_spec
    exists_bounded_ancient_pointed_flow_limit_of_spatially_canonical_before.{u}).1

/-- Untruncated `exists_eventually_strong_spatialCanonicalWitness_of_isTracedRegion`, with the
neck clause at the witness accuracy `ε`. -/
theorem exists_eventually_strong_spatialCanonicalWitnessFull_of_isTracedRegion_C12X :
    ∀ ε : ℝ, 0 < ε → ε < 1 / 11 → ε ≤ crossingStrongEpsW_C12X.{u} →
    ∃ C : ℝ, 1 ≤ C ∧
    ∀ (H : ℕ → ObservedHistory.{u}) (t : ∀ n, Icc (0 : ℝ) (H n).horizon)
      (y : ∀ n, ((H n).stageAt (t n)).Carrier) (R : ℕ → ℝ),
      (∀ n, 0 < R n) →
      (∀ n, metricScalarAt ((H n).stageMetric ((H n).activeStage (t n)) (t n)) (y n) = R n) →
      Tendsto R atTop atTop →
      (∀ n, (H n).time ((H n).activeStage (t n)) < t n) →
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
      ∀ (s : ℕ → ℝ) (Gs : ∀ n, ((H n).stage ((H n).activeStage (t n))).IncomingSlab
        ((H n).time ((H n).activeStage (t n))) (s n)),
        (∀ n, (t n : ℝ) < s n) →
        (∀ n, ∀ τ ∈ Icc ((H n).time ((H n).activeStage (t n))) (t n : ℝ),
          (Gs n).flow.base.metric τ = (H n).stageMetric ((H n).activeStage (t n)) τ) →
      ∃ ψ : ℕ → ℕ, StrictMono ψ ∧ ∀ᶠ i in atTop,
        ∃ Wt : SpatialCanonicalWitness
            ((H (ψ i)).stageMetric ((H (ψ i)).activeStage (t (ψ i))) (t (ψ i))) ε C C (y (ψ i)),
          Wt.capTubeHasNeckChart ε ∧
          ((∃ n, Wt.alternative = .neck n) →
            (H (ψ i)).HistoryStrongNeckFull_C12X ((H (ψ i)).activeStage (t (ψ i))) (Gs (ψ i)) ε
              (y (ψ i)) (t (ψ i))) := by
  intro ε hε hsmall hεW
  have hB13 := (Classical.choose_spec
    exists_bounded_ancient_pointed_flow_limit_of_spatially_canonical_before.{u}).2
  obtain ⟨C, hC, hB8⟩ :=
    eventually_exists_canonicalWitness_survivor_of_ancient_pointed_flow_limit.{u} hε hsmall
  refine ⟨C, hC, ?_⟩
  intro H t y R hR hscal hRlim hlt htraced κ ρ hκ hρ t₀ hsliver hnc Phi hPhi hpinch
    C1s C2s Cs Cq Ctime qs qcan hqs hqcan hwit hderiv s Gs hts hGs
  obtain ⟨W, h, hblock, -, -, -, f, hf, P, F, -, hPc, hconn, hballF, V, N, hV, hVF, φ, hφ, hφF, G,
    hG0, hG, ψ, hψ, hconv, hκG, CB, hCB⟩ :=
    hB13 H t y R hR hRlim htraced hκ hρ hsliver hnc hPhi hpinch hε hεW hqs hqcan hwit hderiv
  have hdom : ∀ n, ∀ τ ∈ Icc ((H n).time ((H n).activeStage (t n))) (t n : ℝ),
      τ ∈ (H n).stageDomain ((H n).activeStage (t n)) := by
    intro n τ hτ
    rcases hτ.1.eq_or_lt with he | hlo
    · rw [← he]
      exact (H n).time_mem_stageDomain _
    rcases hτ.2.eq_or_lt with he | hhi
    · rw [he]
      exact (H n).activeStage_mem (t n)
    exact (H n).mem_stageDomain_of_mem_Ioo ⟨hlo, hhi.trans_le
      ((H n).le_stageEndTime_of_mem_stageDomain ((H n).activeStage_mem (t n)))⟩
  have hSR : ∀ n, ((H n).closedPrefixAt (t n) (hlt n)).flow.scalar (t n) (y n) = R n := by
    intro n
    change metricScalarAt (((H n).closedPrefixAt (t n) (hlt n)).flow.base.metric (t n)) (y n) =
      R n
    rw [(H n).closedPrefixAt_metric]
    exact hscal n
  have hX : ∀ n, scaleMetric (R n) (hR n) ((H n).stageMetric ((H n).activeStage (t n)) (t n)) =
      scaleMetric (R n) (hR n) (((H n).closedPrefixAt (t n) (hlt n)).flow.base.metric (t n)) :=
    fun n => by rw [(H n).closedPrefixAt_metric]
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
  let X : PointedRiemannianSeq.{u, 0, 0} ThreeModel :=
    { obj := fun n =>
        { M := ((H n).stageAt (t n)).Carrier
          basepoint := y n
          metric := scaleMetric (R n) (hR n)
            ((H n).stageMetric ((H n).activeStage (t n)) (t n)) } }
  let D : ℕ → RealTimeInterval := fun n =>
    RealTimeInterval.closed _ _ ((H n).closedPrefixAt (t n) (hlt n)).lt.le
  have hleft : ∀ n, ∃ η : ℝ, 0 < η ∧ Icc ((t n : ℝ) - η) (t n) ⊆ (D n).carrier := fun n =>
    ⟨(t n : ℝ) - (H n).time ((H n).activeStage (t n)), sub_pos.mpr (hlt n),
      fun τ hτ => ⟨by linarith [hτ.1], hτ.2⟩⟩
  choose Nb hNb using fun k => eventually_atTop.1 (hblock k)
  have hsf : ∀ k n, Nb k ≤ n → ∃ (first : Fin ((H n).eventCount + 1))
      (hle : first ≤ (H n).activeStage (t n))
      (hWU : ∀ x : W k n, x.val ∈ (H n).backwardSurvivorDomain first ((H n).activeStage (t n)) hle)
      (hι : IsLocalDiffeomorph ThreeModel ThreeModel ∞ (fun x : W k n =>
        (⟨x.val, hWU x⟩ : (H n).backwardSurvivorDomain first ((H n).activeStage (t n)) hle)))
      (gflow : ℝ → SmoothRiemannianMetric ThreeModel
        ((H n).backwardSurvivorDomain first ((H n).activeStage (t n)) hle)),
      (H n).time first ≤ (t n : ℝ) - 2 * ((k + 2 : ℕ) : ℝ) / R n ∧
      (∀ (j : Fin (H n).eventCount) (hf : first ≤ j.castSucc)
        (hl : j.succ ≤ (H n).activeStage (t n)),
        ∀ τ ∈ Icc ((H n).time j.castSucc) ((H n).time j.succ),
          gflow τ =
            (H n).backwardSurvivorSlabMetric first ((H n).activeStage (t n)) hle j hf hl τ) ∧
      (∀ τ ∈ Ico ((H n).time ((H n).activeStage (t n))) (s n),
        gflow τ = ((Gs n).flow.base.metric τ).restrictOpen
          ((H n).backwardSurvivorDomain first ((H n).activeStage (t n)) hle)) ∧
      IsSolutionOn ({ base := { metric := gflow } } : SolutionOn (I := ThreeModel)
        (M := (H n).backwardSurvivorDomain first ((H n).activeStage (t n)) hle)
        (RealTimeInterval.closedOpen ((H n).time first) (s n)
          (((H n).time_strictMono.monotone hle).trans_lt
            (((H n).activeStage_time_le (t n)).trans_lt (hts n))))) ∧
      ∀ σ ∈ Icc (-((k + 2 : ℕ) : ℝ)) 0,
        h k n σ = scaleMetric (R n) (hR n) (localPullMetric (gflow ((t n : ℝ) + σ / R n))
          (fun x : W k n =>
            (⟨x.val, hWU x⟩ : (H n).backwardSurvivorDomain first ((H n).activeStage (t n)) hle))
          hι) := by
    intro k n hn
    obtain ⟨-, -, -, ⟨a, hat, ha, fs, hfs, -, hcross, htop, hpull⟩, -⟩ := hNb k n hn
    exact (H n).exists_survivor_flow_of_block (t n) (hR n) (Gs n) (hts n) (hGs n) k (W k n) (h k n)
      a hat ha fs hfs hcross htop hpull
  choose first hle hWU hι gflow hwin hslabs hcur hsol hid' using hsf
  let h' : ∀ k n, ℝ → SmoothRiemannianMetric ThreeModel (W k n) := fun k n =>
    if hn : Nb k ≤ n then
      fun σ => scaleMetric (R n) (hR n) (localPullMetric (gflow k n hn ((t n : ℝ) + σ / R n))
        (fun x : W k n => (⟨x.val, hWU k n hn x⟩ :
          (H n).backwardSurvivorDomain (first k n hn) ((H n).activeStage (t n)) (hle k n hn)))
        (hι k n hn))
    else h k n
  have hh' : ∀ k n (hn : Nb k ≤ n), h' k n = fun σ =>
      scaleMetric (R n) (hR n) (localPullMetric (gflow k n hn ((t n : ℝ) + σ / R n))
        (fun x : W k n => (⟨x.val, hWU k n hn x⟩ :
          (H n).backwardSurvivorDomain (first k n hn) ((H n).activeStage (t n)) (hle k n hn)))
        (hι k n hn)) := fun k n hn => dite_eq_left hn
  have hh'eq : ∀ k n (hn : Nb k ≤ n), ∀ σ ∈ Icc (-((k + 2 : ℕ) : ℝ)) 0, h' k n σ = h k n σ := by
    intro k n hn σ hσ
    rw [hh' k n hn, hid' k n hn σ hσ]
  have hsolh' : ∀ k : ℕ, ∀ᶠ n in atTop, IsSolutionOn ({ base.metric := h' k n } :
      SolutionOn (I := ThreeModel) (M := W k n)
        (RealTimeInterval.closed (-((k + 2 : ℕ) : ℝ)) 0 (neg_nonpos.mpr (Nat.cast_nonneg _)))) := by
    intro k
    filter_upwards [hblock k, eventually_ge_atTop (Nb k)] with n hn hNn
    exact hn.2.1.congr_metric fun σ hσ => (hh'eq k n hNn σ hσ).symm
  have hid : ∀ k : ℕ, ∀ᶠ n in atTop,
      (W k n : Set ((H n).stageAt (t n)).Carrier) =
        riemannianBallOf (scaleMetric (R n) (hR n)
          ((H n).stageMetric ((H n).activeStage (t n)) (t n))) (y n) ((k + 3 : ℕ) : ℝ) ∧
      ∀ σ ∈ Icc (-((k + 2 : ℕ) : ℝ)) 0,
      (t n : ℝ) + σ / R n ∈ Icc ((H n).time ((H n).activeStage (t n))) (t n : ℝ) →
      h' k n σ = scaleMetric (R n) (hR n)
        ((((H n).closedPrefixAt (t n) (hlt n)).flow.base.metric ((t n : ℝ) + σ / R n)).restrictOpen
          (W k n)) := by
    intro k
    filter_upwards [hblock k, eventually_ge_atTop (Nb k)] with n hn hNn
    refine ⟨hn.1, fun σ hσ hsD => ?_⟩
    rw [hh'eq k n hNn σ hσ, (H n).closedPrefixAt_metric]
    exact hn.2.2.1 σ hσ (hdom n _ hsD)
  have hconv' : ∀ k (K : Set (V k)), IsCompact K → ∀ p : ℕ, ∀ η : ℝ, 0 < η →
      ∃ j₀ : ℕ, ∀ i ≥ j₀, ∃ hi : N k ≤ ψ i, ∀ σ ∈ Icc (-((k + 1 : ℕ) : ℝ)) 0,
        metricDerivNormSupOn K p
          (localPullMetric (h' k (f (ψ i)) σ) (φ k (ψ i) hi) (hφ k (ψ i) hi))
          ((G σ).restrictOpen (V k)) (P.metric.restrictOpen (V k)) < η := by
    intro k K hK p η hη
    obtain ⟨j₀, hj₀⟩ := hconv k K hK p η hη
    obtain ⟨j₁, hj₁⟩ := eventually_atTop.1
      ((hf.comp hψ).tendsto_atTop.eventually (eventually_ge_atTop (Nb k)))
    refine ⟨max j₀ j₁, fun i hi => ?_⟩
    obtain ⟨hi', hb⟩ := hj₀ i ((le_max_left _ _).trans hi)
    refine ⟨hi', fun σ hσ => ?_⟩
    have hσ2 : σ ∈ Icc (-((k + 2 : ℕ) : ℝ)) 0 := ⟨by
      have := hσ.1
      push_cast at this ⊢
      linarith, hσ.2⟩
    rw [hh'eq k (f (ψ i)) (hj₁ i ((le_max_right _ _).trans hi)) σ hσ2]
    exact hb σ hσ
  obtain ⟨k, hk, hK⟩ := hB8 X D (fun n => ((H n).closedPrefixAt (t n) (hlt n)).flow)
    (fun n => (t n : ℝ)) R hR (fun n => ((H n).closedPrefixAt (t n) (hlt n)).equation) hSR hX hleft
    W h' hsolh' hid f hf P F hPc hballF V N hV hVF φ hφ hφF G hG hG0 ψ hψ hconv' _ hanc hbase o
  refine ⟨f ∘ ψ, hf.comp hψ, ?_⟩
  filter_upwards [hK, (hf.comp hψ).tendsto_atTop.eventually (eventually_ge_atTop (Nb k)),
    (hf.comp hψ).tendsto_atTop.eventually (hblock k)] with i hKi hNi hn
  simp only [Function.comp_apply] at hNi hn
  obtain ⟨hy, K, hKc⟩ := hKi
  have hdom0 : (t (f (ψ i)) : ℝ) + 0 / R (f (ψ i)) ∈
      (H (f (ψ i))).stageDomain ((H (f (ψ i))).activeStage (t (f (ψ i)))) := by
    simpa using (H (f (ψ i))).activeStage_mem (t (f (ψ i)))
  have hh0 : h' k (f (ψ i)) 0 = scaleMetric (R (f (ψ i))) (hR (f (ψ i)))
      (((H (f (ψ i))).stageMetric ((H (f (ψ i))).activeStage (t (f (ψ i))))
        (t (f (ψ i)))).restrictOpen (W k (f (ψ i)))) := by
    have h0 := hn.2.2.1 0 ⟨neg_nonpos.mpr (Nat.cast_nonneg _), le_rfl⟩ hdom0
    rw [zero_div, add_zero] at h0
    rw [hh'eq k (f (ψ i)) hNi 0 ⟨neg_nonpos.mpr (Nat.cast_nonneg _), le_rfl⟩]
    exact h0
  have hball : riemannianClosedBallOf
      (scaleMetric (R (f (ψ i))) (hR (f (ψ i)))
        ((H (f (ψ i))).stageMetric ((H (f (ψ i))).activeStage (t (f (ψ i)))) (t (f (ψ i)))))
      (y (f (ψ i))) (2 * C + 1) ⊆
      (W k (f (ψ i)) : Set ((H (f (ψ i))).stageAt (t (f (ψ i)))).Carrier) := by
    rw [hn.1]
    intro z hz
    exact lt_of_le_of_lt hz ((ENNReal.ofReal_lt_ofReal_iff (by positivity)).2 hk)
  obtain ⟨Wt, hWt, hneck⟩ := exists_spatialCanonicalWitness_of_canonicalWitness_restrictOpen
    ((H (f (ψ i))).stageMetric ((H (f (ψ i))).activeStage (t (f (ψ i)))) (t (f (ψ i))))
    (hR (f (ψ i))) (W k (f (ψ i))) ⟨y (f (ψ i)), hy⟩ (hscal (f (ψ i)))
    (neg_nonpos.mpr (Nat.cast_nonneg _)) (h' k (f (ψ i))) hh0 K hKc hball
  refine ⟨Wt, hWt, fun hW => ?_⟩
  obtain ⟨data, -⟩ := hneck hW
  exact (H (f (ψ i))).historyStrongNeckFull_of_survivor_strongNeck_C12X (t (f (ψ i)))
    (y (f (ψ i)))
    (hR (f (ψ i))) (hscal (f (ψ i))) (Gs (f (ψ i))) (hts (f (ψ i))) (hGs (f (ψ i))) k
    (W k (f (ψ i))) hy (first k _ hNi) (hle k _ hNi) (hWU k _ hNi) (hι k _ hNi) (gflow k _ hNi)
    (hwin k _ hNi) (hslabs k _ hNi) (hcur k _ hNi) (hsol k _ hNi) (h' k (f (ψ i)))
    (fun σ => congrFun (hh' k _ hNi) σ) data.strong

end ObservedHistory

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

end
