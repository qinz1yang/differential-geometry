import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.TracedRegionAncientLimitScalarBound
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.AncientLimitCanonicalWitness
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.AncientPointedFlowLimitCurvature
import DifferentialGeometry.Geometry.Flow.RicciFlow.Compactness.Limits.PointedLimitOrientation
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.AncientPointedFlowLimitBaseScalar

set_option autoImplicit false

noncomputable section

open Set Filter TopologicalSpace
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.CheegerGromovCompactness
open scoped Manifold ContDiff Topology NNReal ENNReal

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

open Perelman.CanonicalNeighborhood.FiniteHorn (SpatialCanonicalWitness CanonicalWitness I3
  exists_canonicalWitness_of_ancient_pointed_flow_limit
  eventually_scalar_derivative_bounds_of_ancient_pointed_flow_limit
  isAncientKappaSolution_flowOfMetric_of_curvatureOperator_nonnegative)

open private ObservedHistory.mem_Icc_of_mem_window from
  DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.TracedRegionAncientLimit

namespace ObservedHistory

universe u

attribute [local instance] PointedRiemannianManifold.topology PointedRiemannianManifold.charted
  PointedRiemannianManifold.smooth PointedRiemannianManifold.t2
  PointedRiemannianManifold.sigmaCompact PointedRiemannianManifold.t2TangentBundle

theorem exists_eventually_canonical_clauses_of_isTracedRegion :
    ∃ epsW : ℝ, 0 < epsW ∧ ∀ ε : ℝ, 0 < ε → ε < 1 / 11 → ε ≤ epsW →
    ∃ C τ₀ : ℝ, 1 ≤ C ∧ 0 < τ₀ ∧
    ∀ (H : ℕ → ObservedHistory.{u}) (t : ∀ n, Icc (0 : ℝ) (H n).horizon)
      (y : ∀ n, ((H n).stageAt (t n)).Carrier) (R : ℕ → ℝ),
      (∀ n, 0 < R n) →
      (∀ n, metricScalarAt ((H n).stageMetric ((H n).activeStage (t n)) (t n)) (y n) = R n) →
      Tendsto R atTop atTop →
      ∀ (hlt : ∀ n, (H n).time ((H n).activeStage (t n)) < t n),
      ((∀ n, τ₀ ≤ R n * ((t n : ℝ) - (H n).time ((H n).activeStage (t n)))) ∨
        ∀ n, R n * ((t n : ℝ) - (H n).time ((H n).activeStage (t n))) < τ₀) →
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
        (τ₀ ≤ ((H (ψ i)).closedPrefixAt (t (ψ i)) (hlt (ψ i))).flow.scalar (t (ψ i)) (y (ψ i)) *
            ((t (ψ i) : ℝ) - (H (ψ i)).time ((H (ψ i)).activeStage (t (ψ i)))) →
          ∃ W : CanonicalWitness ((H (ψ i)).closedPrefixAt (t (ψ i)) (hlt (ψ i))).flow ε C C
            (y (ψ i)) (t (ψ i)), W.capTubeHasNeckChart ε) ∧
        |derivWithin (fun v =>
            ((H (ψ i)).closedPrefixAt (t (ψ i)) (hlt (ψ i))).flow.scalar v (y (ψ i)))
            (Iic (t (ψ i) : ℝ)) (t (ψ i))| ≤
          C * ((H (ψ i)).closedPrefixAt (t (ψ i)) (hlt (ψ i))).flow.scalar (t (ψ i))
            (y (ψ i)) ^ 2 ∧
        ∀ v : TangentSpace I3 (y (ψ i)),
          |Perelman.CanonicalNeighborhood.scalarDifferential
              ((H (ψ i)).closedPrefixAt (t (ψ i)) (hlt (ψ i))).flow (t (ψ i)) (y (ψ i)) v| ≤
            C * ((H (ψ i)).closedPrefixAt (t (ψ i)) (hlt (ψ i))).flow.scalar (t (ψ i)) (y (ψ i)) *
              Real.sqrt (((H (ψ i)).closedPrefixAt (t (ψ i)) (hlt (ψ i))).flow.scalar (t (ψ i))
                (y (ψ i))) *
              Real.sqrt ((((H (ψ i)).closedPrefixAt (t (ψ i)) (hlt (ψ i))).flow.base.metric
                (t (ψ i))).inner (y (ψ i)) v v) := by
  obtain ⟨epsW, hepsW, hB13⟩ :=
    exists_bounded_ancient_pointed_flow_limit_of_spatially_canonical_before.{u}
  refine ⟨epsW, hepsW, fun ε hε hsmall hεW => ?_⟩
  obtain ⟨Cw, τ₀, hCw, hτ₀, hB8w⟩ := exists_canonicalWitness_of_ancient_pointed_flow_limit.{u}
    hε hsmall
  obtain ⟨Cd, -, hB8d⟩ := eventually_scalar_derivative_bounds_of_ancient_pointed_flow_limit.{u}
    hε hsmall
  refine ⟨max Cw Cd, τ₀, hCw.trans (le_max_left _ _), hτ₀, ?_⟩
  intro H t y R hR hscal hRlim hlt hmode htraced κ ρ hκ hρ t₀ hsliver hnc Phi hPhi hpinch
    C1s C2s Cs Cq Ctime qs qcan hqs hqcan hwit hderiv
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
  have hid : ∀ k : ℕ, ∀ᶠ n in atTop, ∀ s ∈ Icc (-((k + 2 : ℕ) : ℝ)) 0,
      (t n : ℝ) + s / R n ∈ Icc ((H n).time ((H n).activeStage (t n))) (t n : ℝ) →
      h k n s = scaleMetric (R n) (hR n)
        ((((H n).closedPrefixAt (t n) (hlt n)).flow.base.metric ((t n : ℝ) + s / R n)).restrictOpen
          (W k n)) := by
    intro k
    filter_upwards [hblock k] with n hn s hs hsD
    rw [(H n).closedPrefixAt_metric]
    exact hn.2.2.1 s hs (hdom n _ hsD)
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
  have hDG := hB8d X D (fun n => ((H n).closedPrefixAt (t n) (hlt n)).flow) (fun n => (t n : ℝ))
    R hR (fun n => ((H n).closedPrefixAt (t n) (hlt n)).equation) hSR hX hleft
    W h (fun k => (hblock k).mono fun n hn => hn.2.1)
    (fun k => ((hblock k).and (hid k)).mono fun n hn => ⟨hn.1.1, hn.2⟩)
    f hf P F hPc hballF V N hV hVF φ hφ hφF G hG hG0 ψ hψ hconv _ hanc hbase o
  have hDG' : ∀ᶠ i in atTop,
      |derivWithin (fun v =>
          ((H (f (ψ i))).closedPrefixAt (t (f (ψ i))) (hlt (f (ψ i)))).flow.scalar v
            (y (f (ψ i)))) (Iic (t (f (ψ i)) : ℝ)) (t (f (ψ i)))| ≤
        max Cw Cd * ((H (f (ψ i))).closedPrefixAt (t (f (ψ i))) (hlt (f (ψ i)))).flow.scalar
          (t (f (ψ i))) (y (f (ψ i))) ^ 2 ∧
      ∀ v : TangentSpace I3 (y (f (ψ i))),
        |Perelman.CanonicalNeighborhood.scalarDifferential
            ((H (f (ψ i))).closedPrefixAt (t (f (ψ i))) (hlt (f (ψ i)))).flow (t (f (ψ i)))
            (y (f (ψ i))) v| ≤
          max Cw Cd * ((H (f (ψ i))).closedPrefixAt (t (f (ψ i))) (hlt (f (ψ i)))).flow.scalar
              (t (f (ψ i))) (y (f (ψ i))) *
            Real.sqrt (((H (f (ψ i))).closedPrefixAt (t (f (ψ i))) (hlt (f (ψ i)))).flow.scalar
              (t (f (ψ i))) (y (f (ψ i)))) *
            Real.sqrt ((((H (f (ψ i))).closedPrefixAt (t (f (ψ i)))
              (hlt (f (ψ i)))).flow.base.metric (t (f (ψ i)))).inner (y (f (ψ i))) v v) := by
    filter_upwards [hDG] with i hi
    have hS0 := (hSR (f (ψ i))).symm ▸ (hR (f (ψ i))).le
    refine ⟨hi.1.trans (mul_le_mul_of_nonneg_right (le_max_right _ _) (sq_nonneg _)),
      fun v => (hi.2 v).trans ?_⟩
    exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right (le_max_right _ _) hS0) (Real.sqrt_nonneg _))
      (Real.sqrt_nonneg _)
  refine ⟨f ∘ ψ, hf.comp hψ, ?_⟩
  rcases hmode with hm | hm
  · have hage : ∀ᶠ n in atTop,
        Icc ((t n : ℝ) - τ₀ / R n) (t n) ⊆ Icc ((H n).time ((H n).activeStage (t n))) (t n) ∧
        Ioo ((t n : ℝ) - τ₀ / R n) (t n) ⊆ Ioo ((H n).time ((H n).activeStage (t n))) (t n) := by
      refine Eventually.of_forall fun n => ?_
      have hle : τ₀ / R n ≤ (t n : ℝ) - (H n).time ((H n).activeStage (t n)) := by
        rw [div_le_iff₀ (hR n), mul_comm]
        exact hm n
      exact ⟨Icc_subset_Icc (by linarith) le_rfl, Ioo_subset_Ioo (by linarith) le_rfl⟩
    have hW := hB8w X D (fun n => ((H n).closedPrefixAt (t n) (hlt n)).flow)
      (fun n => (t n : ℝ)) R hR (fun n => ((H n).closedPrefixAt (t n) (hlt n)).equation) hSR hX
      hage W h hid f hf P F hPc hballF V N hV hVF φ hφ hφF G hG hG0 ψ hψ hconv _ hanc hbase o
    filter_upwards [hW, hDG'] with i hwi hdi
    obtain ⟨K, hK⟩ := hwi
    exact ⟨fun _ => ⟨K.enlargeConstants (le_max_left _ _) (le_max_left _ _),
      hK.enlarge_constants (le_max_left _ _) (le_max_left _ _)⟩, hdi⟩
  · filter_upwards [hDG'] with i hdi
    refine ⟨fun hold => absurd (hm (f (ψ i))) (not_lt.mpr ?_), hdi⟩
    rwa [hSR] at hold

end ObservedHistory

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

end
