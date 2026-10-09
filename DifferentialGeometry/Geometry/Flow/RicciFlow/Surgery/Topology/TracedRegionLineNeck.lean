import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.TracedRegionAncientKappaLimit
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.KappaSolutions.PointedLineNeck
import DifferentialGeometry.Geometry.Compactness.CheegerGromov.Pointed.Convergence.SeparatingSegments
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.SpatialNeckWitnessConversion
import DifferentialGeometry.Geometry.Metric.Comparison.DistanceScaling
import DifferentialGeometry.Geometry.Metric.Distance.SeparatedSidePoint

set_option autoImplicit false

noncomputable section

open Set Filter
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.CheegerGromovCompactness
open scoped Manifold ContDiff Topology NNReal ENNReal

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

open DifferentialGeometry.Geometry.Riemannian
open Perelman.CanonicalNeighborhood (ancientTimeInterval)
open Perelman.CanonicalNeighborhood.FiniteHorn (SpatialCanonicalWitness SpatialNeck)

namespace ObservedHistory

universe u

attribute [local instance] PointedRiemannianManifold.topology PointedRiemannianManifold.charted
  PointedRiemannianManifold.smooth PointedRiemannianManifold.t2
  PointedRiemannianManifold.sigmaCompact PointedRiemannianManifold.t2TangentBundle

private theorem exists_canonical_convergence_of_eq {X : PointedRiemannianSeq.{u, 0, 0} ThreeModel}
    {P Q : PointedRiemannianManifold.{u, 0, 0} ThreeModel} (hQ : Q = P) {f : ℕ → ℕ}
    (F : PointedRiemannianConvergenceMaps X P f) (C : MetricConvergenceData F)
    (hC : ∀ n, C.domain n = CanonicalMetricCompactness.canonicalSourceData F n) :
    ∃ (F' : PointedRiemannianConvergenceMaps X Q f) (C' : MetricConvergenceData F'),
      ∀ n, C'.domain n = CanonicalMetricCompactness.canonicalSourceData F' n := by
  subst hQ
  exact ⟨F, C, hC⟩

theorem exists_eventually_spatialNeck_of_isTracedRegion_of_separating_set :
    ∃ epsW : ℝ, 0 < epsW ∧
    ∀ (H : ℕ → ObservedHistory.{u}) (t : ∀ n, Icc (0 : ℝ) (H n).horizon)
    (y : ∀ n, ((H n).stageAt (t n)).Carrier) (R : ℕ → ℝ), (∀ n, 0 < R n) →
    (∀ n, metricScalarAt ((H n).stageMetric ((H n).activeStage (t n)) (t n)) (y n) = R n) →
    Tendsto R atTop atTop →
    (∀ A T : ℝ, 0 < A → 0 < T → ∃ K : ℝ, 0 ≤ K ∧ ∀ᶠ n in atTop,
      (H n).isTracedRegion (t n) (y n) (A / Real.sqrt (R n)) (T / R n) (K * R n)) →
    ∀ {κ ρ : ℝ}, 0 < κ → 0 < ρ → ∀ {t₀ : ℕ → ℝ},
    Tendsto (fun n => R n * (t n - t₀ n)) atTop (𝓝 0) →
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
    ∀ {eps C1 C2 Cs Cq : ℝ} {Ctime : ℝ≥0} {qs qcan : ℕ → ℝ}, 0 < eps → eps ≤ epsW →
    (∀ n, qs n ≤ Cs * R n) → (∀ n, qcan n ≤ Cq * R n) →
    (∀ n (v : Icc (0 : ℝ) (H n).horizon), (v : ℝ) < t₀ n →
      (H n).time ((H n).activeStage v) < v → ∀ p : ((H n).stageAt v).Carrier,
        qs n < metricScalarAt ((H n).stageMetric ((H n).activeStage v) v) p →
        ∃ Wt : SpatialCanonicalWitness ((H n).stageMetric ((H n).activeStage v) v) eps C1 C2 p,
          Wt.capTubeHasNeckChart eps) →
    (∀ n (v : Icc (0 : ℝ) (H n).horizon), (v : ℝ) < t₀ n →
      (H n).time ((H n).activeStage v) < v → ∀ p : ((H n).stageAt v).Carrier,
        qcan n < metricScalarAt ((H n).stageMetric ((H n).activeStage v) v) p →
        |derivWithin (fun v' => metricScalarAt ((H n).stageMetric ((H n).activeStage v) v') p)
          (Iic (v : ℝ)) v| ≤
          Ctime * metricScalarAt ((H n).stageMetric ((H n).activeStage v) v) p ^ 2) →
    ∀ (S V W : ∀ n, Set ((H n).stageAt (t n)).Carrier), (∀ n, IsOpen (V n)) →
      (∀ n, IsOpen (W n)) → (∀ n, Disjoint (V n) (W n)) → ∀ {B : ℝ}, 0 ≤ B →
    (∀ n, ∀ z ∈ S n,
      riemannianEDistOf ((H n).stageMetric ((H n).activeStage (t n)) (t n)) (y n) z ≤
        ENNReal.ofReal (B / Real.sqrt (R n))) →
    (∀ A : ℝ, B < A → ∀ᶠ n in atTop,
      riemannianClosedBallOf ((H n).stageMetric ((H n).activeStage (t n)) (t n)) (y n)
          (3 * A / Real.sqrt (R n)) \ S n ⊆ V n ∪ W n ∧
      ∃ p ∈ V n, ∃ q ∈ W n,
        ENNReal.ofReal (A / Real.sqrt (R n)) ≤
          riemannianEDistOf ((H n).stageMetric ((H n).activeStage (t n)) (t n)) (y n) p ∧
        riemannianEDistOf ((H n).stageMetric ((H n).activeStage (t n)) (t n)) (y n) p <
          ENNReal.ofReal (3 * A / Real.sqrt (R n)) ∧
        ENNReal.ofReal (A / Real.sqrt (R n)) ≤
          riemannianEDistOf ((H n).stageMetric ((H n).activeStage (t n)) (t n)) (y n) q ∧
        riemannianEDistOf ((H n).stageMetric ((H n).activeStage (t n)) (t n)) (y n) q <
          ENNReal.ofReal (3 * A / Real.sqrt (R n))) →
    ∃ ψ : ℕ → ℕ, StrictMono ψ ∧ ∀ ε : ℝ, 0 < ε → ε < 1 / 11 → ∀ᶠ i in atTop,
      Nonempty (SpatialNeck
        ((H (ψ i)).stageMetric ((H (ψ i)).activeStage (t (ψ i))) (t (ψ i))) ε (y (ψ i))) := by
  obtain ⟨epsW, hepsW, hA⟩ := exists_ancientKappa_pointed_limit_of_isTracedRegion.{u}
  refine ⟨epsW, hepsW, ?_⟩
  intro H t y R hR hscal hRlim htraced κ ρ hκ hρ t₀ hsliver hnc Phi hPhi hpinch eps C1 C2 Cs Cq
    Ctime qs qcan heps hepsW' hqs hqcan hwit hderiv S V W hV hW hVW B hB hS hpoints
  obtain ⟨f, hf, P, F, ⟨C, hcan⟩, hPc, hconn, -, G, hG, hG0, hanc, -⟩ :=
    hA H t y R hR hscal hRlim htraced hκ hρ hsliver hnc hPhi hpinch heps hepsW' hqs hqcan hwit
      hderiv
  let g : ∀ n, SmoothRiemannianMetric ThreeModel ((H n).stageAt (t n)).Carrier :=
    fun n => (H n).stageMetric ((H n).activeStage (t n)) (t n)
  have hsq : ∀ n, 0 < Real.sqrt (R n) := fun n => Real.sqrt_pos.mpr (hR n)
  have hscaled : ∀ n (z : ((H n).stageAt (t n)).Carrier),
      riemannianEDistOf (scaleMetric (R n) (hR n) (g n)) (y n) z =
        ENNReal.ofReal (Real.sqrt (R n)) * riemannianEDistOf (g n) (y n) z := fun n z =>
    edistOf_scale (R n) (hR n) (g n) (y n) z
  have hmulA : ∀ n (a : ℝ), ENNReal.ofReal (Real.sqrt (R n)) *
      ENNReal.ofReal (a / Real.sqrt (R n)) = ENNReal.ofReal a := by
    intro n a
    rw [← ENNReal.ofReal_mul (hsq n).le, mul_div_cancel₀ _ (hsq n).ne']
  have href : ∀ k, (C.domain k).referenceMetric = (C.domain k).limitMetric := by
    intro k
    rw [hcan]
    rfl
  obtain ⟨line, hline⟩ :=
    exists_pointed_metric_line_of_eventual_minimizing_segments_intersecting_bounded_sets C href
      hPc hconn (fun k => S (f k)) hB
      (fun k z hz => by
        change riemannianEDistOf (scaleMetric (R (f k)) (hR (f k)) (g (f k))) (y (f k)) z ≤ _
        rw [hscaled (f k), ← hmulA (f k) B]
        gcongr
        exact hS (f k) z hz)
      (fun A hBA => by
        filter_upwards [hf.tendsto_atTop.eventually (hpoints A hBA)] with k hk
        obtain ⟨hcov, p₀, hp₀, q₀, hq₀, hpa, hpc, hqa, hqc⟩ := hk
        have hA0 : 0 ≤ A := hB.trans hBA.le
        have hBA' : B / Real.sqrt (R (f k)) < A / Real.sqrt (R (f k)) :=
          div_lt_div_of_pos_right hBA (hsq (f k))
        have hbB : 0 ≤ B / Real.sqrt (R (f k)) := div_nonneg hB (hsq (f k)).le
        have hcov' : riemannianBallOf (g (f k)) (y (f k)) (3 * A / Real.sqrt (R (f k))) \
            S (f k) ⊆ V (f k) ∪ W (f k) := fun z hz =>
          hcov ⟨show riemannianEDistOf (g (f k)) (y (f k)) z ≤ _ from le_of_lt hz.1, hz.2⟩
        obtain ⟨p, hp, hpd⟩ :=
          Geometry.Metric.exists_mem_riemannianEDistOf_eq_of_ball_diff_subset (g (f k))
          (hV (f k)) (hW (f k)) (hVW (f k)) hbB hBA' (hS (f k)) hcov' hp₀ hpa hpc
        obtain ⟨q, hq, hqd⟩ :=
          Geometry.Metric.exists_mem_riemannianEDistOf_eq_of_ball_diff_subset (g (f k))
          (hW (f k)) (hV (f k)) (hVW (f k)).symm hbB hBA' (hS (f k))
          (by rw [union_comm]; exact hcov') hq₀ hqa hqc
        have hpX : riemannianEDistOf (scaleMetric (R (f k)) (hR (f k)) (g (f k))) (y (f k)) p =
            ENNReal.ofReal A := by
          rw [hscaled (f k), hpd, hmulA]
        have hqX : riemannianEDistOf (scaleMetric (R (f k)) (hR (f k)) (g (f k))) (y (f k)) q =
            ENNReal.ofReal A := by
          rw [hscaled (f k), hqd, hmulA]
        have hballX : riemannianClosedBallOf (scaleMetric (R (f k)) (hR (f k)) (g (f k)))
            (y (f k)) (3 * A) = riemannianClosedBallOf (g (f k)) (y (f k))
              (3 * A / Real.sqrt (R (f k))) := by
          rw [← riemannianClosedBallOf_scaleMetric (R (f k)) (hR (f k)) (g (f k)) (y (f k))
            (3 * A / Real.sqrt (R (f k))), mul_div_cancel₀ _ (hsq (f k)).ne']
        obtain ⟨γ, hγ0, hγ1, hγs, hγmem, hγmin⟩ :=
          exists_distance_parametrized_minimizer_in_closedBall
            (scaleMetric (R (f k)) (hR (f k)) (g (f k))) (y (f k)) p q hA0 hpX.le hqX.le
            (isClosed_le (continuous_riemannianEDist _ _) continuous_const).isCompact
        refine ⟨γ, _, ENNReal.toReal_nonneg, hγmin, ?_, ?_, ?_⟩
        · by_contra hmiss
          simp only [not_exists, not_and] at hmiss
          have hZ : γ '' Icc 0 (riemannianEDistOf (scaleMetric (R (f k)) (hR (f k)) (g (f k)))
              p q).toReal ⊆ V (f k) ∪ W (f k) := by
            rintro _ ⟨s, hs, rfl⟩
            refine hcov ⟨?_, hmiss s hs⟩
            rw [← hballX]
            exact hγmem s hs
          rcases (isPreconnected_Icc.image γ hγs.continuousOn).subset_or_subset (hV (f k))
              (hW (f k)) (hVW (f k)) hZ with hZV | hZW
          · exact disjoint_left.mp (hVW (f k))
              (hγ1 ▸ hZV ⟨_, ⟨ENNReal.toReal_nonneg, le_rfl⟩, rfl⟩) hq
          · exact disjoint_left.mp (hVW (f k)) hp
              (hγ0 ▸ hZW ⟨0, ⟨le_rfl, ENNReal.toReal_nonneg⟩, rfl⟩)
        · change (riemannianEDistOf (scaleMetric (R (f k)) (hR (f k)) (g (f k))) (y (f k))
            (γ 0)).toReal = A
          rw [hγ0, hpX, ENNReal.toReal_ofReal hA0]
        · change (riemannianEDistOf (scaleMetric (R (f k)) (hR (f k)) (g (f k))) (y (f k))
            (γ _)).toReal = A
          rw [hγ1, hqX, ENNReal.toReal_ofReal hA0])
  obtain ⟨Phi', C', hcan'⟩ := exists_canonical_convergence_of_eq
    (flowOfMetric_atTime ancientTimeInterval P G hG 0 hG0) F C hcan
  refine ⟨f, hf, fun ε hε hsmall => ?_⟩
  obtain ⟨_, _, -, -, k0, hk0⟩ :=
    Perelman.KappaSolutions.pointedAncientKappaLimit_eventually_spatialNeckWitness_of_intrinsic_line
      Phi' C' hcan'
      (fun n => by exact (RiemannianMetricComplete.of_compact (scaleMetric (R n) (hR n) (g n))).1)
      (fun n => ((H n).stageAt (t n)).orientation)
      (fun n => by
        change metricScalarAt (scaleMetric (R n) (hR n) (g n)) (y n) = 1
        rw [metricScalarAt_scaleMetric, hscal n, inv_mul_cancel₀ (hR n).ne'])
      hanc le_rfl line (fun a b => by
        change riemannianEDistOf (G 0) (line a) (line b) = _
        rw [hG0]
        exact hline a b) hε
  refine eventually_atTop.mpr ⟨k0, fun k hk => ?_⟩
  obtain ⟨W, -⟩ := hk0 k hk
  obtain ⟨nk, -⟩ := W.exists_spatialNeck hε hsmall le_rfl
  have hback : scaleMetric (R (f k))⁻¹ (inv_pos.mpr (hR (f k)))
      (scaleMetric (R (f k)) (hR (f k)) (g (f k))) = g (f k) :=
    SmoothRiemannianMetric.ext_inner fun x v w => by
      simp only [scaleMetric_inner]
      rw [← mul_assoc, inv_mul_cancel₀ (hR (f k)).ne', one_mul]
  have nk' := nk.scaleMetric (R (f k))⁻¹ (inv_pos.mpr (hR (f k)))
  rw [hback] at nk'
  exact ⟨nk'⟩

end ObservedHistory

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

end
