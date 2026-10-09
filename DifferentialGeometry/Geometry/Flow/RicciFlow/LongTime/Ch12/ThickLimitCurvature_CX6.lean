import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch12.ThickLimitVolumeLimit_O5
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch12.ThickLimitSeedLocalCore_S18
import DifferentialGeometry.Geometry.Compactness.CheegerGromov.Pointed.Convergence.Inner

set_option autoImplicit false

/-! # CH12-CX6: canonical limits of late slices are hyperbolic, using LTF03 -/

noncomputable section
open DifferentialGeometry DifferentialGeometry.Topology DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Geometry.Hyperbolic DifferentialGeometry.Geometry.Collapse
open DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
open DifferentialGeometry.CheegerGromovCompactness
open GC.LongTime Set Filter
open scoped Manifold ContDiff ENNReal Topology

namespace GC.LongTime.Ch12
universe u
variable {P : OrientedThreeStage.{u}} {g : P.Metric} {F : GC.Interface.RawSurgery P g}

attribute [local instance] PointedRiemannianManifold.topology
  PointedRiemannianManifold.charted PointedRiemannianManifold.smooth
  PointedRiemannianManifold.t2 PointedRiemannianManifold.sigmaCompact
  PointedRiemannianManifold.t2TangentBundle

theorem ricci_of_canonical_defect_CX6 (S : LatePointSequence_S13 F) (σ : ℕ → ℕ)
    (L : PointedRiemannianManifold.{u, 0, 0} ThreeModel)
    (Φ : PointedRiemannianConvergenceMaps S.pointedSeq L σ) (C : MetricConvergenceData Φ)
    (hcan : ∀ n, C.domain n = CanonicalMetricCompactness.canonicalSourceData Φ n)
    (x : L.M) (hdef : ∀ ε : ℝ, 0 < ε → ∀ᶠ n in atTop,
      NormalizedRicciDefect_S13 (S.slices (σ n)) (Φ.map n x) < ε) :
    ∀ v w : TangentSpace ThreeModel x,
      ricciTensor L.metric x v w = -(1 / 2 : ℝ) * L.metric.inner x v w := by
  apply bilin_eq_of_quad_eq_O5 _ _ _ (ricciTensor_symm L.metric x) (L.metric.symm x)
  intro v
  let a : ℕ → ℝ := fun n => ricciTensor (S.slices (σ n)).normalizedMetric (Φ.map n x)
    (mfderiv ThreeModel ThreeModel (Φ.map n) x v) (mfderiv ThreeModel ThreeModel (Φ.map n) x v)
  let b : ℕ → ℝ := fun n => (S.slices (σ n)).normalizedMetric.inner (Φ.map n x)
    (mfderiv ThreeModel ThreeModel (Φ.map n) x v) (mfderiv ThreeModel ThreeModel (Φ.map n) x v)
  let A := ricciTensor L.metric x v v
  let B := L.metric.inner x v v
  have hB : 0 ≤ B := metric_inner_self_nonneg L.metric x v
  have ha : Tendsto a atTop (𝓝 A) :=
    PDE.RicciFlow.Perelman.KappaSolutions.pointedRicci_tendsto_of_metricCG_canonical_domains C hcan x v
  have hb : Tendsto b atTop (𝓝 B) := by
    apply pointed_metric_inner_tendsto (Phi := Φ) _ x v v
    intro K hK
    simpa only [show C.domain = CanonicalMetricCompactness.canonicalSourceData Φ from funext hcan]
      using C.converges K hK 0
  have hineq : ∀ ε : ℝ, 0 < ε → ∀ᶠ n in atTop, |2 * a n + b n| ≤ ε * b n := by
    intro ε hε
    filter_upwards [hdef ε hε] with n hn
    have hq := defect_quad_le_O5 (S.slices (σ n)).normalizedMetric (Φ.map n x)
      (mfderiv ThreeModel ThreeModel (Φ.map n) x v)
    have hD : sSup (defectSet_O5 (S.slices (σ n)).normalizedMetric (Φ.map n x)) < ε := hn
    exact hq.trans (mul_le_mul_of_nonneg_right hD.le (metric_inner_self_nonneg _ _ _))
  have hlim : ∀ ε : ℝ, 0 < ε → |2 * A + B| ≤ ε * B := by
    intro ε hε
    exact le_of_tendsto_of_tendsto ((tendsto_const_nhds.mul ha).add hb).abs
      (tendsto_const_nhds.mul hb) (hineq ε hε)
  have hz : 2 * A + B = 0 := by
    apply abs_nonpos_iff.mp
    apply le_of_forall_pos_lt_add
    intro ε hε
    have h := hlim (ε / (B + 1)) (by positivity)
    have hh : ε / (B + 1) * B < ε := by
      rw [div_mul_eq_mul_div, div_lt_iff₀ (by linarith)]
      nlinarith
    linarith
  change A = -(1 / 2 : ℝ) * B
  linarith

/-- Repointing the actual sequence at the image of a limit point permits LTF03
to use the S18 seed.  Both the time sequence and the maps are the actual ones. -/
theorem canonical_limit_hyperbolic_CX6 {δ : ℝ → ℝ} (Hp : AnalyticSurgeryProfile F δ)
    (hdec : ∀ ε : ℝ, 0 < ε → ∃ B : ℝ, ∀ t : ℝ, B < t → δ t < ε)
    (hneg : EventuallyNegativeScalar_S13 F)
    (hLTF03 : ∀ (S : LatePointSequence_S13 F) (a v R : ℝ),
      SeedHyperbolicOnFixedBallsSeq_S13 Hp hdec hneg S a v R)
    (S : LatePointSequence_S13 F) (σ : ℕ → ℕ) (hσ : StrictMono σ)
    (L : PointedRiemannianManifold.{u, 0, 0} ThreeModel)
    (Φ : PointedRiemannianConvergenceMaps S.pointedSeq L σ) (C : MetricConvergenceData Φ)
    (hcan : ∀ n, C.domain n = CanonicalMetricCompactness.canonicalSourceData Φ n) :
    RicciEqualsMetricMultiple_S13 L.metric (-(1 / 2 : ℝ)) ∧
      hasConstantSectionalCurvature L.metric (-(1 / 4 : ℝ)) := by
  have hric : RicciEqualsMetricMultiple_S13 L.metric (-(1 / 2 : ℝ)) := by
    intro x
    apply ricci_of_canonical_defect_CX6 S σ L Φ C hcan x
    obtain ⟨a, v, ha, hv, hseed⟩ := exists_seed_at_limit_point_S18 Φ C hcan x
    obtain ⟨N, hN⟩ := eventually_atTop.mp hseed
    let T : LatePointSequence_S13 F :=
      { slices := fun n => S.slices (σ (n + N))
        times_tendsto := (S.times_tendsto.comp hσ.tendsto_atTop).comp (tendsto_add_atTop_nat N)
        point := fun n => Φ.map (n + N) x }
    have hs : ∀ n, HasNormalizedSeed_S13 (T.slices n) (T.point n) a v :=
      fun n => hN (n + N) (by omega)
    intro ε hε
    have hd := hLTF03 T a v 1 ha hv zero_lt_one hs ε hε
    have hc : ∀ᶠ n in atTop, NormalizedRicciDefect_S13 (T.slices n) (T.point n) < ε :=
      hd.mono fun n hn => hn (T.point n) (by
        change riemannianEDistOf (T.slices n).normalizedMetric (T.point n) (T.point n) < ENNReal.ofReal 1
        rw [riemannianEDistOf_self]; exact ENNReal.ofReal_pos.mpr zero_lt_one)
    obtain ⟨m, hm⟩ := eventually_atTop.mp hc
    refine eventually_atTop.mpr ⟨m + N, fun n hn => ?_⟩
    have h := hm (n - N) (by omega)
    change NormalizedRicciDefect_S13 (S.slices (σ (n - N + N))) (Φ.map (n - N + N) x) < ε at h
    rwa [Nat.sub_add_cancel (by omega : N ≤ n)] at h
  refine ⟨hric, ?_⟩
  convert ricciEq_constSec_O5 L.metric (-(1 / 2 : ℝ)) hric using 1
  norm_num

end GC.LongTime.Ch12
