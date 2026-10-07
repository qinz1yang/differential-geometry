import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch12.ThickJetsMain_S36
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch12.ThickLimitExtraction_CX6
import DifferentialGeometry.Geometry.Compactness.CheegerGromov.Pointed.Bounds.VolumeInjectivity
import DifferentialGeometry.Geometry.Compactness.CheegerGromov.Pointed.ConnectedComponent

set_option autoImplicit false

/-! # CH12-S36: `hinj` of CX6 and the final S13 extraction predicate -/

noncomputable section
open DifferentialGeometry DifferentialGeometry.Geometry.Collapse DifferentialGeometry.Geometry.Riemannian
open DifferentialGeometry.Geometry.Curvature DifferentialGeometry.CheegerGromovCompactness
open DifferentialGeometry.PDE.RicciFlow DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
open GC.LongTime Set Filter
open scoped Manifold ContDiff ENNReal Topology

namespace GC.LongTime.Ch12
universe u
variable {P : OrientedThreeStage.{u}} {g : P.Metric} {F : GC.Interface.RawSurgery P g} {δ : ℝ → ℝ}

attribute [local instance] PointedRiemannianManifold.topology
  PointedRiemannianManifold.charted PointedRiemannianManifold.smooth
  PointedRiemannianManifold.t2 PointedRiemannianManifold.sigmaCompact
  PointedRiemannianManifold.t2TangentBundle

/-- Ball seeds for a given seed scale `(a, v)` supplied by Q1-scale (tail form). -/
theorem eventualBallSeedsAt_S36 (Hp : AnalyticSurgeryProfile F δ)
    (hdec : ∀ ε : ℝ, 0 < ε → ∃ B : ℝ, ∀ t : ℝ, B < t → δ t < ε)
    (hneg : EventuallyNegativeScalar_S13 F)
    (hLTF03 : ∀ (S : LatePointSequence_S13 F) (a v R : ℝ),
      SeedHyperbolicOnFixedBallsSeq_S13 Hp hdec hneg S a v R)
    (S : LatePointSequence_S13 F) {T a v : ℝ} (ha : 0 < a) (hv : 0 < v)
    (hseed : ∀ n, T ≤ (S.slices n).time → HasNormalizedSeed_S13 (S.slices n) (S.point n) a v)
    {R : ℝ} (hR : 0 < R) :
    ∃ b w2 : ℝ, 0 < b ∧ 0 < w2 ∧ ∀ᶠ n in atTop,
      ∀ q ∈ riemannianBallOf (S.slices n).normalizedMetric (S.point n) R,
        HasNormalizedSeed_S13 (S.slices n) q b w2 := by
  obtain ⟨N, hN⟩ := eventually_atTop.mp (S.times_tendsto.eventually (eventually_ge_atTop T))
  let S' : LatePointSequence_S13 F := S.subsequence (fun j => j + N) (strictMono_id.add_const N)
  obtain ⟨b, w2, hb, hw2, hev⟩ := ballSeeds_S36 Hp hdec hneg hLTF03 S' ha hv
    (fun j => hseed (j + N) (hN _ (by omega))) hR
  refine ⟨b, w2, hb, hw2, ?_⟩
  obtain ⟨M, hM⟩ := eventually_atTop.mp hev
  refine eventually_atTop.mpr ⟨M + N, fun n hn => ?_⟩
  obtain ⟨k, rfl⟩ : ∃ k, n = k + N := ⟨n - N, by omega⟩
  exact hM k (by omega)

/-- **hinj** of CX6 for `w`-thick sequences, from LTF03, W2 and Q1-scale (seed form), via the
Cheeger–Gromov–Taylor volume/curvature injectivity radius estimate. -/
theorem hinj_of_supplies_S36
    (Hp : AnalyticSurgeryProfile F δ)
    (hdec : ∀ ε : ℝ, 0 < ε → ∃ B : ℝ, ∀ t : ℝ, B < t → δ t < ε)
    (hneg : EventuallyNegativeScalar_S13 F)
    (hLTF03 : ∀ (S : LatePointSequence_S13 F) (a v R : ℝ),
      SeedHyperbolicOnFixedBallsSeq_S13 Hp hdec hneg S a v R)
    (hW2 : ∀ w : ℝ, 0 < w → ∃ T Λ b τ C : ℝ, 0 < T ∧ 1 ≤ Λ ∧ 0 < b ∧ 0 < τ ∧ 0 < C ∧
      τ * b ^ 2 < 1 / 2 ∧
      ∀ s : GC.LongTime.RegularSlice F.observation, T ≤ s.time →
      ∀ (p : (s.history.stageAt (sliceTop_S8 s)).Carrier) (r : ℝ), 0 < r →
        r ≤ b * Real.sqrt s.time →
        (∀ q ∈ riemannianBallOf (s.history.stageMetric (s.history.activeStage (sliceTop_S8 s))
            s.time) p r,
          SectionalBoundedBelowAt (s.history.stageMetric (s.history.activeStage (sliceTop_S8 s))
            s.time) q (-(r ^ 2)⁻¹)) →
        ENNReal.ofReal (w * r ^ 3) ≤ ballVolume (s.history.stageMetric
          (s.history.activeStage (sliceTop_S8 s)) s.time) p r →
        (∀ n (i : Fin (F.tower.history n).eventCount),
          (F.tower.history n).time i.succ ∈ Icc (s.time / 2) s.time →
          ∀ h, Λ * (Hp.records n i).nominalRadius h ≤ r) →
        s.history.isTracedRegion (sliceTop_S8 s) p (2 * r) (τ * r ^ 2) (C / r ^ 2))
    (w : ℝ) (hw : 0 < w)
    (hQ1 : ∀ w : ℝ, 0 < w → ∃ T a v : ℝ, 0 < a ∧ 0 < v ∧
      ∀ s : RegularSlice F.observation, T ≤ s.time → ∀ (p : s.stage.Carrier) (r : ℝ), 0 < r →
        curvatureRadius s.normalizedMetric p = ENNReal.ofReal r →
        ENNReal.ofReal (w * r ^ 3) ≤ ballVolume s.normalizedMetric p r →
        HasNormalizedSeed_S13 s p a v) :
    ∀ S : LatePointSequence_S13 F, IsWThickSequence_S13 S w →
      ∀ R : ℝ, 0 < R → ∃ η : ℝ, 0 < η ∧ ∀ᶠ n in atTop,
        ∀ x : (S.pointedSeq.connectedComponent.obj n).M,
          riemannianEDistOf (S.pointedSeq.connectedComponent.obj n).metric
            (S.pointedSeq.connectedComponent.obj n).basepoint x ≤ ENNReal.ofReal R →
          HasInjRadiusAt (S.pointedSeq.connectedComponent.obj n) x η := by
  intro S hS R hR
  obtain ⟨T, a, v, ha, hv, hQ⟩ := hQ1 w hw
  have htime : ∀ᶠ n in atTop, T ≤ (S.slices n).time :=
    S.times_tendsto.eventually (eventually_ge_atTop T)
  have hseed : ∀ n, T ≤ (S.slices n).time → HasNormalizedSeed_S13 (S.slices n) (S.point n) a v := by
    intro n hn
    obtain ⟨r, hr, hrad, hvol⟩ := hS n
    exact hQ (S.slices n) hn (S.point n) r hr hrad hvol
  have hρ : 0 < 2 * (R + 1) + a + 2 := by positivity
  obtain ⟨b, w2, hb, hw2, hev⟩ := eventualBallSeedsAt_S36 Hp hdec hneg hLTF03 S ha hv hseed hρ
  obtain ⟨T', C, hC0, hC⟩ := curvDeriv_of_seed_S36 Hp hW2 hb hw2 0
  have hA : 0 < max C 1 := lt_max_of_lt_right one_pos
  obtain ⟨ι, hι, hX⟩ := exists_uniform_injRadius_of_pointed_bounds.{u} 3 (by norm_num)
    (r := a) (v := v * a ^ 3) (S := R + 1) (A := max C 1) ha (by positivity) (by linarith) hA
  refine ⟨ι, hι, ?_⟩
  have htime' : ∀ᶠ n in atTop, T' ≤ (S.slices n).time :=
    S.times_tendsto.eventually (eventually_ge_atTop T')
  filter_upwards [hev, htime, htime'] with n hn hT hT'
  intro x hx
  let X := S.pointedSeq.obj n
  have hXc : MetricComplete X := (late_sequence_complete_CX6 S).complete n
  have hvol := (hseed n hT).2
  have hRm : ∀ y ∈ riemannianBallOf X.metric X.basepoint (2 * (R + 1) + a + 2),
      Real.sqrt (Tensor0SBundle.normSq0S X.metric y 4 (metricRm04At X.metric y)) ≤ max C 1 := by
    intro y hy
    have h1 := hC (S.slices n) hT' y (hn y hy)
    have hsq := curvatureDerivativeNorm_sq_eq_normSq0S (S.slices n).normalizedMetric 0 y
    have h0 := curvatureDerivativeNorm_nonneg (S.slices n).normalizedMetric 0 y
    have hrw : Real.sqrt (Tensor0SBundle.normSq0S X.metric y 4 (metricRm04At X.metric y)) =
        curvatureDerivativeNorm (S.slices n).normalizedMetric 0 y := by
      rw [show Tensor0SBundle.normSq0S X.metric y 4 (metricRm04At X.metric y) =
        curvatureDerivativeNorm (S.slices n).normalizedMetric 0 y ^ 2 from hsq.symm]
      exact Real.sqrt_sq h0
    rw [hrw]
    exact h1.trans (le_max_left _ _)
  have hinjX := hX X hXc hvol hRm
  let U : TopologicalSpace.Opens (S.slices n).stage.Carrier :=
    connectedComponentOpen (I := ThreeModel) (S.point n)
  let y : U := x
  have e := riemannianEDistOf_restrictOpen_of_isClosed (S.slices n).normalizedMetric U
    isClosed_connectedComponent (⟨S.point n, mem_connectedComponent⟩ : U) y
  have hd : riemannianEDistOf (S.slices n).normalizedMetric (S.point n) y.1 ≤ ENNReal.ofReal R := by
    rw [← e]; exact hx
  have hlt : y.1 ∈ riemannianBallOf X.metric X.basepoint (R + 1) := by
    change riemannianEDistOf (S.slices n).normalizedMetric (S.point n) y.1 < ENNReal.ofReal (R + 1)
    exact hd.trans_lt ((ENNReal.ofReal_lt_ofReal_iff (by linarith)).mpr (by linarith))
  exact (hasInjRadiusAt_restrictOpen_iff X U mem_connectedComponent isClosed_connectedComponent
    hXc y ι).mpr (hinjX y.1 hlt)

end GC.LongTime.Ch12
