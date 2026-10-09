import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch12.ThickJetsDefect_S36
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch12.ThickLimitExtraction_CX6
import DifferentialGeometry.Geometry.Compactness.CheegerGromov.Pointed.Bounds.VolumeInjectivity
import DifferentialGeometry.Geometry.Compactness.CheegerGromov.Pointed.ConnectedComponent

set_option autoImplicit false

/-! # CH12-S36: `hjets` and `hinj` of CX6 from LTF03, W2 and the seed form of Q1-scale -/

noncomputable section
open DifferentialGeometry DifferentialGeometry.Geometry.Collapse DifferentialGeometry.Geometry.Riemannian
open DifferentialGeometry.Geometry.Curvature DifferentialGeometry.CheegerGromovCompactness
open DifferentialGeometry.PDE.RicciFlow DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
open GC.LongTime Set Filter
open scoped Manifold ContDiff ENNReal Topology

namespace GC.LongTime.Ch12
universe u
variable {P : OrientedThreeStage.{u}} {g : P.Metric} {F : GC.Interface.RawSurgery P g} {δ : ℝ → ℝ}

/-- Tail form of the ball-seed statement for a `w`-thick sequence (Q1-scale in seed form). -/
theorem eventualBallSeeds_S36 (Hp : AnalyticSurgeryProfile F δ)
    (hdec : ∀ ε : ℝ, 0 < ε → ∃ B : ℝ, ∀ t : ℝ, B < t → δ t < ε)
    (hneg : EventuallyNegativeScalar_S13 F)
    (hLTF03 : ∀ (S : LatePointSequence_S13 F) (a v R : ℝ),
      SeedHyperbolicOnFixedBallsSeq_S13 Hp hdec hneg S a v R)
    (w : ℝ) (hw : 0 < w)
    (hQ1 : ∀ w : ℝ, 0 < w → ∃ T a v : ℝ, 0 < a ∧ 0 < v ∧
      ∀ s : RegularSlice F.observation, T ≤ s.time → ∀ (p : s.stage.Carrier) (r : ℝ), 0 < r →
        curvatureRadius s.normalizedMetric p = ENNReal.ofReal r →
        ENNReal.ofReal (w * r ^ 3) ≤ ballVolume s.normalizedMetric p r →
        HasNormalizedSeed_S13 s p a v)
    (S : LatePointSequence_S13 F) (hS : IsWThickSequence_S13 S w) {R : ℝ} (hR : 0 < R) :
    ∃ a v b w2 : ℝ, 0 < a ∧ 0 < v ∧ 0 < b ∧ 0 < w2 ∧ ∀ᶠ n in atTop,
      HasNormalizedSeed_S13 (S.slices n) (S.point n) a v ∧
      ∀ q ∈ riemannianBallOf (S.slices n).normalizedMetric (S.point n) R,
        HasNormalizedSeed_S13 (S.slices n) q b w2 := by
  obtain ⟨T, a, v, ha, hv, hQ⟩ := hQ1 w hw
  obtain ⟨N, hN⟩ := eventually_atTop.mp (S.times_tendsto.eventually (eventually_ge_atTop T))
  let S' : LatePointSequence_S13 F := S.subsequence (fun j => j + N) (strictMono_id.add_const N)
  have hseed : ∀ j, HasNormalizedSeed_S13 (S'.slices j) (S'.point j) a v := by
    intro j
    obtain ⟨r, hr, hrad, hvol⟩ := hS (j + N)
    exact hQ (S.slices (j + N)) (hN _ (by omega)) (S.point (j + N)) r hr hrad hvol
  obtain ⟨b, w2, hb, hw2, hev⟩ := ballSeeds_S36 Hp hdec hneg hLTF03 S' ha hv hseed hR
  refine ⟨a, v, b, w2, ha, hv, hb, hw2, ?_⟩
  obtain ⟨M, hM⟩ := eventually_atTop.mp hev
  refine eventually_atTop.mpr ⟨M + N, fun n hn => ?_⟩
  obtain ⟨k, rfl⟩ : ∃ k, n = k + N := ⟨n - N, by omega⟩
  exact ⟨hseed k, hM k (by omega)⟩

attribute [local instance] PointedRiemannianManifold.topology
  PointedRiemannianManifold.charted PointedRiemannianManifold.smooth
  PointedRiemannianManifold.t2 PointedRiemannianManifold.sigmaCompact
  PointedRiemannianManifold.t2TangentBundle

/-- **hjets** of CX6 for `w`-thick sequences, from LTF03, W2 and Q1-scale (seed form). -/
theorem hjets_of_supplies_S36 (Hp : AnalyticSurgeryProfile F δ)
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
      ∀ R : ℝ, 0 < R → ∀ p : ℕ, ∃ C : ℝ, 0 ≤ C ∧
        ∀ᶠ n in atTop, HasLocalCurvDerivBound
          (S.pointedSeq.connectedComponent.obj n) (S.pointedSeq.connectedComponent.obj n).basepoint
          R p C := by
  intro S hS R hR m
  obtain ⟨a, v, b, w2, ha, hv, hb, hw2, hev⟩ :=
    eventualBallSeeds_S36 Hp hdec hneg hLTF03 w hw hQ1 S hS (show 0 < R + 1 by linarith)
  obtain ⟨T, C, hC0, hC⟩ := curvDeriv_of_seed_S36 Hp hW2 hb hw2 m
  refine ⟨C, hC0, ?_⟩
  have htime : ∀ᶠ n in atTop, T ≤ (S.slices n).time :=
    S.times_tendsto.eventually (eventually_ge_atTop T)
  filter_upwards [hev, htime] with n hn hT
  exact localJets_component_S36 S n R m C
    (fun q hq => hC (S.slices n) hT q (hn.2 q hq)) hR.le

end GC.LongTime.Ch12
