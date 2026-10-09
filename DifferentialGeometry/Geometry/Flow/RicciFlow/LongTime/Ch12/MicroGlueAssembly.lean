import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch12.MicroGlueLocalKernel
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch12.MicroGlueVolumeTest

/-!
# CH12-O3, group 3: W4 with a local κ(w), and the composite micro-scale scalar bound

* `W4_scalar_bound_local_O3`: the profile form (`ε, C1, C2 := Hp.epsilon, Hp.C1, Hp.C2`, P4) of
  the local kernel `exists_scalar_bound_at_distance_local_O3`.  Unlike `W4_scalar_bound_O2` it does
  not need a fixed global `κ`-noncollapsing; `κ` enters only through a terminal-time volume test
  near the point.
* `micro_scalar_bound_of_volume_test_O3`: the local kernel fed with the local volume test produced
  by the `w`-test of a test ball (`local_volume_of_volume_test_O3`).  The constants `Q, Λ` depend
  only on `(w, C1, C2, Ctime, Cgrad, phi, ε, A, Cq)`.  At every time `t` of a final slab, for every
  test ball `B_t(p, r)` (`sec ≥ -r⁻²`, `vol ≥ w r³`) and every `y ∈ B_t(p, r/8)` with
  `Λ ≤ (r/8)√R(y)` and the remaining (non-volume) kernel premises, `R ≤ Q R(y)` on
  `B_t(y, A/√R(y))`.  This is the zero-order micro estimate of D-WBD §5 at a point, with the
  profile's decaying `kappa` replaced by `κ(w)`.
-/

set_option autoImplicit false

noncomputable section

open Set Filter
open DifferentialGeometry DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
open DifferentialGeometry.PDE.RicciFlow
open DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn
open DifferentialGeometry.Geometry.Riemannian
open scoped Manifold ContDiff Topology NNReal ENNReal

namespace GC.LongTime.Ch12

universe u

/-- **W4 with a local κ** (profile form, under P4). -/
theorem W4_scalar_bound_local_O3 {P : OrientedThreeStage.{u}} {g : P.Metric}
    {F : GC.Interface.RawSurgery P g} {δ : ℝ → ℝ} (Hp : GC.LongTime.AnalyticSurgeryProfile F δ)
    (hP4 : P4_O2 Hp) (κ : ℝ) (hκ : 0 < κ) (Ctime Cgrad : ℝ≥0) {phi : ℝ → ℝ}
    (hphi : Perelman.AdmissiblePinchingFunction phi) :
    ∀ A : ℝ, 0 < A → ∀ Cq : ℝ,
      ∃ Q Λ : ℝ, 1 ≤ Q ∧ 1 ≤ Λ ∧
      ∀ (H : RetainedCoreHistory.{u})
        (hend : H.time (Fin.last H.eventCount) = H.horizon) {t : ℝ}
        (S : (H.stage (Fin.last H.eventCount)).ClosedSlab (H.time (Fin.last H.eventCount)) t)
        (hS : S.flow.base.metric (H.time (Fin.last H.eventCount)) =
          H.initialMetric (Fin.last H.eventCount))
        (y : (H.stage (Fin.last H.eventCount)).Carrier) (q ρ : ℝ),
        0 < q → q ≤ Cq * S.flow.scalar t y → Λ ≤ S.flow.scalar t y →
        H.time (Fin.last H.eventCount) ≤ t - Λ / S.flow.scalar t y →
        (∀ x, q < S.flow.scalar t x →
          ∃ W : SpatialCanonicalWitness (S.flow.base.metric t) Hp.epsilon Hp.C1 Hp.C2 x,
            W.capTubeHasNeckChart Hp.epsilon) →
        H.EventSlabsDerivative Ctime q (Fin.last H.eventCount) →
        (S.restrictIncoming le_rfl S.lt le_rfl).DerivativeBoundBefore Ctime q t →
        (S.restrictIncoming le_rfl S.lt le_rfl).GradientBoundBefore Cgrad q t →
        H.EventSlabsPinched phi →
        Perelman.PhiAlmostNonnegative (S.restrictIncoming le_rfl S.lt le_rfl).flow
          (Ico (H.time (Fin.last H.eventCount)) t) phi →
        (∀ z : (H.stage (Fin.last H.eventCount)).Carrier,
          riemannianEDistOf (S.flow.base.metric t) y z < ENNReal.ofReal ρ →
          ∀ b : ℝ, 0 < b → b ≤ ρ →
            ENNReal.ofReal κ * ENNReal.ofReal b ^ 3 ≤
              riemannianVolumeMeasure ThreeModel (H.stage (Fin.last H.eventCount)).Carrier
                (S.flow.base.metric t) (riemannianBallOf (S.flow.base.metric t) z b)) →
        Λ ≤ ρ * Real.sqrt (S.flow.scalar t y) →
        ∀ z ∈ riemannianBallOf (S.flow.base.metric t) y (A / Real.sqrt (S.flow.scalar t y)),
          S.flow.scalar t z ≤ Q * S.flow.scalar t y :=
  exists_scalar_bound_at_distance_local_O3.{u} κ Hp.C1 Hp.C2 hκ Ctime Cgrad hphi Hp.epsilon hP4

/-- **Composite micro-scale scalar bound** (local kernel + `w`-volume test of a test ball). -/
theorem micro_scalar_bound_of_volume_test_O3 (w : ℝ) (hw : 0 < w) (C1 C2 : ℝ)
    (Ctime Cgrad : ℝ≥0) {phi : ℝ → ℝ} (hphi : Perelman.AdmissiblePinchingFunction phi) :
    ∀ ε : ℝ, ε ≤ εKL70_O2 → ∀ A : ℝ, 0 < A → ∀ Cq : ℝ,
      ∃ Q Λ : ℝ, 1 ≤ Q ∧ 1 ≤ Λ ∧
      ∀ (H : RetainedCoreHistory.{u})
        (hend : H.time (Fin.last H.eventCount) = H.horizon) {t : ℝ}
        (S : (H.stage (Fin.last H.eventCount)).ClosedSlab (H.time (Fin.last H.eventCount)) t)
        (hS : S.flow.base.metric (H.time (Fin.last H.eventCount)) =
          H.initialMetric (Fin.last H.eventCount))
        (p y : (H.stage (Fin.last H.eventCount)).Carrier) (r q : ℝ), 0 < r →
        (∀ x ∈ riemannianBallOf (S.flow.base.metric t) p r,
          SectionalBoundedBelowAt (S.flow.base.metric t) x (-(r ^ 2)⁻¹)) →
        ENNReal.ofReal (w * r ^ 3) ≤
          riemannianVolumeMeasure ThreeModel (H.stage (Fin.last H.eventCount)).Carrier
            (S.flow.base.metric t) (riemannianBallOf (S.flow.base.metric t) p r) →
        y ∈ riemannianBallOf (S.flow.base.metric t) p (r / 8) →
        0 < q → q ≤ Cq * S.flow.scalar t y → Λ ≤ S.flow.scalar t y →
        H.time (Fin.last H.eventCount) ≤ t - Λ / S.flow.scalar t y →
        (∀ x, q < S.flow.scalar t x →
          ∃ W : SpatialCanonicalWitness (S.flow.base.metric t) ε C1 C2 x,
            W.capTubeHasNeckChart ε) →
        H.EventSlabsDerivative Ctime q (Fin.last H.eventCount) →
        (S.restrictIncoming le_rfl S.lt le_rfl).DerivativeBoundBefore Ctime q t →
        (S.restrictIncoming le_rfl S.lt le_rfl).GradientBoundBefore Cgrad q t →
        H.EventSlabsPinched phi →
        Perelman.PhiAlmostNonnegative (S.restrictIncoming le_rfl S.lt le_rfl).flow
          (Ico (H.time (Fin.last H.eventCount)) t) phi →
        Λ ≤ r / 8 * Real.sqrt (S.flow.scalar t y) →
        ∀ z ∈ riemannianBallOf (S.flow.base.metric t) y (A / Real.sqrt (S.flow.scalar t y)),
          S.flow.scalar t z ≤ Q * S.flow.scalar t y := by
  obtain ⟨κ, hκ, hvolκ⟩ := local_volume_of_volume_test_O3.{u} w hw
  intro ε hε A hA Cq
  obtain ⟨Q, Λ, hQ, hΛ, hker⟩ :=
    exists_scalar_bound_at_distance_local_O3.{u} κ C1 C2 hκ Ctime Cgrad hphi ε hε A hA Cq
  refine ⟨Q, Λ, hQ, hΛ, ?_⟩
  intro H hend t S hS p y r q hr hsec hvol hy hq hqy hΛy hwin hW hderiv hfinal hgrad hpinch
    hpinchF hρ
  exact hker H hend S hS y q (r / 8) hq hqy hΛy hwin hW hderiv hfinal hgrad hpinch hpinchF
    (hvolκ (H.stage (Fin.last H.eventCount)).Carrier (S.flow.base.metric t) p r hr hsec hvol y hy)
    hρ

end GC.LongTime.Ch12
