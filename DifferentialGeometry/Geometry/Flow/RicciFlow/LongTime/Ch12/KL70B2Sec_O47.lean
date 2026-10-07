import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.BoundedCurvatureAtDistanceNecks
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch12.MicroGlueSliceTransfer
import DifferentialGeometry.Geometry.Comparison.RadialHessianLowerBound

/-!
# CH12-O47, group 2: KL70.2 B2 — `Rm ≥ 0` on the escape limit, in O38's form

`[FROZEN] CH12-O47` G2.  `escape_sec_nonneg_O47`: the tree theorem
`metricRm04StandardAt_nonneg_of_normalized_terminal_pinching` (pinching on the slab flows, curvature
normalised by `R(x_i) → ∞`) rewritten as O38's `∀ z, SectionalBoundedBelowAt gL z 0` (the `hsec0`
input of `cone_end_of_ray_necks_O39`).  `slice_escape_sec_nonneg_O47`: the same on the slice slabs
`sliceSlabR_O3 F (s i)` of a sequence of regular slices, the pinching coming from the profile
(`slice_pinching_O3 Hp`, the slice-slab form of the profile pinching used by `hpinchS_O16`), so no
pinching binder remains.
-/

set_option autoImplicit false

noncomputable section

open Set Filter Topology
open DifferentialGeometry DifferentialGeometry.CheegerGromovCompactness
open DifferentialGeometry.Geometry.Curvature DifferentialGeometry.Geometry.Riemannian
open DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
open DifferentialGeometry.PDE.RicciFlow
open DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn
open scoped Manifold ContDiff NNReal ENNReal

namespace GC.LongTime.Ch12

universe u

attribute [local instance] PointedRiemannianManifold.topology PointedRiemannianManifold.charted
  PointedRiemannianManifold.smooth PointedRiemannianManifold.t2
  PointedRiemannianManifold.sigmaCompact PointedRiemannianManifold.t2TangentBundle

private local instance {P : OrientedThreeStage.{u}} {a s : ℝ} (G : P.IncomingSlab a s) :
    SigmaCompactSpace G.terminalRegularOpen :=
  isSigmaCompact_iff_sigmaCompactSpace.mp
    (DifferentialGeometry.Geometry.isSigmaCompact_of_isOpen ThreeModel G.terminalRegularOpen.isOpen)

/-- **B2 (`Rm ≥ 0`) on the escape limit**, O38 form; binders of
`metricRm04StandardAt_nonneg_of_normalized_terminal_pinching` verbatim. -/
theorem escape_sec_nonneg_O47
    (P : ℕ → OrientedThreeStage.{u}) (a s : ℕ → ℝ) (A : ∀ i, (P i).ClosedSlab (a i) (s i))
    (x : ∀ i, ((A i).restrictIncoming le_rfl (A i).lt le_rfl).terminalRegularOpen)
    (hQ : ∀ i, 1 ≤ (A i).flow.scalar (s i) (x i).val)
    {Phi : ℝ → ℝ} (hPhi : Perelman.AdmissiblePinchingFunction Phi)
    (hpinch : ∀ i, Perelman.PhiAlmostNonnegative
      ((A i).restrictIncoming le_rfl (A i).lt le_rfl).flow (Ico (a i) (s i)) Phi)
    {f : ℕ → ℕ} (Pl : PointedRiemannianManifold.{u, 0, 0} ThreeModel)
    (F : PointedRiemannianConvergenceMaps
      ({ obj := fun i =>
          { M := ((A i).restrictIncoming le_rfl (A i).lt le_rfl).terminalRegularOpen
            basepoint := x i
            metric := scaleMetric ((A i).flow.scalar (s i) (x i).val)
              (zero_lt_one.trans_le (hQ i)) ((A i).endpointTerminalLimitMetric (P i)).metric } } :
        PointedRiemannianSeq.{u, 0, 0} ThreeModel) Pl f)
    (M : MetricConvergenceData F)
    (hcanonical : ∀ n, M.domain n = CanonicalMetricCompactness.canonicalSourceData F n)
    (hQlim : Tendsto (fun n => (A (f n)).flow.scalar (s (f n)) (x (f n)).val) atTop atTop) :
    ∀ z : Pl.M, SectionalBoundedBelowAt Pl.metric z 0 := by
  intro z v w
  have h := metricRm04StandardAt_nonneg_of_normalized_terminal_pinching P a s A x hQ hPhi hpinch
    Pl F M hcanonical hQlim z v w
  simpa only [zero_mul] using h

/-- **B2 on the slice slabs**: pinching from the profile (no binder). -/
theorem slice_escape_sec_nonneg_O47 {P₀ : OrientedThreeStage.{u}} {g₀ : P₀.Metric}
    {Fs : GC.Interface.RawSurgery P₀ g₀} {δ : ℝ → ℝ} (Hp : GC.LongTime.AnalyticSurgeryProfile Fs δ)
    (sl : ℕ → RegularSlice Fs.observation)
    (x : ∀ i, ((sliceSlabR_O3 Fs (sl i)).restrictIncoming le_rfl
      (sliceSlabR_O3 Fs (sl i)).lt le_rfl).terminalRegularOpen)
    (hQ : ∀ i, 1 ≤ (sliceSlabR_O3 Fs (sl i)).flow.scalar (sl i).time (x i).val)
    {f : ℕ → ℕ} (Pl : PointedRiemannianManifold.{u, 0, 0} ThreeModel)
    (F : PointedRiemannianConvergenceMaps
      ({ obj := fun i =>
          { M := ((sliceSlabR_O3 Fs (sl i)).restrictIncoming le_rfl
              (sliceSlabR_O3 Fs (sl i)).lt le_rfl).terminalRegularOpen
            basepoint := x i
            metric := scaleMetric ((sliceSlabR_O3 Fs (sl i)).flow.scalar (sl i).time (x i).val)
              (zero_lt_one.trans_le (hQ i)) ((sliceSlabR_O3 Fs (sl i)).endpointTerminalLimitMetric
                ((sliceHistoryR_O3 Fs (sl i)).stage
                  (Fin.last (sliceHistoryR_O3 Fs (sl i)).eventCount))).metric } } :
        PointedRiemannianSeq.{u, 0, 0} ThreeModel) Pl f)
    (M : MetricConvergenceData F)
    (hcanonical : ∀ n, M.domain n = CanonicalMetricCompactness.canonicalSourceData F n)
    (hQlim : Tendsto (fun n => (sliceSlabR_O3 Fs (sl (f n))).flow.scalar (sl (f n)).time
      (x (f n)).val) atTop atTop) :
    ∀ z : Pl.M, SectionalBoundedBelowAt Pl.metric z 0 := by
  obtain ⟨phi, hadm, hphi⟩ := slice_pinching_O3 Hp
  exact escape_sec_nonneg_O47
    (fun i => (sliceHistoryR_O3 Fs (sl i)).stage (Fin.last (sliceHistoryR_O3 Fs (sl i)).eventCount))
    (fun i => (sliceHistoryR_O3 Fs (sl i)).time (Fin.last (sliceHistoryR_O3 Fs (sl i)).eventCount))
    (fun i => (sl i).time) (fun i => sliceSlabR_O3 Fs (sl i)) x hQ hadm
    (fun i => (hphi (sl i)).2.2) Pl F M hcanonical hQlim

end GC.LongTime.Ch12
