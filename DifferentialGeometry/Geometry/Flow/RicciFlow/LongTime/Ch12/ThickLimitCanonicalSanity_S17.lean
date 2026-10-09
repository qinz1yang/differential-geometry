import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch12.ThickLimitInterfaceProps
import DifferentialGeometry.Geometry.Compactness.CheegerGromov.Pointed.Convergence.AmbientQuadraticControl

/-!
# CH12-S17: sanity for the canonical clause of `PointedSmoothConverges_S13`

After the F1 fix, `PointedSmoothConverges_S13 S M` constrains the metrics: the pullbacks of the
actual normalised slice metrics converge to the limit metric, uniformly on compact sets
(`C^0` in the quadratic-form sense, and pointwise on all of `T M × T M`).
-/

set_option autoImplicit false
noncomputable section
open DifferentialGeometry DifferentialGeometry.Topology DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Geometry.Hyperbolic DifferentialGeometry.Geometry.Collapse
open DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
open DifferentialGeometry.CheegerGromovCompactness
open GC.LongTime Set Filter
open scoped Manifold ContDiff ENNReal Topology
namespace GC.LongTime.Ch12
universe u

section
variable (M : FiniteVolumeHyperbolicModel.{u})
variable {P : OrientedThreeStage.{u}} {g : P.Metric} {F : GC.Interface.RawSurgery P g}
  (S : LatePointSequence_S13 F)
local instance seqTop_S17 (k : ℕ) : TopologicalSpace (S.pointedSeq.obj k).M := (S.pointedSeq.obj k).topology
local instance seqCh_S17 (k : ℕ) : ChartedSpace ThreeSpace (S.pointedSeq.obj k).M := (S.pointedSeq.obj k).charted
local instance modelTop_S17 : TopologicalSpace (modelPointed_S13 M).M := (modelPointed_S13 M).topology
local instance modelCh_S17 : ChartedSpace ThreeSpace (modelPointed_S13 M).M := (modelPointed_S13 M).charted
local instance modelSm_S17 : IsManifold ThreeModel ∞ (modelPointed_S13 M).M := (modelPointed_S13 M).smooth
local instance modelT2_S17 : T2Space (modelPointed_S13 M).M := (modelPointed_S13 M).t2
local instance modelSc_S17 : SigmaCompactSpace (modelPointed_S13 M).M := (modelPointed_S13 M).sigmaCompact

/-- Canonical convergence forces `Φ_k^* g_k → g_∞` in `C^0` on every compact `K`:
`|g_k(dΦ v, dΦ v) - g_∞(v,v)| ≤ ε g_∞(v,v)` for all `x ∈ K`, `v`, eventually. -/
theorem PointedSmoothConverges_S13.quad_close_S17 {M : FiniteVolumeHyperbolicModel.{u}} (h : PointedSmoothConverges_S13 S M) :
    ∃ Φ : PointedRiemannianConvergenceMaps S.pointedSeq (modelPointed_S13 M) id,
      ∀ K : Set (modelPointed_S13 M).M, IsCompact K → ∀ ε : ℝ, 0 < ε → ∃ k0 : ℕ, ∀ k, k0 ≤ k →
        K ⊆ Φ.source k ∧ ∀ x ∈ K, ∀ v : TangentSpace ThreeModel x,
          |(S.slices k).normalizedMetric.inner (Φ.map k x)
              (mfderiv ThreeModel ThreeModel (Φ.map k) x v)
              (mfderiv ThreeModel ThreeModel (Φ.map k) x v) - (modelPointed_S13 M).metric.inner x v v| ≤
            ε * (modelPointed_S13 M).metric.inner x v v := by
  obtain ⟨Φ, C, hcan⟩ := h
  have href : ∀ k, (C.domain k).referenceMetric = (C.domain k).limitMetric := by
    intro k; rw [hcan k]; rfl
  exact ⟨Φ, fun K hK ε hε =>
    PDE.RicciFlow.Perelman.KappaSolutions.exists_pointed_full_ambient_quadratic_control
      C href K hK ε hε⟩

/-- Pointwise: `(Φ_k^* g_k)(v,w) → g_∞(v,w)` at every point of the limit. -/
theorem PointedSmoothConverges_S13.tendsto_inner_S17 {M : FiniteVolumeHyperbolicModel.{u}} (h : PointedSmoothConverges_S13 S M) :
    ∃ Φ : PointedRiemannianConvergenceMaps S.pointedSeq (modelPointed_S13 M) id,
      ∀ (x : (modelPointed_S13 M).M) (v w : TangentSpace ThreeModel x),
        Tendsto (fun k => (S.slices k).normalizedMetric.inner (Φ.map k x)
            (mfderiv ThreeModel ThreeModel (Φ.map k) x v)
            (mfderiv ThreeModel ThreeModel (Φ.map k) x w)) atTop
          (𝓝 ((modelPointed_S13 M).metric.inner x v w)) := by
  obtain ⟨Φ, C, hcan⟩ := h
  have href : ∀ k, (C.domain k).referenceMetric = (C.domain k).limitMetric := by
    intro k; rw [hcan k]; rfl
  exact ⟨Φ, fun x v w => C.tendsto_pullback_inner href x v w⟩

end

end GC.LongTime.Ch12
