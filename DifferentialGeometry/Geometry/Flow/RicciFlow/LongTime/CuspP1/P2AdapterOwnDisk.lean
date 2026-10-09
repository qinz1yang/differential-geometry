import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.CuspP1.MeridianTop
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.CuspP1.P2AdapterOwnLoop
import DifferentialGeometry.Geometry.Measure.Area.SpanningComponent
import DifferentialGeometry.Geometry.Metric.LoopLipschitz
import DifferentialGeometry.External.CanonicalTopology.Topology.LoopSpace.ContinuousFilling

/-!
# P2A-13 (step 3): non-emptiness of the spanning-disk competitor class from `fills`
-/

set_option autoImplicit false
noncomputable section
open DifferentialGeometry DifferentialGeometry.Topology DifferentialGeometry.Geometry
open DifferentialGeometry.PDE.RicciFlow.Surgery.Topology GC.Endpoint Set
open scoped Manifold ContDiff
namespace GC.LongTime.CuspP1
universe u
open GC.LongTime

/-- Generic form: a smooth loop in a stage carrier which bounds a continuous disk has a non-empty
spanning-disk competitor class (any metric of the stage). -/
theorem spanningDiskCompetitors_nonempty_of_filling_P2A {P : OrientedThreeStage.{u}}
    (h : P.Metric) {γ : freeLoop P.Carrier}
    (hs : ContMDiff 𝓘(ℝ, ℝ) ThreeModel ∞ (fun t : ℝ => γ (t : loopCircle)))
    (hfill : ∃ u : C(closedDisk, P.Carrier), diskTrace u = γ) :
    (spanningDiskCompetitors h γ).Nonempty := by
  obtain ⟨u, hu⟩ := hfill
  obtain ⟨L, hL⟩ := exists_riemannian_lipschitz_freeLoop_of_contMDiff h (hs.of_le (by simp))
  exact spanningDiskCompetitors_nonempty_of_compact h hL (hu ▸ diskTrace_nullhomotopic u)

variable {P : OrientedThreeStage.{u}} {g : P.Metric} {F : GC.Interface.RawSurgery P g} {K : ℕ}
  {cores : PersistentHyperbolicCores F K}

/-- Step 3 (IMS03): from `fills`, the spanning-disk competitor class of the transported meridian
for the stage metric `postMetric` is non-empty (no auxiliary open set is needed: the stage carrier
is compact, and the competitor class is taken in the whole carrier). -/
theorem PrescribedCuspMeridianTop_CPQ.spanningDiskCompetitors_nonempty_P2A
    (M : PrescribedCuspMeridianTop_CPQ cores) (t : ℝ) (ht : M.exterior.start ≤ t) :
    (spanningDiskCompetitors (postMetric F.observation t) (M.transported t ht)).Nonempty := by
  obtain ⟨u, hu, -⟩ := M.fills t ht
  exact spanningDiskCompetitors_nonempty_of_filling_P2A _
    (M.transported_isSmoothEmbeddedLoop_P2A t ht).smooth ⟨u, hu⟩

end GC.LongTime.CuspP1
