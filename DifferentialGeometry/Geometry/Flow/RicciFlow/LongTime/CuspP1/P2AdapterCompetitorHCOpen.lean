import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.CuspP1.MeridianTop
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.CuspP1.P2AdapterCompetitorHC

/-!
# S-HCOMP G2: competitors inside the open target `U` (the exact type of `hcomp`)

`PrescribedCuspMeridianTop_CPQ.exists_eventual_confined_morrey_disk_P2A`
(`P2AdapterImportedTop.lean:266`) takes the explicit hypothesis `hcomp`: for every open `U`
containing the exterior region and every smooth Riemannian metric `G` on `U`, the transported
meridian, viewed as a smooth embedded loop `γU` in `U`, has a non-empty spanning-disk competitor
class `spanningDiskCompetitors G γU` (disks in `U`, `G`-Lipschitz, with trace exactly `γU`).

`competitors_nonempty_HC` proves exactly that statement from `M.fills` (a continuous disk in the
region, hence in `U`) and G1 (`exists_smoothDiskExtension_diskTrace_of_continuous_HC` through
`spanningDiskCompetitors_nonempty_of_filling_HC`, applied to the open manifold `U` itself).  No
property of `U` or `G` is used beyond `region ⊆ U`; no compactness of `U` is needed.
-/

set_option autoImplicit false
noncomputable section

open Bundle Filter Manifold Set TopologicalSpace
open DifferentialGeometry DifferentialGeometry.Topology DifferentialGeometry.Geometry
open DifferentialGeometry.PDE.RicciFlow.Surgery.Topology GC.Endpoint GC.LongTime
open scoped Manifold ContDiff Topology

namespace GC.LongTime.CuspP1

universe u

variable {P : OrientedThreeStage.{u}} {g : P.Metric} {F : GC.Interface.RawSurgery P g} {K : ℕ}
  {cores : PersistentHyperbolicCores F K}

/-- **G2.**  The exact type of the explicit hypothesis `hcomp` of
`exists_eventual_confined_morrey_disk_P2A`, proved from `fills`. -/
theorem PrescribedCuspMeridianTop_CPQ.competitors_nonempty_HC
    (M : PrescribedCuspMeridianTop_CPQ cores) :
    ∀ (t : ℝ) (ht : M.exterior.start ≤ t)
      (U : Opens (postStage F.observation t).Carrier)
      (G : SmoothRiemannianMetric (𝓡 3) U) (γU : freeLoop U),
      (⟨Subtype.val, continuous_subtype_val⟩ :
        C(U, (postStage F.observation t).Carrier)).comp γU = M.transported t ht →
      IsSmoothEmbeddedLoop (E := EuclideanSpace ℝ (Fin 3)) γU →
      M.exterior.region t ⊆ U → (spanningDiskCompetitors G γU).Nonempty := by
  intro t ht U G γU hγeq hγ hWU
  obtain ⟨u, hu, hrange⟩ := M.fills t ht
  have hmem (z : closedDisk) : u z ∈ U := hWU (hrange (mem_range_self z))
  let u' : C(closedDisk, U) := ⟨fun z => ⟨u z, hmem z⟩, u.continuous.subtype_mk hmem⟩
  have hu' : diskTrace u' = γU := by
    ext θ
    have h1 := congrArg (fun η : freeLoop (postStage F.observation t).Carrier => η θ) hγeq
    have h2 := congrArg (fun η : freeLoop (postStage F.observation t).Carrier => η θ) hu
    exact h2.trans h1.symm
  exact spanningDiskCompetitors_nonempty_of_filling_HC G hγ.smooth ⟨u', hu'⟩

end GC.LongTime.CuspP1
