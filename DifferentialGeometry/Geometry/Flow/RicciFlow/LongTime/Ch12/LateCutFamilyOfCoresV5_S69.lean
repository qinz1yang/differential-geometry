import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch12.LateCutFamilyOfCoresV4_S59
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch12.HNCB_S69

set_option autoImplicit false

/-!
# CH12-S69 (G2): A09 from cores, v5 -- `hNCB` discharged

`exists_late_cut_family_of_cores_v4_S59` left `hNCB` besides the buffered cores `B` and the
truncation `base`.  `hNCB` is now `hNCB_S69`; the conclusion is still the verbatim A09
`exists_late_cut_family`, and only `B` and `base` remain.
-/

noncomputable section

open DifferentialGeometry DifferentialGeometry.Topology
open DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
open DifferentialGeometry.Geometry.Collapse DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Geometry.Riemannian DifferentialGeometry.Geometry
open GC.Endpoint GC.GraphManifold DifferentialGeometry.Geometry.Hyperbolic Set
open GC.Topology GC.LongTime
open scoped Manifold ContDiff ENNReal

universe u

namespace GC.LongTime.Ch12

/-- **A09 from cores, v5 (CH12-S69 G2).**  Conclusion verbatim `exists_late_cut_family`; as v4 with
`hNCB := hNCB_S69 slices htimes B base`.  Remaining inputs: `B` and `base` only. -/
theorem exists_late_cut_family_of_cores_v5_S69 {P : OrientedThreeStage.{u}} {g : P.Metric}
    (F : GC.Interface.RawSurgery P g) (K : ℕ) (hK : lateDerivativeOrder ≤ K) (δ : ℝ → ℝ)
    (hadm : hasAnalyticAdmissibility F δ)
    (hdec : ∀ ε : ℝ, 0 < ε → ∃ B : ℝ, ∀ t : ℝ, B < t → δ t < ε)
    (slices : ℕ → RegularSlice F.observation)
    (htimes : ∀ j : ℕ, (j : ℝ) < (slices j).time)
    (hnonempty : ∀ j : ℕ, Nonempty (slices j).stage.Carrier)
    (B : BufferedPersistentCores F (K + 4))
    (base : ∀ i : Fin B.count, HyperbolicTruncation (B.model i)) :
    Nonempty (LateCutFamily F K slices) :=
  exists_late_cut_family_of_cores_v4_S59 F K hK δ hadm hdec slices htimes hnonempty B base
    (hNCB_S69 slices htimes B base)

end GC.LongTime.Ch12
