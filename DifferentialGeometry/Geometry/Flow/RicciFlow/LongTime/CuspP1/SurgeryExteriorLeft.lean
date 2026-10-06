import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.CuspP1.SurgeryExteriorLeftBasic
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.CuspP1.SurgeryExteriorParent
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.CuspP1.SurgeryExteriorLPC

/-!
# CP1-D8 (G4): the left side of a surgery time (Q5)
-/

set_option autoImplicit false
noncomputable section
open Set Filter Topology Manifold DifferentialGeometry DifferentialGeometry.Topology GC.Endpoint
open DifferentialGeometry.Geometry.Hyperbolic
open DifferentialGeometry.PDE.RicciFlow.Surgery.Topology GC.LongTime
open scoped Manifold ContDiff
namespace GC.LongTime.CuspP1
universe u

variable {P : OrientedThreeStage.{u}} {g : P.Metric} {F : GC.Interface.RawSurgery P g}
  {K : ℕ} {slices : ℕ → RegularSlice F.observation}

/-- points outside the exterior region are exactly the images of interior points of the cores -/
theorem notMem_region_iff_CPD8 {L : LateCutFamily F K slices} (E : PersistentCuspExterior L.cores)
    (t : ℝ) (ht : E.start ≤ t) (o : (postStage F.observation t).Carrier) :
    o ∉ E.region t ↔ ∃ (i : Fin L.cores.count) (c : (E.truncation i).core.Carrier),
      c ∈ ((E.truncation i).core.interior : Set (E.truncation i).core.Carrier) ∧
        L.cores.map i t (E.after_cores.trans ht) ((E.truncation i).inclusion c) = o := by
  unfold PersistentCuspExterior.region
  rw [dif_pos ht, mem_compl_iff, not_not]
  simp only [mem_iUnion, mem_image]
  constructor
  · rintro ⟨i, y, ⟨c, hc, rfl⟩, rfl⟩
    exact ⟨i, c, hc, rfl⟩
  · rintro ⟨i, c, hc, rfl⟩
    exact ⟨i, _, ⟨c, hc, rfl⟩, rfl⟩

theorem continuous_cuspZero_CPD8 {L : LateCutFamily F K slices} (E : PersistentCuspExterior L.cores)
    (i : Fin L.cores.count) (q : Fin (E.truncation i).count) :
    Continuous fun x : Torus => (E.truncation i).cuspMap q (x, halfZero) := by
  have := ((E.truncation i).cuspEmbedding q).contMDiff.continuous
  exact this.comp (continuous_id.prodMk continuous_const)

end GC.LongTime.CuspP1
