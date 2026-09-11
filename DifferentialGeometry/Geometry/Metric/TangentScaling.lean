import Mathlib.Geometry.Manifold.VectorBundle.Tangent
import Mathlib.Topology.VectorBundle.Basic



noncomputable section

open Bundle Manifold Set Filter
open scoped Topology Manifold

namespace DifferentialGeometry.Geometry

variable {X E : Type*} [TopologicalSpace X]
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 1 M]



theorem continuous_tangent_smul {a : X → ℝ} {v : X → TangentBundle I M}
    (ha : Continuous a) (hv : Continuous v) :
    Continuous (fun x => (TotalSpace.mk' E (v x).proj (a x • (v x).2) : TangentBundle I M)) := by
  apply continuous_iff_continuousAt.mpr
  intro x
  let e := trivializationAt E (TangentSpace I) (v x).proj
  obtain ⟨hb, hd⟩ := (FiberBundle.continuousAt_totalSpace E v).mp (hv.continuousAt (x := x))
  apply (FiberBundle.continuousAt_totalSpace E _).mpr
  refine ⟨hb, ?_⟩
  have hc := ha.continuousAt.smul hd
  apply hc.congr_of_eventuallyEq
  have hbase : ∀ᶠ y in 𝓝 x, (v y).proj ∈ e.baseSet :=
    hb.eventually_mem (e.open_baseSet.mem_nhds (mem_baseSet_trivializationAt E (TangentSpace I) _))
  filter_upwards [hbase] with y hy
  exact (e.linear ℝ hy).map_smul (a y) (v y).2

end DifferentialGeometry.Geometry
