import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.Comparison

open Set Manifold
open scoped Manifold ContDiff Topology

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

universe u

namespace GeometricCutoffRecord

variable {H : ObservedHistory.{u}} {i : Fin H.eventCount} {parameters : CutoffParameters}
  (G : GeometricCutoffRecord H i parameters)
  (c : ConnectedComponents (H.stage i.succ).Carrier)

theorem collarMap_notMem_childCore_range_of_recenter_mem_removedBand
    (b : G.ChildBoundary c) (y : Sphere 2) (t : ↑(Icc (G.comparisonLevel c b) 0))
    (hband : |(if b.1.1.2 then (1 : ℝ) else -1) * (1 + (t : ℝ))| < 1) :
    G.collarMap c b (y, t) ∉ Set.range (G.transition.childCoreIntoParent c) := by
  rintro ⟨x, hx⟩
  have hx1 : (x.1.1 : (H.stage i.castSucc).Carrier) = (G.collarMap c b (y, t)).1 := by
    rw [← hx]
    rfl
  obtain ⟨hlo, hhi⟩ := abs_lt.mp hband
  let Z : TubeDomain :=
    (y, ⟨(if b.1.1.2 then (1 : ℝ) else -1) * (1 + (t : ℝ)), by
      exact ⟨by linarith, by linarith⟩⟩)
  have hZmem : (Z.1, (Z.2 : ℝ)) ∈ neckBuffer (G.delta b.1.1.1) :=
    G.tube_in_buffer b.1.1.1 Z
  have hrem : (x.1.1 : (H.stage i.castSucc).Carrier) ∈
      G.transition.trace.tubes.removedBand b.1.1.1 := by
    refine ⟨Z, ⟨hlo, hhi⟩, ?_⟩
    calc (G.transition.trace.tubes.tube b.1.1.1) Z
        = ((G.neck b.1.1.1).chart ⟨(Z.1, (Z.2 : ℝ)), hZmem⟩).1 :=
          G.tube_eq b.1.1.1 Z hZmem
      _ = ((G.static b.1).neck.chart (G.collarParameter c b (y, t))).1 := by
          rw [G.recenter_chart b.1 (G.collarParameter c b (y, t))
            (G.recenter_in_buffer b.1 (G.collarParameter c b (y, t)))]
          congr 1
      _ = (G.collarMap c b (y, t)).1 := (G.collarMap_apply c b (y, t)).symm
      _ = x.1.1 := hx1.symm
  exact x.1.2 (Set.mem_iUnion.mpr ⟨b.1.1.1, hrem⟩)


theorem collarMap_mem_childCore_range_imp_eq_zero_of_delta_inv_le_two
    (b : G.ChildBoundary c) (y : Sphere 2) (t : ↑(Icc (G.comparisonLevel c b) 0))
    (hδ : ((G.static b.1).delta)⁻¹ ≤ 2)
    (h : G.collarMap c b (y, t) ∈ Set.range (G.transition.childCoreIntoParent c)) :
    (t : ℝ) = 0 := by
  by_contra hne
  have ht0 : (t : ℝ) < 0 := lt_of_le_of_ne t.2.2 hne
  have hlow : -(G.static b.1).delta⁻¹ < (t : ℝ) :=
    lt_of_lt_of_le (G.comparisonLevel_lower c b) t.2.1
  have hband : |(if b.1.1.2 then (1 : ℝ) else -1) * (1 + (t : ℝ))| < 1 := by
    have habs : |(if b.1.1.2 then (1 : ℝ) else -1)| = 1 := by
      cases b.1.1.2 <;> simp
    rw [abs_mul, habs, one_mul]
    exact abs_lt.mpr ⟨by linarith, by linarith⟩
  exact G.collarMap_notMem_childCore_range_of_recenter_mem_removedBand c b y t hband h

end GeometricCutoffRecord

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
