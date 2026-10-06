import
  DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Closure.Inhabitants.SolidTorusEdgeModelsSTR

/-!
# S-SOLIDTORUS2 (suffix `_STR`), G2 consumer

What a consumer of the edge piece reads: one interval component and no circle component, the two
end disks of the handle are the whole disks over the two distinct endpoints `t = 0, 1` of `C₂` and
are disjoint, the handle is the whole component, and the edge facts of the cut are the facts of the
actual restriction of the edge stage.
-/

set_option autoImplicit false

noncomputable section

open Set Function
open DifferentialGeometry DifferentialGeometry.Topology GC.Endpoint GC.GraphManifold

namespace GC.GraphManifold.Assembly.FC39P0.SolidTorusSTR

open GC.GraphManifold.Assembly.FC39P0.SolidTorusSTI GC.GraphManifold.Assembly.FC39P0

variable (Z : ZeroDomains Wc)

theorem edgeModels_counts_STR :
    (edgeComponentModels_STR Z).intervalCount = 1 ∧ (edgeComponentModels_STR Z).circleCount = 0 :=
  ⟨rfl, rfl⟩

/-- The end disks of the handle are the whole disks over the registered endpoints. -/
theorem edgeHandle_endDisk_STR (b : Bool) :
    edgeHandle_STR.endDisk b =
      (edgeBundle_STR Z).disk ((edgeComponentModels_STR Z).endpointEquiv ((0 : Fin 1), b)).1 :=
  (edgeComponentModels_STR Z).intervalTriv_disk (0 : Fin 1) (iccEnd b)

/-- The two end disks of the handle are disjoint (the handle is an embedded `D² × [0, 1]`). -/
theorem edgeHandle_endDisks_disjoint_STR :
    Disjoint (edgeHandle_STR.endDisk false) (edgeHandle_STR.endDisk true) := by
  rw [disjoint_iff_inter_eq_empty]
  apply eq_empty_iff_forall_notMem.mpr
  intro y hy
  obtain ⟨a, ha⟩ := hy.1
  obtain ⟨b, hb⟩ := hy.2
  have heq := edgeHandle_STR.injective (ha.trans hb.symm)
  have hend := congrArg (fun z : ClosedCell 2 × Icc (0 : ℝ) 1 => z.2.val) heq
  norm_num [iccEnd] at hend

/-- The edge handle is the whole component of the edge piece over `C₂`. -/
theorem edgeHandle_range_STR :
    range edgeHandle_STR.map =
      (edgeBundle_STR Z).wholeComponent
        ((edgeComponentModels_STR Z).componentEquiv (Sum.inl (0 : Fin 1))) :=
  (edgeComponentModels_STR Z).intervalTriv_range (0 : Fin 1)

/-- The edge piece `M^edge` is the image of the handle: a ball-sized `D² × [0, 1]`. -/
theorem edgePiece_eq_handle_STR : (edgeBundle_STR Z).edgePiece = range edgeHandle_STR.map := by
  rw [edgeHandle_range_STR Z]
  ext y
  constructor
  · rintro ⟨x, ⟨hc, hh⟩, rfl⟩
    refine ⟨x, ⟨?_, hh⟩, rfl⟩
    change _ ∈ (cbaseComp_STR.1)
    rw [cbaseComp_val_STR]
    exact hc
  · rintro ⟨x, ⟨hc, hh⟩, rfl⟩
    refine ⟨x, ⟨?_, hh⟩, rfl⟩
    have hc' : (edgeBundle_STR Z).proj x ∈ cbaseComp_STR.1 := hc
    rw [cbaseComp_val_STR] at hc'
    exact hc'

end GC.GraphManifold.Assembly.FC39P0.SolidTorusSTR
