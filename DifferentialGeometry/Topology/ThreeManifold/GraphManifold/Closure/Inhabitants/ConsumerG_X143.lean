import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Closure.Inhabitants.SphereG_X143

/-! X143: concrete consumers of the produced handles, fibres and labelled rim charts. -/

set_option autoImplicit false
noncomputable section
open Set Function
open DifferentialGeometry DifferentialGeometry.Topology GC.Endpoint GC.Seifert GC.GraphManifold
open GC.GraphManifold.Assembly GC.GraphManifold.Assembly.FC39P0
open scoped Manifold ContDiff Topology

namespace GC.GraphManifold.Assembly.FC39P0.General_X143.Consumer

def firstHandle_X143 : Fin sphereAdapted_X143.edges.handleCount :=
  ⟨0, by change 0 < sphereCertificate_X143.1.handleCount
         rw [sphereCertificate_twoHandles_X143]; decide⟩

def secondHandle_X143 : Fin sphereAdapted_X143.edges.handleCount :=
  ⟨1, by change 1 < sphereCertificate_X143.1.handleCount
         rw [sphereCertificate_twoHandles_X143]; decide⟩

theorem distinctHandles_X143 : firstHandle_X143 ≠ secondHandle_X143 := by
  intro h
  have hv := congrArg Fin.val h
  change (0 : ℕ) = 1 at hv
  exact Nat.zero_ne_one hv

def middleTime_X143 : Icc (0 : ℝ) 1 := ⟨1 / 2, by norm_num, by norm_num⟩

/-- A concrete interior slice point lies in the whole registered row disk. -/
theorem centre_mem_registeredDisk_X143 :
    (sphereCertificate_X143.1.handle firstHandle_X143).map (closedCellCenter 2, middleTime_X143) ∈
      spherePrepared_X143.rows.edge.disk (spherePrepared_X143.rows.edgeModels.intervalBase
        (sphereAdapted_X143.components.handleEquiv firstHandle_X143) middleTime_X143) := by
  rw [← sphereCertificate_disk_X143 firstHandle_X143 middleTime_X143]
  exact mem_range_self (closedCellCenter 2)

/-- The two distinct handles remain registered to distinct whole base components. -/
theorem distinctComponents_X143 :
    spherePrepared_X143.rows.edgeModels.componentEquiv (.inl
      (sphereAdapted_X143.components.handleEquiv firstHandle_X143)) ≠
      spherePrepared_X143.rows.edgeModels.componentEquiv (.inl
        (sphereAdapted_X143.components.handleEquiv secondHandle_X143)) := by
  intro h
  apply distinctHandles_X143
  exact sphereAdapted_X143.components.handleEquiv.injective
    (Sum.inl_injective (spherePrepared_X143.rows.edgeModels.componentEquiv.injective h))

/-- Both endpoints of an actual handle are distinct in the native endpoint registration. -/
theorem distinctEnds_X143 :
    sphereAdapted_X143.components.endOfHandle firstHandle_X143 false ≠
      sphereAdapted_X143.components.endOfHandle firstHandle_X143 true := by
  intro h
  have hp : (firstHandle_X143, false) = (firstHandle_X143, true) :=
    sphereAdapted_X143.components.endOfHandle_injective h
  have hb := congrArg Prod.snd hp
  exact Bool.false_ne_true hb

/-- Consume the SAME certificate's product clause and the general derived compatibility result. -/
theorem product_and_fibre_X143 : sphereCertificate_X143.1.RimProduct ∧
  sphereCertificate_X143.1.EdgeCircleFibreCompatible :=
  ⟨sphereCertificate_rimProduct_X143, sphereCertificate_fibre_X143⟩

/-- An actual rim fibre of the nonempty handle family is also a full circle-region fibre. -/
theorem firstMiddleRim_X143 : ∃ b : sphereCertificate_X143.1.circ.Base,
    (fun w => (sphereCertificate_X143.1.handle firstHandle_X143).map (w, middleTime_X143)) ''
      diskRim =
      Subtype.val '' (sphereCertificate_X143.1.circ.proj ⁻¹' {b}) :=
  sphereCertificate_X143.1.vertical_fibre firstHandle_X143 middleTime_X143

theorem firstVerticalRegistration_X143 :
    sphereAdapted_X143.labelled.globalFaces.faceOfDefining
      (sphereCertificate_X143.1.circ.cornerFirst
        (sphereCertificate_X143.1.handleCorner firstHandle_X143 false)) =
      .vertical (sphereAdapted_X143.labelled.edgeLink.componentOfHandle firstHandle_X143) :=
  sphereAdapted_X143.labelled.first_label firstHandle_X143 false

theorem firstHorizontalRegistration_X143 :
    sphereAdapted_X143.labelled.globalFaces.faceOfDefining
      (sphereCertificate_X143.1.circ.cornerSecond
        (sphereCertificate_X143.1.handleCorner firstHandle_X143 false)) =
      .horizontal (spherePrepared_X143.rows.junctions.horizontal
        (sphereAdapted_X143.labelled.edgeLink.endOfHandle firstHandle_X143 false)) :=
  sphereAdapted_X143.labelled.second_label firstHandle_X143 false

theorem firstRimFullTarget_X143 :
    (sphereCertificate_X143.1.rimChart firstHandle_X143 false).target =
      Subtype.val '' (sphereCertificate_X143.1.circ.proj ⁻¹'
        (sphereCertificate_X143.1.circ.cornerChart
          (sphereCertificate_X143.1.handleCorner firstHandle_X143 false)).target) :=
  sphereAdapted_X143.labelled.target_full firstHandle_X143 false

end GC.GraphManifold.Assembly.FC39P0.General_X143.Consumer
