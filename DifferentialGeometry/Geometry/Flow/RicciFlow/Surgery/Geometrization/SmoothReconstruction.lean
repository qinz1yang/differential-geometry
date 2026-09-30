import DifferentialGeometry.Topology.ThreeManifold.Geometrization.OrientationTransport
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Geometrization.OrientedReconstruction
import DifferentialGeometry.Topology.Manifold.DisjointUnionComponent
import DifferentialGeometry.Topology.ThreeManifold.CappedPoincareStandard

set_option autoImplicit false
noncomputable section
open DifferentialGeometry DifferentialGeometry.Topology
open scoped Manifold ContDiff
namespace GC.Endpoint
universe u

theorem componentsGeometrize_of_diffeomorph
    {M N : ClosedOrientedManifold.{u} 3}
    (f : M.Carrier ≃ₘ⟮𝓡 3, 𝓡 3⟯ N.Carrier)
    (h : ComponentsGeometrize N) : ComponentsGeometrize M := by
  intro C
  exact geometrizes_of_diffeomorph
    (M := N.component (f.continuous.connectedComponentsMap C)) (N := M.component C)
    (ClosedOrientedManifold.diffeomorphComponent f C).symm (h _)

theorem componentsGeometrize_union {ι : Type u} [Fintype ι]
    (M : ι → ClosedOrientedManifold.{u} 3)
    (h : ∀ i, ComponentsGeometrize (M i)) : ComponentsGeometrize (closedOrientedUnion M) := by
  intro C
  obtain ⟨⟨i, x⟩, rfl⟩ := ConnectedComponents.surjective_coe C
  exact geometrizes_of_orientedDiffeomorph (closedOrientedUnionComponent M i x)
    (h i (ConnectedComponents.mk x))

theorem componentsGeometrize_of_cutCapSumData
    {M Q : ClosedOrientedManifold.{u} 3} {E : SphericalCutCapTransition M Q}
    (R : GC.Surgery.CutCapSumData E)
    (retained : ComponentsGeometrize Q) (discarded : ComponentsGeometrize E.discarded)
    (cycles : ∀ w, 0 < R.sphereProducts w →
      Geometrizes (sphereTwoTimesCircleLift.ulift.{0, u})) : ComponentsGeometrize M := by
  let := R.finite_group
  let := Fintype.ofFinite R.Group
  let F := fun w => finiteConnectedSum ((R.factors w).map E.capped.component ++
    List.replicate (R.sphereProducts w) (sphereTwoTimesCircleLift.ulift.{0, u}))
  have capped : ComponentsGeometrize E.capped := by
    intro K
    rcases GC.Surgery.cap_component_retained_or_discarded E K with
      ⟨q, _, ⟨f⟩⟩ | ⟨d, _, ⟨f⟩⟩
    · exact geometrizes_of_orientedDiffeomorph f.symm (retained _)
    · exact geometrizes_of_orientedDiffeomorph f.symm (discarded _)
  have hF : ∀ w, Geometrizes (F w) := by
    intro w
    apply geometrizes_finiteConnectedSum
    intro P hP
    rcases List.mem_append.mp hP with hP | hP
    · obtain ⟨K, _, rfl⟩ := List.mem_map.mp hP
      exact capped K
    · obtain ⟨hn, rfl⟩ := List.mem_replicate.mp hP
      exact cycles w (Nat.pos_of_ne_zero hn)
  exact componentsGeometrize_of_diffeomorph
    (N := closedOrientedUnion (fun w => (F w).toClosedOrientedManifold)) R.reconstruct
    (componentsGeometrize_union _ (fun w => (componentsGeometrize_iff (F w)).mpr (hF w)))

theorem componentsGeometrize_of_cutCap
    {M Q : ClosedOrientedManifold.{u} 3} (E : SphericalCutCapTransition M Q)
    (retained : ComponentsGeometrize Q) (discarded : ComponentsGeometrize E.discarded)
    (cycle : Geometrizes (sphereTwoTimesCircleLift.ulift.{0, u})) :
    ComponentsGeometrize M := by
  obtain ⟨R⟩ := GC.Surgery.actual_cutCapSumData E
  exact componentsGeometrize_of_cutCapSumData R retained discarded (fun _ _ => cycle)

def StandardFactorEndpoints : Prop :=
  ∀ P : ConnectedClosedOrientedManifold.{u} 3, isStandardFactor P → Geometrizes P

theorem geometrizes_of_poincareStandard (standard : StandardFactorEndpoints.{u})
    (M : ConnectedClosedOrientedManifold.{u} 3) (h : isPoincareStandard M.Carrier) :
    Geometrizes M := by
  obtain ⟨R⟩ := h
  exact geometrizes_of_diffeomorph R.diffeomorph.symm
    (geometrizes_finiteConnectedSum R.factors (fun P hP => standard P (R.standard P hP)))

theorem cycle_geometrizes_of_standard (standard : StandardFactorEndpoints.{u}) :
    Geometrizes (sphereTwoTimesCircleLift.ulift.{0, u}) := by
  apply standard
  apply isStandardFactor_of_isSphereTwoTimesCircleFactor
  obtain ⟨f, hf⟩ := isSphereTwoTimesCircleFactor_sphereTwoTimesCircleLift
  let U := (ClosedOrientedManifold.uliftOrientedDiffeomorph.{0, u}
    sphereTwoTimesCircleLift.toClosedOrientedManifold).symm
  exact ⟨U.val.trans f, Diffeomorph.preservesOrientation_trans U.property hf⟩

end GC.Endpoint
