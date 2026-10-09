import DifferentialGeometry.Topology.Surface.Recognition.DiskFaceRecognition

/-!
# Concrete consumers of the FC40b recognitions (lane SF-C)

* The two-sphere is not a single circle-bundle face without disks (FC40b sphere side on `S²` itself).
* The torus `S¹ × S¹`, taken as one bundle component with no disk, is consistent with FC40b's torus
  side (the decision returns `d = 0`).
-/

set_option autoImplicit false

open Set Function

namespace DifferentialGeometry.Topology.Surface

open DifferentialGeometry.Topology

/-- **Consumer (sphere side).** `S²` admits no decomposition as one circle-bundle face over a
circle without disk faces: there is no continuous open map from `S²` (as the face `univ`) to the
circle. -/
theorem sphereTwo_not_single_bundle_face :
    ¬ ∃ p : ↥(univ : Set SphereTwo) → Circle, Continuous p ∧ IsOpenMap p := by
  rintro ⟨p, hp, hpo⟩
  have h := disk_face_count_sphereTwo (Homeomorph.refl SphereTwo) (ι := Fin 0) (κ := Unit)
    (fun i => i.elim0) (fun _ => univ) (fun i => i.elim0) (fun _ => isClosed_univ)
    (fun _ => ⟨sphereTwoNorth, trivial⟩) (by simp [iUnion_const]) (fun i => i.elim0)
    (fun i j hij => (hij (Subsingleton.elim i j)).elim) (fun i => i.elim0) (fun i => i.elim0)
    (fun _ => Or.inl (by simp)) (fun _ _ => ⟨p, hp, hpo⟩)
  simp at h

/-- **Consumer (torus side).** The torus as one circle-bundle component without disks: FC40b's torus
decision returns no disk. -/
theorem circle_prod_circle_disk_face_count :
    Fintype.card Unit = 1 ∧ Fintype.card (Fin 0) = 0 :=
  disk_face_count_torus (Homeomorph.refl (Circle × Circle)) (ι := Fin 0) (κ := Unit)
    (fun i => i.elim0) (fun _ => univ) (fun i => i.elim0) (fun _ => isClosed_univ)
    (fun _ => ⟨(1, 1), trivial⟩) (by simp [iUnion_const]) (fun i => i.elim0)
    (fun i j hij => (hij (Subsingleton.elim i j)).elim) (fun i => i.elim0) (fun i => i.elim0)
    (fun _ => Or.inl (by simp)) (fun i => i.elim0) (fun _ h => by simp at h)

end DifferentialGeometry.Topology.Surface
