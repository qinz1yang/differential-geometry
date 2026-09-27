import DifferentialGeometry.Topology.Homotopy.SphereFamilyDescent
import DifferentialGeometry.Topology.Homotopy.BasepointGroup



noncomputable section

open Set Function ContinuousMap
open scoped Topology

namespace DifferentialGeometry.Topology

variable {X : Type*} [TopologicalSpace X] {x y : X}


def sphereHomotopyBasepointPath (n : ℕ)
    {f : basedMappingSpace (cubeSphereBasepoint n) x}
    {g : basedMappingSpace (cubeSphereBasepoint n) y} (H : f.val.Homotopy g.val) : Path x y where
  toFun t := H (t, cubeSphereBasepoint n)
  continuous_toFun := H.continuous.comp (continuous_id.prodMk continuous_const)
  source' := (H.apply_zero _).trans f.property
  target' := (H.apply_one _).trans g.property



theorem genLoopTransport_of_sphereHomotopy (n : ℕ)
    (Γ : GenLoop (Fin (n + 1)) X x) (Δ : GenLoop (Fin (n + 1)) X y)
    (H : (genLoopSphereHomeomorph n x Γ).val.Homotopy
      (genLoopSphereHomeomorph n y Δ).val) :
    GenLoop.Homotopic Δ (genLoopTransport n (sphereHomotopyBasepointPath n H) Γ) := by
  let F : C(unitInterval × (Fin (n + 1) → unitInterval), X) :=
    ⟨fun z => H (z.1, cubeSphereProjection n z.2),
      H.continuous.comp (continuous_fst.prodMk
        ((cubeSphereProjection n).continuous.comp continuous_snd))⟩
  apply genLoopTransport_extension_unique n (sphereHomotopyBasepointPath n H) Γ Δ F
  · intro v
    exact (H.apply_zero _).trans (genLoopSphereHomeomorph_projection n x Γ v)
  · intro v
    exact (H.apply_one _).trans (genLoopSphereHomeomorph_projection n y Δ v)
  · intro t v hv
    change H (t, cubeSphereProjection n v) = H (t, cubeSphereBasepoint n)
    rw [cubeSphereProjection_boundary n v hv]



def genLoopSphereTransportHomotopy (n : ℕ) (p : Path x y)
    (Γ : GenLoop (Fin (n + 1)) X x) :
    (genLoopSphereHomeomorph n x Γ).val.Homotopy
      (genLoopSphereHomeomorph n y (genLoopTransport n p Γ)).val := by
  let F := (cubePathHomotopy n p Γ).toContinuousMap
  have hb : ∀ t v, v ∈ Cube.boundary (Fin (n + 1)) → F (t, v) = p t :=
    cubePathHomotopy_boundary n p Γ
  refine {
    toFun := sphereFamilyDescendValue n F p.toContinuousMap
    continuous_toFun := continuous_sphereFamilyDescendValue n F p.toContinuousMap hb
    map_zero_left := ?_
    map_one_left := ?_ }
  · intro z
    obtain ⟨v, rfl⟩ := cubeSphereProjection_surjective n z
    rw [sphereFamilyDescendValue_projection n F p.toContinuousMap hb]
    exact (cubePathHomotopy n p Γ).apply_zero v |>.trans
      (genLoopSphereHomeomorph_projection n x Γ v).symm
  · intro z
    obtain ⟨v, rfl⟩ := cubeSphereProjection_surjective n z
    rw [sphereFamilyDescendValue_projection n F p.toContinuousMap hb]
    exact (genLoopSphereHomeomorph_projection n y (genLoopTransport n p Γ) v).symm



theorem genLoop_homotopic_of_sphere_free_homotopic [SimplyConnectedSpace X]
    (n : ℕ) (Γ Δ : GenLoop (Fin (n + 1)) X x)
    (h : (genLoopSphereHomeomorph n x Γ).val.Homotopic
      (genLoopSphereHomeomorph n x Δ).val) : GenLoop.Homotopic Γ Δ := by
  obtain ⟨H⟩ := h
  have ht := genLoopTransport_of_sphereHomotopy n Γ Δ H
  have hp := genLoopTransport_path_homotopic n
    (SimplyConnectedSpace.paths_homotopic (sphereHomotopyBasepointPath n H) (Path.refl x)) Γ
  exact (ht.trans (hp.trans (genLoopTransport_refl_homotopic n Γ))).symm

end DifferentialGeometry.Topology
