import DifferentialGeometry.Topology.Homotopy.CubeSphereProjection
import DifferentialGeometry.Topology.Homotopy.OpenCollapseLocalHomeomorph

noncomputable section

open Set

universe u

namespace DifferentialGeometry.Topology

def cubeSphereProjectionOpenPartialHomeomorph (n : ℕ) :
    OpenPartialHomeomorph (Fin (n + 1) → unitInterval)
      (Metric.sphere (0 : EuclideanSpace ℝ (Fin (n + 2))) 1) :=
  (openCollapseOpenPartialHomeomorph (cubeInterior (Fin (n + 1))) (isOpen_cubeInterior _)).transHomeomorph
    (cubeInteriorSphereHomeomorph n)

theorem cubeSphereProjectionOpenPartialHomeomorph_apply (n : ℕ) (x : Fin (n + 1) → unitInterval) :
    cubeSphereProjectionOpenPartialHomeomorph n x = cubeSphereProjection n x := rfl

theorem cubeSphereProjectionOpenPartialHomeomorph_source (n : ℕ) :
    (cubeSphereProjectionOpenPartialHomeomorph n).source = cubeInterior (Fin (n + 1)) := rfl

theorem cubeSphereProjection_eq_of_mem (n : ℕ) {x y : Fin (n + 1) → unitInterval}
    (hx : x ∈ cubeInterior (Fin (n + 1)))
    (h : cubeSphereProjection n y = cubeSphereProjection n x) : y = x :=
  openCollapse_eq_of_mem hx ((cubeInteriorSphereHomeomorph n).injective h)

theorem cubeSphereProjectionOpenPartialHomeomorph_target (n : ℕ) :
    (cubeSphereProjectionOpenPartialHomeomorph n).target = {cubeSphereBasepoint n}ᶜ := by
  change (cubeInteriorSphereHomeomorph n).symm ⁻¹'
    (openCollapseOpenPartialHomeomorph (cubeInterior (Fin (n + 1))) (isOpen_cubeInterior _)).target = _
  rw [openCollapseOpenPartialHomeomorph_target]
  ext z
  change (cubeInteriorSphereHomeomorph n).symm z ≠ OnePoint.infty ↔ z ≠ cubeSphereBasepoint n
  exact not_congr (Homeomorph.symm_apply_eq (cubeInteriorSphereHomeomorph n))

def liftedCubeSphereProjectionOpenPartialHomeomorph (n : ℕ) :
    OpenPartialHomeomorph (ULift.{u} (Fin (n + 1) → unitInterval)) (ULift.{u} (Metric.sphere (0 : EuclideanSpace ℝ (Fin (n + 2))) 1)) :=
  (Homeomorph.ulift.transOpenPartialHomeomorph
    (cubeSphereProjectionOpenPartialHomeomorph n)).transHomeomorph Homeomorph.ulift.symm

theorem liftedCubeSphereProjectionOpenPartialHomeomorph_apply (n : ℕ)
    (x : ULift.{u} (Fin (n + 1) → unitInterval)) :
    liftedCubeSphereProjectionOpenPartialHomeomorph n x = ULift.up (cubeSphereProjection n x.down) := rfl

theorem liftedCubeSphereProjectionOpenPartialHomeomorph_source (n : ℕ) :
    (liftedCubeSphereProjectionOpenPartialHomeomorph.{u} n).source =
      {x | x.down ∈ cubeInterior (Fin (n + 1))} := rfl

theorem liftedCubeSphereProjectionOpenPartialHomeomorph_target (n : ℕ) :
    (liftedCubeSphereProjectionOpenPartialHomeomorph.{u} n).target = {ULift.up (cubeSphereBasepoint n)}ᶜ := by
  change (Homeomorph.ulift : ULift.{u} (Metric.sphere (0 : EuclideanSpace ℝ (Fin (n + 2))) 1) ≃ₜ _) ⁻¹'
    (cubeSphereProjectionOpenPartialHomeomorph n).target = _
  rw [cubeSphereProjectionOpenPartialHomeomorph_target]
  ext z
  change z.down ≠ cubeSphereBasepoint n ↔ z ≠ ULift.up (cubeSphereBasepoint n)
  exact not_congr ⟨fun h => ULift.ext _ _ h, congrArg ULift.down⟩

def liftedCubeSphereProjection (n : ℕ) :
    C(ULift.{u} (Fin (n + 1) → unitInterval),
      ULift.{u} (Metric.sphere (0 : EuclideanSpace ℝ (Fin (n + 2))) 1)) :=
  ⟨fun y => ULift.up (cubeSphereProjection n y.down),
    continuous_uliftUp.comp ((cubeSphereProjection n).continuous.comp continuous_uliftDown)⟩

theorem liftedCubeSphereProjection_eq_of_mem (n : ℕ)
    {x y : ULift.{u} (Fin (n + 1) → unitInterval)}
    (hx : x.down ∈ cubeInterior (Fin (n + 1)))
    (h : liftedCubeSphereProjection n y = liftedCubeSphereProjection n x) : y = x := by
  apply ULift.ext
  exact cubeSphereProjection_eq_of_mem n hx (congrArg ULift.down h)

theorem liftedCubeSphereProjection_mapsTo (n : ℕ)
    (x : ULift.{u} (Fin (n + 1) → unitInterval))
    (hx : x.down ∈ cubeInterior (Fin (n + 1))) :
    MapsTo (liftedCubeSphereProjection n) ({x}ᶜ : Set _)
      ({liftedCubeSphereProjection n x}ᶜ : Set _) :=
  fun _ hy h => hy (liftedCubeSphereProjection_eq_of_mem n hx h)

end DifferentialGeometry.Topology
