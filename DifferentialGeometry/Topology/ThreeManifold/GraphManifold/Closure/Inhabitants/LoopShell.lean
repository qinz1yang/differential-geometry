import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Closure.Inhabitants.LoopComplement

/-!
The actual annular shell between the same rounded loop solid torus and its deep solid core.
Every base point retains its complete first-Clifford circle orbit.
-/

set_option autoImplicit false

noncomputable section

open Set Function Metric DifferentialGeometry DifferentialGeometry.Topology GC.Endpoint
open GC.GraphManifold
open scoped Manifold ContDiff Topology

namespace GC.GraphManifold.Assembly

def loopShellBase : Set (EuclideanSpace ℝ (Fin 2)) :=
  {z | 1 / 8 ≤ ‖z‖ ^ 2 ∧ ‖z‖ ^ 2 ≤ 1 / 2}

def loopRoundedShell : Set SphereCarrier.{0} :=
  {p | 0 ≤ cliffordHeight p ∧ cliffordHeight p ≤ 3 / 4}

theorem loopShellBase_source {z : EuclideanSpace ℝ (Fin 2)} (hz : z ∈ loopShellBase) :
    ‖z‖ < 1 := by
  change 1 / 8 ≤ ‖z‖ ^ 2 ∧ ‖z‖ ^ 2 ≤ 1 / 2 at hz
  nlinarith [norm_nonneg z]

theorem loopRoundedShell_orbits :
    loopCircleCoordinates '' (loopShellBase ×ˢ Set.univ) = loopRoundedShell := by
  apply Set.Subset.antisymm
  · rintro p ⟨⟨z, θ⟩, hp, rfl⟩
    have hs := loopCircleCoordinates_second (p := (z, θ)) (loopShellBase_source hp.1)
    have hh := norm_sphereSecond_sq_eq (loopCircleCoordinates (z, θ))
    rw [hs, modelPlaneComplex.norm_map] at hh
    have hz : 1 / 8 ≤ ‖z‖ ^ 2 ∧ ‖z‖ ^ 2 ≤ 1 / 2 := hp.1
    change 0 ≤ cliffordHeight _ ∧ cliffordHeight _ ≤ 3 / 4
    constructor <;> linarith [hz.1, hz.2]
  · intro p hp
    change 0 ≤ cliffordHeight p ∧ cliffordHeight p ≤ 3 / 4 at hp
    have hne : sphereFirst p ≠ 0 := by
      intro he
      have hh := norm_sphereFirst_sq_eq p
      rw [he, norm_zero, zero_pow (by decide)] at hh
      linarith [hp.1]
    refine ⟨loopCircleCoordinates.symm p, ?_, loopCircleCoordinates.right_inv hne⟩
    refine ⟨?_, Set.mem_univ _⟩
    rw [loopCircleCoordinates_inverse]
    change 1 / 8 ≤ ‖modelPlaneComplex.symm (sphereSecond p)‖ ^ 2 ∧
      ‖modelPlaneComplex.symm (sphereSecond p)‖ ^ 2 ≤ 1 / 2
    rw [modelPlaneComplex.symm.norm_map, norm_sphereSecond_sq_eq]
    constructor <;> linarith [hp.1, hp.2]

theorem loopRoundedShell_cover :
    solidTorusSet.{0} ∪ loopRoundedShell ∪ Set.range loopComplementVertex.map = Set.univ := by
  rw [loopComplementVertex_range]
  apply Set.eq_univ_of_forall
  intro p
  by_cases hl : cliffordHeight p ≤ 0
  · exact Or.inl (Or.inl hl)
  · by_cases hu : cliffordHeight p ≤ 3 / 4
    · exact Or.inl (Or.inr ⟨(not_le.mp hl).le, hu⟩)
    · exact Or.inr (not_le.mp hu).le

end GC.GraphManifold.Assembly
