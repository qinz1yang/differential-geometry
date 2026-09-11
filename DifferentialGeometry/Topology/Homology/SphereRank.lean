import DifferentialGeometry.Topology.Homology.OneDimensionalSphere
import DifferentialGeometry.Topology.Homology.SphereHomologyOne
import DifferentialGeometry.Topology.Homology.TwoPointReducedZero



noncomputable section

open Set Metric Module

universe u

namespace DifferentialGeometry.Topology

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]


def unitSpherePointOfFinrankPos (h : 0 < finrank ℝ E) : sphere (0 : E) 1 := by
  letI := Module.nontrivial_of_finrank_pos h
  exact ⟨(NormedSpace.sphere_nonempty (E := E) (x := 0)).mpr (by norm_num) |>.choose,
    (NormedSpace.sphere_nonempty (E := E) (x := 0)).mpr (by norm_num) |>.choose_spec⟩

omit [FiniteDimensional ℝ E] in
theorem unitSpherePoleHyperplane_finrank (n : ℕ) (hd : finrank ℝ E = n + 1)
    (v : sphere (0 : E) 1) : finrank ℝ (ℝ ∙ (v : E))ᗮ = n := by
  let : Fact (finrank ℝ E = n + 1) := ⟨hd⟩
  apply Submodule.finrank_orthogonal_span_singleton
  intro h
  have hn := norm_eq_of_mem_sphere v
  rw [h, norm_zero] at hn
  norm_num at hn


theorem unitSphere_pathConnected_of_finrank (hd : 1 < finrank ℝ E) :
    PathConnectedSpace (sphere (0 : E) 1) := by
  apply unitSphere_pathConnected_of_rank
  rw [← finrank_eq_rank ℝ E]
  exact_mod_cast hd



def integralZeroSphereReducedEquiv (hd : finrank ℝ E = 1) :
    integralReducedHomologyZero (sphere (0 : E) 1) ≃ₗ[ℤ] ℤ := by
  let v := unitSpherePointOfFinrankPos (E := E) (by omega)
  letI := oneDimUnitSphere_finite hd v
  exact integralTwoPointReducedZeroEquiv (oneDimUnitSphereEquivBool hd v)

end DifferentialGeometry.Topology
