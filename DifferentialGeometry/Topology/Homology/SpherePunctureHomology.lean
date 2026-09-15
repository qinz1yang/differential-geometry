import DifferentialGeometry.Topology.Homology.SpherePuncture
import DifferentialGeometry.Topology.Homology.ContractiblePair
import DifferentialGeometry.Topology.Homology.LiftedSphere

noncomputable section

namespace DifferentialGeometry.Topology

universe u

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

theorem integralAbsoluteToRelative_sphere_puncture_bijective
    (n : ℕ) (p : Metric.sphere (0 : E) 1) :
    Function.Bijective (integralAbsoluteToRelative (n + 2)
      ({p}ᶜ : Set (Metric.sphere (0 : E) 1))) := by
  let := spherePuncture_contractible p
  exact (integralAbsoluteToRelativeIsoOfContractible n ({p}ᶜ)).toLinearEquiv.bijective

theorem liftedSpherePuncture_contractible (n : ℕ) (p : liftedHomotopySphere.{u} n) :
    ContractibleSpace ({p}ᶜ : Set (liftedHomotopySphere.{u} n)) := by
  let e : ({p}ᶜ : Set (liftedHomotopySphere.{u} n)) ≃ₜ
      ({liftedSphereHomeomorph n p}ᶜ : Set (Metric.sphere (0 : liftedSphereSpace.{u} n) 1)) :=
    (liftedSphereHomeomorph n).subtype (fun x => by
      simp only [Set.mem_compl_iff, Set.mem_singleton_iff]
      exact not_congr (liftedSphereHomeomorph n).injective.eq_iff.symm)
  let := spherePuncture_contractible (liftedSphereHomeomorph n p)
  exact e.contractibleSpace

theorem integralAbsoluteToRelative_liftedSphere_puncture_bijective
    (n k : ℕ) (p : liftedHomotopySphere.{u} n) :
    Function.Bijective (integralAbsoluteToRelative (k + 2)
      ({p}ᶜ : Set (liftedHomotopySphere.{u} n))) := by
  let := liftedSpherePuncture_contractible n p
  exact (integralAbsoluteToRelativeIsoOfContractible k ({p}ᶜ)).toLinearEquiv.bijective

end DifferentialGeometry.Topology
