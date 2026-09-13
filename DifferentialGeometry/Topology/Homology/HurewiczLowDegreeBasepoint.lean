import DifferentialGeometry.Topology.Homology.HurewiczFrontier
import DifferentialGeometry.Topology.Homotopy.BasepointGroup

noncomputable section

universe u

namespace DifferentialGeometry.Topology

variable {X : Type u} [TopologicalSpace X]

theorem IsSphereHurewiczIsomorphism.of_transport (n : ℕ) {x y : X} (p : Path x y)
    {c : integralSingularHomology (n + 1) (liftedHomotopySphere.{u} n)}
    (h : IsSphereHurewiczIsomorphism n X x c) :
    IsSphereHurewiczIsomorphism n X y c := by
  have hfun : sphereHurewicz n y c =
      (sphereHurewicz n x c) ∘ (homotopyGroupBasepointEquiv n p).symm := by
    funext a
    rw [Function.comp_apply]
    calc sphereHurewicz n y c a
        = sphereHurewicz n y c
            ((homotopyGroupBasepointEquiv n p) ((homotopyGroupBasepointEquiv n p).symm a)) := by
          rw [Equiv.apply_symm_apply]
      _ = sphereHurewicz n x c ((homotopyGroupBasepointEquiv n p).symm a) :=
          sphereHurewicz_transport n p c ((homotopyGroupBasepointEquiv n p).symm a)
  refine ⟨?_, ?_⟩
  · rw [hfun]
    exact h.1.comp (homotopyGroupBasepointEquiv n p).symm.bijective
  · intro a b
    obtain ⟨a', rfl⟩ := (homotopyGroupBasepointEquiv n p).surjective a
    obtain ⟨b', rfl⟩ := (homotopyGroupBasepointEquiv n p).surjective b
    change sphereHurewicz n y c
        (homotopyGroupTransport n p a' * homotopyGroupTransport n p b') =
      sphereHurewicz n y c (homotopyGroupTransport n p a') +
        sphereHurewicz n y c (homotopyGroupTransport n p b')
    rw [← homotopyGroupTransport_mul n p a' b',
      sphereHurewicz_transport n p c (a' * b'), h.2 a' b',
      sphereHurewicz_transport n p c a', sphereHurewicz_transport n p c b']

theorem sphereHurewiczTwoCanonical_iff_isSphereHurewiczIsomorphism [SimplyConnectedSpace X]
    (x₀ : X) :
    SphereHurewiczTwoCanonical X ↔
      IsSphereHurewiczIsomorphism 1 X x₀ (integralLiftedSphereGenerator.{u} 1) :=
  ⟨fun h => h x₀, fun h x =>
    IsSphereHurewiczIsomorphism.of_transport 1 (PathConnectedSpace.somePath x₀ x) h⟩

theorem sphereHurewiczThreeCanonical_iff_isSphereHurewiczIsomorphism [SimplyConnectedSpace X]
    (x₀ : X) :
    SphereHurewiczThreeCanonical X ↔
      (Subsingleton (HomotopyGroup (Fin 2) X x₀) →
        IsSphereHurewiczIsomorphism 2 X x₀ (integralLiftedSphereGenerator.{u} 2)) := by
  refine ⟨fun h => h x₀, fun h x hπ₂ => ?_⟩
  let := hπ₂
  have hπ : Subsingleton (HomotopyGroup (Fin 2) X x₀) :=
    homotopyGroup_subsingleton_of_path 1 (PathConnectedSpace.somePath x x₀)
  exact IsSphereHurewiczIsomorphism.of_transport 2 (PathConnectedSpace.somePath x₀ x)
    (h hπ)

theorem hurewicz_two_isomorphism_of_isSphereHurewiczIsomorphism [SimplyConnectedSpace X]
    (x₀ : X)
    (h : IsSphereHurewiczIsomorphism 1 X x₀ (integralLiftedSphereGenerator.{u} 1))
    (x : X) (c : integralSingularHomology 2 (liftedHomotopySphere.{u} 1))
    (hc : IsSphereHomologyGenerator 1 c) :
    Function.Bijective (sphereHurewicz 1 x c) ∧
      ∀ a b : HomotopyGroup (Fin 2) X x,
        sphereHurewicz 1 x c (a * b) = sphereHurewicz 1 x c a + sphereHurewicz 1 x c b :=
  IsSphereHurewiczIsomorphism.of_isSphereHomologyGenerator 1 x hc
    (IsSphereHurewiczIsomorphism.of_transport 1 (PathConnectedSpace.somePath x₀ x) h)

theorem hurewicz_three_isomorphism_of_isSphereHurewiczIsomorphism [SimplyConnectedSpace X]
    (x₀ : X)
    (h : Subsingleton (HomotopyGroup (Fin 2) X x₀) →
      IsSphereHurewiczIsomorphism 2 X x₀ (integralLiftedSphereGenerator.{u} 2))
    (x : X) (hπ₂ : Subsingleton (HomotopyGroup (Fin 2) X x))
    (c : integralSingularHomology 3 (liftedHomotopySphere.{u} 2))
    (hc : IsSphereHomologyGenerator 2 c) :
    Function.Bijective (sphereHurewicz 2 x c) ∧
      ∀ a b : HomotopyGroup (Fin 3) X x,
        sphereHurewicz 2 x c (a * b) = sphereHurewicz 2 x c a + sphereHurewicz 2 x c b := by
  let := hπ₂
  have hπ : Subsingleton (HomotopyGroup (Fin 2) X x₀) :=
    homotopyGroup_subsingleton_of_path 1 (PathConnectedSpace.somePath x x₀)
  exact IsSphereHurewiczIsomorphism.of_isSphereHomologyGenerator 2 x hc
    (IsSphereHurewiczIsomorphism.of_transport 2 (PathConnectedSpace.somePath x₀ x) (h hπ))

theorem isSphereHurewiczIsomorphism_one_punit (x : PUnit.{u + 1}) :
    IsSphereHurewiczIsomorphism 1 PUnit.{u + 1} x (integralLiftedSphereGenerator.{u} 1) :=
  (sphereHurewiczTwoCanonical_iff_isSphereHurewiczIsomorphism (X := PUnit.{u + 1}) x).mp
    sphereHurewiczTwoCanonical_punit

theorem isSphereHurewiczIsomorphism_two_punit (x : PUnit.{u + 1})
    (hπ₂ : Subsingleton (HomotopyGroup (Fin 2) PUnit.{u + 1} x)) :
    IsSphereHurewiczIsomorphism 2 PUnit.{u + 1} x (integralLiftedSphereGenerator.{u} 2) :=
  (sphereHurewiczThreeCanonical_iff_isSphereHurewiczIsomorphism (X := PUnit.{u + 1}) x).mp
    sphereHurewiczThreeCanonical_punit hπ₂

end DifferentialGeometry.Topology
