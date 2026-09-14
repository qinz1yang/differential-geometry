import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.LowDegreeHurewiczCubeBridge
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.HomotopyGroupsAssembly
import DifferentialGeometry.Topology.Homology.HurewiczLowDegreeCriterion
import DifferentialGeometry.Topology.Homology.HurewiczLowDegreeTransport
import DifferentialGeometry.Topology.Homology.HurewiczThreeWitness
import DifferentialGeometry.Topology.Homology.SecondHomologyVanishingClosedThreeManifold

noncomputable section

open Set
open scoped ContDiff Manifold

universe u

namespace DifferentialGeometry.Topology

variable {X : Type u} [TopologicalSpace X]

theorem hurewicz_three_isomorphism_of_cubeSphereFundamentalClass_of_sphereCriterion
    [SimplyConnectedSpace X] (hgen : IsSphereHomologyGenerator.{u} 2 cubeSphereFundamentalClass)
    (hgenThree : HurewiczThreeSphereGeneration X)
    (hnullThree : HurewiczThreeSphereNullhomotopic X)
    (x : X) (hπ₂ : Subsingleton (HomotopyGroup (Fin 2) X x))
    (c : integralSingularHomology 3 (liftedHomotopySphere.{u} 2))
    (hc : IsSphereHomologyGenerator 2 c) :
    Function.Bijective (sphereHurewicz 2 x c) ∧
      ∀ a b : HomotopyGroup (Fin 3) X x,
        sphereHurewicz 2 x c (a * b) = sphereHurewicz 2 x c a + sphereHurewicz 2 x c b :=
  sphereHurewicz_three_isomorphism_of_canonical_generator
    ((sphereHurewiczThreeCanonical_iff_sphereCriterion_of_cubeSphereFundamentalClass
      hgen x hπ₂).mpr ⟨hgenThree, hnullThree⟩) x hπ₂ c hc

theorem
    hurewicz_three_isomorphism_liftedHomotopySphere_of_cubeSphereFundamentalClass_of_nullhomotopic
    (hgen : IsSphereHomologyGenerator.{u} 2 cubeSphereFundamentalClass)
    (hnull : HurewiczThreeSphereNullhomotopic (liftedHomotopySphere.{u} 2))
    (x : liftedHomotopySphere.{u} 2)
    (hπ₂ : Subsingleton (HomotopyGroup (Fin 2) (liftedHomotopySphere.{u} 2) x))
    (c : integralSingularHomology 3 (liftedHomotopySphere.{u} 2))
    (hc : IsSphereHomologyGenerator 2 c) :
    Function.Bijective (sphereHurewicz 2 x c) ∧
      ∀ a b : HomotopyGroup (Fin 3) (liftedHomotopySphere.{u} 2) x,
        sphereHurewicz 2 x c (a * b) = sphereHurewicz 2 x c a + sphereHurewicz 2 x c b :=
  hurewicz_three_isomorphism_of_cubeSphereFundamentalClass_of_sphereCriterion hgen
    (hurewiczThreeSphereGeneration_liftedHomotopySphere_of_cubeSphereFundamentalClass hgen)
    hnull x hπ₂ c hc

theorem
    homotopyTwo_subsingleton_of_sphereHurewiczTwoCanonical_of_noncompactPoincareDuality
    {M : Type u} [TopologicalSpace M] [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
    [IsManifold (𝓡 3) ∞ M] [T2Space M] [CompactSpace M] [SimplyConnectedSpace M]
    (hTwo : SphereHurewiczTwoCanonical M) (x q : M)
    (hpd : noncompactPoincareDualityTwoOne ({x}ᶜ : Set M)) :
    Subsingleton (HomotopyGroup (Fin 2) M q) :=
  homotopyTwo_subsingleton_of_sphereHurewiczTwoCanonical hTwo
    (subsingleton_integralSingularHomology_two_of_noncompactPoincareDuality_punctured x hpd) q

theorem
    homotopyTwo_subsingleton_of_hurewiczTwoSphereNullhomotopic_of_noncompactPoincareDuality
    {M : Type u} [TopologicalSpace M] [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
    [IsManifold (𝓡 3) ∞ M] [T2Space M] [CompactSpace M] [SimplyConnectedSpace M]
    (hnull : HurewiczTwoSphereNullhomotopic M) (x q : M)
    (hpd : noncompactPoincareDualityTwoOne ({x}ᶜ : Set M)) :
    Subsingleton (HomotopyGroup (Fin 2) M q) :=
  @homotopyTwo_subsingleton_of_homologyTwo_of_sphereNullhomotopic M _ _ hnull
    (subsingleton_integralSingularHomology_two_of_noncompactPoincareDuality_punctured x hpd) q

open DifferentialGeometry.PDE.RicciFlow.Surgery.Topology in
theorem
    sphereHurewiczTwoCanonical_iff_forall_subsingleton_homotopyGroup_of_noncompactPoincareDuality
    {M : Type u} [TopologicalSpace M] [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
    [IsManifold (𝓡 3) ∞ M] [T2Space M] [CompactSpace M] [SimplyConnectedSpace M]
    (x : M) (hpd : noncompactPoincareDualityTwoOne ({x}ᶜ : Set M)) :
    SphereHurewiczTwoCanonical M ↔ ∀ q : M, Subsingleton (HomotopyGroup (Fin 2) M q) :=
  sphereHurewiczTwoCanonical_iff_forall_subsingleton_homotopyGroup
    (subsingleton_integralSingularHomology_two_of_noncompactPoincareDuality_punctured x hpd)

theorem hurewicz_two_and_three_isomorphism_of_lowDegreeAssembly
    {M : Type u} [TopologicalSpace M] [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
    [IsManifold (𝓡 3) ∞ M] [T2Space M] [CompactSpace M] [SimplyConnectedSpace M]
    (x : M) (hpd : noncompactPoincareDualityTwoOne ({x}ᶜ : Set M))
    (hTwo : SphereHurewiczTwoCanonical M)
    (hgen : IsSphereHomologyGenerator.{u} 2 cubeSphereFundamentalClass)
    (hgenThree : HurewiczThreeSphereGeneration M)
    (hnullThree : HurewiczThreeSphereNullhomotopic M)
    (q : M) (c₂ : integralSingularHomology 2 (liftedHomotopySphere.{u} 1))
    (hc₂ : IsSphereHomologyGenerator 1 c₂)
    (c₃ : integralSingularHomology 3 (liftedHomotopySphere.{u} 2))
    (hc₃ : IsSphereHomologyGenerator 2 c₃) :
    (Function.Bijective (sphereHurewicz 1 q c₂) ∧
      ∀ a b : HomotopyGroup (Fin 2) M q,
        sphereHurewicz 1 q c₂ (a * b) = sphereHurewicz 1 q c₂ a + sphereHurewicz 1 q c₂ b) ∧
    (Function.Bijective (sphereHurewicz 2 q c₃) ∧
      ∀ a b : HomotopyGroup (Fin 3) M q,
        sphereHurewicz 2 q c₃ (a * b) = sphereHurewicz 2 q c₃ a + sphereHurewicz 2 q c₃ b) :=
  ⟨sphereHurewicz_two_isomorphism_of_canonical_generator hTwo q c₂ hc₂,
    hurewicz_three_isomorphism_of_cubeSphereFundamentalClass_of_sphereCriterion hgen hgenThree
      hnullThree q
      (homotopyTwo_subsingleton_of_sphereHurewiczTwoCanonical_of_noncompactPoincareDuality
        hTwo x q hpd) c₃ hc₃⟩

theorem homotopyTwo_subsingleton_sphereThree_of_hurewiczTwoSphereNullhomotopic
    (hnull : HurewiczTwoSphereNullhomotopic SphereThree) (q : SphereThree) :
    Subsingleton (HomotopyGroup (Fin 2) SphereThree q) :=
  homotopyTwo_subsingleton_of_hurewiczTwoSphereNullhomotopic_of_noncompactPoincareDuality
    hnull (Classical.choice (inferInstance : Nonempty SphereThree)) q
    (noncompactPoincareDualityTwoOne_sphereThree_compl_singleton _)

end DifferentialGeometry.Topology
