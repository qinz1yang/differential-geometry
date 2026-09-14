import DifferentialGeometry.Topology.FundamentalGroup.Sphere
import DifferentialGeometry.Topology.Homology.CubeSphereDegreeUnit
import DifferentialGeometry.Topology.Homology.HurewiczBijectionFrontier
import DifferentialGeometry.Topology.Homology.HurewiczLowDegreeTransport
import DifferentialGeometry.Topology.Homology.HurewiczSphereCriterion
import DifferentialGeometry.Topology.Homology.HurewiczThreeReduction
import DifferentialGeometry.Topology.Homology.SphereRank
import DifferentialGeometry.Topology.ThreeManifold.StandardSphere

noncomputable section

open ContinuousMap Metric

universe u

namespace DifferentialGeometry.Topology

instance liftedHomotopySphere_pathConnectedSpace (n : ℕ) :
    PathConnectedSpace (liftedHomotopySphere.{u} n) := by
  have hrank : 1 < Module.finrank ℝ (liftedSphereSpace.{u} n) := by
    rw [liftedSphereSpace_finrank]
    omega
  let : PathConnectedSpace (sphere (0 : liftedSphereSpace.{u} n) 1) :=
    unitSphere_pathConnected_of_finrank (E := liftedSphereSpace.{u} n) hrank
  exact (liftedSphereHomeomorph.{u} n).symm.surjective.pathConnectedSpace
    (liftedSphereHomeomorph.{u} n).symm.continuous

instance liftedHomotopySphere_simplyConnectedSpace :
    SimplyConnectedSpace (liftedHomotopySphere.{u} 2) := by
  change SimplyConnectedSpace (ULift.{u} (sphere (0 : EuclideanSpace ℝ (Fin 4)) 1))
  exact ContinuousMap.HomotopyEquiv.simplyConnectedSpace
    (Homeomorph.toHomotopyEquiv
      (Homeomorph.ulift (X := sphere (0 : EuclideanSpace ℝ (Fin 4)) 1)))

def euclideanSphereToLiftedHomotopySphere (n : ℕ) :
    C(sphere (0 : EuclideanSpace ℝ (Fin (n + 2))) 1, liftedHomotopySphere.{u} n) :=
  ⟨ULift.up, continuous_uliftUp⟩

theorem euclideanSphereToLiftedHomotopySphere_comp_down (n : ℕ) :
    (euclideanSphereToLiftedHomotopySphere.{u} n).comp (liftedHomotopySphereDown n) =
      ContinuousMap.id (liftedHomotopySphere.{u} n) := by
  ext z
  cases z with
  | up s => rfl

def liftedHomotopySphereIdentityLoop (n : ℕ) :
    GenLoop (Fin (n + 1)) (liftedHomotopySphere.{u} n) (ULift.up (cubeSphereBasepoint n)) :=
  (genLoopSphereHomeomorph n (ULift.up (cubeSphereBasepoint n))).symm
    ⟨euclideanSphereToLiftedHomotopySphere.{u} n, rfl⟩

def liftedHomotopySphereIdentityClass (n : ℕ) (x : liftedHomotopySphere.{u} n) :
    HomotopyGroup (Fin (n + 1)) (liftedHomotopySphere.{u} n) x :=
  homotopyGroupTransport n
    (PathConnectedSpace.somePath (ULift.up (cubeSphereBasepoint n)) x)
    (Quotient.mk _ (liftedHomotopySphereIdentityLoop n))

theorem sphereHurewicz_liftedHomotopySphereIdentityLoop (n : ℕ)
    (c : integralSingularHomology (n + 1) (liftedHomotopySphere.{u} n)) :
    sphereHurewicz n (ULift.up (cubeSphereBasepoint n)) c
      (Quotient.mk _ (liftedHomotopySphereIdentityLoop n)) = c := by
  unfold liftedHomotopySphereIdentityLoop
  rw [sphereHurewicz_mk, Homeomorph.apply_symm_apply,
    euclideanSphereToLiftedHomotopySphere_comp_down, integralSingularHomologyMap_id,
    LinearMap.id_apply]

theorem sphereHurewicz_liftedHomotopySphereIdentityClass (n : ℕ) (x : liftedHomotopySphere.{u} n)
    (c : integralSingularHomology (n + 1) (liftedHomotopySphere.{u} n)) :
    sphereHurewicz n x c (liftedHomotopySphereIdentityClass n x) = c := by
  have htrans := sphereHurewicz_transport n
    (PathConnectedSpace.somePath (ULift.up (cubeSphereBasepoint n)) x) c
    (Quotient.mk _ (liftedHomotopySphereIdentityLoop n))
  unfold liftedHomotopySphereIdentityClass
  exact htrans.trans (sphereHurewicz_liftedHomotopySphereIdentityLoop n c)

theorem exists_sphereHurewicz_eq_self (n : ℕ) (x : liftedHomotopySphere.{u} n)
    (c : integralSingularHomology (n + 1) (liftedHomotopySphere.{u} n)) :
    ∃ a : HomotopyGroup (Fin (n + 1)) (liftedHomotopySphere.{u} n) x,
      sphereHurewicz n x c a = c :=
  ⟨liftedHomotopySphereIdentityClass n x,
    sphereHurewicz_liftedHomotopySphereIdentityClass n x c⟩

theorem integralLiftedSphereGenerator_ne_zero (n : ℕ) :
    integralLiftedSphereGenerator.{u} n ≠ 0 := by
  intro hzero
  have hcoord := integralLiftedSphereGenerator_coordinate.{u} n
  rw [hzero, map_zero] at hcoord
  exact one_ne_zero hcoord.symm

theorem liftedHomotopySphereIdentityClass_ne_one (n : ℕ) (x : liftedHomotopySphere.{u} n) :
    liftedHomotopySphereIdentityClass n x ≠ 1 := by
  intro hone
  have himg := sphereHurewicz_liftedHomotopySphereIdentityClass n x
    (integralLiftedSphereGenerator.{u} n)
  rw [hone, sphereHurewicz_one] at himg
  exact integralLiftedSphereGenerator_ne_zero n himg.symm

theorem nontrivial_homotopyGroup_liftedHomotopySphere (n : ℕ)
    (x : liftedHomotopySphere.{u} n) :
    Nontrivial (HomotopyGroup (Fin (n + 1)) (liftedHomotopySphere.{u} n) x) :=
  ⟨liftedHomotopySphereIdentityClass n x, 1,
    liftedHomotopySphereIdentityClass_ne_one n x⟩

theorem not_surjective_sphereHurewicz_zero_liftedHomotopySphere
    (x : liftedHomotopySphere.{u} 2) :
    ¬ Function.Surjective (sphereHurewicz 2 x
      (0 : integralSingularHomology 3 (liftedHomotopySphere.{u} 2))) := by
  intro hsurj
  obtain ⟨a, ha⟩ := hsurj (integralLiftedSphereGenerator.{u} 2)
  rw [sphereHurewicz_zero 2 x a] at ha
  exact integralLiftedSphereGenerator_ne_zero 2 ha.symm

theorem exists_integralLiftedSphereGenerator_eq_zsmul_cubeSphereFundamentalClass
    (hgen : IsSphereHomologyGenerator.{u} 2 cubeSphereFundamentalClass) :
    ∃ k : ℤ, integralLiftedSphereGenerator.{u} 2 = k • cubeSphereFundamentalClass := by
  rcases IsSphereHomologyGenerator.eq_or_eq_neg 2 hgen
    (integralLiftedSphereGenerator_isGenerator 2) with h | h
  · exact ⟨1, by rw [h, one_smul]⟩
  · exact ⟨-1, by rw [h]; simp⟩

theorem sphereHurewicz_integralLiftedSphereGenerator_mul_of_cubeSphereFundamentalClass
    {X : Type u} [TopologicalSpace X]
    (hgen : IsSphereHomologyGenerator.{u} 2 cubeSphereFundamentalClass)
    (x : X) (a b : HomotopyGroup (Fin 3) X x) :
    sphereHurewicz 2 x (integralLiftedSphereGenerator.{u} 2) (a * b) =
      sphereHurewicz 2 x (integralLiftedSphereGenerator.{u} 2) a +
        sphereHurewicz 2 x (integralLiftedSphereGenerator.{u} 2) b := by
  obtain ⟨k, hk⟩ :=
    exists_integralLiftedSphereGenerator_eq_zsmul_cubeSphereFundamentalClass hgen
  exact sphereHurewicz_mul_of_eq_zsmul_cubeSphereFundamentalClass
    (integralLiftedSphereGenerator.{u} 2) k hk x a b

theorem hurewiczThreeSphereGeneration_liftedHomotopySphere_of_cubeSphereFundamentalClass
    (hgen : IsSphereHomologyGenerator.{u} 2 cubeSphereFundamentalClass) :
    HurewiczThreeSphereGeneration (liftedHomotopySphere.{u} 2) := by
  let x₀ : liftedHomotopySphere.{u} 2 := ULift.up (cubeSphereBasepoint 2)
  refine hurewiczThreeSphereGeneration_of_exists (X := liftedHomotopySphere.{u} 2) x₀
    (sphereHurewicz_integralLiftedSphereGenerator_mul_of_cubeSphereFundamentalClass hgen x₀)
    (liftedHomotopySphereIdentityClass 2 x₀) (integralLiftedSphereGenerator.{u} 2)
    (sphereHurewicz_liftedHomotopySphereIdentityClass 2 x₀
      (integralLiftedSphereGenerator.{u} 2)) ?_
  exact (isSphereHomologyGenerator_iff_forall_exists_zsmul 2
    (integralLiftedSphereGenerator.{u} 2)).mp
    (integralLiftedSphereGenerator_isGenerator 2)

theorem
    isSphereHurewiczIsomorphism_liftedHomotopySphere_of_cubeSphereFundamentalClass_of_nullhomotopic
    (hgen : IsSphereHomologyGenerator.{u} 2 cubeSphereFundamentalClass)
    (hnull : HurewiczThreeSphereNullhomotopic (liftedHomotopySphere.{u} 2))
    (x : liftedHomotopySphere.{u} 2) :
    IsSphereHurewiczIsomorphism 2 (liftedHomotopySphere.{u} 2) x
      (integralLiftedSphereGenerator.{u} 2) := by
  have hmul :=
    sphereHurewicz_integralLiftedSphereGenerator_mul_of_cubeSphereFundamentalClass hgen x
  have hinj : Function.Injective
      (sphereHurewicz 2 x (integralLiftedSphereGenerator.{u} 2)) :=
    (injective_sphereHurewicz_iff_forall_eq_one_of_additive 2 x
      (integralLiftedSphereGenerator.{u} 2) hmul).mpr
      (forall_sphereHurewicz_eq_zero_of_sphereNullhomotopic 2 x hnull)
  have hsurj : Function.Surjective
      (sphereHurewicz 2 x (integralLiftedSphereGenerator.{u} 2)) :=
    (surjective_sphereHurewicz_iff_forall_exists_map_eq 2 x
      (integralLiftedSphereGenerator.{u} 2)).mpr
      (hurewiczThreeSphereGeneration_liftedHomotopySphere_of_cubeSphereFundamentalClass hgen)
  exact ⟨⟨hinj, hsurj⟩, hmul⟩

theorem
    sphereHurewiczThreeCanonical_liftedHomotopySphere_of_cubeSphereFundamentalClass_of_nullhomotopic
    (hgen : IsSphereHomologyGenerator.{u} 2 cubeSphereFundamentalClass)
    (hnull : HurewiczThreeSphereNullhomotopic (liftedHomotopySphere.{u} 2)) :
    SphereHurewiczThreeCanonical (liftedHomotopySphere.{u} 2) :=
  fun x _ =>
    isSphereHurewiczIsomorphism_liftedHomotopySphere_of_cubeSphereFundamentalClass_of_nullhomotopic
      hgen hnull x

open DifferentialGeometry.PDE.RicciFlow.Surgery.Topology in
theorem hurewiczThree_liftedHomotopySphere_bijective_of_cubeSphereFundamentalClass_of_nullhomotopic
    (hgen : IsSphereHomologyGenerator.{u} 2 cubeSphereFundamentalClass)
    (hnull : HurewiczThreeSphereNullhomotopic (liftedHomotopySphere.{u} 2))
    (x : liftedHomotopySphere.{u} 2) :
    Function.Bijective (hurewiczThree x) := by
  rw [hurewiczThree_bijective_iff_sphereHurewicz_cubeSphereFundamentalClass
    (X := liftedHomotopySphere.{u} 2) x]
  exact (bijective_sphereHurewicz_iff_bijective_integralLiftedSphereGenerator 2 x
    cubeSphereFundamentalClass hgen).mpr
    (isSphereHurewiczIsomorphism_liftedHomotopySphere_of_cubeSphereFundamentalClass_of_nullhomotopic
      hgen hnull x).1

open DifferentialGeometry.PDE.RicciFlow.Surgery.Topology in
theorem
    hurewiczThree_standardThreeSphereLift_bijective_of_cubeSphereFundamentalClass_of_nullhomotopic
    (hgen : IsSphereHomologyGenerator.{u} 2 cubeSphereFundamentalClass)
    (hnull : HurewiczThreeSphereNullhomotopic (liftedHomotopySphere.{u} 2))
    (q : standardThreeSphereLift.{u}.Carrier) :
    Function.Bijective (hurewiczThree q) :=
  hurewiczThree_liftedHomotopySphere_bijective_of_cubeSphereFundamentalClass_of_nullhomotopic
    hgen hnull q

theorem hurewiczThreeSphereNullhomotopic_liftedHomotopySphere_of_sphereHurewiczThreeCanonical
    (x₀ : liftedHomotopySphere.{u} 2)
    (hπ₀ : Subsingleton (HomotopyGroup (Fin 2) (liftedHomotopySphere.{u} 2) x₀))
    (h : SphereHurewiczThreeCanonical (liftedHomotopySphere.{u} 2)) :
    HurewiczThreeSphereNullhomotopic (liftedHomotopySphere.{u} 2) :=
  hurewiczThreeSphereNullhomotopic_of_hurewiczThreeBijective
    (hurewiczThreeBijective_of_sphereHurewiczThreeCanonical h) x₀ hπ₀

theorem
    hurewiczThreeSphereNullhomotopic_of_sphereHurewiczTwoCanonical_of_sphereHurewiczThreeCanonical
    (h₂ : SphereHurewiczTwoCanonical (liftedHomotopySphere.{u} 2))
    (h₃ : SphereHurewiczThreeCanonical (liftedHomotopySphere.{u} 2)) :
    HurewiczThreeSphereNullhomotopic (liftedHomotopySphere.{u} 2) :=
  hurewiczThreeSphereNullhomotopic_liftedHomotopySphere_of_sphereHurewiczThreeCanonical
    (ULift.up (cubeSphereBasepoint 2))
    (homotopyTwo_subsingleton_of_sphereHurewiczTwoCanonical h₂
      subsingleton_integralSingularHomology_two_liftedHomotopySphere_two _)
    h₃

end DifferentialGeometry.Topology
