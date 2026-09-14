import DifferentialGeometry.Topology.Homology.HurewiczNullhomotopyCriterion
import DifferentialGeometry.Topology.Homology.HurewiczThreeWitness
import DifferentialGeometry.Topology.Homology.LiftedSphereFunctional

noncomputable section

open ContinuousMap Metric

universe u

namespace DifferentialGeometry.Topology

variable {X : Type u} [TopologicalSpace X]

theorem freeSphereHomologyImage_eq_zero_of_nullhomotopic (n : ℕ)
    (c : integralSingularHomology (n + 1) (liftedHomotopySphere.{u} n))
    {f : C(sphere (0 : EuclideanSpace ℝ (Fin (n + 2))) 1, X)} (hf : f.Nullhomotopic) :
    freeSphereHomologyImage n c (ZerothHomotopy.mk f) = 0 := by
  obtain ⟨y, hy⟩ := hf
  rw [ZerothHomotopy.sound (Joined.somePath ((homotopic_iff_joined f
      (ContinuousMap.const _ y)).mp hy)), freeSphereHomologyImage_const]

theorem freeSphereHomologyImage_eq_zero_of_homotopic (n : ℕ)
    (c : integralSingularHomology (n + 1) (liftedHomotopySphere.{u} n))
    {f g : C(sphere (0 : EuclideanSpace ℝ (Fin (n + 2))) 1, X)} (h : f.Homotopic g)
    (hf : freeSphereHomologyImage n c (ZerothHomotopy.mk f) = 0) :
    freeSphereHomologyImage n c (ZerothHomotopy.mk g) = 0 := by
  rw [ZerothHomotopy.sound (Joined.somePath ((homotopic_iff_joined f g).mp h))] at hf
  exact hf

theorem freeSphereHomologyImage_eq_zero_iff_of_isSphereHomologyGenerator (n : ℕ)
    (c : integralSingularHomology (n + 1) (liftedHomotopySphere.{u} n))
    (hc : IsSphereHomologyGenerator n c)
    (a : ZerothHomotopy C(sphere (0 : EuclideanSpace ℝ (Fin (n + 2))) 1, X)) :
    freeSphereHomologyImage n c a = 0 ↔
      freeSphereHomologyImage n (integralLiftedSphereGenerator.{u} n) a = 0 := by
  have hneg : freeSphereHomologyImage (X := X) n (-integralLiftedSphereGenerator.{u} n) =
      fun b => -freeSphereHomologyImage (X := X) n (integralLiftedSphereGenerator.{u} n) b := by
    funext b
    simpa using freeSphereHomologyImage_zsmul (X := X) n (-1)
      (integralLiftedSphereGenerator.{u} n) b
  rcases (isSphereHomologyGenerator_iff_eq_or_eq_neg_integralLiftedSphereGenerator n c).mp hc
    with h | h
  · rw [h]
  · rw [h, congrFun hneg a, neg_eq_zero]

def freeSphereDegree (n : ℕ) :
    ZerothHomotopy C(sphere (0 : EuclideanSpace ℝ (Fin (n + 2))) 1,
      liftedHomotopySphere.{u} n) → ℤ :=
  fun a => liftedSphereDegreeFunctional.{u} n
    (freeSphereHomologyImage n (integralLiftedSphereGenerator.{u} n) a)

theorem freeSphereDegree_apply (n : ℕ)
    (a : ZerothHomotopy C(sphere (0 : EuclideanSpace ℝ (Fin (n + 2))) 1,
      liftedHomotopySphere.{u} n)) :
    freeSphereDegree.{u} n a = liftedSphereDegreeFunctional.{u} n
      (freeSphereHomologyImage n (integralLiftedSphereGenerator.{u} n) a) := rfl

theorem freeSphereDegree_eq_zero_iff (n : ℕ)
    (a : ZerothHomotopy C(sphere (0 : EuclideanSpace ℝ (Fin (n + 2))) 1,
      liftedHomotopySphere.{u} n)) :
    freeSphereDegree.{u} n a = 0 ↔
      freeSphereHomologyImage n (integralLiftedSphereGenerator.{u} n) a = 0 := by
  constructor
  · intro h
    refine liftedSphereDegreeFunctional_injective n ?_
    rw [freeSphereDegree_apply] at h
    exact h.trans (map_zero (liftedSphereDegreeFunctional.{u} n)).symm
  · intro h
    rw [freeSphereDegree_apply, h, map_zero]

theorem freeSphereDegree_const (n : ℕ) (y : liftedHomotopySphere.{u} n) :
    freeSphereDegree.{u} n (ZerothHomotopy.mk (ContinuousMap.const _ y)) = 0 := by
  rw [freeSphereDegree_apply, freeSphereHomologyImage_const, map_zero]

theorem freeSphereDegree_eq_of_homotopic (n : ℕ)
    {f g : C(sphere (0 : EuclideanSpace ℝ (Fin (n + 2))) 1, liftedHomotopySphere.{u} n)}
    (h : f.Homotopic g) :
    freeSphereDegree.{u} n (ZerothHomotopy.mk f) =
      freeSphereDegree.{u} n (ZerothHomotopy.mk g) := by
  rw [ZerothHomotopy.sound (Joined.somePath ((homotopic_iff_joined f g).mp h))]

theorem freeSphereDegree_const_eq_zero_and_nullhomotopic (n : ℕ)
    (y : liftedHomotopySphere.{u} n) :
    freeSphereDegree.{u} n (ZerothHomotopy.mk (ContinuousMap.const _ y)) = 0 ∧
      (ContinuousMap.const _ y : C(sphere (0 : EuclideanSpace ℝ (Fin (n + 2))) 1,
        liftedHomotopySphere.{u} n)).Nullhomotopic :=
  ⟨freeSphereDegree_const n y, ⟨y, ContinuousMap.Homotopic.refl _⟩⟩

theorem freeSphereDegree_homotopyGroupToFreeSphere_identityClass (n : ℕ)
    (x : liftedHomotopySphere.{u} n) :
    freeSphereDegree.{u} n
      (homotopyGroupToFreeSphere n x (liftedHomotopySphereIdentityClass n x)) = 1 := by
  change liftedSphereDegreeFunctional.{u} n
    (sphereHurewicz n x (integralLiftedSphereGenerator.{u} n)
      (liftedHomotopySphereIdentityClass n x)) = 1
  rw [sphereHurewicz_liftedHomotopySphereIdentityClass,
    liftedSphereDegreeFunctional_generator]

theorem not_nullhomotopic_of_freeSphereDegree_ne_zero (n : ℕ)
    {f : C(sphere (0 : EuclideanSpace ℝ (Fin (n + 2))) 1, liftedHomotopySphere.{u} n)}
    (h : freeSphereDegree.{u} n (ZerothHomotopy.mk f) ≠ 0) : ¬ f.Nullhomotopic := by
  intro hf
  obtain ⟨y, hy⟩ := hf
  refine h ?_
  rw [ZerothHomotopy.sound (Joined.somePath ((homotopic_iff_joined f
    (ContinuousMap.const _ y)).mp hy))]
  exact freeSphereDegree_const n y

theorem exists_freeSphereDegree_eq_one_and_not_nullhomotopic (n : ℕ)
    (x : liftedHomotopySphere.{u} n) :
    ∃ f : C(sphere (0 : EuclideanSpace ℝ (Fin (n + 2))) 1, liftedHomotopySphere.{u} n),
      freeSphereDegree.{u} n (ZerothHomotopy.mk f) = 1 ∧ ¬ f.Nullhomotopic := by
  let q := homotopyGroupToFreeSphere n x (liftedHomotopySphereIdentityClass n x)
  have hout : ZerothHomotopy.mk (Quotient.out q) = q := Quotient.out_eq q
  refine ⟨Quotient.out q, ?_, ?_⟩
  · rw [hout]
    exact freeSphereDegree_homotopyGroupToFreeSphere_identityClass n x
  · refine not_nullhomotopic_of_freeSphereDegree_ne_zero n ?_
    rw [hout, freeSphereDegree_homotopyGroupToFreeSphere_identityClass]
    exact one_ne_zero

theorem hurewiczThreeSphereNullhomotopic_iff_forall_sphereHurewicz_eq_zero
    [SimplyConnectedSpace X] [PathConnectedSpace X] (x : X) :
    HurewiczThreeSphereNullhomotopic X ↔
      ∀ a : HomotopyGroup (Fin 3) X x,
        sphereHurewicz 2 x (integralLiftedSphereGenerator.{u} 2) a = 0 → a = 1 := by
  constructor
  · intro h
    refine (forall_sphereHurewicz_eq_zero_iff_forall_freeSphereHomologyImage_eq_zero 2 x
      (integralLiftedSphereGenerator.{u} 2)).mpr ?_
    intro f hf
    exact (zerothHomotopy_mk_eq_const_iff_nullhomotopic 2 x f).mpr (h f hf)
  · intro h f hf
    exact (zerothHomotopy_mk_eq_const_iff_nullhomotopic 2 x f).mp
      ((forall_sphereHurewicz_eq_zero_iff_forall_freeSphereHomologyImage_eq_zero 2 x
        (integralLiftedSphereGenerator.{u} 2)).mp h f hf)

theorem hurewiczTwoSphereNullhomotopic_iff_forall_sphereHurewicz_eq_zero
    [SimplyConnectedSpace X] [PathConnectedSpace X] (x : X) :
    HurewiczTwoSphereNullhomotopic X ↔
      ∀ a : HomotopyGroup (Fin 2) X x,
        sphereHurewicz 1 x (integralLiftedSphereGenerator.{u} 1) a = 0 → a = 1 := by
  constructor
  · intro h
    refine (forall_sphereHurewicz_eq_zero_iff_forall_freeSphereHomologyImage_eq_zero 1 x
      (integralLiftedSphereGenerator.{u} 1)).mpr ?_
    intro f hf
    exact (zerothHomotopy_mk_eq_const_iff_nullhomotopic 1 x f).mpr (h f hf)
  · intro h f hf
    exact (zerothHomotopy_mk_eq_const_iff_nullhomotopic 1 x f).mp
      ((forall_sphereHurewicz_eq_zero_iff_forall_freeSphereHomologyImage_eq_zero 1 x
        (integralLiftedSphereGenerator.{u} 1)).mp h f hf)

theorem hurewiczThreeSphereNullhomotopic_iff_subsingleton_homotopyGroup
    [SimplyConnectedSpace X] [PathConnectedSpace X] (x : X)
    [Subsingleton (integralSingularHomology 3 X)] :
    HurewiczThreeSphereNullhomotopic X ↔ Subsingleton (HomotopyGroup (Fin 3) X x) :=
  ⟨fun h => subsingleton_homotopyGroup_of_subsingleton_homology_of_sphereNullhomotopic 2 x h,
    fun _ => hurewiczThreeSphereNullhomotopic_of_subsingleton_homotopyGroup x⟩

theorem hurewiczTwoSphereNullhomotopic_iff_subsingleton_homotopyGroup
    [SimplyConnectedSpace X] [PathConnectedSpace X] (x : X)
    [Subsingleton (integralSingularHomology 2 X)] :
    HurewiczTwoSphereNullhomotopic X ↔ Subsingleton (HomotopyGroup (Fin 2) X x) :=
  ⟨fun h => subsingleton_homotopyGroup_of_subsingleton_homology_of_sphereNullhomotopic 1 x h,
    fun _ => hurewiczTwoSphereNullhomotopic_of_subsingleton_homotopyGroup x⟩

theorem hurewiczTwoSphereGeneration_liftedHomotopySphere :
    HurewiczTwoSphereGeneration (liftedHomotopySphere.{u} 2) :=
  @hurewiczTwoSphereGeneration_of_subsingleton (liftedHomotopySphere.{u} 2) _
    (ULift.up (cubeSphereBasepoint 2))
    (subsingleton_integralSingularHomology_two_liftedHomotopySphere_two.{u})

theorem hurewiczTwoSphereNullhomotopic_liftedHomotopySphere_iff_subsingleton_homotopyGroup
    (x : liftedHomotopySphere.{u} 2) :
    HurewiczTwoSphereNullhomotopic (liftedHomotopySphere.{u} 2) ↔
      Subsingleton (HomotopyGroup (Fin 2) (liftedHomotopySphere.{u} 2) x) :=
  @hurewiczTwoSphereNullhomotopic_iff_subsingleton_homotopyGroup (liftedHomotopySphere.{u} 2)
    _ _ _ x (subsingleton_integralSingularHomology_two_liftedHomotopySphere_two.{u})

theorem hurewiczThreeSphereNullhomotopic_liftedHomotopySphere_iff_forall_sphereHurewicz_eq_zero
    (x : liftedHomotopySphere.{u} 2) :
    HurewiczThreeSphereNullhomotopic (liftedHomotopySphere.{u} 2) ↔
      ∀ a : HomotopyGroup (Fin 3) (liftedHomotopySphere.{u} 2) x,
        sphereHurewicz 2 x (integralLiftedSphereGenerator.{u} 2) a = 0 → a = 1 :=
  hurewiczThreeSphereNullhomotopic_iff_forall_sphereHurewicz_eq_zero x

theorem hurewiczThreeSphereNullhomotopic_liftedHomotopySphere_iff_forall_freeSphereDegree_eq_zero :
    HurewiczThreeSphereNullhomotopic (liftedHomotopySphere.{u} 2) ↔
      ∀ f : C(sphere (0 : EuclideanSpace ℝ (Fin 4)) 1, liftedHomotopySphere.{u} 2),
        freeSphereDegree.{u} 2 (ZerothHomotopy.mk f) = 0 → f.Nullhomotopic := by
  constructor
  · intro h f hf
    exact h f ((freeSphereDegree_eq_zero_iff 2 (ZerothHomotopy.mk f)).mp hf)
  · intro h f hf
    exact h f ((freeSphereDegree_eq_zero_iff 2 (ZerothHomotopy.mk f)).mpr hf)

theorem hurewiczTwoSphereNullhomotopic_liftedHomotopySphere_iff_forall_freeSphereDegree_eq_zero :
    HurewiczTwoSphereNullhomotopic (liftedHomotopySphere.{u} 1) ↔
      ∀ f : C(sphere (0 : EuclideanSpace ℝ (Fin 3)) 1, liftedHomotopySphere.{u} 1),
        freeSphereDegree.{u} 1 (ZerothHomotopy.mk f) = 0 → f.Nullhomotopic := by
  constructor
  · intro h f hf
    exact h f ((freeSphereDegree_eq_zero_iff 1 (ZerothHomotopy.mk f)).mp hf)
  · intro h f hf
    exact h f ((freeSphereDegree_eq_zero_iff 1 (ZerothHomotopy.mk f)).mpr hf)

end DifferentialGeometry.Topology
