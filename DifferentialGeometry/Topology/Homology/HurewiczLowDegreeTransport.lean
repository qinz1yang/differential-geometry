import DifferentialGeometry.Topology.Homology.CubeSphereMayerVietorisAlignment
import DifferentialGeometry.Topology.Homology.HurewiczLowDegreeFrontierInstances
import DifferentialGeometry.Topology.Homology.HurewiczSphereCriterion

noncomputable section

open ContinuousMap

open scoped ContinuousMap

universe u

namespace DifferentialGeometry.Topology

variable {X : Type u} [TopologicalSpace X]
variable {Y : Type u} [TopologicalSpace Y]

theorem hurewiczSphereGeneration_of_homotopyEquiv (n : ℕ) (e : X ≃ₕ Y)
    (h : ∀ y : integralSingularHomology (n + 1) X,
      ∃ f : C(Metric.sphere (0 : EuclideanSpace ℝ (Fin (n + 2))) 1, X),
        freeSphereHomologyImage n (integralLiftedSphereGenerator.{u} n)
          (ZerothHomotopy.mk f) = y) :
    ∀ y : integralSingularHomology (n + 1) Y,
      ∃ f : C(Metric.sphere (0 : EuclideanSpace ℝ (Fin (n + 2))) 1, Y),
        freeSphereHomologyImage n (integralLiftedSphereGenerator.{u} n)
          (ZerothHomotopy.mk f) = y := by
  intro y
  obtain ⟨f, hf⟩ := h ((integralSingularHomologyHomotopyEquiv (n + 1) e).symm y)
  refine ⟨e.toFun.comp f, ?_⟩
  have hn := freeSphereHomologyImage_natural n (integralLiftedSphereGenerator.{u} n)
    e.toFun (ZerothHomotopy.mk f)
  rw [freeSpherePostcompose_mk, hf] at hn
  rw [hn]
  exact LinearEquiv.apply_symm_apply (integralSingularHomologyHomotopyEquiv (n + 1) e) y

theorem hurewiczSphereNullhomotopic_of_homotopyEquiv (n : ℕ) (e : X ≃ₕ Y)
    (h : ∀ f : C(Metric.sphere (0 : EuclideanSpace ℝ (Fin (n + 2))) 1, X),
      freeSphereHomologyImage n (integralLiftedSphereGenerator.{u} n)
        (ZerothHomotopy.mk f) = 0 → f.Nullhomotopic) :
    ∀ f : C(Metric.sphere (0 : EuclideanSpace ℝ (Fin (n + 2))) 1, Y),
      freeSphereHomologyImage n (integralLiftedSphereGenerator.{u} n)
        (ZerothHomotopy.mk f) = 0 → f.Nullhomotopic := by
  intro f hf
  have hgf : (e.toFun.comp (e.invFun.comp f)).Homotopic f := by
    have h1 : ((e.toFun.comp e.invFun).comp f).Homotopic ((ContinuousMap.id Y).comp f) :=
      e.right_inv.comp (Homotopic.refl f)
    simpa only [ContinuousMap.comp_assoc, ContinuousMap.id_comp] using h1
  have himg : freeSphereHomologyImage n (integralLiftedSphereGenerator.{u} n)
      (ZerothHomotopy.mk (e.invFun.comp f)) = 0 := by
    have hpath : ZerothHomotopy.mk (e.toFun.comp (e.invFun.comp f)) = ZerothHomotopy.mk f :=
      ZerothHomotopy.sound (Joined.somePath ((homotopic_iff_joined _ _).mp hgf))
    have hn := freeSphereHomologyImage_natural n (integralLiftedSphereGenerator.{u} n)
      e.toFun (ZerothHomotopy.mk (e.invFun.comp f))
    rw [freeSpherePostcompose_mk, hpath, hf] at hn
    refine (integralSingularHomologyHomotopyEquiv (n + 1) e).injective ?_
    rw [map_zero]
    exact hn.symm
  obtain ⟨z, hz⟩ := (h (e.invFun.comp f) himg).comp_right e.toFun
  exact ⟨z, hgf.symm.trans hz⟩

theorem hurewiczTwoSphereGeneration_iff_of_homotopyEquiv (e : X ≃ₕ Y) :
    HurewiczTwoSphereGeneration X ↔ HurewiczTwoSphereGeneration Y :=
  ⟨hurewiczSphereGeneration_of_homotopyEquiv 1 e,
    hurewiczSphereGeneration_of_homotopyEquiv 1 e.symm⟩

theorem hurewiczThreeSphereGeneration_iff_of_homotopyEquiv (e : X ≃ₕ Y) :
    HurewiczThreeSphereGeneration X ↔ HurewiczThreeSphereGeneration Y :=
  ⟨hurewiczSphereGeneration_of_homotopyEquiv 2 e,
    hurewiczSphereGeneration_of_homotopyEquiv 2 e.symm⟩

theorem hurewiczTwoSphereNullhomotopic_iff_of_homotopyEquiv (e : X ≃ₕ Y) :
    HurewiczTwoSphereNullhomotopic X ↔ HurewiczTwoSphereNullhomotopic Y :=
  ⟨hurewiczSphereNullhomotopic_of_homotopyEquiv 1 e,
    hurewiczSphereNullhomotopic_of_homotopyEquiv 1 e.symm⟩

theorem hurewiczThreeSphereNullhomotopic_iff_of_homotopyEquiv (e : X ≃ₕ Y) :
    HurewiczThreeSphereNullhomotopic X ↔ HurewiczThreeSphereNullhomotopic Y :=
  ⟨hurewiczSphereNullhomotopic_of_homotopyEquiv 2 e,
    hurewiczSphereNullhomotopic_of_homotopyEquiv 2 e.symm⟩

theorem forall_sphereHurewicz_eq_zero_of_freeSphereNullhomotopic [SimplyConnectedSpace X]
    (n : ℕ) (x : X)
    (c : integralSingularHomology (n + 1) (liftedHomotopySphere.{u} n))
    (h : ∀ f : C(Metric.sphere (0 : EuclideanSpace ℝ (Fin (n + 2))) 1, X),
      freeSphereHomologyImage n c (ZerothHomotopy.mk f) = 0 → f.Nullhomotopic) :
    ∀ a : HomotopyGroup (Fin (n + 1)) X x, sphereHurewicz n x c a = 0 → a = 1 :=
  (forall_sphereHurewicz_eq_zero_iff_forall_freeSphereHomologyImage_eq_zero n x c).mpr
    (fun f hf => (zerothHomotopy_mk_eq_const_iff_nullhomotopic n x f).mpr (h f hf))

theorem forall_sphereHurewicz_eq_zero_of_sphereNullhomotopic [SimplyConnectedSpace X]
    (n : ℕ) (x : X)
    (h : ∀ f : C(Metric.sphere (0 : EuclideanSpace ℝ (Fin (n + 2))) 1, X),
      freeSphereHomologyImage n (integralLiftedSphereGenerator.{u} n)
        (ZerothHomotopy.mk f) = 0 → f.Nullhomotopic) :
    ∀ a : HomotopyGroup (Fin (n + 1)) X x,
      sphereHurewicz n x (integralLiftedSphereGenerator.{u} n) a = 0 → a = 1 :=
  forall_sphereHurewicz_eq_zero_of_freeSphereNullhomotopic n x
    (integralLiftedSphereGenerator.{u} n) h

theorem subsingleton_homotopyGroup_of_subsingleton_homology_of_sphereNullhomotopic
    [SimplyConnectedSpace X] (n : ℕ) (x : X)
    (h : ∀ f : C(Metric.sphere (0 : EuclideanSpace ℝ (Fin (n + 2))) 1, X),
      freeSphereHomologyImage n (integralLiftedSphereGenerator.{u} n)
        (ZerothHomotopy.mk f) = 0 → f.Nullhomotopic)
    [Subsingleton (integralSingularHomology (n + 1) X)] :
    Subsingleton (HomotopyGroup (Fin (n + 1)) X x) := by
  refine ⟨fun a b => ?_⟩
  have hker := forall_sphereHurewicz_eq_zero_of_sphereNullhomotopic n x h
  have h1 : a * b⁻¹ = 1 := hker (a * b⁻¹) (Subsingleton.elim _ _)
  exact mul_inv_eq_one.mp h1

theorem homotopyTwo_subsingleton_of_homologyTwo_of_sphereNullhomotopic
    [SimplyConnectedSpace X] (h : HurewiczTwoSphereNullhomotopic X)
    [Subsingleton (integralSingularHomology 2 X)] (x : X) :
    Subsingleton (HomotopyGroup (Fin 2) X x) :=
  subsingleton_homotopyGroup_of_subsingleton_homology_of_sphereNullhomotopic 1 x h

theorem homotopyThree_subsingleton_of_homologyThree_of_sphereNullhomotopic
    [SimplyConnectedSpace X] (h : HurewiczThreeSphereNullhomotopic X)
    [Subsingleton (integralSingularHomology 3 X)] (x : X) :
    Subsingleton (HomotopyGroup (Fin 3) X x) :=
  subsingleton_homotopyGroup_of_subsingleton_homology_of_sphereNullhomotopic 2 x h

open DifferentialGeometry.PDE.RicciFlow.Surgery.Topology in
theorem injective_hurewiczThree_of_freeSphereNullhomotopic [SimplyConnectedSpace X] (x : X)
    (h : ∀ f : C(Metric.sphere (0 : EuclideanSpace ℝ (Fin 4)) 1, X),
      freeSphereHomologyImage 2 cubeSphereFundamentalClass (ZerothHomotopy.mk f) = 0 →
        f.Nullhomotopic) :
    Function.Injective (hurewiczThree x) := by
  have hker : ∀ a : HomotopyGroup (Fin 3) X x, hurewiczThree x a = 0 → a = 1 :=
    fun a ha => forall_sphereHurewicz_eq_zero_of_freeSphereNullhomotopic 2 x
      cubeSphereFundamentalClass h a
      ((congrFun (sphereHurewicz_cubeSphereFundamentalClass x) a).trans ha)
  intro a b hab
  have hb : hurewiczThree x b⁻¹ = -hurewiczThree x b := by
    simpa using hurewiczThree_zpow b (-1)
  have h0 : hurewiczThree x (a * b⁻¹) = 0 := by
    rw [hurewiczThree_mul, hab, hb, add_neg_cancel]
  exact mul_inv_eq_one.mp (hker (a * b⁻¹) h0)

theorem sphereHurewiczTwoCanonical_iff_hurewiczTwoBijective_of_multiplicative
    [SimplyConnectedSpace X] (hmul : HurewiczTwoMultiplicative X) :
    SphereHurewiczTwoCanonical X ↔ HurewiczTwoBijective X :=
  ⟨hurewiczTwoBijective_of_sphereHurewiczTwoCanonical,
    fun h x => ⟨h x, hmul x (integralLiftedSphereGenerator.{u} 1)
      (integralLiftedSphereGenerator_isGenerator 1)⟩⟩

theorem sphereHurewiczThreeCanonical_iff_hurewiczThreeBijective_of_multiplicative
    [SimplyConnectedSpace X] (hmul : HurewiczThreeMultiplicative X) :
    SphereHurewiczThreeCanonical X ↔ HurewiczThreeBijective X :=
  ⟨hurewiczThreeBijective_of_sphereHurewiczThreeCanonical,
    fun h x hπ => ⟨h x hπ, hmul x hπ (integralLiftedSphereGenerator.{u} 2)
      (integralLiftedSphereGenerator_isGenerator 2)⟩⟩

theorem hurewiczTwoBijective_iff_of_homotopyEquiv (e : X ≃ₕ Y) [SimplyConnectedSpace X]
    [SimplyConnectedSpace Y] (x : X) (y : Y)
    (hsq : IsSphereHomologyGenerator.{u} 1 squareSphereFundamentalClass.{u}) :
    HurewiczTwoBijective X ↔ HurewiczTwoBijective Y := by
  rw [hurewiczTwoBijective_iff_sphereCriterion_of_multiplicative
      (hurewiczTwoMultiplicative_of_squareSphereFundamentalClass_isGenerator (X := X) hsq) x,
    hurewiczTwoBijective_iff_sphereCriterion_of_multiplicative
      (hurewiczTwoMultiplicative_of_squareSphereFundamentalClass_isGenerator (X := Y) hsq) y,
    hurewiczTwoSphereGeneration_iff_of_homotopyEquiv e,
    hurewiczTwoSphereNullhomotopic_iff_of_homotopyEquiv e]

theorem sphereHurewiczTwoCanonical_iff_of_homotopyEquiv (e : X ≃ₕ Y) [SimplyConnectedSpace X]
    [SimplyConnectedSpace Y] (x : X) (y : Y)
    (hsq : IsSphereHomologyGenerator.{u} 1 squareSphereFundamentalClass.{u}) :
    SphereHurewiczTwoCanonical X ↔ SphereHurewiczTwoCanonical Y := by
  rw [sphereHurewiczTwoCanonical_iff_hurewiczTwoBijective_of_multiplicative
      (hurewiczTwoMultiplicative_of_squareSphereFundamentalClass_isGenerator (X := X) hsq),
    hurewiczTwoBijective_iff_of_homotopyEquiv e x y hsq,
    ← sphereHurewiczTwoCanonical_iff_hurewiczTwoBijective_of_multiplicative
      (hurewiczTwoMultiplicative_of_squareSphereFundamentalClass_isGenerator (X := Y) hsq)]

theorem hurewiczThreeBijective_iff_of_homotopyEquiv (e : X ≃ₕ Y) [SimplyConnectedSpace X]
    [SimplyConnectedSpace Y] (x : X) (y : Y)
    (hπx : Subsingleton (HomotopyGroup (Fin 2) X x))
    (hπy : Subsingleton (HomotopyGroup (Fin 2) Y y))
    (hc : IsSphereHomologyGenerator.{u} 2 cubeSphereFundamentalClass.{u}) :
    HurewiczThreeBijective X ↔ HurewiczThreeBijective Y := by
  rw [hurewiczThreeBijective_iff_sphereCriterion_of_multiplicative
      (hurewiczThreeMultiplicative_of_cubeSphereFundamentalClass_isSphereHomologyGenerator
        (X := X) hc) x hπx,
    hurewiczThreeBijective_iff_sphereCriterion_of_multiplicative
      (hurewiczThreeMultiplicative_of_cubeSphereFundamentalClass_isSphereHomologyGenerator
        (X := Y) hc) y hπy,
    hurewiczThreeSphereGeneration_iff_of_homotopyEquiv e,
    hurewiczThreeSphereNullhomotopic_iff_of_homotopyEquiv e]

theorem sphereHurewiczThreeCanonical_iff_of_homotopyEquiv (e : X ≃ₕ Y) [SimplyConnectedSpace X]
    [SimplyConnectedSpace Y] (x : X) (y : Y)
    (hπx : Subsingleton (HomotopyGroup (Fin 2) X x))
    (hπy : Subsingleton (HomotopyGroup (Fin 2) Y y))
    (hc : IsSphereHomologyGenerator.{u} 2 cubeSphereFundamentalClass.{u}) :
    SphereHurewiczThreeCanonical X ↔ SphereHurewiczThreeCanonical Y := by
  rw [sphereHurewiczThreeCanonical_iff_hurewiczThreeBijective_of_multiplicative
      (hurewiczThreeMultiplicative_of_cubeSphereFundamentalClass_isSphereHomologyGenerator
        (X := X) hc),
    hurewiczThreeBijective_iff_of_homotopyEquiv e x y hπx hπy hc,
    ← sphereHurewiczThreeCanonical_iff_hurewiczThreeBijective_of_multiplicative
      (hurewiczThreeMultiplicative_of_cubeSphereFundamentalClass_isSphereHomologyGenerator
        (X := Y) hc)]

theorem isSphereHomologyGenerator_squareSphereFundamentalClass_of_cubeSphereFundamentalClass
    {B : Type u} [AddCommGroup B] [Module ℤ B]
    (f : CubeSphereMayerVietorisSource.{u} ≃ₗ[ℤ] B) (g : B ≃ₗ[ℤ] ℤ)
    (τ : B ≃ₗ[ℤ] integralSingularHomology 2 (liftedHomotopySphere.{u} 1))
    (halign : integralSphereHomologyShiftEquiv_cubeSphereFundamentalClass f τ)
    (hc : IsSphereHomologyGenerator.{u} 2 cubeSphereFundamentalClass.{u}) :
    IsSphereHomologyGenerator.{u} 1 squareSphereFundamentalClass.{u} :=
  (isSphereHomologyGenerator_cubeSphereFundamentalClass_iff_squareSphereFundamentalClass
    f g τ halign).mp hc

theorem hurewiczTwoMultiplicative_of_cubeSphereFundamentalClass_isSphereHomologyGenerator
    {B : Type u} [AddCommGroup B] [Module ℤ B]
    (f : CubeSphereMayerVietorisSource.{u} ≃ₗ[ℤ] B) (g : B ≃ₗ[ℤ] ℤ)
    (τ : B ≃ₗ[ℤ] integralSingularHomology 2 (liftedHomotopySphere.{u} 1))
    (halign : integralSphereHomologyShiftEquiv_cubeSphereFundamentalClass f τ)
    (hc : IsSphereHomologyGenerator.{u} 2 cubeSphereFundamentalClass.{u}) :
    HurewiczTwoMultiplicative X :=
  hurewiczTwoMultiplicative_of_squareSphereFundamentalClass_isGenerator (X := X)
    (isSphereHomologyGenerator_squareSphereFundamentalClass_of_cubeSphereFundamentalClass
      f g τ halign hc)

theorem hurewiczThreeMultiplicative_of_squareSphereFundamentalClass_isSphereHomologyGenerator
    {B : Type u} [AddCommGroup B] [Module ℤ B]
    (f : CubeSphereMayerVietorisSource.{u} ≃ₗ[ℤ] B) (g : B ≃ₗ[ℤ] ℤ)
    (τ : B ≃ₗ[ℤ] integralSingularHomology 2 (liftedHomotopySphere.{u} 1))
    (halign : integralSphereHomologyShiftEquiv_cubeSphereFundamentalClass f τ)
    (hc : IsSphereHomologyGenerator.{u} 1 squareSphereFundamentalClass.{u}) :
    HurewiczThreeMultiplicative X :=
  hurewiczThreeMultiplicative_of_cubeSphereFundamentalClass_isSphereHomologyGenerator (X := X)
    ((isSphereHomologyGenerator_cubeSphereFundamentalClass_iff_squareSphereFundamentalClass
      f g τ halign).mpr hc)

theorem hurewiczTwoMultiplicative_and_hurewiczThreeMultiplicative_of_squareSphereFundamentalClass
    {B : Type u} [AddCommGroup B] [Module ℤ B]
    (f : CubeSphereMayerVietorisSource.{u} ≃ₗ[ℤ] B) (g : B ≃ₗ[ℤ] ℤ)
    (τ : B ≃ₗ[ℤ] integralSingularHomology 2 (liftedHomotopySphere.{u} 1))
    (halign : integralSphereHomologyShiftEquiv_cubeSphereFundamentalClass f τ)
    (hc : IsSphereHomologyGenerator.{u} 1 squareSphereFundamentalClass.{u}) :
    HurewiczTwoMultiplicative X ∧ HurewiczThreeMultiplicative X :=
  ⟨hurewiczTwoMultiplicative_of_squareSphereFundamentalClass_isGenerator (X := X) hc,
    hurewiczThreeMultiplicative_of_squareSphereFundamentalClass_isSphereHomologyGenerator
      f g τ halign hc⟩

end DifferentialGeometry.Topology
