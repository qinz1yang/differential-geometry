import DifferentialGeometry.Topology.Homology.HurewiczFrontier
import DifferentialGeometry.Topology.Homology.HurewiczSphereCriterion
import DifferentialGeometry.Topology.Homology.HurewiczNullhomotopyCriterion
import DifferentialGeometry.Topology.Homology.LiftedSphereRelativeBridge
import DifferentialGeometry.Topology.Homology.LowDegreeHurewiczNonvacuity

noncomputable section

universe u

namespace DifferentialGeometry.Topology

variable {X : Type u} [TopologicalSpace X]

theorem bijective_sphereHurewicz_iff_of_path (n : ℕ) {x y : X} (p : Path x y)
    (c : integralSingularHomology (n + 1) (liftedHomotopySphere.{u} n)) :
    Function.Bijective (sphereHurewicz n x c) ↔
      Function.Bijective (sphereHurewicz n y c) := by
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
  rw [hfun]
  exact (Equiv.bijective_comp (homotopyGroupBasepointEquiv n p).symm (sphereHurewicz n x c)).symm

theorem surjective_sphereHurewicz_iff_surjective_freeSphereHomologyImage
    [PathConnectedSpace X] (n : ℕ) (x : X)
    (c : integralSingularHomology (n + 1) (liftedHomotopySphere.{u} n)) :
    Function.Surjective (sphereHurewicz n x c) ↔
      Function.Surjective (freeSphereHomologyImage (X := X) n c) := by
  constructor
  · intro h y
    obtain ⟨a, ha⟩ := h y
    refine ⟨homotopyGroupToFreeSphere n x a, ?_⟩
    change sphereHurewicz n x c a = y
    exact ha
  · intro h y
    obtain ⟨b, hb⟩ := h y
    obtain ⟨a, ha⟩ := homotopyGroupToFreeSphere_surjective n x b
    refine ⟨a, ?_⟩
    change freeSphereHomologyImage (X := X) n c (homotopyGroupToFreeSphere n x a) = y
    rw [ha, hb]

def HurewiczTwoBijective (X : Type u) [TopologicalSpace X] [SimplyConnectedSpace X] : Prop :=
  ∀ x : X, Function.Bijective (sphereHurewicz 1 x (integralLiftedSphereGenerator.{u} 1))

def HurewiczThreeBijective (X : Type u) [TopologicalSpace X] [SimplyConnectedSpace X] : Prop :=
  ∀ x : X, Subsingleton (HomotopyGroup (Fin 2) X x) →
    Function.Bijective (sphereHurewicz 2 x (integralLiftedSphereGenerator.{u} 2))

def HurewiczTwoMultiplicative (X : Type u) [TopologicalSpace X] : Prop :=
  ∀ (x : X) (c : integralSingularHomology 2 (liftedHomotopySphere.{u} 1))
    (_ : IsSphereHomologyGenerator 1 c) (a b : HomotopyGroup (Fin 2) X x),
    sphereHurewicz 1 x c (a * b) = sphereHurewicz 1 x c a + sphereHurewicz 1 x c b

def HurewiczThreeMultiplicative (X : Type u) [TopologicalSpace X] : Prop :=
  ∀ (x : X) (_ : Subsingleton (HomotopyGroup (Fin 2) X x))
    (c : integralSingularHomology 3 (liftedHomotopySphere.{u} 2))
    (_ : IsSphereHomologyGenerator 2 c) (a b : HomotopyGroup (Fin 3) X x),
    sphereHurewicz 2 x c (a * b) = sphereHurewicz 2 x c a + sphereHurewicz 2 x c b

def HurewiczTwoSphereGeneration (X : Type u) [TopologicalSpace X] : Prop :=
  ∀ y : integralSingularHomology 2 X,
    ∃ f : C(Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1, X),
      freeSphereHomologyImage 1 (integralLiftedSphereGenerator.{u} 1) (ZerothHomotopy.mk f) = y

def HurewiczTwoSphereNullhomotopic (X : Type u) [TopologicalSpace X] : Prop :=
  ∀ f : C(Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1, X),
    freeSphereHomologyImage 1 (integralLiftedSphereGenerator.{u} 1) (ZerothHomotopy.mk f) = 0 →
      f.Nullhomotopic

def HurewiczThreeSphereGeneration (X : Type u) [TopologicalSpace X] : Prop :=
  ∀ y : integralSingularHomology 3 X,
    ∃ f : C(Metric.sphere (0 : EuclideanSpace ℝ (Fin 4)) 1, X),
      freeSphereHomologyImage 2 (integralLiftedSphereGenerator.{u} 2) (ZerothHomotopy.mk f) = y

def HurewiczThreeSphereNullhomotopic (X : Type u) [TopologicalSpace X] : Prop :=
  ∀ f : C(Metric.sphere (0 : EuclideanSpace ℝ (Fin 4)) 1, X),
    freeSphereHomologyImage 2 (integralLiftedSphereGenerator.{u} 2) (ZerothHomotopy.mk f) = 0 →
      f.Nullhomotopic

theorem hurewiczTwoBijective_of_sphereHurewiczTwoCanonical [SimplyConnectedSpace X]
    (h : SphereHurewiczTwoCanonical X) : HurewiczTwoBijective X :=
  fun x => (h x).1

theorem hurewiczThreeBijective_of_sphereHurewiczThreeCanonical [SimplyConnectedSpace X]
    (h : SphereHurewiczThreeCanonical X) : HurewiczThreeBijective X :=
  fun x hπ => (h x hπ).1

theorem sphereHurewiczTwoCanonical_of_hurewiczTwoFrontier [SimplyConnectedSpace X]
    (h : HurewiczTwoBijective X ∧ HurewiczTwoMultiplicative X) :
    SphereHurewiczTwoCanonical X :=
  fun x => ⟨h.1 x, h.2 x (integralLiftedSphereGenerator.{u} 1)
    (integralLiftedSphereGenerator_isGenerator 1)⟩

theorem sphereHurewiczThreeCanonical_of_hurewiczThreeFrontier [SimplyConnectedSpace X]
    (h : HurewiczThreeBijective X ∧ HurewiczThreeMultiplicative X) :
    SphereHurewiczThreeCanonical X :=
  fun x hπ => ⟨h.1 x hπ, h.2 x hπ (integralLiftedSphereGenerator.{u} 2)
    (integralLiftedSphereGenerator_isGenerator 2)⟩

theorem hurewiczTwoFrontier_iff_sphereHurewiczTwoCanonical [SimplyConnectedSpace X] :
    (HurewiczTwoBijective X ∧ HurewiczTwoMultiplicative X) ↔
      SphereHurewiczTwoCanonical X :=
  ⟨sphereHurewiczTwoCanonical_of_hurewiczTwoFrontier,
    fun h => ⟨hurewiczTwoBijective_of_sphereHurewiczTwoCanonical h,
      fun x c hc => (IsSphereHurewiczIsomorphism.of_isSphereHomologyGenerator 1 (c := c) x hc
        (h x)).2⟩⟩

theorem hurewiczThreeFrontier_iff_sphereHurewiczThreeCanonical [SimplyConnectedSpace X] :
    (HurewiczThreeBijective X ∧ HurewiczThreeMultiplicative X) ↔
      SphereHurewiczThreeCanonical X :=
  ⟨sphereHurewiczThreeCanonical_of_hurewiczThreeFrontier,
    fun h => ⟨hurewiczThreeBijective_of_sphereHurewiczThreeCanonical h,
      fun x hπ c hc => (IsSphereHurewiczIsomorphism.of_isSphereHomologyGenerator 2 (c := c) x hc
        (h x hπ)).2⟩⟩

theorem hurewicz_two_isomorphism_of_frontier [SimplyConnectedSpace X]
    (h : HurewiczTwoBijective X ∧ HurewiczTwoMultiplicative X)
    (x : X) (c : integralSingularHomology 2 (liftedHomotopySphere.{u} 1))
    (hc : IsSphereHomologyGenerator 1 c) :
    Function.Bijective (sphereHurewicz 1 x c) ∧
      ∀ a b : HomotopyGroup (Fin 2) X x,
        sphereHurewicz 1 x c (a * b) = sphereHurewicz 1 x c a + sphereHurewicz 1 x c b :=
  ⟨(bijective_sphereHurewicz_iff_bijective_integralLiftedSphereGenerator 1 x c hc).mpr (h.1 x),
    h.2 x c hc⟩

theorem hurewicz_three_isomorphism_of_frontier [SimplyConnectedSpace X]
    (h : HurewiczThreeBijective X ∧ HurewiczThreeMultiplicative X)
    (x : X) (hπ₂ : Subsingleton (HomotopyGroup (Fin 2) X x))
    (c : integralSingularHomology 3 (liftedHomotopySphere.{u} 2))
    (hc : IsSphereHomologyGenerator 2 c) :
    Function.Bijective (sphereHurewicz 2 x c) ∧
      ∀ a b : HomotopyGroup (Fin 3) X x,
        sphereHurewicz 2 x c (a * b) = sphereHurewicz 2 x c a + sphereHurewicz 2 x c b :=
  ⟨(bijective_sphereHurewicz_iff_bijective_integralLiftedSphereGenerator 2 x c hc).mpr (h.1 x hπ₂),
    h.2 x hπ₂ c hc⟩

theorem hurewicz_two_isomorphism_iff_frontier [SimplyConnectedSpace X] :
    (∀ (x : X) (c : integralSingularHomology 2 (liftedHomotopySphere.{u} 1))
      (_ : IsSphereHomologyGenerator 1 c),
        Function.Bijective (sphereHurewicz 1 x c) ∧
          ∀ a b : HomotopyGroup (Fin 2) X x,
            sphereHurewicz 1 x c (a * b) = sphereHurewicz 1 x c a + sphereHurewicz 1 x c b) ↔
      HurewiczTwoBijective X ∧ HurewiczTwoMultiplicative X :=
  ⟨fun h => ⟨fun x => (h x (integralLiftedSphereGenerator.{u} 1)
      (integralLiftedSphereGenerator_isGenerator 1)).1,
    fun x c hc => (h x c hc).2⟩,
    fun h x c hc => hurewicz_two_isomorphism_of_frontier h x c hc⟩

theorem hurewicz_three_isomorphism_iff_frontier [SimplyConnectedSpace X] :
    (∀ (x : X) (_ : Subsingleton (HomotopyGroup (Fin 2) X x))
      (c : integralSingularHomology 3 (liftedHomotopySphere.{u} 2))
      (_ : IsSphereHomologyGenerator 2 c),
        Function.Bijective (sphereHurewicz 2 x c) ∧
          ∀ a b : HomotopyGroup (Fin 3) X x,
            sphereHurewicz 2 x c (a * b) = sphereHurewicz 2 x c a + sphereHurewicz 2 x c b) ↔
      HurewiczThreeBijective X ∧ HurewiczThreeMultiplicative X :=
  ⟨fun h => ⟨fun x hπ => (h x hπ (integralLiftedSphereGenerator.{u} 2)
      (integralLiftedSphereGenerator_isGenerator 2)).1,
    fun x hπ c hc => (h x hπ c hc).2⟩,
    fun h x hπ c hc => hurewicz_three_isomorphism_of_frontier h x hπ c hc⟩

theorem hurewiczTwoMultiplicative_of_liftedSquareCollapse_bijective
    (hT : Function.Bijective (integralRelativeHomologyMap 2 liftedSquareCollapse.{u}
      liftedSquareCollapse_mapsTo))
    (hrel : ∃ φ : integralRelativeHomology 2 (liftedSquareBoundary.{u}) →ₗ[ℤ] ℤ,
      φ liftedSquareRelativeFundamentalClass.{u} = 1) :
    HurewiczTwoMultiplicative X :=
  fun x c hc => hurewicz_two_mul_of_liftedSquareCollapse_bijective hT hrel x c hc

theorem hurewiczTwoSphereGeneration_of_hurewiczTwoBijective [SimplyConnectedSpace X]
    (h : HurewiczTwoBijective X) (x : X) : HurewiczTwoSphereGeneration X := by
  change ∀ y : integralSingularHomology 2 X,
    ∃ f : C(Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1, X),
      freeSphereHomologyImage 1 (integralLiftedSphereGenerator.{u} 1) (ZerothHomotopy.mk f) = y
  intro y
  obtain ⟨a, ha⟩ :=
    (surjective_sphereHurewicz_iff_surjective_freeSphereHomologyImage 1 x
      (integralLiftedSphereGenerator.{u} 1)).mp (h x).2 y
  have hout : ZerothHomotopy.mk (Quotient.out a) = a := Quotient.out_eq a
  exact ⟨Quotient.out a, by rw [hout]; exact ha⟩

theorem hurewiczTwoSphereNullhomotopic_of_hurewiczTwoBijective [SimplyConnectedSpace X]
    (h : HurewiczTwoBijective X) (x : X) : HurewiczTwoSphereNullhomotopic X := by
  change ∀ f : C(Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1, X),
    freeSphereHomologyImage 1 (integralLiftedSphereGenerator.{u} 1) (ZerothHomotopy.mk f) = 0 →
      f.Nullhomotopic
  intro f hf
  have hker := forall_sphereHurewicz_eq_zero_of_injective 1 x
    (integralLiftedSphereGenerator.{u} 1) (h x).1
  have hmk := (forall_sphereHurewicz_eq_zero_iff_forall_freeSphereHomologyImage_eq_zero 1 x
    (integralLiftedSphereGenerator.{u} 1)).mp hker f hf
  exact (zerothHomotopy_mk_eq_const_iff_nullhomotopic 1 x f).mp hmk

theorem hurewiczThreeSphereGeneration_of_hurewiczThreeBijective [SimplyConnectedSpace X]
    (h : HurewiczThreeBijective X) (x : X)
    (hπ : Subsingleton (HomotopyGroup (Fin 2) X x)) : HurewiczThreeSphereGeneration X := by
  change ∀ y : integralSingularHomology 3 X,
    ∃ f : C(Metric.sphere (0 : EuclideanSpace ℝ (Fin 4)) 1, X),
      freeSphereHomologyImage 2 (integralLiftedSphereGenerator.{u} 2) (ZerothHomotopy.mk f) = y
  intro y
  obtain ⟨a, ha⟩ :=
    (surjective_sphereHurewicz_iff_surjective_freeSphereHomologyImage 2 x
      (integralLiftedSphereGenerator.{u} 2)).mp (h x hπ).2 y
  have hout : ZerothHomotopy.mk (Quotient.out a) = a := Quotient.out_eq a
  exact ⟨Quotient.out a, by rw [hout]; exact ha⟩

theorem hurewiczThreeSphereNullhomotopic_of_hurewiczThreeBijective [SimplyConnectedSpace X]
    (h : HurewiczThreeBijective X) (x : X)
    (hπ : Subsingleton (HomotopyGroup (Fin 2) X x)) :
    HurewiczThreeSphereNullhomotopic X := by
  change ∀ f : C(Metric.sphere (0 : EuclideanSpace ℝ (Fin 4)) 1, X),
    freeSphereHomologyImage 2 (integralLiftedSphereGenerator.{u} 2) (ZerothHomotopy.mk f) = 0 →
      f.Nullhomotopic
  intro f hf
  have hker := forall_sphereHurewicz_eq_zero_of_injective 2 x
    (integralLiftedSphereGenerator.{u} 2) (h x hπ).1
  have hmk := (forall_sphereHurewicz_eq_zero_iff_forall_freeSphereHomologyImage_eq_zero 2 x
    (integralLiftedSphereGenerator.{u} 2)).mp hker f hf
  exact (zerothHomotopy_mk_eq_const_iff_nullhomotopic 2 x f).mp hmk

theorem hurewiczTwoBijective_iff_sphereCriterion_of_multiplicative [SimplyConnectedSpace X]
    (hmul : HurewiczTwoMultiplicative X) (x₀ : X) :
    HurewiczTwoBijective X ↔
      HurewiczTwoSphereGeneration X ∧ HurewiczTwoSphereNullhomotopic X := by
  constructor
  · intro h
    exact ⟨hurewiczTwoSphereGeneration_of_hurewiczTwoBijective h x₀,
      hurewiczTwoSphereNullhomotopic_of_hurewiczTwoBijective h x₀⟩
  · rintro ⟨hg, hk⟩
    have hgen : ∀ y : integralSingularHomology 2 X,
        ∃ f : C(Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1, X),
          freeSphereHomologyImage 1 (integralLiftedSphereGenerator.{u} 1)
            (ZerothHomotopy.mk f) = y := hg
    have hnull' : ∀ f : C(Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1, X),
        freeSphereHomologyImage 1 (integralLiftedSphereGenerator.{u} 1)
          (ZerothHomotopy.mk f) = 0 → f.Nullhomotopic := hk
    have hnull : ∀ f : C(Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1, X),
        freeSphereHomologyImage 1 (integralLiftedSphereGenerator.{u} 1)
          (ZerothHomotopy.mk f) = 0 →
        ZerothHomotopy.mk f = ZerothHomotopy.mk (ContinuousMap.const _ x₀) :=
      fun f hf => (zerothHomotopy_mk_eq_const_iff_nullhomotopic 1 x₀ f).mpr (hnull' f hf)
    have hx₀ : Function.Bijective (sphereHurewicz 1 x₀
        (integralLiftedSphereGenerator.{u} 1)) :=
      (bijective_sphereHurewicz_iff_forall_exists_map_eq_and_nullhomotopic_of_additive 1 x₀
        (integralLiftedSphereGenerator.{u} 1)
        (hmul x₀ (integralLiftedSphereGenerator.{u} 1)
          (integralLiftedSphereGenerator_isGenerator 1))).mpr ⟨hgen, hnull⟩
    intro x
    exact (bijective_sphereHurewicz_iff_of_path 1
      (PathConnectedSpace.somePath x₀ x) (integralLiftedSphereGenerator.{u} 1)).mp hx₀

theorem hurewiczThreeBijective_iff_sphereCriterion_of_multiplicative [SimplyConnectedSpace X]
    (hmul : HurewiczThreeMultiplicative X) (x₀ : X)
    (hπ₀ : Subsingleton (HomotopyGroup (Fin 2) X x₀)) :
    HurewiczThreeBijective X ↔
      HurewiczThreeSphereGeneration X ∧ HurewiczThreeSphereNullhomotopic X := by
  constructor
  · intro h
    exact ⟨hurewiczThreeSphereGeneration_of_hurewiczThreeBijective h x₀ hπ₀,
      hurewiczThreeSphereNullhomotopic_of_hurewiczThreeBijective h x₀ hπ₀⟩
  · rintro ⟨hg, hk⟩
    have hgen : ∀ y : integralSingularHomology 3 X,
        ∃ f : C(Metric.sphere (0 : EuclideanSpace ℝ (Fin 4)) 1, X),
          freeSphereHomologyImage 2 (integralLiftedSphereGenerator.{u} 2)
            (ZerothHomotopy.mk f) = y := hg
    have hnull' : ∀ f : C(Metric.sphere (0 : EuclideanSpace ℝ (Fin 4)) 1, X),
        freeSphereHomologyImage 2 (integralLiftedSphereGenerator.{u} 2)
          (ZerothHomotopy.mk f) = 0 → f.Nullhomotopic := hk
    have hnull : ∀ f : C(Metric.sphere (0 : EuclideanSpace ℝ (Fin 4)) 1, X),
        freeSphereHomologyImage 2 (integralLiftedSphereGenerator.{u} 2)
          (ZerothHomotopy.mk f) = 0 →
        ZerothHomotopy.mk f = ZerothHomotopy.mk (ContinuousMap.const _ x₀) :=
      fun f hf => (zerothHomotopy_mk_eq_const_iff_nullhomotopic 2 x₀ f).mpr (hnull' f hf)
    have hx₀ : Function.Bijective (sphereHurewicz 2 x₀
        (integralLiftedSphereGenerator.{u} 2)) :=
      (bijective_sphereHurewicz_iff_forall_exists_map_eq_and_nullhomotopic_of_additive 2 x₀
        (integralLiftedSphereGenerator.{u} 2)
        (hmul x₀ hπ₀ (integralLiftedSphereGenerator.{u} 2)
          (integralLiftedSphereGenerator_isGenerator 2))).mpr ⟨hgen, hnull⟩
    intro x hπ
    exact (bijective_sphereHurewicz_iff_of_path 2
      (PathConnectedSpace.somePath x₀ x) (integralLiftedSphereGenerator.{u} 2)).mp hx₀

theorem hurewiczTwoBijective_punit : HurewiczTwoBijective PUnit.{u + 1} :=
  fun x => (sphereHurewiczTwoCanonical_punit x).1

theorem hurewiczThreeBijective_punit : HurewiczThreeBijective PUnit.{u + 1} :=
  fun x hπ => (sphereHurewiczThreeCanonical_punit x hπ).1

theorem hurewiczTwoMultiplicative_punit : HurewiczTwoMultiplicative PUnit.{u + 1} :=
  fun x c hc => (IsSphereHurewiczIsomorphism.of_isSphereHomologyGenerator 1 (c := c) x hc
    (sphereHurewiczTwoCanonical_punit x)).2

theorem hurewiczThreeMultiplicative_punit : HurewiczThreeMultiplicative PUnit.{u + 1} :=
  fun x hπ c hc => (IsSphereHurewiczIsomorphism.of_isSphereHomologyGenerator 2 (c := c) x hc
    (sphereHurewiczThreeCanonical_punit x hπ)).2

theorem hurewiczTwoBijective_of_subsingleton [SimplyConnectedSpace X]
    (hπ : ∀ x : X, Subsingleton (HomotopyGroup (Fin 2) X x))
    (hH : Subsingleton (integralSingularHomology 2 X)) : HurewiczTwoBijective X := by
  refine fun x => ?_
  have hinst := hπ x
  have hinst' := hH
  exact (IsSphereHurewiczIsomorphism.of_subsingleton 1 x
    (integralLiftedSphereGenerator.{u} 1)).1

theorem hurewiczTwoMultiplicative_of_subsingleton [SimplyConnectedSpace X]
    (hπ : ∀ x : X, Subsingleton (HomotopyGroup (Fin 2) X x))
    (hH : Subsingleton (integralSingularHomology 2 X)) : HurewiczTwoMultiplicative X := by
  refine fun x c hc => ?_
  have hinst := hπ x
  have hinst' := hH
  exact (IsSphereHurewiczIsomorphism.of_subsingleton 1 x c).2

theorem not_surjective_sphereHurewicz_zero_twoSphere
    (x : Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1) :
    ¬ Function.Surjective (sphereHurewicz 1 x
      (0 : integralSingularHomology 2 (liftedHomotopySphere.{0} 1))) := by
  intro hsurj
  have hzero : sphereHurewicz 1 x
      (0 : integralSingularHomology 2 (liftedHomotopySphere.{0} 1)) = 0 :=
    funext fun a => sphereHurewicz_zero 1 x a
  have hsub : Subsingleton
      (integralSingularHomology 2 (Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1)) :=
    ⟨fun a b => by
      obtain ⟨p, hp⟩ := hsurj a
      obtain ⟨q, hq⟩ := hsurj b
      rw [← hp, ← hq, hzero]
      rfl⟩
  exact not_subsingleton_integralSingularHomology_two_twoSphere hsub

end DifferentialGeometry.Topology
