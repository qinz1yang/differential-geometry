import DifferentialGeometry.Topology.Homology.HurewiczLowDegreeHypothesis
import DifferentialGeometry.Topology.Homology.Homotopy
import DifferentialGeometry.Topology.Homotopy.BasedMap

noncomputable section


universe u

namespace DifferentialGeometry.Topology

variable {X : Type u} [TopologicalSpace X]
variable {Y : Type u} [TopologicalSpace Y]

theorem homotopyGroupBasedHomeomorphMulEquiv_apply {N : Type*} [DecidableEq N] [Nonempty N]
    (e : X ≃ₜ Y) (x : X) (y : Y) (he : e x = y) (a : HomotopyGroup N X x) :
    homotopyGroupBasedHomeomorphMulEquiv e x y he a =
      homotopyGroupBasedMap (⟨e, e.continuous⟩ : C(X, Y)) x y he a := by
  induction a using Quotient.inductionOn with
  | h p => rfl

theorem sphereHurewicz_homeomorph_apply (n : ℕ) (e : X ≃ₜ Y) {x : X} {y : Y} (he : e x = y)
    (c : integralSingularHomology (n + 1) (liftedHomotopySphere.{u} n))
    (a : HomotopyGroup (Fin (n + 1)) X x) :
    sphereHurewicz n y c (homotopyGroupBasedHomeomorphMulEquiv e x y he a) =
      integralSingularHomologyMap (n + 1) (⟨e, e.continuous⟩ : C(X, Y))
        (sphereHurewicz n x c a) := by
  rw [homotopyGroupBasedHomeomorphMulEquiv_apply]
  exact sphereHurewicz_natural n (⟨e, e.continuous⟩ : C(X, Y)) x y he c a

theorem bijective_sphereHurewicz_of_homeomorph (n : ℕ) (e : X ≃ₜ Y) {x : X} {y : Y}
    (he : e x = y) (c : integralSingularHomology (n + 1) (liftedHomotopySphere.{u} n))
    (h : Function.Bijective (sphereHurewicz n x c)) :
    Function.Bijective (sphereHurewicz n y c) := by
  let Φ : HomotopyGroup (Fin (n + 1)) X x ≃* HomotopyGroup (Fin (n + 1)) Y y :=
    homotopyGroupBasedHomeomorphMulEquiv e x y he
  have hfun : sphereHurewicz n y c =
      integralSingularHomologyMap (n + 1) (⟨e, e.continuous⟩ : C(X, Y)) ∘
        sphereHurewicz n x c ∘ Φ.symm := by
    funext a
    rw [Function.comp_apply, Function.comp_apply]
    have h1 := sphereHurewicz_homeomorph_apply n e he c (Φ.symm a)
    rwa [Φ.apply_symm_apply] at h1
  rw [hfun]
  exact (integralSingularHomologyHomotopyEquiv (n + 1) e.toHomotopyEquiv).bijective.comp
    (h.comp Φ.symm.bijective)

theorem hurewiczMultiplicative_transfer_of_homeomorph (n : ℕ) (e : X ≃ₜ Y) {x : X} {y : Y}
    (he : e x = y) (c : integralSingularHomology (n + 1) (liftedHomotopySphere.{u} n))
    (hm : ∀ a b : HomotopyGroup (Fin (n + 1)) X x,
      sphereHurewicz n x c (a * b) = sphereHurewicz n x c a + sphereHurewicz n x c b) :
    ∀ a b : HomotopyGroup (Fin (n + 1)) Y y,
      sphereHurewicz n y c (a * b) = sphereHurewicz n y c a + sphereHurewicz n y c b := by
  let Φ : HomotopyGroup (Fin (n + 1)) X x ≃* HomotopyGroup (Fin (n + 1)) Y y :=
    homotopyGroupBasedHomeomorphMulEquiv e x y he
  have hnat : ∀ a : HomotopyGroup (Fin (n + 1)) X x,
      sphereHurewicz n y c (Φ a) =
        integralSingularHomologyMap (n + 1) (⟨e, e.continuous⟩ : C(X, Y))
          (sphereHurewicz n x c a) :=
    fun a => sphereHurewicz_homeomorph_apply n e he c a
  intro a b
  obtain ⟨a', rfl⟩ := Φ.surjective a
  obtain ⟨b', rfl⟩ := Φ.surjective b
  rw [← map_mul Φ a' b', hnat (a' * b'), hm a' b', map_add, hnat a', hnat b']

theorem isSphereHurewiczIsomorphism_of_homeomorph (n : ℕ) (e : X ≃ₜ Y) {x : X} {y : Y}
    (he : e x = y) {c : integralSingularHomology (n + 1) (liftedHomotopySphere.{u} n)}
    (h : IsSphereHurewiczIsomorphism n X x c) :
    IsSphereHurewiczIsomorphism n Y y c :=
  ⟨bijective_sphereHurewicz_of_homeomorph n e he c h.1,
    hurewiczMultiplicative_transfer_of_homeomorph n e he c h.2⟩

theorem isSphereHurewiczIsomorphism_iff_of_homeomorph (n : ℕ) (e : X ≃ₜ Y) {x : X} {y : Y}
    (he : e x = y) (c : integralSingularHomology (n + 1) (liftedHomotopySphere.{u} n)) :
    IsSphereHurewiczIsomorphism n X x c ↔ IsSphereHurewiczIsomorphism n Y y c := by
  constructor
  · intro h
    exact isSphereHurewiczIsomorphism_of_homeomorph n e he h
  · intro h
    have he' : e.symm y = x := by rw [← he, Homeomorph.symm_apply_apply]
    exact isSphereHurewiczIsomorphism_of_homeomorph n e.symm he' h

theorem hurewiczTwoMultiplicative_iff_of_homeomorph (e : X ≃ₜ Y) :
    HurewiczTwoMultiplicative X ↔ HurewiczTwoMultiplicative Y := by
  constructor
  · intro h y c hc
    exact hurewiczMultiplicative_transfer_of_homeomorph 1 e (e.apply_symm_apply y) c
      (h (e.symm y) c hc)
  · intro h x c hc
    exact hurewiczMultiplicative_transfer_of_homeomorph 1 e.symm (e.symm_apply_apply x) c
      (h (e x) c hc)

theorem hurewiczThreeMultiplicative_iff_of_homeomorph (e : X ≃ₜ Y) :
    HurewiczThreeMultiplicative X ↔ HurewiczThreeMultiplicative Y := by
  constructor
  · intro h y hy c hc
    let : Subsingleton (HomotopyGroup (Fin 2) Y y) := hy
    have hsub : Subsingleton (HomotopyGroup (Fin 2) X (e.symm y)) :=
      (homotopyGroupBasedHomeomorphMulEquiv (N := Fin 2) e (e.symm y) y
        (e.apply_symm_apply y)).injective.subsingleton
    exact hurewiczMultiplicative_transfer_of_homeomorph 2 e (e.apply_symm_apply y) c
      (h (e.symm y) hsub c hc)
  · intro h x hx c hc
    let : Subsingleton (HomotopyGroup (Fin 2) X x) := hx
    have hsub : Subsingleton (HomotopyGroup (Fin 2) Y (e x)) :=
      (homotopyGroupBasedHomeomorphMulEquiv (N := Fin 2) e x (e x) rfl).surjective.subsingleton
    exact hurewiczMultiplicative_transfer_of_homeomorph 2 e.symm (e.symm_apply_apply x) c
      (h (e x) hsub c hc)

theorem hurewiczLowDegreeHypothesis_iff_of_homeomorph (e : X ≃ₜ Y) :
    HurewiczLowDegreeHypothesis X ↔ HurewiczLowDegreeHypothesis Y := by
  constructor
  · refine fun h => ⟨fun y => ?_, fun y hy => ?_⟩
    · exact isSphereHurewiczIsomorphism_of_homeomorph 1 e (e.apply_symm_apply y) (h.1 (e.symm y))
    · let : Subsingleton (HomotopyGroup (Fin 2) Y y) := hy
      have hsub : Subsingleton (HomotopyGroup (Fin 2) X (e.symm y)) :=
        (homotopyGroupBasedHomeomorphMulEquiv (N := Fin 2) e (e.symm y) y
          (e.apply_symm_apply y)).injective.subsingleton
      exact isSphereHurewiczIsomorphism_of_homeomorph 2 e (e.apply_symm_apply y)
        (h.2 (e.symm y) hsub)
  · refine fun h => ⟨fun x => ?_, fun x hx => ?_⟩
    · exact isSphereHurewiczIsomorphism_of_homeomorph 1 e.symm (e.symm_apply_apply x)
        (h.1 (e x))
    · let : Subsingleton (HomotopyGroup (Fin 2) X x) := hx
      have hsub : Subsingleton (HomotopyGroup (Fin 2) Y (e x)) :=
        (homotopyGroupBasedHomeomorphMulEquiv (N := Fin 2) e x (e x) rfl).surjective.subsingleton
      exact isSphereHurewiczIsomorphism_of_homeomorph 2 e.symm (e.symm_apply_apply x)
        (h.2 (e x) hsub)

theorem sphereHurewiczTwoCanonical_iff_of_homeomorph [SimplyConnectedSpace X]
    [SimplyConnectedSpace Y] (e : X ≃ₜ Y) :
    SphereHurewiczTwoCanonical X ↔ SphereHurewiczTwoCanonical Y := by
  constructor
  · intro h y
    exact isSphereHurewiczIsomorphism_of_homeomorph 1 e (e.apply_symm_apply y) (h (e.symm y))
  · intro h x
    exact isSphereHurewiczIsomorphism_of_homeomorph 1 e.symm (e.symm_apply_apply x) (h (e x))

theorem sphereHurewiczThreeCanonical_iff_of_homeomorph [SimplyConnectedSpace X]
    [SimplyConnectedSpace Y] (e : X ≃ₜ Y) :
    SphereHurewiczThreeCanonical X ↔ SphereHurewiczThreeCanonical Y := by
  constructor
  · intro h y hy
    let : Subsingleton (HomotopyGroup (Fin 2) Y y) := hy
    have hsub : Subsingleton (HomotopyGroup (Fin 2) X (e.symm y)) :=
      (homotopyGroupBasedHomeomorphMulEquiv (N := Fin 2) e (e.symm y) y
        (e.apply_symm_apply y)).injective.subsingleton
    exact isSphereHurewiczIsomorphism_of_homeomorph 2 e (e.apply_symm_apply y)
      (h (e.symm y) hsub)
  · intro h x hx
    let : Subsingleton (HomotopyGroup (Fin 2) X x) := hx
    have hsub : Subsingleton (HomotopyGroup (Fin 2) Y (e x)) :=
      (homotopyGroupBasedHomeomorphMulEquiv (N := Fin 2) e x (e x) rfl).surjective.subsingleton
    exact isSphereHurewiczIsomorphism_of_homeomorph 2 e.symm (e.symm_apply_apply x)
      (h (e x) hsub)

theorem hurewiczTwoBijective_iff_of_homeomorph [SimplyConnectedSpace X] [SimplyConnectedSpace Y]
    (e : X ≃ₜ Y) : HurewiczTwoBijective X ↔ HurewiczTwoBijective Y := by
  constructor
  · intro h y
    exact bijective_sphereHurewicz_of_homeomorph 1 e (e.apply_symm_apply y)
      (integralLiftedSphereGenerator.{u} 1) (h (e.symm y))
  · intro h x
    exact bijective_sphereHurewicz_of_homeomorph 1 e.symm (e.symm_apply_apply x)
      (integralLiftedSphereGenerator.{u} 1) (h (e x))

theorem hurewiczThreeBijective_iff_of_homeomorph [SimplyConnectedSpace X] [SimplyConnectedSpace Y]
    (e : X ≃ₜ Y) : HurewiczThreeBijective X ↔ HurewiczThreeBijective Y := by
  constructor
  · intro h y hy
    let : Subsingleton (HomotopyGroup (Fin 2) Y y) := hy
    have hsub : Subsingleton (HomotopyGroup (Fin 2) X (e.symm y)) :=
      (homotopyGroupBasedHomeomorphMulEquiv (N := Fin 2) e (e.symm y) y
        (e.apply_symm_apply y)).injective.subsingleton
    exact bijective_sphereHurewicz_of_homeomorph 2 e (e.apply_symm_apply y)
      (integralLiftedSphereGenerator.{u} 2) (h (e.symm y) hsub)
  · intro h x hx
    let : Subsingleton (HomotopyGroup (Fin 2) X x) := hx
    have hsub : Subsingleton (HomotopyGroup (Fin 2) Y (e x)) :=
      (homotopyGroupBasedHomeomorphMulEquiv (N := Fin 2) e x (e x) rfl).surjective.subsingleton
    exact bijective_sphereHurewicz_of_homeomorph 2 e.symm (e.symm_apply_apply x)
      (integralLiftedSphereGenerator.{u} 2) (h (e x) hsub)

theorem hurewicz_two_isomorphism_of_homeomorph (e : X ≃ₜ Y)
    (h : HurewiczLowDegreeHypothesis X) (y : Y)
    (c : integralSingularHomology 2 (liftedHomotopySphere.{u} 1))
    (hc : IsSphereHomologyGenerator 1 c) :
    Function.Bijective (sphereHurewicz 1 y c) ∧
      ∀ a b : HomotopyGroup (Fin 2) Y y,
        sphereHurewicz 1 y c (a * b) = sphereHurewicz 1 y c a + sphereHurewicz 1 y c b :=
  isSphereHurewiczIsomorphism_of_homeomorph 1 e (e.apply_symm_apply y)
    (hurewicz_two_isomorphism_of_hypothesis h (e.symm y) c hc)

theorem hurewicz_three_isomorphism_of_homeomorph (e : X ≃ₜ Y)
    (h : HurewiczLowDegreeHypothesis X) (y : Y)
    (hπ₂ : Subsingleton (HomotopyGroup (Fin 2) Y y))
    (c : integralSingularHomology 3 (liftedHomotopySphere.{u} 2))
    (hc : IsSphereHomologyGenerator 2 c) :
    Function.Bijective (sphereHurewicz 2 y c) ∧
      ∀ a b : HomotopyGroup (Fin 3) Y y,
        sphereHurewicz 2 y c (a * b) = sphereHurewicz 2 y c a + sphereHurewicz 2 y c b := by
  let : Subsingleton (HomotopyGroup (Fin 2) Y y) := hπ₂
  have hsub : Subsingleton (HomotopyGroup (Fin 2) X (e.symm y)) :=
    (homotopyGroupBasedHomeomorphMulEquiv (N := Fin 2) e (e.symm y) y
      (e.apply_symm_apply y)).injective.subsingleton
  exact isSphereHurewiczIsomorphism_of_homeomorph 2 e (e.apply_symm_apply y)
    (hurewicz_three_isomorphism_of_hypothesis h (e.symm y) hsub c hc)

theorem hurewiczLowDegreeFrontier_iff_of_homeomorph [SimplyConnectedSpace X]
    [SimplyConnectedSpace Y] (e : X ≃ₜ Y) :
    HurewiczLowDegreeFrontier X ↔ HurewiczLowDegreeFrontier Y :=
  (hurewiczLowDegreeHypothesis_iff_frontier (X := X)).symm.trans
    ((hurewiczLowDegreeHypothesis_iff_of_homeomorph e).trans
      (hurewiczLowDegreeHypothesis_iff_frontier (X := Y)))

end DifferentialGeometry.Topology
