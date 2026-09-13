import DifferentialGeometry.Topology.Homology.SphereHurewicz
import DifferentialGeometry.Topology.Homology.SphereGenerator

noncomputable section

open ContinuousMap Metric

universe u

namespace DifferentialGeometry.Topology

variable {X : Type u} [TopologicalSpace X]

theorem freeSphereHomologyImage_const (n : ℕ)
    (c : integralSingularHomology (n + 1) (liftedHomotopySphere.{u} n)) (x : X) :
    freeSphereHomologyImage n c (ZerothHomotopy.mk (ContinuousMap.const _ x)) = 0 := by
  rw [freeSphereHomologyImage_mk, ContinuousMap.const_comp,
    integralSingularHomologyMap_const (n + 1) (by omega) x, LinearMap.zero_apply]

theorem surjective_sphereHurewicz_iff_forall_exists_map_eq [SimplyConnectedSpace X] (n : ℕ)
    (x : X) (c : integralSingularHomology (n + 1) (liftedHomotopySphere.{u} n)) :
    Function.Surjective (sphereHurewicz n x c) ↔
      ∀ y : integralSingularHomology (n + 1) X,
        ∃ f : C(sphere (0 : EuclideanSpace ℝ (Fin (n + 2))) 1, X),
          freeSphereHomologyImage n c (ZerothHomotopy.mk f) = y := by
  have hsurj : Function.Surjective (sphereHurewicz n x c) ↔
      Function.Surjective (freeSphereHomologyImage n c) :=
    Equiv.surjective_comp (homotopyGroupFreeSphereEquiv n x) (freeSphereHomologyImage n c)
  rw [hsurj]
  constructor
  · intro h y
    obtain ⟨a, ha⟩ := h y
    have hout : ZerothHomotopy.mk (Quotient.out a) = a := Quotient.out_eq a
    exact ⟨Quotient.out a, by rw [hout, ha]⟩
  · rintro h y
    obtain ⟨f, hf⟩ := h y
    exact ⟨ZerothHomotopy.mk f, hf⟩


theorem forall_sphereHurewicz_eq_zero_iff_forall_freeSphereHomologyImage_eq_zero
    [SimplyConnectedSpace X] (n : ℕ) (x : X)
    (c : integralSingularHomology (n + 1) (liftedHomotopySphere.{u} n)) :
    (∀ a : HomotopyGroup (Fin (n + 1)) X x, sphereHurewicz n x c a = 0 → a = 1) ↔
      ∀ f : C(sphere (0 : EuclideanSpace ℝ (Fin (n + 2))) 1, X),
        freeSphereHomologyImage n c (ZerothHomotopy.mk f) = 0 →
          ZerothHomotopy.mk f = ZerothHomotopy.mk (ContinuousMap.const _ x) := by
  constructor
  · intro h f hf
    obtain ⟨a, ha⟩ := homotopyGroupToFreeSphere_surjective n x (ZerothHomotopy.mk f)
    have hzero : sphereHurewicz n x c a = 0 := by
      change freeSphereHomologyImage n c (homotopyGroupToFreeSphere n x a) = 0
      rw [ha, hf]
    rw [← ha, h a hzero, homotopyGroupToFreeSphere_one]
  · intro h a ha
    have hfa : freeSphereHomologyImage n c (homotopyGroupToFreeSphere n x a) = 0 := by
      change sphereHurewicz n x c a = 0
      exact ha
    have hout : ZerothHomotopy.mk (Quotient.out (homotopyGroupToFreeSphere n x a)) =
        homotopyGroupToFreeSphere n x a := Quotient.out_eq _
    have hconst := h (Quotient.out (homotopyGroupToFreeSphere n x a)) (by rw [hout]; exact hfa)
    have heq : homotopyGroupToFreeSphere n x a = homotopyGroupToFreeSphere n x 1 := by
      rw [← hout, hconst, homotopyGroupToFreeSphere_one]
    exact homotopyGroupToFreeSphere_injective n x heq

theorem injective_sphereHurewicz_iff_forall_eq_one_of_additive (n : ℕ) (x : X)
    (c : integralSingularHomology (n + 1) (liftedHomotopySphere.{u} n))
    (hmul : ∀ a b : HomotopyGroup (Fin (n + 1)) X x,
      sphereHurewicz n x c (a * b) =
        sphereHurewicz n x c a + sphereHurewicz n x c b) :
    Function.Injective (sphereHurewicz n x c) ↔
      ∀ a : HomotopyGroup (Fin (n + 1)) X x, sphereHurewicz n x c a = 0 → a = 1 := by
  constructor
  · intro hinj a ha
    refine hinj ?_
    rw [ha, sphereHurewicz_one]
  · intro hk a b hab
    have hinv : sphereHurewicz n x c b⁻¹ = -sphereHurewicz n x c b := by
      have h := hmul b b⁻¹
      rw [mul_inv_cancel, sphereHurewicz_one] at h
      exact eq_neg_of_add_eq_zero_right h.symm
    have hzero : sphereHurewicz n x c (a * b⁻¹) = 0 := by
      rw [hmul, hab, hinv, add_neg_cancel]
    exact mul_inv_eq_one.mp (hk _ hzero)

theorem bijective_sphereHurewicz_iff_forall_exists_map_eq_and_nullhomotopic_of_additive
    [SimplyConnectedSpace X] (n : ℕ) (x : X)
    (c : integralSingularHomology (n + 1) (liftedHomotopySphere.{u} n))
    (hmul : ∀ a b : HomotopyGroup (Fin (n + 1)) X x,
      sphereHurewicz n x c (a * b) =
        sphereHurewicz n x c a + sphereHurewicz n x c b) :
    Function.Bijective (sphereHurewicz n x c) ↔
      (∀ y : integralSingularHomology (n + 1) X,
        ∃ f : C(sphere (0 : EuclideanSpace ℝ (Fin (n + 2))) 1, X),
          freeSphereHomologyImage n c (ZerothHomotopy.mk f) = y) ∧
      (∀ f : C(sphere (0 : EuclideanSpace ℝ (Fin (n + 2))) 1, X),
        freeSphereHomologyImage n c (ZerothHomotopy.mk f) = 0 →
          ZerothHomotopy.mk f = ZerothHomotopy.mk (ContinuousMap.const _ x)) := by
  constructor
  · intro h
    exact ⟨(surjective_sphereHurewicz_iff_forall_exists_map_eq n x c).mp h.2,
      (forall_sphereHurewicz_eq_zero_iff_forall_freeSphereHomologyImage_eq_zero n x c).mp
        ((injective_sphereHurewicz_iff_forall_eq_one_of_additive n x c hmul).mp h.1)⟩
  · rintro ⟨hs, hk⟩
    exact ⟨(injective_sphereHurewicz_iff_forall_eq_one_of_additive n x c hmul).mpr
      ((forall_sphereHurewicz_eq_zero_iff_forall_freeSphereHomologyImage_eq_zero n x c).mpr hk),
      (surjective_sphereHurewicz_iff_forall_exists_map_eq n x c).mpr hs⟩

theorem bijective_sphereHurewicz_iff_bijective_integralLiftedSphereGenerator
    [SimplyConnectedSpace X] (n : ℕ) (x : X)
    (c : integralSingularHomology (n + 1) (liftedHomotopySphere.{u} n))
    (hc : IsSphereHomologyGenerator n c) :
    Function.Bijective (sphereHurewicz n x c) ↔
      Function.Bijective (sphereHurewicz n x (integralLiftedSphereGenerator.{u} n)) := by
  rcases (isSphereHomologyGenerator_iff_eq_or_eq_neg_integralLiftedSphereGenerator n c).mp hc
    with rfl | hneg
  · exact Iff.rfl
  · rw [hneg]
    have hneg' : sphereHurewicz n x (-integralLiftedSphereGenerator n) =
        fun a => -sphereHurewicz n x (integralLiftedSphereGenerator n) a := by
      funext a
      simpa using sphereHurewicz_zsmul n (-1) x (integralLiftedSphereGenerator n) a
    rw [hneg']
    exact Equiv.comp_bijective _ (Equiv.neg _)

theorem sphereHurewicz_zpow_of_additive (n : ℕ) (x : X)
    (c : integralSingularHomology (n + 1) (liftedHomotopySphere.{u} n))
    (hmul : ∀ a b : HomotopyGroup (Fin (n + 1)) X x,
      sphereHurewicz n x c (a * b) =
        sphereHurewicz n x c a + sphereHurewicz n x c b)
    (a : HomotopyGroup (Fin (n + 1)) X x) (k : ℤ) :
    sphereHurewicz n x c (a ^ k) = k • sphereHurewicz n x c a := by
  have hinv : ∀ b : HomotopyGroup (Fin (n + 1)) X x,
      sphereHurewicz n x c b⁻¹ = -sphereHurewicz n x c b := by
    intro b
    have h := hmul b b⁻¹
    rw [mul_inv_cancel, sphereHurewicz_one] at h
    exact eq_neg_of_add_eq_zero_right h.symm
  have hnat : ∀ m : ℕ,
      sphereHurewicz n x c (a ^ m) = (m : ℤ) • sphereHurewicz n x c a := by
    intro m
    induction m with
    | zero => rw [pow_zero, sphereHurewicz_one, Nat.cast_zero, zero_zsmul]
    | succ m ih => rw [pow_succ, hmul, ih, Nat.cast_succ, add_zsmul, one_zsmul]
  obtain ⟨m, hm | hm⟩ := Int.eq_nat_or_neg k
  · rw [hm, zpow_natCast, hnat m]
  · rw [hm, zpow_neg, zpow_natCast, hinv (a ^ m), hnat m, neg_zsmul]


private def sphereHurewiczRange (n : ℕ) (x : X)
    (c : integralSingularHomology (n + 1) (liftedHomotopySphere.{u} n))
    (hmul : ∀ a b : HomotopyGroup (Fin (n + 1)) X x,
      sphereHurewicz n x c (a * b) =
        sphereHurewicz n x c a + sphereHurewicz n x c b) :
    AddSubgroup (integralSingularHomology (n + 1) X) where
  carrier := Set.range (sphereHurewicz n x c)
  add_mem' := by
    rintro _ _ ⟨a, rfl⟩ ⟨b, rfl⟩
    exact ⟨a * b, hmul a b⟩
  zero_mem' := ⟨1, sphereHurewicz_one n x c⟩
  neg_mem' := by
    rintro _ ⟨a, rfl⟩
    refine ⟨a⁻¹, ?_⟩
    have h := hmul a a⁻¹
    rw [mul_inv_cancel, sphereHurewicz_one] at h
    exact eq_neg_of_add_eq_zero_right h.symm

theorem surjective_sphereHurewicz_iff_closure_range_eq_top_of_additive [SimplyConnectedSpace X]
    (n : ℕ) (x : X) (c : integralSingularHomology (n + 1) (liftedHomotopySphere.{u} n))
    (hmul : ∀ a b : HomotopyGroup (Fin (n + 1)) X x,
      sphereHurewicz n x c (a * b) =
        sphereHurewicz n x c a + sphereHurewicz n x c b) :
    Function.Surjective (sphereHurewicz n x c) ↔
      AddSubgroup.closure (Set.range (fun f : C(sphere (0 : EuclideanSpace ℝ (Fin (n + 2))) 1,
        X) => freeSphereHomologyImage n c (ZerothHomotopy.mk f))) = ⊤ := by
  have hrange : Set.range (fun f : C(sphere (0 : EuclideanSpace ℝ (Fin (n + 2))) 1,
        X) => freeSphereHomologyImage n c (ZerothHomotopy.mk f)) =
      Set.range (sphereHurewicz n x c) := by
    refine Set.Subset.antisymm ?_ ?_
    · rintro _ ⟨f, rfl⟩
      obtain ⟨a, ha⟩ := homotopyGroupToFreeSphere_surjective n x (ZerothHomotopy.mk f)
      refine ⟨a, ?_⟩
      change freeSphereHomologyImage n c (homotopyGroupToFreeSphere n x a) =
        freeSphereHomologyImage n c (ZerothHomotopy.mk f)
      rw [ha]
    · rintro _ ⟨a, rfl⟩
      obtain ⟨f, hf⟩ : ∃ f, ZerothHomotopy.mk f = homotopyGroupToFreeSphere n x a :=
        ⟨Quotient.out _, Quotient.out_eq _⟩
      refine ⟨f, ?_⟩
      change freeSphereHomologyImage n c (ZerothHomotopy.mk f) =
        freeSphereHomologyImage n c (homotopyGroupToFreeSphere n x a)
      rw [hf]
  constructor
  · intro hsurj
    rw [hrange, Set.range_eq_univ.mpr hsurj]
    exact AddSubgroup.closure_univ
  · intro hcl y
    have htop : (⊤ : AddSubgroup (integralSingularHomology (n + 1) X)) =
        AddSubgroup.closure (Set.range (sphereHurewicz n x c)) := by
      rw [← hrange, ← hcl]
    have hy : y ∈ AddSubgroup.closure (Set.range (sphereHurewicz n x c)) := by
      rw [← htop]
      exact AddSubgroup.mem_top y
    exact (AddSubgroup.closure_le (sphereHurewiczRange n x c hmul)).mpr
      (by rintro _ ⟨a, rfl⟩; exact ⟨a, rfl⟩) hy


theorem exists_sphereHurewicz_eq_sum_zsmul_of_additive [SimplyConnectedSpace X]
    (n : ℕ) [Nontrivial (Fin (n + 1))] (x : X)
    (c : integralSingularHomology (n + 1) (liftedHomotopySphere.{u} n))
    (hmul : ∀ a b : HomotopyGroup (Fin (n + 1)) X x,
      sphereHurewicz n x c (a * b) =
        sphereHurewicz n x c a + sphereHurewicz n x c b)
    {ι : Type*} [Fintype ι]
    (f : ι → C(sphere (0 : EuclideanSpace ℝ (Fin (n + 2))) 1, X)) (k : ι → ℤ) :
    ∃ a : HomotopyGroup (Fin (n + 1)) X x,
      sphereHurewicz n x c a =
        ∑ i, k i • freeSphereHomologyImage n c (ZerothHomotopy.mk (f i)) := by
  classical
  choose a ha using fun i => homotopyGroupToFreeSphere_surjective n x (ZerothHomotopy.mk (f i))
  have hprod : ∀ (s : Finset ι),
      sphereHurewicz n x c (∏ i ∈ s, a i ^ k i) =
        ∑ i ∈ s, k i • sphereHurewicz n x c (a i) := by
    intro s
    induction s using Finset.induction_on with
    | empty => simp [sphereHurewicz_one]
    | insert i s hi ih =>
        rw [Finset.prod_insert hi, Finset.sum_insert hi, hmul,
          sphereHurewicz_zpow_of_additive n x c hmul (a i) (k i), ih]
  refine ⟨∏ i, a i ^ k i, ?_⟩
  rw [hprod Finset.univ]
  refine Finset.sum_congr rfl fun i _ => ?_
  have hi : sphereHurewicz n x c (a i) =
      freeSphereHomologyImage n c (ZerothHomotopy.mk (f i)) := by
    change freeSphereHomologyImage n c (homotopyGroupToFreeSphere n x (a i)) = _
    rw [ha i]
  rw [hi]

end DifferentialGeometry.Topology
