import DifferentialGeometry.Topology.Sphere.SphereSuspension

namespace DifferentialGeometry.Topology

open Set Metric _root_.Topology

variable {m : ℕ} {X : Type*} [TopologicalSpace X]

theorem exists_sphere_collapse_of_height_collar (t : X → ℝ) (ht : Continuous t)
    (Φ : (sphere (0 : EuclideanSpace ℝ (Fin (m + 1))) 1 × SuspensionInterval) ≃ₜ
      {x : X // t x ∈ Icc (-1 : ℝ) 1})
    (hΦ : ∀ p, t (Φ p).val = (p.2 : ℝ)) :
    ∃ F : C(X, sphere (0 : EuclideanSpace ℝ (Fin (m + 2))) 1),
      Function.Surjective F ∧
      (∀ x y, F x = F y ↔ x = y ∨
        (t x ≤ -1 ∧ t y ≤ -1) ∨ (1 ≤ t x ∧ 1 ≤ t y)) ∧
      (∀ x, (F x : EuclideanSpace ℝ (Fin (m + 2))) (Fin.last (m + 1)) ≤ 0 ↔ t x ≤ 0) ∧
      (∀ x, 0 ≤ (F x : EuclideanSpace ℝ (Fin (m + 2))) (Fin.last (m + 1)) ↔ 0 ≤ t x) := by
  classical
  let C : Set X := {x | t x ∈ Icc (-1 : ℝ) 1}
  let A : Set X := {x | t x ≤ -1}
  let B : Set X := {x | 1 ≤ t x}
  let F : X → sphere (0 : EuclideanSpace ℝ (Fin (m + 2))) 1 := fun x =>
    if hx : x ∈ C then sphereSuspension m (Φ.symm ⟨x, hx⟩)
    else if t x < -1 then sphereSouthPole m else sphereNorthPole m
  have hheight (x : C) : ((Φ.symm x).2 : ℝ) = t x := by
    simpa only [Homeomorph.apply_symm_apply] using (hΦ (Φ.symm x)).symm
  have hFC (x : X) (hx : x ∈ C) : F x = sphereSuspension m (Φ.symm ⟨x, hx⟩) :=
    dite_eq_left hx
  have hFA (x : X) (hx : t x ≤ -1) : F x = sphereSouthPole m := by
    by_cases hc : x ∈ C
    · rw [hFC x hc, sphereSuspension_eq_south_iff, hheight]
      exact le_antisymm hx hc.1
    · have hxlt : t x < -1 := lt_of_le_of_ne hx (by
        intro heq
        apply hc
        change t x ∈ Icc (-1 : ℝ) 1
        rw [heq]
        norm_num)
      simp only [F, dite_eq_right hc, ite_eq_left hxlt]
  have hFB (x : X) (hx : 1 ≤ t x) : F x = sphereNorthPole m := by
    by_cases hc : x ∈ C
    · rw [hFC x hc, sphereSuspension_eq_north_iff, hheight]
      exact le_antisymm hc.2 hx
    · have hxnot : ¬t x < -1 := by linarith
      simp only [F, dite_eq_right hc, ite_eq_right hxnot]
  have hFAiff (x : X) : F x = sphereSouthPole m ↔ t x ≤ -1 := by
    refine ⟨?_, hFA x⟩
    intro hx
    by_cases hc : x ∈ C
    · rw [hFC x hc, sphereSuspension_eq_south_iff, hheight] at hx
      exact hx.le
    · by_cases hxa : t x < -1
      · exact hxa.le
      · have hb : 1 ≤ t x := by
          by_contra hb
          exact hc ⟨le_of_not_gt hxa, le_of_lt (lt_of_not_ge hb)⟩
        exact False.elim (sphereSouthPole_ne_northPole m (hx.symm.trans (hFB x hb)))
  have hFBiff (x : X) : F x = sphereNorthPole m ↔ 1 ≤ t x := by
    refine ⟨?_, hFB x⟩
    intro hx
    by_cases hc : x ∈ C
    · rw [hFC x hc, sphereSuspension_eq_north_iff, hheight] at hx
      exact hx.ge
    · by_cases hxb : 1 ≤ t x
      · exact hxb
      · have ha : t x ≤ -1 := by
          by_contra ha
          exact hc ⟨(lt_of_not_ge ha).le, (lt_of_not_ge hxb).le⟩
        exact False.elim (sphereSouthPole_ne_northPole m ((hFA x ha).symm.trans hx))
  have hcover : (A ∪ C) ∪ B = univ := by
    ext x
    simp only [mem_union, mem_univ, iff_true]
    rcases le_total (t x) (-1) with ha | ha
    · exact Or.inl (Or.inl ha)
    · rcases le_total (t x) 1 with hb | hb
      · exact Or.inl (Or.inr ⟨ha, hb⟩)
      · exact Or.inr hb
  have hcont : Continuous F := by
    rw [← continuousOn_univ, ← hcover]
    apply ContinuousOn.union_of_isClosed
      (ContinuousOn.union_of_isClosed ?_ ?_
        (isClosed_Iic.preimage ht) (isClosed_Icc.preimage ht)) ?_
      ((isClosed_Iic.preimage ht).union (isClosed_Icc.preimage ht)) (isClosed_Ici.preimage ht)
    · exact continuousOn_const.congr (fun x hx => hFA x hx)
    · rw [continuousOn_iff_continuous_domRestrict]
      change Continuous (C.domRestrict F)
      have heq : C.domRestrict F = sphereSuspension m ∘ Φ.symm := by
        funext x
        exact hFC x x.2
      rw [heq]
      exact (continuous_sphereSuspension m).comp Φ.symm.continuous
    · exact continuousOn_const.congr (fun x hx => hFB x hx)
  have hFΦ (p : sphere (0 : EuclideanSpace ℝ (Fin (m + 1))) 1 × SuspensionInterval) :
      F (Φ p).val = sphereSuspension m p := by
    rw [hFC _ (Φ p).2]
    exact congrArg (sphereSuspension m) (Φ.symm_apply_apply p)
  have hsurj : Function.Surjective F := by
    intro z
    obtain ⟨p, rfl⟩ := sphereSuspension_surjective m z
    exact ⟨(Φ p).val, hFΦ p⟩
  have hfiber : ∀ x y, F x = F y ↔ x = y ∨
      (t x ≤ -1 ∧ t y ≤ -1) ∨ (1 ≤ t x ∧ 1 ≤ t y) := by
    intro x y
    constructor
    · intro hxy
      by_cases hxA : t x ≤ -1
      · exact Or.inr (Or.inl ⟨hxA, (hFAiff y).mp (hxy.symm.trans (hFA x hxA))⟩)
      by_cases hxB : 1 ≤ t x
      · exact Or.inr (Or.inr ⟨hxB, (hFBiff y).mp (hxy.symm.trans (hFB x hxB))⟩)
      have hyA : ¬t y ≤ -1 := fun hy => hxA ((hFAiff x).mp (hxy.trans (hFA y hy)))
      have hyB : ¬1 ≤ t y := fun hy => hxB ((hFBiff x).mp (hxy.trans (hFB y hy)))
      have hxC : x ∈ C := ⟨(lt_of_not_ge hxA).le, (lt_of_not_ge hxB).le⟩
      have hyC : y ∈ C := ⟨(lt_of_not_ge hyA).le, (lt_of_not_ge hyB).le⟩
      rw [hFC x hxC, hFC y hyC] at hxy
      have heq := (sphereSuspension_eq_iff (Φ.symm ⟨x, hxC⟩).1
        (Φ.symm ⟨y, hyC⟩).1 (Φ.symm ⟨x, hxC⟩).2 (Φ.symm ⟨y, hyC⟩).2).mp hxy
      have hs : (Φ.symm ⟨x, hxC⟩).1 = (Φ.symm ⟨y, hyC⟩).1 := by
        rcases heq.2 with hs | hs | hs
        · exact hs
        · exact (hxA (by simpa only [hheight] using hs.le)).elim
        · exact (hxB (by simpa only [hheight] using hs.ge)).elim
      exact Or.inl (congrArg Subtype.val (Φ.symm.injective (Prod.ext hs heq.1)))
    · rintro (rfl | ⟨hx, hy⟩ | ⟨hx, hy⟩)
      · rfl
      · rw [hFA x hx, hFA y hy]
      · rw [hFB x hx, hFB y hy]
  have hsign (x : X) :
      ((F x : EuclideanSpace ℝ (Fin (m + 2))) (Fin.last (m + 1)) ≤ 0 ↔ t x ≤ 0) ∧
      (0 ≤ (F x : EuclideanSpace ℝ (Fin (m + 2))) (Fin.last (m + 1)) ↔ 0 ≤ t x) := by
    by_cases hx : x ∈ C
    · rw [hFC x hx, sphereSuspension_last, hheight]
      exact ⟨Iff.rfl, Iff.rfl⟩
    · by_cases hxA : t x ≤ -1
      · rw [hFA x hxA]
        simp only [sphereSouthPole, euclidSnoc_apply_last]
        constructor <;> constructor <;> intro hh <;> linarith
      · have hxB : 1 ≤ t x := by
          by_contra hh
          exact hx ⟨(lt_of_not_ge hxA).le, (lt_of_not_ge hh).le⟩
        rw [hFB x hxB]
        simp only [sphereNorthPole, euclidSnoc_apply_last]
        constructor <;> constructor <;> intro hh <;> linarith
  exact ⟨⟨F, hcont⟩, hsurj, hfiber, fun x => (hsign x).1, fun x => (hsign x).2⟩

end DifferentialGeometry.Topology
