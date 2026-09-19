/-
Copyright (c) 2026 Yuan Liao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuan Liao
-/
import DifferentialGeometry.Topology.PiecewiseLinear.CylinderEndMap
import DifferentialGeometry.Topology.LoopSpace.CircleLiftOrientation

/-! Product homeomorphisms for cylindrical diagrams with identical ends. -/

open Set

namespace DifferentialGeometry.Topology.PiecewiseLinear

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

namespace IsCylindricalDiagram

variable {f : E × ℝ → F} {P : Set E} {S : Set F}

theorem eq_iff_fst_eq_and_circle_eq (hf : IsCylindricalDiagram f P S)
    (hends : ∀ x ∈ P, f (x, 0) = f (x, 1)) {x y : E × ℝ}
    (hx : x ∈ P ×ˢ Icc (0 : ℝ) 1) (hy : y ∈ P ×ˢ Icc (0 : ℝ) 1) :
    f x = f y ↔ x.1 = y.1 ∧ (x.2 : loopCircle) = (y.2 : loopCircle) := by
  rcases x with ⟨x, t⟩
  rcases y with ⟨y, s⟩
  rcases hx with ⟨hx, ht0, ht1⟩
  rcases hy with ⟨hy, hs0, hs1⟩
  constructor
  · intro heq
    rcases hf.eq_or_endpoints (x, t) ⟨hx, ht0, ht1⟩ (y, s) ⟨hy, hs0, hs1⟩ heq with
      hxy | hend | hend
    · exact ⟨congrArg Prod.fst hxy, congrArg (fun z : E × ℝ => (z.2 : loopCircle)) hxy⟩
    · change t = 0 ∧ s = 1 at hend
      refine ⟨hf.eq_of_eq_top hx hy ?_, ?_⟩
      · rw [hend.1, hend.2, hends x hx] at heq
        exact heq
      · change (t : loopCircle) = (s : loopCircle)
        rw [hend.1, hend.2, AddCircle.coe_zero, AddCircle.coe_period]
    · change t = 1 ∧ s = 0 at hend
      refine ⟨hf.eq_of_eq_top hx hy ?_, ?_⟩
      · rw [hend.1, hend.2, hends y hy] at heq
        exact heq
      · change (t : loopCircle) = (s : loopCircle)
        rw [hend.1, hend.2, AddCircle.coe_zero, AddCircle.coe_period]
  · rintro ⟨hxy, hts⟩
    change x = y at hxy
    subst y
    obtain ⟨n, hn⟩ := (loopCircle_coe_eq_coe_iff t s).mp hts
    have hnl : (-1 : ℝ) ≤ (n : ℝ) := by linarith
    have hnu : (n : ℝ) ≤ 1 := by linarith
    have hnl' : (-1 : ℤ) ≤ n := by exact_mod_cast hnl
    have hnu' : n ≤ 1 := by exact_mod_cast hnu
    have hn_cases : n = -1 ∨ n = 0 ∨ n = 1 := by omega
    rcases hn_cases with rfl | rfl | rfl
    · have ht : t = 0 := by norm_num at hn; linarith
      have hs : s = 1 := by norm_num at hn; linarith
      simpa only [ht, hs] using hends x hx
    · have hts' : t = s := by norm_num at hn; linarith
      simp only [hts']
    · have ht : t = 1 := by norm_num at hn; linarith
      have hs : s = 0 := by norm_num at hn; linarith
      simpa only [ht, hs] using (hends x hx).symm

theorem exists_homeomorph_prod_circle_of_eq_ends [FiniteDimensional ℝ E]
    (hf : IsCylindricalDiagram f P S) (hP : IsCompact P)
    (hends : ∀ x ∈ P, f (x, 0) = f (x, 1)) :
    ∃ e : S ≃ₜ (P × loopCircle), ∀ (x : P) (t : Icc (0 : ℝ) 1),
      (e.symm (x, (t : ℝ)) : F) = f (x, t) := by
  let _ : CompactSpace P := isCompact_iff_compactSpace.mp hP
  let X := P × Icc (0 : ℝ) 1
  let q : C(X, P × loopCircle) := {
    toFun := fun z => (z.1, (z.2 : ℝ))
    continuous_toFun := continuous_fst.prodMk
      ((AddCircle.continuous_mk' (1 : ℝ)).comp (continuous_subtype_val.comp continuous_snd)) }
  let r : C(X, S) := {
    toFun := fun z => ⟨f (z.1, z.2), hf.image_eq ▸
      ⟨((z.1 : E), (z.2 : ℝ)), ⟨z.1.property, z.2.property⟩, rfl⟩⟩
    continuous_toFun := (hf.isPiecewiseAffineOn.continuousOn.comp_continuous
      ((continuous_subtype_val.comp continuous_fst).prodMk
        (continuous_subtype_val.comp continuous_snd))
      (fun z => ⟨z.1.property, z.2.property⟩)).subtype_mk _ }
  have hqs : Function.Surjective q := by
    intro y
    obtain ⟨t, ht, hty⟩ := exists_lift_mem_Ico y.2
    exact ⟨(y.1, ⟨t, ht.1, ht.2.le⟩), Prod.ext rfl hty⟩
  have hrs : Function.Surjective r := by
    intro y
    have hy : y.val ∈ f '' (P ×ˢ Icc (0 : ℝ) 1) := by
      rw [hf.image_eq]
      exact y.property
    obtain ⟨z, hz, hzy⟩ := hy
    exact ⟨(⟨z.1, hz.1⟩, ⟨z.2, hz.2⟩), Subtype.ext hzy⟩
  have hfib (x y : X) : r x = r y ↔ q x = q y := by
    have h := hf.eq_iff_fst_eq_and_circle_eq hends
      (x := ((x.1 : E), (x.2 : ℝ))) (y := ((y.1 : E), (y.2 : ℝ)))
      ⟨x.1.property, x.2.property⟩ ⟨y.1.property, y.2.property⟩
    constructor
    · intro hxy
      obtain ⟨hfirst, hsecond⟩ := h.mp (congrArg Subtype.val hxy)
      exact Prod.ext (Subtype.ext hfirst) hsecond
    · intro hxy
      apply Subtype.ext
      exact h.mpr ⟨congrArg (fun z : P × loopCircle => (z.1 : E)) hxy,
        congrArg (fun z : P × loopCircle => z.2) hxy⟩
  have hq : Topology.IsQuotientMap q :=
    Topology.IsQuotientMap.of_surjective_continuous hqs q.continuous
  have hfactor : Function.FactorsThrough r q := fun _ _ hxy => (hfib _ _).mpr hxy
  let g := hq.lift r hfactor
  have hgq (x : X) : g (q x) = r x := DFunLike.congr_fun (hq.lift_comp r hfactor) x
  have hgb : Function.Bijective g := by
    constructor
    · intro y z hyz
      obtain ⟨x, rfl⟩ := hqs y
      obtain ⟨w, rfl⟩ := hqs z
      apply (hfib x w).mp
      rwa [hgq, hgq] at hyz
    · intro y
      obtain ⟨x, hx⟩ := hrs y
      exact ⟨q x, (hgq x).trans hx⟩
  let e := Continuous.homeoOfEquivCompactToT2 (f := Equiv.ofBijective g hgb) g.continuous
  exact ⟨e.symm, fun x t => congrArg Subtype.val (hgq (x, t))⟩

end IsCylindricalDiagram

end DifferentialGeometry.Topology.PiecewiseLinear
