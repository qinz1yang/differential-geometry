/-
Copyright (c) 2026 Bennett Chow. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bennett Chow
-/
import DifferentialGeometry.Topology.PiecewiseLinear.CollarInwardMap
import DifferentialGeometry.Topology.PiecewiseLinear.PrismBoundary

/-! # Section34Pierced Ball Height Move -/

open Set Topology

namespace DifferentialGeometry.Topology.PiecewiseLinear

private noncomputable def piercingHeight (s a t : ℝ) : ℝ :=
  max (min t (max ((t - a) / 2) (2 * t - a)))
    (min (t + s) (max t (min (2 * t + a) ((t + a) / 2))))

noncomputable def piercingHeightMove {E : Type*} (g : E → ℝ) (a : ℝ)
    (x : E × ℝ) : E × ℝ := (x.1, piercingHeight (g x.1) a x.2)

private theorem piercingHeight_strictMono (s a : ℝ) : StrictMono (piercingHeight s a) := by
  intro t u htu
  exact max_lt_max
    (min_lt_min htu (max_lt_max (by linarith) (by linarith)))
    (min_lt_min (by linarith)
      (max_lt_max htu (min_lt_min (by linarith) (by linarith))))

private theorem piercingHeight_eq_self (s : ℝ) {a t : ℝ} (ht : t ≤ -a ∨ a ≤ t) :
    piercingHeight s a t = t := by
  have hL : min t (max ((t - a) / 2) (2 * t - a)) = t := by
    apply min_eq_left
    rcases ht with ht | ht
    · exact (by linarith : t ≤ (t - a) / 2).trans (le_max_left _ _)
    · exact (by linarith : t ≤ 2 * t - a).trans (le_max_right _ _)
  have hU : max t (min (2 * t + a) ((t + a) / 2)) = t := by
    apply max_eq_left
    rcases ht with ht | ht
    · exact (min_le_left _ _).trans (by linarith)
    · exact (min_le_right _ _).trans (by linarith)
  simp only [piercingHeight, hL, hU, max_eq_left (min_le_right (t + s) t)]

private theorem piercingHeight_zero {s a : ℝ} (ha : 0 ≤ a) (hs : |s| ≤ a / 2) :
    piercingHeight s a 0 = s := by
  obtain ⟨hlo, hhi⟩ := abs_le.mp hs
  have hL : min (0 : ℝ) (max ((0 - a) / 2) (2 * 0 - a)) = -a / 2 := by
    rw [max_eq_left (by linarith), min_eq_right (by linarith)]
    ring
  have hU : max (0 : ℝ) (min (2 * 0 + a) ((0 + a) / 2)) = a / 2 := by
    rw [min_eq_right (by linarith), max_eq_right (by linarith)]
    ring
  unfold piercingHeight
  rw [hL, hU, zero_add, min_eq_left hhi, max_eq_right (by linarith)]

theorem piercingHeightMove_strictMono {E : Type*} (g : E → ℝ) (a : ℝ) (x : E) :
    StrictMono (fun t => (piercingHeightMove g a (x, t)).2) :=
  piercingHeight_strictMono (g x) a

theorem piercingHeightMove_injective {E : Type*} (g : E → ℝ) (a : ℝ) :
    Function.Injective (piercingHeightMove g a) := by
  intro x y hxy
  have hfst : x.1 = y.1 := by
    simpa only [piercingHeightMove] using congrArg Prod.fst hxy
  apply Prod.ext hfst
  apply (piercingHeight_strictMono (g x.1) a).injective
  simpa only [piercingHeightMove, hfst] using congrArg Prod.snd hxy

theorem piercingHeightMove_eq_self {E : Type*} (g : E → ℝ) {a : ℝ} {x : E × ℝ}
    (hx : x.2 ≤ -a ∨ a ≤ x.2) : piercingHeightMove g a x = x :=
  Prod.ext rfl (piercingHeight_eq_self _ hx)

theorem piercingHeightMove_image_diff_slab {E : Type*} (g : E → ℝ) (a : ℝ)
    (S : Set (E × ℝ)) :
    piercingHeightMove g a '' S \ (univ ×ˢ Ioo (-a) a) = S \ (univ ×ˢ Ioo (-a) a) := by
  have hfixed (x : E × ℝ) (hx : x ∉ univ ×ˢ Ioo (-a) a) : piercingHeightMove g a x = x := by
    apply piercingHeightMove_eq_self
    by_cases hxl : x.2 ≤ -a
    · exact Or.inl hxl
    · exact Or.inr (le_of_not_gt fun hxu => hx ⟨mem_univ _, lt_of_not_ge hxl, hxu⟩)
  ext y
  constructor
  · rintro ⟨⟨x, hx, hxy⟩, hy⟩
    have heq : x = y := (piercingHeightMove_injective g a) (hxy.trans (hfixed y hy).symm)
    exact ⟨heq ▸ hx, hy⟩
  · rintro ⟨hy, hyslab⟩
    exact ⟨⟨y, hy, hfixed y hyslab⟩, hyslab⟩

theorem piercingHeightMove_apply_zero {E : Type*} {g : E → ℝ} {a : ℝ} (ha : 0 ≤ a)
    {x : E} (hx : |g x| ≤ a / 2) : piercingHeightMove g a (x, 0) = (x, g x) :=
  Prod.ext rfl (piercingHeight_zero ha hx)

theorem isPiecewiseAffineOn_piercingHeightMove {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [FiniteDimensional ℝ E] {g : E → ℝ}
    (hg : IsPiecewiseAffineOn g univ) (a : ℝ) :
    IsPiecewiseAffineOn (piercingHeightMove g a) univ := by
  have hfst : IsPiecewiseAffineOn (Prod.fst : E × ℝ → E) univ :=
    isPiecewiseAffineOn_of_affine (LinearMap.fst ℝ E ℝ).toAffineMap isOpen_univ
  have hsnd : IsPiecewiseAffineOn (Prod.snd : E × ℝ → ℝ) univ :=
    isPiecewiseAffineOn_of_affine (LinearMap.snd ℝ E ℝ).toAffineMap isOpen_univ
  have hgfst : IsPiecewiseAffineOn (fun x : E × ℝ => g x.1) univ := by
    simpa only [preimage_univ, inter_univ, Function.comp_def] using hg.comp hfst
  have haff (c d : ℝ) : IsPiecewiseAffineOn (fun x : E × ℝ => c * x.2 + d) univ :=
    isPiecewiseAffineOn_of_affine
      (c • (LinearMap.snd ℝ E ℝ).toAffineMap + AffineMap.const ℝ (E × ℝ) d) isOpen_univ
  have hlow : IsPiecewiseAffineOn (fun x : E × ℝ => (x.2 - a) / 2) univ := by
    convert haff (1 / 2) (-a / 2) using 1
    ext x
    ring
  have hhigh : IsPiecewiseAffineOn (fun x : E × ℝ => (x.2 + a) / 2) univ := by
    convert haff (1 / 2) (a / 2) using 1
    ext x
    ring
  have htwolow : IsPiecewiseAffineOn (fun x : E × ℝ => 2 * x.2 - a) univ := by
    simpa only [sub_eq_add_neg] using haff 2 (-a)
  exact hfst.prod_mk
    ((hsnd.min (hlow.max htwolow)).max
      ((hsnd.add hgfst).min (hsnd.max ((haff 2 a).min hhigh))))

private theorem piercingHeight_continuous (s a : ℝ) : Continuous (piercingHeight s a) := by
  unfold piercingHeight
  fun_prop

private theorem piercingHeight_image_Icc (s a l r : ℝ) (hlr : l ≤ r) :
    piercingHeight s a '' Icc l r = Icc (piercingHeight s a l) (piercingHeight s a r) :=
  (piercingHeight_continuous s a).continuousOn.image_Icc_of_monotoneOn hlr
    ((piercingHeight_strictMono s a).monotone.monotoneOn _)

theorem piercingHeightMove_image_lower {E : Type*} {g : E → ℝ} {a : ℝ}
    (ha : 0 < a) (ha1 : a ≤ 1) {P : Set E} (hg : ∀ x ∈ P, |g x| ≤ a / 2) :
    piercingHeightMove g a '' (P ×ˢ Icc (-1 : ℝ) 0) =
      {y : E × ℝ | y.1 ∈ P ∧ -1 ≤ y.2 ∧ y.2 ≤ g y.1} := by
  have himage (x : E) (hx : x ∈ P) :
      piercingHeight (g x) a '' Icc (-1 : ℝ) 0 = Icc (-1) (g x) := by
    rw [piercingHeight_image_Icc _ _ _ _ (by norm_num),
      piercingHeight_eq_self _ (Or.inl (by linarith)), piercingHeight_zero ha.le (hg x hx)]
  ext y
  constructor
  · rintro ⟨x, hx, rfl⟩
    exact ⟨hx.1, (himage x.1 hx.1).subset ⟨x.2, hx.2, rfl⟩⟩
  · rintro ⟨hy, hz⟩
    obtain ⟨t, ht, hty⟩ := (himage y.1 hy).superset hz
    exact ⟨(y.1, t), ⟨hy, ht⟩, Prod.ext rfl hty⟩

theorem piercingHeightMove_image_upper {E : Type*} {g : E → ℝ} {a : ℝ}
    (ha : 0 < a) (ha1 : a ≤ 1) {P : Set E} (hg : ∀ x ∈ P, |g x| ≤ a / 2) :
    piercingHeightMove g a '' (P ×ˢ Icc (0 : ℝ) 1) =
      {y : E × ℝ | y.1 ∈ P ∧ g y.1 ≤ y.2 ∧ y.2 ≤ 1} := by
  have himage (x : E) (hx : x ∈ P) :
      piercingHeight (g x) a '' Icc (0 : ℝ) 1 = Icc (g x) 1 := by
    rw [piercingHeight_image_Icc _ _ _ _ (by norm_num),
      piercingHeight_zero ha.le (hg x hx),
      piercingHeight_eq_self _ (Or.inr ha1)]
  ext y
  constructor
  · rintro ⟨x, hx, rfl⟩
    exact ⟨hx.1, (himage x.1 hx.1).subset ⟨x.2, hx.2, rfl⟩⟩
  · rintro ⟨hy, hz⟩
    obtain ⟨t, ht, hty⟩ := (himage y.1 hy).superset hz
    exact ⟨(y.1, t), ⟨hy, ht⟩, Prod.ext rfl hty⟩

theorem piercingHeightMove_image_prism {E : Type*} (g : E → ℝ) {a : ℝ}
    (ha1 : a ≤ 1) (P : Set E) :
    piercingHeightMove g a '' (P ×ˢ Icc (-1 : ℝ) 1) = P ×ˢ Icc (-1 : ℝ) 1 := by
  have himage (x : E) :
      piercingHeight (g x) a '' Icc (-1 : ℝ) 1 = Icc (-1 : ℝ) 1 := by
    rw [piercingHeight_image_Icc _ _ _ _ (by norm_num),
      piercingHeight_eq_self _ (Or.inl (by linarith)),
      piercingHeight_eq_self _ (Or.inr ha1)]
  ext y
  constructor
  · rintro ⟨x, hx, rfl⟩
    exact ⟨hx.1, (himage x.1).subset ⟨x.2, hx.2, rfl⟩⟩
  · rintro ⟨hy, hz⟩
    obtain ⟨t, ht, hty⟩ := (himage y.1).superset hz
    exact ⟨(y.1, t), ⟨hy, ht⟩, Prod.ext rfl hty⟩

theorem isPLHomeomorphOn_piercingHeightMove {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [FiniteDimensional ℝ E] {g : E → ℝ}
    (hg : IsPiecewiseAffineOn g univ) (a : ℝ) {P : Set E} (hP : IsPolyhedron P)
    (l r : ℝ) : IsPLHomeomorphOn (piercingHeightMove g a) (P ×ˢ Icc l r)
      (piercingHeightMove g a '' (P ×ˢ Icc l r)) := by
  have hprod : IsPolyhedron (P ×ˢ Icc l r) := hP.prod isHPolytope_Icc.isPolyhedron
  exact isPLHomeomorphOn_of_isPiecewiseAffineOn_of_bijOn hprod
    ((isPiecewiseAffineOn_piercingHeightMove hg a).mono_of_isPolyhedron hprod (subset_univ _))
    (piercingHeightMove_injective g a).injOn.bijOn_image

theorem isPLHomeomorphOn_piercingHeightMove_self {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [FiniteDimensional ℝ E] {g : E → ℝ}
    (hg : IsPiecewiseAffineOn g univ) {a : ℝ} (ha1 : a ≤ 1) {P : Set E}
    (hP : IsPolyhedron P) : IsPLHomeomorphOn (piercingHeightMove g a)
      (P ×ˢ Icc (-1 : ℝ) 1) (P ×ˢ Icc (-1 : ℝ) 1) := by
  have h := isPLHomeomorphOn_piercingHeightMove hg a hP (-1) 1
  rwa [piercingHeightMove_image_prism g ha1 P] at h

theorem exists_pierced_prism_ball_pair {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [FiniteDimensional ℝ E] {g : E → ℝ}
    (hg : IsPiecewiseAffineOn g univ) {a : ℝ} (ha : 0 < a) (ha1 : a ≤ 1)
    {P : Set E} (hP : IsPLBall 2 P) (hga : ∀ x ∈ P, |g x| ≤ a / 2) :
    ∃ A B : Set (E × ℝ), IsPLBall 3 A ∧ IsPLBall 3 B ∧
      A = {y | y.1 ∈ P ∧ -1 ≤ y.2 ∧ y.2 ≤ g y.1} ∧
      B = {y | y.1 ∈ P ∧ -g y.1 ≤ y.2 ∧ y.2 ≤ 1} ∧
      A ∩ B = {y | y.1 ∈ P ∧ |y.2| ≤ g y.1} ∧
      ((interior P ∩ {x | 0 < g x}) ×ˢ Ioo (-1 : ℝ) 1) ⊆ interior A ∪ interior B := by
  let A := piercingHeightMove g a '' (P ×ˢ Icc (-1 : ℝ) 0)
  let B := piercingHeightMove (fun x => -g x) a '' (P ×ˢ Icc (0 : ℝ) 1)
  have hneg : IsPiecewiseAffineOn (fun x => -g x) univ := by
    have hn : IsPiecewiseAffineOn (fun t : ℝ => -t) univ :=
      isPiecewiseAffineOn_of_affine (-(AffineMap.id ℝ ℝ)) isOpen_univ
    simpa only [preimage_univ, inter_univ, Function.comp_def] using hn.comp hg
  have hA : IsPLBall 3 A :=
    (isPLBall_three_prod hP (isPLBall_Icc (by norm_num : (-1 : ℝ) < 0))).of_isPLHomeomorphOn
      (isPLHomeomorphOn_piercingHeightMove hg a hP.isPolyhedron (-1) 0)
  have hB : IsPLBall 3 B :=
    (isPLBall_three_prod hP (isPLBall_Icc (by norm_num : (0 : ℝ) < 1))).of_isPLHomeomorphOn
      (isPLHomeomorphOn_piercingHeightMove hneg a hP.isPolyhedron 0 1)
  have hAe : A = {y | y.1 ∈ P ∧ -1 ≤ y.2 ∧ y.2 ≤ g y.1} :=
    piercingHeightMove_image_lower ha ha1 hga
  have hBe : B = {y | y.1 ∈ P ∧ -g y.1 ≤ y.2 ∧ y.2 ≤ 1} :=
    piercingHeightMove_image_upper ha ha1 (by simpa only [abs_neg] using hga)
  refine ⟨A, B, hA, hB, hAe, hBe, ?_, ?_⟩
  · rw [hAe, hBe]
    ext y
    constructor
    · rintro ⟨hyA, hyB⟩
      exact ⟨hyA.1, abs_le.mpr ⟨hyB.2.1, hyA.2.2⟩⟩
    · rintro ⟨hy, hz⟩
      obtain ⟨hlo, hhi⟩ := abs_le.mp hz
      have hbound := (abs_le.mp (hga y.1 hy)).2
      exact ⟨⟨hy, by linarith, hhi⟩, hy, hlo, by linarith⟩
  · have hcont : Continuous g := continuousOn_univ.mp hg.continuousOn
    have hAo : IsOpen {y : E × ℝ | y.1 ∈ interior P ∧ -1 < y.2 ∧ y.2 < g y.1} :=
      (isOpen_interior.preimage continuous_fst).inter
        ((isOpen_lt continuous_const continuous_snd).inter
          (isOpen_lt continuous_snd (hcont.comp continuous_fst)))
    have hBo : IsOpen {y : E × ℝ | y.1 ∈ interior P ∧ -g y.1 < y.2 ∧ y.2 < 1} :=
      (isOpen_interior.preimage continuous_fst).inter
        ((isOpen_lt (hcont.neg.comp continuous_fst) continuous_snd).inter
          (isOpen_lt continuous_snd continuous_const))
    have hAsub : {y : E × ℝ | y.1 ∈ interior P ∧ -1 < y.2 ∧ y.2 < g y.1} ⊆ A := by
      rw [hAe]
      exact fun _ hy => ⟨interior_subset hy.1, hy.2.1.le, hy.2.2.le⟩
    have hBsub : {y : E × ℝ | y.1 ∈ interior P ∧ -g y.1 < y.2 ∧ y.2 < 1} ⊆ B := by
      rw [hBe]
      exact fun _ hy => ⟨interior_subset hy.1, hy.2.1.le, hy.2.2.le⟩
    rintro y ⟨⟨hyP, hyg⟩, hyl, hyr⟩
    change 0 < g y.1 at hyg
    by_cases hyt : y.2 < g y.1
    · exact Or.inl (interior_maximal hAsub hAo ⟨hyP, hyl, hyt⟩)
    · exact Or.inr (interior_maximal hBsub hBo ⟨hyP, by linarith, hyr⟩)

end DifferentialGeometry.Topology.PiecewiseLinear
