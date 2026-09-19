/-
Copyright (c) 2026 Yuan Liao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuan Liao
-/
import DifferentialGeometry.Topology.PiecewiseLinear.CircleAnnulusIsotopy
import DifferentialGeometry.Topology.LoopSpace.CircleLiftOrientation
import DifferentialGeometry.Topology.LoopSpace.InjectiveLoop

/-! Circle orientation, reflections, and PL pseudo-isotopies. -/

open Set

namespace DifferentialGeometry.Topology.PiecewiseLinear

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

noncomputable def arcPathOfParam {A : Set E} {γ : ℝ → E} (hγ : IsPLHomeomorphOn γ (Icc 0 1) A) :
    Path (γ 0) (γ 1) where
  toFun t := γ (t : ℝ)
  continuous_toFun :=
    hγ.isPiecewiseAffineOn.continuousOn.comp_continuous continuous_subtype_val fun t => t.2
  source' := rfl
  target' := rfl

theorem arcPathOfParam_apply {A : Set E} {γ : ℝ → E} (hγ : IsPLHomeomorphOn γ (Icc 0 1) A)
    (t : unitInterval) : arcPathOfParam hγ t = γ (t : ℝ) := rfl

theorem range_arcPathOfParam {A : Set E} {γ : ℝ → E} (hγ : IsPLHomeomorphOn γ (Icc 0 1) A) :
    Set.range (arcPathOfParam hγ) = A := by
  have h : Set.range (arcPathOfParam hγ) = γ '' Icc (0 : ℝ) 1 := by
    change Set.range (γ ∘ (fun t : unitInterval => (t : ℝ))) = _
    rw [Set.range_comp, Subtype.range_coe]
  rw [h, hγ.image_eq]

theorem injective_arcPathOfParam {A : Set E} {γ : ℝ → E} (hγ : IsPLHomeomorphOn γ (Icc 0 1) A) :
    Function.Injective (arcPathOfParam hγ) := fun s t hst =>
  Subtype.ext (hγ.bijOn.injOn s.2 t.2 hst)

noncomputable def arcPathOfParamRev {B : Set E} {δ : ℝ → E} (hδ : IsPLHomeomorphOn δ (Icc 0 1) B)
    {x y : E} (hx : δ 1 = x) (hy : δ 0 = y) : Path x y where
  toFun t := δ (1 - (t : ℝ))
  continuous_toFun :=
    hδ.isPiecewiseAffineOn.continuousOn.comp_continuous
      (continuous_const.sub continuous_subtype_val)
      fun t => ⟨by linarith [t.2.2], by linarith [t.2.1]⟩
  source' := by simpa using hx
  target' := by simpa using hy

theorem range_arcPathOfParamRev {B : Set E} {δ : ℝ → E} (hδ : IsPLHomeomorphOn δ (Icc 0 1) B)
    {x y : E} (hx : δ 1 = x) (hy : δ 0 = y) :
    Set.range (arcPathOfParamRev hδ hx hy) = B := by
  have h : Set.range (arcPathOfParamRev hδ hx hy) =
      δ '' ((fun t : ℝ => 1 - t) '' Icc (0 : ℝ) 1) := by
    change Set.range (δ ∘ ((fun t : ℝ => 1 - t) ∘ (fun t : unitInterval => (t : ℝ)))) = _
    rw [Set.range_comp, Set.range_comp, Subtype.range_coe]
  rw [h, image_const_sub_Icc]
  norm_num
  exact hδ.image_eq

theorem injective_arcPathOfParamRev {B : Set E} {δ : ℝ → E} (hδ : IsPLHomeomorphOn δ (Icc 0 1) B)
    {x y : E} (hx : δ 1 = x) (hy : δ 0 = y) :
    Function.Injective (arcPathOfParamRev hδ hx hy) := by
  intro s t hst
  have hs : (1 : ℝ) - (s : ℝ) ∈ Icc (0 : ℝ) 1 := ⟨by linarith [s.2.2], by linarith [s.2.1]⟩
  have ht : (1 : ℝ) - (t : ℝ) ∈ Icc (0 : ℝ) 1 := ⟨by linarith [t.2.2], by linarith [t.2.1]⟩
  have h := hδ.bijOn.injOn hs ht hst
  exact Subtype.ext (by linarith)

theorem exists_loopCircle_param_of_arc_decomposition
    {S A B : Set E} {γ δ : ℝ → E} (hγ : IsPLHomeomorphOn γ (Icc 0 1) A)
    (hδ : IsPLHomeomorphOn δ (Icc 0 1) B) (hδ0 : δ 0 = γ 0) (hδ1 : δ 1 = γ 1)
    (hunion : A ∪ B = S) (hinter : A ∩ B = {γ 0, γ 1}) :
    ∃ g : loopCircle → E, Continuous g ∧ BijOn g univ S ∧
      g '' ((fun t : ℝ => (t : loopCircle)) '' Icc 0 ((1 : ℝ) / 2)) = A ∧
        g ((0 : ℝ) : loopCircle) = γ 0 ∧ g (((1 : ℝ) / 2 : ℝ) : loopCircle) = γ 1 := by
  set pA : Path (γ 0) (γ 1) := arcPathOfParam hγ with hpAdef
  set pB : Path (γ 1) (γ 0) := arcPathOfParamRev hδ hδ1 hδ0 with hpBdef
  set ℓ : Path (γ 0) (γ 0) := pA.trans pB with hℓdef
  have hrangeA : Set.range pA = A := range_arcPathOfParam hγ
  have hrangeB : Set.range pB = B := range_arcPathOfParamRev hδ hδ1 hδ0
  have hrange : Set.range ℓ = S := by
    rw [hℓdef, Path.trans_range, hrangeA, hrangeB, hunion]
  have hinj : Function.Injective (pathToCircle ℓ) :=
    pathToCircle_trans_injective (injective_arcPathOfParam hγ)
      (injective_arcPathOfParamRev hδ hδ1 hδ0) (by rw [hrangeA, hrangeB, hinter])
  have hlow : ∀ s : ℝ, ∀ hs : s ∈ Icc (0 : ℝ) ((1 : ℝ) / 2),
      pathToCircle ℓ ((s : ℝ) : loopCircle) = γ (2 * s) := by
    intro s hs
    have hsI : s ∈ Icc (0 : ℝ) 1 := ⟨hs.1, by linarith [hs.2]⟩
    have hcoe := pathToCircle_coe ℓ ⟨s, hsI⟩
    rw [hcoe, hℓdef, Path.trans_apply, dif_pos (show ((⟨s, hsI⟩ : unitInterval) : ℝ) ≤ 1 / 2 from
      hs.2)]
    rfl
  refine ⟨pathToCircle ℓ, (pathToCircle ℓ).continuous, ⟨?_, hinj.injOn, ?_⟩, ?_, ?_, ?_⟩
  · intro θ _
    obtain ⟨t, rfl⟩ := unitInterval_to_loopCircle_surjective θ
    rw [pathToCircle_coe ℓ t]
    exact hrange ▸ Set.mem_range_self t
  · intro y hy
    obtain ⟨t, ht⟩ : y ∈ Set.range ℓ := hrange ▸ hy
    exact ⟨((t : ℝ) : loopCircle), mem_univ _, (pathToCircle_coe ℓ t).trans ht⟩
  · refine Subset.antisymm ?_ ?_
    · rintro _ ⟨_, ⟨s, hs, rfl⟩, rfl⟩
      rw [hlow s hs]
      exact hγ.bijOn.mapsTo ⟨by linarith [hs.1], by linarith [hs.2]⟩
    · intro y hy
      obtain ⟨r, hr, rfl⟩ := hγ.bijOn.surjOn hy
      refine ⟨((r / 2 : ℝ) : loopCircle),
        ⟨r / 2, ⟨by linarith [hr.1], by linarith [hr.2]⟩, rfl⟩, ?_⟩
      rw [hlow (r / 2) ⟨by linarith [hr.1], by linarith [hr.2]⟩]
      ring_nf
  · have h := hlow 0 (by norm_num)
    rw [h]
    norm_num
  · have h := hlow ((1 : ℝ) / 2) (by norm_num)
    rw [h]
    norm_num

theorem exists_pair_ne_of_isPLSphere_one {S : Set E}
    (hS : IsPLSphere 1 S) : ∃ x ∈ S, ∃ y ∈ S, x ≠ y := by
  obtain ⟨f, hf⟩ := hS
  have h0 : (Pi.single (0 : Fin 3) (1 : ℝ)) ∈ stdSimplexBoundary 2 :=
    ⟨single_mem_stdSimplex ℝ _, ⟨1, by simp⟩⟩
  have h1 : (Pi.single (1 : Fin 3) (1 : ℝ)) ∈ stdSimplexBoundary 2 :=
    ⟨single_mem_stdSimplex ℝ _, ⟨0, by simp⟩⟩
  refine ⟨f _, hf.bijOn.mapsTo h0, f _, hf.bijOn.mapsTo h1, fun h => ?_⟩
  have heq := hf.bijOn.injOn h0 h1 h
  have hval := congrFun heq (0 : Fin 3)
  simp at hval

noncomputable def circleConj (g : loopCircle → E) (u : E → E) : loopCircle → loopCircle :=
  Function.invFunOn g Set.univ ∘ (u ∘ g)

omit [NormedAddCommGroup E] [NormedSpace ℝ E] in
theorem circleConj_spec {S : Set E} {g : loopCircle → E} (hgb : BijOn g univ S) {u : E → E}
    (hmu : MapsTo u S S) (θ : loopCircle) : g (circleConj g u θ) = u (g θ) :=
  hgb.invOn_invFunOn.2 (hmu (hgb.mapsTo (mem_univ θ)))

omit [NormedAddCommGroup E] [NormedSpace ℝ E] in
theorem circleConj_id {S : Set E} {g : loopCircle → E} (hgb : BijOn g univ S) (θ : loopCircle) :
    circleConj g (id : E → E) θ = θ :=
  hgb.injOn.leftInvOn_invFunOn (mem_univ θ)

omit [NormedAddCommGroup E] [NormedSpace ℝ E] in
theorem circleConj_comp {S : Set E} {g : loopCircle → E} (hgb : BijOn g univ S) {u v : E → E}
    (hmv : MapsTo v S S) (θ : loopCircle) :
    circleConj g (u ∘ v) θ = circleConj g u (circleConj g v θ) := by
  change Function.invFunOn g univ (u (v (g θ))) =
    Function.invFunOn g univ (u (g (circleConj g v θ)))
  rw [circleConj_spec hgb hmv θ]

omit [NormedAddCommGroup E] [NormedSpace ℝ E] in
theorem bijective_circleConj {S : Set E} {g : loopCircle → E} (hgb : BijOn g univ S) {u : E → E}
    (hbu : BijOn u S S) : Function.Bijective (circleConj g u) := by
  constructor
  · intro a b hab
    have h := congrArg g hab
    rw [circleConj_spec hgb hbu.mapsTo a, circleConj_spec hgb hbu.mapsTo b] at h
    exact hgb.injOn (mem_univ a) (mem_univ b)
      (hbu.injOn (hgb.mapsTo (mem_univ a)) (hgb.mapsTo (mem_univ b)) h)
  · intro η
    obtain ⟨x, hx, hxu⟩ := hbu.surjOn (hgb.mapsTo (mem_univ η))
    obtain ⟨θ, -, hθ⟩ := hgb.surjOn hx
    refine ⟨θ, ?_⟩
    have h : g (circleConj g u θ) = g η := by
      rw [circleConj_spec hgb hbu.mapsTo θ, hθ, hxu]
    exact hgb.injOn (mem_univ _) (mem_univ _) h

noncomputable def paramHomeomorph {S : Set E} {g : loopCircle → E} (hgc : Continuous g)
    (hgb : BijOn g univ S) : loopCircle ≃ₜ ↥S :=
  Continuous.homeoOfEquivCompactToT2
    (f := Equiv.ofBijective (fun θ => (⟨g θ, hgb.mapsTo (mem_univ θ)⟩ : ↥S))
      ⟨fun a b hab => hgb.injOn (mem_univ a) (mem_univ b) (congrArg Subtype.val hab), by
        rintro ⟨y, hy⟩
        obtain ⟨θ, -, hθ⟩ := hgb.surjOn hy
        exact ⟨θ, Subtype.ext hθ⟩⟩)
    (hgc.subtype_mk _)

omit [NormedSpace ℝ E] in
theorem paramHomeomorph_coe {S : Set E} {g : loopCircle → E} (hgc : Continuous g)
    (hgb : BijOn g univ S) (θ : loopCircle) :
    ((paramHomeomorph hgc hgb θ : ↥S) : E) = g θ := rfl

omit [NormedSpace ℝ E] in
theorem paramHomeomorph_symm {S : Set E} {g : loopCircle → E} (hgc : Continuous g)
    (hgb : BijOn g univ S) (y : ↥S) :
    (paramHomeomorph hgc hgb).symm y = Function.invFunOn g univ (y : E) := by
  have h1 : g ((paramHomeomorph hgc hgb).symm y) = (y : E) :=
    congrArg Subtype.val ((paramHomeomorph hgc hgb).apply_symm_apply y)
  have h2 : Function.invFunOn g univ (g ((paramHomeomorph hgc hgb).symm y)) =
      (paramHomeomorph hgc hgb).symm y := hgb.injOn.leftInvOn_invFunOn (mem_univ _)
  rw [← h1, h2]

omit [NormedSpace ℝ E] in
theorem continuous_circleConj {S : Set E} {g : loopCircle → E} (hgc : Continuous g)
    (hgb : BijOn g univ S) {u : E → E} (hcu : ContinuousOn u S) (hmu : MapsTo u S S) :
    Continuous (circleConj g u) := by
  have hmaps : ∀ θ : loopCircle, g θ ∈ S := fun θ => hgb.mapsTo (mem_univ θ)
  have hcomp : circleConj g u =
      fun θ => (paramHomeomorph hgc hgb).symm ⟨u (g θ), hmu (hmaps θ)⟩ := by
    funext θ
    exact (paramHomeomorph_symm hgc hgb ⟨u (g θ), hmu (hmaps θ)⟩).symm
  rw [hcomp]
  exact (paramHomeomorph hgc hgb).continuous_symm.comp
    ((hcu.comp_continuous hgc hmaps).subtype_mk _)

def IsPLCirclePositive (S : Set E) (u : E → E) : Prop :=
  ∃ g : loopCircle → E, Continuous g ∧ BijOn g univ S ∧ HasIncreasingCircleLift (circleConj g u)

omit [NormedSpace ℝ E] in
theorem IsPLCirclePositive.forall_param {S : Set E} {u : E → E} (hu : IsPLCirclePositive S u)
    (hmu : MapsTo u S S) {g : loopCircle → E} (hgc : Continuous g) (hgb : BijOn g univ S) :
    HasIncreasingCircleLift (circleConj g u) := by
  obtain ⟨g₀, hg₀c, hg₀b, h₀⟩ := hu
  set φ : loopCircle ≃ₜ loopCircle :=
    (paramHomeomorph hgc hgb).trans (paramHomeomorph hg₀c hg₀b).symm with hφdef
  have hφval : ∀ θ, φ θ = Function.invFunOn g₀ univ (g θ) := fun θ =>
    paramHomeomorph_symm hg₀c hg₀b _
  have hφsymval : ∀ η, φ.symm η = Function.invFunOn g univ (g₀ η) := by
    intro η
    change (paramHomeomorph hgc hgb).symm ((paramHomeomorph hg₀c hg₀b) η) = _
    rw [paramHomeomorph_symm hgc hgb]
    rfl
  refine (h₀.conj φ).congr fun θ => ?_
  have h1 : g₀ (φ θ) = g θ := by
    rw [hφval]
    exact hg₀b.invOn_invFunOn.2 (hgb.mapsTo (mem_univ θ))
  change circleConj g u θ = φ.symm (circleConj g₀ u (φ θ))
  rw [hφsymval, circleConj_spec hg₀b hmu (φ θ), h1]
  rfl

theorem exists_loopCircle_param_of_isPLSphere_one [FiniteDimensional ℝ E] {S : Set E}
    (hS : IsPLSphere 1 S) : ∃ g : loopCircle → E, Continuous g ∧ BijOn g univ S := by
  obtain ⟨p, hp, q, hq, hpq⟩ := exists_pair_ne_of_isPLSphere_one hS
  obtain ⟨A, B, γ, δ, hγ, hδ, hγ0, hγ1, hδ0, hδ1, hunion, hinter⟩ :=
    exists_arc_decomposition_of_isPLSphere_one hS hp hq hpq
  obtain ⟨g, hgc, hgb, -, -, -⟩ := exists_loopCircle_param_of_arc_decomposition hγ hδ
    (hδ0.trans hγ0.symm) (hδ1.trans hγ1.symm) hunion (by rw [hinter, hγ0, hγ1])
  exact ⟨g, hgc, hgb⟩

theorem isPLCirclePositive_id [FiniteDimensional ℝ E] {S : Set E} (hS : IsPLSphere 1 S) :
    IsPLCirclePositive S (id : E → E) := by
  obtain ⟨g, hgc, hgb⟩ := exists_loopCircle_param_of_isPLSphere_one hS
  exact ⟨g, hgc, hgb, hasIncreasingCircleLift_id.congr fun θ => circleConj_id hgb θ⟩

omit [NormedSpace ℝ E] in
theorem IsPLCirclePositive.comp {S : Set E} {u v : E → E} (hu : IsPLCirclePositive S u)
    (hv : IsPLCirclePositive S v) (hmv : MapsTo v S S) : IsPLCirclePositive S (u ∘ v) := by
  obtain ⟨g, hgc, hgb, hgu⟩ := hu
  exact ⟨g, hgc, hgb,
    (hgu.comp (hv.forall_param hmv hgc hgb)).congr fun θ => circleConj_comp hgb hmv θ⟩

theorem isPLCirclePositive_of_three_fixed [FiniteDimensional ℝ E] {S : Set E}
    (hS : IsPLSphere 1 S) {u : E → E}
    (hcu : ContinuousOn u S) (hbu : BijOn u S S) {x y z : E} (hx : x ∈ S) (hy : y ∈ S) (hz : z ∈ S)
    (hxy : x ≠ y) (hxz : x ≠ z) (hyz : y ≠ z)
    (hux : u x = x) (huy : u y = y) (huz : u z = z) : IsPLCirclePositive S u := by
  obtain ⟨g, hgc, hgb⟩ := exists_loopCircle_param_of_isPLSphere_one hS
  refine ⟨g, hgc, hgb, ?_⟩
  have hfix : ∀ {w : E}, w ∈ S → u w = w →
      circleConj g u (Function.invFunOn g univ w) = Function.invFunOn g univ w := by
    intro w hw hwu
    have hgw : g (Function.invFunOn g univ w) = w := hgb.invOn_invFunOn.2 hw
    change Function.invFunOn g univ (u (g (Function.invFunOn g univ w))) = _
    rw [hgw, hwu]
  have hne : ∀ {a b : E}, a ∈ S → b ∈ S → a ≠ b →
      Function.invFunOn g univ a ≠ Function.invFunOn g univ b := by
    intro a b ha hb hab h
    exact hab (((hgb.invOn_invFunOn.2 ha).symm.trans (congrArg g h)).trans
      (hgb.invOn_invFunOn.2 hb))
  exact hasIncreasingCircleLift_of_three_fixed_of_continuous
    (continuous_circleConj hgc hgb hcu hbu.mapsTo) (bijective_circleConj hgb hbu)
    (hne hx hy hxy) (hne hx hz hxz) (hne hy hz hyz) (hfix hx hux) (hfix hy huy) (hfix hz huz)

theorem isPLCirclePositive_of_eqOn_arc [FiniteDimensional ℝ E] {S B : Set E} {ξ : ℝ → E}
    (hS : IsPLSphere 1 S) (hξ : IsPLHomeomorphOn ξ (Icc 0 1) B) (hBS : B ⊆ S) {r : E → E}
    (hr : IsPLHomeomorphOn r S S) (hrB : EqOn r id B) : IsPLCirclePositive S r := by
  have hm0 : ξ 0 ∈ B := hξ.bijOn.mapsTo (by norm_num)
  have hmh : ξ ((1 : ℝ) / 2) ∈ B := hξ.bijOn.mapsTo (by norm_num)
  have hm1 : ξ 1 ∈ B := hξ.bijOn.mapsTo (by norm_num)
  refine isPLCirclePositive_of_three_fixed hS hr.isPiecewiseAffineOn.continuousOn hr.bijOn
    (hBS hm0) (hBS hmh) (hBS hm1) (fun h => ?_) (fun h => ?_) (fun h => ?_)
    (hrB hm0) (hrB hmh) (hrB hm1)
  · have hq := hξ.bijOn.injOn (show (0 : ℝ) ∈ Icc 0 1 by norm_num)
      (show (1 : ℝ) / 2 ∈ Icc (0 : ℝ) 1 by norm_num) h
    norm_num at hq
  · have hq := hξ.bijOn.injOn (show (0 : ℝ) ∈ Icc 0 1 by norm_num)
      (show (1 : ℝ) ∈ Icc (0 : ℝ) 1 by norm_num) h
    norm_num at hq
  · have hq := hξ.bijOn.injOn (show (1 : ℝ) / 2 ∈ Icc (0 : ℝ) 1 by norm_num)
      (show (1 : ℝ) ∈ Icc (0 : ℝ) 1 by norm_num) h
    norm_num at hq

theorem exists_positive_map_eq_of_isPLSphere_one [FiniteDimensional ℝ E]
    {S : Set E} (hS : IsPLSphere 1 S) {p p' : E} (hp : p ∈ S) (hp' : p' ∈ S) :
    ∃ r : E → E, IsPLHomeomorphOn r S S ∧ IsPLPseudoIsotopicToId r S ∧ r p' = p ∧
      IsPLCirclePositive S r := by
  by_cases hpp : p = p'
  · exact ⟨id, hS.isPolyhedron.isPLHomeomorphOn_id, isPLPseudoIsotopicToId_id hS.isPolyhedron,
      hpp.symm, isPLCirclePositive_id hS⟩
  · obtain ⟨A, B, ε, ξ, hε, hξ, hunion, hinter, hpA, hp'A⟩ :=
      exists_arc_pair_interior_of_isPLSphere_one hS hp hp' hpp
    obtain ⟨r, hr, hrid, hrp, hrB⟩ := exists_isPLPseudoIsotopicToId_map_eq_of_arc hε
      ((isPLBall_Icc zero_lt_one).of_isPLHomeomorphOn hξ).isPolyhedron hunion hinter hpA hp'A
    exact ⟨r, hr, hrid, hrp,
      isPLCirclePositive_of_eqOn_arc hS hξ (hunion ▸ subset_union_right) hr hrB⟩

theorem image_arc_eq_of_isPLCirclePositive
    {S A B : Set E} {γ δ : ℝ → E} (hγ : IsPLHomeomorphOn γ (Icc 0 1) A)
    (hδ : IsPLHomeomorphOn δ (Icc 0 1) B) (hδ0 : δ 0 = γ 0) (hδ1 : δ 1 = γ 1)
    (hunion : A ∪ B = S) (hinter : A ∩ B = {γ 0, γ 1})
    {u : E → E} (hu : IsPLHomeomorphOn u S S) (hpos : IsPLCirclePositive S u)
    (hu0 : u (γ 0) = γ 0) (hu1 : u (γ 1) = γ 1) : u '' A = A := by
  obtain ⟨g, hgc, hgb, hgA, hg0, hghalf⟩ :=
    exists_loopCircle_param_of_arc_decomposition hγ hδ hδ0 hδ1 hunion hinter
  have hbu : BijOn u S S := hu.bijOn
  have hfix : ∀ {w : E} {θ : loopCircle}, g θ = w → u w = w → circleConj g u θ = θ := by
    intro w θ hgθ hwu
    have hval : g (circleConj g u θ) = g θ := by
      rw [circleConj_spec hgb hbu.mapsTo θ, hgθ, hwu]
    exact hgb.injOn (mem_univ _) (mem_univ _) hval
  have himg := image_coe_Icc_zero_half_eq_of_hasIncreasingCircleLift
    (hpos.forall_param hbu.mapsTo hgc hgb)
    (bijective_circleConj hgb hbu).2 (hfix hg0 hu0) (hfix hghalf hu1)
  have hkey : ∀ X : Set loopCircle, u '' (g '' X) = g '' (circleConj g u '' X) := by
    intro X
    rw [← image_comp, ← image_comp]
    exact image_congr fun θ _ => (circleConj_spec hgb hbu.mapsTo θ).symm
  rw [← hgA, hkey, himg]

theorem isPLPseudoIsotopicToId_of_isPLCirclePositive [FiniteDimensional ℝ E]
    {S : Set E} (hS : IsPLSphere 1 S) {u : E → E} (hu : IsPLHomeomorphOn u S S)
    (hpos : IsPLCirclePositive S u) : IsPLPseudoIsotopicToId u S := by
  obtain ⟨p, hp, q, hq, hpq⟩ := exists_pair_ne_of_isPLSphere_one hS
  obtain ⟨r₁, hr₁, hr₁id, hr₁p, hr₁pos⟩ :=
    exists_positive_map_eq_of_isPLSphere_one hS hp (hu.bijOn.mapsTo hp)
  have hw₁ : IsPLHomeomorphOn (r₁ ∘ u) S S := hu.trans hr₁
  have hw₁p : (r₁ ∘ u) p = p := hr₁p
  have hw₁pos : IsPLCirclePositive S (r₁ ∘ u) := hr₁pos.comp hpos hu.bijOn.mapsTo
  have hw₁q : (r₁ ∘ u) q ∈ S := hw₁.bijOn.mapsTo hq
  have hw₁qp : (r₁ ∘ u) q ≠ p := fun h =>
    hpq (hw₁.bijOn.injOn hq hp (h.trans hw₁p.symm)).symm
  obtain ⟨A₂, B₂, ε₂, ξ₂, hε₂, hξ₂, hun₂, hin₂, hε₂0, hqA₂, hwqA₂⟩ :=
    exists_arc_endpoint_pair_interior hS hp hq hw₁q (fun h => hpq h.symm) hw₁qp
  obtain ⟨r₂, hr₂, hr₂id, hr₂q, hr₂B⟩ := exists_isPLPseudoIsotopicToId_map_eq_of_arc hε₂
    ((isPLBall_Icc zero_lt_one).of_isPLHomeomorphOn hξ₂).isPolyhedron hun₂ hin₂ hqA₂ hwqA₂
  have hr₂pos : IsPLCirclePositive S r₂ :=
    isPLCirclePositive_of_eqOn_arc hS hξ₂ (hun₂ ▸ subset_union_right) hr₂ hr₂B
  have hε₂0B : ε₂ 0 ∈ B₂ := (hin₂.symm.subset (Or.inl rfl)).2
  have hw₂ : IsPLHomeomorphOn (r₂ ∘ (r₁ ∘ u)) S S := hw₁.trans hr₂
  have hw₂p : (r₂ ∘ (r₁ ∘ u)) p = p := by
    change r₂ ((r₁ ∘ u) p) = p
    rw [hw₁p, ← hε₂0]
    exact hr₂B hε₂0B
  have hw₂q : (r₂ ∘ (r₁ ∘ u)) q = q := hr₂q
  have hw₂pos : IsPLCirclePositive S (r₂ ∘ (r₁ ∘ u)) := hr₂pos.comp hw₁pos hw₁.bijOn.mapsTo
  obtain ⟨A, B, γ, δ, hγ, hδ, hγ0, hγ1, hδ0, hδ1, hunion, hinter⟩ :=
    exists_arc_decomposition_of_isPLSphere_one hS hp hq hpq
  have hinter' : A ∩ B = {γ 0, γ 1} := by rw [hinter, hγ0, hγ1]
  have hIA : (r₂ ∘ (r₁ ∘ u)) '' A = A := image_arc_eq_of_isPLCirclePositive hγ hδ
    (hδ0.trans hγ0.symm) (hδ1.trans hγ1.symm) hunion hinter' hw₂ hw₂pos
    (hγ0.symm ▸ hw₂p) (hγ1.symm ▸ hw₂q)
  have hne : (r₂ ∘ (r₁ ∘ u)) '' A ≠ B := by
    rw [hIA]
    intro hAB
    have hmid : γ ((1 : ℝ) / 2) ∈ A := hγ.bijOn.mapsTo (by norm_num)
    have hmem : γ ((1 : ℝ) / 2) ∈ ({γ 0, γ 1} : Set E) :=
      hinter' ▸ mem_inter hmid (hAB ▸ hmid)
    rcases hmem with h | h
    · have hq2 := hγ.bijOn.injOn (show (1 : ℝ) / 2 ∈ Icc (0 : ℝ) 1 by norm_num)
        (show (0 : ℝ) ∈ Icc (0 : ℝ) 1 by norm_num) h
      norm_num at hq2
    · have h' : γ ((1 : ℝ) / 2) = γ 1 := h
      have hq2 := hγ.bijOn.injOn (show (1 : ℝ) / 2 ∈ Icc (0 : ℝ) 1 by norm_num)
        (show (1 : ℝ) ∈ Icc (0 : ℝ) 1 by norm_num) h'
      norm_num at hq2
  have hw₂iso : IsPLPseudoIsotopicToId (r₂ ∘ (r₁ ∘ u)) S :=
    isPLPseudoIsotopicToId_of_arc_decomposition_of_ne hγ hδ (hδ0.trans hγ0.symm)
      (hδ1.trans hγ1.symm) hunion hinter' hw₂ (hγ0.symm ▸ hw₂p) (hγ1.symm ▸ hw₂q) hne
  exact isPLPseudoIsotopicToId_of_comp_left hu hr₁ hr₁id
    (isPLPseudoIsotopicToId_of_comp_left hw₁ hr₂ hr₂id hw₂iso)

open Classical in
theorem isPLPseudoIsotopicToId_of_boundary_isPLCirclePositive [FiniteDimensional ℝ E]
    (K : Geometry.SimplicialComplex ℝ E) [Finite K.faces] (hK : IsPLBall 2 K.space)
    {u : E → E} (hu : IsPLHomeomorphOn u K.space K.space)
    (hpos : IsPLCirclePositive (boundaryComplex 2 K).space u) :
    IsPLPseudoIsotopicToId u K.space := by
  classical
  let _ : Finite (boundaryComplex 2 K).faces := (boundaryComplex_faces_finite 2 K).to_subtype
  have hDsub : (boundaryComplex 2 K).space ⊆ K.space := boundaryComplex_space_subset 2 K
  have hDimg : (boundaryComplex 2 K).space = u '' (boundaryComplex 2 K).space :=
    boundaryComplex_space_of_isPLHomeomorphOn K K hK.isCombinatorialManifoldWithBoundary hu
  have huD : IsPLHomeomorphOn u (boundaryComplex 2 K).space (boundaryComplex 2 K).space := by
    have h := hu.restrict (isPolyhedron_space _) hDsub
    rwa [← hDimg] at h
  obtain ⟨Φ, hΦ, hΦ0, hΦ1⟩ := isPLPseudoIsotopicToId_of_isPLCirclePositive
    (isPLSphere_boundaryComplex_space_of_isPLBall K hK) huD hpos
  have hQ : IsPLBall 3 (K.space ×ˢ Icc (0 : ℝ) 1) :=
    isPLBall_three_prod hK (isPLBall_Icc zero_lt_one)
  obtain ⟨A, hAfin, hAspace⟩ := hQ.isPolyhedron.exists_simplicialComplex
  let _ : Finite A.faces := hAfin.to_subtype
  have hAball : IsPLBall 3 A.space := hAspace ▸ hQ
  have hbdA : (boundaryComplex 3 A).space =
      K.space ×ˢ ({1} : Set ℝ) ∪
        (K.space ×ˢ ({0} : Set ℝ) ∪ (boundaryComplex 2 K).space ×ˢ Icc (0 : ℝ) 1) := by
    rw [boundaryComplex_space_prism K hK zero_lt_one A hAspace]
    ext z
    simp only [mem_union, mem_prod, mem_insert_iff, mem_singleton_iff]
    tauto
  set θ : E × ℝ → E × ℝ :=
    fun z => if z.2 = 1 then (u z.1, z.2) else if z.2 = 0 then z else Φ z with hθdef
  have hsing1 : IsPolyhedron ({1} : Set ℝ) := by
    rw [← Icc_self (1 : ℝ)]
    exact isHPolytope_Icc.isPolyhedron
  have hW1poly : IsPolyhedron (K.space ×ˢ ({1} : Set ℝ)) :=
    isPolyhedron_prod_singleton hK.isPolyhedron 1
  have hW00poly : IsPolyhedron (K.space ×ˢ ({0} : Set ℝ)) :=
    isPolyhedron_prod_singleton hK.isPolyhedron 0
  have hWDpoly : IsPolyhedron ((boundaryComplex 2 K).space ×ˢ Icc (0 : ℝ) 1) :=
    (isPolyhedron_space _).prod isHPolytope_Icc.isPolyhedron
  have hθ1 : IsPLHomeomorphOn θ (K.space ×ˢ ({1} : Set ℝ)) (K.space ×ˢ ({1} : Set ℝ)) := by
    refine (hu.prodMap hsing1.isPLHomeomorphOn_id).congr ?_
    rintro z ⟨-, hz2⟩
    have hz2' : z.2 = 1 := hz2
    simp only [hθdef, if_pos hz2']
    rfl
  have hθ00 : IsPLHomeomorphOn θ (K.space ×ˢ ({0} : Set ℝ)) (K.space ×ˢ ({0} : Set ℝ)) := by
    refine hW00poly.isPLHomeomorphOn_id.congr ?_
    rintro z ⟨-, hz2⟩
    have hz2' : z.2 = 0 := hz2
    have hz1 : z.2 ≠ 1 := by rw [hz2']; norm_num
    simp only [hθdef, if_neg hz1, if_pos hz2']
    rfl
  have hθD : IsPLHomeomorphOn θ ((boundaryComplex 2 K).space ×ˢ Icc (0 : ℝ) 1)
      ((boundaryComplex 2 K).space ×ˢ Icc (0 : ℝ) 1) := by
    refine hΦ.congr ?_
    rintro z ⟨hz1, hz2⟩
    by_cases h1 : z.2 = 1
    · have hz : z = (z.1, (1 : ℝ)) := Prod.ext rfl h1
      simp only [hθdef, if_pos h1]
      rw [hz, hΦ1 z.1 hz1, ← h1]
    · by_cases h0 : z.2 = 0
      · have hz : z = (z.1, (0 : ℝ)) := Prod.ext rfl h0
        simp only [hθdef, if_neg h1, if_pos h0]
        rw [hz, hΦ0 z.1 hz1]
      · simp only [hθdef, if_neg h1, if_neg h0]
  have hmeet0 : (K.space ×ˢ ({0} : Set ℝ)) ∩ ((boundaryComplex 2 K).space ×ˢ Icc (0 : ℝ) 1) =
      (boundaryComplex 2 K).space ×ˢ ({0} : Set ℝ) := by
    ext z
    simp only [mem_inter_iff, mem_prod, mem_singleton_iff, mem_Icc]
    constructor
    · rintro ⟨⟨-, hz2⟩, hz1, -⟩
      exact ⟨hz1, hz2⟩
    · rintro ⟨hz1, hz2⟩
      exact ⟨⟨hDsub hz1, hz2⟩, hz1, by norm_num [hz2], by norm_num [hz2]⟩
  have hidD0 : ∀ z ∈ (boundaryComplex 2 K).space ×ˢ ({0} : Set ℝ), θ z = z := by
    rintro z ⟨-, hz2⟩
    have hz2' : z.2 = 0 := hz2
    have hz1 : z.2 ≠ 1 := by rw [hz2']; norm_num
    simp only [hθdef, if_neg hz1, if_pos hz2']
  have hθ0 : IsPLHomeomorphOn θ
      (K.space ×ˢ ({0} : Set ℝ) ∪ (boundaryComplex 2 K).space ×ˢ Icc (0 : ℝ) 1)
      (K.space ×ˢ ({0} : Set ℝ) ∪ (boundaryComplex 2 K).space ×ˢ Icc (0 : ℝ) 1) := by
    refine hθ00.union hθD hW00poly hWDpoly ?_
    rw [hmeet0]
    exact (image_congr hidD0).trans (image_id _)
  have hmeet1 : (K.space ×ˢ ({1} : Set ℝ)) ∩
      (K.space ×ˢ ({0} : Set ℝ) ∪ (boundaryComplex 2 K).space ×ˢ Icc (0 : ℝ) 1) =
      (boundaryComplex 2 K).space ×ˢ ({1} : Set ℝ) := by
    ext z
    simp only [mem_inter_iff, mem_union, mem_prod, mem_singleton_iff, mem_Icc]
    constructor
    · rintro ⟨⟨-, hz2⟩, hcase⟩
      rcases hcase with ⟨-, hz0⟩ | ⟨hz1, -⟩
      · exact absurd (hz2.symm.trans hz0) (by norm_num)
      · exact ⟨hz1, hz2⟩
    · rintro ⟨hz1, hz2⟩
      exact ⟨⟨hDsub hz1, hz2⟩, Or.inr ⟨hz1, by norm_num [hz2], by norm_num [hz2]⟩⟩
  have himD1 : θ '' ((boundaryComplex 2 K).space ×ˢ ({1} : Set ℝ)) =
      (boundaryComplex 2 K).space ×ˢ ({1} : Set ℝ) := by
    have hval : ∀ z ∈ (boundaryComplex 2 K).space ×ˢ ({1} : Set ℝ), θ z = (u z.1, z.2) := by
      rintro z ⟨-, hz2⟩
      have hz2' : z.2 = 1 := hz2
      simp only [hθdef, if_pos hz2']
    rw [image_congr hval]
    ext w
    constructor
    · rintro ⟨z, ⟨hz1, hz2⟩, rfl⟩
      exact ⟨huD.bijOn.mapsTo hz1, hz2⟩
    · rintro ⟨hw1, hw2⟩
      obtain ⟨x, hx, hxu⟩ := huD.bijOn.surjOn hw1
      exact ⟨(x, w.2), ⟨hx, hw2⟩, Prod.ext hxu rfl⟩
  have hθbd := hθ1.union hθ0 hW1poly
    (hW00poly.union hWDpoly) (by rw [hmeet1]; exact himD1)
  rw [← hbdA] at hθbd
  obtain ⟨Ψ, hΨ, hΨbd⟩ :=
    exists_isPLHomeomorphOn_of_boundaryComplex (n := 2) A A hAball hAball hθbd
  refine ⟨Ψ, hAspace ▸ hΨ, fun x hx => ?_, fun x hx => ?_⟩
  · have hmem : (x, (0 : ℝ)) ∈ (boundaryComplex 3 A).space := by
      rw [hbdA]
      exact Or.inr (Or.inl ⟨hx, rfl⟩)
    rw [hΨbd hmem]
    simp [hθdef]
  · have hmem : (x, (1 : ℝ)) ∈ (boundaryComplex 3 A).space := by
      rw [hbdA]
      exact Or.inl ⟨hx, rfl⟩
    rw [hΨbd hmem]
    simp [hθdef]

open Classical in
theorem exists_isPLHomeomorphOn_of_endMaps_boundary_isPLCirclePositive
    {E₂ F G : Type*} [NormedAddCommGroup E₂] [NormedSpace ℝ E₂] [FiniteDimensional ℝ E₂]
    [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
    [NormedAddCommGroup G] [NormedSpace ℝ G] [FiniteDimensional ℝ G] [FiniteDimensional ℝ E]
    (K : Geometry.SimplicialComplex ℝ E) [Finite K.faces] (hK : IsPLBall 2 K.space)
    (K' : Geometry.SimplicialComplex ℝ E₂) [Finite K'.faces] (hK' : IsPLBall 2 K'.space)
    {S : Set F} {T : Set G} {f : E × ℝ → F} {g : E₂ × ℝ → G}
    (hf : IsCylindricalDiagram f K.space S) (hg : IsCylindricalDiagram g K'.space T)
    {uf : E → E} {ug : E₂ → E₂} (huf : IsPLHomeomorphOn uf K.space K.space)
    (hug : IsPLHomeomorphOn ug K'.space K'.space)
    (hfuf : ∀ x ∈ K.space, f (x, 0) = f (uf x, 1))
    (hgug : ∀ x ∈ K'.space, g (x, 0) = g (ug x, 1))
    (hposf : IsPLCirclePositive (boundaryComplex 2 K).space uf)
    (hposg : IsPLCirclePositive (boundaryComplex 2 K').space ug)
    {w : E₂ → E} (hw : IsPLHomeomorphOn w K'.space K.space) :
    ∃ H : F → G, IsPLHomeomorphOn H S T :=
  exists_isPLHomeomorphOn_of_endMaps_pseudoIsotopicToId hf hg hK'.isPolyhedron huf hug hfuf hgug
    (isPLPseudoIsotopicToId_of_boundary_isPLCirclePositive K hK huf hposf)
    (isPLPseudoIsotopicToId_of_boundary_isPLCirclePositive K' hK' hug hposg) hw

theorem exists_isPLHomeomorphOn_reflection_of_arc_decomposition [FiniteDimensional ℝ E]
    {S A B : Set E} {γ δ : ℝ → E} (hγ : IsPLHomeomorphOn γ (Icc 0 1) A)
    (hδ : IsPLHomeomorphOn δ (Icc 0 1) B) (hδ0 : δ 0 = γ 0) (hδ1 : δ 1 = γ 1)
    (hunion : A ∪ B = S) (hinter : A ∩ B = {γ 0, γ 1}) :
    ∃ u : E → E, IsPLHomeomorphOn u S S ∧ ¬ IsPLCirclePositive S u ∧
      (∀ t ∈ Icc (0 : ℝ) 1, u (γ t) = δ t) ∧
      (∀ t ∈ Icc (0 : ℝ) 1, u (δ t) = γ t) ∧ ∀ x ∈ S, u (u x) = x := by
  have hzero : (0 : ℝ) ∈ Icc (0 : ℝ) 1 := by norm_num
  have hone : (1 : ℝ) ∈ Icc (0 : ℝ) 1 := by norm_num
  have hhalf : ((1 : ℝ) / 2) ∈ Icc (0 : ℝ) 1 := by norm_num
  have hAB : A ≠ B := by
    intro h
    have hmid : γ ((1 : ℝ) / 2) ∈ A := hγ.bijOn.mapsTo hhalf
    have hmem : γ ((1 : ℝ) / 2) ∈ ({γ 0, γ 1} : Set E) := hinter ▸ mem_inter hmid (h ▸ hmid)
    rcases hmem with hh | hh
    · have hq := hγ.bijOn.injOn hhalf hzero hh
      norm_num at hq
    · have hh' : γ ((1 : ℝ) / 2) = γ 1 := hh
      have hq := hγ.bijOn.injOn hhalf hone hh'
      norm_num at hq
  have hAball : IsPLBall 1 A := (isPLBall_Icc zero_lt_one).of_isPLHomeomorphOn hγ
  have hBball : IsPLBall 1 B := (isPLBall_Icc zero_lt_one).of_isPLHomeomorphOn hδ
  have hf : IsPLHomeomorphOn (δ ∘ Function.invFunOn γ (Icc 0 1)) A B := hγ.symm.trans hδ
  have hf' : IsPLHomeomorphOn (γ ∘ Function.invFunOn δ (Icc 0 1)) B A := hδ.symm.trans hγ
  have hf0 : (δ ∘ Function.invFunOn γ (Icc 0 1)) (γ 0) = γ 0 := by
    change δ (Function.invFunOn γ (Icc 0 1) (γ 0)) = γ 0
    rw [hγ.bijOn.invOn_invFunOn.1 hzero, hδ0]
  have hf1 : (δ ∘ Function.invFunOn γ (Icc 0 1)) (γ 1) = γ 1 := by
    change δ (Function.invFunOn γ (Icc 0 1) (γ 1)) = γ 1
    rw [hγ.bijOn.invOn_invFunOn.1 hone, hδ1]
  have hf'0 : (γ ∘ Function.invFunOn δ (Icc 0 1)) (γ 0) = γ 0 := by
    change γ (Function.invFunOn δ (Icc 0 1) (γ 0)) = γ 0
    have h : Function.invFunOn δ (Icc 0 1) (γ 0) = 0 := by
      rw [← hδ0]
      exact hδ.bijOn.invOn_invFunOn.1 hzero
    rw [h]
  have hf'1 : (γ ∘ Function.invFunOn δ (Icc 0 1)) (γ 1) = γ 1 := by
    change γ (Function.invFunOn δ (Icc 0 1) (γ 1)) = γ 1
    have h : Function.invFunOn δ (Icc 0 1) (γ 1) = 1 := by
      rw [← hδ1]
      exact hδ.bijOn.invOn_invFunOn.1 hone
    rw [h]
  have heq : EqOn (δ ∘ Function.invFunOn γ (Icc 0 1)) (γ ∘ Function.invFunOn δ (Icc 0 1))
      (A ∩ B) := by
    rw [hinter]
    rintro x hx
    rcases hx with hx | hx
    · rw [show x = γ 0 from hx, hf0, hf'0]
    · have hx' : x = γ 1 := hx
      rw [hx', hf1, hf'1]
  have hsurj : SurjOn (δ ∘ Function.invFunOn γ (Icc 0 1)) (A ∩ B) (B ∩ A) := by
    have hBA : B ∩ A = ({γ 0, γ 1} : Set E) := by rw [inter_comm]; exact hinter
    rw [hBA]
    rintro x hx
    rcases hx with hx | hx
    · exact ⟨γ 0, by rw [hinter]; exact Or.inl rfl,
        by rw [hf0]; exact (show x = γ 0 from hx).symm⟩
    · have hx' : x = γ 1 := hx
      exact ⟨γ 1, by rw [hinter]; exact Or.inr rfl, by rw [hf1]; exact hx'.symm⟩
  obtain ⟨u, hu, huA, huB⟩ := exists_isPLHomeomorphOn_union hAball.isPolyhedron hBball.isPolyhedron
    hf hf' heq hsurj
  have huS : IsPLHomeomorphOn u S S := by
    rw [hunion, show B ∪ A = S by rw [union_comm]; exact hunion] at hu
    exact hu
  have huγ (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) : u (γ t) = δ t := by
    rw [huA (hγ.bijOn.mapsTo ht)]
    change δ (Function.invFunOn γ (Icc 0 1) (γ t)) = δ t
    rw [hγ.bijOn.invOn_invFunOn.1 ht]
  have huδ (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) : u (δ t) = γ t := by
    rw [huB (hδ.bijOn.mapsTo ht)]
    change γ (Function.invFunOn δ (Icc 0 1) (δ t)) = γ t
    rw [hδ.bijOn.invOn_invFunOn.1 ht]
  have hinvol : ∀ x ∈ S, u (u x) = x := by
    intro x hx
    have hxAB : x ∈ A ∪ B := hunion.symm ▸ hx
    rcases hxAB with hxA | hxB
    · obtain ⟨t, ht, rfl⟩ := hγ.bijOn.surjOn hxA
      rw [huγ t ht, huδ t ht]
    · obtain ⟨t, ht, rfl⟩ := hδ.bijOn.surjOn hxB
      rw [huδ t ht, huγ t ht]
  refine ⟨u, huS, ?_, huγ, huδ, hinvol⟩
  intro hpos
  have huimg : u '' A = B := by
    rw [image_congr huA]
    exact hf.image_eq
  have hu0 : u (γ 0) = γ 0 := by
    rw [huA (hγ.bijOn.mapsTo hzero)]
    exact hf0
  have hu1 : u (γ 1) = γ 1 := by
    rw [huA (hγ.bijOn.mapsTo hone)]
    exact hf1
  exact hAB ((huimg.symm.trans
    (image_arc_eq_of_isPLCirclePositive hγ hδ hδ0 hδ1 hunion hinter huS hpos hu0 hu1)).symm)

theorem exists_not_isPLCirclePositive_of_arc_decomposition [FiniteDimensional ℝ E]
    {S A B : Set E} {γ δ : ℝ → E} (hγ : IsPLHomeomorphOn γ (Icc 0 1) A)
    (hδ : IsPLHomeomorphOn δ (Icc 0 1) B) (hδ0 : δ 0 = γ 0) (hδ1 : δ 1 = γ 1)
    (hunion : A ∪ B = S) (hinter : A ∩ B = {γ 0, γ 1}) :
    ∃ u : E → E, IsPLHomeomorphOn u S S ∧ ¬ IsPLCirclePositive S u := by
  obtain ⟨u, hu, hnu, -⟩ := exists_isPLHomeomorphOn_reflection_of_arc_decomposition
    hγ hδ hδ0 hδ1 hunion hinter
  exact ⟨u, hu, hnu⟩

theorem exists_not_isPLCirclePositive_of_isPLSphere_one [FiniteDimensional ℝ E] {S : Set E}
    (hS : IsPLSphere 1 S) : ∃ u : E → E, IsPLHomeomorphOn u S S ∧ ¬ IsPLCirclePositive S u := by
  obtain ⟨p, hp, q, hq, hpq⟩ := exists_pair_ne_of_isPLSphere_one hS
  obtain ⟨A, B, γ, δ, hγ, hδ, hγ0, hγ1, hδ0, hδ1, hunion, hinter⟩ :=
    exists_arc_decomposition_of_isPLSphere_one hS hp hq hpq
  exact exists_not_isPLCirclePositive_of_arc_decomposition hγ hδ (hδ0.trans hγ0.symm)
    (hδ1.trans hγ1.symm) hunion (by rw [hinter, hγ0, hγ1])

end DifferentialGeometry.Topology.PiecewiseLinear
