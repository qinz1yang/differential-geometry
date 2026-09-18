import DifferentialGeometry.Topology.PiecewiseLinear.CircleAnnulusIsotopy
import DifferentialGeometry.Topology.LoopSpace.CircleLiftOrientation
import DifferentialGeometry.Topology.LoopSpace.InjectiveLoop

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

theorem exists_loopCircle_param_of_arc_decomposition [FiniteDimensional ℝ E]
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
      refine ⟨((r / 2 : ℝ) : loopCircle), ⟨r / 2, ⟨by linarith [hr.1], by linarith [hr.2]⟩, rfl⟩, ?_⟩
      rw [hlow (r / 2) ⟨by linarith [hr.1], by linarith [hr.2]⟩]
      ring_nf
  · have h := hlow 0 (by norm_num)
    rw [h]
    norm_num
  · have h := hlow ((1 : ℝ) / 2) (by norm_num)
    rw [h]
    norm_num

theorem exists_pair_ne_of_isPLSphere_one [FiniteDimensional ℝ E] {S : Set E}
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
  change Function.invFunOn g univ (u (v (g θ))) = Function.invFunOn g univ (u (g (circleConj g v θ)))
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

omit [NormedSpace ℝ E] in
theorem continuous_circleConj {S : Set E} {g : loopCircle → E} (hgc : Continuous g)
    (hgb : BijOn g univ S) {u : E → E} (hcu : ContinuousOn u S) (hmu : MapsTo u S S) :
    Continuous (circleConj g u) := by
  have hmaps : ∀ θ : loopCircle, g θ ∈ S := fun θ => hgb.mapsTo (mem_univ θ)
  set e : loopCircle → ↥S := fun θ => ⟨g θ, hmaps θ⟩ with hedef
  have hec : Continuous e := hgc.subtype_mk _
  have hebij : Function.Bijective e := by
    constructor
    · intro a b hab
      exact hgb.injOn (mem_univ a) (mem_univ b) (congrArg Subtype.val hab)
    · rintro ⟨y, hy⟩
      obtain ⟨θ, -, hθ⟩ := hgb.surjOn hy
      exact ⟨θ, Subtype.ext hθ⟩
  set he : loopCircle ≃ₜ ↥S :=
    Continuous.homeoOfEquivCompactToT2 (f := Equiv.ofBijective e hebij) hec with hhedef
  have hinvval : ∀ y : ↥S, Function.invFunOn g univ (y : E) = he.symm y := by
    intro y
    have h1 : g (he.symm y) = (y : E) := congrArg Subtype.val (he.apply_symm_apply y)
    have h2 : Function.invFunOn g univ (g (he.symm y)) = he.symm y :=
      hgb.injOn.leftInvOn_invFunOn (mem_univ _)
    rw [← h1, h2]
  have hcomp : circleConj g u = fun θ => he.symm ⟨u (g θ), hmu (hmaps θ)⟩ := by
    funext θ
    exact hinvval ⟨u (g θ), hmu (hmaps θ)⟩
  rw [hcomp]
  exact he.continuous_symm.comp ((hcu.comp_continuous hgc hmaps).subtype_mk _)

def IsPLCirclePositive (S : Set E) (u : E → E) : Prop :=
  ∀ g : loopCircle → E, Continuous g → BijOn g univ S → HasIncreasingCircleLift (circleConj g u)

omit [NormedSpace ℝ E] in
theorem isPLCirclePositive_id {S : Set E} : IsPLCirclePositive S (id : E → E) :=
  fun _ _ hgb => hasIncreasingCircleLift_id.congr fun θ => circleConj_id hgb θ

omit [NormedSpace ℝ E] in
theorem IsPLCirclePositive.comp {S : Set E} {u v : E → E} (hu : IsPLCirclePositive S u)
    (hv : IsPLCirclePositive S v) (hmv : MapsTo v S S) :
    IsPLCirclePositive S (u ∘ v) := fun g hgc hgb =>
  ((hu g hgc hgb).comp (hv g hgc hgb)).congr fun θ => circleConj_comp hgb hmv θ

theorem isPLCirclePositive_of_three_fixed [FiniteDimensional ℝ E] {S : Set E} {u : E → E}
    (hcu : ContinuousOn u S) (hbu : BijOn u S S) {x y z : E} (hx : x ∈ S) (hy : y ∈ S) (hz : z ∈ S)
    (hxy : x ≠ y) (hxz : x ≠ z) (hyz : y ≠ z)
    (hux : u x = x) (huy : u y = y) (huz : u z = z) : IsPLCirclePositive S u := by
  intro g hgc hgb
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
    (hξ : IsPLHomeomorphOn ξ (Icc 0 1) B) (hBS : B ⊆ S) {r : E → E}
    (hr : IsPLHomeomorphOn r S S) (hrB : EqOn r id B) : IsPLCirclePositive S r := by
  have hm0 : ξ 0 ∈ B := hξ.bijOn.mapsTo (by norm_num)
  have hmh : ξ ((1 : ℝ) / 2) ∈ B := hξ.bijOn.mapsTo (by norm_num)
  have hm1 : ξ 1 ∈ B := hξ.bijOn.mapsTo (by norm_num)
  refine isPLCirclePositive_of_three_fixed hr.isPiecewiseAffineOn.continuousOn hr.bijOn
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
      hpp.symm, isPLCirclePositive_id⟩
  · obtain ⟨A, B, ε, ξ, hε, hξ, hunion, hinter, hpA, hp'A⟩ :=
      exists_arc_pair_interior_of_isPLSphere_one hS hp hp' hpp
    obtain ⟨r, hr, hrid, hrp, hrB⟩ := exists_isPLPseudoIsotopicToId_map_eq_of_arc hε
      ((isPLBall_Icc zero_lt_one).of_isPLHomeomorphOn hξ).isPolyhedron hunion hinter hpA hp'A
    exact ⟨r, hr, hrid, hrp,
      isPLCirclePositive_of_eqOn_arc hξ (hunion ▸ subset_union_right) hr hrB⟩

theorem image_arc_eq_of_isPLCirclePositive [FiniteDimensional ℝ E]
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
  have himg := image_coe_Icc_zero_half_eq_of_hasIncreasingCircleLift (hpos g hgc hgb)
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
    isPLCirclePositive_of_eqOn_arc hξ₂ (hun₂ ▸ subset_union_right) hr₂ hr₂B
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

end DifferentialGeometry.Topology.PiecewiseLinear
