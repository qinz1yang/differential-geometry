import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Seifert.ConeFoldDescentLocal

/-!
# Same-image pairs of the cone-fold descent

`FoldRel b y y'` says that an isometry `γ` of the `.hyperbolicProduct` coordinate metric carries
`y` to `y'` and satisfies `mirrorMap ∘ γ = twistMap b ∘ mirrorMap` on an open neighbourhood `U ⊆ N`
of `y` with `γ(U) ⊆ N` (`twistMap false = id`, `twistMap true = conjMap`). The relation is
reflexive, symmetric and closed under composition (`foldRel_refl`, `foldRel_symm`,
`foldRel_trans`, twists composing by `xor`). Its generators: the flip (globally, twist `conjMap`),
the fibre translations by integers (globally), the wall lifts `wallOneLift` on the band about wall
1 and on the apex disc, `wallTwoLift (q/p)` on the band about wall 2 (twist `conjMap`), and the
screws about the apex on the apex disc (`foldRel_flip`, `foldRel_fibreShift`, `foldRel_wallOne`,
`foldRel_wallTwo`, `foldRel_screw`). The reduction to the triangle and the classification of
same-image pairs are in `ConeFoldDescentReduce`.
-/

set_option autoImplicit false
noncomputable section
open Complex Set Filter Topology
open DifferentialGeometry DifferentialGeometry.Topology GC.Endpoint GC.GraphManifold GC.Geometry
open scoped ContDiff ComplexConjugate Manifold

universe u

namespace GC.Seifert

theorem eq_of_coe_logPoint_eq_of_two_eq {p p' : ModelCoordinates}
    (h1 : (logPoint p : ℂ) = logPoint p')
    (h2 : p 2 = p' 2) : p = p' := by
  have h := logCoords_logPoint p
  rw [UpperHalfPlane.ext h1, h2, logCoords_logPoint] at h
  exact h.symm

theorem eq_vertex_of_coneDisc_eq_zero {v w : ℂ} (hv : 0 < v.im) (hw : 0 < w.im)
    (h : coneDisc v w = 0) : w = v := by
  rw [coneDisc, div_eq_zero_iff] at h
  rcases h with h | h
  · exact sub_eq_zero.1 h
  · exact absurd h (sub_conj_ne_zero hv hw)

theorem im_ofReal_mul_cexp_ofReal_mul_I (r ψ : ℝ) :
    ((r : ℂ) * exp (ψ * I)).im = r * Real.sin ψ := by
  rw [Complex.im_ofReal_mul, Complex.exp_ofReal_mul_I_im]

theorem tubeOf_conj (c : ConeFilling) (w : ℂ) (s : ℝ) :
    c.tubeOf.{u} (conj w) (-s) = ConeShape.FoldData.conjMap (c.tubeOf w s) := by
  refine Prod.ext (ULift.ext ?_) ?_
  · change 3 * conj w * (Circle.exp (2 * Real.pi * c.a * -s) : ℂ) =
      conj (3 * w * (Circle.exp (2 * Real.pi * c.a * s) : ℂ))
    have he : (Circle.exp (2 * Real.pi * c.a * -s) : ℂ) =
        conj (Circle.exp (2 * Real.pi * c.a * s) : ℂ) := by
      rw [← Circle.coe_inv_eq_conj, ← Circle.exp_neg]
      congr 2
      ring
    rw [he, map_mul (starRingEnd ℂ), map_mul (starRingEnd ℂ), map_ofNat]
  · change Circle.exp (2 * Real.pi * c.p * -s) = (Circle.exp (2 * Real.pi * c.p * s))⁻¹
    rw [← Circle.exp_neg]
    congr 1
    ring

namespace ConeShape.FoldData

variable {σ : ConeShape} (D : σ.FoldData) (c : ConeFilling) (hθ : σ.θ₁ * c.p = Real.pi)

def twistMap (b : Bool) (x : PlaneLift.{u} × Circle) : PlaneLift.{u} × Circle :=
  cond b (conjMap x) x

@[simp] theorem twistMap_false (x : PlaneLift.{u} × Circle) : twistMap false x = x := rfl

@[simp] theorem twistMap_true (x : PlaneLift.{u} × Circle) : twistMap true x = conjMap x := rfl

theorem twistMap_twistMap (a b : Bool) (x : PlaneLift.{u} × Circle) :
    twistMap b (twistMap a x) = twistMap (xor a b) x := by
  cases a <;> cases b <;> simp [conjMap_conjMap]

theorem twistMap_invol (b : Bool) (x : PlaneLift.{u} × Circle) :
    twistMap b (twistMap b x) = x := by
  cases b <;> simp [conjMap_conjMap]

theorem conePoint_twistMap (b : Bool) (x : PlaneLift.{u} × Circle) :
    c.conePoint (twistMap b x) = cond b (conj (c.conePoint x)) (c.conePoint x) := by
  cases b
  · rfl
  · exact conePoint_conjMap c x

def FoldRel (b : Bool) (y y' : ModelCoordinates) : Prop :=
  ∃ γ : ModelCoordinates ≃ₘ⟮𝓡 3, 𝓡 3⟯ ModelCoordinates,
    Diffeomorph.pullbackMetric (coordinateModelMetric .hyperbolicProduct) γ =
      coordinateModelMetric .hyperbolicProduct ∧ γ y = y' ∧
    ∃ U : Set ModelCoordinates, IsOpen U ∧ y ∈ U ∧ U ⊆ D.descentDomain c hθ ∧
      MapsTo γ U (D.descentDomain c hθ) ∧
      ∀ z ∈ U, D.mirrorMap.{u} c (γ z) = twistMap b (D.mirrorMap c z)

theorem foldRel_refl {y : ModelCoordinates} (hy : y ∈ D.descentDomain c hθ) :
    D.FoldRel.{u} c hθ false y y :=
  ⟨Diffeomorph.refl (𝓡 3) ModelCoordinates ∞, Diffeomorph.pullbackMetric_refl _, rfl,
    D.descentDomain c hθ, (D.descentDomain c hθ).isOpen, hy, subset_rfl,
    fun _ hz => hz, fun _ _ => rfl⟩

theorem foldRel_symm {b : Bool} {y y' : ModelCoordinates} (h : D.FoldRel.{u} c hθ b y y') :
    D.FoldRel.{u} c hθ b y' y := by
  obtain ⟨γ, hγ, hy, U, hU, hyU, hUN, hmaps, hid⟩ := h
  refine ⟨γ.symm, pullbackMetric_symm_of_isometry hγ, by rw [← hy, γ.symm_apply_apply], γ '' U,
    γ.toHomeomorph.isOpenMap U hU, ⟨y, hyU, hy⟩, ?_, ?_, ?_⟩
  · rintro _ ⟨z, hz, rfl⟩
    exact hmaps hz
  · rintro _ ⟨z, hz, rfl⟩
    rw [γ.symm_apply_apply]
    exact hUN hz
  · rintro _ ⟨z, hz, rfl⟩
    rw [γ.symm_apply_apply, hid z hz, twistMap_invol]

theorem foldRel_trans {a b : Bool} {y y' y'' : ModelCoordinates} (h : D.FoldRel.{u} c hθ a y y')
    (h' : D.FoldRel.{u} c hθ b y' y'') : D.FoldRel.{u} c hθ (xor a b) y y'' := by
  obtain ⟨γ, hγ, hy, U, hU, hyU, hUN, hmaps, hid⟩ := h
  obtain ⟨γ', hγ', hy', U', hU', hyU', hUN', hmaps', hid'⟩ := h'
  refine ⟨γ.trans γ', pullbackMetric_trans_of_isometry hγ hγ', by
      rw [Diffeomorph.coe_trans, Function.comp_apply, hy, hy'], U ∩ γ ⁻¹' U',
    hU.inter (hU'.preimage γ.continuous), ⟨hyU, by rw [mem_preimage, hy]; exact hyU'⟩,
    fun z hz => hUN hz.1, fun z hz => hmaps' hz.2, fun z hz => ?_⟩
  rw [Diffeomorph.coe_trans, Function.comp_apply, hid' _ hz.2, hid z hz.1, twistMap_twistMap]

theorem mirrorMap_of_nonneg {p : ModelCoordinates} (h : 0 ≤ p 0) :
    D.mirrorMap.{u} c p = D.totalMap c p :=
  ite_eq_right (not_lt.2 h)

theorem mirrorMap_of_neg {p : ModelCoordinates} (h : p 0 < 0) :
    D.mirrorMap.{u} c p = conjMap (D.totalMap c (flipMap p)) :=
  ite_eq_left h

theorem totalMap_congr {p p' : ModelCoordinates} (h1 : (logPoint p : ℂ) = logPoint p') (n : ℤ)
    (h2 : p' 2 = p 2 + n) : D.totalMap.{u} c p' = D.totalMap c p := by
  have hp : logPoint p' = logPoint p := (UpperHalfPlane.ext h1).symm
  by_cases hv : (logPoint p : ℂ) = σ.vertexOne
  · rw [totalMap, totalMap, ite_eq_left hv, ite_eq_left (by rw [hp]; exact hv), tubeMap_eq_coneTube,
      tubeMap_eq_coneTube, hp, h2]
    exact c.tubeOf_add_int _ _ n
  · rw [totalMap, totalMap, ite_eq_right hv, ite_eq_right (by rw [hp]; exact hv), liftMap, liftMap]
    congr 1
    refine Prod.ext (ULift.ext (by rw [baseMap_fst, baseMap_fst, hp])) ?_
    rw [baseMap_snd, baseMap_snd, hp, h2, mul_add, Circle.exp_add]
    have : Circle.exp (2 * Real.pi * n) = 1 := by
      rw [mul_comm, Circle.exp_int_mul_two_pi]
    rw [this, mul_one]

theorem logPoint_re_eq' (p : ModelCoordinates) : (logPoint p : ℂ).re = p 0 := by
  rw [coe_logPoint']

theorem mirrorMap_congr {p p' : ModelCoordinates} (h1 : (logPoint p : ℂ) = logPoint p') (n : ℤ)
    (h2 : p' 2 = p 2 + n) : D.mirrorMap.{u} c p' = D.mirrorMap c p := by
  have h0 : p' 0 = p 0 := by rw [← logPoint_re_eq', ← logPoint_re_eq', h1]
  by_cases h : p 0 < 0
  · rw [D.mirrorMap_of_neg c h, D.mirrorMap_of_neg c (p := p') (by rwa [h0])]
    congr 1
    refine D.totalMap_congr c
      (by rw [coe_logPoint_flipMap (σ := σ), coe_logPoint_flipMap (σ := σ), h1]) (-n) ?_
    rw [flipMap_two, flipMap_two, h2]
    push_cast
    ring
  · rw [D.mirrorMap_of_nonneg c (not_lt.1 h),
      D.mirrorMap_of_nonneg c (p := p') (by rw [h0]; exact not_lt.1 h)]
    exact D.totalMap_congr c h1 n h2

theorem foldRel_fibreShift {y : ModelCoordinates} (hy : y ∈ D.descentDomain c hθ) (n : ℤ) :
    D.FoldRel.{u} c hθ false y (fibreShift n y) := by
  refine ⟨fibreShift n, pullbackMetric_fibreShift n, rfl, D.descentDomain c hθ,
    (D.descentDomain c hθ).isOpen, hy, subset_rfl, fun z hz => ?_, fun z _ => ?_⟩
  · change (logPoint (fibreShift n z) : ℂ) ∈ D.descentBase c hθ
    rw [logPoint_fibreShift]
    exact hz
  · rw [twistMap_false]
    exact D.mirrorMap_congr c (by rw [logPoint_fibreShift]) n (fibreShift_two _ _)

theorem mirrorMap_flip {p : ModelCoordinates} (hp : p ∈ D.descentDomain c hθ) :
    D.mirrorMap.{u} c (flipMap p) = conjMap (D.mirrorMap c p) := by
  replace hp : (logPoint p : ℂ) ∈ D.descentBase c hθ := hp
  rcases lt_trichotomy (p 0) 0 with h | h | h
  · have h' : 0 ≤ flipMap p 0 := by rw [flipMap_zero]; linarith
    rw [D.mirrorMap_of_neg c h, conjMap_conjMap, D.mirrorMap_of_nonneg c h']
  · have hz : (logPoint p : ℂ) ∈ D.patchZero :=
      D.mem_patchZero_of_re_nonpos c hθ (D.mem_patches_of_mem_descentBase c hθ hp
        (by rw [logPoint_re_eq', h])) (by rw [logPoint_re_eq', h])
    have h' : 0 ≤ flipMap p 0 := by rw [flipMap_zero, h, neg_zero]
    rw [D.mirrorMap_of_nonneg c h', D.mirrorMap_of_nonneg c h.ge, D.totalMap_eq_mirror c hz,
      conjMap_conjMap]
  · have h' : flipMap p 0 < 0 := by rw [flipMap_zero]; linarith
    rw [D.mirrorMap_of_neg c h', flipMap_flipMap, D.mirrorMap_of_nonneg c h.le]

theorem flipMap_mem_descentDomain {p : ModelCoordinates} (hp : p ∈ D.descentDomain c hθ) :
    flipMap p ∈ D.descentDomain c hθ := by
  change (logPoint (flipMap p) : ℂ) ∈ D.descentBase c hθ
  rw [coe_logPoint_flipMap]
  exact D.refl_zero_mem_descentBase c hθ hp

theorem foldRel_flip {y : ModelCoordinates} (hy : y ∈ D.descentDomain c hθ) :
    D.FoldRel.{u} c hθ true y (flipMap y) := by
  refine ⟨foldFlip 0, pullbackMetric_foldFlip 0, foldFlip_zero_apply y, D.descentDomain c hθ,
    (D.descentDomain c hθ).isOpen, hy, subset_rfl, fun z hz => ?_, fun z hz => ?_⟩
  · rw [foldFlip_zero_apply]
    exact D.flipMap_mem_descentDomain c hθ hz
  · rw [foldFlip_zero_apply, twistMap_true]
    exact D.mirrorMap_flip c hθ hz

theorem patches_subset_descentBase : D.patches c hθ ⊆ D.descentBase c hθ := fun _ hz => Or.inl hz

theorem mem_descentDomain_of_patches {p : ModelCoordinates}
    (hp : (logPoint p : ℂ) ∈ D.patches c hθ) : p ∈ D.descentDomain c hθ :=
  D.patches_subset_descentBase c hθ hp

theorem coneDisc_refl_one_norm (z : ℂ) :
    ‖coneDisc σ.vertexOne (σ.refl 1 z)‖ = ‖coneDisc σ.vertexOne z‖ := by
  rw [σ.coneDisc_vertexOne_refl_one, Complex.norm_conj]

theorem refl_one_mem_patchDisc {z : ℂ} (hz : z ∈ D.patchDisc c hθ) :
    σ.refl 1 z ∈ D.patchDisc c hθ :=
  ⟨σ.refl_im_pos hz.1 1, by rw [coneDisc_refl_one_norm]; exact hz.2⟩

theorem re_lt_of_mem_patchOne {z : ℂ} (hz : z ∈ D.patchOne) : 0 < z.re := hz.2.1

theorem mirrorMap_wallOneLift {p : ModelCoordinates}
    (hp : (logPoint p : ℂ) ∈ D.patchOne ∪ D.patchDisc c hθ) :
    D.mirrorMap.{u} c (σ.wallOneLift p) = conjMap (D.mirrorMap c p) := by
  have hb := σ.coe_logPoint_wallOneLift p
  have hre : 0 ≤ p 0 := by
    rw [← logPoint_re_eq']
    rcases hp with h | h
    · exact h.2.1.le
    · exact (D.re_pos_of_mem_patchDisc c hθ h).le
  have hre' : 0 ≤ σ.wallOneLift p 0 := by
    rw [← logPoint_re_eq', hb]
    rcases hp with h | h
    · exact (D.refl_one_mem_patchOne h).2.1.le
    · exact (D.re_pos_of_mem_patchDisc c hθ (D.refl_one_mem_patchDisc c hθ h)).le
  rw [D.mirrorMap_of_nonneg c hre, D.mirrorMap_of_nonneg c hre']
  by_cases hd : (logPoint p : ℂ) ∈ D.patchDisc c hθ
  · have hd' : (logPoint (σ.wallOneLift p) : ℂ) ∈ D.patchDisc c hθ := by
      rw [hb]
      exact D.refl_one_mem_patchDisc c hθ hd
    rw [D.totalMap_eq_tubeMap_of_mem_patchDisc c hθ hd,
      D.totalMap_eq_tubeMap_of_mem_patchDisc c hθ hd',
      tubeMap_eq_coneTube, tubeMap_eq_coneTube, ConeFilling.coneTube, ConeFilling.coneTube, hb,
      σ.coneDisc_vertexOne_refl_one, σ.wallOneLift_two, tubeOf_conj]
  · have h1 : (logPoint p : ℂ) ∈ D.patchOne := hp.resolve_right hd
    have hv := D.ne_vertexOne_of_mem_patchOne h1
    have hv' : (logPoint (σ.wallOneLift p) : ℂ) ≠ σ.vertexOne := by
      rw [hb]
      exact D.refl_ne_vertexOne_of_mem_patchOne h1
    rw [totalMap, totalMap, ite_eq_right hv, ite_eq_right hv', liftMap, liftMap,
      ← c.coneLift_conjMap]
    congr 1
    refine Prod.ext (ULift.ext ?_) ?_
    · change D.f (logPoint (σ.wallOneLift p)) = conj (D.f (logPoint p))
      rw [hb]
      exact D.f_refl 1 _ h1.2.2.2.2.2.1
    · change Circle.exp (2 * Real.pi * σ.wallOneLift p 2) *
          (σ.foldPhase c.q (logPoint (σ.wallOneLift p)))⁻¹ =
        (Circle.exp (2 * Real.pi * p 2) * (σ.foldPhase c.q (logPoint p))⁻¹)⁻¹
      rw [hb, σ.foldPhase_refl_one c.q h1.1 hv h1.2.2.2.2.2.2.1 h1.2.2.2.2.2.2.2,
        σ.wallOneLift_two, mul_inv, inv_inv, ← Circle.exp_neg]
      congr 2
      ring

theorem foldRel_wallOne {y : ModelCoordinates}
    (hy : (logPoint y : ℂ) ∈ D.patchOne ∪ D.patchDisc c hθ) :
    D.FoldRel.{u} c hθ true y (σ.wallOneLift y) := by
  have hO : IsOpen {p : ModelCoordinates | (logPoint p : ℂ) ∈ D.patchOne ∪ D.patchDisc c hθ} :=
    isOpen_logPoint_preimage (D.isOpen_patchOne.union (D.isOpen_patchDisc c hθ))
  have hsub : ∀ p : ModelCoordinates, (logPoint p : ℂ) ∈ D.patchOne ∪ D.patchDisc c hθ →
      p ∈ D.descentDomain c hθ := by
    rintro p (h | h)
    · exact D.mem_descentDomain_of_patches c hθ (Or.inl (Or.inl (Or.inr h)))
    · exact D.mem_descentDomain_of_patches c hθ (Or.inr h)
  refine ⟨σ.wallOneLift, σ.pullbackMetric_wallOneLift, rfl, _, hO, hy, fun p hp => hsub p hp,
    fun p hp => hsub _ ?_, fun p hp => D.mirrorMap_wallOneLift c hθ hp⟩
  rw [σ.coe_logPoint_wallOneLift]
  rcases hp with h | h
  · exact Or.inl (D.refl_one_mem_patchOne h)
  · exact Or.inr (D.refl_one_mem_patchDisc c hθ h)

theorem circleExp_wallTwo (hθ : σ.θ₁ * c.p = Real.pi) :
    Circle.exp (c.q * (2 * σ.θ₁)) = Circle.exp (2 * Real.pi * (c.q / c.p)) := by
  congr 1
  have hp : (c.p : ℝ) ≠ 0 := c.p_ne_zero
  rw [show σ.θ₁ = Real.pi / c.p by rw [← hθ]; field_simp]
  field_simp

theorem mirrorMap_wallTwoLift (hθ : σ.θ₁ * c.p = Real.pi) (hσ : σ.θ₂ = 0) {p : ModelCoordinates}
    (hp : (logPoint p : ℂ) ∈ D.patchTwo) :
    D.mirrorMap.{u} c (ConeShape.wallTwoLift (c.q / c.p) p) = conjMap (D.mirrorMap c p) := by
  have hb := σ.coe_logPoint_wallTwoLift hσ (c.q / c.p) p
  have hre : 0 ≤ p 0 := by rw [← logPoint_re_eq']; exact hp.2.1.le
  have hre' : 0 ≤ ConeShape.wallTwoLift (c.q / c.p) p 0 := by
    rw [← logPoint_re_eq', hb]
    exact hp.2.2.2.1.le
  rw [D.mirrorMap_of_nonneg c hre, D.mirrorMap_of_nonneg c hre']
  have hv := D.ne_vertexOne_of_mem_patchTwo hp
  have hv' : (logPoint (ConeShape.wallTwoLift (c.q / c.p) p) : ℂ) ≠ σ.vertexOne := by
    rw [hb]
    exact D.refl_ne_vertexOne_of_mem_patchTwo hp
  rw [totalMap, totalMap, ite_eq_right hv, ite_eq_right hv', liftMap, liftMap,
    ← c.coneLift_conjMap]
  congr 1
  refine Prod.ext (ULift.ext ?_) ?_
  · change D.f (logPoint (ConeShape.wallTwoLift (c.q / c.p) p)) = conj (D.f (logPoint p))
    rw [hb]
    exact D.f_refl 2 _ hp.2.2.2.2.2.1
  · change Circle.exp (2 * Real.pi * ConeShape.wallTwoLift (c.q / c.p) p 2) *
        (σ.foldPhase c.q (logPoint (ConeShape.wallTwoLift (c.q / c.p) p)))⁻¹ =
      (Circle.exp (2 * Real.pi * p 2) * (σ.foldPhase c.q (logPoint p))⁻¹)⁻¹
    rw [hb, σ.foldPhase_refl_two c.q hp.1 hv hp.2.2.2.2.2.2.1 hp.2.2.2.2.2.2.2,
      ConeShape.wallTwoLift_two, circleExp_wallTwo (σ := σ) c hθ, mul_inv, inv_inv, mul_inv,
      inv_inv,
      ← mul_assoc, ← Circle.exp_neg, ← Circle.exp_add, ← Circle.exp_neg]
    congr 2
    ring

theorem foldRel_wallTwo (hσ : σ.θ₂ = 0) {y : ModelCoordinates}
    (hy : (logPoint y : ℂ) ∈ D.patchTwo) :
    D.FoldRel.{u} c hθ true y (ConeShape.wallTwoLift (c.q / c.p) y) := by
  have hO : IsOpen {p : ModelCoordinates | (logPoint p : ℂ) ∈ D.patchTwo} :=
    isOpen_logPoint_preimage D.isOpen_patchTwo
  refine ⟨ConeShape.wallTwoLift (c.q / c.p), ConeShape.pullbackMetric_wallTwoLift _, rfl, _, hO,
    hy, fun p hp => D.mem_descentDomain_of_patches c hθ (Or.inl (Or.inr hp)),
    fun p hp => D.mem_descentDomain_of_patches c hθ (Or.inl (Or.inr ?_)),
    fun p hp => D.mirrorMap_wallTwoLift c hθ hσ hp⟩
  rw [σ.coe_logPoint_wallTwoLift hσ]
  exact D.refl_two_mem_patchTwo hp

theorem coneDisc_screw (k : ℤ) (t : ℝ) (p : ModelCoordinates) :
    coneDisc σ.vertexOne (logPoint (screwLift σ.vertexOne σ.vertexOne_im_pos
      (Real.pi * k / c.p) t p)) =
      (Circle.exp (2 * Real.pi * k / c.p) : ℂ) * coneDisc σ.vertexOne (logPoint p) := by
  rw [coneDisc_screwLift, Circle.coe_exp]
  congr 2
  push_cast
  ring

theorem screw_mem_patchDisc (k : ℤ) (t : ℝ) {p : ModelCoordinates}
    (hp : (logPoint p : ℂ) ∈ D.patchDisc c hθ) :
    (logPoint (screwLift σ.vertexOne σ.vertexOne_im_pos (Real.pi * k / c.p) t p) : ℂ) ∈
      D.patchDisc c hθ := by
  refine ⟨logPoint_im_pos _, ?_⟩
  rw [coneDisc_screw (σ := σ) c k t p, norm_mul, Circle.norm_coe, one_mul]
  exact hp.2

theorem mirrorMap_screw (k n : ℤ) {p : ModelCoordinates}
    (hp : (logPoint p : ℂ) ∈ D.patchDisc c hθ) :
    D.mirrorMap.{u} c (screwLift σ.vertexOne σ.vertexOne_im_pos (Real.pi * k / c.p)
      (k * c.q / c.p + n) p) = D.mirrorMap c p := by
  have hp' := D.screw_mem_patchDisc c hθ k (k * c.q / c.p + n) hp
  have h1 : 0 ≤ p 0 := by
    rw [← logPoint_re_eq']
    exact (D.re_pos_of_mem_patchDisc c hθ hp).le
  have h2 : 0 ≤ screwLift σ.vertexOne σ.vertexOne_im_pos (Real.pi * k / c.p)
      (k * c.q / c.p + n) p 0 := by
    rw [← logPoint_re_eq']
    exact (D.re_pos_of_mem_patchDisc c hθ hp').le
  rw [D.mirrorMap_of_nonneg c h1, D.mirrorMap_of_nonneg c h2,
    D.totalMap_eq_tubeMap_of_mem_patchDisc c hθ hp, D.totalMap_eq_tubeMap_of_mem_patchDisc c hθ hp',
    tubeMap_eq_coneTube, tubeMap_eq_coneTube, ConeFilling.coneTube, ConeFilling.coneTube,
    coneDisc_screw (σ := σ) c k, screwLift_two]
  rw [show p 2 + (k * c.q / c.p + n) = p 2 + (k * c.q + n * c.p) / c.p by
    have := c.p_ne_zero
    field_simp]
  exact c.tubeOf_rotate _ _ k n

theorem foldRel_screw (k n : ℤ) {y : ModelCoordinates} (hy : (logPoint y : ℂ) ∈ D.patchDisc c hθ) :
    D.FoldRel.{u} c hθ false y (screwLift σ.vertexOne σ.vertexOne_im_pos (Real.pi * k / c.p)
      (k * c.q / c.p + n) y) := by
  have hO : IsOpen {p : ModelCoordinates | (logPoint p : ℂ) ∈ D.patchDisc c hθ} :=
    isOpen_logPoint_preimage (D.isOpen_patchDisc c hθ)
  refine ⟨_, pullbackMetric_screwLift _ _ _ _, rfl, _, hO, hy,
    fun p hp => D.mem_descentDomain_of_patches c hθ (Or.inr hp),
    fun p hp => D.mem_descentDomain_of_patches c hθ (Or.inr (D.screw_mem_patchDisc c hθ k _ hp)),
    fun p hp => ?_⟩
  rw [twistMap_false]
  exact D.mirrorMap_screw c hθ k n hp

end ConeShape.FoldData

end GC.Seifert
