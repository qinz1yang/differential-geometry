import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Seifert.FilledPantsGeometryReduce

/-!
# Classification of the pairs of the two-cone fold

Lane A5 (design `docs/geometrization/handoffs/20261004-design-a5-filled-pants-assembly.md`, §3.3,
with review 21 §4.3). Two points of the fold domain with the same image under `foldMap` are related
by `FoldRel` (`foldRel_of_foldMap_eq`). Each point is first moved over the doubled triangle
(`exists_foldRel_domain`) and then into a normal position: over `T` minus its vertices, over
`σ₀T \ T` away from `σ₀ v₁`, or over a vertex `v₁`, `v₂` (`exists_foldRel_normal`). Points in
normal position with the same image differ by a deck translation (same base point, by injectivity
of the punctured chart, of `f` on `T` and of `eC` modulo `ℤ`), by a side pairing `γᵢ` followed by
a deck translation (the wall case of A4Q's `pairRel_of_foldExt_eq`), or, over a vertex, by a power
of the screw `Sᵢ` followed by a deck translation (Bézout `pᵢ bᵢ - aᵢ qᵢ = 1`).
-/

set_option autoImplicit false

noncomputable section
open Set Complex Filter
open DifferentialGeometry DifferentialGeometry.Topology GC.Endpoint GC.GraphManifold GC.Geometry
open scoped Topology ComplexConjugate ContDiff Manifold

universe u

namespace GC.Seifert

namespace TwoConeFold

theorem FoldRel.map_eq {M : Type*} {g : SmoothRiemannianMetric (𝓡 3) ModelCoordinates}
    {N : Set ModelCoordinates} {F : ModelCoordinates → M} {y y' : ModelCoordinates}
    (h : FoldRel g N F y y') : F y' = F y := by
  obtain ⟨γ, -, hyy, U, hyU, -, -, hF⟩ := h
  rw [← hyy]
  exact hF y hyU

theorem FoldRel.mem {M : Type*} {g : SmoothRiemannianMetric (𝓡 3) ModelCoordinates}
    {N : Set ModelCoordinates} {F : ModelCoordinates → M} {y y' : ModelCoordinates}
    (h : FoldRel g N F y y') : y' ∈ N := by
  obtain ⟨γ, -, hyy, U, hyU, -, hmaps, -⟩ := h
  rw [← hyy]
  exact hmaps hyU

theorem exists_int_of_eC_eq {s t : ℝ} (h : eC s = eC t) : ∃ m : ℤ, s = t + m := by
  obtain ⟨m, hm⟩ := Circle.exp_eq_exp.1 h
  refine ⟨m, mul_left_cancel₀ (by positivity : (2 * Real.pi) ≠ 0) ?_⟩
  rw [hm]
  ring

theorem vertex_bezout {P : ℕ} {q a b : ℤ} (hP : P ≠ 0) (hb : (P : ℤ) * b - a * q = 1) (m : ℤ) :
    ∃ j : ℕ, ∃ t : ℤ, (t : ℝ) * P - j * q = -m := by
  refine ⟨((-m) * a + |(-m) * a| * P).toNat, (-m) * b + |(-m) * a| * q, ?_⟩
  have hP1 : (1 : ℤ) ≤ P := by exact_mod_cast Nat.one_le_iff_ne_zero.2 hP
  have hj0 : 0 ≤ (-m) * a + |(-m) * a| * P := by
    nlinarith [neg_abs_le ((-m) * a), abs_nonneg ((-m) * a)]
  have hjz : ((((-m) * a + |(-m) * a| * P).toNat : ℕ) : ℤ) = (-m) * a + |(-m) * a| * P :=
    Int.toNat_of_nonneg hj0
  have h : ((-m) * b + |(-m) * a| * q) * (P : ℤ) -
      ((((-m) * a + |(-m) * a| * P).toNat : ℕ) : ℤ) * q = -m := by
    rw [hjz]
    linear_combination (-m) * hb
  exact_mod_cast h

namespace Fold

open ConeShape

section Vertices

variable {σ : ConeShape}

theorem refl_one_vertexOne : σ.refl 1 σ.vertexOne = σ.vertexOne :=
  σ.refl_of_wallSide_eq_zero σ.vertexOne_im_pos (i := 1)
    (show σ.width - σ.vertexOne.re = 0 by rw [vertexOne_re, sub_self])

theorem refl_two_vertexOne : σ.refl 2 σ.vertexOne = σ.vertexOne :=
  σ.refl_of_wallSide_eq_zero σ.vertexOne_im_pos (wallSide_two_vertexOne' σ)

theorem wallSide_two_vertexTwo : σ.wallSide 2 σ.vertexTwo = 0 := by
  change (σ.vertexTwo.re - σ.centre) ^ 2 + σ.vertexTwo.im ^ 2 - 1 / 16 = 0
  rw [vertexTwo_re, vertexTwo_im]
  unfold centre
  nlinarith [Real.sin_sq_add_cos_sq σ.θ₂]

theorem refl_zero_vertexTwo (hθ : 0 < σ.θ₂) : σ.refl 0 σ.vertexTwo = σ.vertexTwo :=
  σ.refl_of_wallSide_eq_zero (vertexTwo_mem_triangle' σ hθ).1 (i := 0)
    (show σ.vertexTwo.re = 0 from vertexTwo_re σ)

theorem refl_two_vertexTwo (hθ : 0 < σ.θ₂) : σ.refl 2 σ.vertexTwo = σ.vertexTwo :=
  σ.refl_of_wallSide_eq_zero (vertexTwo_mem_triangle' σ hθ).1 wallSide_two_vertexTwo

theorem refl_zero_ne_vertexTwo (hθ : 0 < σ.θ₂) {z : ℂ} (hz : z ∉ σ.triangle) :
    σ.refl 0 z ≠ σ.vertexTwo := by
  intro h
  apply hz
  rw [← σ.refl_zero_refl_zero z, h, refl_zero_vertexTwo hθ]
  exact vertexTwo_mem_triangle' σ hθ

end Vertices

variable {W : CompactCarrier.{u}} {d : SeifertData} (C : SeifertBlockCharts W d)
  (m₁ m₂ : Fin d.fillingCount) (hk : d.k = 3)
  (hj : ∀ m : Fin d.fillingCount, (C.port (.inr m)).val ≠ 0)
  (hp : ∀ m : Fin d.fillingCount, 0 < (d.fillingSlope m).1)
  {σ : ConeShape} (D : σ.FoldData)
  (hθ₁ : σ.θ₁ * (chartNumbers C m₁ m₂).p₁ = Real.pi)
  (hθ₂ : σ.θ₂ * (chartNumbers C m₁ m₂).p₂ = Real.pi)
  (hc₁ : C.tubeCentre m₁ = ((3 / 2 : ℝ) : ℂ)) (hc₂ : C.tubeCentre m₂ = ((-(3 / 2) : ℝ) : ℂ))

section Values

include hj hp hc₁ hc₂ in
theorem foldMap_of_triangle {x : ModelCoordinates} (hx : zOf x ∈ σ.triangle)
    (hx1 : zOf x ≠ σ.vertexOne) (hx2 : zOf x ≠ σ.vertexTwo) :
    liftT D (chartNumbers C m₁ m₂) x ∈ C.puncturedDomain ∧
      foldMap C m₁ m₂ hk D hθ₁ hθ₂ x = C.puncturedChart hk (liftT D (chartNumbers C m₁ m₂) x) :=
  ⟨liftT_mem_puncturedDomain C m₁ m₂ hk hp D hθ₁ hθ₂ hc₁ hc₂
      (triangle_diff_subset_mainSet D hθ₁ hθ₂ hx hx1 hx2),
    foldMap_of_main C m₁ m₂ hk hj hp D hθ₁ hθ₂ hc₁ hc₂
      (triangle_diff_subset_mainSet D hθ₁ hθ₂ hx hx1 hx2)⟩

theorem mem_mirrorMain {x : ModelCoordinates} (hx : σ.refl 0 (zOf x) ∈ σ.triangle)
    (hx1 : σ.refl 0 (zOf x) ≠ σ.vertexOne) (hx2 : σ.refl 0 (zOf x) ≠ σ.vertexTwo) :
    zOf x ∈ mirrorSet σ (mainSet D hθ₁ hθ₂) :=
  ⟨zOf_im_pos x, triangle_diff_subset_mainSet D hθ₁ hθ₂ hx hx1 hx2⟩

include hj hp hc₁ hc₂ in
theorem foldMap_of_mirror {x : ModelCoordinates} (hx : σ.refl 0 (zOf x) ∈ σ.triangle)
    (hx1 : σ.refl 0 (zOf x) ≠ σ.vertexOne) (hx2 : σ.refl 0 (zOf x) ≠ σ.vertexTwo) :
    liftS D (chartNumbers C m₁ m₂) x ∈ C.puncturedDomain ∧
      foldMap C m₁ m₂ hk D hθ₁ hθ₂ x = C.puncturedChart hk (liftS D (chartNumbers C m₁ m₂) x) :=
  ⟨liftS_mem_puncturedDomain C m₁ m₂ hk hp D hθ₁ hθ₂ hc₁ hc₂
      (mem_mirrorMain C m₁ m₂ D hθ₁ hθ₂ hx hx1 hx2),
    foldMap_of_mirrorMain C m₁ m₂ hk hj hp D hθ₁ hθ₂ hc₁ hc₂
      (mem_mirrorMain C m₁ m₂ D hθ₁ hθ₂ hx hx1 hx2)⟩

theorem foldMap_of_vertexOne {x : ModelCoordinates} (hx : zOf x = σ.vertexOne) :
    foldMap C m₁ m₂ hk D hθ₁ hθ₂ x = C.tubeMap m₁ (0, eC ((chartNumbers C m₁ m₂).p₁ *
      (x 2 + betaOne D (chartNumbers C m₁ m₂) σ.vertexOne))) := by
  rw [foldMap_of_discOne C m₁ m₂ hk D hθ₁ hθ₂ (by rw [hx]; exact vertexOne_mem_discOne D hθ₁)]
  unfold tubeOne
  rw [hx, coneDisc_self, zero_mul]

theorem foldMap_of_vertexTwo {x : ModelCoordinates} (hx : zOf x = σ.vertexTwo) :
    foldMap C m₁ m₂ hk D hθ₁ hθ₂ x = C.tubeMap m₂ (0, eC ((chartNumbers C m₁ m₂).p₂ *
      (x 2 + betaTwo D (chartNumbers C m₁ m₂) σ.vertexTwo))) := by
  rw [foldMap_of_discTwo C m₁ m₂ hk D hθ₁ hθ₂ (by rw [hx]; exact vertexTwo_mem_discTwo D hθ₂)]
  unfold tubeTwo
  rw [hx, coneDisc_self, mul_zero, zero_mul]

end Values

section Pairs

theorem norm_zero_lt (w : Circle) : ‖((0 : ℂ), w).1‖ < 1 + C.ε := by
  change ‖(0 : ℂ)‖ < 1 + C.ε
  rw [norm_zero]
  linarith [C.ε_pos]

include hj hp hc₁ hc₂ in
theorem eq_moveTrans_of_triangle {x x' : ModelCoordinates} (hx : zOf x ∈ σ.triangle)
    (hx1 : zOf x ≠ σ.vertexOne) (hx2 : zOf x ≠ σ.vertexTwo) (hx' : zOf x' ∈ σ.triangle)
    (hx1' : zOf x' ≠ σ.vertexOne) (hx2' : zOf x' ≠ σ.vertexTwo)
    (h : foldMap C m₁ m₂ hk D hθ₁ hθ₂ x = foldMap C m₁ m₂ hk D hθ₁ hθ₂ x') :
    ∃ k : ℤ, x' = moveTrans k x := by
  obtain ⟨hu, hF⟩ := foldMap_of_triangle C m₁ m₂ hk hj hp D hθ₁ hθ₂ hc₁ hc₂ hx hx1 hx2
  obtain ⟨hu', hF'⟩ := foldMap_of_triangle C m₁ m₂ hk hj hp D hθ₁ hθ₂ hc₁ hc₂ hx' hx1' hx2'
  rw [hF, hF'] at h
  have hl := C.puncturedChart_injOn hk hj hp hu hu' h
  have hf : D.f (zOf x) = D.f (zOf x') := congrArg Prod.fst hl
  have hz : zOf x = zOf x' := D.bijOn_f.injOn hx hx' hf
  have h2 : eC (x 2) * basePhase (chartNumbers C m₁ m₂).k₁ (chartNumbers C m₁ m₂).k₂
      (D.f (zOf x)) = eC (x' 2) * basePhase (chartNumbers C m₁ m₂).k₁
        (chartNumbers C m₁ m₂).k₂ (D.f (zOf x')) := congrArg Prod.snd hl
  rw [hf] at h2
  obtain ⟨k, hk'⟩ := exists_int_of_eC_eq (mul_right_cancel h2).symm
  exact ⟨k, point_ext (by rw [zOf_moveTrans]; exact hz.symm) (by rw [moveTrans_two]; exact hk')⟩

include hj hp hc₁ hc₂ in
theorem eq_moveTrans_of_mirror {x x' : ModelCoordinates} (hx : σ.refl 0 (zOf x) ∈ σ.triangle)
    (hx1 : σ.refl 0 (zOf x) ≠ σ.vertexOne) (hx2 : σ.refl 0 (zOf x) ≠ σ.vertexTwo)
    (hx' : σ.refl 0 (zOf x') ∈ σ.triangle) (hx1' : σ.refl 0 (zOf x') ≠ σ.vertexOne)
    (hx2' : σ.refl 0 (zOf x') ≠ σ.vertexTwo)
    (h : foldMap C m₁ m₂ hk D hθ₁ hθ₂ x = foldMap C m₁ m₂ hk D hθ₁ hθ₂ x') :
    ∃ k : ℤ, x' = moveTrans k x := by
  obtain ⟨hu, hF⟩ := foldMap_of_mirror C m₁ m₂ hk hj hp D hθ₁ hθ₂ hc₁ hc₂ hx hx1 hx2
  obtain ⟨hu', hF'⟩ := foldMap_of_mirror C m₁ m₂ hk hj hp D hθ₁ hθ₂ hc₁ hc₂ hx' hx1' hx2'
  rw [hF, hF'] at h
  have hl := congrArg conjPair (C.puncturedChart_injOn hk hj hp hu hu' h)
  unfold liftS at hl
  rw [conjPair_conjPair, conjPair_conjPair] at hl
  have hf : D.f (zOf (flipMap (chartNumbers C m₁ m₂).c₀ x)) =
      D.f (zOf (flipMap (chartNumbers C m₁ m₂).c₀ x')) := congrArg Prod.fst hl
  rw [refl_zero_zOf_flip, refl_zero_zOf_flip] at hf
  have hz : σ.refl 0 (zOf x) = σ.refl 0 (zOf x') := D.bijOn_f.injOn hx hx' hf
  have hz' : zOf x = zOf x' := by
    rw [← σ.refl_zero_refl_zero (zOf x), hz, σ.refl_zero_refl_zero]
  have h2 : eC (flipMap (chartNumbers C m₁ m₂).c₀ x 2) *
      basePhase (chartNumbers C m₁ m₂).k₁ (chartNumbers C m₁ m₂).k₂
        (D.f (zOf (flipMap (chartNumbers C m₁ m₂).c₀ x))) =
      eC (flipMap (chartNumbers C m₁ m₂).c₀ x' 2) *
        basePhase (chartNumbers C m₁ m₂).k₁ (chartNumbers C m₁ m₂).k₂
          (D.f (zOf (flipMap (chartNumbers C m₁ m₂).c₀ x'))) := congrArg Prod.snd hl
  rw [refl_zero_zOf_flip, refl_zero_zOf_flip, hf] at h2
  obtain ⟨k, hk'⟩ := exists_int_of_eC_eq (mul_right_cancel h2)
  rw [flipMap_two, flipMap_two] at hk'
  exact ⟨k, point_ext (by rw [zOf_moveTrans]; exact hz'.symm)
    (by rw [moveTrans_two]; linarith)⟩

include hj hp hc₁ hc₂ in
theorem foldRel_triangle_mirror {x x' : ModelCoordinates} (hx : zOf x ∈ σ.triangle)
    (hx1 : zOf x ≠ σ.vertexOne) (hx2 : zOf x ≠ σ.vertexTwo) (hxT' : zOf x' ∉ σ.triangle)
    (hx' : σ.refl 0 (zOf x') ∈ σ.triangle) (hx1' : σ.refl 0 (zOf x') ≠ σ.vertexOne)
    (h : foldMap C m₁ m₂ hk D hθ₁ hθ₂ x = foldMap C m₁ m₂ hk D hθ₁ hθ₂ x') :
    FoldRel (coordinateModelMetric .hyperbolicProduct) (foldDomain C m₁ m₂ D hθ₁ hθ₂)
      (foldMap C m₁ m₂ hk D hθ₁ hθ₂) x x' := by
  have hx2' := refl_zero_ne_vertexTwo (θ₂_pos hθ₂) hxT'
  have hreal : ∀ i : Fin 3, ∀ z ∈ σ.triangle, σ.wallSide i z = 0 → (D.f z).im = 0 :=
    fun i z hz h => D.f_real_of_mem_foldWall ⟨hz, h⟩
  obtain ⟨hu, hF⟩ := foldMap_of_triangle C m₁ m₂ hk hj hp D hθ₁ hθ₂ hc₁ hc₂ hx hx1 hx2
  obtain ⟨hu', hF'⟩ := foldMap_of_mirror C m₁ m₂ hk hj hp D hθ₁ hθ₂ hc₁ hc₂ hx' hx1' hx2'
  have hl := C.puncturedChart_injOn hk hj hp hu hu' (hF.symm.trans (h.trans hF'))
  have hf : D.f (zOf x) = conj (D.f (zOf (flipMap (chartNumbers C m₁ m₂).c₀ x'))) :=
    congrArg Prod.fst hl
  rw [refl_zero_zOf_flip] at hf
  have hext : σ.foldExt D.f (zOf x) = σ.foldExt D.f (zOf x') := by
    rw [σ.foldExt_of_mem_triangle D.f hx, foldExt_of_refl_mem hreal hx', hf]
  rcases pairRel_of_foldExt_eq hreal (fun z hz him => exists_wall_of_im_f_eq_zero D hz him)
      D.bijOn_f (Or.inl hx) (σ.mem_domain_iff.2 (Or.inr hx')) hext with
    heq | ⟨i, hi, hw, hside⟩ | ⟨i, -, hw, -⟩
  · exact absurd (heq ▸ hx) hxT'
  · fin_cases i
    · exact absurd rfl hi
    · have hrel := foldRel_gammaOne_patch C m₁ m₂ hk hj hp D hθ₁ hθ₂ hc₁ hc₂
        (mem_patchOne_of_wall D hθ₁ hw hx1)
      have hz1 : zOf (gammaOne C m₁ m₂ (σ := σ) x) = zOf x' := by
        rw [zOf_gammaOne, hside]
        rfl
      obtain ⟨k, hk'⟩ := eq_moveTrans_of_mirror C m₁ m₂ hk hj hp D hθ₁ hθ₂ hc₁ hc₂
        (x := gammaOne C m₁ m₂ (σ := σ) x) (x' := x') (by rw [hz1]; exact hx')
        (by rw [hz1]; exact hx1') (by rw [hz1]; exact hx2') hx' hx1' hx2'
        (hrel.map_eq.trans h)
      rw [hk']
      exact hrel.trans (foldRel_moveTrans C m₁ m₂ hk D hθ₁ hθ₂ hrel.mem k)
    · have hrel := foldRel_gammaTwo C m₁ m₂ hk hj hp D hθ₁ hθ₂ hc₁ hc₂
        (mem_patchTwo_of_wall D hθ₁ hθ₂ hw hx1 hx2)
      have hz1 : zOf (gammaTwo C m₁ m₂ (σ := σ) x) = zOf x' := by
        rw [zOf_gammaTwo C m₁ m₂ x (zOf_im_pos x), hside]
        rfl
      obtain ⟨k, hk'⟩ := eq_moveTrans_of_mirror C m₁ m₂ hk hj hp D hθ₁ hθ₂ hc₁ hc₂
        (x := gammaTwo C m₁ m₂ (σ := σ) x) (x' := x') (by rw [hz1]; exact hx')
        (by rw [hz1]; exact hx1') (by rw [hz1]; exact hx2') hx' hx1' hx2'
        (hrel.map_eq.trans h)
      rw [hk']
      exact hrel.trans (foldRel_moveTrans C m₁ m₂ hk D hθ₁ hθ₂ hrel.mem k)
  · exact absurd hw.1 hxT'

theorem screwOne_iter_vertex {x : ModelCoordinates} (hx : zOf x = σ.vertexOne) (j : ℕ) :
    zOf ((screwOne C m₁ m₂ (σ := σ))^[j] x) = σ.vertexOne ∧
      ((screwOne C m₁ m₂ (σ := σ))^[j] x) 2 = x 2 - j * (chartNumbers C m₁ m₂).k₁ := by
  induction j with
  | zero => simp [hx]
  | succ j ih =>
    rw [Function.iterate_succ_apply', zOf_screwOne, ih.1, refl_two_vertexOne, refl_one_vertexOne,
      screwOne_two, ih.2]
    refine ⟨rfl, ?_⟩
    push_cast
    ring

include hθ₂ in
theorem screwTwo_iter_vertex {x : ModelCoordinates} (hx : zOf x = σ.vertexTwo) (j : ℕ) :
    zOf ((screwTwo C m₁ m₂ (σ := σ))^[j] x) = σ.vertexTwo ∧
      ((screwTwo C m₁ m₂ (σ := σ))^[j] x) 2 = x 2 - j * (chartNumbers C m₁ m₂).k₂ := by
  induction j with
  | zero => simp [hx]
  | succ j ih =>
    rw [Function.iterate_succ_apply', zOf_screwTwo, ih.1, refl_zero_vertexTwo (θ₂_pos hθ₂),
      refl_two_vertexTwo (θ₂_pos hθ₂), screwTwo_two, ih.2]
    refine ⟨rfl, ?_⟩
    push_cast
    ring

include hp in
theorem foldRel_vertexOne {x x' : ModelCoordinates} (hx : zOf x = σ.vertexOne)
    (hx' : zOf x' = σ.vertexOne)
    (h : foldMap C m₁ m₂ hk D hθ₁ hθ₂ x = foldMap C m₁ m₂ hk D hθ₁ hθ₂ x') :
    FoldRel (coordinateModelMetric .hyperbolicProduct) (foldDomain C m₁ m₂ D hθ₁ hθ₂)
      (foldMap C m₁ m₂ hk D hθ₁ hθ₂) x x' := by
  rw [foldMap_of_vertexOne C m₁ m₂ hk D hθ₁ hθ₂ hx,
    foldMap_of_vertexOne C m₁ m₂ hk D hθ₁ hθ₂ hx'] at h
  obtain ⟨-, hs⟩ := (C.tubeMap_eq_iff_of_core (norm_zero_lt C _) (norm_zero_lt C _)).1 h
  obtain ⟨m, hm⟩ := exists_int_of_eC_eq (congrArg Prod.snd hs)
  have hp₁ := p₁_ne_zero hθ₁
  obtain ⟨j, t, hjt⟩ := vertex_bezout hp₁ (chartNumbers_bezout₁ C m₁ m₂ hp) m
  obtain ⟨hz1, h21⟩ := screwOne_iter_vertex C m₁ m₂ hx j
  have hrel := foldRel_screwOne_iter C m₁ m₂ hk hp D hθ₁ hθ₂
    (by rw [hx]; exact vertexOne_mem_discOne D hθ₁) j
  have hk1 := kOne_mul (n := chartNumbers C m₁ m₂) hθ₁
  have heq : x' = moveTrans t ((screwOne C m₁ m₂ (σ := σ))^[j] x) := by
    refine point_ext (by rw [zOf_moveTrans, hz1, hx']) ?_
    rw [moveTrans_two, h21]
    have hpr : ((chartNumbers C m₁ m₂).p₁ : ℝ) ≠ 0 := by exact_mod_cast hp₁
    apply mul_left_cancel₀ hpr
    linear_combination -hm + (j : ℝ) * hk1 - hjt
  rw [heq]
  exact hrel.trans (foldRel_moveTrans C m₁ m₂ hk D hθ₁ hθ₂ hrel.mem t)

include hp in
theorem foldRel_vertexTwo {x x' : ModelCoordinates} (hx : zOf x = σ.vertexTwo)
    (hx' : zOf x' = σ.vertexTwo)
    (h : foldMap C m₁ m₂ hk D hθ₁ hθ₂ x = foldMap C m₁ m₂ hk D hθ₁ hθ₂ x') :
    FoldRel (coordinateModelMetric .hyperbolicProduct) (foldDomain C m₁ m₂ D hθ₁ hθ₂)
      (foldMap C m₁ m₂ hk D hθ₁ hθ₂) x x' := by
  rw [foldMap_of_vertexTwo C m₁ m₂ hk D hθ₁ hθ₂ hx,
    foldMap_of_vertexTwo C m₁ m₂ hk D hθ₁ hθ₂ hx'] at h
  obtain ⟨-, hs⟩ := (C.tubeMap_eq_iff_of_core (norm_zero_lt C _) (norm_zero_lt C _)).1 h
  obtain ⟨m, hm⟩ := exists_int_of_eC_eq (congrArg Prod.snd hs)
  have hp₂ := p₂_ne_zero hθ₂
  obtain ⟨j, t, hjt⟩ := vertex_bezout hp₂ (chartNumbers_bezout₂ C m₁ m₂ hp) m
  obtain ⟨hz1, h21⟩ := screwTwo_iter_vertex C m₁ m₂ hθ₂ hx j
  have hrel := foldRel_screwTwo_iter C m₁ m₂ hk hp D hθ₁ hθ₂
    (by rw [hx]; exact vertexTwo_mem_discTwo D hθ₂) j
  have hk2 := kTwo_mul (n := chartNumbers C m₁ m₂) hθ₂
  have heq : x' = moveTrans t ((screwTwo C m₁ m₂ (σ := σ))^[j] x) := by
    refine point_ext (by rw [zOf_moveTrans, hz1, hx']) ?_
    rw [moveTrans_two, h21]
    have hpr : ((chartNumbers C m₁ m₂).p₂ : ℝ) ≠ 0 := by exact_mod_cast hp₂
    apply mul_left_cancel₀ hpr
    linear_combination -hm + (j : ℝ) * hk2 - hjt
  rw [heq]
  exact hrel.trans (foldRel_moveTrans C m₁ m₂ hk D hθ₁ hθ₂ hrel.mem t)

end Pairs

section Final

theorem exists_foldRel_normal_of_domain {y : ModelCoordinates} (hy : zOf y ∈ σ.domain)
    (hyN : y ∈ foldDomain C m₁ m₂ D hθ₁ hθ₂) :
    ∃ x, FoldRel (coordinateModelMetric .hyperbolicProduct) (foldDomain C m₁ m₂ D hθ₁ hθ₂)
        (foldMap C m₁ m₂ hk D hθ₁ hθ₂) y x ∧
      ((zOf x ∈ σ.triangle ∧ zOf x ≠ σ.vertexOne ∧ zOf x ≠ σ.vertexTwo) ∨
        (zOf x ∉ σ.triangle ∧ σ.refl 0 (zOf x) ∈ σ.triangle ∧
          σ.refl 0 (zOf x) ≠ σ.vertexOne) ∨
        zOf x = σ.vertexOne ∨ zOf x = σ.vertexTwo) := by
  have hrefl := FoldRel.refl' (g := coordinateModelMetric .hyperbolicProduct)
    (F := foldMap C m₁ m₂ hk D hθ₁ hθ₂) (foldDomain C m₁ m₂ D hθ₁ hθ₂).isOpen hyN
  by_cases hT : zOf y ∈ σ.triangle
  · by_cases h1 : zOf y = σ.vertexOne
    · exact ⟨y, hrefl, Or.inr (Or.inr (Or.inl h1))⟩
    by_cases h2 : zOf y = σ.vertexTwo
    · exact ⟨y, hrefl, Or.inr (Or.inr (Or.inr h2))⟩
    exact ⟨y, hrefl, Or.inl ⟨hT, h1, h2⟩⟩
  · have hT' := (σ.mem_domain_iff.1 hy).resolve_left hT
    by_cases h1 : σ.refl 0 (zOf y) = σ.vertexOne
    · have hzx : zOf (rhoOne σ (rhoZero (chartNumbers C m₁ m₂).c₀ y)) = σ.vertexOne := by
        rw [zOf_rhoOne, zOf_rhoZero, h1, refl_one_vertexOne]
      have hrel := foldRel_gammaOne_disc C m₁ m₂ hk D hθ₁ hθ₂
        (y := rhoOne σ (rhoZero (chartNumbers C m₁ m₂).c₀ y))
        (by rw [hzx]; exact vertexOne_mem_discOne D hθ₁)
      rw [gammaOne_inv] at hrel
      exact ⟨_, hrel.symm, Or.inr (Or.inr (Or.inl hzx))⟩
    · exact ⟨y, hrefl, Or.inr (Or.inl ⟨hT, hT', h1⟩)⟩

include hj hp hc₁ hc₂ in
theorem exists_foldRel_normal {y : ModelCoordinates} (hy : y ∈ foldDomain C m₁ m₂ D hθ₁ hθ₂) :
    ∃ x, FoldRel (coordinateModelMetric .hyperbolicProduct) (foldDomain C m₁ m₂ D hθ₁ hθ₂)
        (foldMap C m₁ m₂ hk D hθ₁ hθ₂) y x ∧
      ((zOf x ∈ σ.triangle ∧ zOf x ≠ σ.vertexOne ∧ zOf x ≠ σ.vertexTwo) ∨
        (zOf x ∉ σ.triangle ∧ σ.refl 0 (zOf x) ∈ σ.triangle ∧
          σ.refl 0 (zOf x) ≠ σ.vertexOne) ∨
        zOf x = σ.vertexOne ∨ zOf x = σ.vertexTwo) := by
  obtain ⟨y₀, hy₀, hrel⟩ := exists_foldRel_domain C m₁ m₂ hk hj hp D hθ₁ hθ₂ hc₁ hc₂ hy
  obtain ⟨x, hrel', hx⟩ := exists_foldRel_normal_of_domain C m₁ m₂ hk D hθ₁ hθ₂ hy₀ hrel.mem
  exact ⟨x, hrel.trans hrel', hx⟩

include hj hp hc₁ hc₂ in
theorem foldMap_nonvertex {x : ModelCoordinates}
    (hx : (zOf x ∈ σ.triangle ∧ zOf x ≠ σ.vertexOne ∧ zOf x ≠ σ.vertexTwo) ∨
      (zOf x ∉ σ.triangle ∧ σ.refl 0 (zOf x) ∈ σ.triangle ∧ σ.refl 0 (zOf x) ≠ σ.vertexOne)) :
    ∃ u ∈ C.puncturedDomain, foldMap C m₁ m₂ hk D hθ₁ hθ₂ x = C.puncturedChart hk u := by
  rcases hx with ⟨hA, hA1, hA2⟩ | ⟨hBT, hB, hB1⟩
  · obtain ⟨hu, hF⟩ := foldMap_of_triangle C m₁ m₂ hk hj hp D hθ₁ hθ₂ hc₁ hc₂ hA hA1 hA2
    exact ⟨_, hu, hF⟩
  · obtain ⟨hu, hF⟩ := foldMap_of_mirror C m₁ m₂ hk hj hp D hθ₁ hθ₂ hc₁ hc₂ hB hB1
      (refl_zero_ne_vertexTwo (θ₂_pos hθ₂) hBT)
    exact ⟨_, hu, hF⟩

theorem foldMap_vertex {x : ModelCoordinates} (hx : zOf x = σ.vertexOne ∨ zOf x = σ.vertexTwo) :
    ∃ m w, foldMap C m₁ m₂ hk D hθ₁ hθ₂ x = C.tubeMap m (0, w) := by
  rcases hx with h | h
  · exact ⟨m₁, _, foldMap_of_vertexOne C m₁ m₂ hk D hθ₁ hθ₂ h⟩
  · exact ⟨m₂, _, foldMap_of_vertexTwo C m₁ m₂ hk D hθ₁ hθ₂ h⟩

include hj hp hc₁ hc₂ in
theorem foldMap_nonvertex_ne {x x' : ModelCoordinates}
    (hx : (zOf x ∈ σ.triangle ∧ zOf x ≠ σ.vertexOne ∧ zOf x ≠ σ.vertexTwo) ∨
      (zOf x ∉ σ.triangle ∧ σ.refl 0 (zOf x) ∈ σ.triangle ∧ σ.refl 0 (zOf x) ≠ σ.vertexOne))
    (hx' : zOf x' = σ.vertexOne ∨ zOf x' = σ.vertexTwo) :
    foldMap C m₁ m₂ hk D hθ₁ hθ₂ x ≠ foldMap C m₁ m₂ hk D hθ₁ hθ₂ x' := by
  obtain ⟨u, hu, hF⟩ := foldMap_nonvertex C m₁ m₂ hk hj hp D hθ₁ hθ₂ hc₁ hc₂ hx
  obtain ⟨m, w, hF'⟩ := foldMap_vertex C m₁ m₂ hk D hθ₁ hθ₂ hx'
  rw [hF, hF']
  exact C.puncturedChart_ne_tubeMap_zero hk hj hp hu m w

include hc₁ hc₂ in
theorem foldMap_vertexOne_ne_vertexTwo {x x' : ModelCoordinates} (hx : zOf x = σ.vertexOne)
    (hx' : zOf x' = σ.vertexTwo) :
    foldMap C m₁ m₂ hk D hθ₁ hθ₂ x ≠ foldMap C m₁ m₂ hk D hθ₁ hθ₂ x' := by
  rw [foldMap_of_vertexOne C m₁ m₂ hk D hθ₁ hθ₂ hx, foldMap_of_vertexTwo C m₁ m₂ hk D hθ₁ hθ₂ hx']
  intro h
  obtain ⟨hm, -⟩ := (C.tubeMap_eq_iff_of_core (norm_zero_lt C _) (norm_zero_lt C _)).1 h
  rw [hm] at hc₁
  have h3 := congrArg Complex.re (hc₁.symm.trans hc₂)
  simp only [ofReal_re] at h3
  linarith

include hj hp hc₁ hc₂ in
theorem foldRel_of_normal {x x' : ModelCoordinates} (hxN : x ∈ foldDomain C m₁ m₂ D hθ₁ hθ₂)
    (hx : (zOf x ∈ σ.triangle ∧ zOf x ≠ σ.vertexOne ∧ zOf x ≠ σ.vertexTwo) ∨
      (zOf x ∉ σ.triangle ∧ σ.refl 0 (zOf x) ∈ σ.triangle ∧
        σ.refl 0 (zOf x) ≠ σ.vertexOne) ∨
      zOf x = σ.vertexOne ∨ zOf x = σ.vertexTwo)
    (hx' : (zOf x' ∈ σ.triangle ∧ zOf x' ≠ σ.vertexOne ∧ zOf x' ≠ σ.vertexTwo) ∨
      (zOf x' ∉ σ.triangle ∧ σ.refl 0 (zOf x') ∈ σ.triangle ∧
        σ.refl 0 (zOf x') ≠ σ.vertexOne) ∨
      zOf x' = σ.vertexOne ∨ zOf x' = σ.vertexTwo)
    (h : foldMap C m₁ m₂ hk D hθ₁ hθ₂ x = foldMap C m₁ m₂ hk D hθ₁ hθ₂ x') :
    FoldRel (coordinateModelMetric .hyperbolicProduct) (foldDomain C m₁ m₂ D hθ₁ hθ₂)
      (foldMap C m₁ m₂ hk D hθ₁ hθ₂) x x' := by
  have hθ := θ₂_pos hθ₂
  rcases hx with hA | hB | hV1 | hV2 <;> rcases hx' with hA' | hB' | hV1' | hV2'
  · obtain ⟨k, rfl⟩ := eq_moveTrans_of_triangle C m₁ m₂ hk hj hp D hθ₁ hθ₂ hc₁ hc₂ hA.1 hA.2.1
      hA.2.2 hA'.1 hA'.2.1 hA'.2.2 h
    exact foldRel_moveTrans C m₁ m₂ hk D hθ₁ hθ₂ hxN k
  · exact foldRel_triangle_mirror C m₁ m₂ hk hj hp D hθ₁ hθ₂ hc₁ hc₂ hA.1 hA.2.1 hA.2.2 hB'.1
      hB'.2.1 hB'.2.2 h
  · exact absurd h (foldMap_nonvertex_ne C m₁ m₂ hk hj hp D hθ₁ hθ₂ hc₁ hc₂ (Or.inl hA)
      (Or.inl hV1'))
  · exact absurd h (foldMap_nonvertex_ne C m₁ m₂ hk hj hp D hθ₁ hθ₂ hc₁ hc₂ (Or.inl hA)
      (Or.inr hV2'))
  · exact (foldRel_triangle_mirror C m₁ m₂ hk hj hp D hθ₁ hθ₂ hc₁ hc₂ hA'.1 hA'.2.1 hA'.2.2
      hB.1 hB.2.1 hB.2.2 h.symm).symm
  · obtain ⟨k, rfl⟩ := eq_moveTrans_of_mirror C m₁ m₂ hk hj hp D hθ₁ hθ₂ hc₁ hc₂ hB.2.1 hB.2.2
      (refl_zero_ne_vertexTwo hθ hB.1) hB'.2.1 hB'.2.2 (refl_zero_ne_vertexTwo hθ hB'.1) h
    exact foldRel_moveTrans C m₁ m₂ hk D hθ₁ hθ₂ hxN k
  · exact absurd h (foldMap_nonvertex_ne C m₁ m₂ hk hj hp D hθ₁ hθ₂ hc₁ hc₂ (Or.inr hB)
      (Or.inl hV1'))
  · exact absurd h (foldMap_nonvertex_ne C m₁ m₂ hk hj hp D hθ₁ hθ₂ hc₁ hc₂ (Or.inr hB)
      (Or.inr hV2'))
  · exact absurd h.symm (foldMap_nonvertex_ne C m₁ m₂ hk hj hp D hθ₁ hθ₂ hc₁ hc₂ (Or.inl hA')
      (Or.inl hV1))
  · exact absurd h.symm (foldMap_nonvertex_ne C m₁ m₂ hk hj hp D hθ₁ hθ₂ hc₁ hc₂ (Or.inr hB')
      (Or.inl hV1))
  · exact foldRel_vertexOne C m₁ m₂ hk hp D hθ₁ hθ₂ hV1 hV1' h
  · exact absurd h (foldMap_vertexOne_ne_vertexTwo C m₁ m₂ hk D hθ₁ hθ₂ hc₁ hc₂ hV1 hV2')
  · exact absurd h.symm (foldMap_nonvertex_ne C m₁ m₂ hk hj hp D hθ₁ hθ₂ hc₁ hc₂ (Or.inl hA')
      (Or.inr hV2))
  · exact absurd h.symm (foldMap_nonvertex_ne C m₁ m₂ hk hj hp D hθ₁ hθ₂ hc₁ hc₂ (Or.inr hB')
      (Or.inr hV2))
  · exact absurd h.symm (foldMap_vertexOne_ne_vertexTwo C m₁ m₂ hk D hθ₁ hθ₂ hc₁ hc₂ hV1' hV2)
  · exact foldRel_vertexTwo C m₁ m₂ hk hp D hθ₁ hθ₂ hV2 hV2' h

include hj hp hc₁ hc₂ in
theorem foldRel_of_foldMap_eq {y y' : ModelCoordinates}
    (hy : y ∈ foldDomain C m₁ m₂ D hθ₁ hθ₂) (hy' : y' ∈ foldDomain C m₁ m₂ D hθ₁ hθ₂)
    (h : foldMap C m₁ m₂ hk D hθ₁ hθ₂ y = foldMap C m₁ m₂ hk D hθ₁ hθ₂ y') :
    FoldRel (coordinateModelMetric .hyperbolicProduct) (foldDomain C m₁ m₂ D hθ₁ hθ₂)
      (foldMap C m₁ m₂ hk D hθ₁ hθ₂) y y' := by
  obtain ⟨x, hrel, hx⟩ := exists_foldRel_normal C m₁ m₂ hk hj hp D hθ₁ hθ₂ hc₁ hc₂ hy
  obtain ⟨x', hrel', hx'⟩ := exists_foldRel_normal C m₁ m₂ hk hj hp D hθ₁ hθ₂ hc₁ hc₂ hy'
  have hxx := foldRel_of_normal C m₁ m₂ hk hj hp D hθ₁ hθ₂ hc₁ hc₂ hrel.mem hx hx'
    (hrel.map_eq.trans (h.trans hrel'.map_eq.symm))
  exact (hrel.trans hxx).trans hrel'.symm

end Final

end Fold

end TwoConeFold

end GC.Seifert
