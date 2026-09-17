import DifferentialGeometry.Topology.Planar.VertexRoundingProfile

namespace Schoenflies

open LeanEval.Topology.ClassificationOfSurfaces.Moise in
theorem exists_affine_triangle_graph_coordinates
    (b : AffineBasis (Fin 3) ℝ Plane) (f : Plane →ᵃ[ℝ] ℝ)
    (hf : f (b 1) ≠ f (b 0)) :
    ∃ e : Plane ≃ᵃ[ℝ] Plane, ∀ p, e p = Plane.mk (f p) (b.coord 2 p) := by
  let q : Fin 3 → Plane :=
    ![Plane.mk (f (b 0)) 0, Plane.mk (f (b 1)) 0, Plane.mk (f (b 2)) 1]
  have hq : AffineIndependent ℝ q := by
    apply affineIndependent_plane_triple_of_det_ne_zero
    simpa [Plane.mk, PiLp.sub_apply] using sub_ne_zero.mpr hf
  let e := triangleAffineEquiv b q b.ind hq
  have he (i : Fin 3) : e (b i) = q i := triangleAffineEquiv_apply b q b.ind hq i
  have hx : cartesianX.comp e.toAffineMap = f := by
    apply AffineMap.ext_on b.tot
    rintro p ⟨i, rfl⟩
    change (e (b i)) 0 = f (b i)
    rw [he]
    fin_cases i
    · rfl
    · rfl
    · rfl
  have hy : cartesianY.comp e.toAffineMap = b.coord 2 := by
    apply AffineMap.ext_on b.tot
    rintro p ⟨i, rfl⟩
    change (e (b i)) 1 = b.coord 2 (b i)
    rw [he]
    fin_cases i <;> simp [q, Plane.mk, b.coord_apply]
  refine ⟨e, fun p => ?_⟩
  ext i
  fin_cases i
  · exact congrArg (fun g : Plane →ᵃ[ℝ] ℝ => g p) hx
  · exact congrArg (fun g : Plane →ᵃ[ℝ] ℝ => g p) hy

private noncomputable def cornerLinearEquiv (u c l : ℝ) (hc : c ≠ 0) (hl : l ≠ 0) :
    Plane ≃ₗ[ℝ] Plane where
  toFun z := Plane.mk (z 0 / c) ((z 1 - u * z 0) / l)
  invFun z := Plane.mk (c * z 0) (l * z 1 + u * c * z 0)
  left_inv z := by
    ext i
    fin_cases i <;> dsimp [Plane.mk]
    all_goals field_simp [hc, hl]
    all_goals ring_nf
  right_inv z := by
    ext i
    fin_cases i <;> dsimp [Plane.mk]
    all_goals field_simp [hc, hl]
    all_goals ring_nf
  map_add' z w := by
    ext i
    fin_cases i <;> simp [Plane.mk, PiLp.add_apply] <;> ring_nf
  map_smul' t z := by
    ext i
    fin_cases i <;> simp [Plane.mk] <;> ring_nf

private theorem cornerLinearEquiv_smooth_profile (u c l d ε : ℝ)
    (hc : c ≠ 0) (hl : l ≠ 0) (x : Plane) :
    l * ((cornerLinearEquiv u c l hc hl x) 1 -
      d * Real.smoothMax (ε / c) ((cornerLinearEquiv u c l hc hl x) 0) 0) =
    x 1 - u * x 0 - (l * d / c) * Real.smoothMax ε (x 0) 0 := by
  change l * ((x 1 - u * x 0) / l -
    d * Real.smoothMax (ε / c) (x 0 / c) 0) = _
  rw [← zero_div c, Real.smoothMax.div]
  field_simp
  ring_nf

private theorem cornerLinearEquiv_profile (u c l d : ℝ)
    (hc : 0 < c) (hl : l ≠ 0) (x : Plane) :
    l * ((cornerLinearEquiv u c l hc.ne' hl x) 1 -
      d * max ((cornerLinearEquiv u c l hc.ne' hl x) 0) 0) =
    x 1 - u * x 0 - (l * d / c) * max (x 0) 0 := by
  change l * ((x 1 - u * x 0) / l - d * max (x 0 / c) 0) = _
  rw [← zero_div c, max_div_div_right hc.le]
  field_simp
  ring_nf

theorem exists_affine_smooth_corner_normalization
    (e₀ : Plane ≃ᵃ[ℝ] Plane) {a p b : Plane} {c q u v : ℝ}
    (hc : 0 < c) (hq : 0 < q)
    (ha : e₀ a = Plane.mk (-c) (-u * c)) (hp : e₀ p = 0)
    (hb : e₀ b = Plane.mk q (v * q)) :
    ∃ (e : Plane ≃ᵃ[ℝ] Plane) (r d l : ℝ),
      0 < r ∧ (d = 0 ∨ d = 1) ∧ l ≠ 0 ∧
      e a = Plane.mk (-1) 0 ∧ e p = 0 ∧ e b = Plane.mk r (d * r) ∧
      (∀ ε z, (e₀ z) 1 - u * (e₀ z) 0 -
          (v - u) * Real.smoothMax ε ((e₀ z) 0) 0 =
        l * ((e z) 1 - d * Real.smoothMax (ε / c) ((e z) 0) 0)) ∧
      (∀ z, (e₀ z) 1 - u * (e₀ z) 0 - (v - u) * max ((e₀ z) 0) 0 =
        l * ((e z) 1 - d * max ((e z) 0) 0)) ∧ (d = 0 ↔ u = v) := by
  by_cases huv : v = u
  · subst v
    let e := e₀.trans (cornerLinearEquiv u c c hc.ne' hc.ne').toAffineEquiv
    have he (z : Plane) : e z = Plane.mk ((e₀ z) 0 / c)
        (((e₀ z) 1 - u * (e₀ z) 0) / c) := rfl
    refine ⟨e, q / c, 0, c, div_pos hq hc, Or.inl rfl, hc.ne', ?_, ?_, ?_, ?_, ?_, by simp⟩
    · rw [he, ha]
      ext i
      fin_cases i <;> dsimp [Plane.mk]
      all_goals field_simp [hc]
      all_goals ring_nf
    · rw [he, hp]
      ext i
      fin_cases i <;> simp
    · rw [he, hb]
      ext i
      fin_cases i <;> simp
    · intro ε z
      have h := cornerLinearEquiv_smooth_profile u c c 0 ε hc.ne' hc.ne' (e₀ z)
      simpa only [e, AffineEquiv.trans_apply, LinearEquiv.coe_toAffineEquiv, sub_self,
        mul_zero, zero_div, zero_mul, sub_zero] using h.symm
    · intro z
      have h := cornerLinearEquiv_profile u c c 0 hc hc.ne' (e₀ z)
      simpa only [e, AffineEquiv.trans_apply, LinearEquiv.coe_toAffineEquiv, sub_self,
        mul_zero, zero_div, zero_mul, sub_zero] using h.symm
  · have hvu : v - u ≠ 0 := sub_ne_zero.mpr huv
    have hl : c * (v - u) ≠ 0 := mul_ne_zero hc.ne' hvu
    let e := e₀.trans (cornerLinearEquiv u c (c * (v - u)) hc.ne' hl).toAffineEquiv
    have he (z : Plane) : e z = Plane.mk ((e₀ z) 0 / c)
        (((e₀ z) 1 - u * (e₀ z) 0) / (c * (v - u))) := rfl
    have hscale : c * (v - u) * 1 / c = v - u := by field_simp
    refine ⟨e, q / c, 1, c * (v - u), div_pos hq hc, Or.inr rfl, hl, ?_, ?_, ?_, ?_, ?_, by simp [Ne.symm huv]⟩
    · rw [he, ha]
      ext i
      fin_cases i <;> dsimp [Plane.mk]
      all_goals field_simp [hc, hl]
      all_goals ring_nf
    · rw [he, hp]
      ext i
      fin_cases i <;> simp
    · rw [he, hb]
      ext i
      fin_cases i <;> dsimp [Plane.mk]
      all_goals field_simp [hc, hl]
    · intro ε z
      have h := cornerLinearEquiv_smooth_profile u c (c * (v - u)) 1 ε hc.ne' hl (e₀ z)
      simpa only [e, AffineEquiv.trans_apply, LinearEquiv.coe_toAffineEquiv, hscale] using h.symm
    · intro z
      have h := cornerLinearEquiv_profile u c (c * (v - u)) 1 hc hl (e₀ z)
      simpa only [e, AffineEquiv.trans_apply, LinearEquiv.coe_toAffineEquiv, hscale] using h.symm

open LeanEval.Topology.ClassificationOfSurfaces.Moise in
theorem exists_affine_triangle_corner_coordinates (b : AffineBasis (Fin 3) ℝ Plane) :
    ∃ e : Plane ≃ᵃ[ℝ] Plane,
      e (b 0) = Plane.mk (-1) 0 ∧ e (b 1) = Plane.mk 1 1 ∧ e (b 2) = 0 ∧
      (∀ p, e p = Plane.mk (b.coord 1 p - b.coord 0 p) (b.coord 1 p)) ∧
      (∀ ε p, (e p) 1 - Real.smoothMax ε ((e p) 0) 0 =
        -Real.smoothMax ε (-b.coord 0 p) (-b.coord 1 p)) ∧
      ∀ p, (e p) 1 - max ((e p) 0) 0 = -max (-b.coord 0 p) (-b.coord 1 p) := by
  let q : Fin 3 → Plane := ![Plane.mk (-1) 0, Plane.mk 1 1, Plane.mk 0 0]
  have hq : AffineIndependent ℝ q := by
    apply affineIndependent_plane_triple_of_det_ne_zero
    norm_num [q, Plane.mk, PiLp.sub_apply]
  let e := triangleAffineEquiv b q b.ind hq
  have he (i : Fin 3) : e (b i) = q i := triangleAffineEquiv_apply b q b.ind hq i
  have hx : cartesianX.comp e.toAffineMap = b.coord 1 - b.coord 0 := by
    apply AffineMap.ext_on b.tot
    rintro p ⟨i, rfl⟩
    change (e (b i)) 0 = b.coord 1 (b i) - b.coord 0 (b i)
    rw [he]
    fin_cases i <;> norm_num [q, Plane.mk, b.coord_apply]
  have hy : cartesianY.comp e.toAffineMap = b.coord 1 := by
    apply AffineMap.ext_on b.tot
    rintro p ⟨i, rfl⟩
    change (e (b i)) 1 = b.coord 1 (b i)
    rw [he]
    fin_cases i <;> norm_num [q, Plane.mk, b.coord_apply]
  have heq (p : Plane) : e p = Plane.mk (b.coord 1 p - b.coord 0 p) (b.coord 1 p) := by
    ext i
    fin_cases i
    · exact congrArg (fun g : Plane →ᵃ[ℝ] ℝ => g p) hx
    · exact congrArg (fun g : Plane →ᵃ[ℝ] ℝ => g p) hy
  refine ⟨e, he 0, he 1, ?_, heq, ?_, ?_⟩
  · rw [he]
    ext i
    fin_cases i <;> rfl
  · intro ε p
    rw [heq]
    change b.coord 1 p - Real.smoothMax ε (b.coord 1 p - b.coord 0 p) 0 = _
    have h := Real.smoothMax.add_right ε (-b.coord 0 p) (-b.coord 1 p) (b.coord 1 p)
    rw [neg_add_cancel, neg_add_eq_sub] at h
    linarith only [h]
  · intro p
    rw [heq]
    change b.coord 1 p - max (b.coord 1 p - b.coord 0 p) 0 = _
    rcases le_total (b.coord 0 p) (b.coord 1 p) with h | h
    · rw [max_eq_left (sub_nonneg.mpr h), max_eq_left (neg_le_neg h)]
      ring
    · rw [max_eq_right (sub_nonpos.mpr h), max_eq_right (neg_le_neg h)]
      ring

end Schoenflies
