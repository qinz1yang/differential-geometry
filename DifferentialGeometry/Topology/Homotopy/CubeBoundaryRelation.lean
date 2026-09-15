import DifferentialGeometry.Topology.Homotopy.CubicalBoundary

noncomputable section

open ContinuousMap
open scoped unitInterval

namespace DifferentialGeometry.Topology

variable {X : Type*} [TopologicalSpace X] {x : X}

private abbrev Other := {j : Fin 2 // j ≠ 0}

private theorem other_eq (j : Other) : j = ⟨1, by decide⟩ := by
  apply Subtype.ext
  have h := j.property
  rcases j with ⟨j, hj⟩
  fin_cases j <;> simp_all

def cubeBoundaryFace (G : C(I × I × I, X))
    (hG : ∀ s t u, ((s = 0 ∨ s = 1) ∧ (t = 0 ∨ t = 1)) ∨
      ((s = 0 ∨ s = 1) ∧ (u = 0 ∨ u = 1)) ∨
      ((t = 0 ∨ t = 1) ∧ (u = 0 ∨ u = 1)) → G (s, t, u) = x)
    (j : Fin 3) (e : I) (he : e = 0 ∨ e = 1) : GenLoop (Fin 2) X x := by
  refine ⟨⟨fun v => G (match j with
      | 0 => (e, v 1, v 0)
      | 1 => (v 1, e, v 0)
      | 2 => (v 1, v 0, e)), ?_⟩, ?_⟩
  · fin_cases j <;> dsimp <;> fun_prop
  · rintro v ⟨i, hi⟩
    fin_cases j <;> fin_cases i
    · exact hG _ _ _ (Or.inr (Or.inl ⟨he, hi⟩))
    · exact hG _ _ _ (Or.inl ⟨he, hi⟩)
    · exact hG _ _ _ (Or.inr (Or.inr ⟨he, hi⟩))
    · exact hG _ _ _ (Or.inl ⟨hi, he⟩)
    · exact hG _ _ _ (Or.inr (Or.inr ⟨hi, he⟩))
    · exact hG _ _ _ (Or.inr (Or.inl ⟨hi, he⟩))

private def initialPrismPath (G : C(I × I × I, X)) (t u : I) :
    Path (G (0,0,u)) (G (0,t,u)) where
  toFun r := G (0, ⟨(r : ℝ) * t, unitInterval.mul_mem r.property t.property⟩, u)
  continuous_toFun := by fun_prop
  source' := by simp
  target' := by simp

private def middlePrismPath (G : C(I × I × I, X)) (t u : I) :
    Path (G (0,t,u)) (G (1,t,u)) where
  toFun r := G (r,t,u)
  continuous_toFun := by fun_prop
  source' := rfl
  target' := rfl

private def finalPrismPath (G : C(I × I × I, X)) (t u : I) :
    Path (G (1,t,u)) (G (1,0,u)) where
  toFun r := G (1, ⟨(unitInterval.symm r : ℝ) * t,
    unitInterval.mul_mem (unitInterval.symm r).property t.property⟩, u)
  continuous_toFun := by fun_prop
  source' := by simp
  target' := by simp

private def prismPath (G : C(I × I × I, X)) (t u : I) :
    Path (G (0,0,u)) (G (1,0,u)) :=
  ((initialPrismPath G t u).trans (middlePrismPath G t u)).trans (finalPrismPath G t u)

private theorem prismPath_continuous (G : C(I × I × I, X)) :
    Continuous (fun z : (I × I) × I => prismPath G z.1.1 z.1.2 z.2) := by
  exact Path.trans_continuous_family
    (fun p : I × I => (initialPrismPath G p.1 p.2).trans (middlePrismPath G p.1 p.2))
    (Path.trans_continuous_family (fun p : I × I => initialPrismPath G p.1 p.2)
      (by change Continuous (fun z : (I × I) × I => G (0, ⟨(z.2 : ℝ) * z.1.1, _⟩, z.1.2)); fun_prop)
      (fun p : I × I => middlePrismPath G p.1 p.2)
      (by change Continuous (fun z : (I × I) × I => G (z.2, z.1.1, z.1.2)); fun_prop))
    (fun p : I × I => finalPrismPath G p.1 p.2)
    (by change Continuous (fun z : (I × I) × I => G (1, ⟨(unitInterval.symm z.2 : ℝ) * z.1.1, _⟩, z.1.2)); fun_prop)

private def prismPathMap (G : C(I × I × I, X)) : C((I × I) × I, X) :=
  ⟨fun z => prismPath G z.1.1 z.1.2 z.2, prismPath_continuous G⟩

private def prismLoop (G : C(I × I × I, X))
    (hG : ∀ s t u, ((s = 0 ∨ s = 1) ∧ (t = 0 ∨ t = 1)) ∨
      ((s = 0 ∨ s = 1) ∧ (u = 0 ∨ u = 1)) ∨
      ((t = 0 ∨ t = 1) ∧ (u = 0 ∨ u = 1)) → G (s, t, u) = x)
    (t u : I) : GenLoop Other X x :=
  ⟨⟨fun v => prismPath G t u (v ⟨1, by decide⟩), by fun_prop⟩, by
    rintro v ⟨i, hi⟩
    rw [other_eq i] at hi
    change prismPath G t u (v ⟨1, by decide⟩) = x
    rcases hi with hi | hi
    · rw [hi, Path.source]
      exact hG _ _ _ (Or.inl ⟨Or.inl rfl, Or.inl rfl⟩)
    · rw [hi, Path.target]
      exact hG _ _ _ (Or.inl ⟨Or.inr rfl, Or.inl rfl⟩)⟩

private def prismSquare (G : C(I × I × I, X))
    (hG : ∀ s t u, ((s = 0 ∨ s = 1) ∧ (t = 0 ∨ t = 1)) ∨
      ((s = 0 ∨ s = 1) ∧ (u = 0 ∨ u = 1)) ∨
      ((t = 0 ∨ t = 1) ∧ (u = 0 ∨ u = 1)) → G (s, t, u) = x) :
    C(I × I, GenLoop Other X x) := by
  let Q : C((I × I) × (Other → I), (I × I) × I) :=
    ⟨fun p => (p.1, p.2 ⟨1, by decide⟩), by fun_prop⟩
  let P := (prismPathMap G).comp Q
  have hP : ∀ p : I × I, P.curry p ∈ GenLoop Other X x := by
    intro p v hv
    exact (prismLoop G hG p.1 p.2).property v hv
  exact ⟨fun p => ⟨P.curry p, hP p⟩, P.curry.continuous.subtype_mk hP⟩

private def paddedLoop (a : GenLoop (Fin 2) X x) : GenLoop (Fin 2) X x :=
  GenLoop.transAt 1 (GenLoop.transAt 1 GenLoop.const a) GenLoop.const

private theorem paddedLoop_class (a : GenLoop (Fin 2) X x) :
    (⟦paddedLoop a⟧ : HomotopyGroup (Fin 2) X x) = ⟦a⟧ := by
  have h₁ : (⟦GenLoop.transAt 1 GenLoop.const a⟧ : HomotopyGroup (Fin 2) X x) =
      ((· * ·) : _ → _ → HomotopyGroup (Fin 2) X x) ⟦a⟧ 1 := by
    exact (HomotopyGroup.mul_spec (i := (1 : Fin 2))).symm
  have h₂ : (⟦paddedLoop a⟧ : HomotopyGroup (Fin 2) X x) =
      ((· * ·) : _ → _ → HomotopyGroup (Fin 2) X x) 1 ⟦GenLoop.transAt 1 GenLoop.const a⟧ := by
    exact (HomotopyGroup.mul_spec (i := (1 : Fin 2))).symm
  exact h₂.trans (congrArg (fun z : HomotopyGroup (Fin 2) X x => 1 * z) h₁ |>.trans
    ((one_mul (_ : HomotopyGroup (Fin 2) X x)).trans (mul_one (_ : HomotopyGroup (Fin 2) X x))))

private theorem genLoop_toLoop_one_apply (a : GenLoop (Fin 2) X x) (s t r : I) :
    GenLoop.toLoop 1 a t (fun j : {j : Fin 2 // j ≠ 1} =>
      (![s,r] : Fin 2 → I) j.val) = a ![s,t] := by
  change a (Cube.insertAt 1 (t, fun j => (![s,r] : Fin 2 → I) j.val)) = a ![s,t]
  congr 1
  funext j
  fin_cases j <;> simp

private theorem transAt_apply_insert (a b : GenLoop (Fin 2) X x) (s t : I) :
    GenLoop.transAt 1 a b ![s,t] =
      if h : (t : ℝ) ≤ 1 / 2 then
        a ![s, ⟨2 * t, (unitInterval.mul_pos_mem_iff zero_lt_two).2 ⟨t.2.1, h⟩⟩]
      else b ![s, ⟨2 * t - 1, unitInterval.two_mul_sub_one_mem_iff.2
        ⟨(not_le.1 h).le, t.2.2⟩⟩] := by
  rw [← GenLoop.fromLoop_trans_toLoop]
  change (((GenLoop.toLoop 1 a).trans (GenLoop.toLoop 1 b)) t)
    (fun j : {j : Fin 2 // j ≠ 1} => (![s,t] : Fin 2 → I) j.val) = _
  rw [Path.trans_apply]
  split_ifs <;> rw [genLoop_toLoop_one_apply]

private theorem prismSquare_bottom (G : C(I × I × I, X))
    (hG : ∀ s t u, ((s = 0 ∨ s = 1) ∧ (t = 0 ∨ t = 1)) ∨
      ((s = 0 ∨ s = 1) ∧ (u = 0 ∨ u = 1)) ∨
      ((t = 0 ∨ t = 1) ∧ (u = 0 ∨ u = 1)) → G (s, t, u) = x)
    (u : I) : prismSquare G hG (0,u) =
      GenLoop.toLoop 0 (paddedLoop (cubeBoundaryFace G hG 1 0 (Or.inl rfl))) u := by
  ext v
  let r := v ⟨1, by decide⟩
  change prismPath G 0 u r = paddedLoop (cubeBoundaryFace G hG 1 0 (Or.inl rfl))
    (Cube.insertAt 0 (u,v))
  have hv : Cube.insertAt (0 : Fin 2) (u,v) = ![u,r] := by
    funext j
    fin_cases j <;> simp [r]
  rw [hv]
  simp only [paddedLoop, transAt_apply_insert, prismPath, Path.trans_apply]
  split_ifs
  · change G (0,_,u) = x
    simpa using hG 0 0 u (Or.inl ⟨Or.inl rfl, Or.inl rfl⟩)
  · rfl
  · change G (1,_,u) = x
    simpa using hG 1 0 u (Or.inl ⟨Or.inr rfl, Or.inl rfl⟩)

private theorem prismSquare_side (G : C(I × I × I, X))
    (hG : ∀ s t u, ((s = 0 ∨ s = 1) ∧ (t = 0 ∨ t = 1)) ∨
      ((s = 0 ∨ s = 1) ∧ (u = 0 ∨ u = 1)) ∨
      ((t = 0 ∨ t = 1) ∧ (u = 0 ∨ u = 1)) → G (s, t, u) = x)
    (e : I) (he : e = 0 ∨ e = 1) (t : I) : prismSquare G hG (t,e) =
      GenLoop.toLoop 0 (paddedLoop (cubeBoundaryFace G hG 2 e he)) t := by
  ext v
  let r := v ⟨1, by decide⟩
  change prismPath G t e r = paddedLoop (cubeBoundaryFace G hG 2 e he)
    (Cube.insertAt 0 (t,v))
  have hv : Cube.insertAt (0 : Fin 2) (t,v) = ![t,r] := by
    funext j
    fin_cases j <;> simp [r]
  rw [hv]
  simp only [paddedLoop, transAt_apply_insert, prismPath, Path.trans_apply]
  split_ifs
  · change G (0,_,e) = x
    exact hG _ _ _ (Or.inr (Or.inl ⟨Or.inl rfl, he⟩))
  · rfl
  · change G (1,_,e) = x
    exact hG _ _ _ (Or.inr (Or.inl ⟨Or.inr rfl, he⟩))

private theorem symmAt_apply_insert (a : GenLoop (Fin 2) X x) (s t : I) :
    GenLoop.symmAt 1 a ![s,t] = a ![s,unitInterval.symm t] := by
  change a (fun j => if j = 1 then unitInterval.symm ((![s,t] : Fin 2 → I) 1)
    else (![s,t] : Fin 2 → I) j) = _
  congr 1
  funext j
  fin_cases j <;> simp

private def cubeBoundaryTop (G : C(I × I × I, X))
    (hG : ∀ s t u, ((s = 0 ∨ s = 1) ∧ (t = 0 ∨ t = 1)) ∨
      ((s = 0 ∨ s = 1) ∧ (u = 0 ∨ u = 1)) ∨
      ((t = 0 ∨ t = 1) ∧ (u = 0 ∨ u = 1)) → G (s, t, u) = x) :
    GenLoop (Fin 2) X x :=
  GenLoop.transAt 1
    (GenLoop.transAt 1 (cubeBoundaryFace G hG 0 0 (Or.inl rfl))
      (cubeBoundaryFace G hG 1 1 (Or.inr rfl)))
    (GenLoop.symmAt 1 (cubeBoundaryFace G hG 0 1 (Or.inr rfl)))

private theorem prismSquare_top (G : C(I × I × I, X))
    (hG : ∀ s t u, ((s = 0 ∨ s = 1) ∧ (t = 0 ∨ t = 1)) ∨
      ((s = 0 ∨ s = 1) ∧ (u = 0 ∨ u = 1)) ∨
      ((t = 0 ∨ t = 1) ∧ (u = 0 ∨ u = 1)) → G (s, t, u) = x)
    (u : I) : prismSquare G hG (1,u) = GenLoop.toLoop 0 (cubeBoundaryTop G hG) u := by
  ext v
  let r := v ⟨1, by decide⟩
  change prismPath G 1 u r = cubeBoundaryTop G hG (Cube.insertAt 0 (u,v))
  have hv : Cube.insertAt (0 : Fin 2) (u,v) = ![u,r] := by
    funext j
    fin_cases j <;> simp [r]
  rw [hv]
  simp only [cubeBoundaryTop, transAt_apply_insert, prismPath, Path.trans_apply,
    symmAt_apply_insert]
  split_ifs
  · change G (0,_,u) = G (0,_,u)
    simp
  · rfl
  · change G (1,_,u) = G (1,_,u)
    congr 3
    apply Subtype.ext
    simp

private theorem six_face_group_identity {A : Type*} [CommGroup A]
    (a b c d e f : A) (h : f * c = b⁻¹ * (d * a) * e) : b * c * f = a * d * e := by
  calc
    b * c * f = b * (f * c) := by ac_rfl
    _ = b * (b⁻¹ * (d * a) * e) := by rw [h]
    _ = a * d * e := by
      rw [← mul_assoc b, ← mul_assoc b, mul_inv_cancel, one_mul, mul_comm d a]

theorem homotopyGroup_cube_boundary_relation (G : C(I × I × I, X))
    (hG : ∀ s t u, ((s = 0 ∨ s = 1) ∧ (t = 0 ∨ t = 1)) ∨
      ((s = 0 ∨ s = 1) ∧ (u = 0 ∨ u = 1)) ∨
      ((t = 0 ∨ t = 1) ∧ (u = 0 ∨ u = 1)) → G (s, t, u) = x) :
    let q (i : Fin 3) (e : I) (he : e = 0 ∨ e = 1) : HomotopyGroup (Fin 2) X x :=
      ⟦cubeBoundaryFace G hG i e he⟧
    q 0 1 (Or.inr rfl) * q 1 0 (Or.inl rfl) * q 2 1 (Or.inr rfl) =
      q 0 0 (Or.inl rfl) * q 1 1 (Or.inr rfl) * q 2 0 (Or.inl rfl) := by
  let q (i : Fin 3) (e : I) (he : e = 0 ∨ e = 1) : HomotopyGroup (Fin 2) X x :=
    ⟦cubeBoundaryFace G hG i e he⟧
  change q 0 1 _ * q 1 0 _ * q 2 1 _ = q 0 0 _ * q 1 1 _ * q 2 0 _
  have h := homotopyGroup_mul_eq_mul_of_square (i := (0 : Fin 2))
    (a := paddedLoop (cubeBoundaryFace G hG 1 0 (Or.inl rfl)))
    (b := cubeBoundaryTop G hG)
    (c := paddedLoop (cubeBoundaryFace G hG 2 0 (Or.inl rfl)))
    (d := paddedLoop (cubeBoundaryFace G hG 2 1 (Or.inr rfl)))
    (prismSquare G hG) (prismSquare_bottom G hG) (prismSquare_top G hG)
    (prismSquare_side G hG 0 (Or.inl rfl)) (prismSquare_side G hG 1 (Or.inr rfl))
  have hp (a : GenLoop (Fin 2) X x) :
      (⟦paddedLoop a⟧ : HomotopyGroup (Fin 2) X x) = ⟦a⟧ := paddedLoop_class a
  have ht : (⟦cubeBoundaryTop G hG⟧ : HomotopyGroup (Fin 2) X x) =
      (q 0 1 (Or.inr rfl))⁻¹ * (q 1 1 (Or.inr rfl) * q 0 0 (Or.inl rfl)) := by
    unfold cubeBoundaryTop
    exact (HomotopyGroup.mul_spec (i := (1 : Fin 2))).symm.trans
      (congrArg₂ (fun a b : HomotopyGroup (Fin 2) X x => a * b)
        (HomotopyGroup.inv_spec (i := (1 : Fin 2))).symm
        (HomotopyGroup.mul_spec (i := (1 : Fin 2))).symm)
  rw [hp, hp, hp, ht] at h
  change q 2 1 _ * q 1 0 _ = (q 0 1 _)⁻¹ * (q 1 1 _ * q 0 0 _) * q 2 0 _ at h
  exact six_face_group_identity (q 0 0 _) (q 0 1 _) (q 1 0 _)
    (q 1 1 _) (q 2 0 _) (q 2 1 _) h

end DifferentialGeometry.Topology
