/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.Topology.PiecewiseLinear.Prism
import DifferentialGeometry.Topology.PiecewiseLinear.SubcomplexBallGluing
import DifferentialGeometry.Topology.PiecewiseLinear.FrontierBoundary

open Set

namespace DifferentialGeometry.Topology.PiecewiseLinear

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

theorem IsPolyhedron.isPLHomeomorphOn_prod_const {P : Set E} (hP : IsPolyhedron P) (a : ℝ) :
    IsPLHomeomorphOn (fun x : E => (x, a)) P (P ×ˢ {a}) := by
  let f := (AffineMap.id ℝ E).prod (AffineMap.const ℝ E a)
  apply isPLHomeomorphOn_of_isPiecewiseAffineOn_of_bijOn hP
    ((isPiecewiseAffineOn_of_affine f isOpen_univ).mono_of_isPolyhedron hP (subset_univ _))
  exact ⟨fun _ hx => ⟨hx, rfl⟩, fun _ _ _ _ heq => congrArg Prod.fst heq,
    fun y hy => ⟨y.1, hy.1, Prod.ext rfl hy.2.symm⟩⟩

theorem IsPolyhedron.isPLHomeomorphOn_fst_prod_const {P : Set E} (hP : IsPolyhedron P) (a : ℝ) :
    IsPLHomeomorphOn (Prod.fst : E × ℝ → E) (P ×ˢ {a}) P := by
  have h := hP.isPLHomeomorphOn_prod_const a
  exact h.symm.congr fun x hx => (congrArg Prod.fst (h.bijOn.invOn_invFunOn.2 hx)).symm

open Classical in
theorem prod_left_endpoint_subset_boundaryComplex [d : DecidableEq (E × ℝ)] {P : Set E} (hP :
    IsPLBall 2 P)
    {a b : ℝ} (hab : a < b) (A : Geometry.SimplicialComplex ℝ (E × ℝ)) [Finite A.faces]
    (hAP : A.space = P ×ˢ Icc a b) :
    P ×ˢ {a} ⊆ (boundaryComplex 3 A).space := by
  have hd : d = fun x y => Classical.propDecidable (x = y) := Subsingleton.elim _ _
  subst d
  have hA : IsPLBall 3 A.space := hAP.symm ▸ isPLBall_three_prod hP (isPLBall_Icc hab)
  let B := P ×ˢ Icc (2 * a - b) a
  have hB : IsPLBall 3 B := isPLBall_three_prod hP (isPLBall_Icc (by linarith))
  have hC : IsPLBall 3 (P ×ˢ Icc (2 * a - b) b) :=
    isPLBall_three_prod hP (isPLBall_Icc (by linarith))
  obtain ⟨K, hfin, hspace⟩ := hC.isPolyhedron.exists_simplicialComplex
  let _ : Finite K.faces := hfin.to_subtype
  have hK : IsPLBall 3 K.space := hspace.symm ▸ hC
  have hAK : A.space ⊆ K.space := by
    rw [hAP, hspace]
    rintro x ⟨hx, hxa, hxb⟩
    exact ⟨hx, by linarith, hxb⟩
  have hBK : B ⊆ K.space := by
    rw [hspace]
    rintro x ⟨hx, hxa, hxb⟩
    exact ⟨hx, hxa, by linarith⟩
  have hmeet : A.space ∩ B = P ×ˢ {a} := by
    rw [hAP]
    ext x
    simp only [B, mem_inter_iff, mem_prod, mem_Icc, mem_singleton_iff]
    constructor
    · rintro ⟨⟨hx, ha, _⟩, ⟨_, _, hb⟩⟩
      exact ⟨hx, le_antisymm hb ha⟩
    · rintro ⟨hx, heq⟩
      rw [heq]
      exact ⟨⟨hx, le_rfl, hab.le⟩, hx, by linarith, le_rfl⟩
  have hI : IsPLBall 2 (A.space ∩ B) := by
    rw [hmeet]
    exact hP.of_isPLHomeomorphOn (hP.isPolyhedron.isPLHomeomorphOn_prod_const a)
  have hi := hK.isCombinatorialManifoldWithBoundary.inter_subset_boundaryComplex_of_isPLBall
    A hA hAK hB hBK hI
  rwa [hmeet] at hi

open Classical in
theorem boundaryComplex_space_prism [d : DecidableEq (E × ℝ)]
    (K : Geometry.SimplicialComplex ℝ E) [Finite K.faces]
    (hK : IsPLBall 2 K.space) {a b : ℝ} (hab : a < b)
    (A : Geometry.SimplicialComplex ℝ (E × ℝ)) [Finite A.faces]
    (hAspace : A.space = K.space ×ˢ Icc a b) :
    (boundaryComplex 3 A).space =
      K.space ×ˢ {a, b} ∪ (boundaryComplex 2 K).space ×ˢ Icc a b := by
  have hd : d = fun x y => Classical.propDecidable (x = y) := Subsingleton.elim _ _
  subst d
  let _ : DecidableEq (Fin 2 → ℝ) := Classical.decEq _
  let _ : DecidableEq ((Fin 2 → ℝ) × ℝ) := Classical.decEq _
  obtain ⟨T, hTfin, hTspace⟩ := isPLBall_coordinate_triangle.isPolyhedron.exists_simplicialComplex
  let _ : Finite T.faces := hTfin.to_subtype
  have hT : IsPLBall 2 T.space := hTspace.symm ▸ isPLBall_coordinate_triangle
  obtain ⟨t, ht⟩ := hT
  obtain ⟨k, hk⟩ := hK
  let f := k ∘ Function.invFunOn t (Convexity.StdSimplex.coordinateSet ℝ (Fin 3))
  have hf : IsPLHomeomorphOn f T.space K.space := ht.symm.trans hk
  have hI : IsPLBall 1 (Icc a b) := isPLBall_Icc hab
  have hprod : IsPLBall 3 (T.space ×ˢ Icc a b) := isPLBall_three_prod ⟨t, ht⟩ hI
  obtain ⟨R, hRfin, hRspace⟩ := hprod.isPolyhedron.exists_simplicialComplex
  let _ : Finite R.faces := hRfin.to_subtype
  have hR : IsPLBall 3 R.space := hRspace.symm ▸ hprod
  have hTman := (show IsPLBall 2 T.space from ⟨t, ht⟩).isCombinatorialManifoldWithBoundary
  have hTfront : frontier T.space = (boundaryComplex 2 T).space :=
    frontier_space_eq_boundaryComplex_space_of_finrank (by simp) T hTman
  have hRfront : frontier R.space = (boundaryComplex 3 R).space :=
    frontier_space_eq_boundaryComplex_space_of_finrank (by simp [Module.finrank_prod])
      R hR.isCombinatorialManifoldWithBoundary
  have hboundary : (boundaryComplex 3 R).space =
      T.space ×ˢ {a, b} ∪ (boundaryComplex 2 T).space ×ˢ Icc a b := by
    rw [← hRfront, hRspace, frontier_prod_eq, (isPolyhedron_space T).isClosed.closure_eq,
      frontier_Icc hab.le, hTfront, isClosed_Icc.closure_eq]
  have hmap : IsPLHomeomorphOn (Prod.map f id) R.space A.space := by
    rw [hRspace, hAspace]
    exact hf.prodMap hI.isPolyhedron.isPLHomeomorphOn_id
  rw [boundaryComplex_space_of_isPLHomeomorphOn R A hR.isCombinatorialManifoldWithBoundary hmap,
    hboundary, image_union, prodMap_image_prod, prodMap_image_prod, image_id, image_id,
    hf.image_eq, ← boundaryComplex_space_of_isPLHomeomorphOn T K hTman hf]

end DifferentialGeometry.Topology.PiecewiseLinear
