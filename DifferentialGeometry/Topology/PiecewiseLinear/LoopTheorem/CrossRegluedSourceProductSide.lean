/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.Topology.PiecewiseLinear.LoopTheorem.CrossRegluedSourceProduct
import DifferentialGeometry.Topology.PiecewiseLinear.BoundaryAdaptation

open Set Topology

namespace DifferentialGeometry.Topology.PiecewiseLinear

private noncomputable def orthantChart : ((ℝ × ℝ) × ℝ) ≃ₜ ((ℝ × ℝ) × ℝ) where
  toFun p := ((p.1.1 - p.2, p.1.2 - p.2), min p.1.1 (min p.1.2 p.2))
  invFun p :=
    let m := min p.1.1 (min p.1.2 0)
    ((p.1.1 + p.2 - m, p.1.2 + p.2 - m), p.2 - m)
  left_inv p := by
    have hm : min (p.1.1 - p.2) (min (p.1.2 - p.2) 0) =
        min p.1.1 (min p.1.2 p.2) - p.2 := by
      rw [← sub_self p.2, min_sub_sub_right, min_sub_sub_right]
    dsimp
    rw [hm]
    ext <;> ring
  right_inv p := by
    dsimp
    have hm : min (p.1.1 + p.2 - min p.1.1 (min p.1.2 0))
        (min (p.1.2 + p.2 - min p.1.1 (min p.1.2 0))
          (p.2 - min p.1.1 (min p.1.2 0))) = p.2 := by
      calc
        _ = min (p.1.1 + p.2) (min (p.1.2 + p.2) (0 + p.2)) -
            min p.1.1 (min p.1.2 0) := by
          rw [zero_add, min_sub_sub_right, min_sub_sub_right]
        _ = min p.1.1 (min p.1.2 0) + p.2 - min p.1.1 (min p.1.2 0) := by
          rw [min_add_add_right, min_add_add_right]
        _ = _ := by ring
    rw [hm]
    ext <;> ring
  continuous_toFun :=
    ((continuous_fst.fst.sub continuous_snd).prodMk
      (continuous_fst.snd.sub continuous_snd)).prodMk
        (continuous_fst.fst.min (continuous_fst.snd.min continuous_snd))
  continuous_invFun := by dsimp; fun_prop

private theorem isPiecewiseAffineOn_orthantChart :
    IsPiecewiseAffineOn orthantChart univ := by
  have hx : IsPiecewiseAffineOn (fun p : (ℝ × ℝ) × ℝ => p.1.1) univ :=
    isPiecewiseAffineOn_of_affine
      ((LinearMap.fst ℝ ℝ ℝ).comp (LinearMap.fst ℝ (ℝ × ℝ) ℝ)).toAffineMap isOpen_univ
  have hy : IsPiecewiseAffineOn (fun p : (ℝ × ℝ) × ℝ => p.1.2) univ :=
    isPiecewiseAffineOn_of_affine
      ((LinearMap.snd ℝ ℝ ℝ).comp (LinearMap.fst ℝ (ℝ × ℝ) ℝ)).toAffineMap isOpen_univ
  have hz : IsPiecewiseAffineOn (fun p : (ℝ × ℝ) × ℝ => p.2) univ :=
    isPiecewiseAffineOn_of_affine (LinearMap.snd ℝ (ℝ × ℝ) ℝ).toAffineMap isOpen_univ
  have hn := hz.affine_comp (-AffineMap.id ℝ ℝ)
  change IsPiecewiseAffineOn (fun p : (ℝ × ℝ) × ℝ => -p.2) univ at hn
  change IsPiecewiseAffineOn
    (fun p : (ℝ × ℝ) × ℝ => ((p.1.1 - p.2, p.1.2 - p.2), min p.1.1 (min p.1.2 p.2))) _
  simpa only [sub_eq_add_neg] using
    ((hx.add hn).prod_mk (hy.add hn)).prod_mk (hx.min (hy.min hz))

private noncomputable def intervalCoordinate (a b : ℝ) (upper : Bool) : ℝ ≃ₜ ℝ where
  toFun x := if upper then b - x else x - a
  invFun x := if upper then b - x else x + a
  left_inv x := by cases upper <;> simp
  right_inv x := by cases upper <;> simp
  continuous_toFun := by cases upper <;> dsimp <;> fun_prop
  continuous_invFun := by cases upper <;> dsimp <;> fun_prop

private theorem isPiecewiseAffineOn_intervalCoordinate (a b : ℝ) (upper : Bool) :
    IsPiecewiseAffineOn (intervalCoordinate a b upper) univ := by
  have hc (r : ℝ) : IsPiecewiseAffineOn (fun _ : ℝ => r) univ :=
    isPiecewiseAffineOn_of_affine (AffineMap.const ℝ ℝ r) isOpen_univ
  have hi : IsPiecewiseAffineOn (fun x : ℝ => x) univ :=
    isPiecewiseAffineOn_id isOpen_univ
  cases upper
  · simpa [intervalCoordinate, sub_eq_add_neg] using hi.add (hc (-a))
  · simpa [intervalCoordinate, sub_eq_add_neg] using
      (hc b).add (hi.affine_comp (-AffineMap.id ℝ ℝ))

private theorem intervalCoordinate_mem {a b x : ℝ} (upper : Bool) :
    x ∈ Icc a b ↔ 0 ≤ intervalCoordinate a b upper x ∧
      intervalCoordinate a b upper x ≤ b - a := by
  cases upper <;> dsimp [intervalCoordinate] <;> constructor <;>
    rintro ⟨h1, h2⟩ <;> constructor <;> linarith

private theorem intervalCoordinate_interior {a b x : ℝ} (upper : Bool) :
    x ∈ Ioo a b ↔ 0 < intervalCoordinate a b upper x ∧
      intervalCoordinate a b upper x < b - a := by
  cases upper <;> dsimp [intervalCoordinate] <;> constructor <;>
    rintro ⟨h1, h2⟩ <;> constructor <;> linarith

private theorem exists_intervalCoordinate_lt {a b x : ℝ} (hab : a < b) :
    ∃ upper : Bool, intervalCoordinate a b upper x < b - a := by
  by_cases hx : x < b
  · exact ⟨false, by change x - a < b - a; linarith⟩
  · exact ⟨true, by change b - x < b - a; linarith⟩

private noncomputable def productBoxCoordinate (a b c : Bool) :
    ((ℝ × ℝ) × ℝ) ≃ₜ ((ℝ × ℝ) × ℝ) :=
  ((intervalCoordinate (-3) 2 a).prodCongr (intervalCoordinate (-3) 5 b)).prodCongr
    (intervalCoordinate 0 1 c)

private theorem isPiecewiseAffineOn_productBoxCoordinate (a b c : Bool) :
    IsPiecewiseAffineOn (productBoxCoordinate a b c) univ := by
  have h := ((isPiecewiseAffineOn_intervalCoordinate (-3) 2 a).prodMap
    (isPiecewiseAffineOn_intervalCoordinate (-3) 5 b)).prodMap
      (isPiecewiseAffineOn_intervalCoordinate 0 1 c)
  simpa [productBoxCoordinate, Homeomorph.prodCongr] using h

private theorem productBoxCoordinate_mem (a b c : Bool) {p : (ℝ × ℝ) × ℝ} :
    p ∈ crossingProductBox ↔
      (0 ≤ (productBoxCoordinate a b c p).1.1 ∧
        (productBoxCoordinate a b c p).1.1 ≤ 5) ∧
      (0 ≤ (productBoxCoordinate a b c p).1.2 ∧
        (productBoxCoordinate a b c p).1.2 ≤ 8) ∧
      (0 ≤ (productBoxCoordinate a b c p).2 ∧
        (productBoxCoordinate a b c p).2 ≤ 1) := by
  change (p.1.1 ∈ Icc (-3) 2 ∧ p.1.2 ∈ Icc (-3) 5) ∧ p.2 ∈ Icc 0 1 ↔ _
  rw [intervalCoordinate_mem a, intervalCoordinate_mem b, intervalCoordinate_mem c]
  norm_num [productBoxCoordinate, Homeomorph.prodCongr]
  tauto

private theorem productBoxCoordinate_interior (a b c : Bool) {p : (ℝ × ℝ) × ℝ} :
    p ∈ interior crossingProductBox ↔
      (0 < (productBoxCoordinate a b c p).1.1 ∧
        (productBoxCoordinate a b c p).1.1 < 5) ∧
      (0 < (productBoxCoordinate a b c p).1.2 ∧
        (productBoxCoordinate a b c p).1.2 < 8) ∧
      (0 < (productBoxCoordinate a b c p).2 ∧
        (productBoxCoordinate a b c p).2 < 1) := by
  rw [crossingProductBox, interior_prod_eq, interior_prod_eq, interior_Icc, interior_Icc,
    interior_Icc]
  change (p.1.1 ∈ Ioo (-3) 2 ∧ p.1.2 ∈ Ioo (-3) 5) ∧ p.2 ∈ Ioo 0 1 ↔ _
  rw [intervalCoordinate_interior a, intervalCoordinate_interior b, intervalCoordinate_interior c]
  norm_num [productBoxCoordinate, Homeomorph.prodCongr]
  tauto

theorem isPLHalfSpacePairAt_crossingProductSide (z : EuclideanSpace ℝ (Fin 3)) :
    IsPLHalfSpacePairAt crossingProductSide (frontier crossingProductSide) z := by
  let p := spliceEmbedding.symm z
  obtain ⟨a, ha⟩ := exists_intervalCoordinate_lt (x := p.1.1) (by norm_num : (-3 : ℝ) < 2)
  obtain ⟨b, hb⟩ := exists_intervalCoordinate_lt (x := p.1.2) (by norm_num : (-3 : ℝ) < 5)
  obtain ⟨c, hc⟩ := exists_intervalCoordinate_lt (x := p.2) (by norm_num : (0 : ℝ) < 1)
  let A := productBoxCoordinate a b c
  let f := spliceEmbedding.toHomeomorph.symm.trans A
  let e := (f.trans orthantChart).trans spliceEmbedding.toHomeomorph
  let O : Set (EuclideanSpace ℝ (Fin 3)) :=
    {y | (f y).1.1 < 5 ∧ (f y).1.2 < 8 ∧ (f y).2 < 1}
  have hO : IsOpen O :=
    (isOpen_lt f.continuous.fst.fst continuous_const).inter
      ((isOpen_lt f.continuous.fst.snd continuous_const).inter
        (isOpen_lt f.continuous.snd continuous_const))
  have hzO : z ∈ O := by
    exact ⟨by norm_num at ha; exact ha, by norm_num at hb; exact hb,
      by norm_num at hc; exact hc⟩
  have hplace : IsPiecewiseAffineOn (⇑spliceEmbedding.symm) univ :=
    isPiecewiseAffineOn_of_affine spliceEmbedding.symm.toLinearMap.toAffineMap isOpen_univ
  have hf : IsPiecewiseAffineOn f univ := by
    have h := (isPiecewiseAffineOn_productBoxCoordinate a b c).comp hplace
    rw [preimage_univ, inter_univ] at h
    exact h.congr fun _ _ => rfl
  have he : IsPiecewiseAffineOn e univ := by
    have h := isPiecewiseAffineOn_orthantChart.comp hf
    rw [preimage_univ, inter_univ] at h
    exact h.affine_comp spliceEmbedding.toLinearMap.toAffineMap
  let ℓ := (LinearMap.snd ℝ (ℝ × ℝ) ℝ).comp spliceEmbedding.symm.toLinearMap
  have hℓ : ℓ ≠ 0 := by
    intro h
    have h' := congrArg (fun l => l (spliceEmbedding ((0, 0), 1))) h
    norm_num [ℓ] at h'
  have heval (y : EuclideanSpace ℝ (Fin 3)) :
      ℓ (e y) = min (f y).1.1 (min (f y).1.2 (f y).2) := by
    change (spliceEmbedding.symm (spliceEmbedding (orthantChart (f y)))).2 = _
    rw [ContinuousLinearEquiv.symm_apply_apply]
    rfl
  have hmem (y : EuclideanSpace ℝ (Fin 3)) (hy : y ∈ O) :
      y ∈ crossingProductSide ↔ 0 ≤ ℓ (e y) := by
    have hplace : y ∈ crossingProductSide ↔ spliceEmbedding.symm y ∈ crossingProductBox := by
      constructor
      · rintro ⟨u, hu, rfl⟩
        simpa only [ContinuousLinearEquiv.symm_apply_apply] using hu
      · intro hy
        exact ⟨spliceEmbedding.symm y, hy, spliceEmbedding.apply_symm_apply y⟩
    rw [hplace, productBoxCoordinate_mem a b c, heval, le_min_iff, le_min_iff]
    change ((_ ∧ _) ∧ (_ ∧ _) ∧ (_ ∧ _)) ↔ _
    exact ⟨fun h => ⟨h.1.1, h.2.1.1, h.2.2.1⟩,
      fun h => ⟨⟨h.1, hy.1.le⟩, ⟨h.2.1, hy.2.1.le⟩, ⟨h.2.2, hy.2.2.le⟩⟩⟩
  have hint (y : EuclideanSpace ℝ (Fin 3)) (hy : y ∈ O) :
      y ∈ interior crossingProductSide ↔ 0 < ℓ (e y) := by
    have hplace : y ∈ interior crossingProductSide ↔
        spliceEmbedding.symm y ∈ interior crossingProductBox := by
      have hi : interior crossingProductSide =
          spliceEmbedding '' interior crossingProductBox :=
        (spliceEmbedding.toHomeomorph.image_interior crossingProductBox).symm
      rw [hi]
      constructor
      · rintro ⟨u, hu, rfl⟩
        simpa only [ContinuousLinearEquiv.symm_apply_apply] using hu
      · intro hy
        exact ⟨spliceEmbedding.symm y, hy, spliceEmbedding.apply_symm_apply y⟩
    rw [hplace, productBoxCoordinate_interior a b c, heval, lt_min_iff, lt_min_iff]
    exact ⟨fun h => ⟨h.1.1, h.2.1.1, h.2.2.1⟩,
      fun h => ⟨⟨h.1, hy.1⟩, ⟨h.2.1, hy.2.1⟩, ⟨h.2.2, hy.2.2⟩⟩⟩
  have hatlas : e.toOpenPartialHomeomorph ∈
      (plGroupoid 3).maximalAtlas (EuclideanSpace ℝ (Fin 3)) :=
    (plGroupoid 3).mem_maximalAtlas_of_mem_groupoid
      (mem_plGroupoid_of_isPiecewiseAffineOn he)
  refine ⟨e.toOpenPartialHomeomorph.restr O, ℓ,
    restr_mem_maximalAtlas (G := plGroupoid 3) hatlas hO, hℓ,
    ⟨mem_univ _, hO.interior_eq.symm ▸ hzO⟩,
    fun y hy => hmem y (interior_subset hy.2), ?_⟩
  intro y hy
  change y ∈ frontier crossingProductSide ↔ ℓ (e y) = 0
  rw [isCompact_crossingProductSide.isClosed.frontier_eq, Set.mem_sdiff,
    hmem y (interior_subset hy.2), hint y (interior_subset hy.2), not_lt]
  exact ⟨fun h => le_antisymm h.2 h.1, fun h => ⟨h.ge, h.le⟩⟩

theorem isPLBoundarySide_crossingProductCell :
    IsPLBoundarySide crossingProductCell crossingProductSide (frontier crossingProductSide) := by
  refine ⟨image_subset_iff.mpr crossingProductCell_mapsTo_side,
    isCompact_crossingProductSide.isClosed, isClosed_frontier, ?_,
    fun z _ => isPLHalfSpacePairAt_crossingProductSide z⟩
  rintro y ⟨x, ⟨hx, hnot⟩, rfl⟩
  have hside := crossingProductCell_mapsTo_side hx
  by_contra hint
  apply hnot
  rw [← crossingProductCell_preimage_frontier_side]
  exact ⟨hx, ⟨subset_closure hside, hint⟩⟩

end DifferentialGeometry.Topology.PiecewiseLinear
