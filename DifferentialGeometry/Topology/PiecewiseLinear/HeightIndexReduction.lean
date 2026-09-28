/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.Topology.PiecewiseLinear.HeightIndexComparison
import DifferentialGeometry.Topology.PiecewiseLinear.OppositeTriangleCapPerturbation

open Set

namespace DifferentialGeometry.Topology.PiecewiseLinear

private theorem enat_sub_one_lt_of_add_one_le {a b : ℕ∞} (hb : b ≠ ⊤)
    (hpos : 0 < b - 1) (hle : a + 1 ≤ b) : a - 1 < b - 1 := by
  have hab : a ≤ b := (le_add_of_nonneg_right (show (0 : ℕ∞) ≤ 1 from zero_le)).trans hle
  have ha : a ≠ ⊤ := ne_top_of_le_ne_top hb hab
  lift a to ℕ using ha
  lift b to ℕ using hb
  norm_cast at *
  omega

theorem heightIndex_lt_of_singular_comparison
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    (K R : Geometry.SimplicialComplex ℝ E) [Finite K.faces] [Finite R.faces]
    (hK : IsPLSphere 2 K.space) (hR : IsPLSphere 2 R.space)
    (hdimE : Module.finrank ℝ E = 3) (ℓ f : E →L[ℝ] ℝ) (hℓ : ℓ ≠ 0) (hf : f ≠ 0)
    (hinj : InjOn ℓ K.vertices) (hfinj : InjOn f R.vertices)
    {p q : E} (hp : p ∈ heightSingularPoints K.space ℓ)
    (hpos : 0 < (levelPolygons K.space ℓ (ℓ p)).encard - 1)
    (hother : heightSingularPoints R.space f \ {q} ⊆ heightSingularPoints K.space ℓ \ {p})
    (hcount : ∀ x ∈ K.vertices \ {p}, (levelPolygons R.space f (f x)).encard ≤
      (levelPolygons K.space ℓ (ℓ x)).encard)
    (hqcount : (levelPolygons R.space f (f q)).encard + 1 ≤
      (levelPolygons K.space ℓ (ℓ p)).encard) :
    heightIndex R.space f < heightIndex K.space ℓ := by
  classical
  have hlinear : ℓ.toLinearMap ≠ 0 := by
    intro h
    apply hℓ
    ext x
    exact congrArg (fun a : E →ₗ[ℝ] ℝ => a x) h
  have hfinite : (levelPolygons K.space ℓ (ℓ p)).encard ≠ ⊤ :=
    (finite_levelPolygons K (fun s hs => hK.isCombinatorialManifold.card_le K hs)
      hdimE ℓ.toLinearMap hlinear hinj (ℓ p)).encard_lt_top.ne
  have hpointlt := enat_sub_one_lt_of_add_one_le hfinite hpos hqcount
  let e : heightSingularPoints R.space f → heightSingularPoints K.space ℓ := fun x =>
    if hx : (x : E) = q then ⟨p, hp⟩ else ⟨x, (hother ⟨x.property, hx⟩).1⟩
  have heq : ∀ x : heightSingularPoints R.space f, (x : E) = q → (e x : E) = p := by
    intro x hx
    simp only [e, dite_eq_left hx]
  have hne : ∀ x : heightSingularPoints R.space f, (x : E) ≠ q → (e x : E) = x := by
    intro x hx
    simp only [e, dite_eq_right hx]
  have heinj : Function.Injective e := by
    intro x y hxy
    have hval := congrArg Subtype.val hxy
    by_cases hx : (x : E) = q
    · by_cases hy : (y : E) = q
      · exact Subtype.ext (hx.trans hy.symm)
      · rw [heq x hx, hne y hy] at hval
        exact ((hother ⟨y.property, hy⟩).2 hval.symm).elim
    · by_cases hy : (y : E) = q
      · rw [hne x hx, heq y hy] at hval
        exact ((hother ⟨x.property, hx⟩).2 hval).elim
      · exact Subtype.ext ((hne x hx).symm.trans (hval.trans (hne y hy)))
  apply heightIndex_lt_of_embedding K R hK hR hdimE ℓ f hℓ hf hinj hfinj ⟨e, heinj⟩
  · intro x
    by_cases hx : (x : E) = q
    · change _ ≤ (levelPolygons K.space ℓ (ℓ (e x))).encard - 1
      rw [heq x hx, hx]
      exact hpointlt.le
    · change _ ≤ (levelPolygons K.space ℓ (ℓ (e x))).encard - 1
      rw [hne x hx]
      have hxold := hother ⟨x.property, hx⟩
      have hxv := heightSingularPoints_subset_vertices K
        hK.isCombinatorialManifold.isCombinatorialManifoldWithBoundary hdimE ℓ.toLinearMap
        hlinear hinj hxold.1
      exact tsub_le_tsub_right (hcount x ⟨hxv, hxold.2⟩) 1
  · by_cases hq : q ∈ heightSingularPoints R.space f
    · refine Or.inl ⟨⟨q, hq⟩, ?_⟩
      change _ < (levelPolygons K.space ℓ (ℓ (e ⟨q, hq⟩))).encard - 1
      rw [heq ⟨q, hq⟩ rfl]
      exact hpointlt
    · refine Or.inr ⟨⟨p, hp⟩, ?_, hpos⟩
      rintro ⟨x, hx⟩
      have hxq : (x : E) ≠ q := fun h => hq (h ▸ x.property)
      have hval := congrArg Subtype.val hx
      change (e x : E) = p at hval
      rw [hne x hxq] at hval
      exact (hother ⟨x.property, hxq⟩).2 hval

theorem exists_cap_pair_heightIndex_lt_of_pos
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    (K : Geometry.SimplicialComplex ℝ E) [Finite K.faces] (hK : IsPLSphere 2 K.space)
    (hdimE : Module.finrank ℝ E = 3) (ℓ : E →L[ℝ] ℝ) (hℓ : ℓ ≠ 0)
    (hinj : InjOn ℓ K.vertices) (hindex : 0 < heightIndex K.space ℓ)
    {W : Set E} (hW : IsOpen W) (hWconv : Convex ℝ W) (hKW : K.space ⊆ W) :
    ∃ (R₁ R₂ : Geometry.SimplicialComplex ℝ E) (H : E ≃ₜ E)
      (f₁ f₂ : E →L[ℝ] ℝ) (D : Set E) (u : (Fin 3 → ℝ) → E) (r : ℝ),
      R₁.faces.Finite ∧ R₂.faces.Finite ∧ IsPLSphere 2 R₁.space ∧ IsPLSphere 2 R₂.space ∧
      f₁ ≠ 0 ∧ f₂ ≠ 0 ∧ InjOn f₁ R₁.vertices ∧ InjOn f₂ R₂.vertices ∧
      heightIndex R₁.space f₁ < heightIndex K.space ℓ ∧
      heightIndex R₂.space f₂ < heightIndex K.space ℓ ∧
      IsPLHomeomorphOn H univ univ ∧ EqOn H id Wᶜ ∧ H '' K.space ⊆ W ∧
      IsPLHomeomorphOn u (Convexity.StdSimplex.coordinateSet ℝ (Fin 3)) D ∧ D ⊆ {x | ℓ x = r} ∧
      R₁.space ∩ R₂.space = D ∧
      (R₁.space ∪ R₂.space) \ (D \ (u '' stdSimplexBoundary 2)) = H '' K.space := by
  classical
  have hlinear : ℓ.toLinearMap ≠ 0 := by
    intro h
    apply hℓ
    ext x
    exact congrArg (fun a : E →ₗ[ℝ] ℝ => a x) h
  let _ : Fintype (heightSingularPoints K.space ℓ) :=
    (finite_heightSingularPoints K hK.isCombinatorialManifold.isCombinatorialManifoldWithBoundary
      hdimE ℓ.toLinearMap hlinear hinj).fintype
  have hsum : 0 < ∑ p : heightSingularPoints K.space ℓ,
      ((levelPolygons K.space ℓ (ℓ p)).encard - 1) := by
    simpa only [heightIndex, tsum_fintype] using hindex
  obtain ⟨p, -, hppos⟩ := Finset.sum_pos_iff.mp hsum
  obtain ⟨A, B, D, J, H, R₁, R₂, f₁, f₂, hunion, -, -, -, -, -, hlevel, hH,
    hR₁fin, hR₁space, hR₁, hR₂fin, hR₂space, hR₂, -, hf₁ne, hf₁inj, -, hf₂ne,
    hf₂inj, -, -, -, hcomparison₁, hcomparison₂, -, hfixW, hdecrease₁, hdecrease₂,
    hcap, hrecover, g, hg, hgJ⟩ :=
    exists_small_opposite_triangle_cap_pair_with_level_comparison hdimE K hK ℓ hℓ hinj
      p.property hW hWconv hKW (show (0 : ℝ) < 1 by norm_num)
  let _ : Finite R₁.faces := hR₁fin.to_subtype
  let _ : Finite R₂.faces := hR₂fin.to_subtype
  have hAK : A ⊆ K.space := subset_union_left.trans_eq hunion
  have hBK : B ⊆ K.space := subset_union_right.trans_eq hunion
  have hAcount : (levelPolygons A ℓ (ℓ p)).encard ≤
      (levelPolygons K.space ℓ (ℓ p)).encard := Set.encard_le_encard (by
    intro C hC
    exact ⟨hC.1, fun x hx => ⟨hAK (hC.2 hx).1, (hC.2 hx).2⟩⟩)
  have hBcount : (levelPolygons B ℓ (ℓ p)).encard ≤
      (levelPolygons K.space ℓ (ℓ p)).encard := Set.encard_le_encard (by
    intro C hC
    exact ⟨hC.1, fun x hx => ⟨hBK (hC.2 hx).1, (hC.2 hx).2⟩⟩)
  have hlt₁ := heightIndex_lt_of_singular_comparison K R₁ hK hR₁ hdimE ℓ f₁ hℓ hf₁ne
    hinj hf₁inj p.property hppos hcomparison₁.1 (fun x hx => (hcomparison₁.2 x hx).2)
    (hdecrease₁.trans hAcount)
  have hlt₂ := heightIndex_lt_of_singular_comparison K R₂ hK hR₂ hdimE ℓ f₂ hℓ hf₂ne
    hinj hf₂inj p.property hppos hcomparison₂.1 (fun x hx => (hcomparison₂.2 x hx).2)
    (hdecrease₂.trans hBcount)
  have hHKW : H '' K.space ⊆ W := by
    rintro _ ⟨x, hx, rfl⟩
    by_contra hnot
    have heq : H x = x := H.injective (hfixW hnot)
    exact hnot (heq.symm ▸ hKW hx)
  have hu : IsPLHomeomorphOn (H ∘ g) (Convexity.StdSimplex.coordinateSet ℝ (Fin 3)) (H '' D) :=
    hg.trans (hH.restrict (IsPLBall.isPolyhedron ⟨g, hg⟩) (subset_univ D))
  have hub : (H ∘ g) '' stdSimplexBoundary 2 = H '' J := by rw [image_comp, hgJ]
  refine ⟨R₁, R₂, H, f₁, f₂, H '' D, H ∘ g, ℓ (H p), hR₁fin, hR₂fin, hR₁, hR₂,
    hf₁ne, hf₂ne, hf₁inj, hf₂inj, hlt₁, hlt₂, hH, hfixW, hHKW, hu, hlevel, ?_, ?_⟩
  · rw [hR₁space, hR₂space, ← image_inter H.injective, hcap]
  · rw [hR₁space, hR₂space, hub, ← image_union, ← image_sdiff H.injective,
      ← image_sdiff H.injective, hrecover]
end DifferentialGeometry.Topology.PiecewiseLinear
