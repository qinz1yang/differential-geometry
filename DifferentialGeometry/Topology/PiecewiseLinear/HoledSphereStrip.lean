/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.Topology.PiecewiseLinear.HoledSphereExtension
import DifferentialGeometry.Topology.PiecewiseLinear.BallGluingTwo
import DifferentialGeometry.Topology.PiecewiseLinear.ConvexPolytope
import DifferentialGeometry.Topology.PiecewiseLinear.CirclePrismComparison
import DifferentialGeometry.Topology.PiecewiseLinear.PseudoCell

open Set

namespace DifferentialGeometry.Topology.PiecewiseLinear

local notation "Plane" => EuclideanSpace ℝ (Fin 2)

theorem isHPolytope_rectTwo (a b c d : ℝ) : IsHPolytope (rectTwo a b c d) := by
  refine ⟨isCompact_rectTwo a b c d, Fin 2 ⊕ Fin 2, inferInstance,
    Sum.elim (fun i => euclideanCoord i) (fun i => -euclideanCoord i),
    Sum.elim ![b, d] ![-a, -c], ?_⟩
  ext p
  simp only [mem_rectTwo, mem_Icc, mem_ofPred_eq, Sum.forall, Sum.elim_inl, Sum.elim_inr,
    Fin.forall_fin_two, euclideanCoord_apply, LinearMap.neg_apply, Matrix.cons_val_zero,
    Matrix.cons_val_one, neg_le_neg_iff]
  tauto

theorem isPLBall_rectTwo {a b c d : ℝ} (hab : a < b) (hcd : c < d) :
    IsPLBall 2 (rectTwo a b c d) := by
  have h := (isHPolytope_rectTwo a b c d).isPLBall ⟨EuclideanSpace.single 0 ((a + b) / 2) +
    EuclideanSpace.single 1 ((c + d) / 2), openRectTwo_subset_interior_rectTwo a b c d
      ⟨by simp; constructor <;> linarith, by simp; constructor <;> linarith⟩⟩
  rwa [finrank_euclideanSpace_fin] at h

theorem mem_frontier_rectTwo_of_apply_one_eq {a b c d : ℝ} {x : Plane}
    (hx : x ∈ rectTwo a b c d) (hc : x 1 = c) : x ∈ frontier (rectTwo a b c d) := by
  refine ⟨subset_closure hx, fun hint => ?_⟩
  obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.mp isOpen_interior x hint
  have hy : x - EuclideanSpace.single 1 (ε / 2) ∈ Metric.ball x ε := by
    rw [Metric.mem_ball, dist_eq_norm, sub_sub_cancel_left, norm_neg]
    have hn : ‖EuclideanSpace.single (1 : Fin 2) (ε / 2)‖ = ε / 2 := by
      simpa using hε.le
    rw [hn]
    linarith
  have h1 := (mem_rectTwo.mp (interior_subset (hball hy))).2.1
  simp [hc] at h1
  linarith

theorem exists_planar_strip {ι : Type*} [Finite ι] {D : Set Plane} {H : ι → Set Plane}
    (hD : IsPLBall 2 D) (hH : ∀ i, IsPLBall 2 (H i)) (hHD : ∀ i, H i ⊆ interior D)
    (hdis : Pairwise fun i j => Disjoint (H i) (H j)) (j : ι) {α β : ℝ → Plane}
    (hα : IsPLHomeomorphOn α (Icc 0 1) (α '' Icc 0 1)) (hαD : α '' Icc 0 1 ⊆ frontier D)
    (hβ : IsPLHomeomorphOn β (Icc 0 1) (β '' Icc 0 1)) (hβH : β '' Icc 0 1 ⊆ frontier (H j))
    {r : Plane → Plane} (hr : IsPLHomeomorphOn r (frontier (H j)) (frontier (H j)))
    (hnr : ¬ IsPLCirclePositive (frontier (H j)) r)
    (hrβ : ∀ t ∈ Icc (0 : ℝ) 1, r (β t) = β (1 - t)) :
    ∃ σ : ℝ × ℝ → Plane,
      IsPLHomeomorphOn σ (Icc 0 1 ×ˢ Icc 0 1) (σ '' (Icc 0 1 ×ˢ Icc 0 1)) ∧
      σ '' (Icc 0 1 ×ˢ Icc 0 1) ⊆ D \ ⋃ i, interior (H i) ∧
      σ '' (Icc 0 1 ×ˢ Icc 0 1) ∩ (frontier D ∪ ⋃ i, frontier (H i)) =
        α '' Icc 0 1 ∪ β '' Icc 0 1 ∧
      (∀ t ∈ Icc (0 : ℝ) 1, σ (t, 0) = α t) ∧
      ((∀ t ∈ Icc (0 : ℝ) 1, σ (t, 1) = β t) ∨ ∀ t ∈ Icc (0 : ℝ) 1, σ (t, 1) = β (1 - t)) := by
  classical
  let _ : Fintype ι := Fintype.ofFinite ι
  set N : ℝ := (Fintype.card ι : ℝ) with hN
  let n : ι → ℕ := fun i => (Fintype.equivFin ι i : ℕ)
  have hninj : Function.Injective n := fun i i' h =>
    (Fintype.equivFin ι).injective (Fin.ext h)
  have hnN : ∀ i, (n i : ℝ) + 1 ≤ N := fun i => by
    have h := (Fintype.equivFin ι i).2
    rw [hN]
    exact_mod_cast h
  have hN0 : 0 < N + 1 := by
    have : (0 : ℝ) ≤ N := by rw [hN]; positivity
    linarith
  let xl : ι → ℝ := fun i => (n i : ℝ) / (N + 1)
  let w : ℝ := 1 / (2 * (N + 1))
  have hw : 0 < w := by positivity
  have hxl0 : ∀ i, 0 ≤ xl i := fun i => by positivity
  have hxw : ∀ i, xl i + w = (2 * (n i : ℝ) + 1) / (2 * (N + 1)) := by
    intro i
    simp only [xl, w]
    field_simp
  have hxl1 : ∀ i, xl i + w < 1 := by
    intro i
    rw [hxw, div_lt_one (by positivity)]
    linarith [hnN i]
  have hsep : ∀ i i', n i < n i' → xl i + w < xl i' := by
    intro i i' hlt
    rw [hxw]
    simp only [xl]
    rw [div_lt_div_iff₀ (by positivity) (by positivity)]
    have hle : (n i : ℝ) + 1 ≤ n i' := by exact_mod_cast hlt
    nlinarith
  let Hm : ι → Set Plane := fun i =>
    if i = j then rectTwo (-1) 1 (-1) 1 else rectTwo (xl i) (xl i + w) (3 / 2) (7 / 4)
  let D₀ : Set Plane := rectTwo (-2) 2 (-2) 2
  have hHmj : Hm j = rectTwo (-1) 1 (-1) 1 := ite_eq_left rfl
  have hHmi : ∀ i, i ≠ j → Hm i = rectTwo (xl i) (xl i + w) (3 / 2) (7 / 4) :=
    fun i hi => ite_eq_right hi
  have hD₀ : IsPLBall 2 D₀ := isPLBall_rectTwo (by norm_num) (by norm_num)
  have hHm : ∀ i, IsPLBall 2 (Hm i) := by
    intro i
    by_cases hi : i = j
    · rw [hi, hHmj]
      exact isPLBall_rectTwo (by norm_num) (by norm_num)
    · rw [hHmi i hi]
      exact isPLBall_rectTwo (by linarith) (by norm_num)
  have hHmD : ∀ i, Hm i ⊆ interior D₀ := by
    intro i x hx
    refine openRectTwo_subset_interior_rectTwo _ _ _ _ ?_
    by_cases hi : i = j
    · rw [hi, hHmj] at hx
      obtain ⟨⟨h1, h2⟩, h3, h4⟩ := hx
      exact ⟨⟨by linarith, by linarith⟩, by linarith, by linarith⟩
    · rw [hHmi i hi] at hx
      obtain ⟨⟨h1, h2⟩, h3, h4⟩ := hx
      exact ⟨⟨by linarith [hxl0 i], by linarith [hxl1 i]⟩, by linarith, by linarith⟩
  have hHmdis : Pairwise fun i i' => Disjoint (Hm i) (Hm i') := by
    intro i i' hii
    rw [disjoint_left]
    intro x hx hx'
    by_cases hi : i = j
    · have hi' : i' ≠ j := fun h => hii (hi.trans h.symm)
      rw [hi, hHmj] at hx
      rw [hHmi i' hi'] at hx'
      linarith [(mem_rectTwo.mp hx).2.2, (mem_rectTwo.mp hx').2.1]
    · by_cases hi' : i' = j
      · rw [hi', hHmj] at hx'
        rw [hHmi i hi] at hx
        linarith [(mem_rectTwo.mp hx').2.2, (mem_rectTwo.mp hx).2.1]
      · rw [hHmi i hi] at hx
        rw [hHmi i' hi'] at hx'
        rcases lt_or_gt_of_ne (fun h => hii (hninj h)) with hlt | hlt
        · linarith [hsep i i' hlt, (mem_rectTwo.mp hx).1.2, (mem_rectTwo.mp hx').1.1]
        · linarith [hsep i' i hlt, (mem_rectTwo.mp hx').1.2, (mem_rectTwo.mp hx).1.1]
  let L : ℝ × ℝ →ₗ[ℝ] Plane :=
    (LinearMap.fst ℝ ℝ ℝ).smulRight (EuclideanSpace.single (0 : Fin 2) (1 : ℝ)) +
      (LinearMap.snd ℝ ℝ ℝ).smulRight (EuclideanSpace.single (1 : Fin 2) (1 : ℝ))
  let p₀ : Plane := EuclideanSpace.single 0 (-(1 / 2)) + EuclideanSpace.single 1 (-2)
  let A : ℝ × ℝ →ᵃ[ℝ] Plane :=
    { toFun := fun p => L p + p₀
      linear := L
      map_vadd' := fun p v => by
        simp only [vadd_eq_add, map_add]
        abel }
  have hA0 : ∀ p : ℝ × ℝ, A p 0 = p.1 - 1 / 2 := by
    intro p
    change (L p + p₀) 0 = p.1 - 1 / 2
    simp [L, p₀]
    ring
  have hA1 : ∀ p : ℝ × ℝ, A p 1 = p.2 - 2 := by
    intro p
    change (L p + p₀) 1 = p.2 - 2
    simp [L, p₀]
    ring
  have hAinj : Function.Injective A := by
    intro p p' hpp
    have h0 := hA0 p
    have h1 := hA1 p
    rw [hpp, hA0] at h0
    rw [hpp, hA1] at h1
    exact Prod.ext (by linarith) (by linarith)
  have hAPL : ∀ {P : Set (ℝ × ℝ)}, IsPolyhedron P → IsPLHomeomorphOn A P (A '' P) :=
    fun hP => isPLHomeomorphOn_of_isPiecewiseAffineOn_of_bijOn hP
      ((isPiecewiseAffineOn_of_affine A isOpen_univ).mono_of_isPolyhedron hP (subset_univ _))
      (hAinj.injOn.bijOn_image)
  let emb : ℝ → ℝ →ᵃ[ℝ] ℝ × ℝ := fun c =>
    { toFun := fun t => (t, c)
      linear := LinearMap.inl ℝ ℝ ℝ
      map_vadd' := fun t v => by
        simp [vadd_eq_add] }
  have hembPL : ∀ c : ℝ, IsPLHomeomorphOn (A.comp (emb c)) (Icc 0 1)
      ((A.comp (emb c)) '' Icc 0 1) := by
    intro c
    refine isPLHomeomorphOn_of_isPiecewiseAffineOn_of_bijOn isHPolytope_Icc.isPolyhedron
      ((isPiecewiseAffineOn_of_affine _ isOpen_univ).mono_of_isPolyhedron
        isHPolytope_Icc.isPolyhedron (subset_univ _)) (InjOn.bijOn_image ?_)
    intro t _ t' _ htt
    have h := congrArg (fun x : Plane => x 0) htt
    change A (t, c) 0 = A (t', c) 0 at h
    rw [hA0, hA0] at h
    simpa using h
  let pb : ℝ → Plane := A.comp (emb 0)
  let pt : ℝ → Plane := A.comp (emb 1)
  have hpb : ∀ t, pb t = A (t, 0) := fun t => rfl
  have hpt : ∀ t, pt t = A (t, 1) := fun t => rfl
  have hbot : IsPLHomeomorphOn pb (Icc 0 1) (pb '' Icc 0 1) := hembPL 0
  have htop : IsPLHomeomorphOn pt (Icc 0 1) (pt '' Icc 0 1) := hembPL 1
  have hAD₀ : ∀ p ∈ Icc (0 : ℝ) 1 ×ˢ Icc (0 : ℝ) 1, A p ∈ D₀ := by
    rintro p ⟨⟨h1, h2⟩, h3, h4⟩
    refine ⟨⟨?_, ?_⟩, ?_, ?_⟩ <;> simp only [hA0, hA1] <;> linarith
  have hbotfr : pb '' Icc 0 1 ⊆ frontier D₀ := by
    rintro _ ⟨t, ht, rfl⟩
    exact mem_frontier_rectTwo_of_apply_one_eq (hAD₀ (t, 0) ⟨ht, by norm_num⟩)
      (by rw [hpb, hA1]; norm_num)
  have htopfr : pt '' Icc 0 1 ⊆ frontier (Hm j) := by
    rintro _ ⟨t, ht, rfl⟩
    rw [hHmj]
    refine mem_frontier_rectTwo_of_apply_one_eq ⟨⟨?_, ?_⟩, ?_, ?_⟩ ?_ <;>
      simp only [hpt, hA0, hA1] <;> linarith [ht.1, ht.2]
  obtain ⟨φ, hφ, hφpb⟩ := exists_isPLHomeomorphOn_eqOn_arc_of_isPLSphere_one_of_ambient
    (hD₀.isPLSphere_frontier (n := 1)) (hD.isPLSphere_frontier (n := 1))
    ((isPLBall_Icc zero_lt_one).of_isPLHomeomorphOn hbot) hbotfr (hbot.symm.trans hα) hαD
  obtain ⟨f, hf, hfφ, hfHm, hext⟩ := exists_isPLHomeomorphOn_holed_disk_with_boundary_extension
    hD₀ hD hHm hH hHmD hHD hHmdis hdis hφ
  have hfr : ∀ i, IsPLHomeomorphOn f (frontier (Hm i)) (frontier (H i)) := by
    intro i
    have hsub : Hm i ⊆ D₀ := (hHmD i).trans interior_subset
    have h1 := hf.restrict (hHm i).isPolyhedron hsub
    rw [hfHm i] at h1
    have himg := h1.image_frontier rfl (hHm i).isPolyhedron.isClosed (hH i).isPolyhedron.isClosed
    have h2 := hf.restrict ((hHm i).isPLSphere_frontier (n := 1)).isPolyhedron
      ((hHm i).isPolyhedron.isClosed.frontier_subset.trans hsub)
    rwa [himg] at h2
  obtain ⟨ψp, hψp, hψpt⟩ := exists_isPLHomeomorphOn_eqOn_arc_of_isPLSphere_one_of_ambient
    ((hHm j).isPLSphere_frontier (n := 1)) ((hH j).isPLSphere_frontier (n := 1))
    ((isPLBall_Icc zero_lt_one).of_isPLHomeomorphOn htop) htopfr (htop.symm.trans hβ) hβH
  have hψpt' : ∀ t ∈ Icc (0 : ℝ) 1, ψp (pt t) = β t := by
    intro t ht
    rw [hψpt ⟨t, ht, rfl⟩]
    change β (Function.invFunOn pt (Icc 0 1) (pt t)) = β t
    rw [htop.bijOn.invOn_invFunOn.1 ht]
  obtain ⟨ψj, hψj, hψjpos, hψjβ⟩ : ∃ ψj : Plane → Plane,
      IsPLHomeomorphOn ψj (frontier (Hm j)) (frontier (H j)) ∧
      IsPLCirclePositive (frontier (H j)) (ψj ∘ Function.invFunOn f (frontier (Hm j))) ∧
      ((∀ t ∈ Icc (0 : ℝ) 1, ψj (pt t) = β t) ∨
        ∀ t ∈ Icc (0 : ℝ) 1, ψj (pt t) = β (1 - t)) := by
    have hu : IsPLHomeomorphOn (ψp ∘ Function.invFunOn f (frontier (Hm j)))
        (frontier (H j)) (frontier (H j)) := (hfr j).symm.trans hψp
    by_cases hpos : IsPLCirclePositive (frontier (H j))
        (ψp ∘ Function.invFunOn f (frontier (Hm j)))
    · exact ⟨ψp, hψp, hpos, Or.inl hψpt'⟩
    · refine ⟨r ∘ ψp, hψp.trans hr, ?_, Or.inr fun t ht => ?_⟩
      · have h := isPLCirclePositive_comp_of_not_isPLCirclePositive (u := r)
          (v := ψp ∘ Function.invFunOn f (frontier (Hm j)))
          ((hH j).isPLSphere_frontier (n := 1)) hr hu hnr hpos
        exact h
      · change r (ψp (pt t)) = β (1 - t)
        rw [hψpt' t ht, hrβ t ht]
  let ψ : ι → Plane → Plane := fun i => if i = j then ψj else f
  have hψ : ∀ i, IsPLHomeomorphOn (ψ i) (frontier (Hm i)) (frontier (H i)) := by
    intro i
    by_cases hi : i = j
    · subst hi
      simpa [ψ] using hψj
    · simpa [ψ, hi] using hfr i
  have hψpos : ∀ i, IsPLCirclePositive (frontier (H i))
      (ψ i ∘ Function.invFunOn f (frontier (Hm i))) := by
    intro i
    by_cases hi : i = j
    · subst hi
      simpa [ψ] using hψjpos
    · have hid := isPLCirclePositive_id ((hH i).isPLSphere_frontier (n := 1))
      refine hid.of_eqOn fun z hz => ?_
      simp only [ψ, hi, ite_false, Function.comp_apply, id]
      exact (hfr i).bijOn.surjOn.rightInvOn_invFunOn hz
  obtain ⟨g, hg, hgφ, hgψ⟩ := hext ψ hψ hψpos
  have hsqpoly : IsPolyhedron (Icc (0 : ℝ) 1 ×ˢ Icc (0 : ℝ) 1) :=
    (isHPolytope_Icc.prod isHPolytope_Icc).isPolyhedron
  have hAsq := hAPL hsqpoly
  have hSpoly : IsPolyhedron (A '' (Icc (0 : ℝ) 1 ×ˢ Icc (0 : ℝ) 1)) :=
    hsqpoly.image_of_isPiecewiseAffineOn hAsq.isPiecewiseAffineOn hAsq.bijOn.injOn
  have hnotint : ∀ p ∈ Icc (0 : ℝ) 1 ×ˢ Icc (0 : ℝ) 1, ∀ i, A p ∉ interior (Hm i) := by
    rintro p ⟨⟨h1, h2⟩, h3, h4⟩ i hint
    have hmem := interior_subset hint
    by_cases hi : i = j
    · rw [hi, hHmj] at hint hmem
      have hp2 : A p 1 = -1 := by
        have := (mem_rectTwo.mp hmem).2.1
        rw [hA1] at this ⊢
        linarith
      exact (mem_frontier_rectTwo_of_apply_one_eq hmem hp2).2 hint
    · rw [hHmi i hi] at hmem
      have := (mem_rectTwo.mp hmem).2.1
      rw [hA1] at this
      linarith
  have hSsub : A '' (Icc (0 : ℝ) 1 ×ˢ Icc (0 : ℝ) 1) ⊆ D₀ \ ⋃ i, interior (Hm i) := by
    rintro _ ⟨p, hp, rfl⟩
    refine ⟨hAD₀ p hp, ?_⟩
    simp only [mem_iUnion, not_exists]
    exact hnotint p hp
  have hσ : IsPLHomeomorphOn (g ∘ A) (Icc 0 1 ×ˢ Icc 0 1)
      ((g ∘ A) '' (Icc 0 1 ×ˢ Icc 0 1)) := by
    rw [image_comp]
    exact hAsq.trans (hg.restrict hSpoly hSsub)
  have hσ0 : ∀ t ∈ Icc (0 : ℝ) 1, (g ∘ A) (t, 0) = α t := by
    intro t ht
    change g (pb t) = α t
    rw [hgφ (hbotfr ⟨t, ht, rfl⟩), hφpb ⟨t, ht, rfl⟩]
    change α (Function.invFunOn pb (Icc 0 1) (pb t)) = α t
    rw [hbot.bijOn.invOn_invFunOn.1 ht]
  have hσ1 : ∀ t ∈ Icc (0 : ℝ) 1, (g ∘ A) (t, 1) = ψj (pt t) := by
    intro t ht
    change g (pt t) = ψj (pt t)
    rw [hgψ j (htopfr ⟨t, ht, rfl⟩)]
    simp [ψ]
  have hCirc : g '' (frontier D₀ ∪ ⋃ i, frontier (Hm i)) = frontier D ∪ ⋃ i, frontier (H i) := by
    rw [image_union, image_iUnion, image_congr hgφ, hφ.image_eq]
    congr 1
    exact iUnion_congr fun i => (image_congr (hgψ i)).trans (hψ i).image_eq
  have hCircsub : frontier D₀ ∪ ⋃ i, frontier (Hm i) ⊆ D₀ \ ⋃ i, interior (Hm i) := by
    rintro x (hx | hx)
    · refine ⟨hD₀.isPolyhedron.isClosed.frontier_subset hx, ?_⟩
      simp only [mem_iUnion, not_exists]
      intro i hi
      exact hx.2 (hHmD i (interior_subset hi))
    · obtain ⟨i, hi⟩ := mem_iUnion.mp hx
      have hxi : x ∈ Hm i := (hHm i).isPolyhedron.isClosed.frontier_subset hi
      refine ⟨(hHmD i).trans interior_subset hxi, ?_⟩
      simp only [mem_iUnion, not_exists]
      intro i' hi'
      by_cases hii : i' = i
      · subst hii
        exact hi.2 hi'
      · exact disjoint_left.mp (hHmdis hii) (interior_subset hi') hxi
  have hmodel : A '' (Icc (0 : ℝ) 1 ×ˢ Icc (0 : ℝ) 1) ∩ (frontier D₀ ∪ ⋃ i, frontier (Hm i)) =
      pb '' Icc 0 1 ∪ pt '' Icc 0 1 := by
    apply Subset.antisymm
    · rintro _ ⟨⟨p, ⟨⟨h1, h2⟩, h3, h4⟩, rfl⟩, hx⟩
      rcases hx with hx | hx
      · left
        by_cases hp : p.2 = 0
        · exact ⟨p.1, ⟨h1, h2⟩, by rw [hpb]; congr 1; exact Prod.ext rfl hp.symm⟩
        · exfalso
          have hp' : 0 < p.2 := lt_of_le_of_ne h3 (Ne.symm hp)
          refine hx.2 (openRectTwo_subset_interior_rectTwo _ _ _ _ ⟨⟨?_, ?_⟩, ?_, ?_⟩)
          · rw [hA0]; linarith
          · rw [hA0]; linarith
          · rw [hA1]; linarith
          · rw [hA1]; linarith
      · right
        obtain ⟨i, hi⟩ := mem_iUnion.mp hx
        have hxi : A p ∈ Hm i := (hHm i).isPolyhedron.isClosed.frontier_subset hi
        by_cases hij : i = j
        · rw [hij, hHmj] at hxi
          have hp : p.2 = 1 := by
            have := (mem_rectTwo.mp hxi).2.1
            rw [hA1] at this
            linarith
          exact ⟨p.1, ⟨h1, h2⟩, by rw [hpt]; congr 1; exact Prod.ext rfl hp.symm⟩
        · rw [hHmi i hij] at hxi
          have := (mem_rectTwo.mp hxi).2.1
          rw [hA1] at this
          linarith
    · rintro _ (⟨t, ht, rfl⟩ | ⟨t, ht, rfl⟩)
      · exact ⟨⟨(t, 0), ⟨ht, by norm_num⟩, rfl⟩, Or.inl (hbotfr ⟨t, ht, rfl⟩)⟩
      · exact ⟨⟨(t, 1), ⟨ht, by norm_num⟩, rfl⟩,
          Or.inr (mem_iUnion.mpr ⟨j, htopfr ⟨t, ht, rfl⟩⟩)⟩
  have hgbot : g '' (pb '' Icc 0 1) = α '' Icc 0 1 := by
    rw [image_image]
    exact image_congr fun t ht => hσ0 t ht
  have hgtop : g '' (pt '' Icc 0 1) = β '' Icc 0 1 := by
    rw [image_image]
    rcases hψjβ with h | h
    · exact image_congr fun t ht => (hσ1 t ht).trans (h t ht)
    · have heq : EqOn (fun x => g (pt x)) (fun t => β (1 - t)) (Icc 0 1) :=
        fun t ht => (hσ1 t ht).trans (h t ht)
      rw [image_congr heq]
      have hrev : (fun t : ℝ => 1 - t) '' Icc 0 1 = Icc 0 1 := by
        rw [image_const_sub_Icc]
        norm_num
      rw [show (fun t : ℝ => β (1 - t)) = β ∘ fun t => 1 - t from rfl, image_comp, hrev]
  refine ⟨g ∘ A, hσ, ?_, ?_, hσ0, ?_⟩
  · rw [image_comp, ← hg.image_eq]
    exact image_mono hSsub
  · rw [image_comp, ← hCirc, ← hg.bijOn.injOn.image_inter hSsub hCircsub, hmodel, image_union,
      hgbot, hgtop]
  · rcases hψjβ with h | h
    · exact Or.inl fun t ht => (hσ1 t ht).trans (h t ht)
    · exact Or.inr fun t ht => (hσ1 t ht).trans (h t ht)

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

theorem IsPLSphere.exists_holed_strip {ι : Type*} [Finite ι] {S : Set E} (hS : IsPLSphere 2 S)
    {D : ι → Set E} {q : ι → (Fin 3 → ℝ) → E}
    (hq : ∀ i, IsPLHomeomorphOn (q i) (Convexity.StdSimplex.coordinateSet ℝ (Fin 3)) (D i)) (hDS : ∀ i, D i ⊆ S)
    (hdis : Pairwise fun i j => Disjoint (D i) (D j)) {i₀ j : ι} (hj : j ≠ i₀) {α β : ℝ → E}
    (hα : IsPLHomeomorphOn α (Icc 0 1) (α '' Icc 0 1))
    (hαc : α '' Icc 0 1 ⊆ q i₀ '' stdSimplexBoundary 2)
    (hβ : IsPLHomeomorphOn β (Icc 0 1) (β '' Icc 0 1))
    (hβc : β '' Icc 0 1 ⊆ q j '' stdSimplexBoundary 2) {r : E → E}
    (hr : IsPLHomeomorphOn r (q j '' stdSimplexBoundary 2) (q j '' stdSimplexBoundary 2))
    (hnr : ¬ IsPLCirclePositive (q j '' stdSimplexBoundary 2) r)
    (hrβ : ∀ t ∈ Icc (0 : ℝ) 1, r (β t) = β (1 - t)) :
    ∃ σ : ℝ × ℝ → E,
      IsPLHomeomorphOn σ (Icc 0 1 ×ˢ Icc 0 1) (σ '' (Icc 0 1 ×ˢ Icc 0 1)) ∧
      σ '' (Icc 0 1 ×ˢ Icc 0 1) ⊆ S \ ⋃ i, (D i \ q i '' stdSimplexBoundary 2) ∧
      σ '' (Icc 0 1 ×ˢ Icc 0 1) ∩ ⋃ i, q i '' stdSimplexBoundary 2 =
        α '' Icc 0 1 ∪ β '' Icc 0 1 ∧
      (∀ t ∈ Icc (0 : ℝ) 1, σ (t, 0) = α t) ∧
      ((∀ t ∈ Icc (0 : ℝ) 1, σ (t, 1) = β t) ∨ ∀ t ∈ Icc (0 : ℝ) 1, σ (t, 1) = β (1 - t)) := by
  classical
  obtain ⟨χ, Δ, hΔ, hχ, hχ0, hχi⟩ := hS.exists_holed_chart hq hDS hdis i₀
  set C := S \ (D i₀ \ q i₀ '' stdSimplexBoundary 2) with hCdef
  have hcD : ∀ i, q i '' stdSimplexBoundary 2 ⊆ D i := fun i => by
    rintro _ ⟨y, hy, rfl⟩
    exact (hq i).bijOn.mapsTo hy.1
  have hcC : ∀ i, q i '' stdSimplexBoundary 2 ⊆ C := by
    intro i x hx
    by_cases hi : i = i₀
    · subst hi
      exact ⟨hDS i (hcD i hx), fun h => h.2 hx⟩
    · exact (hχi i hi).1 (hcD i hx)
  have hcpoly : ∀ i, IsPolyhedron (q i '' stdSimplexBoundary 2) := fun i =>
    ((hq i).isPLSphere_image_stdSimplexBoundary (n := 1)).isPolyhedron
  have hintA : ∀ i, i ≠ i₀ → interior (χ '' D i) =
      χ '' D i \ χ '' (q i '' stdSimplexBoundary 2) := by
    intro i hi
    have hcl : IsClosed (χ '' D i) :=
      (IsPLBall.of_isPLHomeomorphOn ⟨q i, hq i⟩ (hχi i hi).2.2.1).isPolyhedron.isClosed
    rw [(hχi i hi).2.2.2, hcl.frontier_eq, sdiff_sdiff_right_self,
      inter_eq_right.mpr interior_subset]
  obtain ⟨hPeq, hPC⟩ := image_sdiff_iUnion_sdiff_eq (S := S) i₀ hχ.bijOn rfl
    (fun i hi => (hχi i hi).1) hcD hintA
  let H : {i // i ≠ i₀} → Set Plane := fun k => χ '' D k.1
  have hH : ∀ k, IsPLBall 2 (H k) := fun k =>
    IsPLBall.of_isPLHomeomorphOn ⟨q k.1, hq k.1⟩ (hχi k.1 k.2).2.2.1
  have hHdis : Pairwise fun k l => Disjoint (H k) (H l) := by
    intro k l hkl
    exact (hdis fun h => hkl (Subtype.ext h)).image hχ.bijOn.injOn (hχi k.1 k.2).1
      (hχi l.1 l.2).1
  have hχc : ∀ i, IsPLHomeomorphOn χ (q i '' stdSimplexBoundary 2)
      (χ '' (q i '' stdSimplexBoundary 2)) := fun i => hχ.restrict (hcpoly i) (hcC i)
  have hχj : IsPLHomeomorphOn χ (q j '' stdSimplexBoundary 2) (frontier (H ⟨j, hj⟩)) := by
    have h := hχc j
    rwa [(hχi j hj).2.2.2] at h
  have hαpoly : IsPolyhedron (α '' Icc 0 1) :=
    ((isPLBall_Icc zero_lt_one).of_isPLHomeomorphOn hα).isPolyhedron
  have hβpoly : IsPolyhedron (β '' Icc 0 1) :=
    ((isPLBall_Icc zero_lt_one).of_isPLHomeomorphOn hβ).isPolyhedron
  have hαpl : IsPLHomeomorphOn (χ ∘ α) (Icc 0 1) ((χ ∘ α) '' Icc 0 1) := by
    rw [image_comp]
    exact hα.trans (hχ.restrict hαpoly (hαc.trans (hcC i₀)))
  have hβpl : IsPLHomeomorphOn (χ ∘ β) (Icc 0 1) ((χ ∘ β) '' Icc 0 1) := by
    rw [image_comp]
    exact hβ.trans (hχ.restrict hβpoly (hβc.trans (hcC j)))
  have hαfr : (χ ∘ α) '' Icc 0 1 ⊆ frontier Δ := by
    rw [image_comp, ← hχ0]
    exact image_mono hαc
  have hβfr : (χ ∘ β) '' Icc 0 1 ⊆ frontier (H ⟨j, hj⟩) := by
    rw [image_comp, ← hχj.image_eq]
    exact image_mono hβc
  have hr' : IsPLHomeomorphOn (χ ∘ r ∘ Function.invFunOn χ (q j '' stdSimplexBoundary 2))
      (frontier (H ⟨j, hj⟩)) (frontier (H ⟨j, hj⟩)) :=
    (hχj.symm.trans hr).trans hχj
  have hnr' : ¬ IsPLCirclePositive (frontier (H ⟨j, hj⟩))
      (χ ∘ r ∘ Function.invFunOn χ (q j '' stdSimplexBoundary 2)) := by
    intro hpos
    apply hnr
    have hc := hpos.conj hr'.bijOn.mapsTo hχj.symm.isPiecewiseAffineOn.continuousOn
      hχj.symm.bijOn
    refine hc.of_eqOn fun y hy => ?_
    have hχy : χ y ∈ frontier (H ⟨j, hj⟩) := hχj.bijOn.mapsTo hy
    have h1 : Function.invFunOn (Function.invFunOn χ (q j '' stdSimplexBoundary 2))
        (frontier (H ⟨j, hj⟩)) y = χ y := by
      have h := hχj.symm.bijOn.injOn.leftInvOn_invFunOn hχy
      rwa [hχj.bijOn.invOn_invFunOn.1 hy] at h
    change r y = Function.invFunOn χ _ (χ (r (Function.invFunOn χ _
      (Function.invFunOn (Function.invFunOn χ _) _ y))))
    rw [h1, hχj.bijOn.invOn_invFunOn.1 hy, hχj.bijOn.invOn_invFunOn.1 (hr.bijOn.mapsTo hy)]
  have hrβ' : ∀ t ∈ Icc (0 : ℝ) 1,
      (χ ∘ r ∘ Function.invFunOn χ (q j '' stdSimplexBoundary 2)) ((χ ∘ β) t) =
        (χ ∘ β) (1 - t) := by
    intro t ht
    change χ (r (Function.invFunOn χ _ (χ (β t)))) = χ (β (1 - t))
    rw [hχj.bijOn.invOn_invFunOn.1 (hβc ⟨t, ht, rfl⟩), hrβ t ht]
  obtain ⟨σ, hσ, hσsub, hσint, hσ0, hσ1⟩ := exists_planar_strip hΔ hH
    (fun k => (hχi k.1 k.2).2.1) hHdis ⟨j, hj⟩ hαpl hαfr hβpl hβfr hr' hnr' hrβ'
  have hσpoly : IsPolyhedron (σ '' (Icc (0 : ℝ) 1 ×ˢ Icc (0 : ℝ) 1)) :=
    (isHPolytope_Icc.prod isHPolytope_Icc).isPolyhedron.image_of_isPiecewiseAffineOn
      hσ.isPiecewiseAffineOn hσ.bijOn.injOn
  have hσΔ : σ '' (Icc (0 : ℝ) 1 ×ˢ Icc (0 : ℝ) 1) ⊆ Δ := hσsub.trans sdiff_subset
  have hχback : ∀ X : Set Plane, X ⊆ Δ → χ '' (Function.invFunOn χ C '' X) = X := by
    intro X hX
    rw [image_image]
    exact (image_congr fun x hx => hχ.bijOn.surjOn.rightInvOn_invFunOn (hX hx)).trans
      (image_id X)
  have hinvP : Function.invFunOn χ C '' (Δ \ ⋃ k, interior (H k)) =
      S \ ⋃ i, (D i \ q i '' stdSimplexBoundary 2) := by
    rw [← hPeq, hχ.bijOn.injOn.invFunOn_image hPC]
  have hsub1 : (Function.invFunOn χ C ∘ σ) '' (Icc 0 1 ×ˢ Icc 0 1) ⊆
      S \ ⋃ i, (D i \ q i '' stdSimplexBoundary 2) := by
    rw [image_comp, ← hinvP]
    exact image_mono hσsub
  have hback : ∀ i, ∀ y ∈ q i '' stdSimplexBoundary 2, Function.invFunOn χ C (χ y) = y :=
    fun i y hy => hχ.bijOn.invOn_invFunOn.1 (hcC i hy)
  refine ⟨Function.invFunOn χ C ∘ σ, ?_, hsub1, ?_, ?_, ?_⟩
  · rw [image_comp]
    exact hσ.trans (hχ.symm.restrict hσpoly hσΔ)
  · have hsub2 : ⋃ i, q i '' stdSimplexBoundary 2 ⊆ C := iUnion_subset hcC
    have hsub3 : α '' Icc 0 1 ∪ β '' Icc 0 1 ⊆ C :=
      union_subset (hαc.trans (hcC i₀)) (hβc.trans (hcC j))
    have hsplit : ⋃ i, q i '' stdSimplexBoundary 2 =
        q i₀ '' stdSimplexBoundary 2 ∪ ⋃ k : {i // i ≠ i₀}, q k.1 '' stdSimplexBoundary 2 := by
      ext x
      simp only [mem_union, mem_iUnion]
      constructor
      · rintro ⟨i, hi⟩
        by_cases h : i = i₀
        · subst h
          exact Or.inl hi
        · exact Or.inr ⟨⟨i, h⟩, hi⟩
      · rintro (h | ⟨k, hk⟩)
        · exact ⟨i₀, h⟩
        · exact ⟨k.1, hk⟩
    have hL : χ '' ((Function.invFunOn χ C ∘ σ) '' (Icc 0 1 ×ˢ Icc 0 1) ∩
        ⋃ i, q i '' stdSimplexBoundary 2) =
        σ '' (Icc 0 1 ×ˢ Icc 0 1) ∩ (frontier Δ ∪ ⋃ k, frontier (H k)) := by
      rw [hχ.bijOn.injOn.image_inter (hsub1.trans hPC) hsub2, image_comp, hχback _ hσΔ, hsplit,
        image_union, image_iUnion, hχ0]
      congr 2
      exact iUnion_congr fun k => (hχi k.1 k.2).2.2.2
    have hR : χ '' (α '' Icc 0 1 ∪ β '' Icc 0 1) = (χ ∘ α) '' Icc 0 1 ∪ (χ ∘ β) '' Icc 0 1 := by
      rw [image_union, image_comp, image_comp]
    rw [← hχ.bijOn.injOn.image_eq_image_iff (inter_subset_left.trans (hsub1.trans hPC)) hsub3,
      hL, hR, hσint]
  · intro t ht
    change Function.invFunOn χ C (σ (t, 0)) = α t
    rw [hσ0 t ht]
    exact hback i₀ (α t) (hαc ⟨t, ht, rfl⟩)
  · rcases hσ1 with h | h
    · refine Or.inl fun t ht => ?_
      change Function.invFunOn χ C (σ (t, 1)) = β t
      rw [h t ht]
      exact hback j (β t) (hβc ⟨t, ht, rfl⟩)
    · refine Or.inr fun t ht => ?_
      change Function.invFunOn χ C (σ (t, 1)) = β (1 - t)
      rw [h t ht]
      have ht' : 1 - t ∈ Icc (0 : ℝ) 1 := ⟨by linarith [ht.2], by linarith [ht.1]⟩
      exact hback j (β (1 - t)) (hβc ⟨1 - t, ht', rfl⟩)

end DifferentialGeometry.Topology.PiecewiseLinear
