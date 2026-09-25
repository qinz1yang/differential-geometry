import DifferentialGeometry.Topology.PiecewiseLinear.Section34SquareShellCrosscutTools

open Set

namespace DifferentialGeometry.Topology.PiecewiseLinear

private theorem half_path_data {γ : ℝ → ℝ × ℝ} {c d : ℝ} (hc : c ≤ 2 * d)
    (hγ : IsPiecewiseAffineOn γ (Icc (-d) d))
    (hbd : γ '' Icc (-d) d ⊆ frontier (Icc (0 : ℝ) 1 ×ˢ Icc (0 : ℝ) 1)) (b : Bool) :
    let σ := fun r : ℝ => if b then -r / 2 else r / 2
    IsPiecewiseAffineOn (γ ∘ σ) (Icc 0 c) ∧
      MapsTo (γ ∘ σ) (Icc 0 c) (frontier (Icc (0 : ℝ) 1 ×ˢ Icc (0 : ℝ) 1)) ∧
      MapsTo σ (Icc 0 c) (Icc (-d) d) := by
  let σ := fun r : ℝ => if b then -r / 2 else r / 2
  have hmaps : MapsTo σ (Icc 0 c) (Icc (-d) d) := by
    intro r hr
    cases b <;> simp only [σ, Bool.false_eq_true, ↓reduceIte, mem_Icc] <;>
      constructor <;> linarith [hr.1, hr.2]
  have hσ : IsPiecewiseAffineOn σ (Icc 0 c) := by
    have h := isPiecewiseAffineOn_of_affine_of_isHPolytope (P := Icc (0 : ℝ) c)
      ((if b then (-1 / 2 : ℝ) else 1 / 2) • AffineMap.id ℝ ℝ) isHPolytope_Icc
    apply h.congr
    intro r _
    change (if b then -r / 2 else r / 2) = (if b then (-1 / 2 : ℝ) else 1 / 2) * r
    cases b <;> simp only [Bool.false_eq_true, ↓reduceIte] <;> ring
  have hinter : Icc (0 : ℝ) c ∩ σ ⁻¹' Icc (-d) d = Icc 0 c := inter_eq_left.mpr hmaps
  exact ⟨hinter ▸ hγ.comp hσ, fun r hr => hbd (mem_image_of_mem γ (hmaps hr)), hmaps⟩

theorem exists_expanded_square_crosscuts
    {A B : Set (ℝ × ℝ)} {δ ε : ℝ → ℝ × ℝ}
    (hδ : IsPLHomeomorphOn δ (Icc 0 1) A) (hε : IsPLHomeomorphOn ε (Icc 0 1) B)
    (hεzero : ε 0 = δ 0) (hεone : ε 1 = δ 1)
    (hA : A ⊆ frontier (Icc (0 : ℝ) 1 ×ˢ Icc (0 : ℝ) 1))
    (hB : B ⊆ frontier (Icc (0 : ℝ) 1 ×ˢ Icc (0 : ℝ) 1))
    (hAB : A ∩ B = {δ 0, δ 1}) {γ : Fin 2 → ℝ → ℝ × ℝ} {c d : ℝ}
    (hc : 0 < c) (hcd : c ≤ 2 * d)
    (hγ : ∀ k, IsPLHomeomorphOn (γ k) (Icc (-d) d) (γ k '' Icc (-d) d))
    (hγbd : ∀ k, γ k '' Icc (-d) d ⊆ frontier (Icc (0 : ℝ) 1 ×ˢ Icc (0 : ℝ) 1))
    (hγzero : γ 0 0 = δ 0) (hγone : γ 1 0 = δ 1)
    (hdis : Disjoint (γ 0 '' Icc (-d) d) (γ 1 '' Icc (-d) d)) :
    let ηX := fun (k : Fin 2) (r : ℝ) => section34SquareShellFlatten c (γ k (-r / 2), r)
    let ηY := fun (k : Fin 2) (r : ℝ) => section34SquareShellFlatten c (γ k (r / 2), r)
    let X := A ∪ (ηX 0 '' Icc 0 c ∪ ηX 1 '' Icc 0 c)
    let Y := B ∪ (ηY 0 '' Icc 0 c ∪ ηY 1 '' Icc 0 c)
    let Q := Icc (-c) (1 + c) ×ˢ Icc (-c) (1 + c)
    ∃ α β : ℝ → ℝ × ℝ, IsPLHomeomorphOn α (Icc 0 1) X ∧
      IsPLHomeomorphOn β (Icc 0 1) Y ∧
      α 0 = ηX 0 c ∧ α 1 = ηX 1 c ∧ β 0 = ηY 0 c ∧ β 1 = ηY 1 c ∧
      X ⊆ Q ∧ Y ⊆ Q ∧
      X ∩ (Icc (0 : ℝ) 1 ×ˢ Icc (0 : ℝ) 1) = A ∧
      Y ∩ (Icc (0 : ℝ) 1 ×ˢ Icc (0 : ℝ) 1) = B ∧
      X ∩ frontier Q = {α 0, α 1} ∧ Y ∩ frontier Q = {β 0, β 1} ∧
      X ∩ Y = {δ 0, δ 1} := by
  let P := Icc (0 : ℝ) 1 ×ˢ Icc (0 : ℝ) 1
  let Q := Icc (-c) (1 + c) ×ˢ Icc (-c) (1 + c)
  let σ := fun (b : Bool) (r : ℝ) => if b then -r / 2 else r / 2
  let η := fun (b : Bool) (k : Fin 2) (r : ℝ) =>
    section34SquareShellFlatten c (γ k (σ b r), r)
  let T := fun b k => η b k '' Icc 0 c
  have hhalf (b : Bool) (k : Fin 2) :=
    half_path_data hcd (hγ k).isPiecewiseAffineOn (hγbd k) b
  have harc (b : Bool) (k : Fin 2) :=
    isPLHomeomorphOn_square_shell_path hc (hhalf b k).1 (hhalf b k).2.1
  have hηzero (b : Bool) (k : Fin 2) : η b k 0 = γ k 0 := by
    simpa only [η, σ, Function.comp_apply, neg_zero, zero_div, ite_self] using (harc b k).2.2.1
  have hTP (b : Bool) (k : Fin 2) : T b k ∩ P = {γ k 0} := by
    simpa only [T, η, σ, Function.comp_apply, neg_zero, zero_div, ite_self, P] using
      (harc b k).2.2.2.1
  have hTQ (b : Bool) (k : Fin 2) : T b k ⊆ Q := (harc b k).2.1
  have hTfront (b : Bool) (k : Fin 2) : T b k ∩ frontier Q = {η b k c} :=
    (harc b k).2.2.2.2
  have h01 (b b' : Bool) : Disjoint (T b 0) (T b' 1) := by
    apply square_shell_paths_disjoint_of_disjoint_base_images hc
      (hhalf b 0).2.1 (hhalf b' 1).2.1
    have hs₀ : (γ 0 ∘ σ b) '' Icc 0 c ⊆ γ 0 '' Icc (-d) d := by
      rintro _ ⟨r, hr, rfl⟩
      exact mem_image_of_mem (γ 0) ((hhalf b 0).2.2 hr)
    have hs₁ : (γ 1 ∘ σ b') '' Icc 0 c ⊆ γ 1 '' Icc (-d) d := by
      rintro _ ⟨r, hr, rfl⟩
      exact mem_image_of_mem (γ 1) ((hhalf b' 1).2.2 hr)
    exact hdis.mono hs₀ hs₁
  have hsame (k : Fin 2) : T true k ∩ T false k = {γ k 0} := by
    have hz : (γ k ∘ σ true) 0 = (γ k ∘ σ false) 0 := by simp [σ]
    have hne : ∀ r ∈ Ioc (0 : ℝ) c, (γ k ∘ σ true) r ≠ (γ k ∘ σ false) r := by
      intro r hr heq
      have heq' := (hγ k).bijOn.injOn ((hhalf true k).2.2 ⟨hr.1.le, hr.2⟩)
        ((hhalf false k).2.2 ⟨hr.1.le, hr.2⟩) heq
      change -r / 2 = r / 2 at heq'
      linarith [hr.1]
    have h := square_shell_path_inter_of_pointwise_ne hc (hhalf true k).2.1
      (hhalf false k).2.1 hz hne
    simpa only [T, η, σ, Function.comp_apply, neg_zero, zero_div, ite_self] using h
  have hAP : A ⊆ P := hA.trans (isClosed_Icc.prod isClosed_Icc).frontier_subset
  have hBP : B ⊆ P := hB.trans (isClosed_Icc.prod isClosed_Icc).frontier_subset
  obtain ⟨α, hα, hαzero, hαone⟩ := exists_PL_arc_of_two_external_arcs hc hδ hAP
    (harc true 0).1 (harc true 1).1 ((hηzero true 0).trans hγzero)
    ((hηzero true 1).trans hγone)
    (hγzero ▸ hTP true 0) (hγone ▸ hTP true 1) (h01 true true)
  obtain ⟨β, hβ, hβzero, hβone⟩ := exists_PL_arc_of_two_external_arcs hc hε hBP
    (harc false 0).1 (harc false 1).1 ((hηzero false 0).trans (hγzero.trans hεzero.symm))
    ((hηzero false 1).trans (hγone.trans hεone.symm))
    ((hγzero.trans hεzero.symm) ▸ hTP false 0)
    ((hγone.trans hεone.symm) ▸ hTP false 1) (h01 false false)
  have hPQ : P ⊆ interior Q := by
    rw [interior_prod_eq, interior_Icc]
    rintro p hp
    exact ⟨by constructor <;> linarith [hp.1.1, hp.1.2],
      by constructor <;> linarith [hp.2.1, hp.2.2]⟩
  have hAfront : A ∩ frontier Q = ∅ := by
    apply disjoint_iff_inter_eq_empty.mp
    exact disjoint_sdiff_self_right.mono_left (hAP.trans hPQ)
  have hBfront : B ∩ frontier Q = ∅ := by
    apply disjoint_iff_inter_eq_empty.mp
    exact disjoint_sdiff_self_right.mono_left (hBP.trans hPQ)
  refine ⟨α, β, hα, hβ, hαzero, hαone, hβzero, hβone,
    union_subset (hAP.trans (hPQ.trans interior_subset)) (union_subset (hTQ true 0) (hTQ true 1)),
    union_subset (hBP.trans (hPQ.trans interior_subset)) (union_subset (hTQ false 0) (hTQ false 1)),
    ?_, ?_, ?_, ?_, ?_⟩
  · change (A ∪ (T true 0 ∪ T true 1)) ∩ P = A
    rw [union_inter_distrib_right, union_inter_distrib_right,
      inter_eq_self_of_subset_left hAP, hTP, hTP, hγzero, hγone]
    exact union_eq_self_of_subset_right (union_subset (singleton_subset_iff.mpr
      (hδ.bijOn.mapsTo (by norm_num))) (singleton_subset_iff.mpr (hδ.bijOn.mapsTo (by norm_num))))
  · change (B ∪ (T false 0 ∪ T false 1)) ∩ P = B
    rw [union_inter_distrib_right, union_inter_distrib_right,
      inter_eq_self_of_subset_left hBP, hTP, hTP, hγzero, hγone, ← hεzero, ← hεone]
    exact union_eq_self_of_subset_right (union_subset (singleton_subset_iff.mpr
      (hε.bijOn.mapsTo (by norm_num))) (singleton_subset_iff.mpr (hε.bijOn.mapsTo (by norm_num))))
  · change (A ∪ (T true 0 ∪ T true 1)) ∩ frontier Q = {α 0, α 1}
    rw [union_inter_distrib_right, union_inter_distrib_right, hAfront, empty_union,
      hTfront, hTfront, hαzero, hαone, singleton_union]
    rfl
  · change (B ∪ (T false 0 ∪ T false 1)) ∩ frontier Q = {β 0, β 1}
    rw [union_inter_distrib_right, union_inter_distrib_right, hBfront, empty_union,
      hTfront, hTfront, hβzero, hβone, singleton_union]
    rfl
  · exact inter_two_external_arc_unions hAP hBP hAB
      (hγzero ▸ hTP true 0) (hγone ▸ hTP true 1)
      (hγzero ▸ hTP false 0) (hγone ▸ hTP false 1)
      (hγzero ▸ hsame 0) (hγone ▸ hsame 1) (h01 true false) (h01 false true).symm

end DifferentialGeometry.Topology.PiecewiseLinear
