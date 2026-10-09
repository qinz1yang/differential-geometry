import DifferentialGeometry.Topology.PiecewiseLinear.Section34CollaredSheetAnnuli
import DifferentialGeometry.Topology.PiecewiseLinear.Section34CollaredSheetAnnuliRibbons

open Set

namespace DifferentialGeometry.Topology.PiecewiseLinear

private theorem image_radial_band {E B M : Type*} [SMul ℝ B]
    (u : E → M) (f : B × ℝ → E) (v : B) (d : ℝ) :
    u '' (f '' (((fun r : ℝ => r • v) '' Icc 0 d) ×ˢ Icc (0 : ℝ) 1)) =
      (fun z : ℝ × ℝ => u (f (z.1 • v, z.2))) '' (Icc 0 d ×ˢ Icc (0 : ℝ) 1) := by
  rw [← image_comp]
  have hp : ((fun r : ℝ => r • v) '' Icc 0 d) ×ˢ Icc (0 : ℝ) 1 =
      Prod.map (fun r : ℝ => r • v) id '' (Icc 0 d ×ˢ Icc (0 : ℝ) 1) := by
    rw [prodMap_image_prod, image_id]
  rw [hp, ← image_comp]
  rfl

theorem Section34SeamMarkedBandFilling.exists_enlargement_with_sheet_annuli
    {M : Type*} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
    {Cc Cp Cq As Bs S T D F J₀ J₁ : Set M}
    (h : Section34SeamMarkedBandFilling Cc Cp Cq As Bs S T D F J₀ J₁) :
    ∃ (P V X Y : Set (EuclideanSpace ℝ (Fin 3))) (u : EuclideanSpace ℝ (Fin 3) → M)
      (H : (ℝ × ℝ) × ℝ → EuclideanSpace ℝ (Fin 3)) (c : ℝ)
      (C : Fin 2 → Set (EuclideanSpace ℝ (Fin 3)))
      (f : Fin 2 → (ℝ × ℝ) × ℝ → EuclideanSpace ℝ (Fin 3)) (α β : Fin 2 → Bool),
      IsPLBall 3 P ∧ IsPLHomeomorphInto 3 u P ∧ u '' P = Cc ∧
      V ⊆ P ∧ u '' V ⊆ interior S ∧ 0 < c ∧ c ≤ 1 ∧
      IsCylindricalDiagram H (Icc (-c) (1 + c) ×ˢ Icc (-c) (1 + c)) V ∧
      (∀ z ∈ Icc (-c) (1 + c) ×ˢ Icc (-c) (1 + c), H (z, 0) = H (z, 1)) ∧
      (∀ k, IsCylindricalDiagram (f k) spliceSquare (C k) ∧ C k ⊆ P ∧
        u '' (f k '' section34MarkedAxis) = ![J₀, J₁] k) ∧
      IsPLAnnulusWithEnds X
        (f 0 '' ({(if α 0 then -c / 2 else c / 2, 0)} ×ˢ Icc (0 : ℝ) 1))
        (f 1 '' ({(if α 1 then -c / 2 else c / 2, 0)} ×ˢ Icc (0 : ℝ) 1)) ∧
      IsPLAnnulusWithEnds Y
        (f 0 '' ({(0, if β 0 then -c / 2 else c / 2)} ×ˢ Icc (0 : ℝ) 1))
        (f 1 '' ({(0, if β 1 then -c / 2 else c / 2)} ×ˢ Icc (0 : ℝ) 1)) ∧
      X ⊆ P ∧ Y ⊆ P ∧ u '' X = u '' V ∩ As ∧ u '' Y = u '' V ∩ Bs := by
  obtain ⟨P, u, R, g, a, A₀, A₁, δ₀, δ₁, hP, hu, hcell, hRfin, -, hRP, -,
    hg, hends, -, -, -, hfirst, hsecond, -, -, ha, -, hzero, hone,
    hδ₀, hδ₁, hδ₀₀, hδ₀₁, hδ₁₀, hδ₁₁, hcover, -, hface₀, hface₁,
    C, f, α, β, hCdis, -, hfamily, c, L, W, ρ, H,
    -, hH, hHends, -, -, hsupport, hc, hc1, -, -, -, -, -, -, -, hWP, -, hρ,
    hρzero, -, -, -, -, hlevels, -⟩ := h
  let _ : Finite R.faces := hRfin.to_subtype
  let I := Icc (0 : ℝ) 1
  let X₀ := g '' (A₀ ×ˢ I)
  let X₁ := g '' (A₁ ×ˢ I)
  let v₀ := fun k : Fin 2 => (if α k then (-1 : ℝ) else 1, (0 : ℝ))
  let v₁ := fun k : Fin 2 => ((0 : ℝ), if β k then (-1 : ℝ) else 1)
  let Y₀ := fun k => f k '' (((fun r : ℝ => r • v₀ k) '' Icc 0 (c / 2)) ×ˢ I)
  let Y₁ := fun k => f k '' (((fun r : ℝ => r • v₁ k) '' Icc 0 (c / 2)) ×ˢ I)
  have hA₀ : A₀ ⊆ I ×ˢ I :=
    (subset_union_left.trans hcover.subset).trans (isClosed_Icc.prod isClosed_Icc).frontier_subset
  have hA₁ : A₁ ⊆ I ×ˢ I :=
    (subset_union_right.trans hcover.subset).trans (isClosed_Icc.prod isClosed_Icc).frontier_subset
  have hX₀R : X₀ ⊆ R.space := (image_mono (prod_mono_left hA₀)).trans hg.image_eq.subset
  have hX₁R : X₁ ⊆ R.space := (image_mono (prod_mono_left hA₁)).trans hg.image_eq.subset
  have haxisP (k : Fin 2) : f k '' section34MarkedAxis ⊆ P :=
    ((image_mono (prod_mono_left (singleton_subset_iff.mpr
      (by norm_num [spliceSquare, Prod.le_def])))).trans (hfamily k).2.2.1.image_eq.subset).trans
      ((hfamily k).2.1.trans interior_subset)
  have haxis (k : Fin 2) : g '' ({a k} ×ˢ I) = f k '' section34MarkedAxis := by
    apply (hu.injOn.image_eq_image_iff
      (((image_mono (prod_mono_left (singleton_subset_iff.mpr
        ((isClosed_Icc.prod isClosed_Icc).frontier_subset (ha k))))).trans
          hg.image_eq.subset).trans hRP) (haxisP k)).mp
    rw [(hfamily k).2.2.2.2.1, ← image_comp]
    fin_cases k
    · exact hzero
    · exact hone
  have hX₀ := hg.isPLAnnulusWithEnds_base_arc hends hδ₀ hA₀
  have hX₁ := hg.isPLAnnulusWithEnds_base_arc hends hδ₁ hA₁
  rw [hδ₀₀, hδ₀₁, haxis 0, haxis 1] at hX₀
  rw [hδ₁₀, hδ₁₁, haxis 0, haxis 1] at hX₁
  have hribbons (k : Fin 2) := (hfamily k).2.2.1.outgoing_ribbon_annuli (d := c / 2)
    (hfamily k).2.2.2.1 (div_pos hc (by norm_num)) (by linarith)
    (hfamily k).2.2.2.2.2.2.2.2.2.2
  have hY₀C (k : Fin 2) : Y₀ k ⊆ C k := (hribbons k).2.2.1
  have hY₁C (k : Fin 2) : Y₁ k ⊆ C k := (hribbons k).2.2.2.1
  have hwhole₀ := hX₀.union_two_external_annuli hX₀R
    (hribbons 0).1 (hribbons 1).1 (hribbons 0).2.2.2.2.1 (hribbons 1).2.2.2.2.1
    (hCdis.mono (hY₀C 0) (hY₀C 1))
  have hwhole₁ := hX₁.union_two_external_annuli hX₁R
    (hribbons 0).2.1 (hribbons 1).2.1 (hribbons 0).2.2.2.2.2 (hribbons 1).2.2.2.2.2
    (hCdis.mono (hY₁C 0) (hY₁C 1))
  have hcore₀ (k : Fin 2) : (fun z : ℝ × ℝ => u (f k (z.1 • v₀ k, z.2))) ''
      ({0} ×ˢ I) ⊆ F := by
    rintro _ ⟨⟨r, s⟩, ⟨hr, hs⟩, rfl⟩
    change r = 0 at hr
    subst r
    simp only [zero_smul]
    have hx : f k (0, s) ∈ X₀ := by
      have hz : f k (0, s) ∈ f k '' section34MarkedAxis := ⟨(0, s), ⟨rfl, hs⟩, rfl⟩
      fin_cases k
      · exact hX₀.rims_subset.1 hz
      · exact hX₀.rims_subset.2 hz
    exact hface₀.subset (show u (f k (0, s)) ∈ (u ∘ g) '' (A₀ ×ˢ I) from
      image_comp u g _ ▸ mem_image_of_mem u hx)
  have hcore₁ (k : Fin 2) : (fun z : ℝ × ℝ => u (f k (z.1 • v₁ k, z.2))) ''
      ({0} ×ˢ I) ⊆ D := by
    rintro _ ⟨⟨r, s⟩, ⟨hr, hs⟩, rfl⟩
    change r = 0 at hr
    subst r
    simp only [zero_smul]
    have hx : f k (0, s) ∈ X₁ := by
      have hz : f k (0, s) ∈ f k '' section34MarkedAxis := ⟨(0, s), ⟨rfl, hs⟩, rfl⟩
      fin_cases k
      · exact hX₁.rims_subset.1 hz
      · exact hX₁.rims_subset.2 hz
    exact hface₁.subset (show u (f k (0, s)) ∈ (u ∘ g) '' (A₁ ×ˢ I) from
      image_comp u g _ ▸ mem_image_of_mem u hx)
  have hlevel₀ (t : ℝ) (ht : t ∈ Ioc (0 : ℝ) c) :
      (u ∘ ρ) '' (frontier R.space ×ˢ {t}) ∩ As =
        ⋃ k, (fun z : ℝ × ℝ => u (f k (z.1 • v₀ k, z.2))) '' ({t / 2} ×ˢ I) := by
    rw [(hlevels t ht).1]
    apply iUnion_congr
    intro k
    ext y
    simp only [mem_image, Prod.exists, mem_prod, mem_singleton_iff]
    cases hα : α k <;> simp [v₀, hα, Prod.smul_mk, smul_eq_mul, neg_div, I]
  have hlevel₁ (t : ℝ) (ht : t ∈ Ioc (0 : ℝ) c) :
      (u ∘ ρ) '' (frontier R.space ×ˢ {t}) ∩ Bs =
        ⋃ k, (fun z : ℝ × ℝ => u (f k (z.1 • v₁ k, z.2))) '' ({t / 2} ×ˢ I) := by
    rw [(hlevels t ht).2]
    apply iUnion_congr
    intro k
    ext y
    simp only [mem_image, Prod.exists, mem_prod, mem_singleton_iff]
    cases hβ : β k <;> simp [v₁, hβ, Prod.smul_mk, smul_eq_mul, neg_div, I]
  have htrace₀ := collar_union_trace_eq_radial_bands (isPolyhedron_space R).isClosed.frontier_subset
    hρ.image_eq hρzero (inter_comm _ _ ▸ hfirst) hcore₀ hlevel₀
  have htrace₁ := collar_union_trace_eq_radial_bands (isPolyhedron_space R).isClosed.frontier_subset
    hρ.image_eq hρzero (inter_comm _ _ ▸ hsecond) hcore₁ hlevel₁
  have htwo (Z : Fin 2 → Set M) : (⋃ k, Z k) = Z 0 ∪ Z 1 := by
    ext y
    simp only [mem_iUnion, mem_union]
    constructor
    · rintro ⟨k, hk⟩
      fin_cases k
      · exact Or.inl hk
      · exact Or.inr hk
    · rintro (hy | hy)
      · exact ⟨0, hy⟩
      · exact ⟨1, hy⟩
  refine ⟨P, R.space ∪ W, X₀ ∪ (Y₀ 0 ∪ Y₀ 1), X₁ ∪ (Y₁ 0 ∪ Y₁ 1), u, H, c,
    C, f, α, β, hP, hu, hcell, union_subset hRP (hWP.trans interior_subset), hsupport,
    hc, hc1, hH, hHends, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro k
    exact ⟨(hfamily k).2.2.1, (hfamily k).2.1.trans interior_subset,
      (hfamily k).2.2.2.2.1⟩
  · simpa only [Prod.smul_mk, smul_eq_mul, mul_zero, mul_ite, mul_neg_one, mul_one,
      neg_div, v₀, X₀, Y₀, I] using hwhole₀
  · simpa only [Prod.smul_mk, smul_eq_mul, mul_zero, mul_ite, mul_neg_one, mul_one,
      neg_div, v₁, X₁, Y₁, I] using hwhole₁
  · exact union_subset (hX₀R.trans hRP) (union_subset
      ((hY₀C 0).trans ((hfamily 0).2.1.trans interior_subset))
      ((hY₀C 1).trans ((hfamily 1).2.1.trans interior_subset)))
  · exact union_subset (hX₁R.trans hRP) (union_subset
      ((hY₁C 0).trans ((hfamily 0).2.1.trans interior_subset))
      ((hY₁C 1).trans ((hfamily 1).2.1.trans interior_subset)))
  · rw [htrace₀, image_union, image_union]
    have hx : u '' X₀ = F := by simpa only [X₀, I, image_comp] using hface₀
    rw [hx, htwo]
    exact congrArg (fun Z => F ∪ Z) (congrArg₂ (· ∪ ·)
      (image_radial_band u (f 0) (v₀ 0) (c / 2))
      (image_radial_band u (f 1) (v₀ 1) (c / 2)))
  · rw [htrace₁, image_union, image_union]
    have hx : u '' X₁ = D := by simpa only [X₁, I, image_comp] using hface₁
    rw [hx, htwo]
    exact congrArg (fun Z => D ∪ Z) (congrArg₂ (· ∪ ·)
      (image_radial_band u (f 0) (v₁ 0) (c / 2))
      (image_radial_band u (f 1) (v₁ 1) (c / 2)))

end DifferentialGeometry.Topology.PiecewiseLinear
