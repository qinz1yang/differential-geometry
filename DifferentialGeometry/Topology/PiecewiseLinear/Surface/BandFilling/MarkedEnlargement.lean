import DifferentialGeometry.Topology.Map.LevelTraces
import DifferentialGeometry.Topology.PiecewiseLinear.CellMapTriangulation
import DifferentialGeometry.Topology.PiecewiseLinear.Section34CollaredSheetAnnuliModel
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

theorem isPLAnnulusWithEnds_collared_sheet_traces
    {M : Type*} {P R W : Set (EuclideanSpace ℝ (Fin 3))}
    {u : EuclideanSpace ℝ (Fin 3) → M} {As Bs : Set M}
    {g : (ℝ × ℝ) × ℝ → EuclideanSpace ℝ (Fin 3)}
    {A₀ A₁ : Set (ℝ × ℝ)} {δ₀ δ₁ : ℝ → ℝ × ℝ} {a : Fin 2 → ℝ × ℝ}
    {C : Fin 2 → Set (EuclideanSpace ℝ (Fin 3))}
    {f : Fin 2 → (ℝ × ℝ) × ℝ → EuclideanSpace ℝ (Fin 3)}
    {α β : Fin 2 → Bool} {c : ℝ}
    {ρ : EuclideanSpace ℝ (Fin 3) × ℝ → EuclideanSpace ℝ (Fin 3)}
    (hRP : R ⊆ P)
    (hg : IsCylindricalDiagram g (Icc (0 : ℝ) 1 ×ˢ Icc (0 : ℝ) 1) R)
    (hends : ∀ z ∈ Icc (0 : ℝ) 1 ×ˢ Icc (0 : ℝ) 1, g (z, 0) = g (z, 1))
    (hδ₀ : IsPLHomeomorphOn δ₀ (Icc 0 1) A₀)
    (hδ₁ : IsPLHomeomorphOn δ₁ (Icc 0 1) A₁)
    (hδ₀₀ : δ₀ 0 = a 0) (hδ₀₁ : δ₀ 1 = a 1)
    (hδ₁₀ : δ₁ 0 = a 0) (hδ₁₁ : δ₁ 1 = a 1)
    (hA₀ : A₀ ⊆ Icc (0 : ℝ) 1 ×ˢ Icc (0 : ℝ) 1)
    (hA₁ : A₁ ⊆ Icc (0 : ℝ) 1 ×ˢ Icc (0 : ℝ) 1)
    (haxis : ∀ k, g '' ({a k} ×ˢ Icc (0 : ℝ) 1) = f k '' section34MarkedAxis)
    (hf : ∀ k, IsCylindricalDiagram (f k) spliceSquare (C k))
    (hfends : ∀ k, ∀ z ∈ spliceSquare, f k (z, 0) = f k (z, 1))
    (hCP : ∀ k, C k ⊆ P) (hCdis : Disjoint (C 0) (C 1))
    (hquad : ∀ k,
      f k '' (section34CrossingQuadrant (α k) (β k) ×ˢ Icc (0 : ℝ) 1) = C k ∩ R)
    (hc : 0 < c) (hc2 : c ≤ 2)
    (hAs : u '' R ∩ As = (u ∘ g) '' (A₀ ×ˢ Icc (0 : ℝ) 1))
    (hBs : u '' R ∩ Bs = (u ∘ g) '' (A₁ ×ˢ Icc (0 : ℝ) 1))
    (hW : ρ '' (frontier R ×ˢ Icc (0 : ℝ) c) = W)
    (hzero : ∀ x ∈ frontier R, ρ (x, 0) = x)
    (hlevels : ∀ t ∈ Ioc (0 : ℝ) c,
      (u ∘ ρ) '' (frontier R ×ˢ {t}) ∩ As =
        ⋃ k, (u ∘ f k) ''
          ({(if α k then -t / 2 else t / 2, 0)} ×ˢ Icc (0 : ℝ) 1) ∧
      (u ∘ ρ) '' (frontier R ×ˢ {t}) ∩ Bs =
        ⋃ k, (u ∘ f k) ''
          ({(0, if β k then -t / 2 else t / 2)} ×ˢ Icc (0 : ℝ) 1)) :
    let I := Icc (0 : ℝ) 1
    let v₀ := fun k : Fin 2 => (if α k then (-1 : ℝ) else 1, (0 : ℝ))
    let v₁ := fun k : Fin 2 => ((0 : ℝ), if β k then (-1 : ℝ) else 1)
    let X := g '' (A₀ ×ˢ I) ∪
      (f 0 '' (((fun r : ℝ => r • v₀ 0) '' Icc 0 (c / 2)) ×ˢ I) ∪
       f 1 '' (((fun r : ℝ => r • v₀ 1) '' Icc 0 (c / 2)) ×ˢ I))
    let Y := g '' (A₁ ×ˢ I) ∪
      (f 0 '' (((fun r : ℝ => r • v₁ 0) '' Icc 0 (c / 2)) ×ˢ I) ∪
       f 1 '' (((fun r : ℝ => r • v₁ 1) '' Icc 0 (c / 2)) ×ˢ I))
    IsPLAnnulusWithEnds X
      (f 0 '' ({(if α 0 then -c / 2 else c / 2, 0)} ×ˢ I))
      (f 1 '' ({(if α 1 then -c / 2 else c / 2, 0)} ×ˢ I)) ∧
    IsPLAnnulusWithEnds Y
      (f 0 '' ({(0, if β 0 then -c / 2 else c / 2)} ×ˢ I))
      (f 1 '' ({(0, if β 1 then -c / 2 else c / 2)} ×ˢ I)) ∧
    X ⊆ P ∧ Y ⊆ P ∧ u '' X = u '' (R ∪ W) ∩ As ∧
      u '' Y = u '' (R ∪ W) ∩ Bs := by
  let F := (u ∘ g) '' (A₀ ×ˢ Icc (0 : ℝ) 1)
  let D := (u ∘ g) '' (A₁ ×ˢ Icc (0 : ℝ) 1)
  have hface₀ : (u ∘ g) '' (A₀ ×ˢ Icc (0 : ℝ) 1) = F := rfl
  have hface₁ : (u ∘ g) '' (A₁ ×ˢ Icc (0 : ℝ) 1) = D := rfl
  have hRpoly : IsPolyhedron R := by
    rw [← hg.image_eq]
    exact hg.isPiecewiseAffineOn.isPolyhedron_image
      (isPLBall_unit_square.isPolyhedron.prod isHPolytope_Icc.isPolyhedron)
  let I := Icc (0 : ℝ) 1
  let X₀ := g '' (A₀ ×ˢ I)
  let X₁ := g '' (A₁ ×ˢ I)
  let v₀ := fun k : Fin 2 => (if α k then (-1 : ℝ) else 1, (0 : ℝ))
  let v₁ := fun k : Fin 2 => ((0 : ℝ), if β k then (-1 : ℝ) else 1)
  let Y₀ := fun k => f k '' (((fun r : ℝ => r • v₀ k) '' Icc 0 (c / 2)) ×ˢ I)
  let Y₁ := fun k => f k '' (((fun r : ℝ => r • v₁ k) '' Icc 0 (c / 2)) ×ˢ I)
  have hX₀R : X₀ ⊆ R := (image_mono (prod_mono_left hA₀)).trans hg.image_eq.subset
  have hX₁R : X₁ ⊆ R := (image_mono (prod_mono_left hA₁)).trans hg.image_eq.subset
  have hX₀ := hg.isPLAnnulusWithEnds_base_arc hends hδ₀ hA₀
  have hX₁ := hg.isPLAnnulusWithEnds_base_arc hends hδ₁ hA₁
  rw [hδ₀₀, hδ₀₁, haxis 0, haxis 1] at hX₀
  rw [hδ₁₀, hδ₁₁, haxis 0, haxis 1] at hX₁
  have hribbons (k : Fin 2) := (hf k).outgoing_ribbon_annuli (d := c / 2)
    (hfends k) (div_pos hc (by norm_num)) (by linarith [hc2])
    (hquad k)
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
      (u ∘ ρ) '' (frontier R ×ˢ {t}) ∩ As =
        ⋃ k, (fun z : ℝ × ℝ => u (f k (z.1 • v₀ k, z.2))) '' ({t / 2} ×ˢ I) := by
    rw [(hlevels t ht).1]
    apply iUnion_congr
    intro k
    ext y
    simp only [mem_image, Prod.exists, mem_prod, mem_singleton_iff]
    cases hα : α k <;> simp [v₀, hα, Prod.smul_mk, smul_eq_mul, neg_div, I]
  have hlevel₁ (t : ℝ) (ht : t ∈ Ioc (0 : ℝ) c) :
      (u ∘ ρ) '' (frontier R ×ˢ {t}) ∩ Bs =
        ⋃ k, (fun z : ℝ × ℝ => u (f k (z.1 • v₁ k, z.2))) '' ({t / 2} ×ˢ I) := by
    rw [(hlevels t ht).2]
    apply iUnion_congr
    intro k
    ext y
    simp only [mem_image, Prod.exists, mem_prod, mem_singleton_iff]
    cases hβ : β k <;> simp [v₁, hβ, Prod.smul_mk, smul_eq_mul, neg_div, I]
  have htrace₀ := DifferentialGeometry.Topology.collar_union_trace_eq_radial_bands hRpoly.isClosed.frontier_subset
    hW hzero hAs hcore₀ hlevel₀
  have htrace₁ := DifferentialGeometry.Topology.collar_union_trace_eq_radial_bands hRpoly.isClosed.frontier_subset
    hW hzero hBs hcore₁ hlevel₁
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
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · simpa only [Prod.smul_mk, smul_eq_mul, mul_zero, mul_ite, mul_neg_one, mul_one,
      neg_div, v₀, X₀, Y₀, I] using hwhole₀
  · simpa only [Prod.smul_mk, smul_eq_mul, mul_zero, mul_ite, mul_neg_one, mul_one,
      neg_div, v₁, X₁, Y₁, I] using hwhole₁
  · exact union_subset (hX₀R.trans hRP) (union_subset
      ((hY₀C 0).trans (hCP 0))
      ((hY₀C 1).trans (hCP 1)))
  · exact union_subset (hX₁R.trans hRP) (union_subset
      ((hY₁C 0).trans (hCP 0))
      ((hY₁C 1).trans (hCP 1)))
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
