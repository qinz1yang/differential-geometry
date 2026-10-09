import DifferentialGeometry.Topology.PiecewiseLinear.Section34CollaredFillingIntersection

open Set

namespace DifferentialGeometry.Topology.PiecewiseLinear

theorem collar_union_trace_eq_radial_bands
    {E M I : Type*} {u : E → M} {ρ : E × ℝ → E} {v : I → ℝ × ℝ → M}
    {R W S : Set E} {A F : Set M} {c : ℝ} (hSR : S ⊆ R)
    (hW : ρ '' (S ×ˢ Icc (0 : ℝ) c) = W)
    (hzero : ∀ x ∈ S, ρ (x, 0) = x) (htrace : u '' R ∩ A = F)
    (hcore : ∀ k, v k '' ({0} ×ˢ Icc (0 : ℝ) 1) ⊆ F)
    (hlevels : ∀ t ∈ Ioc (0 : ℝ) c, (u ∘ ρ) '' (S ×ˢ {t}) ∩ A =
      ⋃ k, v k '' ({t / 2} ×ˢ Icc (0 : ℝ) 1)) :
    u '' (R ∪ W) ∩ A = F ∪ ⋃ k, v k '' (Icc (0 : ℝ) (c / 2) ×ˢ Icc (0 : ℝ) 1) := by
  apply Subset.antisymm
  · rintro _ ⟨⟨x, hx, rfl⟩, hxA⟩
    rcases hx with hx | hx
    · exact Or.inl (htrace.subset ⟨mem_image_of_mem u hx, hxA⟩)
    · obtain ⟨⟨y, t⟩, ⟨hy, ht⟩, rfl⟩ := hW.symm.subset hx
      by_cases ht0 : t = 0
      · rw [ht0, hzero y hy] at hxA ⊢
        exact Or.inl (htrace.subset ⟨mem_image_of_mem u (hSR hy), hxA⟩)
      · have htp : t ∈ Ioc (0 : ℝ) c := ⟨lt_of_le_of_ne ht.1 (Ne.symm ht0), ht.2⟩
        have hm := (hlevels t htp).subset
          ⟨mem_image_of_mem (u ∘ ρ) (show (y, t) ∈ S ×ˢ {t} from ⟨hy, rfl⟩), hxA⟩
        obtain ⟨k, ⟨⟨r, s⟩, ⟨hr, hs⟩, heq⟩⟩ := mem_iUnion.mp hm
        change r = t / 2 at hr
        refine Or.inr (mem_iUnion.mpr ⟨k, (r, s), ⟨?_, hs⟩, heq⟩)
        rw [hr]
        exact ⟨div_nonneg ht.1 (by norm_num), (div_le_div_iff_of_pos_right (by norm_num)).mpr ht.2⟩
  · rintro _ (hyF | hy)
    · obtain ⟨hyR, hyA⟩ := htrace.symm.subset hyF
      exact ⟨image_mono subset_union_left hyR, hyA⟩
    · obtain ⟨k, ⟨⟨r, s⟩, ⟨hr, hs⟩, rfl⟩⟩ := mem_iUnion.mp hy
      by_cases hr0 : r = 0
      · subst r
        obtain ⟨hyR, hyA⟩ := htrace.symm.subset
          (hcore k (mem_image_of_mem (v k) (show (0, s) ∈ {0} ×ˢ Icc (0 : ℝ) 1 from
            ⟨rfl, hs⟩)))
        exact ⟨image_mono subset_union_left hyR, hyA⟩
      · have hrp : 0 < r := lt_of_le_of_ne hr.1 (Ne.symm hr0)
        have ht : 2 * r ∈ Ioc (0 : ℝ) c := by constructor <;> linarith [hr.2]
        have hm := (hlevels (2 * r) ht).symm.subset
          (mem_iUnion.mpr ⟨k, (r, s), ⟨by change r = 2 * r / 2; ring, hs⟩, rfl⟩)
        obtain ⟨⟨⟨x, t⟩, ⟨hx, htr⟩, heq⟩, hyA⟩ := hm
        change t = 2 * r at htr
        subst t
        exact ⟨⟨ρ (x, 2 * r), Or.inr (hW.subset
          (mem_image_of_mem ρ ⟨hx, ht.1.le, ht.2⟩)), heq⟩, hyA⟩

theorem Section34SeamMarkedBandFilling.exists_enlargement_with_individual_sheet_traces
    {M : Type*} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
    {Cc Cp Cq As Bs S T D F J₀ J₁ : Set M}
    (h : Section34SeamMarkedBandFilling Cc Cp Cq As Bs S T D F J₀ J₁) :
    ∃ (P V : Set (EuclideanSpace ℝ (Fin 3))) (u : EuclideanSpace ℝ (Fin 3) → M)
      (H : (ℝ × ℝ) × ℝ → EuclideanSpace ℝ (Fin 3)) (c : ℝ)
      (C : Fin 2 → Set (EuclideanSpace ℝ (Fin 3)))
      (f : Fin 2 → (ℝ × ℝ) × ℝ → EuclideanSpace ℝ (Fin 3)) (α β : Fin 2 → Bool),
      IsPLBall 3 P ∧ IsPLHomeomorphInto 3 u P ∧ u '' P = Cc ∧
      V ⊆ P ∧ u '' V ⊆ interior S ∧ 0 < c ∧ c ≤ 1 ∧
      IsCylindricalDiagram H (Icc (-c) (1 + c) ×ˢ Icc (-c) (1 + c)) V ∧
      (∀ z ∈ Icc (-c) (1 + c) ×ˢ Icc (-c) (1 + c), H (z, 0) = H (z, 1)) ∧
      Disjoint (C 0) (C 1) ∧
      (∀ k, IsCylindricalDiagram (f k) spliceSquare (C k) ∧ C k ⊆ P ∧
        (∀ z ∈ spliceSquare, f k (z, 0) = f k (z, 1)) ∧
        u '' (f k '' section34MarkedAxis) = ![J₀, J₁] k) ∧
      u '' V ∩ As = F ∪ ⋃ k,
        (fun z : ℝ × ℝ => u (f k ((if α k then -z.1 else z.1, 0), z.2))) ''
          (Icc (0 : ℝ) (c / 2) ×ˢ Icc (0 : ℝ) 1) ∧
      u '' V ∩ Bs = D ∪ ⋃ k,
        (fun z : ℝ × ℝ => u (f k ((0, if β k then -z.1 else z.1), z.2))) ''
          (Icc (0 : ℝ) (c / 2) ×ˢ Icc (0 : ℝ) 1) := by
  have hseams := h.toFaceAlignedBandFilling.seams_subset_faces
  obtain ⟨P, u, R, g, a, A₀, A₁, δ₀, δ₁, hP, hu, hcell, hRfin, -, hRP, -, -, -, -, -, -,
    hfirst, hsecond, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -,
    C, f, α, β, hCdis, -, hfamily, c, L, W, ρ, H,
    -, hH, hHends, -, -, hsupport, hc, hc1, -, -, -, -, -, -, -, hWP, -, hρ,
    hzero, -, -, -, -, hlevels, -⟩ := h
  let _ : Finite R.faces := hRfin.to_subtype
  let v₀ := fun (k : Fin 2) (z : ℝ × ℝ) => u (f k ((if α k then -z.1 else z.1, 0), z.2))
  let v₁ := fun (k : Fin 2) (z : ℝ × ℝ) => u (f k ((0, if β k then -z.1 else z.1), z.2))
  have haxis₀ (k : Fin 2) : v₀ k '' ({0} ×ˢ Icc (0 : ℝ) 1) ⊆ F := by
    rintro y ⟨⟨r, t⟩, ⟨hr, ht⟩, rfl⟩
    change r = 0 at hr
    subst r
    have hz : u (f k (0, t)) ∈ ![J₀, J₁] k :=
      (hfamily k).2.2.2.2.1.subset ⟨f k (0, t), ⟨(0, t), ⟨rfl, ht⟩, rfl⟩, rfl⟩
    have hmem : u (f k (0, t)) ∈ J₀ ∪ J₁ := by
      fin_cases k
      · exact Or.inl hz
      · exact Or.inr hz
    have hm := (hseams hmem).2
    change u (f k ((0, 0), t)) ∈ F at hm
    simpa [v₀] using hm
  have haxis₁ (k : Fin 2) : v₁ k '' ({0} ×ˢ Icc (0 : ℝ) 1) ⊆ D := by
    rintro y ⟨⟨r, t⟩, ⟨hr, ht⟩, rfl⟩
    change r = 0 at hr
    subst r
    have hz : u (f k (0, t)) ∈ ![J₀, J₁] k :=
      (hfamily k).2.2.2.2.1.subset ⟨f k (0, t), ⟨(0, t), ⟨rfl, ht⟩, rfl⟩, rfl⟩
    have hmem : u (f k (0, t)) ∈ J₀ ∪ J₁ := by
      fin_cases k
      · exact Or.inl hz
      · exact Or.inr hz
    have hm := (hseams hmem).1
    change u (f k ((0, 0), t)) ∈ D at hm
    simpa [v₁] using hm
  have hlevel₀ (t : ℝ) (ht : t ∈ Ioc (0 : ℝ) c) :
      (u ∘ ρ) '' (frontier R.space ×ˢ {t}) ∩ As =
        ⋃ k, v₀ k '' ({t / 2} ×ˢ Icc (0 : ℝ) 1) := by
    rw [(hlevels t ht).1]
    apply iUnion_congr
    intro k
    ext y
    simp only [mem_image, Prod.exists, mem_prod, mem_singleton_iff]
    simp [v₀, neg_div]
  have hlevel₁ (t : ℝ) (ht : t ∈ Ioc (0 : ℝ) c) :
      (u ∘ ρ) '' (frontier R.space ×ˢ {t}) ∩ Bs =
        ⋃ k, v₁ k '' ({t / 2} ×ˢ Icc (0 : ℝ) 1) := by
    rw [(hlevels t ht).2]
    apply iUnion_congr
    intro k
    ext y
    simp only [mem_image, Prod.exists, mem_prod, mem_singleton_iff]
    simp [v₁, neg_div]
  refine ⟨P, R.space ∪ W, u, H, c, C, f, α, β, hP, hu, hcell,
    union_subset hRP (hWP.trans interior_subset), hsupport, hc, hc1, hH, hHends,
    hCdis, ?_, ?_, ?_⟩
  · intro k
    exact ⟨(hfamily k).2.2.1, (hfamily k).2.1.trans interior_subset,
      (hfamily k).2.2.2.1, (hfamily k).2.2.2.2.1⟩
  · exact collar_union_trace_eq_radial_bands (isPolyhedron_space R).isClosed.frontier_subset
      hρ.image_eq hzero (inter_comm _ _ ▸ hfirst) haxis₀ hlevel₀
  · exact collar_union_trace_eq_radial_bands (isPolyhedron_space R).isClosed.frontier_subset
      hρ.image_eq hzero (inter_comm _ _ ▸ hsecond) haxis₁ hlevel₁

end DifferentialGeometry.Topology.PiecewiseLinear
