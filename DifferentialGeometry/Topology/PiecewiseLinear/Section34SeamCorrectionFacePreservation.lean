import DifferentialGeometry.Topology.PiecewiseLinear.Section34SeamVolumeExtension

open Set

namespace DifferentialGeometry.Topology.PiecewiseLinear

theorem image_rectangle_region_of_circle_product_conjugacy
    {E : Type*} {f : (ℝ × ℝ) × ℝ → E} {σ : ((Fin 3 → ℝ) × ℝ) × ℝ → E}
    {H : E → E} {ψ : (Fin 3 → ℝ) × ℝ → (Fin 3 → ℝ) × ℝ}
    (hσf : ∀ u ∈ Icc (0 : ℝ) 1, ∀ v ∈ Icc (0 : ℝ) 1, ∀ t ∈ Icc (0 : ℝ) 1,
      σ ((stdTriangleLoop t, u), v) = f ((u, v), t))
    (hconj : ∀ z ∈ stdSimplexBoundary 2 ×ˢ Icc (0 : ℝ) 1, ∀ v ∈ Icc (0 : ℝ) 1,
      H (σ (z, v)) = σ (ψ z, v))
    {K V : Set ℝ} (hK : K ⊆ Icc (0 : ℝ) 1) (hV : V ⊆ Icc (0 : ℝ) 1)
    (hψK : ψ '' (stdSimplexBoundary 2 ×ˢ K) = stdSimplexBoundary 2 ×ˢ K) :
    H '' (f '' ((K ×ˢ V) ×ˢ Icc (0 : ℝ) 1)) =
      f '' ((K ×ˢ V) ×ˢ Icc (0 : ℝ) 1) := by
  have heq : σ '' ((stdSimplexBoundary 2 ×ˢ K) ×ˢ V) =
      f '' ((K ×ˢ V) ×ˢ Icc (0 : ℝ) 1) := by
    apply Subset.antisymm
    · rintro y ⟨⟨⟨z, u⟩, v⟩, ⟨⟨hz, hu⟩, hv⟩, rfl⟩
      obtain ⟨t, ht, rfl⟩ := stdTriangleLoop_image.symm.subset hz
      exact ⟨((u, v), t), ⟨⟨hu, hv⟩, ht⟩, (hσf u (hK hu) v (hV hv) t ht).symm⟩
    · rintro y ⟨⟨⟨u, v⟩, t⟩, ⟨⟨hu, hv⟩, ht⟩, rfl⟩
      exact ⟨((stdTriangleLoop t, u), v),
        ⟨⟨stdTriangleLoop_image.subset (mem_image_of_mem stdTriangleLoop ht), hu⟩, hv⟩,
        hσf u (hK hu) v (hV hv) t ht⟩
  have hEq : EqOn (H ∘ σ) (σ ∘ Prod.map ψ id)
      ((stdSimplexBoundary 2 ×ˢ K) ×ˢ V) := fun z hz =>
    hconj z.1 ⟨hz.1.1, hK hz.1.2⟩ z.2 (hV hz.2)
  rw [← heq, ← image_comp, hEq.image_eq, image_comp, prodMap_image_prod, hψK, image_id]

theorem image_square_face_eq_of_annulus_product_conjugacy
    {E : Type*} {f : (ℝ × ℝ) × ℝ → E} {σ : ((Fin 3 → ℝ) × ℝ) × ℝ → E}
    {H : E → E} {ψ : (Fin 3 → ℝ) × ℝ → (Fin 3 → ℝ) × ℝ}
    (hσf : ∀ u ∈ Icc (0 : ℝ) 1, ∀ v ∈ Icc (0 : ℝ) 1, ∀ t ∈ Icc (0 : ℝ) 1,
      σ ((stdTriangleLoop t, u), v) = f ((u, v), t))
    (hconj : ∀ z ∈ stdSimplexBoundary 2 ×ˢ Icc (0 : ℝ) 1, ∀ v ∈ Icc (0 : ℝ) 1,
      H (σ (z, v)) = σ (ψ z, v))
    (hψ : ψ '' (stdSimplexBoundary 2 ×ˢ Icc (0 : ℝ) 1) =
      stdSimplexBoundary 2 ×ˢ Icc (0 : ℝ) 1)
    (hψrim : ∀ r ∈ ({0, 1} : Set ℝ),
      ψ '' (stdSimplexBoundary 2 ×ˢ {r}) = stdSimplexBoundary 2 ×ˢ {r})
    {K : Set ℝ} (hK : K ⊆ Icc (0 : ℝ) 1)
    (hψK : ψ '' (stdSimplexBoundary 2 ×ˢ K) = stdSimplexBoundary 2 ×ˢ K)
    {B : Set (ℝ × ℝ)} (hB : B ⊆ frontier (Icc (0 : ℝ) 1 ×ˢ Icc (0 : ℝ) 1))
    (hbottom : B ∩ (Icc (0 : ℝ) 1 ×ˢ {0}) = K ×ˢ {0})
    (htop : Icc (0 : ℝ) 1 ×ˢ {(1 : ℝ)} ⊆ B ∨
      Disjoint B (Icc (0 : ℝ) 1 ×ˢ {(1 : ℝ)})) :
    H '' (f '' (B ×ˢ Icc (0 : ℝ) 1)) = f '' (B ×ˢ Icc (0 : ℝ) 1) := by
  let I := Icc (0 : ℝ) 1
  have hsingle (r : ℝ) (hr : r ∈ ({0, 1} : Set ℝ)) : {r} ⊆ I := by
    apply singleton_subset_iff.mpr
    rcases hr with rfl | rfl <;> norm_num [I]
  have hbottom' : H '' (f '' ((B ∩ (I ×ˢ {0})) ×ˢ I)) =
      f '' ((B ∩ (I ×ˢ {0})) ×ˢ I) := by
    rw [hbottom]
    exact image_rectangle_region_of_circle_product_conjugacy hσf hconj hK
      (hsingle 0 (by simp)) hψK
  have htop' : H '' (f '' ((B ∩ (I ×ˢ {1})) ×ˢ I)) =
      f '' ((B ∩ (I ×ˢ {1})) ×ˢ I) := by
    rcases htop with htop | htop
    · rw [inter_eq_right.mpr htop]
      exact image_rectangle_region_of_circle_product_conjugacy hσf hconj Subset.rfl
        (hsingle 1 (by simp)) hψ
    · rw [disjoint_iff_inter_eq_empty.mp htop, empty_prod, image_empty, image_empty]
  have hvertical (r : ℝ) (hr : r ∈ ({0, 1} : Set ℝ)) :
      H '' (f '' ((B ∩ ({r} ×ˢ I)) ×ˢ I)) = f '' ((B ∩ ({r} ×ˢ I)) ×ˢ I) := by
    let V := {v ∈ I | (r, v) ∈ B}
    have heq : B ∩ ({r} ×ˢ I) = {r} ×ˢ V := by
      ext p
      constructor
      · rintro ⟨hpB, hp⟩
        exact ⟨hp.1, hp.2, (show p.1 = r from hp.1) ▸ hpB⟩
      · rintro ⟨hp, hv, hB⟩
        have heq : (r, p.2) = p := Prod.ext (show r = p.1 from hp.symm) rfl
        exact ⟨heq ▸ hB, hp, hv⟩
    rw [heq]
    exact image_rectangle_region_of_circle_product_conjugacy hσf hconj (hsingle r hr)
      (fun _ hv => hv.1) (hψrim r hr)
  have hcover : B = (B ∩ (I ×ˢ {0})) ∪ (B ∩ (I ×ˢ {1})) ∪
      (B ∩ ({0} ×ˢ I)) ∪ (B ∩ ({1} ×ˢ I)) := by
    apply Subset.antisymm
    · intro p hp
      have hpf := hB hp
      rw [frontier_prod_eq, isClosed_Icc.closure_eq,
        frontier_Icc (zero_le_one' ℝ)] at hpf
      rcases hpf with ⟨ht, hr⟩ | ⟨hr, ht⟩
      · rcases hr with hr | hr
        · exact Or.inl (Or.inl (Or.inl ⟨hp, ht, hr⟩))
        · exact Or.inl (Or.inl (Or.inr ⟨hp, ht, hr⟩))
      · rcases hr with hr | hr
        · exact Or.inl (Or.inr ⟨hp, hr, ht⟩)
        · exact Or.inr ⟨hp, hr, ht⟩
    · exact union_subset (union_subset (union_subset inter_subset_left inter_subset_left)
        inter_subset_left) inter_subset_left
  change H '' (f '' (B ×ˢ I)) = f '' (B ×ˢ I)
  conv_lhs => rw [hcover]
  simp only [union_prod, image_union, hbottom', htop', hvertical 0 (by simp),
    hvertical 1 (by simp)]
  rw [← image_union, ← image_union, ← image_union, ← union_prod, ← union_prod,
    ← union_prod, ← hcover]

end DifferentialGeometry.Topology.PiecewiseLinear
