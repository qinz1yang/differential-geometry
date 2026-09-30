import DifferentialGeometry.Topology.PiecewiseLinear.SurfaceCircleBicollar
import DifferentialGeometry.Topology.PiecewiseLinear.PLHomeomorphGluing

open Set Topology

namespace DifferentialGeometry.Topology.PiecewiseLinear

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

private theorem snd_const_prod_pl :
    IsPLHomeomorphOn (Prod.snd : ℝ × ℝ → ℝ) ({0} ×ˢ Icc (-1 : ℝ) 1) (Icc (-1) 1) := by
  apply isPLHomeomorphOn_of_isPiecewiseAffineOn_of_bijOn
    ((isHPolytope_singleton (0 : ℝ)).isPolyhedron.prod isHPolytope_Icc.isPolyhedron)
    (isPiecewiseAffineOn_of_affine_of_isHPolytope (LinearMap.snd ℝ ℝ ℝ).toAffineMap
      ((isHPolytope_singleton (0 : ℝ)).prod isHPolytope_Icc))
  refine ⟨fun _ hx => hx.2, ?_, fun t ht => ⟨(0, t), ⟨rfl, ht⟩, rfl⟩⟩
  intro x hx y hy hxy
  exact Prod.ext (hx.1.trans hy.1.symm) hxy

theorem exists_isPLHomeomorphOn_crossed_bicollars
    {J W₀ W₁ : Set E} {ρ σ : E × ℝ → E} (hJ : IsPolyhedron J)
    (hρ : IsPLHomeomorphOn ρ (J ×ˢ Icc (-1 : ℝ) 1) W₀)
    (hσ : IsPLHomeomorphOn σ (J ×ˢ Icc (-1 : ℝ) 1) W₁)
    (hρ₀ : ∀ x ∈ J, ρ (x, 0) = x) (hσ₀ : ∀ x ∈ J, σ (x, 0) = x)
    (hinter : W₀ ∩ W₁ = J) :
    ∃ H : E × (ℝ × ℝ) → E,
      IsPLHomeomorphOn H
        (J ×ˢ ((Icc (-1 : ℝ) 1 ×ˢ {0}) ∪ ({0} ×ˢ Icc (-1 : ℝ) 1))) (W₀ ∪ W₁) ∧
      (∀ x ∈ J, H (x, 0, 0) = x) ∧
      H '' (J ×ˢ (Icc (-1 : ℝ) 1 ×ˢ {0})) = W₀ ∧
      H '' (J ×ˢ ({0} ×ˢ Icc (-1 : ℝ) 1)) = W₁ := by
  let P₀ := J ×ˢ (Icc (-1 : ℝ) 1 ×ˢ ({0} : Set ℝ))
  let P₁ := J ×ˢ (({0} : Set ℝ) ×ˢ Icc (-1 : ℝ) 1)
  have hP₀ : IsPolyhedron P₀ := hJ.prod
    (isHPolytope_Icc.isPolyhedron.prod (isHPolytope_singleton (0 : ℝ)).isPolyhedron)
  have hP₁ : IsPolyhedron P₁ := hJ.prod
    ((isHPolytope_singleton (0 : ℝ)).isPolyhedron.prod isHPolytope_Icc.isPolyhedron)
  have hp₀ : IsPLHomeomorphOn (Prod.map id Prod.fst) P₀ (J ×ˢ Icc (-1 : ℝ) 1) :=
    hJ.isPLHomeomorphOn_id.prodMap
    (isHPolytope_Icc.isPolyhedron.isPLHomeomorphOn_fst_prod_const (0 : ℝ))
  have hp₁ := hJ.isPLHomeomorphOn_id.prodMap snd_const_prod_pl
  have hf := hp₀.trans hρ
  have hg := hp₁.trans hσ
  have hfg : EqOn (ρ ∘ Prod.map id Prod.fst) (σ ∘ Prod.map id Prod.snd) (P₀ ∩ P₁) := by
    intro z hz
    have hs : z.2.1 = 0 := hz.2.2.1
    have ht : z.2.2 = 0 := hz.1.2.2
    change ρ (z.1, z.2.1) = σ (z.1, z.2.2)
    rw [hs, ht, hρ₀ z.1 hz.1.1, hσ₀ z.1 hz.1.1]
  have hsurj : SurjOn (ρ ∘ Prod.map id Prod.fst) (P₀ ∩ P₁) (W₀ ∩ W₁) := by
    intro x hx
    have hxJ := hinter.subset hx
    refine ⟨(x, 0, 0), ⟨⟨hxJ, ?_, rfl⟩, ⟨hxJ, rfl, ?_⟩⟩, hρ₀ x hxJ⟩ <;>
      norm_num
  obtain ⟨H, hH, hH₀, hH₁⟩ :=
    exists_isPLHomeomorphOn_union hP₀ hP₁ hf hg hfg hsurj
  refine ⟨H, ?_, ?_, hH₀.image_eq.trans hf.image_eq, hH₁.image_eq.trans hg.image_eq⟩
  · simpa only [prod_union] using hH
  · intro x hx
    exact (hH₀ (show (x, 0, 0) ∈ P₀ from ⟨hx, by norm_num, rfl⟩)).trans (hρ₀ x hx)

open Classical in
theorem exists_crossing_circle_core
    (K₀ K₁ : Geometry.SimplicialComplex ℝ E) [Finite K₀.faces] [Finite K₁.faces]
    (hK₀ : IsCombinatorialManifold 2 K₀) (hK₁ : IsCombinatorialManifold 2 K₁)
    (hor₀ : IsOrientable 2 K₀) (hor₁ : IsOrientable 2 K₁)
    {J U : Set E} (hJ : IsPLSphere 1 J) (hJ₀ : J ⊆ K₀.space) (hJ₁ : J ⊆ K₁.space)
    (hU : IsOpen U) (hJU : J ⊆ U) (htrace : (K₀.space ∩ K₁.space) ∩ U ⊆ J) :
    ∃ (W₀ W₁ : Set E) (H : E × (ℝ × ℝ) → E),
      IsPolyhedron W₀ ∧ IsPolyhedron W₁ ∧ W₀ ∪ W₁ ⊆ U ∧
      W₀ ∈ 𝓝ˢ[K₀.space] J ∧ W₁ ∈ 𝓝ˢ[K₁.space] J ∧ W₀ ∩ W₁ = J ∧
      (W₀ ∪ W₁) ∩ K₀.space = W₀ ∧ (W₀ ∪ W₁) ∩ K₁.space = W₁ ∧
      IsPLHomeomorphOn H
        (J ×ˢ ((Icc (-1 : ℝ) 1 ×ˢ {0}) ∪ ({0} ×ˢ Icc (-1 : ℝ) 1))) (W₀ ∪ W₁) ∧
      (∀ x ∈ J, H (x, 0, 0) = x) ∧
      H '' (J ×ˢ (Icc (-1 : ℝ) 1 ×ˢ {0})) = W₀ ∧
      H '' (J ×ˢ ({0} ×ˢ Icc (-1 : ℝ) 1)) = W₁ := by
  have hUneigh : U ∈ 𝓝ˢ J := mem_nhdsSet_iff_forall.mpr fun x hx => hU.mem_nhds (hJU hx)
  obtain ⟨W₀, ρ, hW₀, hW₀K, hW₀U, hN₀, hρ, hρ₀⟩ :=
    hK₀.exists_bicollar_of_isPLSphere_one K₀ hor₀ hJ hJ₀ (Filter.mem_inf_of_left hUneigh)
  obtain ⟨W₁, σ, hW₁, hW₁K, hW₁U, hN₁, hσ, hσ₀⟩ :=
    hK₁.exists_bicollar_of_isPLSphere_one K₁ hor₁ hJ hJ₁ (Filter.mem_inf_of_left hUneigh)
  have hJW₀ : J ⊆ W₀ := fun x hx => hρ₀ x hx ▸ hρ.bijOn.mapsTo ⟨hx, by norm_num⟩
  have hJW₁ : J ⊆ W₁ := fun x hx => hσ₀ x hx ▸ hσ.bijOn.mapsTo ⟨hx, by norm_num⟩
  have hinter : W₀ ∩ W₁ = J := Subset.antisymm
    (fun _ hx => htrace ⟨⟨hW₀K hx.1, hW₁K hx.2⟩, hW₀U hx.1⟩)
    (fun _ hx => ⟨hJW₀ hx, hJW₁ hx⟩)
  obtain ⟨H, hH, hHcore, hH₀, hH₁⟩ :=
    exists_isPLHomeomorphOn_crossed_bicollars hJ.isPolyhedron hρ hσ hρ₀ hσ₀ hinter
  refine ⟨W₀, W₁, H, hW₀, hW₁, union_subset hW₀U hW₁U, hN₀, hN₁,
    hinter, ?_, ?_, hH, hHcore, hH₀, hH₁⟩
  · apply Subset.antisymm
    · rintro x ⟨hx | hx, hxK⟩
      · exact hx
      · exact hJW₀ (htrace ⟨⟨hxK, hW₁K hx⟩, hW₁U hx⟩)
    · exact fun _ hx => ⟨Or.inl hx, hW₀K hx⟩
  · apply Subset.antisymm
    · rintro x ⟨hx | hx, hxK⟩
      · exact hJW₁ (htrace ⟨⟨hW₀K hx, hxK⟩, hW₀U hx⟩)
      · exact hx
    · exact fun _ hx => ⟨Or.inr hx, hW₁K hx⟩

end DifferentialGeometry.Topology.PiecewiseLinear
