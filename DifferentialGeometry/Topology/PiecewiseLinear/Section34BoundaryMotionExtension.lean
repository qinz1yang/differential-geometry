import DifferentialGeometry.Topology.PiecewiseLinear.Section34DiskRelativePseudoIsotopy
import DifferentialGeometry.Topology.PiecewiseLinear.CollarNeighborhood
import DifferentialGeometry.Topology.PiecewiseLinear.BicollarBands
import DifferentialGeometry.Topology.PiecewiseLinear.CircleFourPoints

open Set Topology

namespace DifferentialGeometry.Topology.PiecewiseLinear

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

open Classical in
theorem IsCombinatorialManifoldWithBoundary.exists_boundary_extension_of_pseudoisotopy
    (K : Geometry.SimplicialComplex ℝ E) [Finite K.faces]
    (hK : IsCombinatorialManifoldWithBoundary 3 K) {u : E → E}
    (hu : IsPLPseudoIsotopicToId u (boundaryComplex 3 K).space) :
    ∃ F : E → E, IsPLHomeomorphOn F K.space K.space ∧
      EqOn F u (boundaryComplex 3 K).space := by
  let B := boundaryComplex 3 K
  let _ : Finite B.faces := (boundaryComplex_faces_finite 3 K).to_subtype
  have hB : IsCombinatorialManifold 2 B := isCombinatorialManifold_boundaryComplex K hK
  obtain ⟨Φ, hΦ, hΦ₀, hΦ₁⟩ := hu
  obtain ⟨W, ρ, hW, hWK, hWnhds, hρ, hzero, -, -⟩ := hK.exists_collar K
  let r : E × ℝ → E × ℝ := fun z => (z.1, 1 - z.2)
  have hr : IsPLHomeomorphOn r (B.space ×ˢ Icc (0 : ℝ) 1)
      (B.space ×ˢ Icc (0 : ℝ) 1) :=
    ((isPolyhedron_space B).isPLHomeomorphOn_id.prodMap
      isPLHomeomorphOn_one_sub_Icc).congr (fun _ _ => rfl)
  let Ψ := r ∘ Φ ∘ r
  have hΨ : IsPLHomeomorphOn Ψ (B.space ×ˢ Icc (0 : ℝ) 1)
      (B.space ×ˢ Icc (0 : ℝ) 1) := (hr.trans hΦ).trans hr
  have hΨ₀ (x : E) (hx : x ∈ B.space) : Ψ (x, 0) = (u x, 0) := by
    simp only [Ψ, r, Function.comp_apply, sub_zero, hΦ₁ x hx, sub_self]
  have hΨ₁ (x : E) (hx : x ∈ B.space) : Ψ (x, 1) = (x, 1) := by
    simp only [Ψ, r, Function.comp_apply, sub_self, hΦ₀ x hx, sub_zero]
  let f := ρ ∘ Ψ ∘ Function.invFunOn ρ (B.space ×ˢ Icc (0 : ℝ) 1)
  have hf : IsPLHomeomorphOn f W W := (hρ.symm.trans hΨ).trans hρ
  have hfρ (z : E × ℝ) (hz : z ∈ B.space ×ˢ Icc (0 : ℝ) 1) : f (ρ z) = ρ (Ψ z) := by
    change ρ (Ψ (Function.invFunOn ρ (B.space ×ˢ Icc (0 : ℝ) 1) (ρ z))) = ρ (Ψ z)
    rw [hρ.bijOn.invOn_invFunOn.1 hz]
  let R := closure (K.space \ W)
  have hR : IsPolyhedron R := (isPolyhedron_space K).closure_sdiff hW
  have hRK : R ⊆ K.space := closure_minimal sdiff_subset (isPolyhedron_space K).isClosed
  have havoid {x : E} (hx : x ∈ R) (hn : W ∈ 𝓝[K.space] x) : False := by
    obtain ⟨V, hV, hVW⟩ := mem_nhdsWithin_iff_exists_mem_nhds_inter.mp hn
    obtain ⟨y, hyV, hyK, hyW⟩ := mem_closure_iff_nhds.mp hx V hV
    exact hyW (hVW ⟨hyV, hyK⟩)
  have hmeet : W ∩ R ⊆ ρ '' (B.space ×ˢ ({1} : Set ℝ)) := by
    intro x hx
    obtain ⟨⟨y, t⟩, ⟨hy, ht₀, ht₁⟩, rfl⟩ := hρ.bijOn.surjOn hx.1
    have ht : t = 1 := by
      by_contra ht
      have htlt : t < 1 := lt_of_le_of_ne ht₁ ht
      rcases eq_or_lt_of_le ht₀ with htzero | htpos
      · have ht' : t = 0 := htzero.symm
        subst t
        have hxR : y ∈ R := hzero y hy ▸ hx.2
        obtain ⟨O, hO, hBO, hOW⟩ := mem_nhdsSetWithin.mp hWnhds
        exact havoid hxR (mem_nhdsWithin.mpr ⟨O, hO, hBO hy, hOW⟩)
      · exact havoid hx.2
          (hρ.mem_nhdsWithin_of_mem_prod_Ioo hK hB zero_lt_one hWK ⟨hy, htpos, htlt⟩)
    exact ⟨(y, t), ⟨hy, ht⟩, rfl⟩
  have hfix : EqOn f id (W ∩ R) := by
    intro x hx
    obtain ⟨⟨y, t⟩, ⟨hy, ht⟩, rfl⟩ := hmeet hx
    have ht' : t = 1 := ht
    subst t
    rw [hfρ (y, 1) ⟨hy, by norm_num⟩, hΨ₁ y hy]
    rfl
  obtain ⟨F, hF, hFf, -⟩ := exists_isPLHomeomorphOn_union hW hR hf
    hR.isPLHomeomorphOn_id hfix (fun x hx => ⟨x, hx, hfix hx⟩)
  have hcover : W ∪ R = K.space := by
    apply Subset.antisymm (union_subset hWK hRK)
    intro x hx
    by_cases hxW : x ∈ W
    · exact Or.inl hxW
    · exact Or.inr (subset_closure ⟨hx, hxW⟩)
  rw [hcover] at hF
  refine ⟨F, hF, fun x hx => ?_⟩
  have hxW : x ∈ W := hzero x hx ▸ hρ.bijOn.mapsTo ⟨hx, by norm_num⟩
  have hux : u x ∈ B.space := by
    have hh := (hΦ.bijOn.mapsTo (show (x, 1) ∈ B.space ×ˢ Icc (0 : ℝ) 1 from
      ⟨hx, by norm_num⟩)).1
    rwa [hΦ₁ x hx] at hh
  rw [hFf hxW, ← hzero x hx, hfρ (x, 0) ⟨hx, by norm_num⟩, hΨ₀ x hx]
  rw [hzero x hx]
  exact hzero (u x) hux

open Classical in
theorem IsCombinatorialManifoldWithBoundary.exists_boundary_extension_of_disk_support
    (K : Geometry.SimplicialComplex ℝ E) [Finite K.faces]
    (hK : IsCombinatorialManifoldWithBoundary 3 K) {N : Set E} {n : (Fin 3 → ℝ) → E}
    (hn : IsPLHomeomorphOn n (Convexity.StdSimplex.coordinateSet ℝ (Fin 3)) N)
    (hNB : N ⊆ (boundaryComplex 3 K).space) {u : E → E}
    (hu : IsPLHomeomorphOn u (boundaryComplex 3 K).space (boundaryComplex 3 K).space)
    (hfix : EqOn u id (closure ((boundaryComplex 3 K).space \ N))) (huN : u '' N = N) :
    ∃ F : E → E, IsPLHomeomorphOn F K.space K.space ∧
      EqOn F u (boundaryComplex 3 K).space := by
  let _ : Finite (boundaryComplex 3 K).faces := (boundaryComplex_faces_finite 3 K).to_subtype
  obtain ⟨Φ, hΦ, hΦ₀, hΦ₁, -⟩ :=
    (isCombinatorialManifold_boundaryComplex K hK).exists_disk_supported_pseudoisotopy
      (boundaryComplex 3 K) hn hNB hu hfix huN
  exact hK.exists_boundary_extension_of_pseudoisotopy K ⟨Φ, hΦ, hΦ₀, hΦ₁⟩

end DifferentialGeometry.Topology.PiecewiseLinear
