import DifferentialGeometry.Topology.PiecewiseLinear.DiskPseudoIsotopy
import DifferentialGeometry.Topology.PiecewiseLinear.ManifoldSubcomplexBoundary

open Set

namespace DifferentialGeometry.Topology.PiecewiseLinear

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

open Classical in
theorem exists_PL_disk_pseudoisotopy_fixed_side [FiniteDimensional ℝ E]
    (K : Geometry.SimplicialComplex ℝ E) [Finite K.faces] (hK : IsPLBall 2 K.space)
    {u : E → E} (hu : IsPLHomeomorphOn u K.space K.space)
    (hbd : EqOn u id (boundaryComplex 2 K).space) :
    ∃ Φ : E × ℝ → E × ℝ,
      IsPLHomeomorphOn Φ (K.space ×ˢ Icc (0 : ℝ) 1) (K.space ×ˢ Icc (0 : ℝ) 1) ∧
      (∀ x ∈ K.space, Φ (x, 0) = (x, 0)) ∧
      (∀ x ∈ K.space, Φ (x, 1) = (u x, 1)) ∧
      EqOn Φ id ((boundaryComplex 2 K).space ×ˢ Icc (0 : ℝ) 1) := by
  classical
  let _ : Finite (boundaryComplex 2 K).faces := (boundaryComplex_faces_finite 2 K).to_subtype
  have hQ : IsPLBall 3 (K.space ×ˢ Icc (0 : ℝ) 1) :=
    isPLBall_three_prod hK (isPLBall_Icc zero_lt_one)
  obtain ⟨A, hAfin, hAspace⟩ := hQ.isPolyhedron.exists_simplicialComplex
  let _ : Finite A.faces := hAfin.to_subtype
  have hAball : IsPLBall 3 A.space := hAspace ▸ hQ
  have hbdA : (boundaryComplex 3 A).space =
      K.space ×ˢ ({1} : Set ℝ) ∪
        (K.space ×ˢ ({0} : Set ℝ) ∪ (boundaryComplex 2 K).space ×ˢ Icc (0 : ℝ) 1) := by
    rw [boundaryComplex_space_prism K hK zero_lt_one A hAspace]
    ext z
    simp only [mem_union, mem_prod, mem_insert_iff, mem_singleton_iff]
    tauto
  have hW1poly : IsPolyhedron (K.space ×ˢ ({1} : Set ℝ)) :=
    isPolyhedron_prod_singleton hK.isPolyhedron 1
  have hW0poly : IsPolyhedron
      (K.space ×ˢ ({0} : Set ℝ) ∪ (boundaryComplex 2 K).space ×ˢ Icc (0 : ℝ) 1) :=
    (isPolyhedron_prod_singleton hK.isPolyhedron 0).union
      ((isPolyhedron_space (boundaryComplex 2 K)).prod isHPolytope_Icc.isPolyhedron)
  have hsing : IsPolyhedron ({1} : Set ℝ) := by
    rw [← Icc_self (1 : ℝ)]
    exact isHPolytope_Icc.isPolyhedron
  have hθ1 : IsPLHomeomorphOn (fun z : E × ℝ => if z.2 = 1 then (u z.1, z.2) else z)
      (K.space ×ˢ ({1} : Set ℝ)) (K.space ×ˢ ({1} : Set ℝ)) := by
    refine (hu.prodMap hsing.isPLHomeomorphOn_id).congr ?_
    rintro z ⟨-, hz2⟩
    have hz2' : z.2 = 1 := hz2
    simp only [if_pos hz2']
    rfl
  have hθid : EqOn (fun z : E × ℝ => if z.2 = 1 then (u z.1, z.2) else z) id
      (K.space ×ˢ ({0} : Set ℝ) ∪ (boundaryComplex 2 K).space ×ˢ Icc (0 : ℝ) 1) := by
    rintro z hz
    by_cases hz2 : z.2 = 1
    · simp only [if_pos hz2]
      rcases hz with ⟨-, hzbot⟩ | ⟨hzb, -⟩
      · have hzbot' : z.2 = 0 := hzbot
        exact absurd (hz2.symm.trans hzbot') (by norm_num)
      · exact Prod.ext (hbd hzb) rfl
    · simp only [if_neg hz2]
      rfl
  have hθ0 : IsPLHomeomorphOn (fun z : E × ℝ => if z.2 = 1 then (u z.1, z.2) else z)
      (K.space ×ˢ ({0} : Set ℝ) ∪ (boundaryComplex 2 K).space ×ˢ Icc (0 : ℝ) 1)
      (K.space ×ˢ ({0} : Set ℝ) ∪ (boundaryComplex 2 K).space ×ˢ Icc (0 : ℝ) 1) :=
    hW0poly.isPLHomeomorphOn_id.congr hθid
  have hmeet : (fun z : E × ℝ => if z.2 = 1 then (u z.1, z.2) else z) ''
      (K.space ×ˢ ({1} : Set ℝ) ∩
        (K.space ×ˢ ({0} : Set ℝ) ∪ (boundaryComplex 2 K).space ×ˢ Icc (0 : ℝ) 1)) =
      K.space ×ˢ ({1} : Set ℝ) ∩
        (K.space ×ˢ ({0} : Set ℝ) ∪ (boundaryComplex 2 K).space ×ˢ Icc (0 : ℝ) 1) :=
    ((hθid.mono inter_subset_right).image_eq).trans (image_id _)
  have hθ := hθ1.union hθ0 hW1poly hW0poly hmeet
  rw [← hbdA] at hθ
  obtain ⟨Φ, hΦ, hΦbd⟩ :=
    exists_isPLHomeomorphOn_of_boundaryComplex (n := 2) A A hAball hAball hθ
  refine ⟨Φ, hAspace ▸ hΦ, fun x hx => ?_, fun x hx => ?_, ?_⟩
  · have hmem : (x, (0 : ℝ)) ∈ (boundaryComplex 3 A).space := by
      rw [hbdA]
      exact Or.inr (Or.inl ⟨hx, rfl⟩)
    rw [hΦbd hmem]
    exact if_neg (by norm_num)
  · have hmem : (x, (1 : ℝ)) ∈ (boundaryComplex 3 A).space := by
      rw [hbdA]
      exact Or.inl ⟨hx, rfl⟩
    rw [hΦbd hmem]
    exact if_pos rfl
  · intro z hz
    have hmem : z ∈ (boundaryComplex 3 A).space := by
      rw [hbdA]
      exact Or.inr (Or.inr hz)
    exact (hΦbd hmem).trans (hθid (Or.inr hz))

theorem IsCombinatorialManifold.exists_disk_supported_pseudoisotopy
    [FiniteDimensional ℝ E] (K : Geometry.SimplicialComplex ℝ E) [Finite K.faces]
    (hK : IsCombinatorialManifold 2 K) {N : Set E} {n : (Fin 3 → ℝ) → E}
    (hn : IsPLHomeomorphOn n (stdSimplex ℝ (Fin 3)) N) (hNK : N ⊆ K.space)
    {H : E → E} (hH : IsPLHomeomorphOn H K.space K.space)
    (hfix : EqOn H id (closure (K.space \ N))) (hHN : H '' N = N) :
    ∃ Φ : E × ℝ → E × ℝ,
      IsPLHomeomorphOn Φ (K.space ×ˢ Icc (0 : ℝ) 1) (K.space ×ˢ Icc (0 : ℝ) 1) ∧
      (∀ x ∈ K.space, Φ (x, 0) = (x, 0)) ∧
      (∀ x ∈ K.space, Φ (x, 1) = (H x, 1)) ∧
      EqOn Φ id ((closure (K.space \ N)) ×ˢ Icc (0 : ℝ) 1) := by
  classical
  have hN : IsPLBall 2 N := ⟨n, hn⟩
  let C := closure (K.space \ N)
  have hC : IsPolyhedron C := (isPolyhedron_space K).closure_sdiff hN.isPolyhedron
  have hCK : C ⊆ K.space := closure_minimal sdiff_subset (isPolyhedron_space K).isClosed
  have hNC : N ∩ C = n '' stdSimplexBoundary 2 :=
    hK.inter_closure_sdiff_eq_image_stdSimplexBoundary K hn hNK
  have hcover : N ∪ C = K.space := by
    apply Subset.antisymm (union_subset hNK hCK)
    intro x hx
    by_cases hxN : x ∈ N
    · exact Or.inl hxN
    · exact Or.inr (subset_closure ⟨hx, hxN⟩)
  obtain ⟨R, hRfin, hRspace⟩ := hN.isPolyhedron.exists_simplicialComplex
  let _ : Finite R.faces := hRfin.to_subtype
  have hnR : IsPLHomeomorphOn n (stdSimplex ℝ (Fin 3)) R.space := hRspace ▸ hn
  have hbdR : (boundaryComplex 2 R).space = N ∩ C := by
    rw [boundaryComplex_space_of_isPLHomeomorphOn_stdSimplex R hnR,
      simplexBoundary_stdVertices_space, hNC]
  have hHR : IsPLHomeomorphOn H R.space R.space := by
    rw [hRspace]
    simpa only [hHN] using hH.restrict hN.isPolyhedron hNK
  have hfixR : EqOn H id (boundaryComplex 2 R).space := by
    rw [hbdR]
    exact hfix.mono inter_subset_right
  obtain ⟨φ, hφ, hφ₀, hφ₁, hφside⟩ :=
    exists_PL_disk_pseudoisotopy_fixed_side R (hRspace ▸ hN) hHR hfixR
  rw [hRspace] at hφ hφ₀ hφ₁
  rw [hbdR] at hφside
  have hmeet : EqOn φ id ((N ×ˢ Icc (0 : ℝ) 1) ∩ C ×ˢ Icc (0 : ℝ) 1) :=
    fun _ hx => hφside ⟨⟨hx.1.1, hx.2.1⟩, hx.1.2⟩
  obtain ⟨Φ, hΦ, hΦφ, hΦC⟩ := exists_isPLHomeomorphOn_union
    (hN.isPolyhedron.prod isHPolytope_Icc.isPolyhedron)
    (hC.prod isHPolytope_Icc.isPolyhedron) hφ
    (hC.prod isHPolytope_Icc.isPolyhedron).isPLHomeomorphOn_id hmeet
    (fun x hx => ⟨x, hx, hmeet hx⟩)
  rw [← union_prod, hcover] at hΦ
  refine ⟨Φ, hΦ, ?_, ?_, hΦC⟩
  · intro x hx
    rcases hcover.symm.subset hx with hx | hx
    · exact (hΦφ ⟨hx, by simp⟩).trans (hφ₀ x hx)
    · exact hΦC ⟨hx, by simp⟩
  · intro x hx
    rcases hcover.symm.subset hx with hx | hx
    · exact (hΦφ ⟨hx, by simp⟩).trans (hφ₁ x hx)
    · exact (hΦC ⟨hx, by simp⟩).trans (Prod.ext (hfix hx).symm rfl)

end DifferentialGeometry.Topology.PiecewiseLinear
