/-
Copyright (c) 2026 Yuan Liao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuan Liao
-/
import DifferentialGeometry.Topology.PiecewiseLinear.PieceInclusion
import DifferentialGeometry.Topology.PiecewiseLinear.PolyhedralBallTopology
import DifferentialGeometry.Topology.PiecewiseLinear.SurfaceSplitAnnulus

open Set Topology

namespace DifferentialGeometry.Topology.PiecewiseLinear

universe u

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {X : Type u} [TopologicalSpace X] [ChartedSpace (EuclideanSpace ℝ (Fin 3)) X] [T2Space X]

open Classical in
omit [FiniteDimensional ℝ E] in
theorem boundary_prism_sdiff_endpoint_disks
    (K : Geometry.SimplicialComplex ℝ E) {a b : ℝ} (hab : a < b) :
    (K.space ×ˢ {a, b} ∪ (boundaryComplex 2 K).space ×ˢ Icc a b) \
        ((K.space ×ˢ {a}) ∪ (K.space ×ˢ {b})) =
      (boundaryComplex 2 K).space ×ˢ Ioo a b := by
  ext z
  rcases z with ⟨x, t⟩
  constructor
  · rintro ⟨hz, hzend⟩
    rcases hz with ⟨hxK, ht⟩ | ⟨hxJ, ht⟩
    · rcases ht with rfl | rfl
      · exact (hzend (Or.inl ⟨hxK, rfl⟩)).elim
      · exact (hzend (Or.inr ⟨hxK, rfl⟩)).elim
    · have hxK : x ∈ K.space := boundaryComplex_space_subset 2 K hxJ
      have hta : t ≠ a := fun hta => hzend (Or.inl ⟨hxK, hta⟩)
      have htb : t ≠ b := fun htb => hzend (Or.inr ⟨hxK, htb⟩)
      exact ⟨hxJ, lt_of_le_of_ne ht.1 (Ne.symm hta), lt_of_le_of_ne ht.2 htb⟩
  · rintro ⟨hxJ, ht⟩
    have hxK : x ∈ K.space := boundaryComplex_space_subset 2 K hxJ
    refine ⟨Or.inr ⟨hxJ, ht.1.le, ht.2.le⟩, ?_⟩
    rintro (⟨-, hta⟩ | ⟨-, htb⟩)
    · exact ht.1.ne hta.symm
    · exact ht.2.ne htb

open Classical in
theorem PLPieceIn.frontier_image_prism_subinterval
    {N : Set X} (T : PLPieceIn (E × ℝ) 3 X N)
    (K : Geometry.SimplicialComplex ℝ E) [Finite K.faces]
    (hK : IsPLBall 2 K.space) (hdim : Module.finrank ℝ E = 2)
    {a b c : ℝ} (hab : a < b) (hbc : b < c)
    (hTspace : T.complex.space = K.space ×ˢ Icc a c) :
    frontier (T.map '' (K.space ×ˢ Icc a b)) =
      T.map '' (K.space ×ˢ {a, b} ∪ (boundaryComplex 2 K).space ×ˢ Icc a b) := by
  let _ : DecidableEq E := Classical.decEq _
  let _ : DecidableEq (E × ℝ) := Classical.decEq _
  let P := K.space ×ˢ Icc a b
  have hP : IsPLBall 3 P := isPLBall_three_prod hK (isPLBall_Icc hab)
  have hPT : P ⊆ T.complex.space := by
    rw [hTspace]
    exact prod_mono Subset.rfl (Icc_subset_Icc le_rfl hbc.le)
  obtain ⟨S, hSspace, hSmap⟩ := T.exists_restrict_of_isPolyhedron hP.isPolyhedron hPT
  let _ : Finite S.complex.faces := S.finite_faces.to_subtype
  have hS : IsPLBall 3 S.complex.space := hSspace.symm ▸ hP
  have hdimprod : Module.finrank ℝ (E × ℝ) = 3 := by
    simp [Module.finrank_prod, hdim]
  have hfront := S.frontier_eq_image_boundaryComplex hS.isCombinatorialManifoldWithBoundary
  change frontier (T.map '' P) = S.map '' (boundaryComplex 3 S.complex).space at hfront
  have hSfront : frontier S.complex.space = (boundaryComplex 3 S.complex).space :=
    frontier_space_eq_boundaryComplex_space_of_finrank hdimprod S.complex
      hS.isCombinatorialManifoldWithBoundary
  have hKfront : frontier K.space = (boundaryComplex 2 K).space :=
    frontier_space_eq_boundaryComplex_space_of_finrank hdim K
      hK.isCombinatorialManifoldWithBoundary
  have hPfront : frontier P =
      K.space ×ˢ {a, b} ∪ (boundaryComplex 2 K).space ×ˢ Icc a b := by
    rw [show P = K.space ×ˢ Icc a b from rfl, frontier_prod_eq,
      hK.isPolyhedron.isClosed.closure_eq, frontier_Icc hab.le, hKfront,
      isClosed_Icc.closure_eq]
  rw [← hSfront, hSspace, hSmap, hPfront] at hfront
  exact hfront

open Classical in
theorem PLPieceIn.exists_prism_cut_cell_with_boundary_disks
    {N : Set X} (T : PLPieceIn (E × ℝ) 3 X N)
    (K : Geometry.SimplicialComplex ℝ E) [Finite K.faces]
    (hK : IsPLBall 2 K.space) (hdim : Module.finrank ℝ E = 2)
    {a b c : ℝ} (hab : a < b) (hbc : b < c)
    (hTspace : T.complex.space = K.space ×ˢ Icc a c) :
    ∃ C D₀ D₁ : Set X,
      C = T.map '' (K.space ×ˢ Icc a b) ∧
      D₀ = T.map '' (K.space ×ˢ {a}) ∧
      D₁ = T.map '' (K.space ×ˢ {b}) ∧
      IsPolyhedralBall (n := 3) 3 C ∧
      IsPolyhedralBall (n := 3) 2 D₀ ∧
      IsPolyhedralBall (n := 3) 2 D₁ ∧
      C ⊆ N ∧ D₀ ⊆ frontier C ∧ D₁ ⊆ frontier C ∧ Disjoint D₀ D₁ ∧
      frontier C \ (D₀ ∪ D₁) =
        T.map '' ((boundaryComplex 2 K).space ×ˢ Ioo a b) ∧
      IsPathConnected (frontier C \ (D₀ ∪ D₁)) := by
  let _ : DecidableEq E := Classical.decEq _
  let _ : DecidableEq (E × ℝ) := Classical.decEq _
  let P := K.space ×ˢ Icc a b
  let Q₀ := K.space ×ˢ ({a} : Set ℝ)
  let Q₁ := K.space ×ˢ ({b} : Set ℝ)
  let B := K.space ×ˢ {a, b} ∪ (boundaryComplex 2 K).space ×ˢ Icc a b
  let A := (boundaryComplex 2 K).space ×ˢ Ioo a b
  have hP : IsPLBall 3 P := isPLBall_three_prod hK (isPLBall_Icc hab)
  have hQ₀ : IsPLBall 2 Q₀ :=
    hK.of_isPLHomeomorphOn (hK.isPolyhedron.isPLHomeomorphOn_prod_const a)
  have hQ₁ : IsPLBall 2 Q₁ :=
    hK.of_isPLHomeomorphOn (hK.isPolyhedron.isPLHomeomorphOn_prod_const b)
  have hPT : P ⊆ T.complex.space := by
    rw [hTspace]
    exact prod_mono Subset.rfl (Icc_subset_Icc le_rfl hbc.le)
  have hQ₀T : Q₀ ⊆ T.complex.space := by
    rw [hTspace]
    rintro ⟨x, t⟩ ⟨hx, ht⟩
    have ht : t = a := by simpa only [mem_singleton_iff] using ht
    subst t
    exact ⟨hx, le_rfl, (hab.trans hbc).le⟩
  have hQ₁T : Q₁ ⊆ T.complex.space := by
    rw [hTspace]
    rintro ⟨x, t⟩ ⟨hx, ht⟩
    have ht : t = b := by simpa only [mem_singleton_iff] using ht
    subst t
    exact ⟨hx, hab.le, hbc.le⟩
  have hBT : B ⊆ T.complex.space := by
    rw [hTspace]
    rintro ⟨x, t⟩ (⟨hx, ht⟩ | ⟨hx, ht⟩)
    · rcases ht with rfl | rfl
      · exact ⟨hx, le_rfl, (hab.trans hbc).le⟩
      · exact ⟨hx, hab.le, hbc.le⟩
    · exact ⟨boundaryComplex_space_subset 2 K hx, ht.1, ht.2.trans hbc.le⟩
  have hAB : A ⊆ B := by
    rintro ⟨x, t⟩ ⟨hx, ht⟩
    exact Or.inr ⟨hx, ht.1.le, ht.2.le⟩
  have hAT : A ⊆ T.complex.space := hAB.trans hBT
  have hQ₀B : Q₀ ⊆ B := by
    rintro ⟨x, t⟩ ⟨hx, ht⟩
    have ht : t = a := by simpa only [mem_singleton_iff] using ht
    subst t
    exact Or.inl ⟨hx, Or.inl rfl⟩
  have hQ₁B : Q₁ ⊆ B := by
    rintro ⟨x, t⟩ ⟨hx, ht⟩
    have ht : t = b := by simpa only [mem_singleton_iff] using ht
    subst t
    exact Or.inl ⟨hx, Or.inr rfl⟩
  have hfront : frontier (T.map '' P) = T.map '' B := by
    exact T.frontier_image_prism_subinterval K hK hdim hab hbc hTspace
  have hQdis : Disjoint Q₀ Q₁ := by
    rw [disjoint_left]
    rintro z hz₀ hz₁
    have hza : z.2 = a := by simpa only [mem_singleton_iff] using hz₀.2
    have hzb : z.2 = b := by simpa only [mem_singleton_iff] using hz₁.2
    exact hab.ne (hza.symm.trans hzb)
  have hdis : Disjoint (T.map '' Q₀) (T.map '' Q₁) := by
    rw [disjoint_left]
    rintro y ⟨x, hx, rfl⟩ ⟨z, hz, hxz⟩
    have heq : x = z := T.bijOn.injOn (hQ₀T hx) (hQ₁T hz) hxz.symm
    have hxa : x.2 = a := by simpa only [mem_singleton_iff] using hx.2
    have hzb : z.2 = b := by simpa only [mem_singleton_iff] using hz.2
    exact hab.ne (hxa.symm.trans ((congrArg Prod.snd heq).trans hzb))
  have hsafe : frontier (T.map '' P) \ ((T.map '' Q₀) ∪ (T.map '' Q₁)) = T.map '' A := by
    rw [hfront, ← image_union]
    rw [← (T.bijOn.injOn.mono hBT).image_sdiff_subset (union_subset hQ₀B hQ₁B)]
    rw [boundary_prism_sdiff_endpoint_disks K hab]
  have hApath : IsPathConnected A := by
    obtain ⟨R, hRfin, hRspace⟩ := hP.isPolyhedron.exists_simplicialComplex
    let _ : Finite R.faces := hRfin.to_subtype
    have hR : IsPLBall 3 R.space := hRspace.symm ▸ hP
    have hRB : (boundaryComplex 3 R).space = B :=
      boundaryComplex_space_prism K hK hab R hRspace
    have hB : IsPLSphere 2 B :=
      hRB ▸ isPLSphere_boundaryComplex_space_of_isPLBall R hR
    have hBpath := hB.isPathConnected_sdiff_union_of_disjoint_isPLBall_two
      hQ₀ hQ₀B hQ₁ hQ₁B hQdis
    rw [boundary_prism_sdiff_endpoint_disks K hab] at hBpath
    exact hBpath
  have hsafePath : IsPathConnected (frontier (T.map '' P) \
      ((T.map '' Q₀) ∪ (T.map '' Q₁))) := by
    rw [hsafe]
    exact hApath.image' (T.continuousOn.mono hAT)
  refine ⟨T.map '' P, T.map '' Q₀, T.map '' Q₁, rfl, rfl, rfl,
    T.isPolyhedralBall_image hP hPT, T.isPolyhedralBall_image hQ₀ hQ₀T,
    T.isPolyhedralBall_image hQ₁ hQ₁T, ?_, ?_, ?_, hdis, hsafe, hsafePath⟩
  · exact image_subset_iff.mpr (T.bijOn.mapsTo.mono_left hPT)
  · rw [hfront]
    exact image_mono hQ₀B
  · rw [hfront]
    exact image_mono hQ₁B

open Classical in
theorem exists_disjoint_slice_disks_of_centered_prism
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
    {P : Set E} {r : (Fin 3 → ℝ) → E}
    (hr : IsPLHomeomorphOn r (stdSimplex ℝ (Fin 3)) P)
    {N : Set F} {ρ : E × ℝ → F}
    (hρ : IsPLHomeomorphOn ρ (P ×ˢ Icc (-1 : ℝ) 1) N) :
    ∃ (D₀ D₁ A : Set F) (q₀ q₁ : (Fin 3 → ℝ) → F),
      D₀ = ρ '' (P ×ˢ {(-1 / 2 : ℝ)}) ∧
      D₁ = ρ '' (P ×ˢ {(1 / 2 : ℝ)}) ∧
      A = ρ '' ((r '' stdSimplexBoundary 2) ×ˢ Icc (-1 / 2 : ℝ) (1 / 2 : ℝ)) ∧
      IsPLHomeomorphOn q₀ (stdSimplex ℝ (Fin 3)) D₀ ∧
      IsPLHomeomorphOn q₁ (stdSimplex ℝ (Fin 3)) D₁ ∧
      IsPLHomeomorphOn ρ
        ((r '' stdSimplexBoundary 2) ×ˢ Icc (-1 / 2 : ℝ) (1 / 2 : ℝ)) A ∧
      D₀ ⊆ N ∧ D₁ ⊆ N ∧ A ⊆ N ∧ Disjoint D₀ D₁ ∧
      A ∩ D₀ = q₀ '' stdSimplexBoundary 2 ∧
      A ∩ D₁ = q₁ '' stdSimplexBoundary 2 := by
  let J := r '' stdSimplexBoundary 2
  let Q₀ := P ×ˢ {(-1 / 2 : ℝ)}
  let Q₁ := P ×ˢ {(1 / 2 : ℝ)}
  let S := J ×ˢ Icc (-1 / 2 : ℝ) (1 / 2 : ℝ)
  let q₀ := (ρ ∘ fun x : E => (x, (-1 / 2 : ℝ))) ∘ r
  let q₁ := (ρ ∘ fun x : E => (x, (1 / 2 : ℝ))) ∘ r
  have hP : IsPLBall 2 P := ⟨r, hr⟩
  have hJ : IsPLSphere 1 J := by
    let B := simplexBoundary (stdVertices 1) (stdVertices_affineIndependent 1)
    let _ : Finite B.faces := (simplexBoundary_faces_finite _ _).to_subtype
    have h := (isPLSphere_simplexBoundary_std 1).of_isPLHomeomorphOn
      (hr.restrict (isPolyhedron_space B) (simplexBoundary_stdVertices_space_subset 1))
    rwa [simplexBoundary_stdVertices_space] at h
  have hJP : J ⊆ P := by
    rintro x ⟨y, hy, rfl⟩
    have hy' : y ∈
        (simplexBoundary (stdVertices 1) (stdVertices_affineIndependent 1)).space := by
      rwa [simplexBoundary_stdVertices_space]
    exact hr.bijOn.mapsTo (simplexBoundary_stdVertices_space_subset 1 hy')
  have hQ₀P : Q₀ ⊆ P ×ˢ Icc (-1 : ℝ) 1 := by
    rintro ⟨x, t⟩ ⟨hx, ht⟩
    have ht : t = -1 / 2 := by simpa only [mem_singleton_iff] using ht
    subst t
    exact ⟨hx, by norm_num⟩
  have hQ₁P : Q₁ ⊆ P ×ˢ Icc (-1 : ℝ) 1 := by
    rintro ⟨x, t⟩ ⟨hx, ht⟩
    have ht : t = 1 / 2 := by simpa only [mem_singleton_iff] using ht
    subst t
    exact ⟨hx, by norm_num⟩
  have hSP : S ⊆ P ×ˢ Icc (-1 : ℝ) 1 := by
    rintro ⟨x, t⟩ ⟨hx, ht⟩
    exact ⟨hJP hx, ht.1.trans' (by norm_num), ht.2.trans (by norm_num)⟩
  have hq₀ : IsPLHomeomorphOn q₀ (stdSimplex ℝ (Fin 3)) (ρ '' Q₀) :=
    hr.trans ((hP.isPolyhedron.isPLHomeomorphOn_prod_const (-1 / 2 : ℝ)).trans
      (hρ.restrict
        (hP.isPolyhedron.prod (isHPolytope_singleton (-1 / 2 : ℝ)).isPolyhedron) hQ₀P))
  have hq₁ : IsPLHomeomorphOn q₁ (stdSimplex ℝ (Fin 3)) (ρ '' Q₁) :=
    hr.trans ((hP.isPolyhedron.isPLHomeomorphOn_prod_const (1 / 2 : ℝ)).trans
      (hρ.restrict
        (hP.isPolyhedron.prod (isHPolytope_singleton (1 / 2 : ℝ)).isPolyhedron) hQ₁P))
  have hρS : IsPLHomeomorphOn ρ S (ρ '' S) :=
    hρ.restrict (hJ.isPolyhedron.prod isHPolytope_Icc.isPolyhedron) hSP
  have hQdis : Disjoint (ρ '' Q₀) (ρ '' Q₁) := by
    apply disjoint_left.mpr
    rintro y ⟨u, hu, huy⟩ ⟨v, hv, hvy⟩
    have huv := hρ.bijOn.injOn (hQ₀P hu) (hQ₁P hv) (huy.trans hvy.symm)
    have ht := hu.2.symm.trans ((congrArg Prod.snd huv).trans hv.2)
    norm_num at ht
  have hS₀ : S ∩ Q₀ = J ×ˢ {(-1 / 2 : ℝ)} := by
    ext z
    rcases z with ⟨x, t⟩
    constructor
    · rintro ⟨⟨hx, -, -⟩, ⟨-, ht⟩⟩
      exact ⟨hx, ht⟩
    · rintro ⟨hx, ht⟩
      have ht : t = -1 / 2 := by simpa only [mem_singleton_iff] using ht
      subst t
      exact ⟨⟨hx, by norm_num⟩, ⟨hJP hx, rfl⟩⟩
  have hS₁ : S ∩ Q₁ = J ×ˢ {(1 / 2 : ℝ)} := by
    ext z
    rcases z with ⟨x, t⟩
    constructor
    · rintro ⟨⟨hx, -, -⟩, ⟨-, ht⟩⟩
      exact ⟨hx, ht⟩
    · rintro ⟨hx, ht⟩
      have ht : t = 1 / 2 := by simpa only [mem_singleton_iff] using ht
      subst t
      exact ⟨⟨hx, by norm_num⟩, ⟨hJP hx, rfl⟩⟩
  have hq₀boundary : q₀ '' stdSimplexBoundary 2 = ρ '' (J ×ˢ {(-1 / 2 : ℝ)}) := by
    ext y
    constructor
    · rintro ⟨x, hx, rfl⟩
      exact ⟨(r x, -1 / 2), ⟨⟨x, hx, rfl⟩, rfl⟩, rfl⟩
    · rintro ⟨⟨z, t⟩, ⟨⟨x, hx, hxz⟩, ht⟩, rfl⟩
      have ht : t = -1 / 2 := by simpa only [mem_singleton_iff] using ht
      subst t
      exact ⟨x, hx, by simp only [q₀, Function.comp_apply, hxz]⟩
  have hq₁boundary : q₁ '' stdSimplexBoundary 2 = ρ '' (J ×ˢ {(1 / 2 : ℝ)}) := by
    ext y
    constructor
    · rintro ⟨x, hx, rfl⟩
      exact ⟨(r x, 1 / 2), ⟨⟨x, hx, rfl⟩, rfl⟩, rfl⟩
    · rintro ⟨⟨z, t⟩, ⟨⟨x, hx, hxz⟩, ht⟩, rfl⟩
      have ht : t = 1 / 2 := by simpa only [mem_singleton_iff] using ht
      subst t
      exact ⟨x, hx, by simp only [q₁, Function.comp_apply, hxz]⟩
  refine ⟨ρ '' Q₀, ρ '' Q₁, ρ '' S, q₀, q₁, rfl, rfl, rfl,
    hq₀, hq₁, hρS, ?_, ?_, ?_, hQdis, ?_, ?_⟩
  · exact (image_mono hQ₀P).trans hρ.image_eq.subset
  · exact (image_mono hQ₁P).trans hρ.image_eq.subset
  · exact (image_mono hSP).trans hρ.image_eq.subset
  · rw [← hρ.bijOn.injOn.image_inter hSP hQ₀P, hS₀, ← hq₀boundary]
  · rw [← hρ.bijOn.injOn.image_inter hSP hQ₁P, hS₁, ← hq₁boundary]

end DifferentialGeometry.Topology.PiecewiseLinear
