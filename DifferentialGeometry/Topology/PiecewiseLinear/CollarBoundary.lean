import DifferentialGeometry.Topology.PiecewiseLinear.BoundaryDiskPersistence
import DifferentialGeometry.Topology.PiecewiseLinear.PrismBoundary

open Set

namespace DifferentialGeometry.Topology.PiecewiseLinear

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

open Classical in
theorem image_prism_side_subset_boundaryComplex
    (K L : Geometry.SimplicialComplex ℝ E) [Finite K.faces] [Finite L.faces]
    (hK : IsPLBall 2 K.space) {a b : ℝ} (hab : a < b) {g : E × ℝ → E}
    (hg : IsPLHomeomorphOn g (K.space ×ˢ Icc a b) L.space)
    {A : Set E} (hAK : A ⊆ (boundaryComplex 2 K).space) :
    g '' (A ×ˢ Icc a b) ⊆ (boundaryComplex 3 L).space := by
  let _ : DecidableEq (E × ℝ) := Classical.decEq _
  have hprod := isPLBall_three_prod hK (isPLBall_Icc hab)
  obtain ⟨T, hTfin, hTspace⟩ := hprod.isPolyhedron.exists_simplicialComplex
  let _ : Finite T.faces := hTfin.to_subtype
  have hT : IsPLBall 3 T.space := hTspace.symm ▸ hprod
  have hmap : IsPLHomeomorphOn g T.space L.space := hTspace.symm ▸ hg
  rw [boundaryComplex_space_of_isPLHomeomorphOn T L hT.isCombinatorialManifoldWithBoundary hmap,
    boundaryComplex_space_prism K hK hab T hTspace]
  exact image_mono ((prod_mono hAK Subset.rfl).trans subset_union_right)

open Classical in
theorem image_strip_subset_boundaryComplex_complement
    (K C R : Geometry.SimplicialComplex ℝ E) [Finite K.faces] [Finite C.faces] [Finite R.faces]
    (hK : IsCombinatorialManifoldWithBoundary 3 K)
    (hC : IsCombinatorialManifoldWithBoundary 3 C) (hCK : C.space ⊆ K.space)
    (hR : IsCombinatorialManifoldWithBoundary 3 R)
    (hRspace : R.space = closure (K.space \ C.space))
    {P Q A W : Set E} (hP : IsPolyhedron P) (hA : IsPLBall 1 A)
    (hAP : A ⊆ P) (hQP : Q ⊆ P) (hfinite : (A ∩ Q).Finite)
    {a b : ℝ} (hab : a < b) {f : E × ℝ → E}
    (hf : IsPLHomeomorphOn f (P ×ˢ Icc a b) W)
    (hside : f '' (A ×ˢ Icc a b) ⊆ (boundaryComplex 3 K).space)
    (hCW : C.space ∩ W ⊆ f '' (Q ×ˢ Icc a b)) :
    f '' (A ×ˢ Icc a b) ⊆ (boundaryComplex 3 R).space := by
  have hcl := hf.closure_image_prod_Ioc_sdiff hab hP hA hAP hfinite
  have hsub : f '' ((A \ Q) ×ˢ Ioc a b) ⊆ (boundaryComplex 3 K).space \ C.space := by
    rintro x ⟨z, ⟨⟨hzA, hzQ⟩, hzI⟩, rfl⟩
    have hzP : z ∈ P ×ˢ Icc a b := ⟨hAP hzA, Ioc_subset_Icc_self hzI⟩
    refine ⟨hside ⟨z, ⟨hzA, Ioc_subset_Icc_self hzI⟩, rfl⟩, ?_⟩
    intro hxC
    obtain ⟨y, hy, hyz⟩ := hCW ⟨hxC, hf.bijOn.mapsTo hzP⟩
    have heq : y = z := hf.bijOn.injOn ⟨hQP hy.1, hy.2⟩ hzP hyz
    exact hzQ (by simpa only [heq] using hy.1)
  have h := closure_mono hsub
  rw [hcl] at h
  rw [boundaryComplex_space_of_closure_sdiff K C R hK hC hCK hR hRspace]
  exact h.trans subset_union_left

open Classical in
theorem image_prism_side_subset_boundaryComplex_complement
    (D K C R : Geometry.SimplicialComplex ℝ E)
    [Finite D.faces] [Finite K.faces] [Finite C.faces] [Finite R.faces]
    (hD : IsPLBall 2 D.space) (hK : IsCombinatorialManifoldWithBoundary 3 K)
    (hCK : C.space ⊆ K.space) (hR : IsCombinatorialManifoldWithBoundary 3 R)
    (hRspace : R.space = closure (K.space \ C.space))
    {A Q : Set E} (hA : IsPLBall 1 A) (hAD : A ⊆ (boundaryComplex 2 D).space)
    (hQD : Q ⊆ D.space) (hfinite : (A ∩ Q).Finite)
    {a b : ℝ} (hab : a < b) {g : E × ℝ → E}
    (hg : IsPLHomeomorphOn g (D.space ×ˢ Icc a b) C.space)
    (htrace : C.space ∩ (boundaryComplex 3 K).space ⊆
      g '' (D.space ×ˢ {a} ∪ Q ×ˢ Icc a b)) :
    g '' (A ×ˢ Icc a b) ⊆ (boundaryComplex 3 R).space := by
  have hC := (isPLBall_three_prod hD (isPLBall_Icc hab)).of_isPLHomeomorphOn hg
  have hAD' := hAD.trans (boundaryComplex_space_subset 2 D)
  have hside := image_prism_side_subset_boundaryComplex D C hD hab hg hAD
  have hcl := hg.closure_image_prod_Ioc_sdiff hab (isPolyhedron_space D) hA hAD' hfinite
  have hsub : g '' ((A \ Q) ×ˢ Ioc a b) ⊆
      (boundaryComplex 3 C).space \ (boundaryComplex 3 K).space := by
    rintro x ⟨z, ⟨⟨hzA, hzQ⟩, hzI⟩, rfl⟩
    have hzD : z ∈ D.space ×ˢ Icc a b := ⟨hAD' hzA, Ioc_subset_Icc_self hzI⟩
    refine ⟨hside ⟨z, ⟨hzA, Ioc_subset_Icc_self hzI⟩, rfl⟩, ?_⟩
    intro hxK
    obtain ⟨y, hy, hyz⟩ := htrace ⟨hg.bijOn.mapsTo hzD, hxK⟩
    rcases hy with hy | hy
    · have hyD : y ∈ D.space ×ˢ Icc a b :=
        ⟨hy.1, hy.2.symm ▸ ⟨le_rfl, hab.le⟩⟩
      have heq : y = z := hg.bijOn.injOn hyD hzD hyz
      exact hzI.1.ne' ((congrArg Prod.snd heq).symm.trans hy.2)
    · have heq : y = z := hg.bijOn.injOn ⟨hQD hy.1, hy.2⟩ hzD hyz
      exact hzQ (by simpa only [heq] using hy.1)
  have h := closure_mono hsub
  rw [hcl] at h
  rw [boundaryComplex_space_of_closure_sdiff K C R hK hC.isCombinatorialManifoldWithBoundary
    hCK hR hRspace]
  exact h.trans subset_union_right

open Classical in
theorem collar_disk_subset_boundaryComplex_complement {ι : Type*}
    (D K C R : Geometry.SimplicialComplex ℝ E)
    [Finite D.faces] [Finite K.faces] [Finite C.faces] [Finite R.faces]
    (hD : IsPLBall 2 D.space) (hK : IsCombinatorialManifoldWithBoundary 3 K)
    (hCK : C.space ⊆ K.space) (hR : IsCombinatorialManifoldWithBoundary 3 R)
    (hRspace : R.space = closure (K.space \ C.space))
    {B P J W : Set E} (hP : IsPolyhedron P) (hJ : IsPLBall 2 J) (hJB : J ⊆ B)
    (hJD : IsPLBall 1 (J ∩ D.space) ∨ Disjoint J D.space)
    (hJDb : J ∩ D.space ⊆ (boundaryComplex 2 D).space)
    (hfinite : (J ∩ D.space ∩ P).Finite)
    (d : Finset ι) (A : ι → Set E) (hA : ∀ i ∈ d, IsPLBall 1 (A i))
    (hcover : (⋃ i ∈ d, A i) = J ∩ P)
    {a b : ℝ} (hab : a < b) {ρ σ : E × ℝ → E}
    (hρ : IsPLHomeomorphOn ρ (P ×ˢ Icc a b) W)
    (hσ : IsPLHomeomorphOn σ (D.space ×ˢ Icc a b) C.space)
    (hσρ : EqOn σ ρ (P ×ˢ Icc a b))
    (hattach : J ∪ ρ '' ((J ∩ P) ×ˢ Icc a b) ⊆ (boundaryComplex 3 K).space)
    (htrace : C.space ∩ (boundaryComplex 3 K).space =
      σ '' (D.space ×ˢ {a} ∪ (D.space ∩ P) ×ˢ Icc a b))
    (hCB : C.space ∩ B = D.space)
    (hWC : W ∩ C.space = ρ '' ((D.space ∩ P) ×ˢ Icc a b)) :
    J ∪ σ '' ((J ∩ (P ∪ D.space)) ×ˢ Icc a b) ⊆ (boundaryComplex 3 R).space := by
  have hC := (isPLBall_three_prod hD (isPLBall_Icc hab)).of_isPLHomeomorphOn hσ
  have hJC : J ∩ C.space ⊆ J ∩ D.space := by
    rintro x ⟨hxJ, hxC⟩
    exact ⟨hxJ, hCB.subset ⟨hxC, hJB hxJ⟩⟩
  have hclJ : closure (J \ C.space) = J := by
    apply Subset.antisymm (closure_minimal sdiff_subset hJ.isPolyhedron.isClosed)
    rcases hJD with hJD | hJD
    · have hsub : J \ (J ∩ D.space) ⊆ J \ C.space := by
        rintro x ⟨hxJ, hxD⟩
        exact ⟨hxJ, fun hxC => hxD (hJC ⟨hxJ, hxC⟩)⟩
      have h := closure_mono hsub
      rwa [hJ.closure_sdiff_eq_of_isPLBall hJD inter_subset_left (by norm_num)] at h
    · intro x hxJ
      exact subset_closure ⟨hxJ, fun hxC =>
        disjoint_left.mp hJD hxJ (hJC ⟨hxJ, hxC⟩).2⟩
  have hbase : J ⊆ (boundaryComplex 3 R).space := by
    rw [boundaryComplex_space_of_closure_sdiff K C R hK hC.isCombinatorialManifoldWithBoundary
      hCK hR hRspace]
    have h := closure_mono (sdiff_subset_sdiff_left (t := C.space)
      (fun x hx => hattach (Or.inl hx)))
    rw [hclJ] at h
    exact h.trans subset_union_left
  have hAJP : ∀ i ∈ d, A i ⊆ J ∩ P := by
    intro i hi
    rw [← hcover]
    intro x hx
    exact mem_iUnion_of_mem i (mem_iUnion_of_mem hi hx)
  have hold : ρ '' ((J ∩ P) ×ˢ Icc a b) ⊆ (boundaryComplex 3 R).space := by
    rintro x ⟨z, hz, rfl⟩
    obtain ⟨i, hzi⟩ := mem_iUnion.mp (hcover.symm ▸ hz.1)
    obtain ⟨hi, hzi⟩ := mem_iUnion.mp hzi
    have hfi : (A i ∩ (D.space ∩ P)).Finite := hfinite.subset (by
      rintro y ⟨hyA, hyD, hyP⟩
      exact ⟨⟨(hAJP i hi hyA).1, hyD⟩, hyP⟩)
    have hside : ρ '' (A i ×ˢ Icc a b) ⊆ (boundaryComplex 3 K).space := by
      intro y hy
      exact hattach (Or.inr (image_mono (prod_mono (hAJP i hi) Subset.rfl) hy))
    have hCW : C.space ∩ W ⊆ ρ '' ((D.space ∩ P) ×ˢ Icc a b) := by
      rintro y ⟨hyC, hyW⟩
      exact hWC.subset ⟨hyW, hyC⟩
    exact image_strip_subset_boundaryComplex_complement K C R hK
      hC.isCombinatorialManifoldWithBoundary hCK hR hRspace hP (hA i hi)
      ((hAJP i hi).trans inter_subset_right) inter_subset_right hfi hab hρ hside hCW
      ⟨z, ⟨hzi, hz.2⟩, rfl⟩
  have hnew : σ '' ((J ∩ D.space) ×ˢ Icc a b) ⊆ (boundaryComplex 3 R).space := by
    rcases hJD with hJD | hJD
    · have hfi : ((J ∩ D.space) ∩ (D.space ∩ P)).Finite := hfinite.subset (by
        rintro x ⟨hxJD, -, hxP⟩
        exact ⟨hxJD, hxP⟩)
      exact image_prism_side_subset_boundaryComplex_complement D K C R hD hK hCK
        hR hRspace hJD hJDb inter_subset_left hfi hab hσ htrace.subset
    · rintro x ⟨z, hz, -⟩
      exact (disjoint_left.mp hJD hz.1.1 hz.1.2).elim
  rintro x (hxJ | ⟨z, hz, rfl⟩)
  · exact hbase hxJ
  · rcases hz.1.2 with hzP | hzD
    · rw [hσρ ⟨hzP, hz.2⟩]
      exact hold ⟨z, ⟨⟨hz.1.1, hzP⟩, hz.2⟩, rfl⟩
    · exact hnew ⟨z, ⟨⟨hz.1.1, hzD⟩, hz.2⟩, rfl⟩
end DifferentialGeometry.Topology.PiecewiseLinear
