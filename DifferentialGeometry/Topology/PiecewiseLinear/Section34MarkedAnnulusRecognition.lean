import DifferentialGeometry.Topology.PiecewiseLinear.Section34AnnularBandUniqueness
import DifferentialGeometry.Topology.PiecewiseLinear.ExistsCombinatorialTriangulation
import DifferentialGeometry.Topology.PiecewiseLinear.CircleArcs

open Set

namespace DifferentialGeometry.Topology.PiecewiseLinear

theorem IsAnnulusOn.isConnected_sdiff_ends {M : Type*} [TopologicalSpace M]
    {A J K : Set M} (hA : IsAnnulusOn A J K) : IsConnected (A \ (J ∪ K)) := by
  obtain ⟨f, hf, hi, hfull, hzero, hone⟩ := hA.exists_continuous_lateral_parametrization
  rw [← hfull, ← hzero, ← hone, ← image_lateral_open_eq_sdiff_ends hi]
  exact ((isConnected_stdSimplexBoundary 0).prod
    (isConnected_Ioo (zero_lt_one : (0 : ℝ) < 1))).image f
      (hf.mono (prod_mono_right Ioo_subset_Icc_self))

theorem IsAnnulusOn.closure_sdiff_ends {M : Type*} [TopologicalSpace M] [T2Space M]
    {A J K : Set M} (hA : IsAnnulusOn A J K) : closure (A \ (J ∪ K)) = A := by
  obtain ⟨f, hf, hi, hfull, hzero, hone⟩ := hA.exists_continuous_lateral_parametrization
  rw [← hfull, ← hzero, ← hone, ← image_lateral_open_eq_sdiff_ends hi]
  exact closure_image_lateral_open hf

theorem IsAnnulusOn.eq_of_subset_of_same_ends {M : Type*}
    [TopologicalSpace M] [T2Space M] {S A B J K : Set M}
    [ChartedSpace (EuclideanSpace ℝ (Fin 2)) S]
    (hA : IsAnnulusOn A J K) (hB : IsAnnulusOn B J K) (hBS : B ⊆ S)
    (hAB : A ⊆ B) : A = B := by
  obtain ⟨x, hxA, hxend⟩ := hA.isConnected_sdiff_ends.nonempty
  have hBA : B \ (J ∪ K) ⊆ A :=
    hA.subset_of_isPreconnected_of_disjoint_boundary_within (hAB.trans hBS)
      (sdiff_subset.trans hBS) hB.isConnected_sdiff_ends.isPreconnected
      ⟨x, ⟨hAB hxA, hxend⟩, hxA⟩ disjoint_sdiff_left
  exact hAB.antisymm (hB.closure_sdiff_ends ▸
    closure_minimal hBA hA.isCompact.isClosed)

theorem IsAnnulusOn.eq_or_eq_of_annular_cover {M : Type*}
    [TopologicalSpace M] [T2Space M] {S A B C J K : Set M}
    [ChartedSpace (EuclideanSpace ℝ (Fin 2)) S]
    (hA : IsAnnulusOn A J K) (hB : IsAnnulusOn B J K) (hC : IsAnnulusOn C J K)
    (hAS : A ⊆ S) (hcover : B ∪ C = S) (hinter : B ∩ C = J ∪ K) :
    A = B ∨ A = C := by
  have hcore : A \ (J ∪ K) ⊆ B ∨ A \ (J ∪ K) ⊆ C := by
    apply isPreconnected_iff_subset_of_disjoint_closed.mp
      hA.isConnected_sdiff_ends.isPreconnected B C hB.isCompact.isClosed hC.isCompact.isClosed
      (sdiff_subset.trans (hAS.trans hcover.symm.subset))
    apply disjoint_iff_inter_eq_empty.mp
    exact disjoint_left.mpr fun _ hx hy => hx.2 (hinter.subset hy)
  have hBS : B ⊆ S := hcover ▸ subset_union_left
  have hCS : C ⊆ S := hcover ▸ subset_union_right
  rcases hcore with hBcore | hCcore
  · exact Or.inl (hA.eq_of_subset_of_same_ends hB hBS
      (hA.closure_sdiff_ends ▸ closure_minimal hBcore hB.isCompact.isClosed))
  · exact Or.inr (hA.eq_of_subset_of_same_ends hC hCS
      (hA.closure_sdiff_ends ▸ closure_minimal hCcore hC.isCompact.isClosed))

theorem IsPLTorus.nonempty_chartedSpace_two
    {T : Set (EuclideanSpace ℝ (Fin 3))} (hT : IsPLTorus T) :
    Nonempty (ChartedSpace (EuclideanSpace ℝ (Fin 2)) T) := by
  obtain ⟨K, hfin, hspace⟩ := hT.1.exists_simplicialComplex
  let _ : Finite K.faces := hfin.to_subtype
  obtain ⟨ψ⟩ := hT.2
  have hK := isCombinatorialManifold_two_of_homeomorph_sphere_prod K
    ((Homeomorph.setCongr hspace).trans ψ)
  let _ : ChartedSpace (EuclideanSpace ℝ (Fin 2)) K.space := combinatorialChartedSpace K hK
  exact ⟨(Homeomorph.setCongr hspace).chartedSpace⟩

private theorem annulus_product_arc {E F : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [FiniteDimensional ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F]
    [FiniteDimensional ℝ F] {J : Set E} {A : Set F} (hJ : IsPLSphere 1 J)
    {δ : ℝ → F} (hδ : IsPLHomeomorphOn δ (Icc 0 1) A) :
    IsAnnulusOn (J ×ˢ A) (J ×ˢ {δ 0}) (J ×ˢ {δ 1}) := by
  obtain ⟨g, hg⟩ := hJ
  have hm := hg.prodMap hδ
  have ha := isAnnulusOn_stdSimplex_lateral.image_of_continuousOn_injOn
    hm.isPiecewiseAffineOn.continuousOn hm.bijOn.injOn
  simpa only [prodMap_image_prod, hg.image_eq, hδ.image_eq, image_singleton] using ha

theorem IsAnnulusOn.eq_or_eq_product_bands {E F M : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
    [TopologicalSpace M] [T2Space M] {J : Set E} {Q B C : Set F} {S A : Set M}
    [ChartedSpace (EuclideanSpace ℝ (Fin 2)) S] (hJ : IsPLSphere 1 J)
    {f : E × F → M} (hf : ContinuousOn f (J ×ˢ Q)) (hi : InjOn f (J ×ˢ Q))
    (himage : f '' (J ×ˢ Q) = S) {x y : F}
    (hA : IsAnnulusOn A (f '' (J ×ˢ {x})) (f '' (J ×ˢ {y}))) (hAS : A ⊆ S)
    {δ ε : ℝ → F} (hδ : IsPLHomeomorphOn δ (Icc 0 1) B)
    (hε : IsPLHomeomorphOn ε (Icc 0 1) C)
    (hδ₀ : δ 0 = x) (hδ₁ : δ 1 = y) (hε₀ : ε 0 = x) (hε₁ : ε 1 = y)
    (hcover : B ∪ C = Q) (hinter : B ∩ C = {x, y}) :
    A = f '' (J ×ˢ B) ∨ A = f '' (J ×ˢ C) := by
  have hBQ : B ⊆ Q := hcover ▸ subset_union_left
  have hCQ : C ⊆ Q := hcover ▸ subset_union_right
  have hB := (annulus_product_arc hJ hδ).image_of_continuousOn_injOn
    (hf.mono (prod_mono_right hBQ)) (hi.mono (prod_mono_right hBQ))
  have hC := (annulus_product_arc hJ hε).image_of_continuousOn_injOn
    (hf.mono (prod_mono_right hCQ)) (hi.mono (prod_mono_right hCQ))
  rw [hδ₀, hδ₁] at hB
  rw [hε₀, hε₁] at hC
  apply hA.eq_or_eq_of_annular_cover hB hC hAS
  · rw [← image_union, ← prod_union, hcover, himage]
  · rw [← hi.image_inter (prod_mono_right hBQ) (prod_mono_right hCQ)]
    rw [← prod_inter, hinter, prod_insert, image_union]
    simp only [prod_singleton]

theorem IsAnnulusOn.exists_product_arc_eq {E F M : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
    [TopologicalSpace M] [T2Space M] {J : Set E} {Q : Set F} {S A : Set M}
    [ChartedSpace (EuclideanSpace ℝ (Fin 2)) S] (hJ : IsPLSphere 1 J)
    (hQ : IsPLSphere 1 Q) {f : E × F → M} (hf : ContinuousOn f (J ×ˢ Q))
    (hi : InjOn f (J ×ˢ Q)) (himage : f '' (J ×ˢ Q) = S) {x y : F}
    (hx : x ∈ Q) (hy : y ∈ Q) (hxy : x ≠ y)
    (hA : IsAnnulusOn A (f '' (J ×ˢ {x})) (f '' (J ×ˢ {y}))) (hAS : A ⊆ S) :
    ∃ (B C : Set F) (δ ε : ℝ → F),
      IsPLHomeomorphOn δ (Icc 0 1) B ∧ IsPLHomeomorphOn ε (Icc 0 1) C ∧
      δ 0 = x ∧ δ 1 = y ∧ ε 0 = x ∧ ε 1 = y ∧ B ∪ C = Q ∧ B ∩ C = {x, y} ∧
      A = f '' (J ×ˢ B) := by
  obtain ⟨B, C, δ, ε, hδ, hε, hδ₀, hδ₁, hε₀, hε₁, hcover, hinter⟩ :=
    exists_arc_decomposition_of_isPLSphere_one hQ hx hy hxy
  rcases hA.eq_or_eq_product_bands hJ hf hi himage hAS hδ hε hδ₀ hδ₁ hε₀ hε₁
      hcover hinter with heq | heq
  · exact ⟨B, C, δ, ε, hδ, hε, hδ₀, hδ₁, hε₀, hε₁, hcover, hinter, heq⟩
  · exact ⟨C, B, ε, δ, hε, hδ, hε₀, hε₁, hδ₀, hδ₁,
      (union_comm _ _).trans hcover, (inter_comm _ _).trans hinter, heq⟩

theorem IsPLTorus.nonempty_chartedSpace_image {M : Type*}
    [TopologicalSpace M] [T2Space M] {T : Set (EuclideanSpace ℝ (Fin 3))}
    (hT : IsPLTorus T) {u : EuclideanSpace ℝ (Fin 3) → M}
    (hu : ContinuousOn u T) (hi : InjOn u T) :
    Nonempty (ChartedSpace (EuclideanSpace ℝ (Fin 2)) (u '' T)) := by
  let g : T → M := fun x => u x.val
  have hg : Continuous g := hu.domRestrict
  have hgi : Function.Injective g := fun x y hxy =>
    Subtype.ext (hi x.property y.property hxy)
  let _ : CompactSpace T := isCompact_iff_compactSpace.mp hT.1.isCompact
  have hrange : range g = u '' T := by
    exact range_comp u Subtype.val |>.trans (by rw [Subtype.range_coe])
  obtain ⟨hchart⟩ := hT.nonempty_chartedSpace_two
  let _ := hchart
  exact ⟨((hg.isClosedEmbedding hgi).isEmbedding.toHomeomorph.trans
    (Homeomorph.setCongr hrange)).chartedSpace⟩

theorem IsPLTorus.exists_product_arc_eq_of_annulus_image {E F M : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
    [TopologicalSpace M] [T2Space M] {T : Set (EuclideanSpace ℝ (Fin 3))}
    (hT : IsPLTorus T) {J : Set E} {Q : Set F} (hJ : IsPLSphere 1 J)
    (hQ : IsPLSphere 1 Q) {f : E × F → EuclideanSpace ℝ (Fin 3)}
    (hf : IsPLHomeomorphOn f (J ×ˢ Q) T) {u : EuclideanSpace ℝ (Fin 3) → M}
    (hu : ContinuousOn u T) (hi : InjOn u T) {x y : F}
    (hx : x ∈ Q) (hy : y ∈ Q) (hxy : x ≠ y) {A : Set M}
    (hA : IsAnnulusOn A ((u ∘ f) '' (J ×ˢ {x})) ((u ∘ f) '' (J ×ˢ {y})))
    (hAT : A ⊆ u '' T) :
    ∃ (B C : Set F) (δ ε : ℝ → F),
      IsPLHomeomorphOn δ (Icc 0 1) B ∧ IsPLHomeomorphOn ε (Icc 0 1) C ∧
      δ 0 = x ∧ δ 1 = y ∧ ε 0 = x ∧ ε 1 = y ∧ B ∪ C = Q ∧ B ∩ C = {x, y} ∧
      A = (u ∘ f) '' (J ×ˢ B) := by
  obtain ⟨hchart⟩ := hT.nonempty_chartedSpace_image hu hi
  let _ := hchart
  apply hA.exists_product_arc_eq hJ hQ
    (hu.comp hf.isPiecewiseAffineOn.continuousOn hf.bijOn.mapsTo)
    (hi.comp hf.bijOn.injOn hf.bijOn.mapsTo) ?_ hx hy hxy hAT
  rw [image_comp, hf.image_eq]

end DifferentialGeometry.Topology.PiecewiseLinear
