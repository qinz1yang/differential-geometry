import DifferentialGeometry.Topology.Engulfing.Simplex.SimplexEngulfing

namespace DifferentialGeometry.Topology.Engulfing

open Set _root_.Topology

noncomputable section

variable {E M : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [TopologicalSpace M] [T2Space M]

theorem exists_chart_extension_fixed_outside {j : E → M} (hj : IsOpenEmbedding j)
    (e : E ≃ₜ E) {W : Set E} (hW : Bornology.IsBounded W)
    (hfix : ∀ x ∉ W, e x = x) :
    ∃ H : M ≃ₜ M, (∀ x, H (j x) = j (e x)) ∧
      (∀ x ∉ j '' W, H x = x) ∧ IsCompact (closure {x | H x ≠ x}) := by
  obtain ⟨H, hH, hfixH, _⟩ := exists_homeomorph_extension_of_isOpenEmbedding
    hj e hW.isCompact_closure (fun x hx => hfix x (fun h => hx (subset_closure h)))
  refine ⟨H, hH, ?_, ?_⟩
  · intro x hx
    by_cases hrange : x ∈ range j
    · obtain ⟨y, rfl⟩ := hrange
      rw [hH, hfix]
      exact fun hy => hx (mem_image_of_mem j hy)
    · exact hfixH x (fun h => hrange (image_subset_range j _ h))
  · have hcompact : IsCompact (j '' closure W) := hW.isCompact_closure.image hj.continuous
    apply hcompact.of_isClosed_subset isClosed_closure
    apply closure_minimal _ hcompact.isClosed
    intro x hx
    by_contra hn
    exact hx (hfixH x hn)

namespace SimplexSplit

variable {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]

theorem exists_simplex_engulfing_in_chart (s : SimplexSplit ι) (v : ι → E)
    (hv : AffineIndependent ℝ v) {j : E → M} (hj : IsOpenEmbedding j)
    {J : Set s.base} (hJ : IsClosed J) {U A : Set M} {W : Set E}
    (hU : IsOpen U) (hW : IsOpen W) (hA : IsClosed A) (hAU : A ⊆ U)
    (hWbounded : Bornology.IsBounded W)
    (hroof : ∀ i ∈ s.right, j '' simplexFacet v i ⊆ U)
    (hcolumns : ∀ z ∈ J, ∀ t ∈ Icc (s.lower z.1) (s.upper z.1), j (s.prismPoint v z.1 t) ∈ U)
    (hmoving : ∀ z ∉ J, ∀ t ∈ Ioc (s.lower z.1) (s.upper z.1), s.prismPoint v z.1 t ∈ W)
    (havoid : ∀ z ∉ J, ∀ t ∈ Ioc (s.lower z.1) (s.upper z.1), j (s.prismPoint v z.1 t) ∉ A) :
    ∃ H : M ≃ₜ M, (∀ x ∉ j '' W, H x = x) ∧ (∀ x ∈ A, H x = x) ∧
      A ∪ j '' convexHull ℝ (range v) ⊆ H '' U ∧ IsCompact (closure {x | H x ≠ x}) := by
  obtain ⟨e, hfix, hkeep, hinc⟩ := s.exists_simplex_engulfing v hv hJ
    (hU.preimage hj.continuous) hW (hA.preimage hj.continuous)
    (fun x hx => hAU hx) (fun i hi x hx => hroof i hi (mem_image_of_mem j hx))
    hcolumns hmoving havoid
  obtain ⟨H, hH, hfixH, hcompact⟩ :=
    exists_chart_extension_fixed_outside hj e hWbounded hfix
  have hkeepH : ∀ x ∈ A, H x = x := by
    intro x hx
    by_cases hrange : x ∈ range j
    · obtain ⟨y, rfl⟩ := hrange
      rw [hH, hkeep y hx]
    · exact hfixH x (fun h => hrange (image_subset_range j _ h))
  refine ⟨H, hfixH, hkeepH, ?_, hcompact⟩
  intro x hx
  rcases hx with hx | hx
  · exact ⟨x, hAU hx, hkeepH x hx⟩
  · obtain ⟨y, hy, rfl⟩ := hx
    obtain ⟨z, hz, he⟩ := hinc (Or.inr hy)
    exact ⟨j z, hz, (hH z).trans (congrArg j he)⟩

theorem exists_simplex_engulfing_in_chart_no_exceptions (s : SimplexSplit ι) (v : ι → E)
    (hv : AffineIndependent ℝ v) {j : E → M} (hj : IsOpenEmbedding j)
    {U A : Set M} {W : Set E}
    (hU : IsOpen U) (hW : IsOpen W) (hA : IsClosed A) (hAU : A ⊆ U)
    (hWbounded : Bornology.IsBounded W)
    (hroof : ∀ i ∈ s.right, j '' simplexFacet v i ⊆ U)
    (hmoving : ∀ z : s.base, ∀ t ∈ Ioc (s.lower z.1) (s.upper z.1), s.prismPoint v z.1 t ∈ W)
    (havoid : ∀ z : s.base, ∀ t ∈ Ioc (s.lower z.1) (s.upper z.1), j (s.prismPoint v z.1 t) ∉ A) :
    ∃ H : M ≃ₜ M, (∀ x ∉ j '' W, H x = x) ∧ (∀ x ∈ A, H x = x) ∧
      A ∪ j '' convexHull ℝ (range v) ⊆ H '' U ∧ IsCompact (closure {x | H x ≠ x}) := by
  exact s.exists_simplex_engulfing_in_chart v hv hj (J := ∅) isClosed_empty
    hU hW hA hAU hWbounded hroof (fun z hz => False.elim hz)
    (fun z _ => hmoving z) (fun z _ => havoid z)

def lowerRoof (s : SimplexSplit ι) (v : ι → E) : Set E :=
  ⋃ i ∈ s.right, simplexFacet v i

theorem prismPoint_notMem_lowerRoof (s : SimplexSplit ι) (v : ι → E)
    (hv : AffineIndependent ℝ v) (z : s.base) {t : ℝ}
    (ht : t ∈ Ioc (s.lower z.1) (s.upper z.1)) :
    s.prismPoint v z.1 t ∉ s.lowerRoof v := by
  intro h
  have hfacet : ∃ i ∈ s.right, s.prismPoint v z.1 t ∈ simplexFacet v i := by
    obtain ⟨i, hi, hx⟩ := mem_iUnion₂.mp h
    exact ⟨i, hi, hx⟩
  have he := (s.ambientPrismHomeomorph_lower_graph_iff v hv
    (s.prismPoint_mem_simplex v hv z ⟨ht.1.le, ht.2⟩)).mpr hfacet
  rw [s.ambientPrismHomeomorph_apply_prismPoint] at he
  exact (ne_of_gt ht.1) he

theorem exists_simplex_engulfing_in_chart_of_roof (s : SimplexSplit ι) (v : ι → E)
    (hv : AffineIndependent ℝ v) {j : E → M} (hj : IsOpenEmbedding j)
    {U A : Set M} {W : Set E}
    (hU : IsOpen U) (hW : IsOpen W) (hA : IsClosed A) (hAU : A ⊆ U)
    (hWbounded : Bornology.IsBounded W) (hroof : j '' s.lowerRoof v ⊆ U)
    (hmoving : convexHull ℝ (range v) \ s.lowerRoof v ⊆ W)
    (hattach : j ⁻¹' A ∩ convexHull ℝ (range v) ⊆ s.lowerRoof v) :
    ∃ H : M ≃ₜ M, (∀ x ∉ j '' W, H x = x) ∧ (∀ x ∈ A, H x = x) ∧
      A ∪ j '' convexHull ℝ (range v) ⊆ H '' U ∧ IsCompact (closure {x | H x ≠ x}) := by
  apply s.exists_simplex_engulfing_in_chart_no_exceptions v hv hj
    hU hW hA hAU hWbounded
  · intro i hi x hx
    obtain ⟨y, hy, rfl⟩ := hx
    exact hroof (mem_image_of_mem j (mem_iUnion₂.mpr ⟨i, hi, hy⟩))
  · intro z t ht
    exact hmoving ⟨s.prismPoint_mem_simplex v hv z ⟨ht.1.le, ht.2⟩,
      s.prismPoint_notMem_lowerRoof v hv z ht⟩
  · intro z t ht hApoint
    exact s.prismPoint_notMem_lowerRoof v hv z ht (hattach
      ⟨hApoint, s.prismPoint_mem_simplex v hv z ⟨ht.1.le, ht.2⟩⟩)

end SimplexSplit

end

end DifferentialGeometry.Topology.Engulfing
