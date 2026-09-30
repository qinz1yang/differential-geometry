import DifferentialGeometry.Topology.Engulfing.Simplex.SimplexPrismTransport
import DifferentialGeometry.Topology.Engulfing.Prism.PrismColumns
import DifferentialGeometry.Topology.Homeomorph.CompactSupportExtension

namespace DifferentialGeometry.Topology.Engulfing

open Set _root_.Topology

noncomputable section

variable {ι E : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

namespace SimplexSplit

def prismPoint (s : SimplexSplit ι) (v : ι → E) (z : s.horizontal) (t : ℝ) : E :=
  simplexPoint v (s.fiberPoint z t)

theorem ambientPrismHomeomorph_apply_prismPoint (s : SimplexSplit ι) (v : ι → E)
    (hv : AffineIndependent ℝ v) (z : s.horizontal) (t : ℝ) :
    s.ambientPrismHomeomorph v hv (s.prismPoint v z t) = ((0, z), t) := by
  apply (s.ambientPrismHomeomorph v hv).symm.injective
  rw [Homeomorph.symm_apply_apply, s.ambientPrismHomeomorph_symm_apply]
  simp only [Submodule.coe_zero, zero_add, prismPoint]

theorem prismPoint_mem_simplex (s : SimplexSplit ι) (v : ι → E)
    (hv : AffineIndependent ℝ v) (z : s.base) {t : ℝ}
    (ht : t ∈ Icc (s.lower z.1) (s.upper z.1)) :
    s.prismPoint v z.1 t ∈ convexHull ℝ (range v) := by
  apply (s.ambientPrismHomeomorph_simplex_iff v hv _).mpr
  rw [s.ambientPrismHomeomorph_apply_prismPoint]
  exact ⟨rfl, ht⟩

theorem prismPoint_lower_mem_facet (s : SimplexSplit ι) (v : ι → E)
    (hv : AffineIndependent ℝ v) (z : s.base) :
    ∃ i ∈ s.right, s.prismPoint v z.1 (s.lower z.1) ∈ simplexFacet v i := by
  apply (s.ambientPrismHomeomorph_lower_graph_iff v hv
    (s.prismPoint_mem_simplex v hv z ⟨le_rfl, z.property⟩)).mp
  rw [s.ambientPrismHomeomorph_apply_prismPoint]

theorem prismPoint_upper_mem_facet (s : SimplexSplit ι) (v : ι → E)
    (hv : AffineIndependent ℝ v) (z : s.base) :
    ∃ i ∈ s.left, s.prismPoint v z.1 (s.upper z.1) ∈ simplexFacet v i := by
  apply (s.ambientPrismHomeomorph_upper_graph_iff v hv
    (s.prismPoint_mem_simplex v hv z ⟨z.property, le_rfl⟩)).mp
  rw [s.ambientPrismHomeomorph_apply_prismPoint]

theorem exists_simplex_engulfing_of_graph (s : SimplexSplit ι) (v : ι → E)
    (hv : AffineIndependent ℝ v) {J : Set s.base} (hJ : IsClosed J)
    {U W A : Set E} (hU : IsOpen U) (hW : IsOpen W) (hA : IsClosed A) (hAU : A ⊆ U)
    (hgraph : ∀ z : s.base, s.prismPoint v z.1 (s.lower z.1) ∈ U)
    (hcolumns : ∀ z ∈ J, ∀ t ∈ Icc (s.lower z.1) (s.upper z.1), s.prismPoint v z.1 t ∈ U)
    (hmoving : ∀ z ∉ J, ∀ t ∈ Ioc (s.lower z.1) (s.upper z.1), s.prismPoint v z.1 t ∈ W)
    (havoid : ∀ z ∉ J, ∀ t ∈ Ioc (s.lower z.1) (s.upper z.1), s.prismPoint v z.1 t ∉ A) :
    ∃ H : E ≃ₜ E, (∀ x ∉ W, H x = x) ∧ (∀ x ∈ A, H x = x) ∧
      A ∪ convexHull ℝ (range v) ⊆ H '' U := by
  let e := s.ambientPrismHomeomorph v hv
  let f : s.base → ℝ := fun z => s.lower z.1
  let g : s.base → ℝ := fun z => s.upper z.1
  have hf : Continuous f := s.continuous_lower.comp
    (continuous_subtype_val.comp continuous_subtype_val)
  have hg : Continuous g := s.continuous_upper.comp
    (continuous_subtype_val.comp continuous_subtype_val)
  have hp (z : s.base) (t : ℝ) : e.symm ((0, z.1), t) = s.prismPoint v z.1 t := by
    rw [s.ambientPrismHomeomorph_symm_apply]
    simp only [Submodule.coe_zero, zero_add, prismPoint]
  obtain ⟨G, _, hfix, hkeep, _, _, hinc⟩ := exists_prism_engulfing_relative_columns
    (0 : simplexTransverse v) s.isClosed_base hf hg (fun z => z.property)
    (fun z hz => s.lower_eq_upper_of_mem_frontier hz) hJ
    (hU.preimage e.symm.continuous) (hW.preimage e.symm.continuous)
    (hA.preimage e.symm.continuous) (fun p hp => hAU hp)
    (fun z => by change e.symm _ ∈ U; rw [hp]; exact hgraph z)
    (fun z hz t ht => by change e.symm _ ∈ U; rw [hp]; exact hcolumns z hz t ht)
    (fun z hz t ht => by change e.symm _ ∈ W; rw [hp]; exact hmoving z hz t ht)
    (fun z hz t ht => by change e.symm _ ∉ A; rw [hp]; exact havoid z hz t ht)
  let H : E ≃ₜ E := (e.trans G).trans e.symm
  have hHx (x : E) : H x = e.symm (G (e x)) := rfl
  refine ⟨H, ?_, ?_, ?_⟩
  · intro x hx
    rw [hHx, hfix]
    · exact e.symm_apply_apply x
    · change e.symm (e x) ∉ W
      simpa only [e.symm_apply_apply] using hx
  · intro x hx
    rw [hHx, hkeep]
    · exact e.symm_apply_apply x
    · change e.symm (e x) ∈ A
      simpa only [e.symm_apply_apply] using hx
  · intro x hx
    rcases hx with hx | hx
    · refine ⟨x, hAU hx, ?_⟩
      rw [hHx, hkeep]
      · exact e.symm_apply_apply x
      · change e.symm (e x) ∈ A
        simpa only [e.symm_apply_apply] using hx
    · obtain ⟨hzero, ht⟩ := (s.ambientPrismHomeomorph_simplex_iff v hv x).mp hx
      let z : s.base := ⟨(e x).1.2, ht.1.trans ht.2⟩
      have he : ((0, z.1), (e x).2) = e x := by
        apply Prod.ext
        · apply Prod.ext
          · exact hzero.symm
          · rfl
        · rfl
      have hi := hinc z (e x).2 ht
      rw [he] at hi
      obtain ⟨p, hpU, hpG⟩ := hi
      refine ⟨e.symm p, hpU, ?_⟩
      rw [hHx, e.apply_symm_apply, hpG, e.symm_apply_apply]

theorem exists_simplex_engulfing (s : SimplexSplit ι) (v : ι → E)
    (hv : AffineIndependent ℝ v) {J : Set s.base} (hJ : IsClosed J)
    {U W A : Set E} (hU : IsOpen U) (hW : IsOpen W) (hA : IsClosed A) (hAU : A ⊆ U)
    (hroof : ∀ i ∈ s.right, simplexFacet v i ⊆ U)
    (hcolumns : ∀ z ∈ J, ∀ t ∈ Icc (s.lower z.1) (s.upper z.1), s.prismPoint v z.1 t ∈ U)
    (hmoving : ∀ z ∉ J, ∀ t ∈ Ioc (s.lower z.1) (s.upper z.1), s.prismPoint v z.1 t ∈ W)
    (havoid : ∀ z ∉ J, ∀ t ∈ Ioc (s.lower z.1) (s.upper z.1), s.prismPoint v z.1 t ∉ A) :
    ∃ H : E ≃ₜ E, (∀ x ∉ W, H x = x) ∧ (∀ x ∈ A, H x = x) ∧
      A ∪ convexHull ℝ (range v) ⊆ H '' U := by
  apply s.exists_simplex_engulfing_of_graph v hv hJ hU hW hA hAU _ hcolumns hmoving havoid
  intro z
  obtain ⟨i, hi, hx⟩ := s.prismPoint_lower_mem_facet v hv z
  exact hroof i hi hx

theorem exists_simplex_engulfing_compact_support (s : SimplexSplit ι) (v : ι → E)
    (hv : AffineIndependent ℝ v) {J : Set s.base} (hJ : IsClosed J)
    {U W A : Set E} (hU : IsOpen U) (hW : IsOpen W) (hA : IsClosed A) (hAU : A ⊆ U)
    (hWbounded : Bornology.IsBounded W)
    (hroof : ∀ i ∈ s.right, simplexFacet v i ⊆ U)
    (hcolumns : ∀ z ∈ J, ∀ t ∈ Icc (s.lower z.1) (s.upper z.1), s.prismPoint v z.1 t ∈ U)
    (hmoving : ∀ z ∉ J, ∀ t ∈ Ioc (s.lower z.1) (s.upper z.1), s.prismPoint v z.1 t ∈ W)
    (havoid : ∀ z ∉ J, ∀ t ∈ Ioc (s.lower z.1) (s.upper z.1), s.prismPoint v z.1 t ∉ A) :
    ∃ H : E ≃ₜ E, (∀ x ∉ W, H x = x) ∧ (∀ x ∈ A, H x = x) ∧
      A ∪ convexHull ℝ (range v) ⊆ H '' U ∧ IsCompact (closure {x | H x ≠ x}) := by
  obtain ⟨H, hfix, hkeep, hinc⟩ :=
    s.exists_simplex_engulfing v hv hJ hU hW hA hAU hroof hcolumns hmoving havoid
  refine ⟨H, hfix, hkeep, hinc, ?_⟩
  apply hWbounded.isCompact_closure.of_isClosed_subset isClosed_closure
  apply closure_mono
  intro x hx
  by_contra hnot
  exact hx (hfix x hnot)

end SimplexSplit

end

end DifferentialGeometry.Topology.Engulfing
