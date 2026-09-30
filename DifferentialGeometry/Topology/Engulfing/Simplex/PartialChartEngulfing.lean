import DifferentialGeometry.Topology.Engulfing.Simplex.Columns.ExceptionalEngulfing
import Mathlib.Topology.PartialHomeomorph.Basic
import DifferentialGeometry.Topology.Engulfing.Simplex.SimplexMembrane

namespace DifferentialGeometry.Topology.Engulfing

open Set _root_.Topology

noncomputable section

variable {E M : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [TopologicalSpace M] [T2Space M]

theorem exists_partial_chart_extension_fixed_outside
    (e : OpenPartialHomeomorph M E) (h : E ≃ₜ E) {W : Set E}
    (hW : Bornology.IsBounded W) (hWe : closure W ⊆ e.target)
    (hfix : ∀ x ∉ W, h x = x) :
    ∃ H : M ≃ₜ M, (∀ x ∈ e.target, H (e.symm x) = e.symm (h x)) ∧
      (∀ x ∉ e.symm '' W, H x = x) ∧ IsCompact (closure {x | H x ≠ x}) := by
  have hWT : W ⊆ e.target := subset_trans subset_closure hWe
  have hT (x : E) : x ∈ e.target ↔ h x ∈ e.target := by
    constructor
    · intro hx
      by_contra hn
      have heq := hfix (h x) (fun hw => hn (hWT hw))
      have hxeq : h x = x := h.injective heq
      exact hn (hxeq.symm ▸ hx)
    · intro hx
      by_contra hn
      rw [hfix x (fun hw => hn (hWT hw))] at hx
      exact hn hx
  let h' : e.target ≃ₜ e.target := h.subtype hT
  let j : e.target → M := fun x => e.symm x
  have hj : IsOpenEmbedding j :=
    e.open_source.isOpenEmbedding_subtypeVal.comp e.symm.toHomeomorphSourceTarget.isOpenEmbedding
  let K : Set e.target := Subtype.val ⁻¹' closure W
  have hK : IsCompact K := IsEmbedding.subtypeVal.isInducing.isCompact_preimage'
    hW.isCompact_closure (by simpa using hWe)
  have hfix' (x : e.target) (hx : x ∉ K) : h' x = x := by
    apply Subtype.ext
    exact hfix x (fun hw => hx (subset_closure hw))
  obtain ⟨H, hH, houtside, _⟩ :=
    exists_homeomorph_extension_of_isOpenEmbedding hj h' hK hfix'
  have hHapply (x : E) (hx : x ∈ e.target) : H (e.symm x) = e.symm (h x) :=
    hH ⟨x, hx⟩
  refine ⟨H, hHapply, ?_, ?_⟩
  · intro x hx
    by_cases hr : x ∈ range j
    · obtain ⟨y, rfl⟩ := hr
      rw [hH]
      have heq : h' y = y := by
        apply Subtype.ext
        exact hfix y (fun hy => hx ⟨y, hy, rfl⟩)
      rw [heq]
    · exact houtside x (fun hm => hr (image_subset_range j K hm))
  · apply (hK.image hj.continuous).of_isClosed_subset isClosed_closure
    apply closure_minimal _ (hK.image hj.continuous).isClosed
    intro x hx
    by_contra hn
    exact hx (houtside x hn)

namespace SimplexSplit

variable {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]

theorem exists_simplex_engulfing_in_partial_chart (s : SimplexSplit ι) (v : ι → E)
    (hv : AffineIndependent ℝ v) (e : OpenPartialHomeomorph M E)
    {J : Set s.base} (hJ : IsClosed J) {U A : Set M} {W : Set E}
    (hU : IsOpen U) (hW : IsOpen W) (hA : IsClosed A) (hAU : A ⊆ U)
    (hWbounded : Bornology.IsBounded W) (hWe : closure W ⊆ e.target)
    (hσe : convexHull ℝ (range v) ⊆ e.target)
    (hroof : ∀ i ∈ s.right, e.symm '' simplexFacet v i ⊆ U)
    (hcolumns : ∀ z ∈ J, ∀ t ∈ Icc (s.lower z.1) (s.upper z.1),
      e.symm (s.prismPoint v z.1 t) ∈ U)
    (hmoving : ∀ z ∉ J, ∀ t ∈ Ioc (s.lower z.1) (s.upper z.1),
      s.prismPoint v z.1 t ∈ W)
    (havoid : ∀ z ∉ J, ∀ t ∈ Ioc (s.lower z.1) (s.upper z.1),
      e.symm (s.prismPoint v z.1 t) ∉ A) :
    ∃ H : M ≃ₜ M, (∀ x ∉ e.symm '' W, H x = x) ∧ (∀ x ∈ A, H x = x) ∧
      A ∪ e.symm '' convexHull ℝ (range v) ⊆ H '' U ∧
      IsCompact (closure {x | H x ≠ x}) := by
  let U' := e.target ∩ e.symm ⁻¹' U
  let A' := closure W ∩ e.symm ⁻¹' A
  have hU' : IsOpen U' := e.continuousOn_symm.isOpen_inter_preimage e.open_target hU
  have hA' : IsClosed A' :=
    (e.continuousOn_symm.mono hWe).preimage_isClosed_of_isClosed isClosed_closure hA
  obtain ⟨h, hfix, hkeep, hinc⟩ := s.exists_simplex_engulfing v hv hJ hU' hW hA'
    (fun x hx => ⟨hWe hx.1, hAU hx.2⟩)
    (fun i hi x hx => ⟨hσe (simplexFacet_subset_convexHull v i hx),
      hroof i hi (mem_image_of_mem e.symm hx)⟩)
    (fun z hz t ht => ⟨hσe (s.prismPoint_mem_simplex v hv z ht), hcolumns z hz t ht⟩)
    hmoving (fun z hz t ht hx => havoid z hz t ht hx.2)
  obtain ⟨H, hH, hfixH, hcompact⟩ :=
    exists_partial_chart_extension_fixed_outside e h hWbounded hWe hfix
  have hkeepH : ∀ x ∈ A, H x = x := by
    intro x hx
    by_cases hw : x ∈ e.symm '' W
    · obtain ⟨y, hy, rfl⟩ := hw
      rw [hH y (hWe (subset_closure hy)), hkeep y ⟨subset_closure hy, hx⟩]
    · exact hfixH x hw
  refine ⟨H, hfixH, hkeepH, ?_, hcompact⟩
  intro x hx
  rcases hx with hx | hx
  · exact ⟨x, hAU hx, hkeepH x hx⟩
  · obtain ⟨y, hy, rfl⟩ := hx
    obtain ⟨z, hz, he⟩ := hinc (Or.inr hy)
    exact ⟨e.symm z, hz.2, (hH z hz.1).trans (congrArg e.symm he)⟩

theorem exists_simplex_engulfing_in_partial_chart_of_exceptional_columns
    (s : SimplexSplit ι) (v : ι → E) (hv : AffineIndependent ℝ v)
    (e : OpenPartialHomeomorph M E) {T : Set E} (hT : IsCompact T)
    {U A : Set M} {W : Set E}
    (hU : IsOpen U) (hW : IsOpen W) (hA : IsClosed A) (hAU : A ⊆ U)
    (hWbounded : Bornology.IsBounded W) (hWe : closure W ⊆ e.target)
    (hσe : convexHull ℝ (range v) ⊆ e.target)
    (hroof : e.symm '' s.lowerRoof v ⊆ U)
    (hmoving : convexHull ℝ (range v) \ s.lowerRoof v ⊆ W)
    (hattach : e.symm ⁻¹' A ∩ convexHull ℝ (range v) ⊆ s.lowerRoof v ∪ T)
    (hcolumns : e.symm '' s.columnSaturation v hv T ⊆ U) :
    ∃ H : M ≃ₜ M, (∀ x ∉ e.symm '' W, H x = x) ∧ (∀ x ∈ A, H x = x) ∧
      A ∪ e.symm '' convexHull ℝ (range v) ⊆ H '' U ∧
      IsCompact (closure {x | H x ≠ x}) := by
  classical
  apply s.exists_simplex_engulfing_in_partial_chart v hv e
    (s.isClosed_columnBase v hv hT) hU hW hA hAU hWbounded hWe hσe
  · intro i hi x hx
    obtain ⟨y, hy, rfl⟩ := hx
    exact hroof (mem_image_of_mem e.symm (mem_iUnion₂.mpr ⟨i, hi, hy⟩))
  · intro z hz t ht
    apply hcolumns
    exact mem_image_of_mem e.symm
      ((s.prismPoint_mem_columnSaturation_iff v hv T z ht).mpr hz)
  · intro z _ t ht
    exact hmoving ⟨s.prismPoint_mem_simplex v hv z ⟨ht.1.le, ht.2⟩,
      s.prismPoint_notMem_lowerRoof v hv z ht⟩
  · intro z hz t ht hxA
    have hxσ := s.prismPoint_mem_simplex v hv z ⟨ht.1.le, ht.2⟩
    have hxT := (hattach ⟨hxA, hxσ⟩).resolve_left
      (s.prismPoint_notMem_lowerRoof v hv z ht)
    apply hz
    apply (s.prismPoint_mem_columnSaturation_iff v hv T z ⟨ht.1.le, ht.2⟩).mp
    exact ⟨hxσ, s.prismPoint v z.1 t, hxT, rfl⟩

end SimplexSplit

end

end DifferentialGeometry.Topology.Engulfing
