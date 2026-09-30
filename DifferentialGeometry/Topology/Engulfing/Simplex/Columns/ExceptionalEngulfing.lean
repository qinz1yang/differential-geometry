import DifferentialGeometry.Topology.Engulfing.Simplex.Columns.ColumnPolyhedron
import DifferentialGeometry.Topology.Engulfing.Simplex.SimplexEngulfingChart

namespace DifferentialGeometry.Topology.Engulfing

open Set _root_.Topology

noncomputable section

variable {E M : Type*} [DecidableEq E] [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [TopologicalSpace M] [T2Space M]
  {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]

namespace SimplexSplit

omit [DecidableEq E] in
theorem exists_simplex_engulfing_in_chart_of_exceptional_columns
    (s : SimplexSplit ι) (v : ι → E) (hv : AffineIndependent ℝ v)
    {j : E → M} (hj : IsOpenEmbedding j) {T : Set E} (hT : IsCompact T)
    {U A : Set M} {W : Set E}
    (hU : IsOpen U) (hW : IsOpen W) (hA : IsClosed A) (hAU : A ⊆ U)
    (hWbounded : Bornology.IsBounded W) (hroof : j '' s.lowerRoof v ⊆ U)
    (hmoving : convexHull ℝ (range v) \ s.lowerRoof v ⊆ W)
    (hattach : j ⁻¹' A ∩ convexHull ℝ (range v) ⊆ s.lowerRoof v ∪ T)
    (hcolumns : j '' s.columnSaturation v hv T ⊆ U) :
    ∃ H : M ≃ₜ M, (∀ x ∉ j '' W, H x = x) ∧ (∀ x ∈ A, H x = x) ∧
      A ∪ j '' convexHull ℝ (range v) ⊆ H '' U ∧
      IsCompact (closure {x | H x ≠ x}) := by
  classical
  apply s.exists_simplex_engulfing_in_chart v hv hj (s.isClosed_columnBase v hv hT)
    hU hW hA hAU hWbounded
  · intro i hi x hx
    obtain ⟨y, hy, rfl⟩ := hx
    exact hroof (mem_image_of_mem j (mem_iUnion₂.mpr ⟨i, hi, hy⟩))
  · intro z hz t ht
    apply hcolumns
    exact mem_image_of_mem j ((s.prismPoint_mem_columnSaturation_iff v hv T z ht).mpr hz)
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
