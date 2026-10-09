import DifferentialGeometry.Topology.SphereSeparation.BicollarComponents
import DifferentialGeometry.Topology.SphereSeparation.EuclideanComplementCompactSide
import DifferentialGeometry.Topology.Ends.ComplementComponents

noncomputable section

open Set Topology

namespace DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions

private theorem closure_eq_compl_of_two_sides
    {V : Type*} [TopologicalSpace V] {C D S : Set V}
    (hdisjoint : Disjoint C D) (hunion : C ∪ D = Sᶜ)
    (hclosure : closure C = C ∪ S) : closure C = Dᶜ := by
  classical
  rw [hclosure]
  ext x
  have hu : (x ∈ C ∨ x ∈ D) ↔ x ∉ S :=
    Iff.of_eq (congrArg (fun U : Set V => x ∈ U) hunion)
  have hd : ¬ (x ∈ C ∧ x ∈ D) := fun h => Set.disjoint_left.mp hdisjoint h.1 h.2
  change (x ∈ C ∨ x ∈ S) ↔ x ∉ D
  tauto

theorem exists_bicollar_compact_end_sides
    {A M V : Type*} [TopologicalSpace A] [T2Space A] [CompactSpace A] [ConnectedSpace A]
    [TopologicalSpace M] [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
    (hdim : 2 ≤ Module.finrank ℝ V) (e : M ≃ₜ V)
    (φ : A × ℝ → M) (hφ : IsOpenEmbedding φ) :
    ∃ B E : Set M,
      IsConnected B ∧ IsConnected E ∧ IsOpen B ∧ IsOpen E ∧ Disjoint B E ∧
      B ∪ E = (range (fun y => φ (y, 0)))ᶜ ∧
      IsCompact (closure B) ∧ ¬ IsCompact (closure E) ∧
      closure B = B ∪ range (fun y => φ (y, 0)) ∧
      interior (closure B) = B ∧
      frontier (closure B) = range (fun y => φ (y, 0)) ∧
      frontier E = range (fun y => φ (y, 0)) ∧
      (((∀ y z, z < 0 → φ (y, z) ∈ B) ∧ (∀ y z, 0 < z → φ (y, z) ∈ E)) ∨
       ((∀ y z, z < 0 → φ (y, z) ∈ E) ∧ (∀ y z, 0 < z → φ (y, z) ∈ B))) := by
  classical
  let q : A × ℝ → V := e ∘ φ
  have hq : IsOpenEmbedding q := e.isOpenEmbedding.comp hφ
  let S : Set V := range (fun y => q (y, 0))
  have hS : IsCompact S := isCompact_range
    (hq.continuous.comp (continuous_id.prodMk continuous_const))
  obtain ⟨C, D, hC, hD, hCop, hDop, hCD, hCDunion, hCf, hDf, hCcl, hDcl,
    _hcomponents, hnegative, hpositive⟩ := bicollar_complement_components q hq
  have horiented : ∃ C D : Set V,
      IsConnected C ∧ IsConnected D ∧ IsOpen C ∧ IsOpen D ∧ Disjoint C D ∧
      C ∪ D = Sᶜ ∧ IsCompact (closure C) ∧ ¬ IsCompact (closure D) ∧
      frontier C = S ∧ frontier D = S ∧ closure C = C ∪ S ∧ closure D = D ∪ S ∧
      (((∀ y z, z < 0 → q (y, z) ∈ C) ∧ (∀ y z, 0 < z → q (y, z) ∈ D)) ∨
       ((∀ y z, z < 0 → q (y, z) ∈ D) ∧ (∀ y z, 0 < z → q (y, z) ∈ C))) := by
    rcases exactly_one_compact_closure_of_two_complementary_components hdim hS
      hC hD hCop hDop hCD hCDunion with hcompact | hcompact
    · exact ⟨C, D, hC, hD, hCop, hDop, hCD, hCDunion, hcompact.1, hcompact.2,
        hCf, hDf, hCcl, hDcl, Or.inl ⟨hnegative, hpositive⟩⟩
    · exact ⟨D, C, hD, hC, hDop, hCop, hCD.symm, (union_comm D C).trans hCDunion,
        hcompact.1, hcompact.2, hDf, hCf, hDcl, hCcl, Or.inr ⟨hnegative, hpositive⟩⟩
  obtain ⟨C, D, hC, hD, hCop, hDop, hCD, hCDunion, hCc, hDnc, _hCf, hDf,
    hCcl, hDcl, hsign⟩ := horiented
  have hCcompl : closure C = Dᶜ := closure_eq_compl_of_two_sides hCD hCDunion hCcl
  have hDcompl : closure D = Cᶜ := closure_eq_compl_of_two_sides hCD.symm
    ((union_comm D C).trans hCDunion) hDcl
  have hCint : interior (closure C) = C := by
    rw [hCcompl, interior_compl, hDcompl, compl_compl]
  have hCfront : frontier (closure C) = S := by
    rw [hCcompl, frontier_compl, hDf]
  have hcentral : e ⁻¹' S = range (fun y => φ (y, 0)) := by
    ext x
    constructor
    · rintro ⟨y, hy⟩
      exact ⟨y, e.injective hy⟩
    · rintro ⟨y, rfl⟩
      exact ⟨y, rfl⟩
  refine ⟨e ⁻¹' C, e ⁻¹' D, e.isConnected_preimage.mpr hC,
    e.isConnected_preimage.mpr hD, e.isOpen_preimage.mpr hCop,
    e.isOpen_preimage.mpr hDop, hCD.preimage e, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [← preimage_union, hCDunion, preimage_compl, hcentral]
  · rw [← e.preimage_closure]
    exact e.isCompact_preimage.mpr hCc
  · rw [← e.preimage_closure]
    exact fun h => hDnc (e.isCompact_preimage.mp h)
  · rw [← e.preimage_closure, hCcl, preimage_union, hcentral]
  · rw [← e.preimage_closure, ← e.preimage_interior, hCint]
  · rw [← e.preimage_closure, ← e.preimage_frontier, hCfront, hcentral]
  · rw [← e.preimage_frontier, hDf, hcentral]
  · exact hsign

open DifferentialGeometry.Geometry.Topology in
theorem exists_bicollar_compact_end_sides_of_homotopic_disjoint
    {A M : Type*} [TopologicalSpace A] [T2Space A] [CompactSpace A] [ConnectedSpace A]
    [TopologicalSpace M] [T2Space M] [ConnectedSpace M] [LocallyConnectedSpace M]
    [NoncompactSpace M]
    (φ : A × ℝ → M) (hφ : IsOpenEmbedding φ)
    (r : C(M, M)) (hr : ContinuousMap.Homotopic r (ContinuousMap.id M))
    (hdisjoint : Disjoint (range r) (range (fun y => φ (y, 0))))
    (hends : ¬ DifferentialGeometry.Geometry.Topology.HasAtLeastEnds M 2) :
    ∃ B E : Set M,
      IsConnected B ∧ IsConnected E ∧ IsOpen B ∧ IsOpen E ∧ Disjoint B E ∧
      B ∪ E = (range (fun y => φ (y, 0)))ᶜ ∧
      IsCompact (closure B) ∧ ¬ IsCompact (closure E) ∧
      closure B = B ∪ range (fun y => φ (y, 0)) ∧
      interior (closure B) = B ∧
      frontier (closure B) = range (fun y => φ (y, 0)) ∧
      frontier E = range (fun y => φ (y, 0)) ∧
      (((∀ y z, z < 0 → φ (y, z) ∈ B) ∧ (∀ y z, 0 < z → φ (y, z) ∈ E)) ∨
       ((∀ y z, z < 0 → φ (y, z) ∈ E) ∧ (∀ y z, 0 < z → φ (y, z) ∈ B))) := by
  classical
  let S : Set M := range (fun y => φ (y, 0))
  have hS : IsCompact S := isCompact_range
    (hφ.continuous.comp (continuous_id.prodMk continuous_const))
  obtain ⟨C, D, hC, hD, hCop, hDop, hCD, hCDunion, hCf, hDf, hCcl, hDcl,
    _hcomponents, hnegative, hpositive⟩ :=
      bicollar_complement_components_of_homotopic_disjoint φ hφ r hr hdisjoint
  have horiented : ∃ C D : Set M,
      IsConnected C ∧ IsConnected D ∧ IsOpen C ∧ IsOpen D ∧ Disjoint C D ∧
      C ∪ D = Sᶜ ∧ IsCompact (closure C) ∧ ¬ IsCompact (closure D) ∧
      frontier C = S ∧ frontier D = S ∧ closure C = C ∪ S ∧ closure D = D ∪ S ∧
      (((∀ y z, z < 0 → φ (y, z) ∈ C) ∧ (∀ y z, 0 < z → φ (y, z) ∈ D)) ∨
       ((∀ y z, z < 0 → φ (y, z) ∈ D) ∧ (∀ y z, 0 < z → φ (y, z) ∈ C))) := by
    rcases exactly_one_compact_closure_of_not_hasAtLeastEnds_two hends hS
        hC hD hCop hDop hCD hCDunion with hcompact | hcompact
    · exact ⟨C, D, hC, hD, hCop, hDop, hCD, hCDunion, hcompact.1, hcompact.2,
        hCf, hDf, hCcl, hDcl, Or.inl ⟨hnegative, hpositive⟩⟩
    · exact ⟨D, C, hD, hC, hDop, hCop, hCD.symm, (union_comm D C).trans hCDunion,
        hcompact.1, hcompact.2, hDf, hCf, hDcl, hCcl, Or.inr ⟨hnegative, hpositive⟩⟩
  obtain ⟨C, D, hC, hD, hCop, hDop, hCD, hCDunion, hCc, hDnc, _hCf, hDf,
    hCcl, hDcl, hsign⟩ := horiented
  have hCcompl : closure C = Dᶜ := closure_eq_compl_of_two_sides hCD hCDunion hCcl
  have hDcompl : closure D = Cᶜ := closure_eq_compl_of_two_sides hCD.symm
    ((union_comm D C).trans hCDunion) hDcl
  have hCint : interior (closure C) = C := by
    rw [hCcompl, interior_compl, hDcompl, compl_compl]
  have hCfront : frontier (closure C) = S := by
    rw [hCcompl, frontier_compl, hDf]
  exact ⟨C, D, hC, hD, hCop, hDop, hCD, hCDunion, hCc, hDnc, hCcl,
    hCint, hCfront, hDf, hsign⟩

end DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions
