import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.KappaSolutions.BicollarSliceComponents
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.KappaSolutions.BicollarBandExtension

set_option autoImplicit false

noncomputable section

open Set Topology

namespace DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions

variable {A M : Type*} [TopologicalSpace A] [T2Space A] [CompactSpace A] [ConnectedSpace A]
  [TopologicalSpace M] [T2Space M] [SimplyConnectedSpace M] [LocallyPathConnectedSpace M]
  (φ : A × ℝ → M) (hφ : IsOpenEmbedding φ) (a : A)

include hφ

theorem bicollar_lower_closure_subset {s t : ℝ} (hst : s < t) :
    closure (bicollarLowerSide φ a s) ⊆ bicollarLowerSide φ a t := by
  obtain ⟨hBs, _hEs, _hBsop, _hEsop, hBEs, _hcs, _hBfs, _hEfs, hBcls, _hEcls,
    hns, hps⟩ := bicollar_slice_components φ hφ a s
  obtain ⟨_hBt, _hEt, hBtop, hEtop, hBEt, hct, _hBft, _hEft, _hBclt, _hEclt,
    hnt, _hpt⟩ := bicollar_slice_components φ hφ a t
  have havoid : bicollarLowerSide φ a s ⊆ (range (fun y => φ (y, t)))ᶜ := by
    intro q hq
    rintro ⟨y, rfl⟩
    exact Set.disjoint_left.mp hBEs hq (hps y t hst)
  have hsub : bicollarLowerSide φ a s ⊆ bicollarLowerSide φ a t :=
    hBs.isPreconnected.subset_left_of_subset_union hBtop hEtop hBEt
      (by rw [hct]; exact havoid)
      ⟨φ (a, s - 1), hns a (s - 1) (by linarith), hnt a (s - 1) (by linarith)⟩
  rw [hBcls]
  apply union_subset hsub
  rintro q ⟨y, rfl⟩
  exact hnt y s hst

private theorem bicollar_extension_eq_lower {s t : ℝ} (hst : s < t)
    (hBc : IsCompact (closure (bicollarLowerSide φ a s))) :
    let D := bicollarLowerSide φ a s ∪ φ '' ((univ : Set A) ×ˢ Iio t)
    D = bicollarLowerSide φ a t ∧
      IsCompact (closure D) ∧
      closure D = closure (bicollarLowerSide φ a s) ∪
        φ '' ((univ : Set A) ×ˢ Icc s t) := by
  obtain ⟨hBs, _hEs, hBsop, _hEsop, hBEs, _hcs, _hBfs, _hEfs, hBcls, _hEcls,
    hns, hps⟩ := bicollar_slice_components φ hφ a s
  obtain ⟨hDconn, hDopen, hDc, hDcl, _hBsub, hDfr⟩ :=
    bicollar_band_extends_compact_side φ hφ hst (bicollarLowerSide φ a s)
      hBs hBsop hBc hBcls hns
      (fun y z hz hmem => Set.disjoint_left.mp hBEs hmem (hps y z hz))
  let D := bicollarLowerSide φ a s ∪ φ '' ((univ : Set A) ×ˢ Iio t)
  have hpoint : φ (a, t - 1) ∈ D :=
    Or.inr ⟨(a, t - 1), ⟨mem_univ _, by change t - 1 < t; linarith⟩, rfl⟩
  have heq := connectedComponentIn_compl_frontier_eq hDconn hDopen hpoint
  rw [hDfr] at heq
  exact ⟨heq.symm, hDc, hDcl⟩

theorem bicollar_lower_compact_of_zero
    (hzero : IsCompact (closure (bicollarLowerSide φ a 0))) (c : ℝ) :
    IsCompact (closure (bicollarLowerSide φ a c)) := by
  rcases lt_trichotomy c 0 with hc | rfl | hc
  · exact hzero.of_isClosed_subset isClosed_closure
      ((bicollar_lower_closure_subset φ hφ a hc).trans subset_closure)
  · exact hzero
  · obtain ⟨heq, hcompact, _hclosure⟩ := bicollar_extension_eq_lower φ hφ a hc hzero
    rwa [heq] at hcompact


theorem bicollar_lower_regular_open (c : ℝ) :
    interior (closure (bicollarLowerSide φ a c)) = bicollarLowerSide φ a c := by
  classical
  obtain ⟨_hB, _hE, _hBop, _hEop, hBE, hcover, _hBfr, _hEfr, hBcl, hEcl,
    _hn, _hp⟩ := bicollar_slice_components φ hφ a c
  have hBC : closure (bicollarLowerSide φ a c) = (bicollarUpperSide φ a c)ᶜ := by
    rw [hBcl]
    ext x
    have hu : (x ∈ bicollarLowerSide φ a c ∨ x ∈ bicollarUpperSide φ a c) ↔
        x ∉ range (fun y => φ (y, c)) :=
      Iff.of_eq (congrArg (fun U : Set M => x ∈ U) hcover)
    have hd : ¬ (x ∈ bicollarLowerSide φ a c ∧ x ∈ bicollarUpperSide φ a c) :=
      fun hx => Set.disjoint_left.mp hBE hx.1 hx.2
    change (x ∈ bicollarLowerSide φ a c ∨ x ∈ range (fun y => φ (y, c))) ↔
      x ∉ bicollarUpperSide φ a c
    tauto
  have hEC : closure (bicollarUpperSide φ a c) = (bicollarLowerSide φ a c)ᶜ := by
    rw [hEcl]
    ext x
    have hu : (x ∈ bicollarLowerSide φ a c ∨ x ∈ bicollarUpperSide φ a c) ↔
        x ∉ range (fun y => φ (y, c)) :=
      Iff.of_eq (congrArg (fun U : Set M => x ∈ U) hcover)
    have hd : ¬ (x ∈ bicollarLowerSide φ a c ∧ x ∈ bicollarUpperSide φ a c) :=
      fun hx => Set.disjoint_left.mp hBE hx.1 hx.2
    change (x ∈ bicollarUpperSide φ a c ∨ x ∈ range (fun y => φ (y, c))) ↔
      x ∉ bicollarLowerSide φ a c
    tauto
  rw [hBC, interior_compl, hEC, compl_compl]

theorem bicollar_ordered_band
    (hzero : IsCompact (closure (bicollarLowerSide φ a 0)))
    {s t : ℝ} (hst : s < t) :
    closure (bicollarLowerSide φ a s) ⊆ bicollarLowerSide φ a t ∧
      closure (bicollarLowerSide φ a t) =
        closure (bicollarLowerSide φ a s) ∪ φ '' ((univ : Set A) ×ˢ Icc s t) ∧
      (φ '' ((univ : Set A) ×ˢ Icc s t))ᶜ =
        bicollarLowerSide φ a s ∪ bicollarUpperSide φ a t := by
  obtain ⟨hD, _hDc, hDcl⟩ := bicollar_extension_eq_lower φ hφ a hst
    (bicollar_lower_compact_of_zero φ hφ a hzero s)
  rw [hD] at hDcl
  refine ⟨bicollar_lower_closure_subset φ hφ a hst, hDcl, ?_⟩
  obtain ⟨_hBs, _hEs, _hBsop, _hEsop, hBEs, _hcs, _hBfs, _hEfs, hBcls, _hEcls,
    _hns, hps⟩ := bicollar_slice_components φ hφ a s
  obtain ⟨_hBt, _hEt, _hBtop, hEtop, hBEt, hct, _hBft, _hEft, hBclt, _hEclt,
    _hnt, _hpt⟩ := bicollar_slice_components φ hφ a t
  let Q : Set M := φ '' ((univ : Set A) ×ˢ Icc s t)
  have hSs : range (fun y => φ (y, s)) ⊆ Q := by
    rintro q ⟨y, rfl⟩
    exact ⟨(y, s), ⟨mem_univ _, le_rfl, hst.le⟩, rfl⟩
  have hclQ : closure (bicollarLowerSide φ a t) = bicollarLowerSide φ a s ∪ Q := by
    rw [hDcl, hBcls, union_assoc, union_eq_self_of_subset_left hSs]
  have hQnotB : Disjoint Q (bicollarLowerSide φ a s) := by
    rw [Set.disjoint_left]
    rintro q ⟨⟨y, z⟩, ⟨_, hzlo, _hzhi⟩, rfl⟩ hqB
    rcases eq_or_lt_of_le hzlo with hz | hz
    · have hqavoid := connectedComponentIn_subset
        (range (fun y => φ (y, s)))ᶜ (φ (a, s - 1)) hqB
      exact hqavoid ⟨y, by rw [hz]⟩
    · exact Set.disjoint_left.mp hBEs hqB (hps y z hz)
  have hQnotE : Disjoint Q (bicollarUpperSide φ a t) := by
    have havoid : closure (bicollarLowerSide φ a t) ⊆ (bicollarUpperSide φ a t)ᶜ :=
      closure_minimal hBEt.subset_compl_right hEtop.isClosed_compl
    rw [Set.disjoint_left]
    intro q hqQ hqE
    apply havoid _ hqE
    rw [hclQ]
    exact Or.inr hqQ
  have hcover : closure (bicollarLowerSide φ a t) ∪ bicollarUpperSide φ a t = univ := by
    apply Set.eq_univ_of_forall
    intro q
    by_cases hqt : q ∈ range (fun y => φ (y, t))
    · left
      rw [hBclt]
      exact Or.inr hqt
    · have hq : q ∈ bicollarLowerSide φ a t ∪ bicollarUpperSide φ a t := by
        rw [hct]
        exact hqt
      rcases hq with hqB | hqE
      · exact Or.inl (subset_closure hqB)
      · exact Or.inr hqE
  change Qᶜ = bicollarLowerSide φ a s ∪ bicollarUpperSide φ a t
  ext q
  constructor
  · intro hq
    have hqu : q ∈ closure (bicollarLowerSide φ a t) ∪ bicollarUpperSide φ a t := by
      rw [hcover]
      exact mem_univ q
    rcases hqu with hqcl | hqE
    · rw [hclQ] at hqcl
      exact Or.inl (hqcl.resolve_right hq)
    · exact Or.inr hqE
  · rintro (hqB | hqE) hqQ
    · exact Set.disjoint_left.mp hQnotB hqQ hqB
    · exact Set.disjoint_left.mp hQnotE hqQ hqE

theorem bicollar_path_crosses_slice (c : ℝ) {x y : M}
    (hx : x ∈ bicollarLowerSide φ a c) (hy : y ∈ bicollarUpperSide φ a c)
    (γ : Path x y) : ∃ u, γ u ∈ range (fun z => φ (z, c)) := by
  by_contra! havoid
  obtain ⟨_hB, _hE, hBop, hEop, hBE, hcover, _hBfr, _hEfr, _hBcl, _hEcl,
    _hn, _hp⟩ := bicollar_slice_components φ hφ a c
  have hsub : range γ ⊆ bicollarLowerSide φ a c ∪ bicollarUpperSide φ a c := by
    rw [hcover]
    rintro q ⟨u, rfl⟩
    exact havoid u
  have hlower : range γ ⊆ bicollarLowerSide φ a c :=
    (isConnected_range γ.continuous).isPreconnected.subset_left_of_subset_union
      hBop hEop hBE hsub ⟨x, ⟨0, γ.source⟩, hx⟩
  exact Set.disjoint_left.mp hBE (hlower ⟨1, γ.target⟩) hy

theorem bicollar_upper_noncompact [NoncompactSpace M]
    (hzero : IsCompact (closure (bicollarLowerSide φ a 0))) (c : ℝ) :
    ¬ IsCompact (closure (bicollarUpperSide φ a c)) := by
  intro hEc
  have hBc := bicollar_lower_compact_of_zero φ hφ a hzero c
  obtain ⟨_hB, _hE, _hBop, _hEop, _hBE, hcover, _hBfr, _hEfr, hBcl, _hEcl,
    _hn, _hp⟩ := bicollar_slice_components φ hφ a c
  have hu : closure (bicollarLowerSide φ a c) ∪
      closure (bicollarUpperSide φ a c) = univ := by
    apply Set.eq_univ_of_forall
    intro q
    by_cases hqS : q ∈ range (fun y => φ (y, c))
    · left
      rw [hBcl]
      exact Or.inr hqS
    · have hq : q ∈ bicollarLowerSide φ a c ∪ bicollarUpperSide φ a c := by
        rw [hcover]
        exact hqS
      rcases hq with hqB | hqE
      · exact Or.inl (subset_closure hqB)
      · exact Or.inr (subset_closure hqE)
  exact noncompact_univ M (hu ▸ hBc.union hEc)

end DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions
