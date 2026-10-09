import DifferentialGeometry.Topology.Surface.Recognition.EmbeddedFacePartitionBCF

/-!
# An embedded face partition from indexed families of subsets of the ambient space (lane S-BCF03b)

Kernel of the assembly of BCF03 G7 part 1: the geometry produces, inside the ambient space `Wt`,
finitely many closed disks `D i` and closed circle-bundle pieces `P j` covering a closed set `Y`
(a component of `∂M₂`), with a side map and the parametrizations (in `Wt`, not in the subtype).
This file transports them to `EmbeddedFacePartition_BCF ↥Y` (reindexing by `Fin`, restriction of
every parametrization to the subtype `↥Y`).

* `exists_embeddedFacePartition_of_family_BCF`: the transport, with the identification of every
  disk and piece of the structure with the given sets (`Pt.disk (eI i) = val ⁻¹' D i`, ...),
  of the side map, and `diskCount = card I`, `pieceCount = card J`.
-/

set_option autoImplicit false

open Set Function Topology

namespace DifferentialGeometry.Topology.Surface

open DifferentialGeometry.Topology

variable {Wt : Type*} [TopologicalSpace Wt]

/-- **Transport of a family of disks and pieces in `Wt` to an embedded face partition of
`↥Y`.** -/
theorem exists_embeddedFacePartition_of_family_BCF {Y : Set Wt} {I J : Type*} [Fintype I]
    [Fintype J] [DecidableEq J] (D : I → Set Wt) (P : J → Set Wt) (side : I → J)
    (hDY : ∀ i, D i ⊆ Y)
    (hPY : ∀ j, P j ⊆ Y) (hD : ∀ i, IsClosed (D i)) (hP : ∀ j, IsClosed (P j))
    (hPne : ∀ j, (P j).Nonempty) (hcov : Y ⊆ (⋃ i, D i) ∪ ⋃ j, P j)
    (hDD : Pairwise (Disjoint on D)) (hPP : Pairwise (Disjoint on P))
    (hside : ∀ i j, (D i ∩ P j).Nonempty → side i = j)
    (hdeg : ∀ j, (Finset.univ.filter (fun i => side i = j)).card = 0 ∨
      (Finset.univ.filter (fun i => side i = j)).card = 2)
    (hdisk : ∀ i, ∃ h : Disk 2 → Wt, Continuous h ∧ Injective h ∧ range h = D i ∧
      h '' diskSphere 2 = D i ∩ P (side i))
    (hann : ∀ j, (Finset.univ.filter (fun i => side i = j)).card = 2 →
      ∃ e : Metric.sphere (0 : EuclideanSpace ℝ (Fin 2)) 1 × Icc (0 : ℝ) 1 → Wt, Continuous e ∧
        Injective e ∧ range e = P j ∧ ∀ i, side i = j →
          D i ∩ P j = e '' {q | (q.2 : ℝ) = 0} ∨ D i ∩ P j = e '' {q | (q.2 : ℝ) = 1})
    (hcirc : ∀ j, (Finset.univ.filter (fun i => side i = j)).card = 0 →
      ∃ p : P j → Circle, Continuous p ∧ IsOpenMap p) :
    ∃ (Pt : EmbeddedFacePartition_BCF Y) (eI : I ≃ Fin Pt.diskCount) (eJ : J ≃ Fin Pt.pieceCount),
      Pt.diskCount = Fintype.card I ∧ Pt.pieceCount = Fintype.card J ∧
      (∀ i, Pt.disk (eI i) = Subtype.val ⁻¹' D i) ∧
      (∀ j, Pt.piece (eJ j) = Subtype.val ⁻¹' P j) ∧ ∀ i, Pt.side (eI i) = eJ (side i) := by
  classical
  let eI : I ≃ Fin (Fintype.card I) := Fintype.equivFin I
  let eJ : J ≃ Fin (Fintype.card J) := Fintype.equivFin J
  have hcl : ∀ s : Set Wt, IsClosed s → IsClosed (Subtype.val ⁻¹' s : Set Y) := fun s hs =>
    hs.preimage continuous_subtype_val
  -- restriction of a map into `Wt` with range in `Y` to a map into `↥Y`
  have hlift : ∀ {α : Type _} [TopologicalSpace α] (h : α → Wt), Continuous h →
      (∀ x, h x ∈ Y) → ∃ h' : α → Y, Continuous h' ∧ ∀ x, (h' x : Wt) = h x := fun h hc hy =>
    ⟨fun x => ⟨h x, hy x⟩, hc.subtype_mk _, fun _ => rfl⟩
  have hdeg' : ∀ j : Fin (Fintype.card J),
      (Finset.univ.filter (fun k : Fin (Fintype.card I) => eJ (side (eI.symm k)) = j)).card =
        (Finset.univ.filter (fun i : I => side i = eJ.symm j)).card := by
    intro j
    refine Finset.card_equiv eI.symm fun k => ?_
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    exact (Equiv.eq_symm_apply eJ).symm
  refine ⟨{ diskCount := Fintype.card I
            pieceCount := Fintype.card J
            disk := fun k => Subtype.val ⁻¹' D (eI.symm k)
            piece := fun k => Subtype.val ⁻¹' P (eJ.symm k)
            side := fun k => eJ (side (eI.symm k))
            isClosed_disk := fun k => hcl _ (hD _)
            isClosed_piece := fun k => hcl _ (hP _)
            piece_nonempty := ?_
            cover := ?_
            disk_disjoint := ?_
            piece_disjoint := ?_
            side_spec := ?_
            degree := ?_
            disk_param := ?_
            annulus_param := ?_
            circle_base := ?_ }, eI, eJ, rfl, rfl, ?_, ?_, ?_⟩
  · intro k
    obtain ⟨x, hx⟩ := hPne (eJ.symm k)
    exact ⟨⟨x, hPY _ hx⟩, hx⟩
  · refine eq_univ_of_forall fun y => ?_
    rcases hcov y.2 with hy | hy
    · obtain ⟨i, hi⟩ := mem_iUnion.mp hy
      exact Or.inl (mem_iUnion.mpr ⟨eI i, by simpa using hi⟩)
    · obtain ⟨j, hj⟩ := mem_iUnion.mp hy
      exact Or.inr (mem_iUnion.mpr ⟨eJ j, by simpa using hj⟩)
  · intro k k' hkk'
    have hne : eI.symm k ≠ eI.symm k' := fun h => hkk' (eI.symm.injective h)
    exact (hDD hne).preimage Subtype.val
  · intro k k' hkk'
    have hne : eJ.symm k ≠ eJ.symm k' := fun h => hkk' (eJ.symm.injective h)
    exact (hPP hne).preimage Subtype.val
  · intro k j ⟨y, hyk, hyj⟩
    have h1 := hside (eI.symm k) (eJ.symm j) ⟨y.1, hyk, hyj⟩
    change eJ (side (eI.symm k)) = j
    rw [h1]
    simp
  · intro j
    rw [hdeg']
    exact hdeg _
  · intro k
    obtain ⟨h, hc, hi, hr, himg⟩ := hdisk (eI.symm k)
    obtain ⟨h', hc', hv⟩ := hlift h hc fun x => hDY _ (hr ▸ mem_range_self x)
    refine ⟨h', hc', fun x x' hxx' => hi ?_, ?_, ?_⟩
    · rw [← hv, ← hv, hxx']
    · ext y
      constructor
      · rintro ⟨x, rfl⟩
        change (h' x : Wt) ∈ D (eI.symm k)
        rw [hv]
        exact hr ▸ mem_range_self x
      · intro hy
        have hy' : (y : Wt) ∈ range h := hr ▸ hy
        obtain ⟨x, hx⟩ := hy'
        exact ⟨x, Subtype.ext (by rw [hv, hx])⟩
    · ext y
      constructor
      · rintro ⟨x, hx, rfl⟩
        have hm : (h' x : Wt) ∈ h '' diskSphere 2 := ⟨x, hx, (hv x).symm⟩
        rw [himg] at hm
        exact ⟨hm.1, by simpa using hm.2⟩
      · rintro ⟨hy1, hy2⟩
        have hm : (y : Wt) ∈ h '' diskSphere 2 := by
          rw [himg]
          exact ⟨hy1, by simpa using hy2⟩
        obtain ⟨x, hx, hxy⟩ := hm
        exact ⟨x, hx, Subtype.ext (by rw [hv, hxy])⟩
  · intro j hj
    have hj' : (Finset.univ.filter (fun i : I => side i = eJ.symm j)).card = 2 := by
      rw [← hdeg' j]
      exact hj
    obtain ⟨e, hc, hi, hr, hends⟩ := hann (eJ.symm j) hj'
    obtain ⟨e', hc', hv⟩ := hlift e hc fun x => hPY _ (hr ▸ mem_range_self x)
    have himg : ∀ s : Set (Metric.sphere (0 : EuclideanSpace ℝ (Fin 2)) 1 × Icc (0 : ℝ) 1),
        e' '' s = Subtype.val ⁻¹' (e '' s) := by
      intro s
      ext y
      constructor
      · rintro ⟨x, hx, rfl⟩
        exact ⟨x, hx, (hv x).symm⟩
      · rintro ⟨x, hx, hxy⟩
        exact ⟨x, hx, Subtype.ext (by rw [hv, hxy])⟩
    refine ⟨e', hc', fun x x' hxx' => hi ?_, ?_, ?_⟩
    · rw [← hv, ← hv, hxx']
    · ext y
      constructor
      · rintro ⟨x, rfl⟩
        change (e' x : Wt) ∈ P (eJ.symm j)
        rw [hv]
        exact hr ▸ mem_range_self x
      · intro hy
        have hy' : (y : Wt) ∈ range e := hr ▸ hy
        obtain ⟨x, hx⟩ := hy'
        exact ⟨x, Subtype.ext (by rw [hv, hx])⟩
    · intro k hk
      have hk' : side (eI.symm k) = eJ.symm j := by
        change eJ (side (eI.symm k)) = j at hk
        rw [← hk]
        simp
      have hint : ∀ s : Set Wt, (Subtype.val ⁻¹' D (eI.symm k) ∩ Subtype.val ⁻¹' P (eJ.symm j) :
          Set Y) = Subtype.val ⁻¹' (D (eI.symm k) ∩ P (eJ.symm j)) := fun _ => rfl
      rcases hends (eI.symm k) hk' with h | h
      · exact Or.inl (by rw [himg, ← h]; exact hint ∅)
      · exact Or.inr (by rw [himg, ← h]; exact hint ∅)
  · intro k hk
    have hk' : (Finset.univ.filter (fun i : I => side i = eJ.symm k)).card = 0 := by
      rw [← hdeg' k]
      exact hk
    obtain ⟨p, hpc, hpo⟩ := hcirc (eJ.symm k) hk'
    let ψ : (Subtype.val ⁻¹' P (eJ.symm k) : Set Y) ≃ₜ P (eJ.symm k) :=
      { toFun := fun x => ⟨x.1.1, x.2⟩
        invFun := fun w => ⟨⟨w.1, hPY _ w.2⟩, w.2⟩
        left_inv := fun _ => rfl
        right_inv := fun _ => rfl
        continuous_toFun := (continuous_subtype_val.comp continuous_subtype_val).subtype_mk _
        continuous_invFun :=
          (((continuous_subtype_val).subtype_mk _).subtype_mk _) }
    exact ⟨fun x => p (ψ x), hpc.comp ψ.continuous, hpo.comp ψ.isOpenMap⟩
  · intro i
    simp [eI]
  · intro j
    simp [eJ]
  · intro i
    simp [eI, eJ]

end DifferentialGeometry.Topology.Surface
