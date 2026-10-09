import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Closure.FC39StageFaceModelOBDe

/-!
# A new slim end that misses `∂M₁` lies in `M₂`, and the frontier of the slim set

Lane O-BD1 (by S-BD2e), G11h (suffix `_OBDe`), abstract rows.

* `newEnd_subset_M₂_OBDe`: a new end whose set misses `∂M₁` lies in `M₂` (field g6 `⊇`, and the
  `hNew` of `residualSet_disjoint_OBDe`): the slim set is `{fn ≤ 0}` near the end with `fn`
  regular, so the end is not in the relative interior of the slim set inside `M₁`;
* `frontier_slimSet_subset_ends_OBDe`: the frontier of the slim set lies in the union of the end
  slices (a point of a piece off its model boundary is interior to its range).
-/

set_option autoImplicit false

noncomputable section

open Set Function Filter
open DifferentialGeometry DifferentialGeometry.Topology GC.Endpoint GC.Seifert GC.GraphManifold
open Manifold
open scoped Manifold ContDiff Topology

universe u

namespace GC.GraphManifold.Assembly.FC39P0

variable {W : CompactCarrier.{u}} {n : ℕ} {E : BoundaryTori W n}
  {A : SmoothStageGeometry74 W E} {D : StageCutChoice74 A}

/-- **A new slim end that misses `∂M₁` lies in `M₂`.** -/
theorem newEnd_subset_M₂_OBDe (R : StageCutRows74 A D) (cov : CutCoverFacts74 A D)
    (e : R.slimPieces.NewEnd)
    (hfree : ∀ x ∈ R.slimPieces.endSet e.1, x ∉ frontier (regionM1 A.zero A.cusp)) :
    R.slimPieces.endSet e.1 ⊆ D.M₂ := by
  classical
  intro x₀ hx₀
  have hlevel : R.slimPieces.endSet e.1 =
      {x | x ∈ R.slimPieces.endNear e ∧ R.slimPieces.endFn e x = 0} :=
    R.slimPieces.endFn_level e
  have hx₀' : x₀ ∈ {x | x ∈ R.slimPieces.endNear e ∧ R.slimPieces.endFn e x = 0} := hlevel ▸ hx₀
  obtain ⟨hxn, hfn0⟩ := hx₀'
  have hx₀r : x₀ ∈ range (R.slimPieces.piece e.1.1.1).map := by
    obtain ⟨p, -, rfl⟩ := hx₀
    exact ⟨p, rfl⟩
  have hsl : x₀ ∈ D.slimSet := by
    rw [← R.slim.union_eq]
    exact mem_iUnion.2 ⟨e.1.1.1, hx₀r⟩
  have hM1 : x₀ ∈ regionM1 A.zero A.cusp := cov.slimSet_subset_M₁ hsl
  refine ⟨hM1, fun hrel => ?_⟩
  obtain ⟨-, O', hO', hx₀O', hO'S⟩ := mem_relInt_iff_exists_open_JN74.1 hrel
  have hint : x₀ ∈ interior (regionM1 A.zero A.cusp) := by
    by_contra h
    exact hfree x₀ hx₀ ⟨subset_closure hM1, h⟩
  let Sj : Set W.Carrier :=
    ⋃ j ∈ {j : Fin R.slimPieces.count | j ≠ e.1.1.1}, range (R.slimPieces.piece j).map
  have hSj : IsClosed Sj :=
    (Set.toFinite _).isClosed_biUnion fun j _ => (R.slimPieces.piece j).isClosed_range
  have hnoSj : x₀ ∉ Sj := by
    intro h
    obtain ⟨j, hj, hxj⟩ := mem_iUnion₂.1 h
    exact disjoint_left.1 (R.slimPieces.disjoint (Ne.symm hj)) hx₀r hxj
  have hVo : IsOpen (O' ∩ interior (regionM1 A.zero A.cusp) ∩
      (R.slimPieces.endNear e : Set W.Carrier) ∩ Sjᶜ) :=
    ((hO'.inter isOpen_interior).inter (R.slimPieces.endNear e).isOpen).inter hSj.isOpen_compl
  have hV : (O' ∩ interior (regionM1 A.zero A.cusp) ∩
      (R.slimPieces.endNear e : Set W.Carrier) ∩ Sjᶜ) ∈ 𝓝 x₀ :=
    hVo.mem_nhds ⟨⟨⟨hx₀O', hint⟩, hxn⟩, hnoSj⟩
  obtain ⟨-, y, ⟨⟨⟨hyO', hyint⟩, hyn⟩, hySj⟩, hypos⟩ := exists_mem_lt_of_regular_JN74
    (R.slimPieces.endNear_interior e hxn)
    (((R.slimPieces.endFn_smooth e).contMDiffAt
      ((R.slimPieces.endNear e).isOpen.mem_nhds hxn)).mdifferentiableAt (by simp)) hfn0
    (R.slimPieces.endFn_regular e x₀ hxn hfn0) hV
  have hyS : y ∈ D.slimSet := hO'S ⟨hyO', interior_subset hyint⟩
  rw [← R.slim.union_eq] at hyS
  obtain ⟨j, hj⟩ := mem_iUnion.1 hyS
  have hjj : j = e.1.1.1 := by
    by_contra hne
    exact hySj (mem_iUnion₂.2 ⟨j, hne, hj⟩)
  subst hjj
  have := (Set.ext_iff.1 (R.slimPieces.endFn_eq e) y).1 ⟨hj, hyn⟩
  exact absurd this.2 (not_le.2 hypos)

/-- **The frontier of the slim set lies in the union of the end slices.** -/
theorem frontier_slimSet_subset_ends_OBDe (R : StageCutRows74 A D) :
    frontier D.slimSet ⊆ ⋃ e : R.slimPieces.End, R.slimPieces.endSet e := by
  classical
  intro x ⟨hxc, hxi⟩
  have hclosed : IsClosed D.slimSet := isClosed_slimSet_JN74 R
  have hxS : x ∈ D.slimSet := hclosed.closure_eq ▸ hxc
  have hxS' := hxS
  rw [← R.slim.union_eq] at hxS'
  obtain ⟨j, hj⟩ := mem_iUnion.1 hxS'
  by_cases hbd : x ∈ pieceBoundary (R.slimPieces.piece j)
  · obtain ⟨q, hq, rfl⟩ := hbd
    let Fm : ModelBoundaryFace (R.slimPieces.piece j) :=
      ActualComponent.of (S := (𝓡∂ 3).boundary (R.slimPieces.piece j).Piece) hq
    have hmem : q ∈ Fm.1 := mem_connectedComponentIn hq
    obtain ⟨b, hint, hF⟩ := R.slimPieces.endFace_exhausted j Fm
    refine mem_iUnion.2 ⟨⟨(j, b), hint⟩, ?_⟩
    have hq' : q ∈ (R.slimPieces.endFace ⟨(j, b), hint⟩).1 := by rw [hF]; exact hmem
    have h2 : q ∈ slimModelEnd (R.slimPieces.model j) b := by
      have := R.slimPieces.endFace_eq (⟨(j, b), hint⟩ : R.slimPieces.End)
      rw [← this]
      exact hq'
    exact ⟨q, h2, rfl⟩
  · exact absurd (by
      have h1 := range_diff_pieceBoundary_subset_interior_OBDe (R.slimPieces.piece j) ⟨hj, hbd⟩
      rw [← R.slim.union_eq]
      exact interior_mono (subset_iUnion (fun j => range (R.slimPieces.piece j).map) j) h1) hxi

/-- **Field g6 `slim_M2`: `slimSet ∩ M₂` is the union of the new ends**, given that the new ends
miss `∂M₁`. -/
theorem slim_M2_OBDe (R : StageCutRows74 A D) (cov : CutCoverFacts74 A D)
    (hKR : ∀ F : NeighbourFace A.zero A.cusp, neighbourSet F ∩ D.slimSet ⊆
      relInt (regionM1 A.zero A.cusp) D.slimSet)
    (hfree : ∀ e : R.slimPieces.NewEnd, ∀ x ∈ R.slimPieces.endSet e.1,
      x ∉ frontier (regionM1 A.zero A.cusp)) :
    D.slimSet ∩ D.M₂ = ⋃ e : R.slimPieces.NewEnd, R.slimPieces.endSet e.1 := by
  classical
  ext x
  constructor
  · rintro ⟨hxS, hxM⟩
    have hclosed : IsClosed D.slimSet := isClosed_slimSet_JN74 R
    have hfr : x ∈ frontier D.slimSet := by
      refine ⟨subset_closure hxS, fun hint => ?_⟩
      exact hxM.2 (interior_subset_relInt_JN74 cov.slimSet_subset_M₁ hint)
    obtain ⟨e, he⟩ := mem_iUnion.1 (frontier_slimSet_subset_ends_OBDe R hfr)
    have hk : R.slimPieces.endKind e = none := by
      rcases hk : R.slimPieces.endKind e with _ | F
      · rfl
      · exfalso
        have hset := R.slim.shared_eq e F hk
        rw [hset] at he
        exact hxM.2 (hKR F ⟨he, hxS⟩)
    exact mem_iUnion.2 ⟨⟨e, hk⟩, he⟩
  · intro hx
    obtain ⟨e, he⟩ := mem_iUnion.1 hx
    refine ⟨?_, newEnd_subset_M₂_OBDe R cov e (hfree e) he⟩
    rw [← R.slim.union_eq]
    obtain ⟨p, -, rfl⟩ := he
    exact mem_iUnion.2 ⟨e.1.1.1, p, rfl⟩

/-- **Field g4 `frontier_M2`: `∂M₂ = ∂M₂-faces`** (the union of the residual faces), given the
removal property, that new ends miss `∂M₁`, that a neighbour face meeting the slim set is shared by
an end, and that `∂M₁` is the union of the neighbour faces. -/
theorem frontier_M₂_OBDe (R : StageCutRows74 A D) (cov : CutCoverFacts74 A D)
    (hKR : ∀ F : NeighbourFace A.zero A.cusp, neighbourSet F ∩ D.slimSet ⊆
      relInt (regionM1 A.zero A.cusp) D.slimSet)
    (hfree : ∀ e : R.slimPieces.NewEnd, ∀ x ∈ R.slimPieces.endSet e.1,
      x ∉ frontier (regionM1 A.zero A.cusp))
    (hshare : ∀ F : NeighbourFace A.zero A.cusp, (neighbourSet F ∩ D.slimSet).Nonempty →
      ∃ e, R.slimPieces.endKind e = some F)
    (hFb : ∀ F : NeighbourFace A.zero A.cusp, neighbourSet F ⊆ frontier (regionM1 A.zero A.cusp))
    (hcovb : frontier (regionM1 A.zero A.cusp) ⊆ ⋃ F : NeighbourFace A.zero A.cusp,
      neighbourSet F) :
    frontier D.M₂ = R.slimPieces.boundaryM2 := by
  classical
  have hM1c : IsClosed (regionM1 A.zero A.cusp) := isClosed_regionM1_GSAFE A.zero A.cusp
  have hM2c : IsClosed D.M₂ := isClosed_M₂_JN74 D
  have hSc : IsClosed D.slimSet := isClosed_slimSet_JN74 R
  ext x
  constructor
  · intro hxf
    have hxM : x ∈ D.M₂ := hM2c.frontier_subset hxf
    by_cases hxb : x ∈ frontier (regionM1 A.zero A.cusp)
    · obtain ⟨F, hxF⟩ := mem_iUnion.1 (hcovb hxb)
      have hun : ∀ e, R.slimPieces.endKind e ≠ some F := by
        intro e he
        have hset := R.slim.shared_eq e F he
        have hxe : x ∈ R.slimPieces.endSet e := by rw [hset]; exact hxF
        have hxS : x ∈ D.slimSet := by
          rw [← R.slim.union_eq]
          obtain ⟨p, -, rfl⟩ := hxe
          exact mem_iUnion.2 ⟨e.1.1, p, rfl⟩
        exact hxM.2 (hKR F ⟨hxF, hxS⟩)
      exact mem_iUnion.2 ⟨.inl ⟨F, hun⟩, hxF⟩
    · have hint1 : x ∈ interior (regionM1 A.zero A.cusp) := by
        by_contra h
        exact hxb ⟨subset_closure hxM.1, h⟩
      have hxS : x ∈ D.slimSet := by
        by_contra hnS
        apply hxf.2
        refine mem_interior.2 ⟨interior (regionM1 A.zero A.cusp) ∩ (D.slimSet)ᶜ, ?_,
          isOpen_interior.inter hSc.isOpen_compl, hint1, hnS⟩
        rintro y ⟨hy1, hy2⟩
        exact ⟨interior_subset hy1, fun hr => hy2 (relInt_subset_JN74 hr)⟩
      have hfrS : x ∈ frontier D.slimSet := by
        refine ⟨subset_closure hxS, fun hint => ?_⟩
        exact hxM.2 (interior_subset_relInt_JN74 cov.slimSet_subset_M₁ hint)
      obtain ⟨e, he⟩ := mem_iUnion.1 (frontier_slimSet_subset_ends_OBDe R hfrS)
      have hk : R.slimPieces.endKind e = none := by
        rcases hk : R.slimPieces.endKind e with _ | F
        · rfl
        · exfalso
          have hset := R.slim.shared_eq e F hk
          rw [hset] at he
          exact hxM.2 (hKR F ⟨he, hxS⟩)
      exact mem_iUnion.2 ⟨.inr ⟨e, hk⟩, he⟩
  · intro hx
    obtain ⟨Fl, hxFl⟩ := mem_iUnion.1 hx
    rcases Fl with ⟨F, hF⟩ | e
    · have hxb := hFb F hxFl
      have hxM1 : x ∈ regionM1 A.zero A.cusp := hM1c.frontier_subset hxb
      have hxS : x ∉ D.slimSet := by
        intro hS
        obtain ⟨e, he⟩ := hshare F ⟨x, hxFl, hS⟩
        exact hF e he
      have hxM : x ∈ D.M₂ := ⟨hxM1, fun hr => hxS (relInt_subset_JN74 hr)⟩
      refine ⟨subset_closure hxM, fun hint => ?_⟩
      exact hxb.2 (interior_mono (fun y hy => hy.1) hint)
    · have hxM : x ∈ D.M₂ :=
        newEnd_subset_M₂_OBDe R cov e (hfree e) hxFl
      have hlevel : R.slimPieces.endSet e.1 =
          {x | x ∈ R.slimPieces.endNear e ∧ R.slimPieces.endFn e x = 0} :=
        R.slimPieces.endFn_level e
      have hx' : x ∈ {x | x ∈ R.slimPieces.endNear e ∧ R.slimPieces.endFn e x = 0} :=
        hlevel ▸ hxFl
      obtain ⟨hxn, hfn0⟩ := hx'
      obtain ⟨O, hOo, hxO, hOn, hOM, -⟩ := faceModel_newEnd_OBDe R hKR e hxFl hxM
      refine ⟨subset_closure hxM, fun hint => ?_⟩
      have hV : interior D.M₂ ∩ O ∈ 𝓝 x :=
        (isOpen_interior.inter hOo).mem_nhds ⟨hint, hxO⟩
      obtain ⟨⟨y, ⟨hyi, hyO⟩, hyneg⟩, -⟩ := exists_mem_lt_of_regular_JN74
        (R.slimPieces.endNear_interior e hxn)
        (((R.slimPieces.endFn_smooth e).contMDiffAt
          ((R.slimPieces.endNear e).isOpen.mem_nhds hxn)).mdifferentiableAt (by simp)) hfn0
        (R.slimPieces.endFn_regular e x hxn hfn0) hV
      have := (hOM y hyO).1 (interior_subset hyi)
      exact absurd this (not_le.2 hyneg)

/-- **Distinct neighbour faces are disjoint** (zero model faces of one piece or of distinct pieces,
cusp fronts, zero versus cusp). -/
theorem neighbourSet_disjoint_OBDe (cov : CutCoverFacts74 A D)
    {F F' : NeighbourFace A.zero A.cusp} (hne : F ≠ F') :
    Disjoint (neighbourSet F) (neighbourSet F') := by
  classical
  rcases F with ⟨i, Fm⟩ | ⟨b, Fb⟩ <;> rcases F' with ⟨i', Fm'⟩ | ⟨b', Fb'⟩
  · refine disjoint_left.2 fun x hx hx' => ?_
    obtain ⟨p, hp, rfl⟩ := hx
    obtain ⟨p', hp', hpp⟩ := hx'
    by_cases hii : i = i'
    · subst hii
      have hpp' : p' = p := (A.zero.piece i).injective hpp
      subst hpp'
      apply hne
      have hFm : Fm = Fm' := ActualComponent.eq_of_mem hp hp'
      subst hFm
      rfl
    · exact disjoint_left.1 (A.zero.disjoint hii) ⟨p, rfl⟩ ⟨p', hpp⟩
  · refine disjoint_left.2 fun x hx hx' => ?_
    obtain ⟨p, -, rfl⟩ := hx
    obtain ⟨p', -, hpp⟩ := hx'
    exact disjoint_left.1 (cov.zero_cusp_disjoint i b') ⟨p, rfl⟩ ⟨p', hpp⟩
  · refine disjoint_left.2 fun x hx hx' => ?_
    obtain ⟨p, -, rfl⟩ := hx
    obtain ⟨p', -, hpp⟩ := hx'
    exact disjoint_left.1 (cov.zero_cusp_disjoint i' b) ⟨p', hpp⟩ ⟨p, rfl⟩
  · by_cases hbb : b = b'
    · subst hbb
      exact absurd (by
        have hFb : Fb = Fb' := Subtype.ext (Fb.2.trans Fb'.2.symm)
        subst hFb
        rfl) hne
    · refine disjoint_left.2 fun x hx hx' => ?_
      obtain ⟨p, -, rfl⟩ := hx
      obtain ⟨p', -, hpp⟩ := hx'
      exact disjoint_left.1 (A.cusp.disjoint hbb) ⟨p, rfl⟩ ⟨p', hpp⟩

/-- **A neighbour face meeting the slim set is shared by an end**, given that every point of
`slimSet ∩ ∂M₁` lies in the end set of a shared end. -/
theorem hshare_of_ends_OBDe (R : StageCutRows74 A D) (cov : CutCoverFacts74 A D)
    (hFb : ∀ F : NeighbourFace A.zero A.cusp, neighbourSet F ⊆ frontier (regionM1 A.zero A.cusp))
    (hend : ∀ x ∈ D.slimSet ∩ frontier (regionM1 A.zero A.cusp),
      ∃ e F', R.slimPieces.endKind e = some F' ∧ x ∈ R.slimPieces.endSet e)
    (F : NeighbourFace A.zero A.cusp) (hne : (neighbourSet F ∩ D.slimSet).Nonempty) :
    ∃ e, R.slimPieces.endKind e = some F := by
  obtain ⟨x, hxF, hxS⟩ := hne
  obtain ⟨e, F', hk, hxe⟩ := hend x ⟨hxS, hFb F hxF⟩
  have hset := R.slim.shared_eq e F' hk
  rw [hset] at hxe
  have hFF : F' = F := by
    by_contra h
    exact disjoint_left.1 (neighbourSet_disjoint_OBDe cov h) hxe hxF
  exact ⟨e, hFF ▸ hk⟩

end GC.GraphManifold.Assembly.FC39P0
