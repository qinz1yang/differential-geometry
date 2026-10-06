import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Closure.FC39StageFaceModelJN74
import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Closure.AssemblyFC42ClosedPieces
import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.CliffordGluing

/-!
# Cusp-aware local models of `M₂` at a residual face (boundary route)

Lane O-BD1 (by S-BD2e), G11c (suffix `_OBDe`). The closed kit `FC39StageFaceModelJN74`
(`faceModel_zero_JN74`, `faceModel_newEnd_JN74`, `exists_faceModel_JN74`) is stated with
`[IsEmpty (Fin n)]`: it discards the cusp cores. The boundary has cusp cores, so this file proves
the same local models with the cusp cores kept:

* `range_diff_pieceBoundary_subset_interior_OBDe`: a point of an embedded piece that is not on its
  model boundary is an interior point of its range (invariance of domain from the bijective
  differential);
* `mem_regionM1_iff_of_disjoint_OBDe`: away from the cusp cores `M₁ = (int Z)ᶜ`;
* `cusp_range_inter_regionM1_subset_front_OBDe`: a point of a cusp core lying in `M₁` is on the
  front (the internal end): the external end lies in the open collar owned by the core;
* the removal property is stated for the neighbour faces: `hKR : ∀ F, neighbourSet F ∩ slimSet ⊆
  relInt_{M₁} slimSet` (zero model faces and cusp fronts alike);
* `faceModel_zero_OBDe`, `faceModel_newEnd_OBDe`, NEW `faceModel_cusp_OBDe`, and
  `exists_faceModel_OBDe` for every residual face.

No premise besides `hKR` (the removal property, produced at the chain level) and the cover facts
`CutCoverFacts74` (zero domains and cusp cores are disjoint).
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

/-- **A point of an embedded piece off its model boundary is an interior point of its range.** -/
theorem range_diff_pieceBoundary_subset_interior_OBDe (P : PieceEmbedding W) :
    range P.map \ pieceBoundary P ⊆ interior (range P.map) := by
  rintro _ ⟨⟨q, rfl⟩, hb⟩
  have hq : (𝓡∂ 3).IsInteriorPoint q := by
    rcases (𝓡∂ 3).isInteriorPoint_or_isBoundaryPoint q with h | h
    · exact h
    · exact absurd ⟨q, (show q ∈ (𝓡∂ 3).boundary P.Piece from h), rfl⟩ hb
  have hdim : Module.finrank ℝ (EuclideanSpace ℝ (Fin 3)) =
      Module.finrank ℝ (EuclideanSpace ℝ (Fin 3)) := rfl
  have hn := GC.Seifert.image_mem_nhds_of_mfderiv_injective P.smooth hq (P.isInteriorPoint_map hq)
    (P.mfderiv_bijective q).1 hdim Filter.univ_mem
  rw [image_univ] at hn
  exact mem_interior_iff_mem_nhds.2 hn

/-- **Away from the cusp cores, `M₁` is the complement of the interior of the zero domains.** -/
theorem mem_regionM1_iff_of_disjoint_OBDe {Z : ZeroDomains W} {C : CuspCores W E}
    {O : Set W.Carrier} (hO : IsOpen O) (hOC : Disjoint O (⋃ b, range (C.piece b).map))
    {x : W.Carrier} (hx : x ∈ O) :
    x ∈ regionM1 Z C ↔ x ∉ interior (⋃ i, range (Z.piece i).map) := by
  unfold regionM1
  rw [mem_compl_iff, not_iff_not]
  constructor
  · intro h
    rw [mem_interior] at h ⊢
    obtain ⟨V, hV, hVo, hxV⟩ := h
    refine ⟨V ∩ O, ?_, hVo.inter hO, hxV, hx⟩
    rintro y ⟨hyV, hyO⟩
    rcases hV hyV with hz | hc
    · exact hz
    · exact absurd hc (disjoint_left.1 hOC hyO)
  · exact fun h => interior_mono subset_union_left h

/-- The internal face (front) of the cusp core `b` as a neighbour face. -/
def cuspFrontFace_OBDe (Z : ZeroDomains W) (C : CuspCores W E) (b : Fin n) :
    NeighbourFace Z C :=
  .inr ⟨b, ⟨C.internalModelFace b, rfl⟩⟩

/-- The front of the cusp core `b`. -/
def cuspFront_OBDe (C : CuspCores W E) (b : Fin n) : Set W.Carrier :=
  range fun t => (C.piece b).map (C.product b (t, iccEnd true))

theorem neighbourSet_cuspFrontFace_OBDe (Z : ZeroDomains W) (C : CuspCores W E) (b : Fin n) :
    neighbourSet (cuspFrontFace_OBDe Z C b) = cuspFront_OBDe C b := by
  change (C.piece b).map '' (C.internalModelFace b).1 = _
  rw [C.internalModelFace_eq b, ← range_comp]
  rfl

/-- **A point of a cusp core that lies in `M₁` is on its front.** -/
theorem cusp_range_inter_regionM1_subset_front_OBDe (Z : ZeroDomains W) (C : CuspCores W E)
    (b : Fin n) {x : W.Carrier} (hxr : x ∈ range (C.piece b).map) (hM : x ∈ regionM1 Z C) :
    x ∈ cuspFront_OBDe C b := by
  by_contra hfront
  apply hM
  have hsub : range (C.piece b).map ⊆ (⋃ i, range (Z.piece i).map) ∪ ⋃ b', range (C.piece b').map :=
    fun y hy => Or.inr (mem_iUnion.2 ⟨b, hy⟩)
  refine interior_mono hsub ?_
  by_cases hbd : x ∈ pieceBoundary (C.piece b)
  · obtain ⟨q, hq, rfl⟩ := hbd
    let Fm : ModelBoundaryFace (C.piece b) :=
      ActualComponent.of (S := (𝓡∂ 3).boundary (C.piece b).Piece) hq
    have hmem : q ∈ Fm.1 := mem_connectedComponentIn hq
    rcases C.modelFace_cases b Fm with h | h
    · rw [h, C.internalModelFace_eq b] at hmem
      obtain ⟨t, rfl⟩ := hmem
      exact absurd ⟨t, rfl⟩ hfront
    · rw [h, C.externalModelFace_eq b] at hmem
      obtain ⟨t, rfl⟩ := hmem
      rw [C.external_end b t]
      have hsrc : (t, halfZero) ∈ (E.collar b).source := by
        rw [E.source_eq b]
        exact halfZero_mem_halfCollarSource t
      exact interior_maximal (C.collar_owned b) (E.collar b).open_target
        ((E.collar b).map_source hsrc)
  · exact range_diff_pieceBoundary_subset_interior_OBDe (C.piece b) ⟨hxr, hbd⟩

/-- A zero model face is a neighbour face. -/
theorem neighbourSet_zeroFace_OBDe (Z : ZeroDomains W) (C : CuspCores W E) (i : Fin Z.count)
    (Fm : ModelBoundaryFace (Z.piece i)) :
    neighbourSet (.inl ⟨i, Fm⟩ : NeighbourFace Z C) = (Z.piece i).map '' Fm.1 :=
  rfl

/-- The model boundary face of a boundary point of a zero piece through that point. -/
theorem exists_zeroFace_of_pieceBoundary_OBDe (Z : ZeroDomains W) (i : Fin Z.count)
    {x : W.Carrier} (hx : x ∈ pieceBoundary (Z.piece i)) :
    ∃ Fm : ModelBoundaryFace (Z.piece i), x ∈ (Z.piece i).map '' Fm.1 := by
  obtain ⟨q, hq, rfl⟩ := hx
  exact ⟨ActualComponent.of (S := (𝓡∂ 3).boundary (Z.piece i).Piece) hq, q,
    mem_connectedComponentIn hq, rfl⟩

section FaceModels

variable {A : SmoothStageGeometry74 W E} {D : StageCutChoice74 A}

/-- The union of the cusp core ranges is closed. -/
theorem isClosed_cuspUnion_OBDe (C : CuspCores W E) :
    IsClosed (⋃ b, range (C.piece b).map) :=
  isClosed_iUnion_of_finite fun b => (C.piece b).isClosed_range

/-- The union of the zero domain ranges is closed. -/
theorem isClosed_zeroUnion_OBDe (Z : ZeroDomains W) :
    IsClosed (⋃ i, range (Z.piece i).map) :=
  isClosed_iUnion_of_finite fun i => (Z.piece i).isClosed_range

/-- **The local model of `M₂` at a point of an unshared zero face** (cusp cores kept). -/
theorem faceModel_zero_OBDe (R : StageCutRows74 A D) (cov : CutCoverFacts74 A D)
    (hKR : ∀ F : NeighbourFace A.zero A.cusp, neighbourSet F ∩ D.slimSet ⊆
      relInt (regionM1 A.zero A.cusp) D.slimSet)
    (i : Fin A.zero.count) (Fm : ModelBoundaryFace (A.zero.piece i)) {x₀ : W.Carrier}
    (hx₀ : x₀ ∈ (A.zero.piece i).map '' Fm.1) (hM : x₀ ∈ D.M₂) :
    ∃ O : Set W.Carrier, IsOpen O ∧ x₀ ∈ O ∧ O ⊆ A.zero.near i ∧
      (∀ x ∈ O, x ∈ D.M₂ ↔ 0 ≤ A.zero.ratio i x) ∧
      ∀ x ∈ O, A.zero.ratio i x = 0 → x ∈ (A.zero.piece i).map '' Fm.1 := by
  classical
  have hbd : x₀ ∈ pieceBoundary (A.zero.piece i) := by
    obtain ⟨p, hp, rfl⟩ := hx₀
    refine ⟨p, ?_, rfl⟩
    obtain ⟨x, -, hm⟩ := Fm.2
    rw [hm] at hp
    exact connectedComponentIn_subset _ _ hp
  have hr0 : A.zero.ratio i x₀ = 0 := by
    have h := A.zero.boundary_eq i
    rw [h] at hbd
    exact hbd
  have hM' : x₀ ∈ regionM1 A.zero A.cusp \ relInt (regionM1 A.zero A.cusp) D.slimSet := hM
  have hnosl : x₀ ∉ D.slimSet := fun hs =>
    hM'.2 (hKR (.inl ⟨i, Fm⟩) ⟨hx₀, hs⟩)
  let Zo : Set W.Carrier := ⋃ j ∈ {j : Fin A.zero.count | j ≠ i}, range (A.zero.piece j).map
  have hZo : IsClosed Zo :=
    (Set.toFinite _).isClosed_biUnion fun j _ => (A.zero.piece j).isClosed_range
  have hnoZo : x₀ ∉ Zo := by
    intro h
    obtain ⟨j, hj, hxj⟩ := mem_iUnion₂.1 h
    obtain ⟨p, -, rfl⟩ := hx₀
    exact disjoint_left.1 (A.zero.disjoint (Ne.symm hj)) ⟨p, rfl⟩ hxj
  have hCc : IsClosed (⋃ b, range (A.cusp.piece b).map) := isClosed_cuspUnion_OBDe A.cusp
  have hnoC : x₀ ∉ ⋃ b, range (A.cusp.piece b).map := by
    intro h
    obtain ⟨b, hb⟩ := mem_iUnion.1 h
    obtain ⟨p, -, rfl⟩ := hx₀
    exact disjoint_left.1 (cov.zero_cusp_disjoint i b) ⟨p, rfl⟩ hb
  obtain ⟨Of, hOf, hOfeq⟩ := exists_open_inter_pieceBoundary_eq_JN74 (A.zero.piece i) Fm
  have hx₀Of : x₀ ∈ Of := (Set.ext_iff.1 hOfeq x₀).2 hx₀ |>.1
  have hnear : x₀ ∈ A.zero.near i := A.zero.zero_subset_near i hr0
  refine ⟨(D.slimSet)ᶜ ∩ Zoᶜ ∩ (⋃ b, range (A.cusp.piece b).map)ᶜ ∩
      (A.zero.near i : Set W.Carrier) ∩ Of,
    ((((isClosed_slimSet_JN74 R).isOpen_compl.inter hZo.isOpen_compl).inter
      hCc.isOpen_compl).inter (A.zero.near i).isOpen).inter hOf,
    ⟨⟨⟨⟨hnosl, hnoZo⟩, hnoC⟩, hnear⟩, hx₀Of⟩, fun x hx => hx.1.2, ?_, ?_⟩
  · intro x hx
    obtain ⟨⟨⟨⟨hxsl, hxZo⟩, hxC⟩, hxn⟩, -⟩ := hx
    have hxint : x ∈ W.interior := A.zero.near_interior i hxn
    have hrd : MDifferentiableAt W.model 𝓘(ℝ, ℝ) (A.zero.ratio i) x :=
      ((A.zero.ratio_smooth i) x).mdifferentiableAt (by simp)
    have hxrel : x ∉ relInt (regionM1 A.zero A.cusp) D.slimSet := fun h =>
      hxsl (relInt_subset_JN74 h)
    have hM2 : x ∈ D.M₂ ↔ x ∈ regionM1 A.zero A.cusp := by
      change x ∈ regionM1 A.zero A.cusp \ relInt (regionM1 A.zero A.cusp) D.slimSet ↔ _
      exact ⟨fun h => h.1, fun h => ⟨h, hxrel⟩⟩
    have hint : x ∈ interior (⋃ j, range (A.zero.piece j).map) ↔ A.zero.ratio i x < 0 := by
      constructor
      · intro h
        refine lt_of_mem_interior_sublevel_JN74 hxint hrd
          (fun h0 => A.zero.ratio_regular i x h0) ?_
        refine mem_interior.2 ⟨interior (⋃ j, range (A.zero.piece j).map) ∩ Zoᶜ,
          ?_, isOpen_interior.inter hZo.isOpen_compl, ⟨h, hxZo⟩⟩
        rintro y ⟨hyI, hyZ⟩
        obtain ⟨j, hj⟩ := mem_iUnion.1 (interior_subset hyI)
        by_cases hji : j = i
        · subst hji
          have := (Set.ext_iff.1 (A.zero.range_eq j) y).1 hj
          exact this
        · exact absurd (mem_iUnion₂.2 ⟨j, hji, hj⟩) hyZ
      · intro h
        refine mem_interior.2 ⟨{y | A.zero.ratio i y < 0}, ?_,
          isOpen_lt (A.zero.ratio_smooth i).continuous continuous_const, h⟩
        intro y hy
        refine mem_iUnion.2 ⟨i, ?_⟩
        rw [A.zero.range_eq i]
        exact (show A.zero.ratio i y < 0 from hy).le
    rw [hM2, mem_regionM1_iff_of_disjoint_OBDe (Z := A.zero) (C := A.cusp) hCc.isOpen_compl
      disjoint_compl_left hxC, hint, not_lt]
  · intro x hx hr
    obtain ⟨-, hxOf⟩ := hx
    have hxb : x ∈ pieceBoundary (A.zero.piece i) := by
      rw [A.zero.boundary_eq i]
      exact hr
    exact (Set.ext_iff.1 hOfeq x).1 ⟨hxOf, hxb⟩

/-- **A point of a cusp core, in `M₂`, is not in the cusp front's neighbouring slim set**, and no
point of `M₂ ∩ slimSet` lies in a cusp core. -/
theorem not_mem_cusp_of_slim_regionM2_OBDe (hKR : ∀ F : NeighbourFace A.zero A.cusp,
      neighbourSet F ∩ D.slimSet ⊆ relInt (regionM1 A.zero A.cusp) D.slimSet)
    {x₀ : W.Carrier} (hsl : x₀ ∈ D.slimSet) (hM : x₀ ∈ D.M₂) :
    x₀ ∉ ⋃ b, range (A.cusp.piece b).map := by
  intro h
  obtain ⟨b, hb⟩ := mem_iUnion.1 h
  have hM' : x₀ ∈ regionM1 A.zero A.cusp \ relInt (regionM1 A.zero A.cusp) D.slimSet := hM
  have hf := cusp_range_inter_regionM1_subset_front_OBDe A.zero A.cusp b hb hM'.1
  rw [← neighbourSet_cuspFrontFace_OBDe A.zero A.cusp b] at hf
  exact hM'.2 (hKR _ ⟨hf, hsl⟩)

/-- **A point of a zero domain that is in `M₂` and in the slim set is not possible** (zero
faces): the removal property in the form used for new ends. -/
theorem not_mem_zero_of_slim_regionM2_OBDe (hKR : ∀ F : NeighbourFace A.zero A.cusp,
      neighbourSet F ∩ D.slimSet ⊆ relInt (regionM1 A.zero A.cusp) D.slimSet)
    {x₀ : W.Carrier} (hsl : x₀ ∈ D.slimSet) (hM : x₀ ∈ D.M₂)
    (hC : x₀ ∉ ⋃ b, range (A.cusp.piece b).map) :
    x₀ ∉ ⋃ i, range (A.zero.piece i).map := by
  intro h
  obtain ⟨i, hi⟩ := mem_iUnion.1 h
  have hM' : x₀ ∈ regionM1 A.zero A.cusp \ relInt (regionM1 A.zero A.cusp) D.slimSet := hM
  have hle : A.zero.ratio i x₀ ≤ 0 := (Set.ext_iff.1 (A.zero.range_eq i) x₀).1 hi
  rcases hle.lt_or_eq with hlt | h0
  · have hM1' := (mem_regionM1_iff_of_disjoint_OBDe (Z := A.zero) (C := A.cusp)
      (isClosed_cuspUnion_OBDe A.cusp).isOpen_compl disjoint_compl_left hC).1 hM'.1
    apply hM1'
    refine mem_interior.2 ⟨{y | A.zero.ratio i y < 0}, ?_,
      isOpen_lt (A.zero.ratio_smooth i).continuous continuous_const, hlt⟩
    intro y hy
    refine mem_iUnion.2 ⟨i, ?_⟩
    rw [A.zero.range_eq i]
    exact (show A.zero.ratio i y < 0 from hy).le
  · have hbd : x₀ ∈ pieceBoundary (A.zero.piece i) := by
      rw [A.zero.boundary_eq i]
      exact h0
    obtain ⟨Fm, hFm⟩ := exists_zeroFace_of_pieceBoundary_OBDe A.zero i hbd
    exact hM'.2 (hKR (.inl ⟨i, Fm⟩) ⟨hFm, hsl⟩)

/-- **The local model of `M₂` at a point of a new slim end** (cusp cores kept). -/
theorem faceModel_newEnd_OBDe (R : StageCutRows74 A D)
    (hKR : ∀ F : NeighbourFace A.zero A.cusp, neighbourSet F ∩ D.slimSet ⊆
      relInt (regionM1 A.zero A.cusp) D.slimSet)
    (e : R.slimPieces.NewEnd) {x₀ : W.Carrier} (hx₀ : x₀ ∈ R.slimPieces.endSet e.1)
    (hM : x₀ ∈ D.M₂) :
    ∃ O : Set W.Carrier, IsOpen O ∧ x₀ ∈ O ∧ O ⊆ (R.slimPieces.endNear e : Set W.Carrier) ∧
      (∀ x ∈ O, x ∈ D.M₂ ↔ 0 ≤ R.slimPieces.endFn e x) ∧
      ∀ x ∈ O, R.slimPieces.endFn e x = 0 → x ∈ R.slimPieces.endSet e.1 := by
  classical
  have hlevel : R.slimPieces.endSet e.1 =
      {x | x ∈ R.slimPieces.endNear e ∧ R.slimPieces.endFn e x = 0} :=
    R.slimPieces.endFn_level e
  have hxn : x₀ ∈ R.slimPieces.endNear e := by
    have h' : x₀ ∈ {x | x ∈ R.slimPieces.endNear e ∧ R.slimPieces.endFn e x = 0} := hlevel ▸ hx₀
    exact h'.1
  have hx₀r : x₀ ∈ range (R.slimPieces.piece e.1.1.1).map := by
    obtain ⟨p, -, rfl⟩ := hx₀
    exact ⟨p, rfl⟩
  have hunion : R.slimPieces.union = D.slimSet := R.slim.union_eq
  have hx₀sl : x₀ ∈ D.slimSet := by
    rw [← hunion]
    exact mem_iUnion.2 ⟨e.1.1.1, hx₀r⟩
  have hCc := isClosed_cuspUnion_OBDe A.cusp
  have hnoC : x₀ ∉ ⋃ b, range (A.cusp.piece b).map :=
    not_mem_cusp_of_slim_regionM2_OBDe hKR hx₀sl hM
  have hnoZ : x₀ ∉ ⋃ i, range (A.zero.piece i).map :=
    not_mem_zero_of_slim_regionM2_OBDe hKR hx₀sl hM hnoC
  have hM1 : ∀ x ∈ (⋃ b, range (A.cusp.piece b).map)ᶜ,
      x ∈ regionM1 A.zero A.cusp ↔ x ∉ interior (⋃ i, range (A.zero.piece i).map) :=
    fun x hx => mem_regionM1_iff_of_disjoint_OBDe (Z := A.zero) (C := A.cusp) hCc.isOpen_compl
      disjoint_compl_left hx
  let Sj : Set W.Carrier :=
    ⋃ j ∈ {j : Fin R.slimPieces.count | j ≠ e.1.1.1}, range (R.slimPieces.piece j).map
  have hSj : IsClosed Sj :=
    (Set.toFinite _).isClosed_biUnion fun j _ => (R.slimPieces.piece j).isClosed_range
  have hnoSj : x₀ ∉ Sj := by
    intro h
    obtain ⟨j, hj, hxj⟩ := mem_iUnion₂.1 h
    exact disjoint_left.1 (R.slimPieces.disjoint (Ne.symm hj)) hx₀r hxj
  have hZc : IsClosed (⋃ i, range (A.zero.piece i).map) := isClosed_zeroUnion_OBDe A.zero
  refine ⟨(⋃ i, range (A.zero.piece i).map)ᶜ ∩ Sjᶜ ∩ (⋃ b, range (A.cusp.piece b).map)ᶜ ∩
      (R.slimPieces.endNear e : Set W.Carrier),
    ((hZc.isOpen_compl.inter hSj.isOpen_compl).inter hCc.isOpen_compl).inter
      (R.slimPieces.endNear e).isOpen,
    ⟨⟨⟨hnoZ, hnoSj⟩, hnoC⟩, hxn⟩, fun x hx => hx.2, ?_, ?_⟩
  · intro x hx
    obtain ⟨⟨⟨hxZ, hxSj⟩, hxC⟩, hxn'⟩ := hx
    have hxint : x ∈ W.interior := R.slimPieces.endNear_interior e hxn'
    have hxM1 : x ∈ regionM1 A.zero A.cusp := by
      rw [hM1 x hxC]
      intro hc
      exact hxZ (interior_subset hc)
    have hrel : x ∈ relInt (regionM1 A.zero A.cusp) D.slimSet ↔ R.slimPieces.endFn e x < 0 := by
      constructor
      · intro h
        obtain ⟨-, O', hO', hxO', hO'S⟩ := mem_relInt_iff_exists_open_JN74.1 h
        refine lt_of_mem_interior_sublevel_JN74 hxint
          (((R.slimPieces.endFn_smooth e).contMDiffAt
            ((R.slimPieces.endNear e).isOpen.mem_nhds hxn')).mdifferentiableAt (by simp))
          (fun h0 => R.slimPieces.endFn_regular e x hxn' h0) ?_
        refine mem_interior.2 ⟨O' ∩ ((⋃ i, range (A.zero.piece i).map)ᶜ ∩ Sjᶜ ∩
          (⋃ b, range (A.cusp.piece b).map)ᶜ ∩ (R.slimPieces.endNear e : Set W.Carrier)), ?_,
          hO'.inter (((hZc.isOpen_compl.inter hSj.isOpen_compl).inter hCc.isOpen_compl).inter
            (R.slimPieces.endNear e).isOpen), ⟨hxO', ⟨⟨⟨hxZ, hxSj⟩, hxC⟩, hxn'⟩⟩⟩
        rintro y ⟨hyO', ⟨⟨hyZ, hySj⟩, hyC⟩, hyn⟩
        have hyM1 : y ∈ regionM1 A.zero A.cusp := by
          rw [hM1 y hyC]
          intro hc
          exact hyZ (interior_subset hc)
        have hysl : y ∈ D.slimSet := hO'S ⟨hyO', hyM1⟩
        rw [← hunion] at hysl
        obtain ⟨j, hj⟩ := mem_iUnion.1 hysl
        have hjj : j = e.1.1.1 := by
          by_contra hne
          exact hySj (mem_iUnion₂.2 ⟨j, hne, hj⟩)
        subst hjj
        have := (Set.ext_iff.1 (R.slimPieces.endFn_eq e) y).1 ⟨hj, hyn⟩
        exact this.2
      · intro hlt
        refine mem_relInt_iff_exists_open_JN74.2 ⟨hxM1, ?_⟩
        refine ⟨(R.slimPieces.endNear e : Set W.Carrier) ∩ R.slimPieces.endFn e ⁻¹' Iio 0,
          (R.slimPieces.endFn_smooth e).continuousOn.isOpen_inter_preimage
            (R.slimPieces.endNear e).isOpen isOpen_Iio, ⟨hxn', hlt⟩, ?_⟩
        · rintro y ⟨⟨hy2, hy1⟩, -⟩
          have := (Set.ext_iff.1 (R.slimPieces.endFn_eq e) y).2
            ⟨hy2, le_of_lt (show R.slimPieces.endFn e y < 0 from hy1)⟩
          rw [← hunion]
          exact mem_iUnion.2 ⟨e.1.1.1, this.1⟩
    have hM2 : x ∈ D.M₂ ↔ x ∉ relInt (regionM1 A.zero A.cusp) D.slimSet := by
      change x ∈ regionM1 A.zero A.cusp \ relInt (regionM1 A.zero A.cusp) D.slimSet ↔ _
      exact ⟨fun h => h.2, fun h => ⟨hxM1, h⟩⟩
    rw [hM2, hrel, not_lt]
  · intro x hx h0
    rw [hlevel]
    exact ⟨hx.2, h0⟩

end FaceModels

end GC.GraphManifold.Assembly.FC39P0
