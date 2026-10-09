import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Closure.FC39StageFaceStructJN74
import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Closure.FC39GSafeRows
import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Closure.FC39StageJunctions74
import DifferentialGeometry.Topology.Maps.RelativeInteriorRemoval

/-!
# Draft 74, `local_faces`, step 4: the local model of `M₂` at a residual face

Lane S-JUNCTIONS (by S-JUNCTIONS4), G24 part 2 (suffix `_JN74`). On any rows `R` of a stage geometry
with no cusp pieces (`IsEmpty (Fin n)`, the closed route), a residual face `Fl` and a point `x₀` of
it, with `x₀ ∈ M₂` and the removal property `hKR` of the zero faces over `D₃`
(`∂Z_i ∩ f₃⁻¹(D₃) ⊆ relInt_{M₁} f₃⁻¹(D₃)`):

* `exists_faceModel_JN74`: an open `O ∋ x₀` inside the face neighbourhood on which
  `M₂ = {residualFn ≥ 0}` and `{residualFn = 0} = Fl`.

Zero face: the other zero pieces and the slim set are absent near `x₀` (`hKR`),
`int Z = {ratio < 0}` by regularity, and the face is open in `∂Z_i` (components of the boundary
manifold). New end: `hKR` keeps the zero pieces away, the other slim pieces are disjoint, the slim
piece is `{fn ≤ 0}`.
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

/-- The relative interior as an existence of an open set. -/
theorem mem_relInt_iff_exists_open_JN74 {X : Type*} [TopologicalSpace X] {A S : Set X} {x : X} :
    x ∈ relInt A S ↔ x ∈ A ∧ ∃ O : Set X, IsOpen O ∧ x ∈ O ∧ O ∩ A ⊆ S :=
  DifferentialGeometry.Topology.mem_image_interior_preimage_val_iff

/-- `M₂` is closed. -/
theorem isClosed_M₂_JN74 {A : SmoothStageGeometry74 W E} (D : StageCutChoice74 A) :
    IsClosed D.M₂ :=
  isClosed_diff_relInt_GSAFE (isClosed_regionM1_GSAFE A.zero A.cusp) _

/-- The slim set is closed when the slim pieces fill it. -/
theorem isClosed_slimSet_JN74 {A : SmoothStageGeometry74 W E} {D : StageCutChoice74 A}
    (R : StageCutRows74 A D) : IsClosed D.slimSet := by
  rw [← R.slim.union_eq]
  exact isClosed_iUnion_of_finite fun j => (R.slimPieces.piece j).isClosed_range

/-- `M₁` has no cusp part when there are no cusp pieces. -/
theorem regionM1_eq_of_isEmpty_JN74 [IsEmpty (Fin n)] (Z : ZeroDomains W) (C : CuspCores W E) :
    regionM1 Z C = (interior (⋃ i, range (Z.piece i).map))ᶜ := by
  have h : (⋃ b, range (C.piece b).map) = ∅ := iUnion_of_empty _
  unfold regionM1
  rw [h, union_empty]

/-- **The local model of `M₂` at a point of an unshared zero face.** -/
theorem faceModel_zero_JN74 [IsEmpty (Fin n)] {A : SmoothStageGeometry74 W E}
    {D : StageCutChoice74 A} (R : StageCutRows74 A D)
    (hKR : ∀ i, pieceBoundary (A.zero.piece i) ∩ D.slimSet ⊆
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
  have hnosl : x₀ ∉ D.slimSet := fun hs => hM'.2 (hKR i ⟨hbd, hs⟩)
  let Zo : Set W.Carrier := ⋃ j ∈ {j : Fin A.zero.count | j ≠ i}, range (A.zero.piece j).map
  have hZo : IsClosed Zo :=
    (Set.toFinite _).isClosed_biUnion fun j _ => (A.zero.piece j).isClosed_range
  have hnoZo : x₀ ∉ Zo := by
    intro h
    obtain ⟨j, hj, hxj⟩ := mem_iUnion₂.1 h
    obtain ⟨p, -, rfl⟩ := hx₀
    exact disjoint_left.1 (A.zero.disjoint (Ne.symm hj)) ⟨p, rfl⟩ hxj
  obtain ⟨Of, hOf, hOfeq⟩ := exists_open_inter_pieceBoundary_eq_JN74 (A.zero.piece i) Fm
  have hx₀Of : x₀ ∈ Of := (Set.ext_iff.1 hOfeq x₀).2 hx₀ |>.1
  have hnear : x₀ ∈ A.zero.near i := A.zero.zero_subset_near i hr0
  refine ⟨(D.slimSet)ᶜ ∩ Zoᶜ ∩ (A.zero.near i : Set W.Carrier) ∩ Of,
    (((isClosed_slimSet_JN74 R).isOpen_compl.inter hZo.isOpen_compl).inter
      (A.zero.near i).isOpen).inter hOf, ⟨⟨⟨hnosl, hnoZo⟩, hnear⟩, hx₀Of⟩,
    fun x hx => hx.1.2, ?_, ?_⟩
  · intro x hx
    obtain ⟨⟨⟨hxsl, hxZo⟩, hxn⟩, -⟩ := hx
    have hxint : x ∈ W.interior := A.zero.near_interior i hxn
    have hrd : MDifferentiableAt W.model 𝓘(ℝ, ℝ) (A.zero.ratio i) x :=
      ((A.zero.ratio_smooth i) x).mdifferentiableAt (by simp)
    have hxrel : x ∉ relInt (regionM1 A.zero A.cusp) D.slimSet := fun h =>
      hxsl (relInt_subset_JN74 h)
    have hM2 : x ∈ D.M₂ ↔ x ∈ regionM1 A.zero A.cusp := by
      change x ∈ regionM1 A.zero A.cusp \ relInt (regionM1 A.zero A.cusp) D.slimSet ↔ _
      exact ⟨fun h => h.1, fun h => ⟨h, hxrel⟩⟩
    rw [hM2, regionM1_eq_of_isEmpty_JN74]
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
    change x ∈ (interior (⋃ j, range (A.zero.piece j).map))ᶜ ↔ _
    rw [mem_compl_iff, hint, not_lt]
  · intro x hx hr
    obtain ⟨-, hxOf⟩ := hx
    have hxb : x ∈ pieceBoundary (A.zero.piece i) := by
      rw [A.zero.boundary_eq i]
      exact hr
    exact (Set.ext_iff.1 hOfeq x).1 ⟨hxOf, hxb⟩

/-- **The local model of `M₂` at a point of a new slim end.** -/
theorem faceModel_newEnd_JN74 [IsEmpty (Fin n)] {A : SmoothStageGeometry74 W E}
    {D : StageCutChoice74 A} (R : StageCutRows74 A D)
    (hKR : ∀ i, pieceBoundary (A.zero.piece i) ∩ D.slimSet ⊆
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
  have hM' : x₀ ∈ regionM1 A.zero A.cusp \ relInt (regionM1 A.zero A.cusp) D.slimSet := hM
  have hM1 := regionM1_eq_of_isEmpty_JN74 A.zero A.cusp
  have hnoZ : x₀ ∉ ⋃ i, range (A.zero.piece i).map := by
    intro h
    obtain ⟨i, hi⟩ := mem_iUnion.1 h
    have hle : A.zero.ratio i x₀ ≤ 0 := (Set.ext_iff.1 (A.zero.range_eq i) x₀).1 hi
    rcases hle.lt_or_eq with hlt | h0
    · have hM1' : x₀ ∈ (interior (⋃ i, range (A.zero.piece i).map))ᶜ := hM1 ▸ hM'.1
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
      exact hM'.2 (hKR i ⟨hbd, hx₀sl⟩)
  let Sj : Set W.Carrier :=
    ⋃ j ∈ {j : Fin R.slimPieces.count | j ≠ e.1.1.1}, range (R.slimPieces.piece j).map
  have hSj : IsClosed Sj :=
    (Set.toFinite _).isClosed_biUnion fun j _ => (R.slimPieces.piece j).isClosed_range
  have hnoSj : x₀ ∉ Sj := by
    intro h
    obtain ⟨j, hj, hxj⟩ := mem_iUnion₂.1 h
    exact disjoint_left.1 (R.slimPieces.disjoint (Ne.symm hj)) hx₀r hxj
  have hZc : IsClosed (⋃ i, range (A.zero.piece i).map) :=
    isClosed_iUnion_of_finite fun i => (A.zero.piece i).isClosed_range
  refine ⟨(⋃ i, range (A.zero.piece i).map)ᶜ ∩ Sjᶜ ∩ (R.slimPieces.endNear e : Set W.Carrier),
    (hZc.isOpen_compl.inter hSj.isOpen_compl).inter (R.slimPieces.endNear e).isOpen,
    ⟨⟨hnoZ, hnoSj⟩, hxn⟩, fun x hx => hx.2, ?_, ?_⟩
  · intro x hx
    obtain ⟨⟨hxZ, hxSj⟩, hxn'⟩ := hx
    have hxint : x ∈ W.interior := R.slimPieces.endNear_interior e hxn'
    have hxM1 : x ∈ regionM1 A.zero A.cusp := by
      rw [hM1]
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
          (R.slimPieces.endNear e : Set W.Carrier)), ?_,
          hO'.inter ((hZc.isOpen_compl.inter hSj.isOpen_compl).inter
            (R.slimPieces.endNear e).isOpen), ⟨hxO', ⟨hxZ, hxSj⟩, hxn'⟩⟩
        rintro y ⟨hyO', ⟨hyZ, hySj⟩, hyn⟩
        have hyM1 : y ∈ regionM1 A.zero A.cusp := by
          rw [hM1]
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

namespace SlimPiecesV2

variable {Z : ZeroDomains W} {C : CuspCores W E} (S : SlimPiecesV2 W Z C)

/-- **The face functions are regular on their faces.** -/
theorem residualFn_mfderiv_ne_zero_JN74 (Fl : S.ResidualFace) {x : W.Carrier}
    (hx : x ∈ S.residualSet Fl) : mfderiv W.model 𝓘(ℝ, ℝ) (S.residualFn Fl) x ≠ 0 := by
  rcases Fl with ⟨F | F, hF⟩ | e
  · obtain ⟨p, hp, rfl⟩ := hx
    have hb : (Z.piece F.1).map p ∈ pieceBoundary (Z.piece F.1) :=
      ⟨p, F.2.subset hp, rfl⟩
    rw [Z.boundary_eq F.1] at hb
    exact Z.ratio_regular F.1 _ hb
  · obtain ⟨b, F', hF'⟩ := F
    have hn := S.residualSet_subset_residualNear_JN74 (.inl ⟨.inr ⟨b, F', hF'⟩, hF⟩) hx
    subst hF'
    have h0 : C.cuspFn b x = 0 := by
      obtain ⟨p, hp, rfl⟩ := hx
      rw [C.internalModelFace_eq b] at hp
      obtain ⟨t, rfl⟩ := hp
      have h2 : (C.piece b).map (C.product b (t, iccEnd true)) ∈ range fun t =>
          (C.piece b).map (C.product b (t, iccEnd true)) := ⟨t, rfl⟩
      rw [C.internal_eq b] at h2
      exact h2.2
    exact C.fn_regular b x hn h0
  · have hn := S.residualSet_subset_residualNear_JN74 (.inr e) hx
    have h0 : S.endFn e x = 0 := by
      have h := S.endFn_level e
      have hx' : x ∈ (S.piece e.1.1.1).map '' slimModelEnd (S.model e.1.1.1) e.1.1.2 := hx
      rw [h] at hx'
      exact hx'.2
    exact S.endFn_regular e x hn h0

end SlimPiecesV2

/-- **The local model of `M₂` at a point of a residual face** (zero face or new slim end): an open
neighbourhood of the point in the face neighbourhood on which `M₂ = {h_F ≥ 0}` and the zero set of
`h_F` is the face. -/
theorem exists_faceModel_JN74 [IsEmpty (Fin n)] {A : SmoothStageGeometry74 W E}
    {D : StageCutChoice74 A} (R : StageCutRows74 A D) (F : JunctionFaceFacts74 A D R)
    (hKR : ∀ i, pieceBoundary (A.zero.piece i) ∩ D.slimSet ⊆
      relInt (regionM1 A.zero A.cusp) D.slimSet)
    (Fl : R.slimPieces.ResidualFace) {x₀ : W.Carrier} (hx₀ : x₀ ∈ R.slimPieces.residualSet Fl) :
    ∃ O : Set W.Carrier, IsOpen O ∧ x₀ ∈ O ∧ O ⊆ (R.slimPieces.residualNear Fl : Set W.Carrier) ∧
      (∀ x ∈ O, x ∈ D.M₂ ↔ 0 ≤ R.slimPieces.residualFn Fl x) ∧
      ∀ x ∈ O, R.slimPieces.residualFn Fl x = 0 → x ∈ R.slimPieces.residualSet Fl := by
  have hfr : x₀ ∈ frontier D.M₂ := by
    rw [F.frontier_M2]
    exact mem_iUnion.2 ⟨Fl, hx₀⟩
  have hM : x₀ ∈ D.M₂ := (isClosed_M₂_JN74 D).frontier_subset hfr
  rcases Fl with ⟨F' | F', hF'⟩ | e
  · exact faceModel_zero_JN74 R hKR F'.1 F'.2 hx₀ hM
  · obtain ⟨b, -⟩ := F'
    exact (IsEmpty.false b).elim
  · exact faceModel_newEnd_JN74 R hKR e hx₀ hM

end GC.GraphManifold.Assembly.FC39P0
