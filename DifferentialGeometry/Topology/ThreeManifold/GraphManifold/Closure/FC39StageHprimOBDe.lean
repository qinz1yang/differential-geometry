import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Closure.FC39StageCornerDescentLocOBDe
import DifferentialGeometry.Geometry.Collapse.EdgeDisk.CornerTube

/-!
# The sign model `C₂ ∩ U = {b ≥ 0}` of an endpoint from a descended face function

Lane O-BD1 (by S-BD2e), G11f (suffix `_OBDe`). The primitive `hprim` of an endpoint `e` of the edge
base asks for a function `b` of the edge base with `h_F = b ∘ q₁` on an open set around the rim and
`C₂ ∩ U = {b ≥ 0}` near `e`. Given the descended equation on an open `N' ⊇ disk(e)` (the WHOLE disk
over `e`, which lies in the face `F`), the sign model follows from the face model of `M₂` and the
properness of the edge bundle:

* `edge_tube_OBDe`: whole-fibre shrinking for the sublevel `{T ≤ level}` of an edge bundle (the
  restriction of `proj` to the sublevel is a proper map into the locally compact base);
* `exists_cbase_sign_OBDe`: a neighbourhood `V` of `e` with `c ∈ C₂ ↔ 0 ≤ b c` for `c ∈ V`: a point
  `x` of the disk over `c` lies in the face model, where `M₂ = {h_F ≥ 0}`, `x ∈ M^edge ↔ c ∈ C₂`
  and `h_F x = b c`.
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

/-- **Whole-fibre shrinking for the sublevel of an edge bundle**: an open `Ω ⊆ W` containing the
whole disk over `c₀` contains the whole sublevel part of the preimage of a neighbourhood of `c₀`. -/
theorem edge_tube_OBDe (P : EdgeBundle W) {Ω : Set W.Carrier} (hΩ : IsOpen Ω) {c₀ : P.Base}
    (hfib : ∀ x : P.source, P.proj x = c₀ → P.height x ≤ P.level → (x : W.Carrier) ∈ Ω) :
    ∃ V : Set P.Base, IsOpen V ∧ c₀ ∈ V ∧ ∀ x : P.source, P.proj x ∈ V → P.height x ≤ P.level →
      (x : W.Carrier) ∈ Ω := by
  have : LocallyCompactSpace P.Base :=
    ChartedSpace.locallyCompactSpace (EuclideanSpace ℝ (Fin 1)) P.Base
  let Y := {x : P.source // P.height x ≤ P.level}
  let g : Y → W.Carrier := fun y => (y.1 : W.Carrier)
  let f : Y → P.Base := fun y => P.proj y.1
  have hg : Topology.IsInducing g :=
    Topology.IsInducing.subtypeVal.comp Topology.IsInducing.subtypeVal
  have hfc : Continuous f := P.proj.continuous.comp continuous_subtype_val
  have hproper : IsProperMap f := by
    rw [isProperMap_iff_isCompact_preimage]
    refine ⟨hfc, fun K hK => ?_⟩
    rw [hg.isCompact_iff]
    have h := P.proper K hK
    convert h using 1
    ext z
    constructor
    · rintro ⟨y, hy, rfl⟩
      exact ⟨y.1, ⟨hy, y.2⟩, rfl⟩
    · rintro ⟨x, ⟨hx1, hx2⟩, rfl⟩
      exact ⟨⟨x, hx2⟩, hx1, rfl⟩
  obtain ⟨U, hU, hc₀U, -, hUsub⟩ := Geometry.Collapse.EdgeDisk.exists_open_tube_subset_EFC
    hproper.isClosedMap (N := g ⁻¹' Ω) (hΩ.preimage hg.continuous)
    (c₀ := c₀) (fun y hy => hfib y.1 hy y.2) (V := Set.univ) isOpen_univ trivial
  exact ⟨U, hU, hc₀U, fun x hx hT => hUsub (show (⟨x, hT⟩ : Y) ∈ f ⁻¹' U from hx)⟩

namespace StageCutRows74

variable {A : SmoothStageGeometry74 W E} {D : StageCutChoice74 A} {R : StageCutRows74 A D}

/-- **`c ∈ C₂ ↔ 0 ≤ b c` near an endpoint** from the descended face equation on an open set around
the whole disk over the endpoint. -/
theorem exists_cbase_sign_OBDe (F : JunctionFaceFacts74 A D R) (cov : CutCoverFacts74 A D)
    (hKR : ∀ F : NeighbourFace A.zero A.cusp, neighbourSet F ∩ D.slimSet ⊆
      relInt (regionM1 A.zero A.cusp) D.slimSet)
    (hE : ∀ x : R.edge.source, R.edge.height x ≤ R.edge.level →
      (x : W.Carrier) ∈ D.M₂ → (x : W.Carrier) ∈ D.edgeSet)
    (e : R.edge.EdgeEnd) (b : R.edge.Base → ℝ) (N' : Set W.Carrier) (hN' : IsOpen N')
    (hdisk : R.edge.disk e.1 ⊆ N')
    (hNeq : ∀ x ∈ N', ∃ hx : x ∈ R.edge.source,
      R.slimPieces.residualFn (F.horizontal e) x = b (R.edge.proj ⟨x, hx⟩)) :
    ∃ V : Set R.edge.Base, IsOpen V ∧ e.1 ∈ V ∧
      ∀ c ∈ V, (c ∈ R.edge.cbase ↔ 0 ≤ b c) := by
  classical
  have hedge : R.edge.edgePiece = D.edgeSet := D.edgePiece_edgeBundle74 R.edgeFacts
  have hmodel : ∀ x ∈ R.slimPieces.residualSet (F.horizontal e), ∃ O : Set W.Carrier,
      IsOpen O ∧ x ∈ O ∧ O ⊆ (R.slimPieces.residualNear (F.horizontal e) : Set W.Carrier) ∧
      (∀ y ∈ O, y ∈ D.M₂ ↔ 0 ≤ R.slimPieces.residualFn (F.horizontal e) y) ∧
      ∀ y ∈ O, R.slimPieces.residualFn (F.horizontal e) y = 0 →
        y ∈ R.slimPieces.residualSet (F.horizontal e) :=
    fun x hx => exists_faceModel_OBDe R cov F hKR (F.horizontal e) hx
  choose! O hOo hxO hOn hOM hOz using hmodel
  let Ω : Set W.Carrier := N' ∩ ⋃ x ∈ R.edge.disk e.1, O x
  have hΩ : IsOpen Ω :=
    hN'.inter (isOpen_biUnion fun x hx => hOo x (F.horizontal_disk e hx))
  have hfib : ∀ x : R.edge.source, R.edge.proj x = e.1 → R.edge.height x ≤ R.edge.level →
      (x : W.Carrier) ∈ Ω := by
    intro x hx1 hx2
    have hd : (x : W.Carrier) ∈ R.edge.disk e.1 := ⟨x, ⟨hx1, hx2⟩, rfl⟩
    exact ⟨hdisk hd, mem_iUnion₂.2 ⟨x, hd, hxO x (F.horizontal_disk e hd)⟩⟩
  obtain ⟨V, hV, heV, hVsub⟩ := edge_tube_OBDe R.edge hΩ hfib
  refine ⟨V, hV, heV, fun c hc => ?_⟩
  obtain ⟨φ, -, hφ⟩ := R.edge.fibre_disk c
  obtain ⟨x, hx⟩ : ∃ x : R.edge.source, R.edge.proj x = c ∧ R.edge.height x ≤ R.edge.level := by
    have hmem : φ (closedCellCenter 2) ∈ range φ := ⟨_, rfl⟩
    rw [hφ] at hmem
    obtain ⟨x, hx, -⟩ := hmem
    exact ⟨x, hx⟩
  obtain ⟨hx1, hx2⟩ := hx
  have hxΩ : (x : W.Carrier) ∈ Ω := hVsub x (by rw [hx1]; exact hc) hx2
  obtain ⟨hxN', hxU⟩ := hxΩ
  obtain ⟨x', hx'd, hxO'⟩ := mem_iUnion₂.1 hxU
  have hM : (x : W.Carrier) ∈ D.M₂ ↔ 0 ≤ R.slimPieces.residualFn (F.horizontal e) x :=
    hOM x' (F.horizontal_disk e hx'd) x hxO'
  obtain ⟨hxs, hxeq⟩ := hNeq x hxN'
  have hxx : (⟨(x : W.Carrier), hxs⟩ : R.edge.source) = x := Subtype.ext rfl
  rw [hxx, hx1] at hxeq
  have hedgeiff : c ∈ R.edge.cbase ↔ (x : W.Carrier) ∈ D.edgeSet := by
    rw [← hedge]
    constructor
    · intro hcb
      exact ⟨x, ⟨hx1 ▸ hcb, hx2⟩, rfl⟩
    · rintro ⟨z, ⟨hz1, hz2⟩, hzx⟩
      have hzx' : z = x := Subtype.ext hzx
      subst hzx'
      rw [← hx1]
      exact hz1
  rw [hedgeiff]
  constructor
  · intro h
    have h1 := hM.1 (cov.edgeSet_subset_M₂ h)
    rwa [hxeq] at h1
  · intro h0
    exact hE x hx2 (hM.2 (by rw [hxeq]; exact h0))

/-- **The descended face function is regular at the endpoint**: `h_F = b ∘ q₁` on an open set
around the disk over `e` and `d h_F ≠ 0` on the face give `db(e) ≠ 0`. -/
theorem mfderiv_descended_ne_zero_OBDe (F : JunctionFaceFacts74 A D R) (e : R.edge.EdgeEnd)
    (b : R.edge.Base → ℝ) (hbd : MDifferentiableAt (𝓡 1) 𝓘(ℝ, ℝ) b e.1) (N' : Set W.Carrier)
    (hN' : IsOpen N') (hdisk : R.edge.disk e.1 ⊆ N')
    (hNeq : ∀ x ∈ N', ∃ hx : x ∈ R.edge.source,
      R.slimPieces.residualFn (F.horizontal e) x = b (R.edge.proj ⟨x, hx⟩)) :
    mfderiv (𝓡 1) 𝓘(ℝ, ℝ) b e.1 ≠ 0 := by
  classical
  obtain ⟨φ, -, hφ⟩ := R.edge.fibre_disk e.1
  obtain ⟨z, hz1, hz2⟩ : ∃ z : R.edge.source, R.edge.proj z = e.1 ∧
      R.edge.height z ≤ R.edge.level := by
    have hmem : φ (closedCellCenter 2) ∈ range φ := ⟨_, rfl⟩
    rw [hφ] at hmem
    obtain ⟨z, hz, -⟩ := hmem
    exact ⟨z, hz⟩
  have hzd : (z : W.Carrier) ∈ R.edge.disk e.1 := ⟨z, ⟨hz1, hz2⟩, rfl⟩
  have hzF := F.horizontal_disk e hzd
  intro h0
  apply R.slimPieces.residualFn_mfderiv_ne_zero_JN74 (F.horizontal e) hzF
  have hbd' : MDifferentiableAt (𝓡 1) 𝓘(ℝ, ℝ) b (R.edge.proj z) := by
    rw [hz1]
    exact hbd
  have hproj : MDifferentiableAt W.model (𝓡 1) R.edge.proj z :=
    (R.edge.proj_smooth z).mdifferentiableAt (by simp)
  have hev : (fun w : R.edge.source => R.slimPieces.residualFn (F.horizontal e) w) =ᶠ[𝓝 z]
      b ∘ R.edge.proj := by
    filter_upwards [continuous_subtype_val.continuousAt.preimage_mem_nhds
      (hN'.mem_nhds (hdisk hzd))] with w hw
    obtain ⟨hws, hweq⟩ := hNeq w hw
    have hww : (⟨(w : W.Carrier), hws⟩ : R.edge.source) = w := Subtype.ext rfl
    rw [hww] at hweq
    exact hweq
  rw [← mfderiv_restrict_open (I := W.model) (J := 𝓘(ℝ, ℝ))
    (R.slimPieces.residualFn (F.horizontal e)) R.edge.source z, hev.mfderiv_eq,
    mfderiv_comp z hbd' hproj, hz1, h0]
  ext v
  rfl

/-- **The primitive `hprim` of an endpoint from a descended face function**: a function `b` of the
edge base, smooth on a neighbourhood of `e`, with `h_F = b ∘ q₁` on an open set `N'` around
the whole disk over `e` gives the clauses of the endpoint primitive (smooth, regular, sign
model, descended equation near the rim). -/
theorem exists_hprim_of_descended_OBDe (F : JunctionFaceFacts74 A D R) (cov : CutCoverFacts74 A D)
    (hKR : ∀ F : NeighbourFace A.zero A.cusp, neighbourSet F ∩ D.slimSet ⊆
      relInt (regionM1 A.zero A.cusp) D.slimSet)
    (hE : ∀ x : R.edge.source, R.edge.height x ≤ R.edge.level →
      (x : W.Carrier) ∈ D.M₂ → (x : W.Carrier) ∈ D.edgeSet)
    (e : R.edge.EdgeEnd) (b : R.edge.Base → ℝ) (U₀ : TopologicalSpace.Opens R.edge.Base)
    (heU₀ : e.1 ∈ U₀) (hb : ContMDiffOn (𝓡 1) 𝓘(ℝ, ℝ) ∞ b U₀) (N' : Set W.Carrier)
    (hN' : IsOpen N') (hdisk : R.edge.disk e.1 ⊆ N')
    (hNeq : ∀ x ∈ N', ∃ hx : x ∈ R.edge.source,
      R.slimPieces.residualFn (F.horizontal e) x = b (R.edge.proj ⟨x, hx⟩)) :
    ∃ (U : TopologicalSpace.Opens R.edge.Base), e.1 ∈ U ∧
      ContMDiffOn (𝓡 1) 𝓘(ℝ, ℝ) ∞ b U ∧ mfderiv (𝓡 1) 𝓘(ℝ, ℝ) b e.1 ≠ 0 ∧
      R.edge.cbase ∩ U = {c | c ∈ U ∧ 0 ≤ b c} ∧
      ∃ N'' : Set W.Carrier, IsOpen N'' ∧ R.edge.rim e.1 ⊆ N'' ∧ ∀ x ∈ N'',
        ∃ hx : x ∈ R.edge.source,
          R.slimPieces.residualFn (F.horizontal e) x = b (R.edge.proj ⟨x, hx⟩) := by
  obtain ⟨V, hV, heV, hVsign⟩ := exists_cbase_sign_OBDe F cov hKR hE e b N' hN' hdisk hNeq
  refine ⟨⟨V ∩ U₀, hV.inter U₀.isOpen⟩, ⟨heV, heU₀⟩, hb.mono inter_subset_right,
    mfderiv_descended_ne_zero_OBDe F e b
      ((hb.contMDiffAt (U₀.isOpen.mem_nhds heU₀)).mdifferentiableAt (by simp)) N' hN' hdisk hNeq,
    ?_, N', hN', ?_, hNeq⟩
  · ext c
    constructor
    · rintro ⟨hc, hcV, hcU⟩
      exact ⟨⟨hcV, hcU⟩, (hVsign c hcV).1 hc⟩
    · rintro ⟨⟨hcV, hcU⟩, h0⟩
      exact ⟨(hVsign c hcV).2 h0, hcV, hcU⟩
  · rintro x ⟨z, ⟨hz1, hz2⟩, hzx⟩
    exact hdisk ⟨z, ⟨hz1, hz2.le⟩, hzx⟩

end StageCutRows74

end GC.GraphManifold.Assembly.FC39P0
