import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Closure.FC39StageCornerRankPrimJN74
import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Closure.FC39StageFaceDisjointJN74
import DifferentialGeometry.Topology.Manifold.LinearChartMaps74

/-!
# Draft 74, the endpoint primitives `hprim` from the face equation (W level)

Lane S-JUNCTIONS (by S-JUNCTIONS5), G32 (suffix `_JN74`). On any rows without cusp pieces:

* `exists_edge_tube_JN74`: a neighbourhood of an endpoint `c` of the edge base such that the
  whole disks over it lie in a given open set containing the disk over `c` (properness);
* `label_eq_of_disk_JN74`: two residual faces containing the same (nonempty) end disk are equal;
* `mfderiv_ne_zero_of_eq_JN74`: if the face function of the label is `b ∘ q₁` near the end disk
  (`b` smooth near the endpoint) then `db(c) ≠ 0` (the face function is regular on the face);
* `hprim_of_eq_JN74`: the whole EDP05 primitives at an endpoint (b smooth on `U ∋ e`, `db(e) ≠ 0`,
  `C₂ ∩ U = {b ≥ 0}`, `h_F = b ∘ q₁` on an open set containing the rim): from the equation
  `h_F = b ∘ q₁` on the face neighbourhood, the face model `exists_faceModel_JN74`, and
  `c ∈ C₂ ↔ the disk over c meets M₂` (`hCM`).
-/

set_option autoImplicit false

noncomputable section

open Set Function Filter
open DifferentialGeometry DifferentialGeometry.Topology GC.Endpoint GC.Seifert GC.GraphManifold
open Manifold
open scoped Manifold ContDiff Topology

universe u

namespace GC.GraphManifold.Assembly.FC39P0

variable {W : CompactCarrier.{u}}

/-- **Tube lemma for the edge bundle**: if the disk over `c` lies in an open set `Ω`, so do the
disks over a neighbourhood of `c` (`EdgeBundle.proper`). -/
theorem exists_edge_tube_JN74 (P : EdgeBundle W) {Ω : Set W.Carrier} (hΩ : IsOpen Ω)
    {c : P.Base} (hc : P.disk c ⊆ Ω) :
    ∃ V : TopologicalSpace.Opens P.Base, c ∈ V ∧ ∀ c' ∈ V, P.disk c' ⊆ Ω := by
  have : LocallyCompactSpace P.Base :=
    ChartedSpace.locallyCompactSpace (EuclideanSpace ℝ (Fin 1)) P.Base
  obtain ⟨K₀, hK₀, hK₀c⟩ := exists_compact_mem_nhds c
  have hZ := P.proper K₀ hK₀
  have hZ' : IsCompact (Subtype.val '' {x : P.source | P.proj x ∈ K₀ ∧ P.height x ≤ P.level} \ Ω) :=
    hZ.diff hΩ
  let Zs : Set P.source := {x | (x : W.Carrier) ∈
    Subtype.val '' {x : P.source | P.proj x ∈ K₀ ∧ P.height x ≤ P.level} \ Ω}
  have hZs : IsCompact Zs := by
    have hemb : Topology.IsEmbedding (Subtype.val : P.source → W.Carrier) :=
      Topology.IsEmbedding.subtypeVal
    refine hemb.isCompact_iff.2 ?_
    have : Subtype.val '' Zs = Subtype.val '' {x : P.source | P.proj x ∈ K₀ ∧
        P.height x ≤ P.level} \ Ω := by
      ext z
      constructor
      · rintro ⟨x, hx, rfl⟩
        exact hx
      · intro hz
        obtain ⟨x, hx, rfl⟩ := hz.1
        exact ⟨x, hz, rfl⟩
    rw [this]
    exact hZ'
  have hY : IsClosed (P.proj '' Zs) := (hZs.image P.proj.continuous).isClosed
  refine ⟨⟨interior K₀ \ P.proj '' Zs, isOpen_interior.sdiff hY⟩,
    ⟨mem_interior_iff_mem_nhds.2 hK₀c, ?_⟩, ?_⟩
  · rintro ⟨x, hx, hxc⟩
    obtain ⟨y, ⟨-, hyh⟩, hyx⟩ := hx.1
    have hyx' : y = x := Subtype.ext hyx
    subst hyx'
    exact hx.2 (hc ⟨y, ⟨hxc, hyh⟩, rfl⟩)
  · rintro c' ⟨hc'K, hc'Y⟩ z ⟨x, ⟨hxc, hxh⟩, rfl⟩
    by_contra hzΩ
    have hxK : P.proj x ∈ K₀ := by
      rw [hxc]
      exact interior_subset hc'K
    exact hc'Y ⟨x, ⟨⟨x, ⟨hxK, hxh⟩, rfl⟩, hzΩ⟩, hxc⟩

variable {n : ℕ} {E : BoundaryTori W n} {A : SmoothStageGeometry74 W E} {D : StageCutChoice74 A}
  (R : StageCutRows74 A D)

namespace StageCutRows74

open DifferentialGeometry.Topology.Handle in
/-- **Every end disk is nonempty**. -/
theorem disk_nonempty_JN74 (c : R.edge.Base) : (R.edge.disk c).Nonempty := by
  obtain ⟨φ, -, hφ⟩ := R.edge.fibre_disk c
  exact ⟨φ ⟨0, by simp⟩, hφ ▸ mem_range_self _⟩

/-- **Two residual faces containing the same end disk are equal**. -/
theorem label_eq_of_disk_JN74 [IsEmpty (Fin n)]
    (hKR : ∀ i, pieceBoundary (A.zero.piece i) ∩ D.slimSet ⊆
      relInt (regionM1 A.zero A.cusp) D.slimSet)
    (hNew : ∀ e : R.slimPieces.NewEnd, R.slimPieces.endSet e.1 ⊆ D.M₂) (c : R.edge.Base)
    {F₁ F₂ : R.slimPieces.ResidualFace} (h₁ : R.edge.disk c ⊆ R.slimPieces.residualSet F₁)
    (h₂ : R.edge.disk c ⊆ R.slimPieces.residualSet F₂) : F₁ = F₂ := by
  by_contra hne
  obtain ⟨z, hz⟩ := R.disk_nonempty_JN74 c
  exact disjoint_left.1 (residualSet_disjoint_JN74 R hKR hNew hne) (h₁ hz) (h₂ hz)

/-- **The differential of the descended face equation is nonzero at the endpoint**: if the face
function of the label `Fl` containing the disk over `e` equals `b ∘ q₁` near the disk, with `b`
smooth near `e`, then `db(e) ≠ 0`. -/
theorem mfderiv_ne_zero_of_eq_JN74 (e : R.edge.EdgeEnd) (Fl : R.slimPieces.ResidualFace)
    (hdisk : R.edge.disk e.1 ⊆ R.slimPieces.residualSet Fl) (b : R.edge.Base → ℝ)
    (U₀ : TopologicalSpace.Opens R.edge.Base) (heU₀ : e.1 ∈ U₀)
    (hb : ContMDiffOn (𝓡 1) 𝓘(ℝ, ℝ) ∞ b U₀)
    (hEq : ∀ x (hx : x ∈ R.edge.source), x ∈ (R.slimPieces.residualNear Fl : Set W.Carrier) →
      R.slimPieces.residualFn Fl x = b (R.edge.proj ⟨x, hx⟩)) :
    mfderiv (𝓡 1) 𝓘(ℝ, ℝ) b e.1 ≠ 0 := by
  intro h0
  obtain ⟨x₀, hx₀⟩ := R.disk_nonempty_JN74 e.1
  have hmem := hdisk hx₀
  obtain ⟨z, ⟨hzc, -⟩, rfl⟩ := hx₀
  have hreg := R.slimPieces.residualFn_mfderiv_ne_zero_JN74 Fl hmem
  have hF : MDifferentiableAt W.model 𝓘(ℝ, ℝ) (R.slimPieces.residualFn Fl) (z : W.Carrier) := by
    by_contra hn
    exact hreg (mfderiv_zero_of_not_mdifferentiableAt hn)
  have hnear : (z : W.Carrier) ∈ (R.slimPieces.residualNear Fl : Set W.Carrier) :=
    R.slimPieces.residualSet_subset_residualNear_JN74 Fl hmem
  have hev : (fun w : R.edge.source => R.slimPieces.residualFn Fl w.1) =ᶠ[nhds z]
      fun w => b (R.edge.proj w) := by
    have hopen : IsOpen {w : R.edge.source |
        (w.1 : W.Carrier) ∈ (R.slimPieces.residualNear Fl : Set W.Carrier)} :=
      (R.slimPieces.residualNear Fl).isOpen.preimage continuous_subtype_val
    filter_upwards [hopen.mem_nhds hnear] with w hw using hEq w.1 w.2 hw
  have hg1 : mfderiv W.model 𝓘(ℝ, ℝ) (fun w : R.edge.source => R.slimPieces.residualFn Fl w.1) z =
      mfderiv W.model 𝓘(ℝ, ℝ) (R.slimPieces.residualFn Fl) (z : W.Carrier) :=
    DifferentialGeometry.Topology.Manifold.mfderiv_comp_subtype_val_R74 R.edge.source
      (fun _ => rfl) z hF
  have hbd : MDifferentiableAt (𝓡 1) 𝓘(ℝ, ℝ) b (R.edge.proj z) :=
    (hb.contMDiffAt (U₀.isOpen.mem_nhds (by rw [hzc]; exact heU₀))).mdifferentiableAt (by simp)
  have hpd : MDifferentiableAt W.model (𝓡 1) R.edge.proj z :=
    (R.edge.proj_smooth z).mdifferentiableAt (by simp)
  have hg2 := mfderiv_comp z hbd hpd
  have h0' : mfderiv (𝓡 1) 𝓘(ℝ, ℝ) b (R.edge.proj z) = 0 := by
    rw [hzc]
    exact h0
  apply hreg
  rw [← hg1, hev.mfderiv_eq]
  change mfderiv W.model 𝓘(ℝ, ℝ) (b ∘ R.edge.proj) z = 0
  rw [hg2, h0']
  exact ContinuousLinearMap.zero_comp _

/-- **The EDP05 endpoint primitives from the face equation** (see the module docstring): the face
function of the label equals `b ∘ q₁` on the face neighbourhood, `b` is smooth near `e`, and a base
point lies in `C₂` iff its disk meets `M₂`. -/
theorem hprim_of_eq_JN74 [IsEmpty (Fin n)] (F : JunctionFaceFacts74 A D R)
    (hKR : ∀ i, pieceBoundary (A.zero.piece i) ∩ D.slimSet ⊆
      relInt (regionM1 A.zero A.cusp) D.slimSet)
    (hCM : ∀ c : R.edge.Base, c ∈ R.edge.cbase ↔ ∃ x ∈ R.edge.disk c, x ∈ D.M₂)
    (e : R.edge.EdgeEnd) (b : R.edge.Base → ℝ) (U₀ : TopologicalSpace.Opens R.edge.Base)
    (heU₀ : e.1 ∈ U₀) (hb : ContMDiffOn (𝓡 1) 𝓘(ℝ, ℝ) ∞ b U₀)
    (hEq : ∀ x (hx : x ∈ R.edge.source),
      x ∈ (R.slimPieces.residualNear (F.horizontal e) : Set W.Carrier) →
      R.slimPieces.residualFn (F.horizontal e) x = b (R.edge.proj ⟨x, hx⟩)) :
    ∃ U : TopologicalSpace.Opens R.edge.Base, e.1 ∈ U ∧
      ContMDiffOn (𝓡 1) 𝓘(ℝ, ℝ) ∞ b U ∧ mfderiv (𝓡 1) 𝓘(ℝ, ℝ) b e.1 ≠ 0 ∧
      R.edge.cbase ∩ U = {c | c ∈ U ∧ 0 ≤ b c} ∧
      ∃ N' : Set W.Carrier, IsOpen N' ∧ R.edge.rim e.1 ⊆ N' ∧ ∀ x ∈ N',
        ∃ hx : x ∈ R.edge.source,
          R.slimPieces.residualFn (F.horizontal e) x = b (R.edge.proj ⟨x, hx⟩) := by
  have hmodel : ∀ x ∈ R.edge.disk e.1, ∃ O : Set W.Carrier,
      IsOpen O ∧ x ∈ O ∧ O ⊆ (R.slimPieces.residualNear (F.horizontal e) : Set W.Carrier) ∧
      (∀ y ∈ O, y ∈ D.M₂ ↔ 0 ≤ R.slimPieces.residualFn (F.horizontal e) y) ∧
      ∀ y ∈ O, R.slimPieces.residualFn (F.horizontal e) y = 0 →
        y ∈ R.slimPieces.residualSet (F.horizontal e) :=
    fun x hx => exists_faceModel_JN74 R F hKR (F.horizontal e) (F.horizontal_disk e hx)
  choose! O hOo hxO hOn hOM hO0 using hmodel
  let Ω : Set W.Carrier := ⋃ x ∈ R.edge.disk e.1, O x
  have hΩo : IsOpen Ω := isOpen_biUnion fun x hx => hOo x hx
  have hdΩ : R.edge.disk e.1 ⊆ Ω := fun x hx => mem_biUnion hx (hxO x hx)
  have hΩ : ∀ z ∈ Ω, z ∈ (R.slimPieces.residualNear (F.horizontal e) : Set W.Carrier) ∧
      (z ∈ D.M₂ ↔ 0 ≤ R.slimPieces.residualFn (F.horizontal e) z) := by
    intro z hz
    obtain ⟨x, hx, hzx⟩ := mem_iUnion₂.1 hz
    exact ⟨hOn x hx hzx, hOM x hx z hzx⟩
  obtain ⟨V, heV, hV⟩ := exists_edge_tube_JN74 R.edge hΩo hdΩ
  have hdiskb : ∀ c : R.edge.Base, ∀ x ∈ R.edge.disk c, ∃ hx : x ∈ R.edge.source,
      R.edge.proj ⟨x, hx⟩ = c := by
    rintro c x ⟨z, ⟨hz, -⟩, rfl⟩
    exact ⟨z.2, hz⟩
  have hbval : ∀ c ∈ V, ∀ x ∈ R.edge.disk c, R.slimPieces.residualFn (F.horizontal e) x = b c := by
    intro c hc x hx
    obtain ⟨hxs, hxc⟩ := hdiskb c x hx
    rw [← hxc]
    exact hEq x hxs (hΩ x (hV c hc hx)).1
  refine ⟨V ⊓ U₀, ⟨heV, heU₀⟩, hb.mono inf_le_right,
    R.mfderiv_ne_zero_of_eq_JN74 e (F.horizontal e) (F.horizontal_disk e) b U₀ heU₀ hb hEq,
    ?_, ?_⟩
  · ext c
    constructor
    · rintro ⟨hcb, hcU⟩
      obtain ⟨x, hx, hxM⟩ := (hCM c).1 hcb
      have h1 := (hΩ x (hV c hcU.1 hx)).2.1 hxM
      rw [hbval c hcU.1 x hx] at h1
      exact ⟨hcU, h1⟩
    · rintro ⟨hcU, hc0⟩
      obtain ⟨x, hx⟩ := R.disk_nonempty_JN74 c
      refine ⟨(hCM c).2 ⟨x, hx, ?_⟩, hcU⟩
      refine (hΩ x (hV c hcU.1 hx)).2.2 ?_
      rw [hbval c hcU.1 x hx]
      exact hc0
  · refine ⟨(R.slimPieces.residualNear (F.horizontal e) : Set W.Carrier) ∩ R.edge.source,
      (R.slimPieces.residualNear (F.horizontal e)).isOpen.inter R.edge.source.isOpen, ?_,
      fun x hx => ⟨hx.2, hEq x hx.2 hx.1⟩⟩
    rintro x ⟨z, ⟨hz, hh⟩, rfl⟩
    exact ⟨R.slimPieces.residualSet_subset_residualNear_JN74 (F.horizontal e)
      (F.horizontal_disk e ⟨z, ⟨hz, hh.le⟩, rfl⟩), z.2⟩

end StageCutRows74

end GC.GraphManifold.Assembly.FC39P0
