import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Closure.FC39StageCornerOpenJN74
import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Closure.FC39StageTubes74
import DifferentialGeometry.Geometry.Collapse.EdgeDisk.CornerRelativeInterior

/-!
# Draft 74, G7 (FDC03 corner model), step 2: the corner sign data from local primitives

Lane S-JUNCTIONS2 (suffix `_JN74`). `exists_cornerRank_descended_of_local_JN74` builds the
`CornerRank74` and `CornerDescended74` of an endpoint `e` from

* the descent patch `CornerDescent74 F G e` (D74-14 layer 1; S-EDP-FDC4 G10),
* a point of the rim fibre and the descended face equation `b` with `db(e) ≠ 0` (EDP05),
* ONE open set `N` of the circle domain containing the WHOLE rim fibre, inside the edge source and
  the residual buffer, on which: `h_F = b ∘ q₁`; `M₂ = {h_F ≥ 0}` (EDP05 / ZSP05 local `M₂`);
  `M^edge = {h_F ≥ 0, T ≤ 0}` (FDC02's set equality with `C₂ = {b ≥ 0}` near the endpoint); the
  component of `e` is `{b ≥ 0}` near `e`.

The rank is DERIVED (`cornerRank_surjective_JN74`), the vertex side of the sign model is structural
(`SlimPiecesV2.vertexSide_JN74`), the edge side follows from the primitives, and the region side
`R ⇔ {x ≥ 0, y ≥ 0}` from FDC03's corner kernel (`fdc03_relInterior_of_wholeCornerTube_EFC`: R0
chart `(T̄, h̄)`, open circle projection, closed circle projection, whole-tube shrinking) and the
comparison of relative interiors in the open circle domain.
-/

set_option autoImplicit false

noncomputable section

open Set Function Filter
open DifferentialGeometry DifferentialGeometry.Topology GC.Endpoint GC.Seifert GC.GraphManifold
open DifferentialGeometry.Geometry.Collapse.EdgeDisk
open Manifold
open scoped Manifold ContDiff Topology

universe u

namespace GC.GraphManifold.Assembly.FC39P0

variable {W : CompactCarrier.{u}} {n : ℕ} {E : BoundaryTori W n}

/-- The relative interior in an open subset is the relative interior in the ambient space, at
points of the open subset. -/
theorem relInt_open_JN74 {X : Type*} [TopologicalSpace X] {Q : TopologicalSpace.Opens X}
    {M Ed : Set X} {x : Q} :
    (x : X) ∈ relInt M Ed ↔
      x ∈ relInt (Subtype.val ⁻¹' M : Set Q) (Subtype.val ⁻¹' Ed : Set Q) := by
  unfold relInt
  rw [mem_image_interior_preimage_val_iff, mem_image_interior_preimage_val_iff]
  constructor
  · rintro ⟨hM, O, hO, hxO, hOE⟩
    exact ⟨hM, Subtype.val ⁻¹' O, hO.preimage continuous_subtype_val, hxO,
      fun y hy => hOE ⟨hy.1, hy.2⟩⟩
  · rintro ⟨hM, O', hO', hxO', hO'E⟩
    refine ⟨hM, Subtype.val '' O', Q.isOpen.isOpenMap_subtype_val O' hO', ⟨x, hxO', rfl⟩, ?_⟩
    rintro _ ⟨⟨y, hy, rfl⟩, hyM⟩
    exact hO'E ⟨hy, hyM⟩

/-- **Corner rank and descended data of an endpoint from local primitives** (see the module
docstring for the list of primitives). -/
theorem exists_cornerRank_descended_of_local_JN74 {A : SmoothStageGeometry74 W E}
    {D : StageCutChoice74 A} {R : StageCutRows74 A D} {F : JunctionFaceFacts74 A D R}
    {G : JunctionRimFacts74 A D R} (e : R.edge.EdgeEnd) (d : CornerDescent74 F G e)
    (hfib : ∃ p : R.circle.domain, R.circle.proj p = G.rimBase e.1)
    (b : R.edge.Base → ℝ) (U : TopologicalSpace.Opens R.edge.Base) (heU : e.1 ∈ U)
    (hb : ContMDiffOn (𝓡 1) 𝓘(ℝ, ℝ) ∞ b U) (hbreg : mfderiv (𝓡 1) 𝓘(ℝ, ℝ) b e.1 ≠ 0)
    (N : Set R.circle.domain) (hN : IsOpen N)
    (hNfib : R.circle.proj ⁻¹' {G.rimBase e.1} ⊆ N)
    (hbuf : ∀ x ∈ N, (x : W.Carrier) ∈ R.edge.source ∧
      (x : W.Carrier) ∈ R.slimPieces.residualNear (F.horizontal e))
    (hNeq : ∀ x ∈ N, ∃ hx : (x : W.Carrier) ∈ R.edge.source,
      R.slimPieces.residualFn (F.horizontal e) x = b (R.edge.proj ⟨x, hx⟩))
    (hM2 : ∀ x ∈ N, (x : W.Carrier) ∈ D.M₂ ↔ 0 ≤ R.slimPieces.residualFn (F.horizontal e) x)
    (hE : ∀ x ∈ N, (x : W.Carrier) ∈ D.edgeSet ↔
      0 ≤ R.slimPieces.residualFn (F.horizontal e) x ∧ R.cornerT x ≤ 0)
    (hC : ∀ x ∈ N, ∀ hx : (x : W.Carrier) ∈ R.edge.source,
      (R.edge.proj ⟨x, hx⟩ ∈ e.component.1 ↔ 0 ≤ b (R.edge.proj ⟨x, hx⟩))) :
    ∃ K : CornerRank74 F G e, Nonempty (CornerDescended74 K) := by
  classical
  obtain ⟨p₀, hp₀⟩ := hfib
  have hrank := cornerRank_surjective_JN74 (F := F) (G := G) e p₀ hp₀ b U heU hb hbreg N hN
    (hNfib hp₀) hNeq
  have hEB : Module.finrank ℝ (EuclideanSpace ℝ (Fin 2)) = 2 := finrank_euclideanSpace_fin
  have hf : MDifferentiableAt W.model (𝓡 2) R.circle.proj p₀ :=
    (R.circle.proj_smooth p₀).mdifferentiableAt (by simp)
  obtain ⟨U₀, hU₀, hc₀U, hres⟩ := fdc03_relInterior_of_wholeCornerTube_EFC (I := W.model)
    (IB := 𝓡 2) hEB R.circle.proj.continuous (isClosedMap_circleBundle74 R.circleFacts)
    R.circle.isOpenMap_proj_JN74 d.rim_mem d.Tb_smooth d.hb_smooth d.desc d.center hp₀ hf hrank
    hN hNfib (M₂ := Subtype.val ⁻¹' D.M₂) (Medge := Subtype.val ⁻¹' D.edgeSet)
    (fun y hy => ⟨hM2 y hy, hE y hy⟩)
  have hside : ∀ x ∈ N ∩ R.circle.proj ⁻¹' U₀,
      ((x : W.Carrier) ∈ R.slimPieces.rowSet (R.slimPieces.residualOwner (F.horizontal e)) ↔
        R.slimPieces.residualFn (F.horizontal e) x ≤ 0) ∧
      ((x : W.Carrier) ∈ R.edge.wholeComponent e.component ↔
        0 ≤ R.slimPieces.residualFn (F.horizontal e) x ∧ R.cornerT x ≤ 0) ∧
      ((x : W.Carrier) ∈ R.circle.region ↔
        0 ≤ R.cornerT x ∧ 0 ≤ R.slimPieces.residualFn (F.horizontal e) x) := by
    intro x hx
    obtain ⟨hxS, hxb⟩ := hNeq x hx.1
    have hT : R.cornerT x = R.edge.height ⟨x, hxS⟩ - R.edge.level := by
      simp only [StageCutRows74.cornerT, hxS, ↓reduceDIte]
    refine ⟨SlimPiecesV2.vertexSide_JN74 (S := R.slimPieces) (F := F.horizontal e)
      (hbuf x hx.1).2, ?_, ?_⟩
    · constructor
      · rintro ⟨y, ⟨hy1, hy2⟩, hyx⟩
        have hy : y = ⟨x, hxS⟩ := Subtype.ext hyx
        subst hy
        refine ⟨?_, ?_⟩
        · rw [hxb]
          exact (hC x hx.1 hxS).1 hy1
        · rw [hT]
          exact sub_nonpos.2 hy2
      · rintro ⟨h1, h2⟩
        refine ⟨⟨x, hxS⟩, ⟨(hC x hx.1 hxS).2 (hxb ▸ h1), ?_⟩, rfl⟩
        rw [hT] at h2
        exact sub_nonpos.1 h2
    · have hreg := Set.ext_iff.1 (D.region_circleBundle74_eq_M₃ R.circleFacts) (x : W.Carrier)
      have hrel := relInt_open_JN74 (Q := R.circle.domain) (M := D.M₂) (Ed := D.edgeSet) (x := x)
      have hk := (hres x hx.2).2
      change x ∈ (Subtype.val ⁻¹' D.M₂ : Set R.circle.domain) \
        relInt (Subtype.val ⁻¹' D.M₂ : Set R.circle.domain)
          (Subtype.val ⁻¹' D.edgeSet : Set R.circle.domain) ↔ _ at hk
      refine hreg.trans ?_
      refine Iff.trans ?_ hk
      change (x : W.Carrier) ∈ D.M₂ \ relInt D.M₂ D.edgeSet ↔ _
      simp only [Set.mem_sdiff, mem_preimage]
      exact and_congr Iff.rfl (not_congr hrel)
  refine ⟨{ point := p₀
            point_proj := hp₀
            rank := hrank
            nbhd := N ∩ R.circle.proj ⁻¹' U₀
            nbhd_open := hN.inter (hU₀.preimage R.circle.proj.continuous)
            fibre_sub := fun p hp => ⟨hNfib hp, by
              change R.circle.proj p ∈ U₀
              rw [show R.circle.proj p = G.rimBase e.1 from hp]
              exact hc₀U⟩
            nbhd_buffer := fun x hx => hbuf x hx.1
            sign := hside }, ⟨?_⟩⟩
  exact
    { descended := b
      descended_smooth := ⟨U, heU, hb⟩
      descended_regular := hbreg
      descended_eq := fun x hx => hNeq x hx.1 }

end GC.GraphManifold.Assembly.FC39P0
