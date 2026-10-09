import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Closure.FC39StageCircleDescentJN74

/-!
# Draft 74, the corner descent `CornerDescent74` from fibre-constancy

Lane S-JUNCTIONS (by S-JUNCTIONS3), G18 (suffix `_JN74`). Layer 1 of D74-14 at an actual endpoint
`e`, reduced to the face-specific input "`T − 4Δ` and the face function `h_F` are constant on the
`q₀`-fibres over a patch whose preimage lies in the edge source and in the face neighbourhood":

* `SlimPiecesV2.residualFn_contMDiffOn_JN74` (the face function is smooth on its neighbourhood) and
  `SlimPiecesV2.residualFn_eq_zero_JN74` (it vanishes on the face), from the structure fields of
  the zero domains, cusp cores and slim pieces;
* **`cornerDescent_ofFibreConst_JN74`**: a `CornerDescent74 F G e` (patch, `Tb`, `hb`, `desc`,
  `center`) from the patch `N ∋ rimBase e`, `hsrc` (preimage of `N` in the edge source and the
  residual neighbourhood), the two fibre-constancies and a point of the rim fibre; `Tb` and `hb` are
  produced by `cornerT_descends_JN74` / `exists_descended_of_fibreConst_JN74`.
-/

set_option autoImplicit false

noncomputable section

open Set Function
open DifferentialGeometry DifferentialGeometry.Topology GC.Endpoint GC.Seifert GC.GraphManifold
open Manifold
open scoped Manifold ContDiff Topology

universe u

namespace GC.GraphManifold.Assembly.FC39P0

variable {W : CompactCarrier.{u}} {n : ℕ} {E : BoundaryTori W n}

namespace SlimPiecesV2

variable {Z : ZeroDomains W} {C : CuspCores W E} (S : SlimPiecesV2 W Z C)

/-- **The face function of a residual face is smooth on its neighbourhood.** -/
theorem residualFn_contMDiffOn_JN74 (F : S.ResidualFace) :
    ContMDiffOn W.model 𝓘(ℝ, ℝ) ∞ (S.residualFn F) (S.residualNear F) := by
  rcases F with ⟨F | F, hF⟩ | e
  · exact (Z.ratio_smooth F.1).contMDiffOn
  · exact C.fn_smooth F.1
  · exact S.endFn_smooth e

/-- **The face function vanishes on its face.** -/
theorem residualFn_eq_zero_JN74 (F : S.ResidualFace) {x : W.Carrier}
    (hx : x ∈ S.residualSet F) : S.residualFn F x = 0 := by
  rcases F with ⟨F | F, hF⟩ | e
  · obtain ⟨p, hp, rfl⟩ := hx
    have hb : (Z.piece F.1).map p ∈ pieceBoundary (Z.piece F.1) :=
      ⟨p, F.2.subset hp, rfl⟩
    have := Z.boundary_eq F.1 ▸ hb
    exact this
  · obtain ⟨b, F', hF'⟩ := F
    subst hF'
    obtain ⟨p, hp, rfl⟩ := hx
    rw [C.internalModelFace_eq b] at hp
    obtain ⟨t, rfl⟩ := hp
    have h2 : (C.piece b).map (C.product b (t, iccEnd true)) ∈ range fun t =>
        (C.piece b).map (C.product b (t, iccEnd true)) := ⟨t, rfl⟩
    rw [C.internal_eq b] at h2
    exact h2.2
  · have h := S.endFn_level e
    have hx' : x ∈ (S.piece e.1.1.1).map '' slimModelEnd (S.model e.1.1.1) e.1.1.2 := hx
    rw [h] at hx'
    exact hx'.2

end SlimPiecesV2

section Descent

variable {A : SmoothStageGeometry74 W E} {D : StageCutChoice74 A} {R : StageCutRows74 A D}

open Classical in
/-- **`CornerDescent74` from fibre-constancy** (layer 1 of D74-14 at an actual endpoint): over a
patch `N ∋ rimBase e` of the circle base whose preimage lies in the edge source and in the face
neighbourhood of `horizontal e`, on whose `q₀`-fibres `T − 4Δ` and `h_F` are constant, with a point
over the rim base point: `Tb`, `hb` smooth on `N` with `T − 4Δ = Tb ∘ q₀`, `h_F = hb ∘ q₀`, both
vanishing at the rim base point (the rim fibre lies on the vertical and the horizontal face). -/
def cornerDescent_ofFibreConst_JN74 (F : JunctionFaceFacts74 A D R) (G : JunctionRimFacts74 A D R)
    (e : R.edge.EdgeEnd) (N : TopologicalSpace.Opens R.circle.Base) (hN : G.rimBase e.1 ∈ N)
    (hsrc : ∀ x : R.circle.domain, R.circle.proj x ∈ N → (x : W.Carrier) ∈ R.edge.source ∧
      (x : W.Carrier) ∈ R.slimPieces.residualNear (F.horizontal e))
    (hconstT : ∀ x y : R.circle.domain, R.circle.proj x ∈ N →
      R.circle.proj y = R.circle.proj x → R.cornerT x = R.cornerT y)
    (hconstH : ∀ x y : R.circle.domain, R.circle.proj x ∈ N →
      R.circle.proj y = R.circle.proj x →
      R.slimPieces.residualFn (F.horizontal e) x.1 = R.slimPieces.residualFn (F.horizontal e) y.1)
    (hfib : ∃ p : R.circle.domain, R.circle.proj p = G.rimBase e.1) :
    CornerDescent74 F G e :=
  let hT := cornerT_descends_JN74 R N (fun x hx => (hsrc x hx).1) hconstT
  let hf : ContMDiffOn W.model 𝓘(ℝ, ℝ) ∞ (R.slimPieces.residualFn (F.horizontal e))
      (R.circle.tube (N : Set R.circle.Base)) :=
    (R.slimPieces.residualFn_contMDiffOn_JN74 (F.horizontal e)).mono (by
      rintro _ ⟨x, hx, rfl⟩
      exact (hsrc x hx).2)
  let hH := exists_descended_of_fibreConst_JN74 R.circle N
    (R.slimPieces.residualFn (F.horizontal e)) hf hconstH
  { patch := N
    rim_mem := hN
    Tb := Classical.choose hT
    hb := Classical.choose hH
    Tb_smooth := (Classical.choose_spec hT).1
    hb_smooth := (Classical.choose_spec hH).1
    desc := fun x hx => ⟨(Classical.choose_spec hT).2 x hx, (Classical.choose_spec hH).2 x hx⟩
    center := by
      obtain ⟨p, hp⟩ := hfib
      have hpN : R.circle.proj p ∈ N := by
        rw [hp]
        exact hN
      have hpmem : (p : W.Carrier) ∈ R.edge.rim e.1 := by
        rw [G.rim_fibre e.1 (R.edge.frontier_cbase_subset e.2)]
        exact ⟨p, hp, rfl⟩
      obtain ⟨x, ⟨hxproj, hxh⟩, hxp⟩ := hpmem
      have hxs : (p : W.Carrier) ∈ R.edge.source := hxp ▸ x.2
      refine ⟨?_, ?_⟩
      · have h1 := (Classical.choose_spec hT).2 p hpN
        rw [hp] at h1
        rw [← h1]
        have hx' : x = ⟨p, hxs⟩ := Subtype.ext hxp
        simp only [StageCutRows74.cornerT, hxs, ↓reduceDIte]
        rw [← hx']
        exact sub_eq_zero.2 hxh
      · have h1 := (Classical.choose_spec hH).2 p hpN
        rw [hp] at h1
        rw [← h1]
        refine R.slimPieces.residualFn_eq_zero_JN74 (F.horizontal e) (F.horizontal_disk e ?_)
        exact ⟨x, ⟨hxproj, le_of_eq hxh⟩, hxp⟩ }

end Descent

end GC.GraphManifold.Assembly.FC39P0
