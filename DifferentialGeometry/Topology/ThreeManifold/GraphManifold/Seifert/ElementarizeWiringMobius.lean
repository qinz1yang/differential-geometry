import
  DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Seifert.ElementarizeWiringMobiusRefine
import
  DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Seifert.ElementarizeWiringMobiusDecomp
import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Seifert.ElementarizeWiringAssembly

/-!
# `ElementarizeOnSubCollar` from the Möbius branch (tier T4)

Lane P1X2 (P1 wiring), the frozen tier T4 of lane P1W.

`elementarizeOnSubCollar_of_mobiusBranch` proves `ElementarizeOnSubCollar` from the three frozen
hypotheses: `hMD3` (lane MD3's core decomposition into planar and Möbius pieces with base cuts and
level-0 bottom sides), `hMD5` (a synchronised Möbius piece: a smooth embedding of
`mobiusBundleCarrier` onto the circle bundle over an embedded Möbius base, its boundary torus over
the boundary circle and synchronised there with a lifted flow) and `hE` (an elementary presentation
of `mobiusBundleCarrier` with one external torus whose collar is `mobiusExternalCollar`).

By P1W's reduced T4 (`elementarizeOnSubCollar_of_nonorientable`) it suffices to refine every
component with a non-orientable base. For such a component, `hMD3` applied to Morse data of the
base gives a planar decomposition of the core of shrunk Morse data `D'`, which
`nonempty_mobiusCore_of_decomposition` sorts into a `MobiusCore D'`; the piece system of the
elementary presentation of `hE` is carried over along the maps `χ` of `hMD5`, one copy per Möbius
piece, its external torus seamed to the adjacent planar or collar piece by the synchronised flow,
and `exists_componentRefinement_mobius` gives the component refinements.

The frozen text is kept, except that the binders `hι`, `hc`, `hcol`, `hint` inside `hMD5`, which
the statement never refers to, are written `_hι`, `_hc`, `_hcol`, `_hint` (the same statement up
to binder names; otherwise the unused-variables linter fires on them).
-/

set_option autoImplicit false

noncomputable section
open Set Function
open DifferentialGeometry DifferentialGeometry.Topology GC.Endpoint GC.GraphManifold
open scoped Manifold ContDiff Topology

universe u

namespace GC.Seifert.Wiring

theorem elementarizeOnSubCollar_of_mobiusBranch
    (hMD3 : ∀ (B : CompactSurface.{u}) (D : BaseMorseData B), ∃ D' : BaseMorseData B,
      D'.f = D.f ∧ D'.crit = D.crit ∧ D'.m = D.m ∧ D'.κ ≤ D.κ ∧
      (∀ i : Fin (D'.m + 1), ∃ j : Fin (D.m + 1), D'.level i = D.level j) ∧
      ∃ P : PlanarDecomposition D'.core,
        (∀ c, ∃ cB : PartialDiffeomorph ((𝓡 1).prod 𝓘(ℝ, ℝ)) (SurfaceModel.model B.kind)
          (Circle × ℝ) B.Carrier ∞,
          cB.source = {p | -1 < p.2 ∧ p.2 < 1} ∧
            ∀ t s, -1 < s → s < 1 → (P.cut c (t, s)).val = cB (t, s)) ∧
        ∀ j l, (∀ c b, P.cutSide c b ≠ ⟨j, l⟩) → ∃ (x₀ : B.Carrier) (hx₀ : D'.f x₀ = D'.level 0)
          (σ : Circle ≃ₘ⟮𝓡 1, 𝓡 1⟯ Circle), ∀ t s (hs : 0 ≤ s), s < 1 →
            (P.inclusion j ((P.piece j).collar l (t, halfPoint s hs))).val =
              Classical.choose (D'.exists_levelBicollar 0 hx₀) (σ t, s))
    (hMD5 : ∀ {C : CompactCarrier.{u}} {U : TopologicalSpace.Opens C.Carrier}
      (F : CircleFibration C U) (M : MobiusBase.{u}) {ι : M.surface.Carrier → F.base.Carrier}
      (_hι : Manifold.IsSmoothEmbedding
        (SurfaceModel.model M.surface.kind) (SurfaceModel.model F.base.kind) ∞ ι)
      (c : PartialDiffeomorph ((𝓡 1).prod 𝓘(ℝ, ℝ)) (SurfaceModel.model F.base.kind) (Circle × ℝ)
        F.base.Carrier ∞)
      (_hc : c.source = {p | -1 < p.2 ∧ p.2 < 1}) (b : Bool) (σ : Circle ≃ₘ⟮𝓡 1, 𝓡 1⟯ Circle)
      (_hcol : ∀ t s (hs : 0 ≤ s), s < 1 →
        ι (M.collar (t, halfPoint s hs)) = c (σ t, if b then s else -s))
      (_hint : ∀ q, (SurfaceModel.model F.base.kind).IsInteriorPoint (ι q))
      (L : LiftedBicollar F c),
      ∃ χ : mobiusBundleCarrier.{u}.Carrier → U, ContMDiff (𝓡∂ 3) C.model ∞ (fun q => (χ q).val) ∧
        Function.Injective χ ∧
        (∀ q, Function.Bijective (mfderiv (𝓡∂ 3) C.model (fun q => (χ q).val) q)) ∧
        range χ = F.projection ⁻¹' range ι ∧
        range (fun t => χ (mobiusExternalCollar (t, halfZero))) =
          F.projection ⁻¹' range (fun θ => c (θ, 0)) ∧
        ∃ δ > 0, ∀ t s (hs : 0 ≤ s), s < δ → χ (mobiusExternalCollar (t, halfPoint s hs)) =
          L.flow (if b then s else -s) (χ (mobiusExternalCollar (t, halfZero))))
    (hE : ∃ E : ElementaryPresentation mobiusBundleCarrier.{u}, ∃ h : E.toTorus.externalCount = 1,
      ∀ p, p ∈ halfCollarSource → E.toTorus.external.collar (Fin.cast h.symm 0) p =
        mobiusExternalCollar p) :
    ElementarizeOnSubCollar.{u} := by
  obtain ⟨E, hE1, hEc⟩ := hE
  refine elementarizeOnSubCollar_of_nonorientable fun W G i _ => ?_
  obtain ⟨D⟩ := exists_baseMorseData (G.fibration i).base
  obtain ⟨D', -, -, -, -, -, P, hcut, hbot⟩ := hMD3 _ D
  obtain ⟨Pm⟩ := nonempty_mobiusCore_of_decomposition D' P hcut hbot
  have hS1 : ∀ e : Fin E.toPieceSystem.externalCount, e = Fin.cast hE1.symm 0 := fun e =>
    Fin.ext (by
      have h1 : e.val < 1 := hE1 ▸ e.2
      change e.val = 0
      omega)
  exact exists_componentRefinement_mobius G.toTorusPresentation i (G.fibration i) Pm
    E.toPieceSystem (Fin.cast hE1.symm 0) hS1
    (fun p hp => ((E.pieceMap_collar (.inr (.inr (Fin.cast hE1.symm 0))) hp).trans
      (E.toTorus.marked_collar (Fin.cast hE1.symm 0) p hp)).trans (hEc p hp)) hMD5

end GC.Seifert.Wiring
