import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Seifert.ElementarizeWiringMobius
import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Seifert.ElementarizeInstances
import
  DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Seifert.CoreDecompositionMobiusAssembly

/-!
# The P1 producer modulo the synchronised Möbius piece

Lane P1X2 (P1 wiring). Two of the three hypotheses of the frozen tier T4
(`elementarizeOnSubCollar_of_mobiusBranch`) are theorems:

* `hE` is RG02's elementary presentation of `mobiusBundleCarrier` (`acceptanceMobius`, three
  product pieces over `P₃`, `P₁`, `P₁` and two seams), whose external collar is
  `mobiusExternalCollar` by definition (`mobiusBranch_hE`);
* `hMD3` is lane MD3b's `CoreDecomposition.exists_planarMobiusDecomposition_core_of_shrink`.

So `ElementarizeOnSubCollar` follows from `hMD5` alone (`elementarizeOnSubCollar_of_mobiusPiece`,
the frozen text of `hMD5` with the binder names of T4). For raw presentations all of whose bases are
orientable the clause of `ElementarizeOnSubCollar` holds without any hypothesis (P1W's
`elementarizeOnSubCollar_rawGraph_of_orientable`).
-/

set_option autoImplicit false

noncomputable section
open Set Function
open DifferentialGeometry DifferentialGeometry.Topology GC.Endpoint GC.GraphManifold
open scoped Manifold ContDiff Topology

universe u

namespace GC.Seifert.Wiring

theorem mobiusBranch_hE :
    ∃ E : ElementaryPresentation mobiusBundleCarrier.{u}, ∃ h : E.toTorus.externalCount = 1,
      ∀ p, p ∈ halfCollarSource → E.toTorus.external.collar (Fin.cast h.symm 0) p =
        mobiusExternalCollar p :=
  ⟨acceptanceMobius, rfl, fun _ _ => rfl⟩

theorem elementarizeOnSubCollar_of_mobiusPiece
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
          L.flow (if b then s else -s) (χ (mobiusExternalCollar (t, halfZero)))) :
    ElementarizeOnSubCollar.{u} :=
  elementarizeOnSubCollar_of_mobiusBranch
    (fun _ D => CoreDecomposition.exists_planarMobiusDecomposition_core_of_shrink D) hMD5
    mobiusBranch_hE

end GC.Seifert.Wiring
