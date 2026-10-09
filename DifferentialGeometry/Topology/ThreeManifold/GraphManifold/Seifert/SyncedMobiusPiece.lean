import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Seifert.SyncedMobiusPieceCollar
import
  DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Seifert.ElementarizeWiringMobiusCore
import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Seifert.TorusCollarStraightening

/-!
# The synchronised Möbius piece

Lane MD5b: `exists_syncedMobiusPiece`, the frozen hypothesis `hMD5` of tier T4 of the P1 wiring
(`Wiring.elementarizeOnSubCollar_of_mobiusPiece`). The map is `χ₀ ∘ Φ`, with `χ₀` the
diffeomorphism of `mobiusBundleSet` onto `π⁻¹ (range ι)` of `SF/SyncedMobiusPieceMap.lean` and
`Φ` the straightening (`exists_torusCollar_straightening`) of `mobiusExternalCollar` onto the
flow-out collar `flowCollar` near the boundary torus, so that on the thin collar the map is the
flow of `L` started on the boundary.
-/

set_option autoImplicit false

noncomputable section
open Set Function
open DifferentialGeometry DifferentialGeometry.Topology GC.Endpoint GC.GraphManifold
open scoped Manifold ContDiff Topology

universe u

namespace GC.Seifert

theorem exists_syncedMobiusPiece {C : CompactCarrier.{u}} {U : TopologicalSpace.Opens C.Carrier}
    (F : CircleFibration C U) (M : MobiusBase.{u}) {ι : M.surface.Carrier → F.base.Carrier}
    (hι : Manifold.IsSmoothEmbedding (SurfaceModel.model M.surface.kind)
      (SurfaceModel.model F.base.kind) ∞ ι)
    (c : PartialDiffeomorph ((𝓡 1).prod 𝓘(ℝ, ℝ)) (SurfaceModel.model F.base.kind) (Circle × ℝ)
      F.base.Carrier ∞)
    (hc : c.source = {p | -1 < p.2 ∧ p.2 < 1}) (b : Bool) (σ : Circle ≃ₘ⟮𝓡 1, 𝓡 1⟯ Circle)
    (hcol : ∀ t s (hs : 0 ≤ s), s < 1 →
      ι (M.collar (t, halfPoint s hs)) = c (σ t, if b then s else -s))
    (hint : ∀ q, (SurfaceModel.model F.base.kind).IsInteriorPoint (ι q)) (L : LiftedBicollar F c) :
    ∃ χ : mobiusBundleCarrier.{u}.Carrier → U, ContMDiff (𝓡∂ 3) C.model ∞ (fun q => (χ q).val) ∧
      Function.Injective χ ∧
      (∀ q, Function.Bijective (mfderiv (𝓡∂ 3) C.model (fun q => (χ q).val) q)) ∧
      range χ = F.projection ⁻¹' range ι ∧
      range (fun t => χ (mobiusExternalCollar (t, halfZero))) =
        F.projection ⁻¹' range (fun θ => c (θ, 0)) ∧
      ∃ δ > 0, ∀ t s (hs : 0 ≤ s), s < δ → χ (mobiusExternalCollar (t, halfPoint s hs)) =
        L.flow (if b then s else -s) (χ (mobiusExternalCollar (t, halfZero))) := by
  let D : MobiusPiece.PieceData F M := ⟨ι, hι, c, hc, b, σ, hcol, hint⟩
  have hsrc : ∀ p, (p, halfZero) ∈ mobiusExternalCollar.{u}.source ∩ (D.flowCollar L).source := by
    intro p
    refine ⟨?_, ?_⟩
    · rw [mobiusExternalCollar_source]
      exact zero_mem_halfCollarSource p
    · change (0 : ℝ) < D.wd L
      exact D.wd_pos L
  have h0 : ∀ p, D.flowCollar L (p, halfZero) = mobiusExternalCollar (p, halfZero) := by
    intro p
    rw [D.flowCollar_apply]
    change D.χinv (L.flow (D.sg 0) (D.bd p)) = _
    rw [show D.sg 0 = 0 by simp [MobiusPiece.PieceData.sg], L.flow_zero]
    exact D.χinv_χ₀ _
  obtain ⟨δ, hδ, Φ, hΦ, -⟩ := exists_torusCollar_straightening (C := mobiusBundleCarrier.{u})
    mobiusExternalCollar (D.flowCollar L) hsrc (fun p => (h0 p).symm)
    (fun p => MobiusPiece.PieceData.isBoundaryPoint_externalCollar p) isOpen_univ (subset_univ _)
  have hΦ0 : ∀ t, Φ (mobiusExternalCollar (t, halfZero)) = mobiusExternalCollar (t, halfZero) := by
    intro t
    rw [hΦ t halfZero (by change (0 : ℝ) < δ; exact hδ), h0]
  refine ⟨fun q => D.χ₀ (Φ q), D.contMDiff_χ₀.comp Φ.contMDiff,
    D.injective_χ₀.comp Φ.injective, fun q => ?_, ?_, ?_, ?_⟩
  · have h1 : MDifferentiableAt (𝓡∂ 3) C.model (fun x => (D.χ₀ x).val) (Φ q) :=
      D.contMDiff_χ₀.mdifferentiableAt (by simp)
    have h2 : MDifferentiableAt (𝓡∂ 3) (𝓡∂ 3) Φ q := Φ.contMDiff.mdifferentiableAt (by simp)
    change Function.Bijective (mfderiv (𝓡∂ 3) C.model ((fun x => (D.χ₀ x).val) ∘ Φ) q)
    rw [mfderiv_comp q h1 h2]
    exact (D.bijective_mfderiv_χ₀ (Φ q)).comp
      (Φ.mfderivToContinuousLinearEquiv (by simp) q).bijective
  · rw [← D.range_χ₀]
    exact Φ.surjective.range_comp D.χ₀
  · have hr : range (fun t => D.χ₀ (Φ (mobiusExternalCollar (t, halfZero)))) =
        range (fun t => D.χ₀ (mobiusExternalCollar (t, halfZero))) := by
      simp only [hΦ0]
    change range (fun t => D.χ₀ (Φ (mobiusExternalCollar (t, halfZero)))) = _
    rw [hr]
    ext y
    constructor
    · rintro ⟨t, rfl⟩
      exact (D.mem_zero_iff _).mpr (MobiusPiece.PieceData.isBoundaryPoint_externalCollar t)
    · intro hy
      have hyK : y ∈ range D.χ₀ := by
        rw [D.range_χ₀]
        obtain ⟨θ, hθ⟩ := hy
        refine ⟨M.collar (σ.symm θ, halfZero), ?_⟩
        change ι _ = _
        rw [mobius_zero_eq M c b σ hcol, Diffeomorph.apply_symm_apply]
        exact hθ
      obtain ⟨x, rfl⟩ := hyK
      obtain ⟨t, ht⟩ := (isBoundaryPoint_iff_external x).mp ((D.mem_zero_iff x).mp hy)
      exact ⟨t, congrArg D.χ₀ ht⟩
  · refine ⟨min δ (D.wd L), lt_min hδ (D.wd_pos L), fun t s hs hsδ => ?_⟩
    have hsw : s < D.wd L := hsδ.trans_le (min_le_right _ _)
    change D.χ₀ (Φ _) = L.flow _ (D.χ₀ (Φ _))
    rw [hΦ0, hΦ t (halfPoint s hs) (by change s < δ; exact hsδ.trans_le (min_le_left _ _)),
      D.flowCollar_apply]
    change D.χ₀ (D.χinv (L.flow (D.sg s) (D.bd t))) = _
    rw [D.χ₀_χinv (D.flow_bd_mem L t hs hsw), D.sg_eq]
    rfl

end GC.Seifert
