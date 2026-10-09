import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Seifert.MixedSplitLedger
import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Seifert.TorusMappingClassProof
import DifferentialGeometry.Topology.ThreeManifold.PrimeDecomposition.CutCapExistence

/-!
# The mixed split producer from the side data

Lane MS-b, tier MS6 (design `handoffs/20261004-design-ms-mixed-split.md` §3, review 30 §6). At an
inner split seam `j` of a mixed stage `σ`: linearize (`σL = σ.linearize`, with the cut carrier,
cut map, protected seams, frozen pieces and move predicates of `σ`), take the split tube of `σL`
and its cut-cap transition `X` (`sphereSystemCapping`, a single tube), the side data given by the
explicit input `hN4m : ExistsMixedSideData` and the capping conditions at the width
`δ₂ = min δ₁ (min δ₀ (1/4))`, and the mixed stages `capStage D hC c` on every capped component.
The protected seam tori avoid the surgery region (`disjoint_seamTorus_surgeryRegion`), the inner
count drops on every component (`innerCount_capStage_lt`), the collar ledgers of
`MixedSplitLedger` read the seams of `σ` because `σL` agrees with `σ` below height `1/4`
(`seam_linearize_of_le`), and the frozen ledgers are those of `σL` read on `σ`. Linearization
also preserves terminality (`MixedStage.isTerminal_linearize`).
-/

set_option autoImplicit false

noncomputable section
open Set Function
open DifferentialGeometry DifferentialGeometry.Topology GC.Endpoint GC.GraphManifold
open scoped Manifold ContDiff Topology

universe u

namespace GC.Seifert.RelativeNormalization

theorem MixedStage.isTerminal_linearize {Q : ConnectedClosedOrientedManifold.{u} 3}
    (σ : MixedStage Q) (hL : TorusMappingClassLinear) :
    (σ.linearize hL).IsTerminal ↔ σ.IsTerminal :=
  forall_congr' fun j => forall_congr' fun b => by
    rw [σ.isMergeSeam_linearize hL j b, σ.isSplitSeam_linearize hL j b,
      σ.isAbsorbSeam_linearize hL j b]

theorem mixedSplit_of_sideData (hN4m : ExistsMixedSideData.{u}) : MixedSplit.{u} := by
  intro Q σ j b h
  let hL := torusMappingClassLinear_holds
  let σL := σ.linearize hL
  have hL' : σL.IsSplitSeam j b := (σ.isSplitSeam_linearize hL j b).mpr h
  have hlin : σL.IsLinearSeam j := σ.isLinearSeam_linearize hL j
  let S₀ := σL.splitData hL'
  obtain ⟨P, X, hX⟩ := sphereSystemCapping Q (σL.splitSeamTube S₀ hlin) ⟨()⟩
  have hne : Nonempty X.tubes.Index := by
    rw [hX]
    exact ⟨()⟩
  have hsub : Subsingleton X.tubes.Index := by
    rw [hX]
    exact inferInstanceAs (Subsingleton Unit)
  let a : X.tubes.Index := hne.some
  obtain ⟨δ₀, hδ₀, hD⟩ := hN4m Q σL hL' S₀ hlin hX X.capping a
  obtain ⟨δ₁, hδ₁, hCC⟩ := σL.exists_cappedConditions S₀ hlin a hX
  have hpos : 0 < min δ₁ (min δ₀ (1 / 4)) := lt_min hδ₁ (lt_min hδ₀ (by norm_num))
  have hle₁ : min δ₁ (min δ₀ (1 / 4)) ≤ δ₁ := min_le_left _ _
  have hle₀ : min δ₁ (min δ₀ (1 / 4)) ≤ δ₀ := (min_le_right _ _).trans (min_le_left _ _)
  have hle : min δ₁ (min δ₀ (1 / 4)) ≤ 1 / 4 := (min_le_right _ _).trans (min_le_right _ _)
  obtain ⟨D⟩ := hD _ hpos hle₀
  have hC := hCC _ hpos hle₁
  refine ⟨P, X, MixedStage.capStage D hC, MixedStage.protEquiv D hC,
    MixedStage.frozenEquiv D hC, hsub, hne, fun k hk => ?_,
    MixedStage.innerCount_capStage_lt D hC, fun k => ?_, fun i => ?_⟩
  · have hkj : k ≠ j := fun he => h.1 (he ▸ hk)
    rw [hX, ← σ.seamTorus_linearize hL k]
    exact σL.disjoint_seamTorus_surgeryRegion S₀ hlin hkj
  · refine ⟨MixedStage.capCollarLedger D hC _ _ (σ.toTorus.seam k.1) fun t s hs => ?_⟩
    exact (σ.seam_linearize_of_le hL k.1 t ((le_abs_self s).trans (hs.le.trans hle))).symm.trans
      (congrArg (fun m => σL.toTorus.seam m (t, s)) (MixedStage.seamEquiv_protEquiv D hC k).symm)
  · let L := MixedStage.capFrozenLedger D hC _ _ (MixedStage.frozenCap hL' i)
      (MixedStage.pieceEquiv_frozenEquiv D hC i)
    exact ⟨{ diffeo := L.diffeo, oriented := L.oriented, map := L.map }⟩

end GC.Seifert.RelativeNormalization
