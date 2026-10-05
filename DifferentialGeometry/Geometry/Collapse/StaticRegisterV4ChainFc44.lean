import DifferentialGeometry.Geometry.Collapse.StaticRegisterV4ChainPbr

/-!
# FC44's CLOSED binding on register V4 (PBR01 + the chain on the register's own stage data)

Lane C14-REG-CHAIN, G4. Blueprint `master207B.tex`, FC44 (`found:fibration-parameter-order`,
B:9998–10024): KL (15.4) orders `{𝓜, β₃} ≺ {c_slim, Ω_i} ≺ Γ₃ ≺ {Σ₃, Ξ₃} ≺ c_edge ≺ Γ₂ ≺ {Σ₂, Ξ₂}
≺ c_{2-stratum} ≺ Γ₁ ≺ {Σ₁, Ξ₁} ≺ … ≺ β₂ ≺ Δ ≺ …`; "deliver a register of every consumer
inequality and its allowed predecessors, including positivity/finiteness of each bound". B:10336:
PBR01 (with PBR02–PBR03) "supplies FC44's CLOSED binding".

`fc44_closed_binding_RGC`: on every closed standing sequence, ONE strategy `T` (refining
`closedStrategyCompleteV4C` and the chain caps) such that
* the register is inhabited (PBR01, `exists_closedRegisterV4`) and the validity record holds;
* at EVERY register `R`: the chain's numbers are `R`'s STAGE values, chosen first in V4's order
  (stage → β₃ → circle → β₂ → βc → Δ → …), and they satisfy GAF01's CHOICE in the chain's form
  (`ClosedStage.chain_numbers_RGC`, i.e. KL's `c, Γ, Σ, Ξ` BEFORE `β₂, Δ`); PR10's `C_ρ` is fixed at
  the stage, dominates EDP01's chain constant and every stage output's (SMV) constant
  (`2c_w^{(j)}/Σ_j ≤ C_ρ/100`), and `C_ρΔΛ < 10⁻⁶`; every threshold slot of `T` is positive (the
  fields `*_pos` of `ClosedThresholdsV4`);
* every consumer reads the SAME assignment: on every member of `R`'s tail, the final family at
  `R`'s values and the chain on `R`'s stage data exist (G2/G3).
The boundary half of FC44 (`r_∂` appended after `V`) is lane BSTG-D1's.
-/

set_option autoImplicit false

noncomputable section

open Set Function Metric Bundle Manifold Filter
open scoped ContDiff Manifold Topology
open DifferentialGeometry GC.Endpoint GC.MetricGeometry
open DifferentialGeometry.Geometry.Riemannian DifferentialGeometry.Analysis

namespace DifferentialGeometry.Geometry.Collapse

universe u

local notation "ℝ²" => EuclideanSpace ℝ (Fin 2)

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace

/-- **FC44's closed binding** (see the module header). -/
theorem fc44_closed_binding_RGC (K : ℕ) (hK : 10 ≤ K) (A : ℝ → ℝ)
    (hA : ∀ x, 0 < x → 0 < A x) (Wseq : ℕ → CompactCarrier.{u})
    (gseq : ∀ m, SmoothRiemannianMetric (Wseq m).model (Wseq m).Carrier)
    (hf : ∀ m, ClosedMemberFacts (Wseq m))
    (hg : ∀ m, closedCollapseHypotheses (Wseq m) (gseq m) K A (closedCounterexampleRatio (m + 2))) :
    ∃ T : ClosedThresholdsV4 (earlyDataSharedV4 K),
      ClosedStrategyRefinesV4 T (closedStrategyCompleteV4C (earlyDataSharedV4 K)) ∧
      PartialClosedThresholdValidityV4Rows K A Wseq gseq (earlyDataSharedV4 K) T ∧
      Nonempty (ClosedRegisterV4 (earlyDataSharedV4 K) T) ∧
      ∀ R : ClosedRegisterV4 (earlyDataSharedV4 K) T,
        ((∀ j, 0 < (earlyDataSharedV4 K).Ξ j (R.stage.Γ j) ∧ 0 < R.stage.Sig j ∧
            128 * ((earlyDataSharedV4 K).Ξ j (R.stage.Γ j))⁻¹ * R.stage.Sig j ≤ 1 / 5 ∧
            0 ≤ R.stage.e j) ∧
          5 / 3 * (earlyDataSharedV4 K).Ξ 0 (R.stage.Γ 0) * R.stage.Sig 0 < R.stage.c 0 ∧
          R.stage.c 0 ≤ 1 / 512 ∧
          (5 / 3 * (earlyDataSharedV4 K).Ξ 0 (R.stage.Γ 0) * R.stage.Sig 0 * gafCutoffConstant *
              gafDerivativeBound + (earlyDataSharedV4 K).Ξ 0 (R.stage.Γ 0) * gafDerivativeBound +
              R.stage.e 0) < R.stage.c 0 ∧
          R.stage.c 0 ≤ 4 * gafKappa / 5 ∧ R.stage.c 0 ≤ 3 * R.stage.Sig 1 / 10 ∧
          (R.stage.c 0 + (5 / 3 * (earlyDataSharedV4 K).Ξ 1 (R.stage.Γ 1) * R.stage.Sig 1 +
              (1 + (earlyDataSharedV4 K).Ξ 1 (R.stage.Γ 1)) * R.stage.c 0)) < R.stage.c 1 ∧
          R.stage.c 1 ≤ 1 / 512 ∧
          ((5 / 3 * (earlyDataSharedV4 K).Ξ 1 (R.stage.Γ 1) * R.stage.Sig 1 +
              (1 + (earlyDataSharedV4 K).Ξ 1 (R.stage.Γ 1)) * R.stage.c 0) * gafCutoffConstant *
              (gafDerivativeBound + R.stage.c 0) +
              (earlyDataSharedV4 K).Ξ 1 (R.stage.Γ 1) * (gafDerivativeBound + R.stage.c 0) +
              R.stage.e 1 + 2 * R.stage.c 0) < R.stage.c 1 ∧
          R.stage.c 1 ≤ 4 * gafKappa / 5 ∧ R.stage.c 1 ≤ 3 * R.stage.Sig 2 / 10 ∧
          (R.stage.c 1 + (5 / 3 * (earlyDataSharedV4 K).Ξ 2 (R.stage.Γ 2) * R.stage.Sig 2 +
              (1 + (earlyDataSharedV4 K).Ξ 2 (R.stage.Γ 2)) * R.stage.c 1)) < R.stage.c 2 ∧
          R.stage.c 2 ≤ 1 / 512 ∧
          ((5 / 3 * (earlyDataSharedV4 K).Ξ 2 (R.stage.Γ 2) * R.stage.Sig 2 +
              (1 + (earlyDataSharedV4 K).Ξ 2 (R.stage.Γ 2)) * R.stage.c 1) * gafCutoffConstant *
              (gafDerivativeBound + R.stage.c 1) +
              (earlyDataSharedV4 K).Ξ 2 (R.stage.Γ 2) * (gafDerivativeBound + R.stage.c 1) +
              R.stage.e 2 + 2 * R.stage.c 1) < R.stage.c 2) ∧
        100 * (gafDerivativeBound + 1) *
            (1 + gafCutoffConstant + 1 * stageCwAt_V4C R.stage 0 / R.stage.Sig 0) ≤
          closedScaleConstantV4 (earlyDataSharedV4 K) T R.stage ∧
        (∀ j, 2 * stageCwAt_V4C R.stage j / R.stage.Sig j ≤
          closedScaleConstantV4 (earlyDataSharedV4 K) T R.stage / 100) ∧
        closedScaleConstantV4 (earlyDataSharedV4 K) T R.stage * R.later.excl.Δ *
          R.later.scale.Λ < 1 / 10 ^ 6 ∧
        ∃ εr δ Λz : ℝ, ∀ m, R.later.tail ≤ m →
          ∃ M : ClosedModel (Wseq m) (gseq m),
            ∃ F : ClosedFamilyInstanceC14DV4 K R M δ εr Λz,
              ∃ sel : Fin 3 → BlockSpace (fun _ : CGPTag F.family.toLocalChartFamily
                  F.family.zero => ℝ²) → M.X,
                (∀ st, ∀ x ∈ gafCloudEnlarged F.family.toLocalChartFamily F.family.zero st,
                  cgpProjMap F.family.toLocalChartFamily F.family.zero
                    (gafStageTags F.family.toLocalChartFamily F.family.zero st) (sel st x) = x) ∧
                ∃ C : Gaf02Chain F.family.toLocalChartPackets K
                    (fun j => (earlyDataSharedV4 K).Ξ j (R.stage.Γ j)) R.stage.Γ R.stage.Sig
                    R.stage.e R.stage.c (stageCwAt_V4C R.stage),
                  C.sel = sel := by
  obtain ⟨T, hv, hTU, -, hNb, hcw, hR⟩ := register_yields_chain_RGC K hK A hA Wseq gseq hf hg
  refine ⟨T, hTU, hv, exists_closedRegisterV4 _ T, fun R => ⟨R.stage.chain_numbers_RGC,
    R.stage.chain_scaleConstant_le_RGC hNb hcw, R.stage.smv_le_scaleConstant_RGC hNb hcw,
    R.later.regScale_Cρ, ?_⟩⟩
  obtain ⟨-, εr, -, Λz, δc, -, -, ht⟩ := hR R
  refine ⟨εr, δc, Λz, fun m hm => ?_⟩
  obtain ⟨M, F, -, -, -, -, -, -, hchain⟩ := ht m hm
  have : ConnectedSpace (Wseq m).Carrier := (hf m).connected
  have : Nonempty M.X := ⟨M.ψ.symm (Classical.arbitrary (Wseq m).Carrier)⟩
  obtain ⟨sel, hsel⟩ := exists_gafSelection_RGC F.family.toLocalChartPackets
  obtain ⟨C, hC, -⟩ := hchain sel hsel
  exact ⟨M, F, sel, hsel, C, hC⟩

end DifferentialGeometry.Geometry.Collapse
