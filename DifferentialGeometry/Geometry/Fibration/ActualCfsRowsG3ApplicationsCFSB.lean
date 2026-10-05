import DifferentialGeometry.Geometry.Fibration.ActualCfs28RowCFSB
import DifferentialGeometry.Geometry.Fibration.ActualCfs29RowCFSB
import DifferentialGeometry.Geometry.Fibration.ActualCfs24RowCFSB

/-!
# Consumers of CFS28 and CFS29: CFS28 feeds CFS24's (ZL) for whole blocks

* `blockRestrict_singleton_eq_zero_CFSB`: `π_{t} w = 0 ↔ w_t = 0`.
* `Gaf02ChainE.cfs28_to_cfs24_CFSB`: on the enhanced chain, CFS28 verifies EVERY centre and plane
  hypothesis (ZL) of CFS24 for the whole-block projection `π_{t}` of a small block
  (`R_i < ρ(p)/16`) at `x = π_st𝓔⁰(p)`, so the stage projection `π_st ∘ a_st` has zero `i` block on
  `B(x, r_x)` — the mechanism of CFS29.
-/

set_option autoImplicit false

noncomputable section

open Set Function Metric Bundle Manifold Filter
open scoped ContDiff Manifold Topology
open DifferentialGeometry.Geometry.Riemannian GC.MetricGeometry
open DifferentialGeometry.Analysis

namespace DifferentialGeometry.Geometry.Collapse

local notation "E3" => EuclideanSpace ℝ (Fin 3)
local notation "ℝ²" => EuclideanSpace ℝ (Fin 2)

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace

attribute [local instance] LocalChartPackets.instMetricN LocalChartPackets.instChartedN
  LocalChartPackets.instMetricC

/-- The coordinate projection onto one block vanishes if that block does. -/
theorem blockRestrict_singleton_eq_zero_CFSB {κ : Type*} [Finite κ] [DecidableEq κ] (t : κ)
    (w : BlockSpace (fun _ : κ => ℝ²)) (hw : w t = 0) :
    blockRestrict {t} w = 0 := by
  have := Fintype.ofFinite κ
  refine PiLp.ext fun s => ?_
  rw [blockRestrict_apply]
  split_ifs with hs
  · rw [Finset.mem_singleton.mp hs, hw]
    rfl
  · rfl

namespace Gaf02ChainE

variable {X : Type} [MetricSpace X] [ChartedSpace E3 X]
  [IsManifold 𝓘(ℝ, E3) ∞ X] [CompactSpace X] {g : SmoothRiemannianMetric 𝓘(ℝ, E3) X}
  {hmetric : ∀ a b : X, riemannianEDistOf g a b = ENNReal.ofReal (dist a b)}
  {ρ : X → ℝ} {hρ : ∀ p, 0 < ρ p} {Λ : ℝ} {β : ℕ → ℝ} {Δ σs : ℝ} {K : ℕ}
  {σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V vs ζ Λz : ℝ}
  {P : LocalChartPacketsC14 X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T
    V vs ζ Λz} {Kj : ℕ} {Ξ Γ S eg c cw : Fin 3 → ℝ}

open Classical in
/-- **CFS28 → CFS24** on the enhanced chain: for an active stage output `O`, a core point
`x = π_st𝓔⁰(p) ∈ S_st` and a retained block `i` with `R_i < ρ(p)/16`, (ZL) holds for the whole
block projection `π_{t}` (`t` the tag of `i`) on the whole contributor window of `x`, hence the
stage projection has zero `i` block on `B(x, r_x)`. -/
theorem cfs28_to_cfs24_CFSB (C : Gaf02ChainE P Kj Ξ Γ S eg c cw) (st : Fin 3)
    (O : Cfs15StageOutput (gafStageDim st) Kj (Ξ st) (cw st)
      (gafCloud P.toLocalChartFamily P.zero st) (gafCloudEnlarged P.toLocalChartFamily P.zero st)
      (fun x => S st * ρ (C.toChain.sel st x)) (C.toChain.plane st))
    (hO : C.toChain.slot st = .active O) {p : X}
    {x : BlockSpace (fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²)}
    (hpx : cgpProjMap P.toLocalChartFamily P.zero (gafStageTags P.toLocalChartFamily P.zero st) p =
      x) (hx : x ∈ gafCloud P.toLocalChartFamily P.zero st)
    (i : CGPMarkerIndex P.toLocalChartFamily)
    (hi : ρ (cgpMarkerCentre P.toLocalChartFamily i) < ρ p / 16) :
    ∀ z ∈ ball x (S st * ρ (C.toChain.sel st x)),
      blockRestrict {cgpMarkerTag P.toLocalChartFamily P.zero i}
        ((gafStageQ P.toLocalChartFamily P.zero st).starProjection ((C.toChain.slot st).map z)) =
        0 := by
  have hZL : ∀ u ∈ O.I, (closedBall u (80 * (Ξ st)⁻¹ * (S st * ρ (C.toChain.sel st u))) ∩
      ball x (8 * (Ξ st)⁻¹ * (S st * ρ (C.toChain.sel st x)))).Nonempty →
      blockRestrict {cgpMarkerTag P.toLocalChartFamily P.zero i} u = 0 ∧
        C.toChain.plane st u ≤ LinearMap.ker
          ((blockRestrict (V := fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²)
            {cgpMarkerTag P.toLocalChartFamily P.zero i} :
            BlockSpace (fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²) →L[ℝ]
              BlockSpace (fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²)) :
            BlockSpace (fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²) →ₗ[ℝ]
              BlockSpace (fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²)) := by
    intro u hu hmeet
    have h := C.cfs28_row_CFSB st hpx hx (O.I_subset hu) hmeet i hi
    refine ⟨blockRestrict_singleton_eq_zero_CFSB _ u h.1, fun w hw => ?_⟩
    exact blockRestrict_singleton_eq_zero_CFSB _ w (h.2 w hw)
  exact (cfs24_row_CFSB C.toChain st O hO {cgpMarkerTag P.toLocalChartFamily P.zero i} hx
    hZL).2.2.1

end Gaf02ChainE

end DifferentialGeometry.Geometry.Collapse
