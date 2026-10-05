import DifferentialGeometry.Geometry.Fibration.ActualCfs24RowCFSB
import DifferentialGeometry.Geometry.Fibration.ActualCfs26RowCFSB
import DifferentialGeometry.Geometry.Collapse.LocalExport.LocalChartPacketsC14ZeroTypes

/-!
# Consumers of CFS24 and CFS26 on the actual data

* `cfs26_row_C14Z_CFSB`: CFS26 on the final closed family `LocalChartPacketsC14Z` (through its
  projection to `LocalChartPackets`).
* `Gaf02Chain.cfs26_CFSB`: CFS26's hypotheses read off the chain object (`C.std`), so every chain
  carries the support-scale bounds of its own family.
* `Gaf02Chain.cfs24_stage_CFSB`: CFS24 at the chain's OWN stage maps `Ψ₁, Ψ₂, Ψ₃` (the blended
  adjustments with the actual cutoffs `ψ₁, ψ₂, ψ₃`) keeps a zero coordinate.
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

variable {X : Type} [mX : MetricSpace X] [ChartedSpace E3 X] [IsManifold 𝓘(ℝ, E3) ∞ X]
  [CompactSpace X] {g : SmoothRiemannianMetric 𝓘(ℝ, E3) X}
  {hmetric : ∀ a b : X, riemannianEDistOf g a b = ENNReal.ofReal (dist a b)}
  {ρ : X → ℝ} {hρ : ∀ p, 0 < ρ p} {Λ : ℝ} {β : ℕ → ℝ} {Δ σs : ℝ} {K : ℕ}
  {σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V vs ζ Λz : ℝ}

/-- **CFS26 on the final closed family** `LocalChartPacketsC14Z`: the support-scale bounds (AS)
on the domains and closed supports, full markers on cores and enlarged stage clouds, the
`[3/5, 5/3]` ratio for ANY two preimages, and the first clause of CFS07. -/
theorem cfs26_row_C14Z_CFSB {oM : ManifoldOrientation 𝓘(ℝ, E3) X 3}
    (P : LocalChartPacketsC14Z X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T
      V vs ζ Λz oM)
    (hΔ : 1 ≤ Δ) (hΛ : 0 ≤ Λ) (hsmall : Λ * (1000000 * Δ) ≤ 1 / 4) (hσs : 0 ≤ σs)
    (hσs1 : σs ≤ 1 / 100) :
    (∀ a : CGPMarkerIndex P.toLocalChartFamily,
      ∀ q ∈ closedBall (cgpMarkerCentre P.toLocalChartFamily a)
        (cgpMarkerDomain P.toLocalChartFamily a * ρ (cgpMarkerCentre P.toLocalChartFamily a)),
      3 * ρ (cgpMarkerCentre P.toLocalChartFamily a) / 4 ≤ ρ q ∧
        ρ q ≤ 5 * ρ (cgpMarkerCentre P.toLocalChartFamily a) / 4) ∧
    (∀ st, ∀ x ∈ gafCloudEnlarged P.toLocalChartFamily P.zero st, ∀ q q' : X,
      cgpProjMap P.toLocalChartFamily P.zero (gafStageTags P.toLocalChartFamily P.zero st) q = x →
      cgpProjMap P.toLocalChartFamily P.zero (gafStageTags P.toLocalChartFamily P.zero st) q' =
        x →
      3 / 5 * ρ q ≤ ρ q' ∧ ρ q' ≤ 5 / 3 * ρ q) := by
  have h := cfs26_row_CFSB P.toLocalChartPackets hΔ hΛ hsmall hσs hσs1
  exact ⟨h.1, h.2.2.2.2.2.1⟩

namespace Gaf02Chain

variable {P : LocalChartPackets X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc Lmax τ γ δ εr e
    T V}
  {Kj : ℕ} {Ξ Γ S eg c cw : Fin 3 → ℝ}

/-- CFS26 for the family of a chain: every hypothesis is read off `C.std`. -/
theorem cfs26_CFSB (C : Gaf02Chain P Kj Ξ Γ S eg c cw) :
    (∀ a p, 0 < cgpMarker P.toLocalChartFamily P.zero a
        (cgpGlobalMap P.toLocalChartFamily P.zero p) →
      3 * ρ (cgpMarkerCentre P.toLocalChartFamily a) / 4 ≤ ρ p ∧
        ρ p ≤ 5 * ρ (cgpMarkerCentre P.toLocalChartFamily a) / 4) ∧
    (∀ st, ∀ x ∈ gafCloudEnlarged P.toLocalChartFamily P.zero st,
      ∃ a : CGPMarkerIndex P.toLocalChartFamily,
        blockMarkerCLM (cgpMarkerTag P.toLocalChartFamily P.zero a) x =
          ρ (cgpMarkerCentre P.toLocalChartFamily a)) := by
  obtain ⟨hΛ, hΔ, -, -, -, -, -, -, hσs, hσs1, -⟩ := C.std
  have h := cfs26_row_CFSB P hΔ hΛ C.small_BAS hσs hσs1
  exact ⟨h.2.2.1, h.2.2.2.2.1⟩

open Classical in
/-- CFS24 at the chain's own stage maps: if the slot of stage `st` is the output `O` and (ZL)
holds for `π_T` on the contributor window of `x ∈ S_st`, then `Ψ₁` (stage `0`), `Ψ₂` (stage `1`)
and `Ψ₃` (stage `2`) keep `π_T z = 0` at every input with `π_{Q_st} z ∈ B(x, r_x)`. -/
theorem cfs24_stage_CFSB (C : Gaf02Chain P Kj Ξ Γ S eg c cw) (st : Fin 3)
    (O : Cfs15StageOutput (gafStageDim st) Kj (Ξ st) (cw st)
      (gafCloud P.toLocalChartFamily P.zero st) (gafCloudEnlarged P.toLocalChartFamily P.zero st)
      (fun x => S st * ρ (C.sel st x)) (C.plane st))
    (hO : C.slot st = .active O) (Tg : Finset (CGPTag P.toLocalChartFamily P.zero))
    {x : BlockSpace (fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²)}
    (hx : x ∈ gafCloud P.toLocalChartFamily P.zero st)
    (hZL : ∀ i ∈ O.I, (closedBall i (80 * (Ξ st)⁻¹ * (S st * ρ (C.sel st i))) ∩
        ball x (8 * (Ξ st)⁻¹ * (S st * ρ (C.sel st x)))).Nonempty →
      blockRestrict Tg i = 0 ∧ C.plane st i ≤ LinearMap.ker
        ((blockRestrict (V := fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²) Tg :
          BlockSpace (fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²) →L[ℝ]
            BlockSpace (fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²)) :
          BlockSpace (fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²) →ₗ[ℝ]
            BlockSpace (fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²)))
    (z : BlockSpace (fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²))
    (hz : (gafStageQ P.toLocalChartFamily P.zero st).starProjection z ∈
      ball x (S st * ρ (C.sel st x))) (hTz : blockRestrict Tg z = 0) :
    blockRestrict Tg (![C.Ψ₁, C.Ψ₂, C.Ψ₃] st z) = 0 := by
  have h := (cfs24_row_CFSB C st O hO Tg hx hZL).2.2.2
  fin_cases st
  · exact h _ z hz hTz
  · exact h _ z hz hTz
  · exact h _ z hz hTz

end Gaf02Chain

end DifferentialGeometry.Geometry.Collapse
