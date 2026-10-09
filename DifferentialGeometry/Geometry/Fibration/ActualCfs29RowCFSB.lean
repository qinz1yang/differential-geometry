import DifferentialGeometry.Geometry.Fibration.ActualStageChainPlateau
import DifferentialGeometry.Geometry.Fibration.ActualStageChainWitness
import DifferentialGeometry.Geometry.Fibration.ActualStageNearMarkers
import DifferentialGeometry.Geometry.Fibration.ActualStageCloudInputsApplications
import DifferentialGeometry.Geometry.Metric.ActualCloudStagePreservation

/-!
# CFS29 on the actual stage maps of the GAF02 chain

Blueprint `master207B.tex`, CFS29 (`lem:fibration-small-marker-preservation`, B:3733–3755). Each
stage of the chain `C : Gaf02Chain P …` is constructed with the (PP) planes of the stage tests,
the CFS15 smoothing (the slot's native output), `128 Ξ_st⁻¹ Σ_st ≤ 1/5` (so
`Σ_st ≤ 1/(640 b_st)`, `b_st = Ξ_st⁻¹`), and its blended adjustment is
`Ψ_st = adjustmentMap Q_st (π_{Q_st} ∘ a_st) ψ_st`. For an ARBITRARY input map `f` whose cutoff
localizes the original point to the stage cloud on its closed support and whose value error is at
most `3Σ_stρ(p)/10`: if `f` has zero `a` marker whenever `ζ_a(p) = 0` and `R_a < ρ(p)/16`, so has
`Ψ_st ∘ f` (threshold with the ORIGINAL `ρ(p)`; no condition on the scale coordinate of `f`).

* `starProjection_kerOrth_eq_zero_iff_CFSB`: `π_{(ker v)ᗮ} w = 0 ↔ v w = 0` (scalar markers).
* `cfs29_scalar_step_CFSB`: the scalar-marker form of `actualCloud_stage_small_marker_preservation`.
* **`Gaf02Chain.cfs29_row_CFSB`** (the row on the chain's stage maps, any input `f`).
* `Gaf02Chain.cfs29_chain_CFSB`: the induction along the chain's own `g₀ = 𝓔⁰, g₁, g₂, E`.
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

section Kernel

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [FiniteDimensional ℝ H]

/-- The projection onto the line `(ker v)ᗮ` of a scalar marker `v` vanishes iff `v` does. -/
theorem starProjection_kerOrth_eq_zero_iff_CFSB {v : H →L[ℝ] ℝ} {w : H} :
    (LinearMap.ker (v : H →ₗ[ℝ] ℝ))ᗮ.starProjection w = 0 ↔ v w = 0 := by
  rw [Submodule.starProjection_apply_eq_zero_iff, Submodule.orthogonal_orthogonal,
    LinearMap.mem_ker]
  rfl

/-- **CFS29, one stage, scalar markers** (kernel form): a stage `adjustmentMap Q Pst ψ` with CFS16's
data and the stage projection's small-marker locality `hnear` keeps every small marker
(`R_i < ρ(q)/16`, original `ρ`) of an input `f` equal to zero. -/
theorem cfs29_scalar_step_CFSB {M A : Type*}
    (Q : Submodule ℝ H) (Pst : H → H) (hP : ∀ z, Pst z ∈ Q) (ψ : H → ℝ)
    (F f : M → H) (ρ : M → ℝ) (v : A → H →L[ℝ] ℝ) (R : A → ℝ) (hR : ∀ i, 0 < R i)
    (hsupport : ∀ i q, 0 < v i (Q.starProjection (F q)) →
      3 * R i / 4 ≤ ρ q ∧ ρ q ≤ 5 * R i / 4)
    (hfull : ∀ q, ψ (f q) ≠ 0 → ∃ i, v i (Q.starProjection (F q)) = R i)
    (S : Set H) (select : H → M) (hselect : ∀ x ∈ S, Q.starProjection (F (select x)) = x)
    {σ e : ℝ} (hσ : 0 < σ) (he : e ≤ 3 * σ / 10)
    (hloc : ∀ q, ψ (f q) ≠ 0 → Q.starProjection (F q) ∈ S)
    (herror : ∀ q, ψ (f q) ≠ 0 → ‖f q - F q‖ ≤ e * ρ q)
    (hnear : ∀ x ∈ S, ∀ z ∈ ball x (σ * ρ (select x)), ∀ q, Q.starProjection (F q) = x →
      ∀ i, R i < ρ q / 16 → v i (Pst z) = 0)
    (hretained : ∀ i, (LinearMap.ker (v i : H →ₗ[ℝ] ℝ))ᗮ ≤ Q ∨
      (LinearMap.ker (v i : H →ₗ[ℝ] ℝ))ᗮ ≤ Qᗮ)
    (hinput : ∀ q i, R i < ρ q / 16 → v i (f q) = 0) :
    ∀ q i, R i < ρ q / 16 → v i (adjustmentMap Q Pst ψ (f q)) = 0 := by
  intro q i hi
  have h := actualCloud_stage_small_marker_preservation Q Pst hP ψ F f ρ
    (fun i => (LinearMap.ker (v i : H →ₗ[ℝ] ℝ))ᗮ) (fun i y => v i y) R hR hsupport hfull S select
    hselect hσ he hloc herror
    (fun x hx z hz q hq i hi => (starProjection_kerOrth_eq_zero_iff_CFSB (v := v i)).mpr
      (hnear x hx z hz q hq i hi)) hretained
    (fun q i hi => (starProjection_kerOrth_eq_zero_iff_CFSB (v := v i)).mpr (hinput q i hi)) q i hi
  exact (starProjection_kerOrth_eq_zero_iff_CFSB (v := v i)).mp h

end Kernel

namespace Gaf02Chain

variable {X : Type} [mX : MetricSpace X] [ChartedSpace E3 X] [IsManifold 𝓘(ℝ, E3) ∞ X]
  [CompactSpace X] {g : SmoothRiemannianMetric 𝓘(ℝ, E3) X}
  {hmetric : ∀ a b : X, riemannianEDistOf g a b = ENNReal.ofReal (dist a b)}
  {ρ : X → ℝ} {hρ : ∀ p, 0 < ρ p} {Λ : ℝ} {β : ℕ → ℝ} {Δ σs : ℝ} {K : ℕ}
  {σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V : ℝ}
  {P : LocalChartPackets X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V}
  {Kj : ℕ} {Ξ Γ S eg c cw : Fin 3 → ℝ}

/-- A retained marker with `R_a < ρ(p)/16` has `ζ_a(p) = 0` (positive markers obey (AS)). -/
theorem small_cutoff_eq_zero_CFSB (C : Gaf02Chain P Kj Ξ Γ S eg c cw)
    (a : CGPMarkerIndex P.toLocalChartFamily) (p : X)
    (ha : ρ (cgpMarkerCentre P.toLocalChartFamily a) < ρ p / 16) :
    cgpMarkerCutoff P.toLocalChartFamily a p = 0 := by
  obtain ⟨hΛ, hΔ, -, -, hLΛ, -, -, -, hσs, hσs1, -⟩ := C.std
  have hdat := gafMarker_data_GAF7 P hΛ hΔ hLΛ hσs hσs1
  refine le_antisymm ?_ (hdat.1 a p)
  by_contra hpos
  have h := hdat.2.2 a p (lt_of_not_ge hpos)
  have hR := hρ (cgpMarkerCentre P.toLocalChartFamily a)
  linarith [h.2]

/-- **CFS29** (`lem:fibration-small-marker-preservation`) on the actual stage `st` of the chain.
For ANY input map `f` such that (i) the stage cutoff localizes the original point on its closed
support (`f p ∈ tsupport ψ_st ⇒ π_st 𝓔⁰ p ∈ S_st`), (ii) the preceding value error is at most
`3Σ_stρ(p)/10`, and (iii) `v_a(f p) = 0` whenever `ζ_a(p) = 0` and `R_a < ρ(p)/16`: the blended
adjustment `Ψ_st ∘ f` has the same property (threshold with the original `ρ(p)`). -/
theorem cfs29_row_CFSB (C : Gaf02Chain P Kj Ξ Γ S eg c cw) (st : Fin 3)
    (f : X → BlockSpace (fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²))
    (hloc : ∀ p, f p ∈ tsupport (gafStageCutoff_BAS P st) →
      (gafStageQ P.toLocalChartFamily P.zero st).starProjection
        (cgpGlobalMap P.toLocalChartFamily P.zero p) ∈ gafCloud P.toLocalChartFamily P.zero st)
    (herr : ∀ p, ‖f p - cgpGlobalMap P.toLocalChartFamily P.zero p‖ ≤ 3 * S st / 10 * ρ p)
    (hin : ∀ p (a : CGPMarkerIndex P.toLocalChartFamily),
      cgpMarkerCutoff P.toLocalChartFamily a p = 0 →
      ρ (cgpMarkerCentre P.toLocalChartFamily a) < ρ p / 16 →
      blockMarkerCLM (cgpMarkerTag P.toLocalChartFamily P.zero a) (f p) = 0) :
    ∀ p (a : CGPMarkerIndex P.toLocalChartFamily),
      cgpMarkerCutoff P.toLocalChartFamily a p = 0 →
      ρ (cgpMarkerCentre P.toLocalChartFamily a) < ρ p / 16 →
      blockMarkerCLM (cgpMarkerTag P.toLocalChartFamily P.zero a)
        (adjustmentMap (gafStageQ P.toLocalChartFamily P.zero st)
          (fun y => (gafStageQ P.toLocalChartFamily P.zero st).starProjection
            ((C.slot st).map y)) (gafStageCutoff_BAS P st) (f p)) = 0 := by
  obtain ⟨hΛ, hΔ, -, -, hLΛ, -, -, -, -, -, -⟩ := C.std
  obtain ⟨hnum, -⟩ := C.numbers
  obtain ⟨hΞ, hsg, hmo, -⟩ := hnum st
  have hin' := gafStage_marker_inputs_GAF5 P hΔ hΛ hLΛ st (C.sel st) (C.hsel st)
  have hnear := gafStage_hnear_GAF4 P hΔ hΛ hLΛ st (C.sel st) (C.hsel st) hsg hΞ hmo (C.plane st)
    (plane_le_ker_marker_BAS C st) (C.slot st).map
    (fun x hx z hz => ((C.slot st).bounds x hx z hz).2.2.2)
  have hsupp : ∀ p, gafStageCutoff_BAS P st (f p) ≠ 0 → f p ∈ tsupport (gafStageCutoff_BAS P st) :=
    fun p hp => subset_tsupport _ hp
  intro p a _ ha
  exact cfs29_scalar_step_CFSB (gafStageQ P.toLocalChartFamily P.zero st)
    (fun y => (gafStageQ P.toLocalChartFamily P.zero st).starProjection ((C.slot st).map y))
    (fun z => Submodule.starProjection_apply_mem _ _) (gafStageCutoff_BAS P st)
    (cgpGlobalMap P.toLocalChartFamily P.zero) f ρ
    (fun a => blockMarkerCLM (V := fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²)
      (cgpMarkerTag P.toLocalChartFamily P.zero a))
    (fun a => ρ (cgpMarkerCentre P.toLocalChartFamily a)) (fun _ => hρ _) hin'.2.1
    (fun q hq => hin'.2.2.1 q (hloc q (hsupp q hq))) (gafCloud P.toLocalChartFamily P.zero st)
    (C.sel st) hin'.2.2.2 hsg le_rfl (fun q hq => hloc q (hsupp q hq)) (fun q _ => herr q)
    hnear hin'.1 (fun q b hb => hin q b (C.small_cutoff_eq_zero_CFSB b q hb) hb) p a ha

/-- **CFS29 along the chain** (the induction of CFS30 / CFS31 started from the original zero
markers): the small markers (`ζ_a(p) = 0`, `R_a < ρ(p)/16`) vanish at `𝓔⁰`, `g₁`, `g₂` and `E`. -/
theorem cfs29_chain_CFSB (C : Gaf02Chain P Kj Ξ Γ S eg c cw) :
    ∀ p (a : CGPMarkerIndex P.toLocalChartFamily),
      cgpMarkerCutoff P.toLocalChartFamily a p = 0 →
      ρ (cgpMarkerCentre P.toLocalChartFamily a) < ρ p / 16 →
      blockMarkerCLM (cgpMarkerTag P.toLocalChartFamily P.zero a)
          (cgpGlobalMap P.toLocalChartFamily P.zero p) = 0 ∧
        blockMarkerCLM (cgpMarkerTag P.toLocalChartFamily P.zero a) (C.g₁ p) = 0 ∧
        blockMarkerCLM (cgpMarkerTag P.toLocalChartFamily P.zero a) (C.g₂ p) = 0 ∧
        blockMarkerCLM (cgpMarkerTag P.toLocalChartFamily P.zero a) (C.E p) = 0 := by
  obtain ⟨hΛ, hΔ, -, -, hLΛ, -, -, -, hσs, hσs1, -⟩ := C.std
  have hdat := gafMarker_data_GAF7 P hΛ hΔ hLΛ hσs hσs1
  have hm := C.stage_small_markers
  intro p a h0 ha
  refine ⟨?_, hm.1 p a ha, hm.2.1 p a ha, hm.2.2 p a ha⟩
  rw [hdat.2.1 a p, h0, mul_zero]

end Gaf02Chain

end DifferentialGeometry.Geometry.Collapse
