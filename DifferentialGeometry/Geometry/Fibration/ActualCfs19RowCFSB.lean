import DifferentialGeometry.Geometry.Fibration.ActualCfs2223RowCFSB
import DifferentialGeometry.Geometry.Fibration.ActualStageCloudInputs
import DifferentialGeometry.Geometry.Fibration.ActualEdgeSupportLink
import DifferentialGeometry.Geometry.Metric.CloudGateTubeRow
import Mathlib.Topology.UrysohnsLemma

/-!
# CFS19 on the actual data: threshold gates and fixed-data support stability at every stage

Blueprint `master207B.tex`, CFS19 (`prop:fibration-cutoff-gate-stability`, B:3053–3115). On the
actual packets with `M = X` compact, `F = 𝓔⁰` (smooth, CGP01), `ρ` (Lipschitz), the ACTUAL stage
cutoffs `ψ₁` (CFS31's source cutoff), `ψ₂` (CFS23, on `O = {x_ρ > 0}`), `ψ₃` (CFS22) and the
ORIGINAL open threshold-`7` cores `A₁, A₂, A₃` (strict inequalities on the open chart balls):

* the gate: a continuous `G` with `supp_O ψ ⊆ {G ≥ 1/2}` and `G ∘ F = 0` off `A` exists, because
  the actual cutoffs localize the ORIGINAL point on their closed supports
  (`cfs19_gate_CFSB`, Urysohn on the compact `F(M \ A)` and the closed support);
* FIXED-DATA existence: `κ > 0` (`κ ≤ 3Σ_st/10`) such that EVERY `f` with `|f − F| ≤ κρ` has image
  in `O`, `f(p) ∈ supp_O ψ ⇒ p ∈ A`, and then, by CFS16 (full markers on the actual clouds, (AS) at
  positive markers, the chain's selections), `π_st f(p)` lies in the half-tube of the original
  centre;
  `f(M) ∩ supp_O ψ ⊆ π_st⁻¹ N_r(S_st)` with `r = Σ_st ρ ∘ sel`; and CFS18 supplies the smooth
  adjustment on an open neighbourhood of `f(M)`.

Main theorems: `Gaf02Chain.cfs19_row_CFSB` (any actual stage `st`, any cutoff that localizes the
original point to an open `A` whose projection lies in `S_st`) and its instances
`cfs19_first_CFSB`, `cfs19_edge_CFSB`, `cfs19_slim_CFSB` at the three actual cutoffs.
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

/-- **CFS19's gate from closed-support localization** (Urysohn): if `F(p) ∈ T` (`T` closed) forces
`p ∈ A` (`A` open in the compact `M`), some continuous `G` is `≥ 1/2` on `T` and vanishes on `F`
off `A`. -/
theorem cfs19_gate_CFSB {M H : Type*} [TopologicalSpace M] [CompactSpace M]
    [NormedAddCommGroup H] (F : M → H) (hF : Continuous F) (A : Set M)
    (hA : IsOpen A) (T : Set H) (hT : IsClosed T) (hloc : ∀ p, F p ∈ T → p ∈ A) :
    ∃ G : H → ℝ, Continuous G ∧ T ⊆ {z | (1 / 2 : ℝ) ≤ G z} ∧ ∀ p ∉ A, G (F p) = 0 := by
  have hK : IsClosed (F '' Aᶜ) := (hA.isClosed_compl.isCompact.image hF).isClosed
  have hd : Disjoint (F '' Aᶜ) T := by
    rw [Set.disjoint_left]
    rintro _ ⟨p, hp, rfl⟩ hpT
    exact hp (hloc p hpT)
  obtain ⟨G, hG0, hG1, -⟩ := exists_continuous_zero_one_of_isClosed hK hT hd
  refine ⟨G, G.continuous, fun z hz => ?_, fun p hp => hG0 ⟨p, hp, rfl⟩⟩
  have h1 : G z = 1 := hG1 hz
  exact (by rw [h1]; norm_num : (1 / 2 : ℝ) ≤ G z)

namespace Gaf02Chain

variable {X : Type} [mX : MetricSpace X] [ChartedSpace E3 X] [IsManifold 𝓘(ℝ, E3) ∞ X]
  [CompactSpace X] {g : SmoothRiemannianMetric 𝓘(ℝ, E3) X}
  {hmetric : ∀ a b : X, riemannianEDistOf g a b = ENNReal.ofReal (dist a b)}
  {ρ : X → ℝ} {hρ : ∀ p, 0 < ρ p} {Λ : ℝ} {β : ℕ → ℝ} {Δ σs : ℝ} {K : ℕ}
  {σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V : ℝ}
  {P : LocalChartPackets X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V}
  {Kj : ℕ} {Ξ Γ S eg c cw : Fin 3 → ℝ}

/-- `𝓔⁰` is continuous on the chain's family (CGP01, the margin from packet (iv)). -/
theorem continuous_globalMap_CFSB (C : Gaf02Chain P Kj Ξ Γ S eg c cw) :
    Continuous (cgpGlobalMap P.toLocalChartFamily P.zero) := by
  obtain ⟨hΛ, hΔ, hμ, hτ, hLΛ, -, he, -⟩ := C.std
  have hΔ0 : 0 < Δ := by linarith
  have hΔΛ : 100 * Δ * Λ ≤ 1 / 100 := by nlinarith
  exact (cgp01_rowE P.toLocalChartFamilyE P.zero hΛ hΔ0 hμ hτ hΔΛ (by linarith)).continuous

open Classical in
/-- The stage selection extended to all of `X`: the chain's selection over `S̃_st`, `p` itself
elsewhere; it is a preimage selection for `π_st ∘ 𝓔⁰` everywhere. -/
def cfs19Sel_CFSB (C : Gaf02Chain P Kj Ξ Γ S eg c cw) (st : Fin 3) (p : X) : X :=
  if (gafStageQ P.toLocalChartFamily P.zero st).starProjection
      (cgpGlobalMap P.toLocalChartFamily P.zero p) ∈ gafCloudEnlarged P.toLocalChartFamily P.zero st
  then C.sel st ((gafStageQ P.toLocalChartFamily P.zero st).starProjection
    (cgpGlobalMap P.toLocalChartFamily P.zero p)) else p

theorem cfs19Sel_spec_CFSB (C : Gaf02Chain P Kj Ξ Γ S eg c cw) (st : Fin 3) (p : X) :
    (gafStageQ P.toLocalChartFamily P.zero st).starProjection
        (cgpGlobalMap P.toLocalChartFamily P.zero (C.cfs19Sel_CFSB st p)) =
      (gafStageQ P.toLocalChartFamily P.zero st).starProjection
        (cgpGlobalMap P.toLocalChartFamily P.zero p) := by
  classical
  unfold cfs19Sel_CFSB
  split_ifs with h
  · rw [gafStageQ_starProjection_globalMap]
    exact C.hsel st _ h
  · rfl

open Classical in
/-- **CFS19** (`prop:fibration-cutoff-gate-stability`) at an actual stage `st` of the chain, for a
cutoff `ψ` smooth on an open `O ∋ F(M)` whose closed support localizes the ORIGINAL point to an open
`A ⊆ X` with `π_st F(A) ⊆ S_st`: there is `κ > 0`, `κ ≤ 3Σ_st/10`, such that every `f` with
`|f − F| ≤ κρ` maps into `O`, `f(p) ∈ supp_O ψ ⇒ p ∈ A` with `π_st f(p)` in the CFS16 half-tube of
the original centre, `f(M) ∩ supp_O ψ ⊆ π_st⁻¹ N_r(S)` (`r = Σ_st ρ ∘ sel`), and CFS18's adjustment
by any
field smooth on `O ∩` tube is smooth on an open neighbourhood `V ⊆ O` of `f(M)`. -/
theorem cfs19_row_CFSB (C : Gaf02Chain P Kj Ξ Γ S eg c cw) (st : Fin 3)
    (ψ : BlockSpace (fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²) → ℝ)
    {O : Set (BlockSpace (fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²))} (hO : IsOpen O)
    (hFO : ∀ p, cgpGlobalMap P.toLocalChartFamily P.zero p ∈ O) (hψ : ContDiffOn ℝ ∞ ψ O)
    (A : Set X) (hA : IsOpen A)
    (hAS : ∀ p ∈ A, (gafStageQ P.toLocalChartFamily P.zero st).starProjection
      (cgpGlobalMap P.toLocalChartFamily P.zero p) ∈ gafCloud P.toLocalChartFamily P.zero st)
    (hloc0 : ∀ p, cgpGlobalMap P.toLocalChartFamily P.zero p ∈ tsupport ψ → p ∈ A) :
    ∃ κ : ℝ, 0 < κ ∧ κ ≤ 3 * S st / 10 ∧
      ∀ f : X → BlockSpace (fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²),
        (∀ p, ‖f p - cgpGlobalMap P.toLocalChartFamily P.zero p‖ ≤ κ * ρ p) →
      (∀ p, f p ∈ O) ∧
      (∀ p, f p ∈ closure (support ψ ∩ O) → p ∈ A ∧
        ‖(gafStageQ P.toLocalChartFamily P.zero st).starProjection (f p) -
            (gafStageQ P.toLocalChartFamily P.zero st).starProjection
              (cgpGlobalMap P.toLocalChartFamily P.zero p)‖ ≤
          S st * ρ (C.cfs19Sel_CFSB st p) / 2 ∧
        ball ((gafStageQ P.toLocalChartFamily P.zero st).starProjection (f p))
            (S st * ρ (C.cfs19Sel_CFSB st p) / 2) ⊆
          ball ((gafStageQ P.toLocalChartFamily P.zero st).starProjection
            (cgpGlobalMap P.toLocalChartFamily P.zero p)) (S st * ρ (C.cfs19Sel_CFSB st p))) ∧
      range f ∩ (closure (support ψ ∩ O) ∩ O) ⊆
        cfsProjectedTube (gafStageQ P.toLocalChartFamily P.zero st).starProjection
          (cgpGlobalMap P.toLocalChartFamily P.zero) A (fun p => S st * ρ (C.cfs19Sel_CFSB st p)) ∧
      ∀ k : BlockSpace (fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²) →
          BlockSpace (fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²),
        ContDiffOn ℝ ∞ k (O ∩ cfsProjectedTube
          (gafStageQ P.toLocalChartFamily P.zero st).starProjection
          (cgpGlobalMap P.toLocalChartFamily P.zero) A (fun p => S st * ρ (C.cfs19Sel_CFSB st p))) →
        ∃ W : Set (BlockSpace (fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²)), IsOpen W ∧
          range f ⊆ W ∧ W ⊆ O ∧
          closure (support ψ ∩ W) ∩ W ⊆
            cfsProjectedTube (gafStageQ P.toLocalChartFamily P.zero st).starProjection
              (cgpGlobalMap P.toLocalChartFamily P.zero) A
              (fun p => S st * ρ (C.cfs19Sel_CFSB st p)) ∧
          ContDiffOn ℝ ∞ ((cfsProjectedTube
              (gafStageQ P.toLocalChartFamily P.zero st).starProjection
              (cgpGlobalMap P.toLocalChartFamily P.zero) A
              (fun p => S st * ρ (C.cfs19Sel_CFSB st p))).piecewise
            (fun z => z + ψ z • k z) id) W ∧
          (∀ z ∈ W, z ∉ cfsProjectedTube (gafStageQ P.toLocalChartFamily P.zero st).starProjection
              (cgpGlobalMap P.toLocalChartFamily P.zero) A
              (fun p => S st * ρ (C.cfs19Sel_CFSB st p)) → ψ z = 0) := by
  obtain ⟨hΛ, hΔ, -, -, hLΛ, -, -, -, -, -, -⟩ := C.std
  obtain ⟨hnum, -⟩ := C.numbers
  obtain ⟨-, hsg, -, -⟩ := hnum st
  have hsmall : Λ * (1000000 * Δ) ≤ 1 / 4 := by nlinarith
  have hF := C.continuous_globalMap_CFSB
  have hρc : Continuous ρ := P.lipschitz_scale.continuous
  obtain ⟨G, hG, hgate, hout⟩ := cfs19_gate_CFSB (cgpGlobalMap P.toLocalChartFamily P.zero) hF A
    hA (closure (support ψ ∩ O)) isClosed_closure
    (fun p hp => hloc0 p (closure_mono inter_subset_left hp))
  exact cfs19_row O hO (cgpGlobalMap P.toLocalChartFamily P.zero) hFO hF ρ hρc hρ A hA G ψ
    hG.continuousOn hψ (fun z hz => hgate hz.1) hout
    (gafStageQ P.toLocalChartFamily P.zero st).starProjection
    (Submodule.starProjection_norm_le _)
    (fun a z => blockMarkerCLM (cgpMarkerTag P.toLocalChartFamily P.zero a) z)
    (fun a => ρ (cgpMarkerCentre P.toLocalChartFamily a)) (fun _ => hρ _)
    (fun a p hp => gafStage_support_GAF4 P.toLocalChartFamily P.zero hΔ hΛ hsmall st a p hp)
    (fun p hp => gafStage_fullS_GAF5 P hΔ hΛ hLΛ st p (hAS p hp)) (C.cfs19Sel_CFSB st)
    (C.cfs19Sel_spec_CFSB st) hsg

end Gaf02Chain

end DifferentialGeometry.Geometry.Collapse
