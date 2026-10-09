import DifferentialGeometry.Geometry.Fibration.ActualStageChainE

/-!
# FC33's first clause on the chain: `E = Ψ₃Ψ₂Ψ₁𝓔⁰` with `|E − 𝓔⁰| < c_adj ρ`, `‖DE − D𝓔⁰‖ < c_adj`

Blueprint `master207B.tex`, FC33 (`found:fibration-final-bases`, B:2873–2886): "Deliver KL 13.1
with `𝓔 = Ψ₃Ψ₂Ψ₁𝓔⁰`, `|𝓔(p) − 𝓔⁰(p)| < c_adjust ρ(p)`, `‖D𝓔 − D𝓔⁰‖ < c_adjust`. There are
embedded bases `W_j ⊂ Q_j` …". This module proves the FIRST clause on the chain object of GAF02
(`Gaf02Chain`, produced on every packet of the final family on GAF01's single choice by
`gaf01_full_row_RFC`, whose clause (2) gives `c₃ < c_adjust`):

* `Gaf02Chain.fc33_adjusted_RFC`: for `c₃ < c_adj`, `E = Ψ₃ ∘ Ψ₂ ∘ Ψ₁ ∘ 𝓔⁰` (definitional), `E`
  is smooth, `‖E(p) − 𝓔⁰(p)‖ < c_adj ρ(p)` and `‖dE w − d𝓔⁰ w‖ ≤ H √g(w, w)` with `H < c_adj`.
* Consumer `Gaf02ChainE.fc33_adjusted_RFC` (the same on the chain on the enhanced planes).

The bases clause (embedded `W_j ⊂ Q_j` of dimensions `2, 1, 1` and the submersions
`π_jE : U_j → W_j` on the exact threshold-`5` domains) is GAF02's BASES part (lanes C14-BASESb,
BASES-P; `Gaf02Bases`, `gaf02_bases_row_BAS`), not proved here.
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

variable {X : Type} [mX : MetricSpace X] [ChartedSpace E3 X] [IsManifold 𝓘(ℝ, E3) ∞ X]
  [CompactSpace X] {g : SmoothRiemannianMetric 𝓘(ℝ, E3) X}
  {hmetric : ∀ a b : X, riemannianEDistOf g a b = ENNReal.ofReal (dist a b)}
  {ρ : X → ℝ} {hρ : ∀ p, 0 < ρ p} {Λ : ℝ} {β : ℕ → ℝ} {Δ σs : ℝ} {K : ℕ}
  {σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V vs ζ Λz : ℝ}

/-- **FC33, first clause** (B:2875–2879) on the chain: for `c₃ < c_adj`, the final map
`E = Ψ₃ ∘ Ψ₂ ∘ Ψ₁ ∘ 𝓔⁰` is smooth, `‖E − 𝓔⁰‖ < c_adj ρ` and its derivative error is bounded by
some `H < c_adj` in the norm of `g`. -/
theorem Gaf02Chain.fc33_adjusted_RFC
    {P : LocalChartPackets X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V}
    {Kj : ℕ} {Ξ Γ S eg c cw : Fin 3 → ℝ} (C : Gaf02Chain P Kj Ξ Γ S eg c cw) {cadj : ℝ}
    (hc : c 2 < cadj) :
    C.E = C.Ψ₃ ∘ C.Ψ₂ ∘ C.Ψ₁ ∘ cgpGlobalMap P.toLocalChartFamily P.zero ∧
      ContMDiff 𝓘(ℝ, E3) 𝓘(ℝ, BlockSpace (fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²)) ∞
        C.E ∧
      (∀ p, ‖C.E p - cgpGlobalMap P.toLocalChartFamily P.zero p‖ < cadj * ρ p) ∧
      ∃ Hd : ℝ, Hd < cadj ∧ ∀ p w, ‖mvfderiv 𝓘(ℝ, E3) C.E p w -
        mvfderiv 𝓘(ℝ, E3) (cgpGlobalMap P.toLocalChartFamily P.zero) p w‖ ≤
          Hd * Real.sqrt (g.inner p w w) := by
  obtain ⟨Hd, hHd, hD⟩ := C.stage_derivative_lt.2.2
  exact ⟨rfl, C.stage_smooth.2.2, fun p => (C.stage_error_lt.2.2 p).trans_le
    (mul_le_mul_of_nonneg_right hc.le (hρ p).le), Hd, hHd.trans hc, hD⟩

/-- **Consumer**: FC33's first clause for the chain on the enhanced planes (`Ĉ.E = Ĉ.toChain.E`). -/
theorem Gaf02ChainE.fc33_adjusted_RFC
    {P : LocalChartPacketsC14 X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T
      V vs ζ Λz} {Kj : ℕ} {Ξ Γ S eg c cw : Fin 3 → ℝ} (C : Gaf02ChainE P Kj Ξ Γ S eg c cw)
    {cadj : ℝ} (hc : c 2 < cadj) :
    ContMDiff 𝓘(ℝ, E3) 𝓘(ℝ, BlockSpace (fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²)) ∞
        C.E ∧
      (∀ p, ‖C.E p - cgpGlobalMap P.toLocalChartFamily P.zero p‖ < cadj * ρ p) ∧
      ∃ Hd : ℝ, Hd < cadj ∧ ∀ p w, ‖mvfderiv 𝓘(ℝ, E3) C.E p w -
        mvfderiv 𝓘(ℝ, E3) (cgpGlobalMap P.toLocalChartFamily P.zero) p w‖ ≤
          Hd * Real.sqrt (g.inner p w w) :=
  (C.toChain.fc33_adjusted_RFC hc).2

end DifferentialGeometry.Geometry.Collapse
