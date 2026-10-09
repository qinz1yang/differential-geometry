import DifferentialGeometry.Geometry.Fibration.ActualStageChainEZeroRatio
import DifferentialGeometry.Geometry.Collapse.LocalExport.BoundaryZeroDomainIsotopyBGR

/-!
# ZSP02 on the boundary family (lane B-BCG-ROWS): ZSP02 global linearized definer H_k and its factorization on the thin annulus

GENERATED from `DifferentialGeometry/Geometry/Fibration/ActualStageChainEZeroRatio.lean` by `build-logs/scratch/B-BCG-ROWSb/gen_zsp02.py` (engine B-PORT-A's
`portlib2.py`). Closed family → boundary family (`LocalPacketsOnB`, `ZeroModelFamilyOn`, complete
σ-compact carrier); every ported declaration `x` ↦ `x_BGR`.
-/

set_option autoImplicit false

noncomputable section

open Set Function Metric Bundle Manifold Filter
open scoped ContDiff Manifold Topology
open DifferentialGeometry.Geometry.Riemannian GC.MetricGeometry
open DifferentialGeometry.Geometry.Operator
open DifferentialGeometry.Analysis

namespace DifferentialGeometry.Geometry.Collapse

local notation "E3" => EuclideanSpace ℝ (Fin 3)
local notation "ℝ²" => EuclideanSpace ℝ (Fin 2)

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace

attribute [local instance] nezero_finrank_euclideanThree_LC87

attribute [local instance] LocalChartPackets.instMetricN LocalChartPackets.instChartedN
  LocalChartPackets.instMetricC

section Kernel

variable {X : Type} [mX : MetricSpace X] [ChartedSpace E3 X] [IsManifold 𝓘(ℝ, E3) ∞ X]
  [CompleteSpace X] [SigmaCompactSpace X] {g : SmoothRiemannianMetric 𝓘(ℝ, E3) X}
  {hmetric : ∀ a b : X, riemannianEDistOf g a b = ENNReal.ofReal (dist a b)}
  {ρ : X → ℝ} {hρ : ∀ p, 0 < ρ p} {Λ : ℝ} {β : ℕ → ℝ} {Δ σs : ℝ} {K : ℕ}
  {σc μ b s b' s' ε γc βc : ℝ}
  {N C : X → Type} [∀ a, MetricSpace (N a)] [∀ a, ChartedSpace E3 (N a)]
  [∀ a, MetricSpace (C a)] {o : ∀ a, C a} {δ εr e T V : ℝ}
  {Lmax τ γ vs ζ Λz : ℝ} {U₁ U₂ Ue₁ Ue₂ : Set X}

/-- ZSP02's global linearized defining function `H_k = ψ(η_k) + χ(η_k)(ℓ_k ∘ f + .4 − η_k)` (the
function of (ZH) at `τ = 1`). -/
def zspDefiner_ZSP35_BGR (L : LocalPacketsOnB X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V vs U₁ U₂ Ue₁ Ue₂)
    (Z : ZeroModelFamilyOn 𝓘(ℝ, E3) X g ρ hρ β N C o δ εr e T V U₁ U₂) (k : Z.finite_centres.toFinset)
    (f : X → BlockSpace (fun _ : CGPTag_BAUGP L Z => ℝ²)) : X → ℝ :=
  fun z => zspPsi_ZSP35 ((Z.zero k.1 ((Set.Finite.mem_toFinset _).mp k.2)).radial z) +
    zspChi_ZSP35 ((Z.zero k.1 ((Set.Finite.mem_toFinset _).mp k.2)).radial z) *
      (zspQCLM_ZSP35_BGR L Z k (f z) + 2 / 5 -
        (Z.zero k.1 ((Set.Finite.mem_toFinset _).mp k.2)).radial z)

/-- **The factorization on the thin annulus**: where `.39 < η_k < .41` and `v_k ≠ 0`,
`H_k − .4 = (v_k/R_k)(u_k/v_k − .4)`. -/
theorem zspDefiner_sub_eq_ZSP35_BGR
    (L : LocalPacketsOnB X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V vs U₁ U₂ Ue₁ Ue₂)
    (Z : ZeroModelFamilyOn 𝓘(ℝ, E3) X g ρ hρ β N C o δ εr e T V U₁ U₂) (k : Z.finite_centres.toFinset)
    (f : X → BlockSpace (fun _ : CGPTag_BAUGP L Z => ℝ²)) {z : X}
    (h1 : 39 / 100 < (Z.zero k.1 ((Set.Finite.mem_toFinset _).mp k.2)).radial z)
    (h2 : (Z.zero k.1 ((Set.Finite.mem_toFinset _).mp k.2)).radial z < 41 / 100)
    (hv : (f z (.inr (.inr (.inr (.inl k))))).snd ≠ 0) :
    zspDefiner_ZSP35_BGR L Z k f z - 2 / 5 =
      ((Z.zero k.1 ((Set.Finite.mem_toFinset _).mp k.2)).radius)⁻¹ *
          (f z (.inr (.inr (.inr (.inl k))))).snd *
        (((f z (.inr (.inr (.inr (.inl k))))).fst : ℝ²) 0 /
          (f z (.inr (.inr (.inr (.inl k))))).snd - 2 / 5) := by
  have hR := (Z.zero k.1 ((Set.Finite.mem_toFinset _).mp k.2)).radius_pos
  rw [zspDefiner_ZSP35_BGR, zspPsi_eq_self_ZSP35 (by linarith) (by linarith),
    zspChi_eq_one_ZSP35 (by linarith) (by linarith), zspQCLM_apply_ZSP35_BGR]
  field_simp
  ring

end Kernel

variable {X : Type} [mX : MetricSpace X] [ChartedSpace E3 X] [IsManifold 𝓘(ℝ, E3) ∞ X]
  [CompleteSpace X] [SigmaCompactSpace X] {g : SmoothRiemannianMetric 𝓘(ℝ, E3) X}
  {hmetric : ∀ a b : X, riemannianEDistOf g a b = ENNReal.ofReal (dist a b)}
  {ρ : X → ℝ} {hρ : ∀ p, 0 < ρ p} {Λ : ℝ} {β : ℕ → ℝ} {Δ σs : ℝ} {K : ℕ}
  {σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V vs ζ Λz : ℝ}
  {Kj : ℕ} {Ξ Γ S eg c cw : Fin 3 → ℝ}
  {U₁ U₂ Ue₁ Ue₂ : Set X}

section Final

variable {oM : ManifoldOrientation 𝓘(ℝ, E3) X 3}

end Final


end DifferentialGeometry.Geometry.Collapse
