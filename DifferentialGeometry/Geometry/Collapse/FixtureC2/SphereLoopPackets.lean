import DifferentialGeometry.Geometry.Collapse.FixtureC2.SphereLoopFamily
import DifferentialGeometry.Geometry.Collapse.LocalExport.LocalChartPacketsC14ZeroTypes

/-!
# The closed family `LocalChartPacketsC14Z` on the sphere loop (S-FIXTURE-C2b, F2, G3 file 4)

`loopPacketsC14Z_FXC2 : LocalChartPacketsC14Z (LoopC ℓ) (loopMetric3 ℓ) … oM`: the sphere loop
`S² × S¹_ℓ` (`ℓ = N Δ R`) at the constant scale `ρ ≡ R` with

* the NON-EMPTY slim family (`loopSlim_FXC2`: `N` actual centres `π_0 (z₀, k Δ R)`, an LC87
  `SlimCentre` at every centre with the formula cutoff and the value tolerance `vs`);
* the circle, edge and zero families EMPTY (rank exactly one everywhere, no strong edge point,
  no zero stratum), `sec ≥ 0`;
* `oM` a PARAMETER (the zero family is empty, so `zero_sublevel_types` holds for every `oM`).

`weak_edge_density` is vacuous because EVERY one-stratum point is slim (the antecedent is refuted
by `loopSlimFactor_FXC2`). Projections `loopPacketsC14_FXC2`, `loopPacketsC14D_FXC2`.
-/

set_option autoImplicit false
noncomputable section
open Set Function Metric Bundle GC.MetricGeometry
open DifferentialGeometry DifferentialGeometry.Geometry DifferentialGeometry.Geometry.Riemannian
open DifferentialGeometry.Geometry.Collapse
open scoped Manifold ContDiff Topology ENNReal

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace
attribute [local instance] sphereDimension cylinderDimension sphereCompact sphereConnected
  intrinsicMetric intrinsicUniform intrinsicEMetric intrinsicPseudoMetric intrinsicBundle
  cylinderRiemannian cylinderContinuous cylinderComplete
attribute [local instance] loopMS3_FXC2
attribute [local instance] nezero_finrank_euclideanThree_LC87

namespace DifferentialGeometry.Geometry.Collapse

local notation "S2" => Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1
local notation "E3" => EuclideanSpace ℝ (Fin 3)

section Packets

variable (ℓ : LoopLen_FXC2) {R : ℝ} (hR : 0 < R) {β : ℕ → ℝ} {D0 : ℝ}
  (hD0 : ∀ s s' : S2, sphereDist_FXC2 s s' ≤ D0) (hβ1 : 0 < β 1) (hβ1' : β 1 < 1)
  (hβ2 : β 2 ≤ 3 / 20) (hβ3 : β 3 ≤ 3 / 20) (hthin : β 1 / 2 + D0 / R ≤ 1 / 100)
  (hℓ : 8 * R / β 1 ≤ ℓ.1)
  {Δ σs vs : ℝ} {K : ℕ} (hΔ : 1 ≤ Δ) (hσs : 0 < σs) (hσs1 : σs ≤ 1 / 100) (hvs : 0 < vs)
  (hK : 5 ≤ K) (hR1 : 1 ≤ R) (hD00 : 0 ≤ D0) (z₀ : S2) {N : ℕ} (hN : ℓ.1 = N * (Δ * R))
  (hΔR : 2 * D0 ≤ Δ * R) (hβ0 : β 1 < slimBeta0_FXC2 hR z₀ hΔ hσs hσs1 hvs hK)
  {Lam σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V ζ Λz : ℝ} (hbs : b + s ≤ 1 / 100)

include hR1 hD00 hD0 hβ1 hβ1' hβ2 hβ3 hthin hℓ hN hΔR hβ0 hσs hσs1 hvs hK hbs in
/-- **The family `LocalChartFamilyE` of the sphere loop**: the non-empty slim family and the empty
circle and edge families. -/
def loopFamilyE_FXC2 :
    LocalChartFamilyE (LoopC_FXC2 ℓ) (loopMetric3_FXC2 ℓ) (loopMS3_hmetric_FXC2 ℓ)
      (fun _ => R) (fun _ => hR) Lam β Δ σs K σc μ b s b' s' ε γc βc Lmax τ where
  contMDiff_scale := contMDiff_const
  lipschitz_scale := (LipschitzWith.const R).weaken zero_le
  circle := loopCircle_FXC2 ℓ hR hD0 hβ1 hβ1' hβ2 hβ3 hthin hℓ
  slim := loopSlim_FXC2 ℓ hR hD0 hβ1 hβ1' hβ2 hβ3 hthin hℓ hΔ hσs hσs1 hvs hK hR1 hD00 z₀ hN hΔR
    hβ0
  edge := loopEdge_FXC2 ℓ hR hD0 hβ1 hβ1' hthin hℓ hΔ hbs
  exhaustion := fun x => by
    obtain ⟨k, hk⟩ := loopCentres_cover_FXC2 ℓ z₀ (loop_sp_pos_FXC2 hR hΔ) hN hD00 hD0 x
    refine Or.inr (Or.inr (Or.inl ⟨loopCentre_FXC2 ℓ z₀ (Δ * R) k, ⟨k, rfl⟩, ?_⟩))
    rw [mem_ball]
    have := loop_sp_pos_FXC2 hR hΔ
    linarith
  circle_cutoff_eq := fun j hj => absurd hj (notMem_empty j)
  slim_cutoff_eq := fun j hj => (Classical.choose_spec (exists_slimCentre_loop_FXC2 hΔ hσs hσs1
    hvs hK hR hR1 z₀ ℓ (loop_two_R_le_FXC2 ℓ hR hβ1 hβ1' hℓ) j (loopSlimA_FXC2 ℓ z₀ j hj)
    (loopSlimHja_FXC2 ℓ z₀ j hj) hβ1 hβ0
    (loopSlimFactor_FXC2 ℓ hR hD0 hβ1 hβ1' hthin hℓ hΔ j))).1
  sectional_buffer := fun _ _ _ _ y _ =>
    (loopMetric3_sectional_FXC2 ℓ y).mono (neg_nonpos.mpr (inv_nonneg.mpr (sq_nonneg _)))
  edge_coarse := fun j hj => absurd hj (notMem_empty j)

include hR1 hD00 hD0 hβ1 hβ1' hβ2 hβ3 hthin hℓ hN hΔR hβ0 hσs hσs1 hvs hK hbs in
/-- **`LocalChartPacketsC14` on the sphere loop** (non-empty slim family; empty circle / edge /
zero families). -/
def loopPacketsC14_FXC2 :
    LocalChartPacketsC14 (LoopC_FXC2 ℓ) (loopMetric3_FXC2 ℓ) (loopMS3_hmetric_FXC2 ℓ)
      (fun _ => R) (fun _ => hR) Lam β Δ σs K σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V vs ζ
      Λz where
  toLocalChartFamilyE := loopFamilyE_FXC2 ℓ hR hD0 hβ1 hβ1' hβ2 hβ3 hthin hℓ hΔ hσs hσs1 hvs hK
    hR1 hD00 z₀ hN hΔR hβ0 hbs
  circleAdapted := fun j hj => absurd hj (notMem_empty j)
  N := fun _ => LoopC_FXC2 ℓ
  C := fun _ => PUnit.{1}
  instMetricN := fun _ => loopMS3_FXC2 ℓ
  instChartedN := fun _ => inferInstance
  instMetricC := fun _ => inferInstance
  o := fun _ => PUnit.unit
  zero := loopZero_FXC2 ℓ hR hD0 hβ1 hβ1' hβ2 hβ3 hthin hℓ
  edgeDisk := fun j hj => absurd hj (notMem_empty j)
  circle_residual := fun j hj => absurd hj (notMem_empty j)
  zero_local_comparison := fun c hc => absurd hc (notMem_empty c)
  slim_value := fun j hj => (Classical.choose_spec (exists_slimCentre_loop_FXC2 hΔ hσs hσs1
    hvs hK hR hR1 z₀ ℓ (loop_two_R_le_FXC2 ℓ hR hβ1 hβ1' hℓ) j (loopSlimA_FXC2 ℓ z₀ j hj)
    (loopSlimHja_FXC2 ℓ z₀ j hj) hβ1 hβ0
    (loopSlimFactor_FXC2 ℓ hR hD0 hβ1 hβ1' hthin hℓ hΔ j))).2
  zero_shell_split := fun c hc => absurd hc (notMem_empty c)
  zero_adapted := fun c hc => absurd hc (notMem_empty c)
  zero_curvature := fun c hc => absurd hc (notMem_empty c)
  edge_section := fun j hj => absurd hj (notMem_empty j)

include hR1 hD00 hD0 hβ1 hβ1' hβ2 hβ3 hthin hℓ hN hΔR hβ0 hσs hσs1 hvs hK hbs in
/-- `LocalChartPacketsC14D` on the sphere loop (`weak_edge_density` is vacuous: every one-stratum
point has a slim factor). -/
def loopPacketsC14D_FXC2 :
    LocalChartPacketsC14D (LoopC_FXC2 ℓ) (loopMetric3_FXC2 ℓ) (loopMS3_hmetric_FXC2 ℓ)
      (fun _ => R) (fun _ => hR) Lam β Δ σs K σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V vs ζ
      Λz where
  toLocalChartPacketsC14 := loopPacketsC14_FXC2 ℓ hR hD0 hβ1 hβ1' hβ2 hβ3 hthin hℓ hΔ hσs hσs1
    hvs hK hR1 hD00 z₀ hN hΔR hβ0 hbs
  weak_edge_density := fun p _ hns =>
    absurd (loopSlimFactor_FXC2 ℓ hR hD0 hβ1 hβ1' hthin hℓ hΔ p) hns

variable (oM : ManifoldOrientation 𝓘(ℝ, E3) (LoopC_FXC2 ℓ) 3)

include hR1 hD00 hD0 hβ1 hβ1' hβ2 hβ3 hthin hℓ hN hΔR hβ0 hσs hσs1 hvs hK hbs in
/-- **The complete closed family `LocalChartPacketsC14Z` on the sphere loop** (`oM` a parameter:
the zero family is empty). The slim family is NON-EMPTY: the stage clauses of the closed rows have
actual content on it (`N` centres, actual slim charts and product models). -/
def loopPacketsC14Z_FXC2 :
    LocalChartPacketsC14Z (LoopC_FXC2 ℓ) (loopMetric3_FXC2 ℓ) (loopMS3_hmetric_FXC2 ℓ)
      (fun _ => R) (fun _ => hR) Lam β Δ σs K σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V vs ζ
      Λz oM where
  toLocalChartPacketsC14D := loopPacketsC14D_FXC2 ℓ hR hD0 hβ1 hβ1' hβ2 hβ3 hthin hℓ hΔ hσs hσs1
    hvs hK hR1 hD00 z₀ hN hΔR hβ0 hbs
  zero_sublevel_types := fun c hc => absurd hc (notMem_empty c)

end Packets

end DifferentialGeometry.Geometry.Collapse
