import DifferentialGeometry.Geometry.Collapse.LocalExport.BoundaryPacketsBFR

/-!
# No 3-splitting at the revised edge collars (lane BCG-5, consumer of `LocalPacketsOnBFR`)

BCG01's edge-collar cover on `edgeB` (blueprint 207B, `B:8806–8814`; review 51 row 2) needs the
two-stratum fact at the collar points `x ∈ B(j, 100Δρ_j)` of every revised edge centre `j`: no
3-splitting at tolerance `β 3` in `ρ(x)⁻¹ d` (lane BCG-4's input
`h3 : ¬ HasEuclideanSplitting x 3 (β 3)` of `EdgeFamilyOn.collar_two_stratum_BCG4` and
`LocalPacketsOnBF.edgeB_collar_circle_BCG4`). On the extended final boundary family it is read
off from the field `rank_le_two` and the packet domain `edgeB_domain`:

* `not_hasEuclideanSplitting_three_of_rank_le_two_BCG5`: rank `≤ 2` excludes a 3-splitting at
  tolerance `β 3`;
* `LocalPacketsOnBFR.edgeB_domain_no_three_BCG5`: every point of the packet domain
  `B(j, 1000Δρ_j)` of every revised edge centre lies in `U₁` and has no 3-splitting;
* `LocalPacketsOnBFR.edgeB_collar_no_three_BCG5`: the same at every collar point
  `d(x, j) < 100Δρ_j` (BCG-4's form).
-/

set_option autoImplicit false

noncomputable section

open Set Function Metric Bundle Manifold Filter
open scoped ContDiff Manifold Topology
open DifferentialGeometry.Geometry.Riemannian GC.MetricGeometry

namespace DifferentialGeometry.Geometry.Collapse

local notation "E3" => EuclideanSpace ℝ (Fin 3)

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace

/-- **Rank `≤ 2` excludes a 3-splitting**: if the splitting rank of the scale `ρ` at `x` is at most
`2`, then `x` has no 3-splitting at tolerance `β 3` in the metric `ρ(x)⁻¹ d`. -/
theorem not_hasEuclideanSplitting_three_of_rank_le_two_BCG5 {X : Type} [mX : MetricSpace X]
    {ρ : X → ℝ} {hρ : ∀ p, 0 < ρ p} {β : ℕ → ℝ} {x : X}
    (h : scaledSplittingRank.{0, 0} ρ hρ β x ≤ 2) :
    ¬ @HasEuclideanSplitting.{0, 0} X (mX.rescale (ρ x)⁻¹ (inv_pos.mpr (hρ x))) x 3 (β 3) :=
  fun h3 => by
    have h' := @le_splittingRank.{0, 0} X (mX.rescale (ρ x)⁻¹ (inv_pos.mpr (hρ x))) x β 3 3 le_rfl
      h3
    change @splittingRank.{0, 0} X (mX.rescale (ρ x)⁻¹ (inv_pos.mpr (hρ x))) x β 3 ≤ 2 at h
    omega

section Final

variable {X : Type} [mX : MetricSpace X] [ChartedSpace E3 X] [IsManifold 𝓘(ℝ, E3) ∞ X]
  [CompleteSpace X] [SigmaCompactSpace X] {g : SmoothRiemannianMetric 𝓘(ℝ, E3) X}
  {hmetric : ∀ a b : X, riemannianEDistOf g a b = ENNReal.ofReal (dist a b)}
  {ρ : X → ℝ} {hρ : ∀ p, 0 < ρ p} {Λ : ℝ} {β : ℕ → ℝ} {Δ σs : ℝ} {K : ℕ}
  {σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V vs ζ Λz : ℝ} {U₁ U₂ Ue₁ Ue₂ : Set X}

/-- **No 3-splitting on the packet domains of the revised edge charts**: at every revised edge
centre `j`, every point of `B(j, 1000Δρ_j)` lies in `U₁` (`edgeB_domain`) and has no 3-splitting
at tolerance `β 3` in `ρ(x)⁻¹ d` (`rank_le_two`). -/
theorem LocalPacketsOnBFR.edgeB_domain_no_three_BCG5
    (F : LocalPacketsOnBFR X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V
      vs ζ Λz U₁ U₂ Ue₁ Ue₂) :
    ∀ j ∈ F.edgeB.centres, ∀ x, dist x j < 1000 * Δ * ρ j → x ∈ U₁ ∧
      ¬ @HasEuclideanSplitting.{0, 0} X (mX.rescale (ρ x)⁻¹ (inv_pos.mpr (hρ x))) x 3 (β 3) :=
  fun j hj x hx =>
    ⟨F.edgeB_domain j hj (mem_ball.mpr hx),
      not_hasEuclideanSplitting_three_of_rank_le_two_BCG5
        (F.rank_le_two x (F.edgeB_domain j hj (mem_ball.mpr hx)))⟩

/-- **No 3-splitting at the revised edge collars** (BCG01's two-stratum input, lane BCG-4's form):
at every revised edge centre `j` and every collar point `d(x, j) < 100Δρ_j`, `x` has no
3-splitting at tolerance `β 3` in `ρ(x)⁻¹ d`. -/
theorem LocalPacketsOnBFR.edgeB_collar_no_three_BCG5
    (F : LocalPacketsOnBFR X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V
      vs ζ Λz U₁ U₂ Ue₁ Ue₂) {j : X} (hj : j ∈ F.edgeB.centres) {x : X}
    (hx : dist x j < 100 * Δ * ρ j) :
    ¬ @HasEuclideanSplitting.{0, 0} X (mX.rescale (ρ x)⁻¹ (inv_pos.mpr (hρ x))) x 3 (β 3) := by
  have hd := dist_nonneg (x := x) (y := j)
  exact (F.edgeB_domain_no_three_BCG5 j hj x (by linarith)).2

end Final

end DifferentialGeometry.Geometry.Collapse
