import DifferentialGeometry.Geometry.Collapse.FixtureC2.SphereLoopKL
import DifferentialGeometry.Geometry.Collapse.MetricRank.ThinOnlyRank
import DifferentialGeometry.Geometry.Collapse.MetricRank.RankAdapters
import DifferentialGeometry.Geometry.Collapse.FixtureC2.SphereLoopNoEdge

/-!
# Splitting rank exactly one on the long sphere loop (S-FIXTURE-C2b, K2, G2 file 5)

At the constant scale `R` (`R ≥ 200 (D₀ + 1)`, `D₀` the diameter of the unit sphere) every point of
the sphere loop of length `ℓ ≥ 8 R / β₁` has `scaledSplittingRank = 1`: the thin product
approximation of `SphereLoopKL` (at `δ = β₁ / 2`, factor of diameter `D₀ / R`) and
`scaledSplittingRank_eq_one_of_thin_line_only_SMR`. Hence the one-stratum is everything and the
other three strata are empty.
-/

set_option autoImplicit false
noncomputable section
open Bundle Manifold Set Metric
open DifferentialGeometry DifferentialGeometry.Geometry DifferentialGeometry.Geometry.Metric
open DifferentialGeometry.Geometry.Riemannian DifferentialGeometry.Geometry.Collapse
open GC.MetricGeometry
open scoped Manifold ContDiff

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace
attribute [local instance] sphereDimension cylinderDimension sphereCompact sphereConnected
  intrinsicMetric intrinsicUniform intrinsicEMetric intrinsicPseudoMetric intrinsicBundle
  cylinderRiemannian cylinderContinuous cylinderComplete
attribute [local instance] loopMS3_FXC2

namespace DifferentialGeometry.Geometry.Collapse

local notation "S2" => Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1

section Rank

variable (ℓ : LoopLen_FXC2) {R : ℝ} (hR : 0 < R) {β : ℕ → ℝ} {D0 : ℝ}

/-- **Rank exactly one at every point** of the long sphere loop at the constant scale `R`. -/
theorem loopRank_eq_one_FXC2 (hD0 : ∀ s s' : S2, sphereDist_FXC2 s s' ≤ D0) (hβ1 : 0 < β 1)
    (hβ1' : β 1 < 1) (hβ2 : β 2 ≤ 3 / 20) (hβ3 : β 3 ≤ 3 / 20)
    (hthin : β 1 / 2 + D0 / R ≤ 1 / 100) (hℓ : 8 * R / β 1 ≤ ℓ.1) (p : LoopC_FXC2 ℓ) :
    scaledSplittingRank.{0, 0} (fun _ : LoopC_FXC2 ℓ => R) (fun _ => hR) β p = 1 := by
  have hδ : 0 < β 1 / 2 := half_pos hβ1
  have hδ1 : β 1 / 2 < 1 := by linarith
  have hℓ' : 4 * R / (β 1 / 2) ≤ ℓ.1 := by
    have : 4 * R / (β 1 / 2) = 8 * R / β 1 := by field_simp; ring
    linarith
  obtain ⟨Z, mZ, z, hZ, ⟨f⟩⟩ := loopKL_exists_FXC2 ℓ hR hδ hδ1 hℓ' hD0 p
  exact scaledSplittingRank_eq_one_of_thin_line_only_SMR (hρ := fun _ => hR) (m := loopMS3_FXC2 ℓ)
    f hZ hthin (by linarith) hβ1' hβ2 hβ3

theorem loopStratum_one_eq_univ_FXC2 (hD0 : ∀ s s' : S2, sphereDist_FXC2 s s' ≤ D0)
    (hβ1 : 0 < β 1) (hβ1' : β 1 < 1) (hβ2 : β 2 ≤ 3 / 20) (hβ3 : β 3 ≤ 3 / 20)
    (hthin : β 1 / 2 + D0 / R ≤ 1 / 100) (hℓ : 8 * R / β 1 ≤ ℓ.1) :
    scaledSplittingStratum.{0, 0} (fun _ : LoopC_FXC2 ℓ => R) (fun _ => hR) β 1 = univ :=
  eq_univ_of_forall fun p => loopRank_eq_one_FXC2 ℓ hR hD0 hβ1 hβ1' hβ2 hβ3 hthin hℓ p

theorem loopStratum_ne_one_empty_FXC2 (hD0 : ∀ s s' : S2, sphereDist_FXC2 s s' ≤ D0)
    (hβ1 : 0 < β 1) (hβ1' : β 1 < 1) (hβ2 : β 2 ≤ 3 / 20) (hβ3 : β 3 ≤ 3 / 20)
    (hthin : β 1 / 2 + D0 / R ≤ 1 / 100) (hℓ : 8 * R / β 1 ≤ ℓ.1) {k : Fin 4} (hk : k ≠ 1) :
    scaledSplittingStratum.{0, 0} (fun _ : LoopC_FXC2 ℓ => R) (fun _ => hR) β k = ∅ := by
  refine eq_empty_of_forall_notMem fun p hp => hk (Fin.ext ?_)
  change scaledSplittingRank.{0, 0} (fun _ : LoopC_FXC2 ℓ => R) (fun _ => hR) β p = k.val at hp
  rw [loopRank_eq_one_FXC2 ℓ hR hD0 hβ1 hβ1' hβ2 hβ3 hthin hℓ p] at hp
  exact hp.symm

/-- **The long sphere loop has no strong edge point** at the constant scale `R`
(`b + s ≤ 1/100`, `1 ≤ Δ`). -/
theorem loopNotEdge_FXC2 (hD0 : ∀ s s' : S2, sphereDist_FXC2 s s' ≤ D0) (hβ1 : 0 < β 1)
    (hβ1' : β 1 < 1) (hthin : β 1 / 2 + D0 / R ≤ 1 / 100) (hℓ : 8 * R / β 1 ≤ ℓ.1)
    {Δ b s : ℝ} (hΔ : 1 ≤ Δ) (hbs : b + s ≤ 1 / 100) (p : LoopC_FXC2 ℓ) :
    ¬ @isEdgePoint.{0, 0} (LoopC_FXC2 ℓ) ((loopMS3_FXC2 ℓ).rescale R⁻¹ (inv_pos.mpr hR)) p Δ b
      s := by
  have hδ : 0 < β 1 / 2 := half_pos hβ1
  have hδ1 : β 1 / 2 < 1 := by linarith
  have hℓ' : 4 * R / (β 1 / 2) ≤ ℓ.1 := by
    have : 4 * R / (β 1 / 2) = 8 * R / β 1 := by field_simp; ring
    linarith
  exact @not_isEdgePoint_of_thin_line_FXC2.{0, 0, 0} (LoopC_FXC2 ℓ)
    ((loopMS3_FXC2 ℓ).rescale R⁻¹ (inv_pos.mpr hR)) p Δ b s (β 1 / 2) (D0 / R) hΔ hbs hthin
    (loopKL_exists_FXC2 ℓ hR hδ hδ1 hℓ' hD0 p)

/-- The thin approximation at the register tolerance `β 1` itself (the shape of
`SlimFamily.covers` and `EdgeFamily.covers_nonslim`): a factor of diameter `< 1000 Δ`. -/
theorem loopSlimFactor_FXC2 (hD0 : ∀ s s' : S2, sphereDist_FXC2 s s' ≤ D0) (hβ1 : 0 < β 1)
    (hβ1' : β 1 < 1) (hthin : β 1 / 2 + D0 / R ≤ 1 / 100) (hℓ : 8 * R / β 1 ≤ ℓ.1) {Δ : ℝ}
    (hΔ : 1 ≤ Δ) (p : LoopC_FXC2 ℓ) :
    ∃ (Z : Type) (mZ : MetricSpace Z) (z : Z), letI := mZ
      Bornology.IsBounded (univ : Set Z) ∧ Metric.diam (univ : Set Z) < 1000 * Δ ∧
      Nonempty (@KleinerLottApprox (LoopC_FXC2 ℓ) (WithLp 2 (ℝ × Z))
        ((loopMS3_FXC2 ℓ).rescale R⁻¹ (inv_pos.mpr hR)) _ p (WithLp.toLp 2 ((0 : ℝ), z))
        (β 1)) := by
  have hℓ' : 4 * R / β 1 ≤ ℓ.1 := by
    have : 4 * R / β 1 ≤ 8 * R / β 1 := by
      apply div_le_div_of_nonneg_right _ hβ1.le
      linarith
    linarith
  obtain ⟨Z, mZ, z, hZ, hK⟩ := loopKL_exists_FXC2 ℓ hR hβ1 hβ1' hℓ' hD0 p
  refine ⟨Z, mZ, z, Metric.isBounded_iff.mpr ⟨D0 / R, fun a _ b _ => hZ a b⟩, ?_, hK⟩
  have hD00 : 0 ≤ D0 / R := le_trans dist_nonneg (hZ z z)
  have : Metric.diam (univ : Set Z) ≤ D0 / R :=
    Metric.diam_le_of_forall_dist_le hD00 (fun a _ b _ => hZ a b)
  have hδ : 0 < β 1 / 2 := half_pos hβ1
  linarith

end Rank

end DifferentialGeometry.Geometry.Collapse
