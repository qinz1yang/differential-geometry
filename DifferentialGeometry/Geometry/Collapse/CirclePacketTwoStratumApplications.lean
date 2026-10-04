import DifferentialGeometry.Geometry.Collapse.CirclePacketTwoStratum

/-!
# Consumer: the circle cutoff family of LPA06 on the two-stratum

Blueprint `master207A.tex`, LPA06 (A:30586–30640), circle family only: the circle cutoffs form
an indexed finite family whose cutoffs equal one on the physical covering balls `B(j, 2ρ_j)`,
have closed supports in the physical balls `B(j, 200ρ_j)`, and whose SUPPORT multiplicity is at
most the numerical constant `V₋(6·10⁶ + 2/3) / V₋(1/3)` (curvature `-(1/(2·10⁶))²`), fixed before
`Δ` and `w′`.
-/

set_option autoImplicit false

noncomputable section

open Set Function Metric Manifold Filter
open scoped ContDiff Manifold Topology
open DifferentialGeometry.Geometry.Riemannian
open GC.MetricGeometry
open DifferentialGeometry.Geometry.Riemannian.VolumeComparison

namespace DifferentialGeometry.Geometry.Collapse

universe uE uH u

variable {E : Type uE} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
  {H : Type uH} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]

/-- **The circle cutoff family on the two-stratum, with its support multiplicity.** -/
theorem eventually_circle_cutoff_family_two_stratum (hdim : Module.finrank ℝ E = 3) :
    ∃ a₂ : ℝ, 0 < a₂ ∧ ∀ γ : ℝ, 0 < γ → γ < 1 / 10 → ∃ β₀ : ℝ, 0 < β₀ ∧ β₀ ≤ a₂ ∧
      ∀ β : ℕ → ℝ, 0 < β 2 → β 2 ≤ β₀ → ∀ σ : ℝ, 0 < σ → σ < 1 → σ ≤ a₂ →
      ∀ Λ : ℝ, 0 < Λ → Λ * 2000000 ≤ 1 / 100 → ∃ w₀ : ℝ, 0 < w₀ ∧
      ∀ w : ℝ, 0 < w → w < w₀ → w < 4 * Real.pi / 3 →
      ∀ (X : ℕ → Type u) [∀ i, MetricSpace (X i)] [∀ i, ChartedSpace H (X i)]
        [∀ i, IsManifold I ∞ (X i)] [∀ i, CompactSpace (X i)]
        (g : ∀ i, SmoothRiemannianMetric I (X i)),
        (∀ i a b, riemannianEDistOf (g i) a b = ENNReal.ofReal (dist a b)) →
        ∀ (α : ℕ → ℝ), Tendsto α atTop atTop →
        (∀ i (p : X i), ENNReal.ofReal (α i * firstVolumeScale (g i) p (α i)⁻¹) ≤
          curvatureRadius (g i) p) →
      ∀ᶠ i in atTop, ∃ ρ : X i → ℝ, ∃ hρpos : ∀ p, 0 < ρ p, ∃ J : Set (X i), J.Finite ∧
        J ⊆ scaledSplittingStratum.{u, 0} ρ hρpos β 2 ∧
        (∀ p ∈ scaledSplittingStratum.{u, 0} ρ hρpos β 2, ∃ j ∈ J,
          ball p (ρ p) ⊆ ball j (2 * ρ j)) ∧
        ∃ ζ : X i → X i → ℝ,
          (∀ j ∈ J, ContMDiff I 𝓘(ℝ, ℝ) ∞ (ζ j) ∧ HasCompactSupport (ζ j) ∧
            (∀ x, ζ j x ∈ Icc 0 1) ∧ (∀ x ∈ ball j (2 * ρ j), ζ j x = 1) ∧
            tsupport (ζ j) ⊆ ball j (200 * ρ j)) ∧
          ∀ x : X i, ((J ∩ {j | x ∈ tsupport (ζ j)}).ncard : ℝ) ≤
            modelVolume (-((1 / 2000000 : ℝ) ^ 2)) 3 (3 * 2000000 + 2 / 3) /
              modelVolume (-((1 / 2000000 : ℝ) ^ 2)) 3 (1 / 3) := by
  obtain ⟨a₂, ha₂, h⟩ := eventually_circle_packets_two_stratum.{uE, uH, u} (E := E) (H := H)
    (I := I) hdim
  refine ⟨a₂, ha₂, fun γ hγ hγone => ?_⟩
  obtain ⟨β₀, hβ₀, hβ₀a, h⟩ := h γ hγ hγone
  refine ⟨β₀, hβ₀, hβ₀a, fun β hβ hββ₀ σ hσ hσ1 hσa Λ hΛ hΛsmall => ?_⟩
  obtain ⟨w₀, hw₀, h⟩ := h β hβ hββ₀ σ hσ hσ1 hσa Λ hΛ hΛsmall
  refine ⟨w₀, hw₀, fun w hw hww₀ hwc X _ _ _ _ g hmetric α hα hstand => ?_⟩
  filter_upwards [h w hw hww₀ hwc X g hmetric α hα hstand] with i hi
  obtain ⟨ρ, hρpos, -, -, -, -, hpt, J, hfin, hJS, -, hcov, hmult⟩ := hi
  have hcut : ∀ j : X i, ∃ ζ : X i → ℝ, j ∈ J → (ContMDiff I 𝓘(ℝ, ℝ) ∞ ζ ∧
      HasCompactSupport ζ ∧ (∀ x, ζ x ∈ Icc 0 1) ∧ (∀ x ∈ ball j (2 * ρ j), ζ x = 1) ∧
      tsupport ζ ⊆ ball j (200 * ρ j)) := by
    intro j
    by_cases hj : j ∈ J
    · obtain ⟨C, mC, c, -, -, -, -, -, Y, mY, a, F, η, hη, hrank, -, -, -, -, -, -, -, -, ζ,
          hζ, hsupp, hζ01, -, -, -, -, hball, hphys⟩ := hpt j (hJS hj)
      exact ⟨ζ, fun _ => ⟨hζ, hsupp, hζ01, fun x hx => (hball hx).2, hphys⟩⟩
    · exact ⟨0, fun hj' => (hj hj').elim⟩
  choose ζ hζ using hcut
  refine ⟨ρ, hρpos, J, hfin, hJS, hcov, ζ, fun j hj => hζ j hj, fun x => ?_⟩
  refine le_trans ?_ (hmult x)
  have hsub : J ∩ {j | x ∈ tsupport (ζ j)} ⊆ J ∩ {j | x ∈ ball j (2000000 * ρ j)} := by
    rintro j ⟨hj, hx⟩
    refine ⟨hj, ball_subset_ball ?_ ((hζ j hj).2.2.2.2 hx)⟩
    linarith [hρpos j]
  exact_mod_cast Set.ncard_le_ncard hsub (hfin.subset inter_subset_left)

end DifferentialGeometry.Geometry.Collapse
