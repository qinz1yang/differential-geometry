import DifferentialGeometry.Geometry.Fibration.ActualRawAlignmentZeroApplications
import DifferentialGeometry.Geometry.Collapse.LocalExport.LocalChartPacketsC14ZeroTypes

/-!
# TCP02 complete on the final closed family (`LocalChartPacketsC14Z`): the four kinds on one `P`

External review 60 (§三 TCP02, §七.1) and dispositions-task60 ("TCP02: zero clause missing from the
registered entry"): the registered `tcp02_row` returns circle / slim / edge only. Blueprint
`master207B.tex`, TCP02 (B:5311–5369): every listed constant-radius coordinate has one coisometry
with (TR) on `B(p_i, 1000)` and every meeting zero block a unit row `A₀` with
`|d(p₀, x) − d(p₀, p_i) − A₀u_i(x)| < E` (TR0) (distances in `R_i` units).

* `tcp02_zero_PKG`: (TR0) on the final family `P : LocalChartPacketsC14Z`, in the three-term shape
  of the other kinds: zero reference `p₀ = k`, the SAME circle centre `i` and scale `ρ(i)`, the
  actual closed-support meeting `tsupport(ζ_k) ∩ B(i, 10ρ(i)) ≠ ∅` (`ζ_k` = the zero block cutoff of
  `cgpCutoff`), on `B(i, 1000ρ(i))`:
  `‖e₀ ρ(i)⁻¹d(k, x) − A₀ u_i(x) − e₀ ρ(i)⁻¹d(k, i)‖ < E₀` (translation `c₀ = ρ(i)⁻¹d(k, p_i)`).
* `tcp02_full_row_PKG`: the complete row — circle, slim, edge AND zero — on ONE `P`, under ONE
  threshold choice (`σ`, `η₂` early, `η₁(Δ)`; C14-KA5's `tcp02_rowZ` on the Z projection of `P`).
* consumer `tcp02_full_row_zero_difference_PKG`: the translation-free (difference) form of the zero
  clause on the final family, as TCP03's zero block reads it.
-/

set_option autoImplicit false

noncomputable section

open Set Function Metric Bundle Manifold Filter
open scoped ContDiff Manifold Topology
open DifferentialGeometry.Geometry.Riemannian GC.MetricGeometry
open DifferentialGeometry.Analysis

namespace DifferentialGeometry.Geometry.Collapse

local notation "E3" => EuclideanSpace ℝ (Fin 3)
local notation "E1" => EuclideanSpace ℝ (Fin 1)
local notation "ℝ²" => EuclideanSpace ℝ (Fin 2)

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace

attribute [local instance] nezero_finrank_euclideanThree_LC87

attribute [local instance] LocalChartPackets.instMetricN LocalChartPackets.instChartedN
  LocalChartPackets.instMetricC

/-- The two-term (TR0) of C14-ZERO in the three-term shape `‖e₀a − A₀u − e₀c‖`. -/
theorem single_three_term_PKG {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    (A : F →L[ℝ] E1) (r a c : ℝ) (u : F) :
    EuclideanSpace.single (0 : Fin 1) (r * a) - A u - EuclideanSpace.single 0 (r * c) =
      EuclideanSpace.single 0 (r * (a - c)) - A u := by
  rw [sub_right_comm, single_zero_sub_KA5, ← mul_sub]

/-- **TCP02 (TR0) on the final closed family.** For a target error `E₀` and the exclusion quality
`ν` (`3ν ≤ β₃ < 1`) there are an early `σ ≤ 1/1000` and a zero quality bound `η₁` (independent of
`Δ`) such that every actual `P : LocalChartPacketsC14Z` with the zero ranges (`0 ≤ Λ`, `1 ≤ Δ`,
`LΛ < 10⁻⁵`, `e < 1/40`, `T ≥ 1600L`), `3β₂ ≤ σ`, `β₁ ≤ η₁` and `σ⁻¹ ≤ Lmax` has, at every circle
centre `i` and every zero ball (centre `p₀ = k`) whose closed support meets `D_i = B(i, 10ρ(i))`, a
unit row `A₀ : ℝ² → ℝ¹` with `‖e₀ρ(i)⁻¹d(k, x) − A₀u_i(x) − e₀ρ(i)⁻¹d(k, i)‖ < E₀` on
`B(i, 1000ρ(i))` (`u_i = circleRaw_KA3`, the ORIGINAL raw circle coordinate at `i`). -/
theorem tcp02_zero_PKG {E₀ ν : ℝ} (hE : 0 < E₀) (hν : 0 < ν) (hν1 : ν < 1) :
    ∃ σ : ℝ, 0 < σ ∧ σ ≤ 1 / 1000 ∧ ∃ η₁ : ℝ, 0 < η₁ ∧
    ∀ {X : Type} [MetricSpace X] [ChartedSpace E3 X] [IsManifold 𝓘(ℝ, E3) ∞ X]
      [CompactSpace X] {g : SmoothRiemannianMetric 𝓘(ℝ, E3) X}
      {hmetric : ∀ a b : X, riemannianEDistOf g a b = ENNReal.ofReal (dist a b)}
      {ρ : X → ℝ} {hρ : ∀ p, 0 < ρ p} {Λ : ℝ} {β : ℕ → ℝ} {Δ σs : ℝ} {K : ℕ}
      {σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V vs ζ Λz : ℝ}
      {oM : ManifoldOrientation 𝓘(ℝ, E3) X 3}
      (P : LocalChartPacketsC14Z X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc Lmax τ γ δ εr
        e T V vs ζ Λz oM),
      0 ≤ Λ → 1 ≤ Δ → 1000000 * Δ * Λ < 1 / 100000 → e < 1 / 40 → 1600 * (1000000 * Δ) ≤ T →
      3 * ν ≤ β 3 → β 3 < 1 → 3 * β 2 ≤ σ → β 1 ≤ η₁ → σ⁻¹ ≤ Lmax →
      ∀ i ∈ P.circle.centres, ∀ k (hk : k ∈ P.zero.centres),
        (tsupport (fun y => Calculus.annularCutoff Calculus.cutoffProfile
          ((P.zero.zero k hk).radial y)) ∩ ball i (10 * ρ i)).Nonempty →
        ∃ A₀ : ℝ² →L[ℝ] E1, A₀.comp (ContinuousLinearMap.adjoint A₀) = ContinuousLinearMap.id ℝ _ ∧
          ∀ x, dist x i < 1000 * ρ i →
            ‖EuclideanSpace.single 0 ((ρ i)⁻¹ * dist k x) -
                A₀ (circleRaw_KA3 P.toLocalChartPackets i x) -
                EuclideanSpace.single 0 ((ρ i)⁻¹ * dist k i)‖ < E₀ := by
  obtain ⟨σ, hσ, hσ1, η₁, hη₁, hzero⟩ := tcp02_zero_supplier_ZERO hE hν hν1
  refine ⟨σ, hσ, hσ1, η₁, hη₁, ?_⟩
  intro X _ _ _ _ g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V vs ζ Λz oM
    P hΛ hΔ hLΛ he hT hν3 hβ3 hβ2σ hβ1 hσL i hi k hk hmeet
  obtain ⟨A₀, hA₀, hal⟩ := hzero P.toLocalChartPacketsRVZ.toLocalChartPacketsZ hΛ hΔ hLΛ he hT hν3
    hβ3 hβ2σ hβ1 hσL i hi k hk hmeet
  refine ⟨A₀, hA₀, fun x hx => ?_⟩
  rw [single_three_term_PKG]
  exact hal x hx

/-- **TCP02, the complete row on the final closed family**: for a target error `E₀` and `ν`
(`3ν ≤ β₃ < 1`) there are an early `σ ≤ 1/1000`, an early circle quality bound `η₂` and, for every
`Δ ≥ 1`, a quality bound `η₁` such that every actual `P : LocalChartPacketsC14Z` in FC07's ranges
with `3β₂ ≤ σ`, `β₂ ≤ η₂`, `β₁, b ≤ η₁`, `σ⁻¹ ≤ Lmax` has, at every circle centre `i`, for the SAME
`i`, `ρ(i)` and reference coordinate `u_i`: (TR) for every circle, slim and edge chart `j` whose
closed support meets `D_i = B(i, 10ρ(i))`, and (TR0) for every zero ball whose closed support meets
`D_i`, all on `B(i, 1000ρ(i))` with translation `c_j = s_ju_j(p_i)` (`c₀ = ρ(i)⁻¹d(p₀, p_i)`). -/
theorem tcp02_full_row_PKG {E₀ ν : ℝ} (hE : 0 < E₀) (hν : 0 < ν) (hν1 : ν < 1) :
    ∃ σ : ℝ, 0 < σ ∧ σ ≤ 1 / 1000 ∧ ∃ η₂ : ℝ, 0 < η₂ ∧ ∀ Δ : ℝ, 1 ≤ Δ → ∃ η₁ : ℝ, 0 < η₁ ∧
    ∀ {X : Type} [MetricSpace X] [ChartedSpace E3 X] [IsManifold 𝓘(ℝ, E3) ∞ X]
      [CompactSpace X] {g : SmoothRiemannianMetric 𝓘(ℝ, E3) X}
      {hmetric : ∀ a b : X, riemannianEDistOf g a b = ENNReal.ofReal (dist a b)}
      {ρ : X → ℝ} {hρ : ∀ p, 0 < ρ p} {Λ : ℝ} {β : ℕ → ℝ} {σs : ℝ} {K : ℕ}
      {σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V vs ζ Λz : ℝ}
      {oM : ManifoldOrientation 𝓘(ℝ, E3) X 3}
      (P : LocalChartPacketsC14Z X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc Lmax τ γ δ εr
        e T V vs ζ Λz oM),
      0 ≤ Λ → μ ≤ 1 / 100 → τ ≤ 1 / 100 → 1000000 * Δ * Λ < 1 / 100000 →
      4 * (10 + 2 * (2000000 * Δ) + Δ / 3) ≤ Lmax → e < 1 / 40 → 1600 * (1000000 * Δ) ≤ T →
      3 * ν ≤ β 3 → β 3 < 1 → 3 * β 2 ≤ σ → β 2 ≤ η₂ → β 1 ≤ η₁ → b ≤ η₁ → σ⁻¹ ≤ Lmax →
      ∀ i ∈ P.circle.centres,
        (∀ j ∈ P.circle.centres, (tsupport (P.circle.cutoff j) ∩ ball i (10 * ρ i)).Nonempty →
          ∃ A : ℝ² →L[ℝ] ℝ², A.comp (ContinuousLinearMap.adjoint A) = ContinuousLinearMap.id ℝ _ ∧
            ∀ x, dist x i < 1000 * ρ i →
              ‖(ρ j / ρ i) • circleRaw_KA3 P.toLocalChartPackets j x -
                A (circleRaw_KA3 P.toLocalChartPackets i x) -
                (ρ j / ρ i) • circleRaw_KA3 P.toLocalChartPackets j i‖ < E₀) ∧
        (∀ j ∈ P.slim.centres, (tsupport (P.slim.cutoff j) ∩ ball i (10 * ρ i)).Nonempty →
          ∃ A : ℝ² →L[ℝ] E1, A.comp (ContinuousLinearMap.adjoint A) = ContinuousLinearMap.id ℝ _ ∧
            ∀ x, dist x i < 1000 * ρ i →
              ‖(ρ j / ρ i) • EuclideanSpace.single 0 (slimRaw_KA3 P.toLocalChartFamily j x) -
                A (circleRaw_KA3 P.toLocalChartPackets i x) -
                (ρ j / ρ i) • EuclideanSpace.single 0 (slimRaw_KA3 P.toLocalChartFamily j i)‖ <
                E₀) ∧
        (∀ j ∈ P.edge.centres, (tsupport (P.edge.cutoff j) ∩ ball i (10 * ρ i)).Nonempty →
          ∃ A : ℝ² →L[ℝ] E1, A.comp (ContinuousLinearMap.adjoint A) = ContinuousLinearMap.id ℝ _ ∧
            ∀ x, dist x i < 1000 * ρ i →
              ‖(ρ j / ρ i) • EuclideanSpace.single 0 (edgeRaw_KA3 P.toLocalChartFamily j x) -
                A (circleRaw_KA3 P.toLocalChartPackets i x) -
                (ρ j / ρ i) • EuclideanSpace.single 0 (edgeRaw_KA3 P.toLocalChartFamily j i)‖ <
                E₀) ∧
        ∀ k (hk : k ∈ P.zero.centres),
          (tsupport (fun y => Calculus.annularCutoff Calculus.cutoffProfile
            ((P.zero.zero k hk).radial y)) ∩ ball i (10 * ρ i)).Nonempty →
          ∃ A₀ : ℝ² →L[ℝ] E1,
            A₀.comp (ContinuousLinearMap.adjoint A₀) = ContinuousLinearMap.id ℝ _ ∧
            ∀ x, dist x i < 1000 * ρ i →
              ‖EuclideanSpace.single 0 ((ρ i)⁻¹ * dist k x) -
                  A₀ (circleRaw_KA3 P.toLocalChartPackets i x) -
                  EuclideanSpace.single 0 ((ρ i)⁻¹ * dist k i)‖ < E₀ := by
  obtain ⟨σ, hσ, hσ1, η₂, hη₂, hrow⟩ := tcp02_rowZ hE hν hν1
  refine ⟨σ, hσ, hσ1, η₂, hη₂, fun Δ hΔ => ?_⟩
  obtain ⟨η₁, hη₁, hrow'⟩ := hrow Δ hΔ
  refine ⟨η₁, hη₁, ?_⟩
  intro X _ _ _ _ g hmetric ρ hρ Λ β σs K σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V vs ζ Λz oM P
    hΛ hμ hτ hLΛ hLmax he hT hν3 hβ3 hβ2σ hβ2 hβ1 hb hσL i hi
  obtain ⟨hc, hsl, hed, hz⟩ := hrow' P.toLocalChartPacketsRVZ.toLocalChartPacketsZ hΛ hμ hτ hLΛ
    hLmax he hT hν3 hβ3 hβ2σ hβ2 hβ1 hb hσL i hi
  refine ⟨hc, hsl, hed, fun k hk hmeet => ?_⟩
  obtain ⟨A₀, hA₀, hal⟩ := hz k hk hmeet
  refine ⟨A₀, hA₀, fun x hx => ?_⟩
  rw [single_three_term_PKG]
  exact hal x hx

/-- **Consumer: the difference form of the zero clause on the final family** (as TCP03's zero block
reads TCP02): under the threshold choice of `tcp02_full_row_PKG`, at every circle centre `i` and
every zero ball meeting `D_i`, `‖e₀ρ(i)⁻¹(d(p₀, x) − d(p₀, y)) − A₀(u_i x − u_i y)‖ < 2E₀` on
`B(i, 1000ρ(i))`. -/
theorem tcp02_full_row_zero_difference_PKG {E₀ ν : ℝ} (hE : 0 < E₀) (hν : 0 < ν) (hν1 : ν < 1) :
    ∃ σ : ℝ, 0 < σ ∧ σ ≤ 1 / 1000 ∧ ∃ η₂ : ℝ, 0 < η₂ ∧ ∀ Δ : ℝ, 1 ≤ Δ → ∃ η₁ : ℝ, 0 < η₁ ∧
    ∀ {X : Type} [MetricSpace X] [ChartedSpace E3 X] [IsManifold 𝓘(ℝ, E3) ∞ X]
      [CompactSpace X] {g : SmoothRiemannianMetric 𝓘(ℝ, E3) X}
      {hmetric : ∀ a b : X, riemannianEDistOf g a b = ENNReal.ofReal (dist a b)}
      {ρ : X → ℝ} {hρ : ∀ p, 0 < ρ p} {Λ : ℝ} {β : ℕ → ℝ} {σs : ℝ} {K : ℕ}
      {σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V vs ζ Λz : ℝ}
      {oM : ManifoldOrientation 𝓘(ℝ, E3) X 3}
      (P : LocalChartPacketsC14Z X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc Lmax τ γ δ εr
        e T V vs ζ Λz oM),
      0 ≤ Λ → μ ≤ 1 / 100 → τ ≤ 1 / 100 → 1000000 * Δ * Λ < 1 / 100000 →
      4 * (10 + 2 * (2000000 * Δ) + Δ / 3) ≤ Lmax → e < 1 / 40 → 1600 * (1000000 * Δ) ≤ T →
      3 * ν ≤ β 3 → β 3 < 1 → 3 * β 2 ≤ σ → β 2 ≤ η₂ → β 1 ≤ η₁ → b ≤ η₁ → σ⁻¹ ≤ Lmax →
      ∀ i ∈ P.circle.centres, ∀ k (hk : k ∈ P.zero.centres),
        (tsupport (fun y => Calculus.annularCutoff Calculus.cutoffProfile
          ((P.zero.zero k hk).radial y)) ∩ ball i (10 * ρ i)).Nonempty →
        ∃ A₀ : ℝ² →L[ℝ] E1,
          A₀.comp (ContinuousLinearMap.adjoint A₀) = ContinuousLinearMap.id ℝ _ ∧
          ∀ x y, dist x i < 1000 * ρ i → dist y i < 1000 * ρ i →
            ‖EuclideanSpace.single 0 ((ρ i)⁻¹ * (dist k x - dist k y)) -
              A₀ (circleRaw_KA3 P.toLocalChartPackets i x -
                circleRaw_KA3 P.toLocalChartPackets i y)‖ < 2 * E₀ := by
  obtain ⟨σ, hσ, hσ1, η₂, hη₂, hrow⟩ := tcp02_full_row_PKG hE hν hν1
  refine ⟨σ, hσ, hσ1, η₂, hη₂, fun Δ hΔ => ?_⟩
  obtain ⟨η₁, hη₁, hrow'⟩ := hrow Δ hΔ
  refine ⟨η₁, hη₁, ?_⟩
  intro X _ _ _ _ g hmetric ρ hρ Λ β σs K σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V vs ζ Λz oM P
    hΛ hμ hτ hLΛ hLmax he hT hν3 hβ3 hβ2σ hβ2 hβ1 hb hσL i hi k hk hmeet
  obtain ⟨A₀, hA₀, hal⟩ := (hrow' P hΛ hμ hτ hLΛ hLmax he hT hν3 hβ3 hβ2σ hβ2 hβ1 hb hσL i
    hi).2.2.2 k hk hmeet
  refine ⟨A₀, hA₀, fun x y hx hy => ?_⟩
  have h := norm_sub_sub_lt_of_affine_KA3 A₀ (s := 1)
    (c := EuclideanSpace.single 0 ((ρ i)⁻¹ * dist k i))
    (a := EuclideanSpace.single 0 ((ρ i)⁻¹ * dist k x))
    (a' := EuclideanSpace.single 0 ((ρ i)⁻¹ * dist k y))
    (by rw [one_smul]; exact hal x hx) (by rw [one_smul]; exact hal y hy)
  rw [one_smul, single_zero_sub_KA5, ← mul_sub] at h
  exact h

end DifferentialGeometry.Geometry.Collapse
