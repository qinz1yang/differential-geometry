import DifferentialGeometry.Geometry.Fibration.ActualZeroConstantComparison
import DifferentialGeometry.Geometry.Fibration.ActualSlimConstantComparison
import DifferentialGeometry.Geometry.Fibration.ActualRawAlignmentFullPackage
import DifferentialGeometry.Geometry.Fibration.ActualSlimStrictComparisonPackage

/-!
# TCP03: the four comparison kinds in ONE output shape on the final closed family

External review 60 (§四.5) and dispositions-task60 ("SGP03, TCP03: faithful as the parts read
together — record a combined output shape"). Blueprint `master207B.tex`, TCP03 (B:5370–5440). The
consumption shape of the review is `∀ i, ∀ j ∈ J_i^circle ⊔ J_i^slim ⊔ J_i^edge ⊔ J_i^0,
∃ A_ij, c_ij, Coisometry ∧ Raw ∧ Value ∧ Derivative`; here the disjoint union is written as four
conjuncts with the SAME clause shape (no new proof: the four registered parts `tcp03_circle_row`,
`tcp03_slim_row`, `tcp03_edge_row`, `tcp03_zero_row` under ONE threshold choice, as `tcp05_row`
assembles them).

* `tcp03_full_row_PKG`: on `P : LocalChartPacketsC14Z`, ONE early `σ ≤ 1/1000`, `η₂`, `γ₀` and, for
  every `Δ ≥ 3`, ONE `η₁`; at every circle centre `i`, every chart `j` of each kind whose closed
  support meets `D_i = B(i, 10ρ(i))` has ONE coisometry `A` with
  (Raw) `‖s_ju_j(x) − Au_i(x) − c_j‖ < θ²/1000` on `B(i, 1000ρ(i))`, `c_j = s_ju_j(p_i)`
  (zero kind: `s₀u₀ = ρ(i)⁻¹d(p₀, ·)`),
  (Value) `‖U_j(x) − Aη_i(x) − c'_j‖ ≤ θ/2` and (Derivative) `‖DU_j(w) − ADη_i(w)‖ ≤ (θ/2)|w|` on
  `D_i` (`U_j = s_jη_j`, `c'_j = c_j` except the zero kind, `c'_0 = U₀(p_i)`; norms of `ρ(i)⁻²g`).
* consumer `tcp03_full_row_strict_PKG`: the strict `< θ|w|` derivative reading (`w ≠ 0`) for the
  four kinds at once.
-/

set_option autoImplicit false

noncomputable section

open Set Function Metric
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

/-- **TCP03, the four kinds in one output shape on the final closed family** (see the module
docstring). Hypotheses: FC07's ranges and TCP03's quality bounds at `θ` (those of `tcp05_row`
without TCP04's). -/
theorem tcp03_full_row_PKG {θ ν : ℝ} (hθ : 0 < θ) (hθ1 : θ < 1) (hν : 0 < ν) (hν1 : ν < 1) :
    ∃ σ : ℝ, 0 < σ ∧ σ ≤ 1 / 1000 ∧ ∃ η₂ γ₀ : ℝ, 0 < η₂ ∧ 0 < γ₀ ∧
    ∀ Δ : ℝ, 3 ≤ Δ → ∃ η₁ : ℝ, 0 < η₁ ∧
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
      σc ≤ θ ^ 2 / 1000 → μ * Δ ≤ θ / 100 →
      3 * ν ≤ β 3 → β 3 < 1 → 3 * β 2 ≤ σ → β 2 ≤ η₂ → γ ≤ γ₀ → b ≤ η₁ → β 1 ≤ η₁ → 0 < σs →
      σs ≤ θ ^ 2 / 1000 → vs ≤ θ / 100 → 0 < ζ → ζ ≤ θ ^ 2 / 1000 → εr ≤ θ / 100 →
      20 * Λz ≤ T → σ⁻¹ ≤ Lmax →
      ∀ i (hi : i ∈ P.circle.centres),
        (∀ j (hj : j ∈ P.circle.centres),
          (tsupport (P.circle.cutoff j) ∩ ball i (10 * ρ i)).Nonempty →
          ∃ A : ℝ² →L[ℝ] ℝ², A.comp (ContinuousLinearMap.adjoint A) = ContinuousLinearMap.id ℝ _ ∧
            (∀ x, dist x i < 1000 * ρ i →
              ‖(ρ j / ρ i) • circleRaw_KA3 P.toLocalChartPackets j x -
                A (circleRaw_KA3 P.toLocalChartPackets i x) -
                (ρ j / ρ i) • circleRaw_KA3 P.toLocalChartPackets j i‖ < θ ^ 2 / 1000) ∧
            ∀ x ∈ ball i (10 * ρ i),
              ‖(ρ j / ρ i) • cgpCircleCoord P.toLocalChartFamily j hj x -
                  A (cgpCircleCoord P.toLocalChartFamily i hi x) -
                  (ρ j / ρ i) • circleRaw_KA3 P.toLocalChartPackets j i‖ ≤ θ / 2 ∧
              ∀ w : TangentSpace 𝓘(ℝ, E3) x,
                ‖(ρ j / ρ i) • mvfderiv 𝓘(ℝ, E3) (cgpCircleCoord P.toLocalChartFamily j hj) x w -
                    A (mvfderiv 𝓘(ℝ, E3) (cgpCircleCoord P.toLocalChartFamily i hi) x w)‖ ≤
                  θ / 2 * Real.sqrt ((ρ i)⁻¹ ^ 2 * g.inner x w w)) ∧
        (∀ j (hj : j ∈ P.slim.centres), (tsupport (P.slim.cutoff j) ∩ ball i (10 * ρ i)).Nonempty →
          ∃ A : ℝ² →L[ℝ] E1, A.comp (ContinuousLinearMap.adjoint A) = ContinuousLinearMap.id ℝ _ ∧
            (∀ x, dist x i < 1000 * ρ i →
              ‖(ρ j / ρ i) • EuclideanSpace.single 0 (slimRaw_KA3 P.toLocalChartFamily j x) -
                A (circleRaw_KA3 P.toLocalChartPackets i x) -
                (ρ j / ρ i) • EuclideanSpace.single 0 (slimRaw_KA3 P.toLocalChartFamily j i)‖ <
                θ ^ 2 / 1000) ∧
            ∀ x ∈ ball i (10 * ρ i),
              ‖(ρ j / ρ i) • EuclideanSpace.single 0 ((P.slim.centre j hj).coord x) -
                  A (cgpCircleCoord P.toLocalChartFamily i hi x) -
                  (ρ j / ρ i) • EuclideanSpace.single 0 (slimRaw_KA3 P.toLocalChartFamily j i)‖ ≤
                θ / 2 ∧
              ∀ w : TangentSpace 𝓘(ℝ, E3) x,
                ‖(ρ j / ρ i) • EuclideanSpace.single 0
                      (mvfderiv 𝓘(ℝ, E3) (P.slim.centre j hj).coord x w) -
                    A (mvfderiv 𝓘(ℝ, E3) (cgpCircleCoord P.toLocalChartFamily i hi) x w)‖ ≤
                  θ / 2 * Real.sqrt ((ρ i)⁻¹ ^ 2 * g.inner x w w)) ∧
        (∀ j ∈ P.edge.centres, (tsupport (P.edge.cutoff j) ∩ ball i (10 * ρ i)).Nonempty →
          ∃ A : ℝ² →L[ℝ] E1, A.comp (ContinuousLinearMap.adjoint A) = ContinuousLinearMap.id ℝ _ ∧
            (∀ x, dist x i < 1000 * ρ i →
              ‖(ρ j / ρ i) • EuclideanSpace.single 0 (edgeRaw_KA3 P.toLocalChartFamily j x) -
                A (circleRaw_KA3 P.toLocalChartPackets i x) -
                (ρ j / ρ i) • EuclideanSpace.single 0 (edgeRaw_KA3 P.toLocalChartFamily j i)‖ <
                θ ^ 2 / 1000) ∧
            ∀ x ∈ ball i (10 * ρ i),
              ‖(ρ j / ρ i) • EuclideanSpace.single 0 (P.edge.coord j x) -
                  A (cgpCircleCoord P.toLocalChartFamily i hi x) -
                  (ρ j / ρ i) • EuclideanSpace.single 0 (edgeRaw_KA3 P.toLocalChartFamily j i)‖ ≤
                θ / 2 ∧
              ∀ w : TangentSpace 𝓘(ℝ, E3) x,
                ‖(ρ j / ρ i) • EuclideanSpace.single 0
                      (mvfderiv 𝓘(ℝ, E3) (P.edge.coord j) x w) -
                    A (mvfderiv 𝓘(ℝ, E3) (cgpCircleCoord P.toLocalChartFamily i hi) x w)‖ ≤
                  θ / 2 * Real.sqrt ((ρ i)⁻¹ ^ 2 * g.inner x w w)) ∧
        ∀ k (hk : k ∈ P.zero.centres),
          (tsupport (fun y => Calculus.annularCutoff Calculus.cutoffProfile
            ((P.zero.zero k hk).radial y)) ∩ ball i (10 * ρ i)).Nonempty →
          ∃ A : ℝ² →L[ℝ] E1, A.comp (ContinuousLinearMap.adjoint A) = ContinuousLinearMap.id ℝ _ ∧
            (∀ x, dist x i < 1000 * ρ i →
              ‖EuclideanSpace.single 0 ((ρ i)⁻¹ * dist k x) -
                A (circleRaw_KA3 P.toLocalChartPackets i x) -
                EuclideanSpace.single 0 ((ρ i)⁻¹ * dist k i)‖ < θ ^ 2 / 1000) ∧
            ∀ x ∈ ball i (10 * ρ i),
              ‖EuclideanSpace.single 0
                    ((P.zero.zero k hk).radius / ρ i * (P.zero.zero k hk).radial x) -
                  A (cgpCircleCoord P.toLocalChartFamily i hi x) -
                  EuclideanSpace.single 0
                    ((P.zero.zero k hk).radius / ρ i * (P.zero.zero k hk).radial i)‖ ≤ θ / 2 ∧
              ∀ w : TangentSpace 𝓘(ℝ, E3) x,
                ‖EuclideanSpace.single 0 ((P.zero.zero k hk).radius / ρ i *
                      mvfderiv 𝓘(ℝ, E3) (P.zero.zero k hk).radial x w) -
                    A (mvfderiv 𝓘(ℝ, E3) (cgpCircleCoord P.toLocalChartFamily i hi) x w)‖ ≤
                  θ / 2 * Real.sqrt ((ρ i)⁻¹ ^ 2 * g.inner x w w) := by
  have hθ2 : θ ^ 2 / 2000 < θ ^ 2 / 1000 := by
    have : 0 < θ ^ 2 := by positivity
    linarith
  obtain ⟨σ1, hσ1, hσ11, η21, hη21, γ01, hγ01, hcirc⟩ := tcp03_circle_row hθ hθ1 hν hν1
  obtain ⟨σ2, hσ2, -, γ02, hγ02, hslim⟩ := tcp03_slim_row hθ hθ1 hν hν1
  obtain ⟨σ3, hσ3, -, γ03, hγ03, hedge⟩ := tcp03_edge_row hθ hθ1 hν hν1
  obtain ⟨σ4, hσ4, -, η24, hη24, γ04, hγ04, η14, hη14, hzero⟩ := tcp03_zero_row hθ hθ1 hν hν1
  set σ := min σ1 (min σ2 (min σ3 σ4)) with hσdef
  have hσ0 : 0 < σ := lt_min hσ1 (lt_min hσ2 (lt_min hσ3 hσ4))
  have hσle1 : σ ≤ σ1 := min_le_left _ _
  have hσle2 : σ ≤ σ2 := (min_le_right _ _).trans (min_le_left _ _)
  have hσle3 : σ ≤ σ3 := (min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _))
  have hσle4 : σ ≤ σ4 := (min_le_right _ _).trans ((min_le_right _ _).trans (min_le_right _ _))
  refine ⟨σ, hσ0, hσle1.trans hσ11, min η21 η24, min γ01 (min γ02 (min γ03 γ04)),
    lt_min hη21 hη24, lt_min hγ01 (lt_min hγ02 (lt_min hγ03 hγ04)), fun Δ hΔ => ?_⟩
  have hΔ1 : (1 : ℝ) ≤ Δ := le_trans (by norm_num) hΔ
  obtain ⟨η12, hη12, hslimΔ⟩ := hslim Δ hΔ1
  obtain ⟨η13, hη13, hedgeΔ⟩ := hedge Δ hΔ
  refine ⟨min η12 (min η13 η14), lt_min hη12 (lt_min hη13 hη14), ?_⟩
  intro X _ _ _ _ g hmetric ρ hρ Λ β σs K σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V vs ζ Λz oM P
    hΛ hμ hτ hLΛ hLmax he hT hσcθ hμΔ hν3 hβ3 h3β2 hβ2 hγ hb hβ1 hσs hσsθ hvs hζ hζθ hεr hΛz hσL
    i hi
  have hinv : ∀ σ' : ℝ, σ ≤ σ' → σ'⁻¹ ≤ Lmax := fun σ' h => (inv_anti₀ hσ0 h).trans hσL
  have hCrow := hcirc P.toLocalChartPackets hΛ hΔ1 hμ hτ hLΛ hLmax he hT hν3 hβ3
    (h3β2.trans hσle1) (hβ2.trans (min_le_left _ _)) (hγ.trans (min_le_left _ _)) (hinv _ hσle1)
    i hi
  have hSrow := hslimΔ P.toLocalChartPacketsRVZ.toLocalChartPacketsRV hΛ hμ hτ hLΛ hLmax he hT hν3
    hβ3 (h3β2.trans hσle2) (hγ.trans ((min_le_right _ _).trans (min_le_left _ _)))
    (hβ1.trans (min_le_left _ _)) hσs hσsθ hvs (hinv _ hσle2) i hi
  have hErow := hedgeΔ P.toLocalChartPackets hΛ hμ hτ hLΛ hLmax he hT hν3 hβ3 (h3β2.trans hσle3)
    (hγ.trans ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _))))
    (hb.trans ((min_le_right _ _).trans (min_le_left _ _))) hσcθ hμΔ (hinv _ hσle3) i hi
  have hZrow := hzero P.toLocalChartPacketsRVZ.toLocalChartPacketsZ hΛ hΔ1 hLΛ he hT hν3 hβ3
    (h3β2.trans hσle4) (hβ2.trans (min_le_right _ _))
    (hγ.trans ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_right _ _))))
    (hβ1.trans ((min_le_right _ _).trans (min_le_right _ _))) hζ hζθ hεr hΛz (hinv _ hσle4) i hi
  refine ⟨fun j hj hm => hCrow j hj hm, fun j hj hm => ?_, fun j hj hm => ?_,
    fun k hk hm => ?_⟩
  · obtain ⟨A, hA, hR, hTC⟩ := hSrow j hj hm
    exact ⟨A, hA, fun x hx => (hR x hx).trans hθ2, hTC⟩
  · obtain ⟨A, hA, hR, hTC⟩ := hErow j hj hm
    exact ⟨A, hA, fun x hx => (hR x hx).trans hθ2, hTC⟩
  · obtain ⟨A, hA, hR, hTC⟩ := hZrow k hk hm
    refine ⟨A, hA, fun x hx => ?_, fun x hx => ?_⟩
    · rw [single_three_term_PKG]
      exact (hR x hx).trans hθ2
    · obtain ⟨hv, hd⟩ := hTC x hx
      refine ⟨?_, hd⟩
      rw [single_three_term_PKG]
      exact hv

/-- **Consumer: the strict derivative reading of TCP03 for the four kinds at once.** Under the
thresholds of `tcp03_full_row_PKG`, at every circle centre `i`, every listed chart of each kind has
ONE coisometry `A` with `‖DU_j(w) − ADη_i(w)‖ < θ|w|` for every `w ≠ 0` on `D_i`. -/
theorem tcp03_full_row_strict_PKG {θ ν : ℝ} (hθ : 0 < θ) (hθ1 : θ < 1) (hν : 0 < ν)
    (hν1 : ν < 1) :
    ∃ σ : ℝ, 0 < σ ∧ σ ≤ 1 / 1000 ∧ ∃ η₂ γ₀ : ℝ, 0 < η₂ ∧ 0 < γ₀ ∧
    ∀ Δ : ℝ, 3 ≤ Δ → ∃ η₁ : ℝ, 0 < η₁ ∧
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
      σc ≤ θ ^ 2 / 1000 → μ * Δ ≤ θ / 100 →
      3 * ν ≤ β 3 → β 3 < 1 → 3 * β 2 ≤ σ → β 2 ≤ η₂ → γ ≤ γ₀ → b ≤ η₁ → β 1 ≤ η₁ → 0 < σs →
      σs ≤ θ ^ 2 / 1000 → vs ≤ θ / 100 → 0 < ζ → ζ ≤ θ ^ 2 / 1000 → εr ≤ θ / 100 →
      20 * Λz ≤ T → σ⁻¹ ≤ Lmax →
      ∀ i (hi : i ∈ P.circle.centres),
        (∀ j (hj : j ∈ P.circle.centres),
          (tsupport (P.circle.cutoff j) ∩ ball i (10 * ρ i)).Nonempty →
          ∃ A : ℝ² →L[ℝ] ℝ², A.comp (ContinuousLinearMap.adjoint A) = ContinuousLinearMap.id ℝ _ ∧
            ∀ x ∈ ball i (10 * ρ i), ∀ w : TangentSpace 𝓘(ℝ, E3) x, w ≠ 0 →
              ‖(ρ j / ρ i) • mvfderiv 𝓘(ℝ, E3) (cgpCircleCoord P.toLocalChartFamily j hj) x w -
                  A (mvfderiv 𝓘(ℝ, E3) (cgpCircleCoord P.toLocalChartFamily i hi) x w)‖ <
                θ * Real.sqrt ((ρ i)⁻¹ ^ 2 * g.inner x w w)) ∧
        (∀ j (hj : j ∈ P.slim.centres), (tsupport (P.slim.cutoff j) ∩ ball i (10 * ρ i)).Nonempty →
          ∃ A : ℝ² →L[ℝ] E1, A.comp (ContinuousLinearMap.adjoint A) = ContinuousLinearMap.id ℝ _ ∧
            ∀ x ∈ ball i (10 * ρ i), ∀ w : TangentSpace 𝓘(ℝ, E3) x, w ≠ 0 →
              ‖(ρ j / ρ i) • EuclideanSpace.single 0
                    (mvfderiv 𝓘(ℝ, E3) (P.slim.centre j hj).coord x w) -
                  A (mvfderiv 𝓘(ℝ, E3) (cgpCircleCoord P.toLocalChartFamily i hi) x w)‖ <
                θ * Real.sqrt ((ρ i)⁻¹ ^ 2 * g.inner x w w)) ∧
        (∀ j ∈ P.edge.centres, (tsupport (P.edge.cutoff j) ∩ ball i (10 * ρ i)).Nonempty →
          ∃ A : ℝ² →L[ℝ] E1, A.comp (ContinuousLinearMap.adjoint A) = ContinuousLinearMap.id ℝ _ ∧
            ∀ x ∈ ball i (10 * ρ i), ∀ w : TangentSpace 𝓘(ℝ, E3) x, w ≠ 0 →
              ‖(ρ j / ρ i) • EuclideanSpace.single 0
                    (mvfderiv 𝓘(ℝ, E3) (P.edge.coord j) x w) -
                  A (mvfderiv 𝓘(ℝ, E3) (cgpCircleCoord P.toLocalChartFamily i hi) x w)‖ <
                θ * Real.sqrt ((ρ i)⁻¹ ^ 2 * g.inner x w w)) ∧
        ∀ k (hk : k ∈ P.zero.centres),
          (tsupport (fun y => Calculus.annularCutoff Calculus.cutoffProfile
            ((P.zero.zero k hk).radial y)) ∩ ball i (10 * ρ i)).Nonempty →
          ∃ A : ℝ² →L[ℝ] E1, A.comp (ContinuousLinearMap.adjoint A) = ContinuousLinearMap.id ℝ _ ∧
            ∀ x ∈ ball i (10 * ρ i), ∀ w : TangentSpace 𝓘(ℝ, E3) x, w ≠ 0 →
              ‖EuclideanSpace.single 0 ((P.zero.zero k hk).radius / ρ i *
                    mvfderiv 𝓘(ℝ, E3) (P.zero.zero k hk).radial x w) -
                  A (mvfderiv 𝓘(ℝ, E3) (cgpCircleCoord P.toLocalChartFamily i hi) x w)‖ <
                θ * Real.sqrt ((ρ i)⁻¹ ^ 2 * g.inner x w w) := by
  obtain ⟨σ, hσ, hσ1, η₂, γ₀, hη₂, hγ₀, hrow⟩ := tcp03_full_row_PKG hθ hθ1 hν hν1
  refine ⟨σ, hσ, hσ1, η₂, γ₀, hη₂, hγ₀, fun Δ hΔ => ?_⟩
  obtain ⟨η₁, hη₁, hrow'⟩ := hrow Δ hΔ
  refine ⟨η₁, hη₁, ?_⟩
  intro X _ _ _ _ g hmetric ρ hρ Λ β σs K σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V vs ζ Λz oM P
    hΛ hμ hτ hLΛ hLmax he hT hσcθ hμΔ hν3 hβ3 h3β2 hβ2 hγ hb hβ1 hσs hσsθ hvs hζ hζθ hεr hΛz hσL
    i hi
  have hq : ∀ x (w : TangentSpace 𝓘(ℝ, E3) x), w ≠ 0 → 0 < (ρ i)⁻¹ ^ 2 * g.inner x w w :=
    fun x w hw => mul_pos (by have := hρ i; positivity) (g.pos x w hw)
  obtain ⟨hC, hS, hE, hZ⟩ := hrow' P hΛ hμ hτ hLΛ hLmax he hT hσcθ hμΔ hν3 hβ3 h3β2 hβ2 hγ hb hβ1
    hσs hσsθ hvs hζ hζθ hεr hΛz hσL i hi
  refine ⟨fun j hj hm => ?_, fun j hj hm => ?_, fun j hj hm => ?_, fun k hk hm => ?_⟩
  · obtain ⟨A, hA, -, hTC⟩ := hC j hj hm
    exact ⟨A, hA, fun x hx w hw =>
      lt_of_le_half_mul_sqrt_PKG hθ (hq x w hw) ((hTC x hx).2 w)⟩
  · obtain ⟨A, hA, -, hTC⟩ := hS j hj hm
    exact ⟨A, hA, fun x hx w hw =>
      lt_of_le_half_mul_sqrt_PKG hθ (hq x w hw) ((hTC x hx).2 w)⟩
  · obtain ⟨A, hA, -, hTC⟩ := hE j hj hm
    exact ⟨A, hA, fun x hx w hw =>
      lt_of_le_half_mul_sqrt_PKG hθ (hq x w hw) ((hTC x hx).2 w)⟩
  · obtain ⟨A, hA, -, hTC⟩ := hZ k hk hm
    exact ⟨A, hA, fun x hx w hw =>
      lt_of_le_half_mul_sqrt_PKG hθ (hq x w hw) ((hTC x hx).2 w)⟩

end DifferentialGeometry.Geometry.Collapse
