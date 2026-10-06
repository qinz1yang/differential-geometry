import DifferentialGeometry.Geometry.Collapse.FixtureC2.SphereLoopChainRows5

/-!
# SGP04, SGP05 and SGP06 on the closed sphere-loop packet (S-FIXTURE-C2d, G8 file 3)

`loopSlimRows5_sgp_FXC2`: for every closed C2 family `PZ` (every `ℓ`, `R`, orientation parameter,
register `Δ = 1200`, `K = 5`, `εr = 0`, all other scalars `0`) whose numeric parameters satisfy the
facts exported by `loopSlimRows5_FXC2` (`β 2 = β₂`, `β 1 ≤ η'`, `L_c' ≤ L_max`, `0 < σ_s < θ'²/10⁶`,
`v_s < θ'/100`, `0 < ζ < θ'²/10⁶`, `ζ < 1/(100 · 10⁶ Δ)`), the generic rows `hS` (the first
components of `loopSlimRows5_FXC2`) give, on `P = C14of PZ`: SGP04 (`Sgp04OutV2`), SGP06
(`Sgp06OutV2`) and the SGP05 conclusion of `sgp05_row_C14`, verbatim, at the C2 types
(`ρ i.1 = R`, `g = loopMetric3_FXC2 ℓ`).
-/

set_option autoImplicit false
noncomputable section
open Set Function Metric Bundle Manifold Filter GC.MetricGeometry
open scoped ContDiff Manifold Topology ENNReal
open DifferentialGeometry DifferentialGeometry.Geometry DifferentialGeometry.Geometry.Riemannian
open DifferentialGeometry.Geometry.Collapse

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace
attribute [local instance] sphereDimension cylinderDimension sphereCompact sphereConnected
  intrinsicMetric intrinsicUniform intrinsicEMetric intrinsicPseudoMetric intrinsicBundle
  cylinderRiemannian cylinderContinuous cylinderComplete
attribute [local instance] loopMS3_FXC2
attribute [local instance] nezero_finrank_euclideanThree_LC87
attribute [local instance] instMetricNC14_FXC2 instChartedNC14_FXC2 instMetricCC14_FXC2

namespace DifferentialGeometry.Geometry.Collapse

local notation "E3" => EuclideanSpace ℝ (Fin 3)

local notation "C14of" PZ => LocalChartPacketsC14D.toLocalChartPacketsC14
  (LocalChartPacketsC14Z.toLocalChartPacketsC14D PZ)

/-- **SGP04, SGP05 and SGP06 on the closed C2 packet** at the register of
`loopSlimRows5_FXC2`. See the module docstring. -/
theorem loopSlimRows5_sgp_FXC2 {β₂ θ' Lc' η' Γ₆ sg eg₆ : ℝ}
    (hS :
      ∀ (X : Type) [MetricSpace X] [ChartedSpace E3 X] [IsManifold 𝓘(ℝ, E3) ∞ X]
        [CompactSpace X] (g : SmoothRiemannianMetric 𝓘(ℝ, E3) X)
        (hmetric : ∀ a b : X, riemannianEDistOf g a b = ENNReal.ofReal (dist a b))
        (ρ : X → ℝ) (hρ : ∀ p, 0 < ρ p) (Λ : ℝ) (β : ℕ → ℝ) (σs : ℝ) (K : ℕ)
        (σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V vs ζ Λz : ℝ)
        (P : LocalChartPacketsC14 X g hmetric ρ hρ Λ β 1200 σs K σc μ b s b' s' ε γc βc Lmax τ γ δ
          εr e T V vs ζ Λz),
        β 2 = β₂ → β 1 ≤ η' → Lc' ≤ Lmax → 0 ≤ Λ → 1000000 * 1200 * Λ < 1 / 100000 →
        e < 1 / 40 → 1600 * (1000000 * 1200) ≤ T → 20 * Λz ≤ T →
        0 < σs → σs < θ' ^ 2 / 10 ^ 6 → vs < θ' / 100 →
        0 < ζ → ζ < θ' ^ 2 / 10 ^ 6 → ζ < 1 / (100 * (1000000 * 1200)) →
        εr < θ' / (100 * (1000000 * 1200)) →
        Sgp04OutV2 P.toLocalChartPacketsRVZ (1 / 200 : ℝ) ∧ Sgp06OutV2 P Γ₆ sg eg₆ ∧
        ∀ i : P.toLocalChartFamily.slim.finite_centres.toFinset,
          ∃ sgn c zsgn zc : X → ℝ,
          (∀ j, |sgn j| ≤ 1) ∧ (∀ k, |zsgn k| ≤ 1) ∧
          (∀ x ∈ ball i.1 (10 ^ 6 * 1200 * ρ i.1),
            |(P.slim.centre i.1 ((Set.Finite.mem_toFinset _).mp i.2)).coord x| ≤
              8 * 10 ^ 5 * 1200 →
            ‖(ρ i.1)⁻¹ • cgpProjMap P.toLocalChartFamily P.zero
                (cgpQ3Tags P.toLocalChartFamily P.zero) x -
              sgpFullGraph P.toLocalChartFamily P.zero i sgn c zsgn zc
                ((P.slim.centre i.1 ((Set.Finite.mem_toFinset _).mp i.2)).coord x)‖ <
              (1 / 200 : ℝ) ∧
            ∀ w : TangentSpace 𝓘(ℝ, E3) x,
              ‖(ρ i.1)⁻¹ • mvfderiv 𝓘(ℝ, E3) (cgpProjMap P.toLocalChartFamily P.zero
                  (cgpQ3Tags P.toLocalChartFamily P.zero)) x w -
                fderiv ℝ (sgpFullGraph P.toLocalChartFamily P.zero i sgn c zsgn zc)
                  ((P.slim.centre i.1 ((Set.Finite.mem_toFinset _).mp i.2)).coord x)
                  (mvfderiv 𝓘(ℝ, E3) (P.slim.centre i.1
                    ((Set.Finite.mem_toFinset _).mp i.2)).coord x w)‖ ≤
                (1 / 200 : ℝ) * Real.sqrt ((ρ i.1)⁻¹ ^ 2 * g.inner x w w)) ∧
          ∀ p ∈ ball i.1 (10 ^ 6 * 1200 * ρ i.1),
            |(P.slim.centre i.1 ((Set.Finite.mem_toFinset _).mp i.2)).coord p| ≤
              7 * (10 ^ 5 * 1200) →
            ∀ q, cgpProjMap P.toLocalChartFamily P.zero (cgpQ3Tags P.toLocalChartFamily P.zero) q =
              cgpProjMap P.toLocalChartFamily P.zero (cgpQ3Tags P.toLocalChartFamily P.zero) p →
            let Tx := fderiv ℝ (sgpFullGraph P.toLocalChartFamily P.zero i sgn c zsgn zc)
              ((P.slim.centre i.1 ((Set.Finite.mem_toFinset _).mp i.2)).coord p)
            let Pq := Tx.range.orthogonalProjectionOnto.comp ((ρ i.1)⁻¹ • mvfderiv 𝓘(ℝ, E3)
              (cgpProjMap P.toLocalChartFamily P.zero (cgpQ3Tags P.toLocalChartFamily P.zero)) q)
            Function.Surjective Pq ∧
            (∀ v, ‖(ρ i.1)⁻¹ • mvfderiv 𝓘(ℝ, E3) (cgpProjMap P.toLocalChartFamily P.zero
                (cgpQ3Tags P.toLocalChartFamily P.zero)) q v - (Pq v : BlockSpace _)‖ ≤
              (1 / 200 : ℝ) * Real.sqrt ((ρ i.1)⁻¹ ^ 2 * g.inner q v v)) ∧
            (∀ v, (∀ k, Pq k = 0 → g.inner q v k = 0) →
              1 / 2 * Real.sqrt ((ρ i.1)⁻¹ ^ 2 * g.inner q v v) ≤ ‖Pq v‖) ∧
            ∀ v, ‖Pq v‖ ≤ 3 * sgpGraphBound * Real.sqrt ((ρ i.1)⁻¹ ^ 2 * g.inner q v v))
    {ℓ : LoopLen_FXC2} {R : ℝ} {hR : 0 < R} {β : ℕ → ℝ} {σs vs γc Lmax ζ : ℝ}
    (hθ' : 0 < θ') (hβ : β 2 = β₂) (hη : β 1 ≤ η') (hL : Lc' ≤ Lmax) (hσs : 0 < σs)
    (hσ : σs < θ' ^ 2 / 10 ^ 6) (hv : vs < θ' / 100) (hζ : 0 < ζ) (hζ1 : ζ < θ' ^ 2 / 10 ^ 6)
    (hζ2 : ζ < 1 / (100 * (1000000 * 1200))) {oM : ManifoldOrientation 𝓘(ℝ, E3) (LoopC_FXC2 ℓ) 3}
    (PZ : LocalChartPacketsC14Z (LoopC_FXC2 ℓ) (loopMetric3_FXC2 ℓ) (loopMS3_hmetric_FXC2 ℓ)
      (fun _ => R) (fun _ => hR) 0 β 1200 σs 5 0 0 0 0 0 0 0 γc 0 Lmax 0 0 0 0 0
      (1600 * (1000000 * 1200)) 0 vs ζ 0 oM)
    (P : LocalChartPacketsC14 (LoopC_FXC2 ℓ) (loopMetric3_FXC2 ℓ) (loopMS3_hmetric_FXC2 ℓ)
      (fun _ => R) (fun _ => hR) 0 β 1200 σs 5 0 0 0 0 0 0 0 γc 0 Lmax 0 0 0 0 0
      (1600 * (1000000 * 1200)) 0 vs ζ 0)
    (hP : P = (C14of PZ)) :
        Sgp04OutV2 P.toLocalChartPacketsRVZ (1 / 200 : ℝ) ∧ Sgp06OutV2 P Γ₆ sg eg₆ ∧
        ∀ i : P.toLocalChartFamily.slim.finite_centres.toFinset, ∃ sgn c zsgn zc : LoopC_FXC2 ℓ → ℝ,
          (∀ j, |sgn j| ≤ 1) ∧ (∀ k, |zsgn k| ≤ 1) ∧
          (∀ x ∈ ball i.1 (10 ^ 6 * 1200 * R),
            |(P.slim.centre i.1 ((Set.Finite.mem_toFinset _).mp i.2)).coord x| ≤
              8 * 10 ^ 5 * 1200 →
            ‖R⁻¹ • cgpProjMap P.toLocalChartFamily P.zero
                (cgpQ3Tags P.toLocalChartFamily P.zero) x -
              sgpFullGraph P.toLocalChartFamily P.zero i sgn c zsgn zc
                ((P.slim.centre i.1 ((Set.Finite.mem_toFinset _).mp i.2)).coord x)‖ <
              (1 / 200 : ℝ) ∧
            ∀ w : TangentSpace 𝓘(ℝ, E3) x,
              ‖R⁻¹ • mvfderiv 𝓘(ℝ, E3) (cgpProjMap P.toLocalChartFamily P.zero
                  (cgpQ3Tags P.toLocalChartFamily P.zero)) x w -
                fderiv ℝ (sgpFullGraph P.toLocalChartFamily P.zero i sgn c zsgn zc)
                  ((P.slim.centre i.1 ((Set.Finite.mem_toFinset _).mp i.2)).coord x)
                  (mvfderiv 𝓘(ℝ, E3) (P.slim.centre i.1
                    ((Set.Finite.mem_toFinset _).mp i.2)).coord x w)‖ ≤
                (1 / 200 : ℝ) * Real.sqrt (R⁻¹ ^ 2 * (loopMetric3_FXC2 ℓ).inner x w w)) ∧
          ∀ p ∈ ball i.1 (10 ^ 6 * 1200 * R),
            |(P.slim.centre i.1 ((Set.Finite.mem_toFinset _).mp i.2)).coord p| ≤
              7 * (10 ^ 5 * 1200) →
            ∀ q, cgpProjMap P.toLocalChartFamily P.zero (cgpQ3Tags P.toLocalChartFamily P.zero) q =
              cgpProjMap P.toLocalChartFamily P.zero (cgpQ3Tags P.toLocalChartFamily P.zero) p →
            let Tx := fderiv ℝ (sgpFullGraph P.toLocalChartFamily P.zero i sgn c zsgn zc)
              ((P.slim.centre i.1 ((Set.Finite.mem_toFinset _).mp i.2)).coord p)
            let Pq := Tx.range.orthogonalProjectionOnto.comp (R⁻¹ • mvfderiv 𝓘(ℝ, E3)
              (cgpProjMap P.toLocalChartFamily P.zero (cgpQ3Tags P.toLocalChartFamily P.zero)) q)
            Function.Surjective Pq ∧
            (∀ v, ‖R⁻¹ • mvfderiv 𝓘(ℝ, E3) (cgpProjMap P.toLocalChartFamily P.zero
                (cgpQ3Tags P.toLocalChartFamily P.zero)) q v - (Pq v : BlockSpace _)‖ ≤
              (1 / 200 : ℝ) * Real.sqrt (R⁻¹ ^ 2 * (loopMetric3_FXC2 ℓ).inner q v v)) ∧
            (∀ v, (∀ k, Pq k = 0 → (loopMetric3_FXC2 ℓ).inner q v k = 0) →
              1 / 2 * Real.sqrt (R⁻¹ ^ 2 * (loopMetric3_FXC2 ℓ).inner q v v) ≤ ‖Pq v‖) ∧
            ∀ v, ‖Pq v‖ ≤ 3 * sgpGraphBound *
              Real.sqrt (R⁻¹ ^ 2 * (loopMetric3_FXC2 ℓ).inner q v v) := by
  subst hP
  exact hS _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ (C14of PZ) hβ hη hL le_rfl
    (by norm_num) (by norm_num) le_rfl (by norm_num) hσs hσ hv hζ hζ1 hζ2 (by positivity)

end DifferentialGeometry.Geometry.Collapse
