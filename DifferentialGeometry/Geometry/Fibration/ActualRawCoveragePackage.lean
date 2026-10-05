import DifferentialGeometry.Geometry.Fibration.ActualEdgeZeroComparisonApplications
import DifferentialGeometry.Geometry.Fibration.ActualZeroRawAlignment
import DifferentialGeometry.Geometry.Collapse.LocalExport.LocalChartPacketsC14ZeroTypes

/-!
# SGP02 and EGP03 as whole rows on the final closed family: alignment AND buffered raw coverage

External review 60 (§三 SGP02 / EGP03, §四.2, §七.2) and dispositions-task60: the registered entries
return the raw alignments (RA, R0 / ER, ER0) but not the row's buffered raw coverage clause, which
"cannot be read off the RA output" and must be listed in the row's package on the SAME `P`.
Blueprint `master207B.tex`: SGP02 (B:4410–4481): "Every original raw tested ball contains the
radius-`100L` ball about its own center. The reference product map has distortion at most `δ` on
that ball and actual lifts in `B(p_i, 21L)` to error less than `δ` for target points of radius less
than `20L`"; EGP03 (B:4897–4941): the same for every original edge / slim raw splitting.

The coverage clauses EXIST in the tree: `sgp02_reference_tests` (slim splittings) and
`egp03_reference_tests` (edge splittings), for `β₁` resp. `b ≤ min(1/(1000L), δ/100)`; no new Prop.

* `sgp02_full_row_PKG`: on `P : LocalChartPacketsC14Z`, ONE threshold choice `Lc, η₀`; at every slim
  reference `i` (same `i`, same `ρ(i)`): (RA) for every `j ∈ J_i` on `B(i, 30Lρ(i))`; `a_i = 1`,
  `c_i = 0`; (R0) for every zero support meeting `D_i`; the buffered raw coverage of the reference
  splitting and of every listed splitting.
* `egp03_full_row_PKG`: on `P : LocalChartPacketsC14Z`, ONE threshold choice; at every edge
  reference `i`: (ER) on `J_e ∪ J_s`, (ER0), `a_i = 1`, `c_i = 0`, the buffered raw coverage of the reference
  edge splitting, of every listed edge splitting and of every listed slim splitting.
* consumer `sgp02_raw_lipschitz_PKG`: the reference raw coordinate is `1`-Lipschitz up to `δ` on
  `B(i, 100Lρ(i))` (reference units), from the coverage clause of the whole row.
-/

set_option autoImplicit false

noncomputable section

open Set Function Metric
open scoped ContDiff Manifold Topology
open DifferentialGeometry.Geometry.Riemannian GC.MetricGeometry
open DifferentialGeometry.Analysis

namespace DifferentialGeometry.Geometry.Collapse

local notation "E3" => EuclideanSpace ℝ (Fin 3)

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace

attribute [local instance] nezero_finrank_euclideanThree_LC87

attribute [local instance] LocalChartPackets.instMetricN LocalChartPackets.instChartedN
  LocalChartPackets.instMetricC

/-- **SGP02, the whole row on the final closed family.** Fix `Δ ≥ 1`, the exclusion quality `β₂`,
the coverage tolerance `δr > 0` and `E > 0`. There are ONE curvature radius `Lc` and ONE raw quality
`η₀` such that for EVERY actual `P : LocalChartPacketsC14Z` with `β 2 = β₂`, `β 1 ≤ η₀`,
`Lc ≤ Lmax`, `10⁶ΔΛ < 10⁻⁵`, `e < 1/40`, `T ≥ 1600L`, at every slim centre `i`: (RA) for every
`j ∈ J_i`; `a_i = 1, c_i = 0`; (R0) for every zero ball whose support meets `D_i = B(i, .95Lρ(i))`;
and the buffered raw coverage of the reference and of every listed splitting `j`: tested radius
`β₁⁻¹ ≥ 100L`, distortion `≤ δr` on `B(j, 100Lρ(j))`, lifts of targets of radius `< 20L` in
`B(j, 21Lρ(j))` to error `< δr` (units `ρ(j)⁻¹d`). -/
theorem sgp02_full_row_PKG {Δ β₂ δr E : ℝ} (hΔ : 1 ≤ Δ) (hβ₂ : 0 < β₂) (hβ₂1 : β₂ < 1)
    (hδr : 0 < δr) (hE : 0 < E) :
    ∃ Lc η₀ : ℝ, 0 < Lc ∧ 0 < η₀ ∧
      ∀ (X : Type) [MetricSpace X] [ChartedSpace E3 X] [IsManifold 𝓘(ℝ, E3) ∞ X]
        [CompactSpace X] (g : SmoothRiemannianMetric 𝓘(ℝ, E3) X)
        (hmetric : ∀ a b : X, riemannianEDistOf g a b = ENNReal.ofReal (dist a b))
        (ρ : X → ℝ) (hρ : ∀ p, 0 < ρ p) (Λ : ℝ) (β : ℕ → ℝ) (σs : ℝ) (K : ℕ)
        (σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V vs ζ Λz : ℝ)
        (oM : ManifoldOrientation 𝓘(ℝ, E3) X 3)
        (P : LocalChartPacketsC14Z X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc Lmax τ γ δ
          εr e T V vs ζ Λz oM),
        β 2 = β₂ → β 1 ≤ η₀ → Lc ≤ Lmax → 0 ≤ Λ → 1000000 * Δ * Λ < 1 / 100000 →
        e < 1 / 40 → 1600 * (1000000 * Δ) ≤ T →
        ∀ i ∈ P.slim.centres,
          (∀ j ∈ sgpSlimList P.slim i, ∃ a : ℝ, (a = 1 ∨ a = -1) ∧
            ∀ x ∈ ball i (30 * (1000000 * Δ) * ρ i),
              |ρ j / ρ i * sgpRaw P.slim j x - a * sgpRaw P.slim i x -
                ρ j / ρ i * sgpRaw P.slim j i| < E) ∧
          (∀ x, ρ i / ρ i * sgpRaw P.slim i x - 1 * sgpRaw P.slim i x -
            ρ i / ρ i * sgpRaw P.slim i i = 0) ∧
          (∀ k (hk : k ∈ P.zero.centres),
            (tsupport (fun y => Calculus.annularCutoff Calculus.cutoffProfile
              ((P.zero.zero k hk).radial y)) ∩ ball i (95 / 100 * (1000000 * Δ) * ρ i)).Nonempty →
            ∃ a₀ : ℝ, (a₀ = 1 ∨ a₀ = -1) ∧ ∀ x ∈ ball i (30 * (1000000 * Δ) * ρ i),
              |(ρ i)⁻¹ * (dist k x - dist k i) - a₀ * sgpRaw P.slim i x| < E) ∧
          ∀ j (hj : j ∈ P.slim.centres), (j = i ∨ j ∈ sgpSlimList P.slim i) →
            letI := (P.slim.centre j hj).instZ
            100 * (1000000 * Δ) ≤ (β 1)⁻¹ ∧
              (∀ x ∈ ball j (100 * (1000000 * Δ) * ρ j),
                ∀ x' ∈ ball j (100 * (1000000 * Δ) * ρ j),
                |dist (sgpSplitMap (P.slim.centre j hj) x) (sgpSplitMap (P.slim.centre j hj) x') -
                  (ρ j)⁻¹ * dist x x'| ≤ δr) ∧
              ∀ y, dist y (sgpSplitMap (P.slim.centre j hj) j) < 20 * (1000000 * Δ) →
                ∃ x ∈ ball j (21 * (1000000 * Δ) * ρ j),
                  dist y (sgpSplitMap (P.slim.centre j hj) x) < δr := by
  obtain ⟨L₁, η₁, hL₁, hη₁, h1⟩ := sgp02_row hΔ hβ₂ hβ₂1 hE
  obtain ⟨L₂, η₂, hL₂, hη₂, h2⟩ := sgp02_zero_supplier_ZERO hΔ hβ₂ hβ₂1 hE
  refine ⟨max L₁ L₂, min (min η₁ η₂) (min (1 / (1000 * (1000000 * Δ))) (δr / 100)),
    lt_max_of_lt_left hL₁, lt_min (lt_min hη₁ hη₂) (lt_min (by positivity) (by positivity)), ?_⟩
  intro X _ _ _ _ g hmetric ρ hρ Λ β σs K σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V vs ζ Λz oM P
    hβ2 hβ1 hLmax hΛ hLΛ he hT i hi
  have hβ₁ : β 1 ≤ η₁ := hβ1.trans ((min_le_left _ _).trans (min_le_left _ _))
  have hβ₂' : β 1 ≤ η₂ := hβ1.trans ((min_le_left _ _).trans (min_le_right _ _))
  have hβc : β 1 ≤ min (1 / (1000 * (1000000 * Δ))) (δr / 100) := hβ1.trans (min_le_right _ _)
  refine ⟨h1 X g hmetric ρ hρ Λ β σs K σc μ b s b' s' ε γc βc Lmax P.toLocalChartFamilyQ hβ2 hβ₁
      ((le_max_left _ _).trans hLmax) hΛ hLΛ i hi,
    sgp02_self P.slim i,
    h2 X g hmetric ρ hρ Λ β σs K σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V ζ Λz
      P.toLocalChartPacketsRVZ.toLocalChartPacketsZ hβ2 hβ₂' ((le_max_right _ _).trans hLmax) hΛ
      hLΛ he hT i hi,
    fun j hj _ => sgp02_reference_tests P.slim hΔ hβc hj⟩

/-- **EGP03, the whole row on the final closed family.** Fix `Δ ≥ 1`, the exclusion quality
`β₂ < 10⁻⁶`, the coverage tolerance `δr > 0` and `E > 0`. There are ONE curvature radius `Lc` and
ONE raw quality `η₀` such that for EVERY actual `P : LocalChartPacketsC14Z` with `b, β₁ ≤ η₀`,
`s < 10⁻⁶`, `Lc ≤ Lmax`, `10⁶ΔΛ < 10⁻⁵`, `μ, τ ≤ 1/100`, `e < 1/40`, `T ≥ 1600L`, at every edge
centre `i` (same `i`, same `ρ(i)`): (ER) for `J_e` and `J_s` on `B(i, 600Δρ(i))`, (ER0) for every
zero ball whose support meets `D_i = B(i, 20Δρ(i))`, `a_i = 1, c_i = 0`, and the buffered raw
coverage of the reference edge splitting, of every listed edge splitting (an original splitting
whose real factor is `egpRaw`) and of every listed slim splitting. -/
theorem egp03_full_row_PKG {Δ β₂ δr E : ℝ} (hΔ : 1 ≤ Δ) (hβ₂ : 0 < β₂)
    (hβ₂1 : β₂ < 1 / 1000000) (hδr : 0 < δr) (hE : 0 < E) :
    ∃ Lc η₀ : ℝ, 0 < Lc ∧ 0 < η₀ ∧
      ∀ (X : Type) [mX : MetricSpace X] [ChartedSpace E3 X] [IsManifold 𝓘(ℝ, E3) ∞ X]
        [CompactSpace X] (g : SmoothRiemannianMetric 𝓘(ℝ, E3) X)
        (hmetric : ∀ a b : X, riemannianEDistOf g a b = ENNReal.ofReal (dist a b))
        (ρ : X → ℝ) (hρ : ∀ p, 0 < ρ p) (Λ : ℝ) (β : ℕ → ℝ) (σs : ℝ) (K : ℕ)
        (σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V vs ζ Λz : ℝ)
        (oM : ManifoldOrientation 𝓘(ℝ, E3) X 3)
        (P : LocalChartPacketsC14Z X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc Lmax τ γ δ
          εr e T V vs ζ Λz oM),
        b ≤ η₀ → s < 1 / 1000000 → β 1 ≤ η₀ → Lc ≤ Lmax → 0 ≤ Λ →
        1000000 * Δ * Λ < 1 / 100000 → μ ≤ 1 / 100 → τ ≤ 1 / 100 → e < 1 / 40 →
        1600 * (1000000 * Δ) ≤ T → ∀ i ∈ P.edge.centres,
          (∀ j ∈ egpEdgeList P.toLocalChartFamily i, ∃ a : ℝ, (a = 1 ∨ a = -1) ∧
            ∀ x ∈ ball i (600 * Δ * ρ i),
              |ρ j / ρ i * egpRaw P.edge j x - a * egpRaw P.edge i x -
                ρ j / ρ i * egpRaw P.edge j i| < E) ∧
          (∀ j ∈ egpSlimList P.toLocalChartFamily i, ∃ a : ℝ, (a = 1 ∨ a = -1) ∧
            ∀ x ∈ ball i (600 * Δ * ρ i),
              |ρ j / ρ i * sgpRaw P.slim j x - a * egpRaw P.edge i x -
                ρ j / ρ i * sgpRaw P.slim j i| < E) ∧
          (∀ k (hk : k ∈ P.zero.centres),
            (tsupport (fun y => Calculus.annularCutoff Calculus.cutoffProfile
              ((P.zero.zero k hk).radial y)) ∩ ball i (20 * Δ * ρ i)).Nonempty →
            ∃ a₀ : ℝ, (a₀ = 1 ∨ a₀ = -1) ∧ ∀ x ∈ ball i (600 * Δ * ρ i),
              |(ρ i)⁻¹ * (dist k x - dist k i) - a₀ * egpRaw P.edge i x| < E) ∧
          (∀ x, ρ i / ρ i * egpRaw P.edge i x - 1 * egpRaw P.edge i x -
            ρ i / ρ i * egpRaw P.edge i i = 0) ∧
          (∀ j ∈ P.edge.centres, (j = i ∨ j ∈ egpEdgeList P.toLocalChartFamily i) →
            ∃ (Y : Type) (mY : MetricSpace Y), letI := mY
              ∃ q : Y, ∃ f : @KleinerLottApprox X (WithLp 2 (ℝ × Y))
                  (mX.rescale (ρ j)⁻¹ (inv_pos.mpr (hρ j))) _ j (WithLp.toLp 2 ((0 : ℝ), q)) b,
                let u := @KleinerLottApprox.toFun X _ (mX.rescale (ρ j)⁻¹ (inv_pos.mpr (hρ j))) _
                  _ _ _ f
                (∀ x, (u x).fst = egpRaw P.edge j x) ∧ 100 * (1000000 * Δ) ≤ b⁻¹ ∧
                  (∀ x ∈ ball j (100 * (1000000 * Δ) * ρ j),
                    ∀ x' ∈ ball j (100 * (1000000 * Δ) * ρ j),
                    |dist (u x) (u x') - (ρ j)⁻¹ * dist x x'| ≤ δr) ∧
                  ∀ y, dist y (u j) < 20 * (1000000 * Δ) →
                    ∃ x ∈ ball j (21 * (1000000 * Δ) * ρ j), dist y (u x) < δr) ∧
          ∀ j (hj : j ∈ egpSlimList P.toLocalChartFamily i),
            letI := (P.slim.centre j hj.1).instZ
            100 * (1000000 * Δ) ≤ (β 1)⁻¹ ∧
              (∀ x ∈ ball j (100 * (1000000 * Δ) * ρ j),
                ∀ x' ∈ ball j (100 * (1000000 * Δ) * ρ j),
                |dist (sgpSplitMap (P.slim.centre j hj.1) x)
                    (sgpSplitMap (P.slim.centre j hj.1) x') - (ρ j)⁻¹ * dist x x'| ≤ δr) ∧
              ∀ y, dist y (sgpSplitMap (P.slim.centre j hj.1) j) < 20 * (1000000 * Δ) →
                ∃ x ∈ ball j (21 * (1000000 * Δ) * ρ j),
                  dist y (sgpSplitMap (P.slim.centre j hj.1) x) < δr := by
  obtain ⟨L₁, η₁, hL₁, hη₁, h1⟩ := egp03_full_row hΔ hβ₂ hβ₂1 hE
  refine ⟨L₁, min η₁ (min (1 / (1000 * (1000000 * Δ))) (δr / 100)), hL₁,
    lt_min hη₁ (lt_min (by positivity) (by positivity)), ?_⟩
  intro X _ _ _ _ g hmetric ρ hρ Λ β σs K σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V vs ζ Λz oM P
    hb hs hβ1 hLmax hΛ hLΛ hμ hτ he hT i hi
  have hbc : b ≤ min (1 / (1000 * (1000000 * Δ))) (δr / 100) := hb.trans (min_le_right _ _)
  have hβc : β 1 ≤ min (1 / (1000 * (1000000 * Δ))) (δr / 100) := hβ1.trans (min_le_right _ _)
  obtain ⟨hE', hS', hZ'⟩ := h1 X g hmetric ρ hρ Λ β σs K σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V
    ζ Λz P.toLocalChartPacketsRVZ.toLocalChartPacketsZ (hb.trans (min_le_left _ _)) hs
    (hβ1.trans (min_le_left _ _)) hLmax hΛ hLΛ hμ hτ he hT i hi
  exact ⟨hE', hS', hZ', egp03_self P.edge i, fun j hj _ => egp03_reference_tests P.edge hΔ hbc hj,
    fun j hj => sgp02_reference_tests P.slim hΔ hβc hj.1⟩

/-- **Consumer: the reference raw coordinate is `1`-Lipschitz up to `δr`** on `B(i, 100Lρ(i))`
(reference units), from the buffered raw coverage of SGP02's whole row on the final family:
`|u_i(x) − u_i(x')| ≤ ρ(i)⁻¹d(x, x') + δr`. -/
theorem sgp02_raw_lipschitz_PKG {Δ β₂ δr E : ℝ} (hΔ : 1 ≤ Δ) (hβ₂ : 0 < β₂) (hβ₂1 : β₂ < 1)
    (hδr : 0 < δr) (hE : 0 < E) :
    ∃ Lc η₀ : ℝ, 0 < Lc ∧ 0 < η₀ ∧
      ∀ (X : Type) [MetricSpace X] [ChartedSpace E3 X] [IsManifold 𝓘(ℝ, E3) ∞ X]
        [CompactSpace X] (g : SmoothRiemannianMetric 𝓘(ℝ, E3) X)
        (hmetric : ∀ a b : X, riemannianEDistOf g a b = ENNReal.ofReal (dist a b))
        (ρ : X → ℝ) (hρ : ∀ p, 0 < ρ p) (Λ : ℝ) (β : ℕ → ℝ) (σs : ℝ) (K : ℕ)
        (σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V vs ζ Λz : ℝ)
        (oM : ManifoldOrientation 𝓘(ℝ, E3) X 3)
        (P : LocalChartPacketsC14Z X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc Lmax τ γ δ
          εr e T V vs ζ Λz oM),
        β 2 = β₂ → β 1 ≤ η₀ → Lc ≤ Lmax → 0 ≤ Λ → 1000000 * Δ * Λ < 1 / 100000 →
        e < 1 / 40 → 1600 * (1000000 * Δ) ≤ T →
        ∀ i ∈ P.slim.centres, ∀ x ∈ ball i (100 * (1000000 * Δ) * ρ i),
          ∀ x' ∈ ball i (100 * (1000000 * Δ) * ρ i),
            |sgpRaw P.slim i x - sgpRaw P.slim i x'| ≤ (ρ i)⁻¹ * dist x x' + δr := by
  obtain ⟨Lc, η₀, hLc, hη₀, hrow⟩ := sgp02_full_row_PKG hΔ hβ₂ hβ₂1 hδr hE
  refine ⟨Lc, η₀, hLc, hη₀, ?_⟩
  intro X _ _ _ _ g hmetric ρ hρ Λ β σs K σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V vs ζ Λz oM P
    hβ2 hβ1 hLmax hΛ hLΛ he hT i hi x hx x' hx'
  obtain ⟨-, -, -, hcov⟩ := hrow X g hmetric ρ hρ Λ β σs K σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T
    V vs ζ Λz oM P hβ2 hβ1 hLmax hΛ hLΛ he hT i hi
  let _ := (P.slim.centre i hi).instZ
  obtain ⟨-, hdist, -⟩ := hcov i hi (Or.inl rfl)
  have hd := hdist x hx x' hx'
  have hfst := WithLp.dist_fst_le (sgpSplitMap (P.slim.centre i hi) x)
    (sgpSplitMap (P.slim.centre i hi) x')
  rw [Real.dist_eq] at hfst
  rw [sgpRaw_of_mem P.slim hi, sgpRaw_of_mem P.slim hi]
  linarith [(abs_le.mp hd).2]

end DifferentialGeometry.Geometry.Collapse
