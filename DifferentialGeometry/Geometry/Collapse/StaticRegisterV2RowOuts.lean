import DifferentialGeometry.Geometry.Collapse.StaticRegisterV2Validity
import DifferentialGeometry.Geometry.Fibration.ActualCircleGram
import DifferentialGeometry.Geometry.Fibration.ActualRawAlignment
import DifferentialGeometry.Geometry.Fibration.ActualZeroConstantComparison
import DifferentialGeometry.Geometry.Fibration.ActualHeightComparison
import DifferentialGeometry.Geometry.Fibration.ActualEdgeRawAlignment
import DifferentialGeometry.Geometry.Fibration.ActualEdgeZeroComparisonApplications
import DifferentialGeometry.Geometry.Fibration.ActualSlimComparisonList
import DifferentialGeometry.Geometry.Fibration.ActualSlimRawAlignment
import DifferentialGeometry.Geometry.Fibration.ActualSlimZeroComparison

/-!
# The native conclusions of the early chapter-14 rows, as `Prop`s of a family (lane FC39-VAL3)

External review 52 ("Missing obligations to add"): the closed validity record carries, per slot, the
NATIVE conclusion of the rows that request it. This file states each early row's conclusion
verbatim as a `Prop` of the smallest family projection the row is stated on and of its tolerance,
and checks, by the accepted row itself, that the row concludes exactly that `Prop`.

* `Tcp01GramOutV2 P` (`tcp01_gram`, TCP01's Gram clause at every circle centre and every point of
  `B(j, 200ρ(j))`), `Sgp01OutV2 P` (`sgp01_row`, SGP01 at every slim centre: list, count `≤ N_*`,
  (SL), zero supports, enclosure): checks `tcp01_gram_out_VAL3`, `sgp01_row_out_VAL3`.
* `Tcp02OutV2 P E₀` (`tcp02_row`), `Tcp03ZeroOutV2 P θ` (`tcp03_zero_row`), `Tcp04OutV2 P θ`
  (`tcp04_row`), `Egp03OutV2 L E` (`egp03_row`), `Egp04OutV2 P θ` (`egp04_row_RVZ`),
  `Sgp02OutV2 Q E` (`sgp02_row`), `Sgp03ZeroOutV2 P θ E` (`sgp03_zero_row`; its conclusion reads
  the accuracy `E` as well): the verbatim checks `<row>_out_VAL3` restate each row with its
  conclusion replaced by the `Out` and are proved by the row.

The register values at which the record evaluates these `Out`s are fixed in
`StaticRegisterV2ValidityRows`.
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
local notation "ℝ¹" => EuclideanSpace ℝ (Fin 1)

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace

attribute [local instance] nezero_finrank_euclideanThree_LC87

section Outs

variable {X : Type} [MetricSpace X] [ChartedSpace E3 X] [IsManifold 𝓘(ℝ, E3) ∞ X]
  [CompactSpace X] {g : SmoothRiemannianMetric 𝓘(ℝ, E3) X}
  {hmetric : ∀ a b : X, riemannianEDistOf g a b = ENNReal.ofReal (dist a b)}
  {ρ : X → ℝ} {hρ : ∀ p, 0 < ρ p} {Λ : ℝ} {β : ℕ → ℝ} {Δ σs : ℝ} {K : ℕ}
  {σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V vs ζ Λz : ℝ}

/-- TCP01's Gram clause (`tcp01_gram`, verbatim conclusion) at every circle centre `j` and every
point `x` of `B(j, 200ρ(j))`, in the normalized metric `ρ(j)⁻² g`. -/
def Tcp01GramOutV2
    (P : LocalChartPackets X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V) :
    Prop :=
  ∀ j (hj : j ∈ P.circle.centres) x, x ∈ ball j (200 * ρ j) →
    (∀ w : TangentSpace 𝓘(ℝ, E3) x, (ρ j)⁻¹ ^ 2 * g.inner x w w = 1 →
      ‖mvfderiv 𝓘(ℝ, E3) (cgpCircleCoord P.toLocalChartFamily j hj) x w‖ ≤ 1 + γ) ∧
    ∀ ξ : ℝ², ‖ξ‖ = 1 → ∃ w : TangentSpace 𝓘(ℝ, E3) x, (ρ j)⁻¹ ^ 2 * g.inner x w w = 1 ∧
      ‖mvfderiv 𝓘(ℝ, E3) (cgpCircleCoord P.toLocalChartFamily j hj) x w - ξ‖ < γ + β 2 ∧
      1 - (γ + β 2) <
        inner ℝ (mvfderiv 𝓘(ℝ, E3) (cgpCircleCoord P.toLocalChartFamily j hj) x w) ξ

/-- **Verbatim check**: `tcp01_gram` concludes `Tcp01GramOutV2`. -/
theorem tcp01_gram_out_VAL3
    (P : LocalChartPackets X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V)
    (hγ : 0 ≤ γ) (hβ : β 2 ≤ 1 / 10000000) : Tcp01GramOutV2 P :=
  fun _ hj _ hx => tcp01_gram P hγ hβ hj hx

/-- SGP01's conclusion (`sgp01_row`, verbatim) at every slim centre `i`. -/
def Sgp01OutV2
    (P : LocalChartPacketsR X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T
      V) : Prop :=
  ∀ i (hi : i ∈ P.slim.centres),
    i ∈ sgpSlimList P.slim i ∧
    ((sgpSlimList P.slim i).ncard : ℝ) ≤ egp02SlimCount ∧
    (∀ j ∈ sgpSlimList P.slim i, 99 / 100 < ρ j / ρ i ∧ ρ j / ρ i < 101 / 100 ∧
      dist i j < 2 * (1000000 * Δ) * ρ i) ∧
    (∀ k₁ (hk₁ : k₁ ∈ P.zero.centres) k₂ (hk₂ : k₂ ∈ P.zero.centres),
      (tsupport (fun y => Calculus.annularCutoff Calculus.cutoffProfile
        ((P.zero.zero k₁ hk₁).radial y)) ∩ ball i (95 / 100 * (1000000 * Δ) * ρ i)).Nonempty →
      (tsupport (fun y => Calculus.annularCutoff Calculus.cutoffProfile
        ((P.zero.zero k₂ hk₂).radial y)) ∩ ball i (95 / 100 * (1000000 * Δ) * ρ i)).Nonempty →
      k₁ = k₂) ∧
    (∀ k (hk : k ∈ P.zero.centres),
      (tsupport (fun y => Calculus.annularCutoff Calculus.cutoffProfile
        ((P.zero.zero k hk).radial y)) ∩ ball i (95 / 100 * (1000000 * Δ) * ρ i)).Nonempty →
      T / 20 ≤ (P.zero.zero k hk).radius / ρ i ∧
      ∀ x ∈ ball i (95 / 100 * (1000000 * Δ) * ρ i),
        3 / 20 * (P.zero.zero k hk).radius < dist k x ∧
          dist k x < 19 / 20 * (P.zero.zero k hk).radius) ∧
    ∀ q ∈ ball i (10 ^ 6 * Δ * ρ i), |(P.slim.centre i hi).coord q| ≤ 8 * (100000 * Δ) →
      q ∈ ball i (91 / 100 * (10 ^ 6 * Δ) * ρ i)

/-- **Verbatim check**: `sgp01_row` concludes `Sgp01OutV2`. -/
theorem sgp01_row_out_VAL3
    (P : LocalChartPacketsR X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T
      V)
    (hΛ : 0 ≤ Λ) (hΔ : 1 ≤ Δ) (hLΛ : 1000000 * Δ * Λ < 1 / 100000) (he : e < 1 / 40)
    (hT : 1600 * (1000000 * Δ) ≤ T) (hσs : 0 ≤ σs) (hσs1 : σs ≤ 1 / 100) : Sgp01OutV2 P :=
  fun _ hi => sgp01_row P hΛ hΔ hLΛ he hT hσs hσs1 hi

/-- The conclusion of `tcp02_row` (verbatim) on `P`. -/
def Tcp02OutV2
    (P : LocalChartPackets X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V)
    (E₀ : ℝ) : Prop :=
  ∀ i ∈ P.circle.centres,
    (∀ j ∈ P.circle.centres, (tsupport (P.circle.cutoff j) ∩ ball i (10 * ρ i)).Nonempty →
      ∃ A : ℝ² →L[ℝ] ℝ², A.comp (ContinuousLinearMap.adjoint A) = ContinuousLinearMap.id ℝ _ ∧
        ∀ x, dist x i < 1000 * ρ i →
          ‖(ρ j / ρ i) • circleRaw_KA3 P j x - A (circleRaw_KA3 P i x) -
            (ρ j / ρ i) • circleRaw_KA3 P j i‖ < E₀) ∧
    (∀ j ∈ P.slim.centres, (tsupport (P.slim.cutoff j) ∩ ball i (10 * ρ i)).Nonempty →
      ∃ A : ℝ² →L[ℝ] EuclideanSpace ℝ (Fin 1),
        A.comp (ContinuousLinearMap.adjoint A) = ContinuousLinearMap.id ℝ _ ∧
        ∀ x, dist x i < 1000 * ρ i →
          ‖(ρ j / ρ i) • EuclideanSpace.single 0 (slimRaw_KA3 P.toLocalChartFamily j x) -
            A (circleRaw_KA3 P i x) -
            (ρ j / ρ i) • EuclideanSpace.single 0 (slimRaw_KA3 P.toLocalChartFamily j i)‖ <
            E₀) ∧
    ∀ j ∈ P.edge.centres, (tsupport (P.edge.cutoff j) ∩ ball i (10 * ρ i)).Nonempty →
      ∃ A : ℝ² →L[ℝ] EuclideanSpace ℝ (Fin 1),
        A.comp (ContinuousLinearMap.adjoint A) = ContinuousLinearMap.id ℝ _ ∧
        ∀ x, dist x i < 1000 * ρ i →
          ‖(ρ j / ρ i) • EuclideanSpace.single 0 (edgeRaw_KA3 P.toLocalChartFamily j x) -
            A (circleRaw_KA3 P i x) -
            (ρ j / ρ i) • EuclideanSpace.single 0 (edgeRaw_KA3 P.toLocalChartFamily j i)‖ <
            E₀

/-- The conclusion of `tcp03_zero_row` (verbatim) on `P`. -/
def Tcp03ZeroOutV2
    (P : LocalChartPacketsZ X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V
      ζ Λz)
    (θ : ℝ) : Prop :=
  ∀ i (hi : i ∈ P.circle.centres), ∀ k (hk : k ∈ P.zero.centres),
    (tsupport (fun y => Calculus.annularCutoff Calculus.cutoffProfile
      ((P.zero.zero k hk).radial y)) ∩ ball i (10 * ρ i)).Nonempty →
    ∃ A₀ : ℝ² →L[ℝ] ℝ¹,
      A₀.comp (ContinuousLinearMap.adjoint A₀) = ContinuousLinearMap.id ℝ _ ∧
      (∀ x, dist x i < 1000 * ρ i →
        ‖EuclideanSpace.single 0 ((ρ i)⁻¹ * (dist k x - dist k i)) -
          A₀ (circleRaw_KA3 P.toLocalChartPacketsR.toLocalChartPacketsD.toLocalChartPackets
            i x)‖ < θ ^ 2 / 2000) ∧
      ∀ x ∈ ball i (10 * ρ i),
        ‖EuclideanSpace.single 0 ((P.zero.zero k hk).radius / ρ i *
              ((P.zero.zero k hk).radial x - (P.zero.zero k hk).radial i)) -
            A₀ (cgpCircleCoord P.toLocalChartFamily i hi x)‖ ≤ θ / 2 ∧
        ∀ w : TangentSpace 𝓘(ℝ, E3) x,
          ‖EuclideanSpace.single 0 ((P.zero.zero k hk).radius / ρ i *
                mvfderiv 𝓘(ℝ, E3) (P.zero.zero k hk).radial x w) -
              A₀ (mvfderiv 𝓘(ℝ, E3) (cgpCircleCoord P.toLocalChartFamily i hi) x w)‖ ≤
            θ / 2 * Real.sqrt ((ρ i)⁻¹ ^ 2 * g.inner x w w)

/-- The conclusion of `tcp04_row` (verbatim) on `P`. -/
def Tcp04OutV2
    (P : LocalChartPackets X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V)
    (θ : ℝ) : Prop :=
  ∀ i (hi : i ∈ P.circle.centres),
    ((∀ j ∈ P.edge.centres, ¬ (tsupport (P.edge.cutoff j) ∩ ball i (10 * ρ i)).Nonempty) →
      ∀ j, ∀ x ∈ ball i (10 * ρ i), P.edge.cutoff j x = 0) ∧
    ((∃ j ∈ P.edge.centres, (tsupport (P.edge.cutoff j) ∩ ball i (10 * ρ i)).Nonempty) →
      (∀ x ∈ ball i (10 * ρ i), P.edge.smoothing x / ρ x < 3 * Δ / 20 ∧
        ∀ j ∈ P.edge.centres, x ∈ ball j (100 * Δ * ρ j) →
          P.edge.cutoff j x = edgeCoordinateProfile (P.edge.coord j x / Δ)) ∨
      ∃ B : ℝ² →L[ℝ] ℝ¹, B.comp (ContinuousLinearMap.adjoint B) = ContinuousLinearMap.id ℝ _ ∧
        ∀ x ∈ ball i (10 * ρ i),
          Δ / 10 ≤ P.edge.smoothing x / ρ x ∧ P.edge.smoothing x / ρ x ≤ 181 * Δ / 20 ∧
          ContMDiffAt 𝓘(ℝ, E3) 𝓘(ℝ, ℝ) ∞ (fun y => P.edge.smoothing y / ρ y) x ∧
          ‖EuclideanSpace.single 0 (P.edge.smoothing x / ρ x - P.edge.smoothing i / ρ i) -
              B (cgpCircleCoord P.toLocalChartFamily i hi x -
                cgpCircleCoord P.toLocalChartFamily i hi i)‖ ≤ θ / 2 ∧
          ∀ w : TangentSpace 𝓘(ℝ, E3) x,
            ‖EuclideanSpace.single 0
                  (mvfderiv 𝓘(ℝ, E3) (fun y => P.edge.smoothing y / ρ y) x w) -
                B (mvfderiv 𝓘(ℝ, E3) (cgpCircleCoord P.toLocalChartFamily i hi) x w)‖ ≤
              θ / 20 * Real.sqrt ((ρ i)⁻¹ ^ 2 * g.inner x w w) ∧
            |mvfderiv 𝓘(ℝ, E3) (fun y => P.edge.smoothing y / ρ y) x w| ≤
              2 * Real.sqrt ((ρ i)⁻¹ ^ 2 * g.inner x w w))

/-- The conclusion of `egp03_row` (verbatim) on `L`. -/
def Egp03OutV2
    (L : LocalChartFamilyE X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc Lmax τ)
    (E : ℝ) : Prop :=
  ∀ i ∈ L.edge.centres,
    (∀ j ∈ egpEdgeList L.toLocalChartFamily i, ∃ a : ℝ, (a = 1 ∨ a = -1) ∧
      ∀ x ∈ ball i (600 * Δ * ρ i),
        |ρ j / ρ i * egpRaw L.edge j x - a * egpRaw L.edge i x -
          ρ j / ρ i * egpRaw L.edge j i| < E) ∧
    (∀ j ∈ egpSlimList L.toLocalChartFamily i, ∃ a : ℝ, (a = 1 ∨ a = -1) ∧
      ∀ x ∈ ball i (600 * Δ * ρ i),
        |ρ j / ρ i * sgpRaw L.slim j x - a * egpRaw L.edge i x -
          ρ j / ρ i * sgpRaw L.slim j i| < E)

/-- The conclusion of `egp04_row_RVZ` (verbatim) on `P`. -/
def Egp04OutV2
    (P : LocalChartPacketsRVZ X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V
      vs ζ Λz)
    (θ : ℝ) : Prop :=
  ∀ i ∈ P.edge.centres,
    (∀ j ∈ egpEdgeList P.toLocalChartFamily i, ∃ a : ℝ, (a = 1 ∨ a = -1) ∧
      ∀ x ∈ ball i (20 * Δ * ρ i),
        |ρ j / ρ i * P.edge.coord j x -
            (a * P.edge.coord i x + ρ j / ρ i * egpRaw P.edge j i)| < θ ∧
          ∀ w : TangentSpace 𝓘(ℝ, E3) x, (ρ i)⁻¹ ^ 2 * g.inner x w w = 1 →
            |ρ j / ρ i * mvfderiv 𝓘(ℝ, E3) (P.edge.coord j) x w -
              a * mvfderiv 𝓘(ℝ, E3) (P.edge.coord i) x w| < θ) ∧
    (∀ j (hj : j ∈ P.slim.centres),
      (tsupport (P.slim.cutoff j) ∩ ball i (20 * Δ * ρ i)).Nonempty →
      ∃ a : ℝ, (a = 1 ∨ a = -1) ∧ ∀ x ∈ ball i (20 * Δ * ρ i),
        |ρ j / ρ i * (P.slim.centre j hj).coord x -
            (a * P.edge.coord i x + ρ j / ρ i * sgpRaw P.slim j i)| < θ ∧
          ∀ w : TangentSpace 𝓘(ℝ, E3) x, (ρ i)⁻¹ ^ 2 * g.inner x w w = 1 →
            |ρ j / ρ i * mvfderiv 𝓘(ℝ, E3) (P.slim.centre j hj).coord x w -
              a * mvfderiv 𝓘(ℝ, E3) (P.edge.coord i) x w| < θ) ∧
    ∀ k (hk : k ∈ P.zero.centres),
      (tsupport (fun y => Calculus.annularCutoff Calculus.cutoffProfile
        ((P.zero.zero k hk).radial y)) ∩ ball i (20 * Δ * ρ i)).Nonempty →
      ∃ a₀ : ℝ, (a₀ = 1 ∨ a₀ = -1) ∧ ∀ x ∈ ball i (20 * Δ * ρ i),
        |(P.zero.zero k hk).radius / ρ i * (P.zero.zero k hk).radial x -
            (a₀ * P.edge.coord i x +
              (P.zero.zero k hk).radius / ρ i * (P.zero.zero k hk).radial i)| < θ ∧
          ∀ w : TangentSpace 𝓘(ℝ, E3) x, (ρ i)⁻¹ ^ 2 * g.inner x w w = 1 →
            |(P.zero.zero k hk).radius / ρ i *
                mvfderiv 𝓘(ℝ, E3) (P.zero.zero k hk).radial x w -
              a₀ * mvfderiv 𝓘(ℝ, E3) (P.edge.coord i) x w| < θ

/-- The conclusion of `sgp02_row` (verbatim) on `Q`. -/
def Sgp02OutV2
    (Q : LocalChartFamilyQ X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc Lmax)
    (E : ℝ) : Prop :=
  ∀ i ∈ Q.slim.centres, ∀ j ∈ sgpSlimList Q.slim i, ∃ a : ℝ, (a = 1 ∨ a = -1) ∧
    ∀ x ∈ ball i (30 * (1000000 * Δ) * ρ i),
      |ρ j / ρ i * sgpRaw Q.slim j x - a * sgpRaw Q.slim i x -
        ρ j / ρ i * sgpRaw Q.slim j i| < E

/-- The conclusion of `sgp03_zero_row` (verbatim) on `P`. -/
def Sgp03ZeroOutV2
    (P : LocalChartPacketsRVZ X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V
      vs ζ Λz)
    (θ E : ℝ) : Prop :=
  ∀ i (hi : i ∈ P.slim.centres), ∀ k (hk : k ∈ P.zero.centres),
    (tsupport (fun y => Calculus.annularCutoff Calculus.cutoffProfile
      ((P.zero.zero k hk).radial y)) ∩ ball i (95 / 100 * (1000000 * Δ) * ρ i)).Nonempty →
    ∃ a₀ : ℝ, (a₀ = 1 ∨ a₀ = -1) ∧
      (∀ x ∈ ball i (30 * (1000000 * Δ) * ρ i),
        |(ρ i)⁻¹ * (dist k x - dist k i) - a₀ * sgpRaw P.slim i x| < E) ∧
      (∀ x ∈ ball i (95 / 100 * (1000000 * Δ) * ρ i), ∀ w : TangentSpace 𝓘(ℝ, E3) x,
        |(P.zero.zero k hk).radius / ρ i *
            mvfderiv 𝓘(ℝ, E3) (P.zero.zero k hk).radial x w -
          a₀ * mvfderiv 𝓘(ℝ, E3) (P.slim.centre i hi).coord x w| ≤
          θ * Real.sqrt ((ρ i)⁻¹ ^ 2 * g.inner x w w)) ∧
      ∀ x ∈ ball i (95 / 100 * (1000000 * Δ) * ρ i),
        |(P.zero.zero k hk).radius / ρ i * (P.zero.zero k hk).radial x -
          (a₀ * (P.slim.centre i hi).coord x +
            (P.zero.zero k hk).radius / ρ i * (P.zero.zero k hk).radial i)| < θ

end Outs

/-- **Verbatim check**: `tcp02_row` concludes the `Out` above. -/
theorem tcp02_row_out_VAL3 {E₀ ν : ℝ} (hE : 0 < E₀) (hν : 0 < ν) (hν1 : ν < 1) :
    ∃ σ : ℝ, 0 < σ ∧ σ ≤ 1 / 1000 ∧ ∃ η₂ : ℝ, 0 < η₂ ∧ ∀ Δ : ℝ, 1 ≤ Δ → ∃ η₁ : ℝ, 0 < η₁ ∧
    ∀ {X : Type} [MetricSpace X] [ChartedSpace E3 X] [IsManifold 𝓘(ℝ, E3) ∞ X]
      [CompactSpace X] {g : SmoothRiemannianMetric 𝓘(ℝ, E3) X}
      {hmetric : ∀ a b : X, riemannianEDistOf g a b = ENNReal.ofReal (dist a b)}
      {ρ : X → ℝ} {hρ : ∀ p, 0 < ρ p} {Λ : ℝ} {β : ℕ → ℝ} {σs : ℝ} {K : ℕ}
      {σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V : ℝ}
      (P : LocalChartPackets X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T
        V),
      0 ≤ Λ → μ ≤ 1 / 100 → τ ≤ 1 / 100 → 1000000 * Δ * Λ < 1 / 100000 →
      4 * (10 + 2 * (2000000 * Δ) + Δ / 3) ≤ Lmax → e < 1 / 40 → 1600 * (1000000 * Δ) ≤ T →
      3 * ν ≤ β 3 → β 3 < 1 → 3 * β 2 ≤ σ → β 2 ≤ η₂ → β 1 ≤ η₁ → b ≤ η₁ → σ⁻¹ ≤ Lmax →
      Tcp02OutV2 P E₀ :=
  tcp02_row hE hν hν1

/-- **Verbatim check**: `tcp03_zero_row` concludes the `Out` above. -/
theorem tcp03_zero_row_out_VAL3 {θ ν : ℝ} (hθ : 0 < θ) (hθ1 : θ < 1) (hν : 0 < ν) (hν1 : ν < 1) :
    ∃ σ : ℝ, 0 < σ ∧ σ ≤ 1 / 1000 ∧ ∃ η₂ : ℝ, 0 < η₂ ∧ ∃ γ₀ : ℝ, 0 < γ₀ ∧ ∃ η₁ : ℝ, 0 < η₁ ∧
    ∀ {X : Type} [MetricSpace X] [ChartedSpace E3 X] [IsManifold 𝓘(ℝ, E3) ∞ X]
      [CompactSpace X] {g : SmoothRiemannianMetric 𝓘(ℝ, E3) X}
      {hmetric : ∀ a b : X, riemannianEDistOf g a b = ENNReal.ofReal (dist a b)}
      {ρ : X → ℝ} {hρ : ∀ p, 0 < ρ p} {Λ : ℝ} {β : ℕ → ℝ} {Δ σs : ℝ} {K : ℕ}
      {σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V ζ Λz : ℝ}
      (P : LocalChartPacketsZ X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc Lmax τ γ δ εr e
        T V ζ Λz),
      0 ≤ Λ → 1 ≤ Δ → 1000000 * Δ * Λ < 1 / 100000 → e < 1 / 40 → 1600 * (1000000 * Δ) ≤ T →
      3 * ν ≤ β 3 → β 3 < 1 → 3 * β 2 ≤ σ → β 2 ≤ η₂ → γ ≤ γ₀ → β 1 ≤ η₁ → 0 < ζ →
      ζ ≤ θ ^ 2 / 1000 → εr ≤ θ / 100 → 20 * Λz ≤ T → σ⁻¹ ≤ Lmax →
      Tcp03ZeroOutV2 P θ :=
  tcp03_zero_row hθ hθ1 hν hν1

/-- **Verbatim check**: `tcp04_row` concludes the `Out` above. -/
theorem tcp04_row_out_VAL3 {θ ν : ℝ} (hθ : 0 < θ) (hθ1 : θ < 1) (hν : 0 < ν) (hν1 : ν < 1) :
    ∃ σ : ℝ, 0 < σ ∧ σ ≤ 1 / 1000 ∧ ∃ η₂ : ℝ, 0 < η₂ ∧ ∃ γ₀ : ℝ, 0 < γ₀ ∧ ∃ ηc : ℝ, 0 < ηc ∧
    ∀ {X : Type} [MetricSpace X] [ChartedSpace E3 X] [IsManifold 𝓘(ℝ, E3) ∞ X]
      [CompactSpace X] {g : SmoothRiemannianMetric 𝓘(ℝ, E3) X}
      {hmetric : ∀ a b : X, riemannianEDistOf g a b = ENNReal.ofReal (dist a b)}
      {ρ : X → ℝ} {hρ : ∀ p, 0 < ρ p} {Λ : ℝ} {β : ℕ → ℝ} {Δ σs : ℝ} {K : ℕ}
      {σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V : ℝ}
      (P : LocalChartPackets X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T
        V),
      0 ≤ Λ → 1200 ≤ Δ → μ ≤ 1 / 100 → τ ≤ 1 / 100 → 1000000 * Δ * Λ < 1 / 100000 →
      4 * (10 + 2 * (2000000 * Δ) + Δ / 3) ≤ Lmax → e < 1 / 40 → 1600 * (1000000 * Δ) ≤ T →
      0 ≤ ε → ε ≤ 1 → 0 ≤ σc → σc ≤ 1 → 3 * ν ≤ β 3 → β 3 < 1 → 3 * β 2 ≤ σ → β 2 ≤ η₂ →
      γ ≤ γ₀ → 0 < γc → γc ≤ γ₀ → βc ≤ ηc → σ⁻¹ ≤ Lmax →
      Tcp04OutV2 P θ :=
  tcp04_row hθ hθ1 hν hν1

/-- **Verbatim check**: `egp03_row` concludes the `Out` above. -/
theorem egp03_row_out_VAL3 {Δ β₂ E : ℝ} (hΔ : 1 ≤ Δ) (hβ₂ : 0 < β₂) (hβ₂1 : β₂ < 1 / 1000000)
    (hE : 0 < E) :
    ∃ Lc η₀ : ℝ, 0 < Lc ∧ 0 < η₀ ∧
      ∀ (X : Type) [MetricSpace X] [ChartedSpace E3 X] [IsManifold 𝓘(ℝ, E3) ∞ X]
        [CompactSpace X] (g : SmoothRiemannianMetric 𝓘(ℝ, E3) X)
        (hmetric : ∀ a b : X, riemannianEDistOf g a b = ENNReal.ofReal (dist a b))
        (ρ : X → ℝ) (hρ : ∀ p, 0 < ρ p) (Λ : ℝ) (β : ℕ → ℝ) (σs : ℝ) (K : ℕ)
        (σc μ b s b' s' ε γc βc Lmax τ : ℝ)
        (L : LocalChartFamilyE X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc Lmax τ),
        b ≤ η₀ → s < 1 / 1000000 → β 1 ≤ η₀ → Lc ≤ Lmax → 0 ≤ Λ →
        1000000 * Δ * Λ < 1 / 100000 → μ ≤ 1 / 100 → τ ≤ 1 / 100 → Egp03OutV2 L E :=
  egp03_row hΔ hβ₂ hβ₂1 hE

/-- **Verbatim check**: `egp04_row_RVZ` concludes the `Out` above. -/
theorem egp04_row_RVZ_out_VAL3 {Δ β₂ θ : ℝ} (hΔ : 1 ≤ Δ) (hβ₂ : 0 < β₂) (hβ₂1 : β₂ < 1 / 1000000)
    (hθ : 0 < θ) (hθ1 : θ < 1) :
    ∃ Lc η₀ : ℝ, 0 < Lc ∧ 0 < η₀ ∧
      ∀ (X : Type) [MetricSpace X] [ChartedSpace E3 X] [IsManifold 𝓘(ℝ, E3) ∞ X]
        [CompactSpace X] (g : SmoothRiemannianMetric 𝓘(ℝ, E3) X)
        (hmetric : ∀ a b : X, riemannianEDistOf g a b = ENNReal.ofReal (dist a b))
        (ρ : X → ℝ) (hρ : ∀ p, 0 < ρ p) (Λ : ℝ) (β : ℕ → ℝ) (σs : ℝ) (K : ℕ)
        (σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V vs ζ Λz : ℝ)
        (P : LocalChartPacketsRVZ X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc Lmax τ γ δ
          εr e T V vs ζ Λz),
        b ≤ η₀ → s < 1 / 1000000 → β 1 ≤ η₀ → Lc ≤ Lmax → 0 ≤ Λ →
        1000000 * Δ * Λ < 1 / 100000 → μ ≤ 1 / 100 → τ ≤ 1 / 100 → σc ≤ θ ^ 2 / 10 ^ 8 →
        μ * Δ < θ / 100 → 0 < σs → σs ≤ θ ^ 2 / 10 ^ 8 → vs < θ / 100 → e < 1 / 40 →
        1600 * (1000000 * Δ) ≤ T → 20 * Λz ≤ T → 0 < ζ → ζ ≤ θ ^ 2 / 10 ^ 8 →
        ζ ≤ 1 / (1000 * (1000000 * Δ)) → εr < θ / (100 * (1000000 * Δ)) →
        Egp04OutV2 P θ :=
  egp04_row_RVZ hΔ hβ₂ hβ₂1 hθ hθ1

/-- **Verbatim check**: `sgp02_row` concludes the `Out` above. -/
theorem sgp02_row_out_VAL3 {Δ β₂ E : ℝ} (hΔ : 1 ≤ Δ) (hβ₂ : 0 < β₂) (hβ₂1 : β₂ < 1) (hE : 0 < E) :
    ∃ Lc η₀ : ℝ, 0 < Lc ∧ 0 < η₀ ∧
      ∀ (X : Type) [MetricSpace X] [ChartedSpace E3 X] [IsManifold 𝓘(ℝ, E3) ∞ X]
        [CompactSpace X] (g : SmoothRiemannianMetric 𝓘(ℝ, E3) X)
        (hmetric : ∀ a b : X, riemannianEDistOf g a b = ENNReal.ofReal (dist a b))
        (ρ : X → ℝ) (hρ : ∀ p, 0 < ρ p) (Λ : ℝ) (β : ℕ → ℝ) (σs : ℝ) (K : ℕ)
        (σc μ b s b' s' ε γc βc Lmax : ℝ)
        (Q : LocalChartFamilyQ X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc Lmax),
        β 2 = β₂ → β 1 ≤ η₀ → Lc ≤ Lmax → 0 ≤ Λ → 1000000 * Δ * Λ < 1 / 100000 →
        Sgp02OutV2 Q E :=
  sgp02_row hΔ hβ₂ hβ₂1 hE

/-- **Verbatim check**: `sgp03_zero_row` concludes the `Out` above. -/
theorem sgp03_zero_row_out_VAL3 {Δ β₂ θ E : ℝ} (hΔ : 1 ≤ Δ) (hβ₂ : 0 < β₂) (hβ₂1 : β₂ < 1)
    (hθ : 0 < θ) (hθ1 : θ < 1) (hE : 0 < E) (hEθ : E < θ ^ 2 / 10 ^ 6) :
    ∃ Lc η₀ : ℝ, 0 < Lc ∧ 0 < η₀ ∧
      ∀ (X : Type) [MetricSpace X] [ChartedSpace E3 X] [IsManifold 𝓘(ℝ, E3) ∞ X]
        [CompactSpace X] (g : SmoothRiemannianMetric 𝓘(ℝ, E3) X)
        (hmetric : ∀ a b : X, riemannianEDistOf g a b = ENNReal.ofReal (dist a b))
        (ρ : X → ℝ) (hρ : ∀ p, 0 < ρ p) (Λ : ℝ) (β : ℕ → ℝ) (σs : ℝ) (K : ℕ)
        (σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V vs ζ Λz : ℝ)
        (P : LocalChartPacketsRVZ X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc Lmax τ γ δ
          εr e T V vs ζ Λz),
        β 2 = β₂ → β 1 ≤ η₀ → Lc ≤ Lmax → 0 ≤ Λ → 1000000 * Δ * Λ < 1 / 100000 →
        e < 1 / 40 → 1600 * (1000000 * Δ) ≤ T → 20 * Λz ≤ T →
        0 < σs → σs < θ ^ 2 / 10 ^ 6 → vs < θ / 100 →
        0 < ζ → ζ < θ ^ 2 / 10 ^ 6 → ζ < 1 / (100 * (1000000 * Δ)) →
        εr < θ / (100 * (1000000 * Δ)) →
        Sgp03ZeroOutV2 P θ E :=
  sgp03_zero_row hΔ hβ₂ hβ₂1 hθ hθ1 hE hEθ

end DifferentialGeometry.Geometry.Collapse
