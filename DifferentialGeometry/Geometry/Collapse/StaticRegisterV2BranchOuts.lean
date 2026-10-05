import DifferentialGeometry.Geometry.Collapse.StaticRegisterV2Validity
import DifferentialGeometry.Geometry.Fibration.ActualFirstGraph
import DifferentialGeometry.Geometry.Fibration.ActualEdgeGraph
import DifferentialGeometry.Geometry.Fibration.ActualSlimGraphApprox
import DifferentialGeometry.Geometry.Fibration.ActualFirstCloud
import DifferentialGeometry.Geometry.Fibration.ActualEdgeCloudCoverageApplications
import DifferentialGeometry.Geometry.Fibration.ActualSlimCloudApplications

/-!
# The native conclusions of the graph rows and of the three branch ends, as `Prop`s (FC39-VAL3)

External review 52 ("Missing obligations to add", `early.C`: the three graph moduli on the ACTUAL
graph models; the cloud tests of the three branches): each row's conclusion, verbatim, as a `Prop`
of the family it is stated on and of its accuracy parameters, with a check that the accepted row
concludes exactly that `Prop`.

* Graph rows: `Tcp05OutV2 P eg` (`tcp05_row`, the circle graph model with constant
  `tcpGraphConst`), `Egp06OutV2 P eg` (`egp06_row`, `egpGraphConst`), `Sgp04OutV2 P eg`
  (`sgp04_row`, `sgpGraphBound`).
* Branch ends: `Tcp06OutV2 P Γ sg eg` (`tcp06_row`, first cloud: rank-two planes on `S₁`, the
  cloud test of `cfs08_first_cloud`, projected rank at every preimage), `Egp07OutV2 P Γ Sg eg`
  (`egp07_row_C14`, edge cloud), `Sgp06OutV2 P Γ sg eg` (`sgp06_row_C14`, slim cloud).
* The verbatim checks `<row>_out_VAL3` restate each row with its conclusion replaced by the `Out`
  and are proved by the row.
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

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace

attribute [local instance] nezero_finrank_euclideanThree_LC87

section Outs

variable {X : Type} [MetricSpace X] [ChartedSpace E3 X] [IsManifold 𝓘(ℝ, E3) ∞ X]
  [CompactSpace X] {g : SmoothRiemannianMetric 𝓘(ℝ, E3) X}
  {hmetric : ∀ a b : X, riemannianEDistOf g a b = ENNReal.ofReal (dist a b)}
  {ρ : X → ℝ} {hρ : ∀ p, 0 < ρ p} {Λ : ℝ} {β : ℕ → ℝ} {Δ σs : ℝ} {K : ℕ}
  {σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V vs ζ Λz : ℝ}

/-- The conclusion of `tcp05_row` (verbatim) on `P`. -/
def Tcp05OutV2
    (P : LocalChartPacketsC14 X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T
      V vs ζ Λz)
    (eg : ℝ) : Prop :=
  ∀ i (hi : i ∈ P.circle.centres),
    ∃ Φ : ℝ² → BlockSpace (fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²),
      ContDiff ℝ ∞ Φ ∧
      (∀ j : P.circle.finite_centres.toFinset, j.1 = i → ∀ a,
        Φ a (.inl j) = WithLp.toLp 2 (a, 1)) ∧
      (∀ a, ‖fderiv ℝ Φ a‖ ≤ tcpGraphConst ∧ ‖fderiv ℝ (fderiv ℝ Φ) a‖ ≤ tcpGraphConst) ∧
      ∀ x ∈ ball i (200 * ρ i), ‖cgpCircleCoord P.toLocalChartFamily i hi x‖ ≤ 8 →
        ‖(ρ i)⁻¹ • cgpGlobalMap P.toLocalChartFamily P.zero x -
            Φ (cgpCircleCoord P.toLocalChartFamily i hi x)‖ < eg ∧
        ∀ w : TangentSpace 𝓘(ℝ, E3) x,
          ‖(ρ i)⁻¹ • mvfderiv 𝓘(ℝ, E3) (cgpGlobalMap P.toLocalChartFamily P.zero) x w -
              fderiv ℝ Φ (cgpCircleCoord P.toLocalChartFamily i hi x)
                (mvfderiv 𝓘(ℝ, E3) (cgpCircleCoord P.toLocalChartFamily i hi) x w)‖ ≤
            eg * Real.sqrt ((ρ i)⁻¹ ^ 2 * g.inner x w w)

/-- The conclusion of `egp06_row` (verbatim) on `P`. -/
def Egp06OutV2
    (P : LocalChartPacketsRVZ X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V
      vs ζ Λz)
    (eg : ℝ) : Prop :=
  ∀ i ∈ P.edge.centres,
    ∃ sgn c : CGPTag P.toLocalChartFamily P.zero → ℝ, (∀ t, |sgn t| ≤ 1) ∧
      ∀ x ∈ ball i (100 * Δ * ρ i), |P.edge.coord i x| ≤ 8 * Δ →
        cgpHeight P.toLocalChartFamily x ≤ 8 * Δ →
        ‖(ρ i)⁻¹ • cgpProjMap P.toLocalChartFamily P.zero
            (cgpQ2Tags P.toLocalChartFamily P.zero) x -
          egpModelGraph P.toLocalChartFamily P.zero i sgn c (P.edge.coord i x)‖ < eg ∧
        ∀ w : TangentSpace 𝓘(ℝ, E3) x, (ρ i)⁻¹ ^ 2 * g.inner x w w = 1 →
          ‖(ρ i)⁻¹ • mvfderiv 𝓘(ℝ, E3) (cgpProjMap P.toLocalChartFamily P.zero
              (cgpQ2Tags P.toLocalChartFamily P.zero)) x w -
            fderiv ℝ (egpModelGraph P.toLocalChartFamily P.zero i sgn c)
              (P.edge.coord i x) (mvfderiv 𝓘(ℝ, E3) (P.edge.coord i) x w)‖ < eg

/-- The conclusion of `sgp04_row` (verbatim) on `P`. -/
def Sgp04OutV2
    (P : LocalChartPacketsRVZ X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V
      vs ζ Λz)
    (eg : ℝ) : Prop :=
  ∀ i : P.toLocalChartFamily.slim.finite_centres.toFinset, ∃ sgn c zsgn zc : X → ℝ,
    (∀ j, |sgn j| ≤ 1) ∧ (∀ k, |zsgn k| ≤ 1) ∧
    ∀ x ∈ ball i.1 (10 ^ 6 * Δ * ρ i.1),
      |(P.slim.centre i.1 ((Set.Finite.mem_toFinset _).mp i.2)).coord x| ≤
        8 * 10 ^ 5 * Δ →
      ‖(ρ i.1)⁻¹ • cgpProjMap P.toLocalChartFamily P.zero
          (cgpQ3Tags P.toLocalChartFamily P.zero) x -
        sgpFullGraph P.toLocalChartFamily P.zero i sgn c zsgn zc
          ((P.slim.centre i.1 ((Set.Finite.mem_toFinset _).mp i.2)).coord x)‖ < eg ∧
      ∀ w : TangentSpace 𝓘(ℝ, E3) x,
        ‖(ρ i.1)⁻¹ • mvfderiv 𝓘(ℝ, E3) (cgpProjMap P.toLocalChartFamily P.zero
            (cgpQ3Tags P.toLocalChartFamily P.zero)) x w -
          fderiv ℝ (sgpFullGraph P.toLocalChartFamily P.zero i sgn c zsgn zc)
            ((P.slim.centre i.1 ((Set.Finite.mem_toFinset _).mp i.2)).coord x)
            (mvfderiv 𝓘(ℝ, E3) (P.slim.centre i.1
              ((Set.Finite.mem_toFinset _).mp i.2)).coord x w)‖ ≤
          eg * Real.sqrt ((ρ i.1)⁻¹ ^ 2 * g.inner x w w)

/-- The conclusion of `tcp06_row` (verbatim) on `P`. -/
def Tcp06OutV2
    (P : LocalChartPacketsC14 X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T
      V vs ζ Λz)
    (Γ sg eg : ℝ) : Prop :=
  ∃ plane : BlockSpace (fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²) →
      Submodule ℝ (BlockSpace (fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²)),
    (∀ x ∈ cgpGlobalMap P.toLocalChartFamily P.zero '' fc04Set P.toLocalChartFamily P.zero 7,
      Module.finrank ℝ (plane x) = 2) ∧
    (∀ x ∈ cgpGlobalMap P.toLocalChartFamily P.zero '' fc04Set P.toLocalChartFamily P.zero 7,
      hausdorffEDist (cgpGlobalMap P.toLocalChartFamily P.zero ''
          fc04Set P.toLocalChartFamily P.zero 8 ∩
          ball x (scaleRadius (cgpScaleTag P.toLocalChartFamily P.zero) sg x / Γ))
        ((AffineSubspace.mk' x (plane x) :
            Set (BlockSpace (fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²))) ∩
          ball x (scaleRadius (cgpScaleTag P.toLocalChartFamily P.zero) sg x / Γ)) ≤
        ENNReal.ofReal (Γ * scaleRadius (cgpScaleTag P.toLocalChartFamily P.zero) sg x)) ∧
    ∀ x ∈ cgpGlobalMap P.toLocalChartFamily P.zero '' fc04Set P.toLocalChartFamily P.zero 7,
      ∃ i : P.toLocalChartFamily.circle.finite_centres.toFinset,
      ∀ q, cgpGlobalMap P.toLocalChartFamily P.zero q = x →
      let Pq := (plane x).orthogonalProjectionOnto.comp ((ρ i.1)⁻¹ • mvfderiv 𝓘(ℝ, E3)
        (cgpGlobalMap P.toLocalChartFamily P.zero) q)
      Function.Surjective Pq ∧
      (∀ v, ‖(ρ i.1)⁻¹ • mvfderiv 𝓘(ℝ, E3) (cgpGlobalMap P.toLocalChartFamily P.zero) q v -
          (Pq v : BlockSpace _)‖ ≤ eg * Real.sqrt ((ρ i.1)⁻¹ ^ 2 * g.inner q v v)) ∧
      (∀ v, (∀ k, Pq k = 0 → g.inner q v k = 0) →
        1 / 2 * Real.sqrt ((ρ i.1)⁻¹ ^ 2 * g.inner q v v) ≤ ‖Pq v‖) ∧
      ∀ v, ‖Pq v‖ ≤ 3 * tcpGraphConst * Real.sqrt ((ρ i.1)⁻¹ ^ 2 * g.inner q v v)

/-- The conclusion of `egp07_row_C14` (verbatim) on `P`. -/
def Egp07OutV2
    (P : LocalChartPacketsC14 X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T
      V vs ζ Λz)
    (Γ Sg eg : ℝ) : Prop :=
  ∃ plane : BlockSpace (fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²) →
      Submodule ℝ (BlockSpace (fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²)),
    (∀ x ∈ cgpProjMap P.toLocalChartFamily P.zero (cgpQ2Tags P.toLocalChartFamily P.zero) ''
        fc27EdgeSet P.toLocalChartFamily 7, Module.finrank ℝ (plane x) = 1) ∧
    (∀ select : BlockSpace (fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²) → X,
      (∀ x ∈ cgpProjMap P.toLocalChartFamily P.zero (cgpQ2Tags P.toLocalChartFamily P.zero) ''
          fc27EdgeSet P.toLocalChartFamily 8,
        cgpProjMap P.toLocalChartFamily P.zero (cgpQ2Tags P.toLocalChartFamily P.zero)
          (select x) = x) →
      ∀ x ∈ cgpProjMap P.toLocalChartFamily P.zero (cgpQ2Tags P.toLocalChartFamily P.zero) ''
        fc27EdgeSet P.toLocalChartFamily 7,
        hausdorffEDist (cgpProjMap P.toLocalChartFamily P.zero
            (cgpQ2Tags P.toLocalChartFamily P.zero) '' fc27EdgeSet P.toLocalChartFamily 8 ∩
            ball x (Sg * ρ (select x) / Γ))
          ((AffineSubspace.mk' x (plane x) :
              Set (BlockSpace (fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²))) ∩
            ball x (Sg * ρ (select x) / Γ)) ≤ ENNReal.ofReal (Γ * (Sg * ρ (select x)))) ∧
    ∀ x ∈ cgpProjMap P.toLocalChartFamily P.zero (cgpQ2Tags P.toLocalChartFamily P.zero) ''
        fc27EdgeSet P.toLocalChartFamily 7,
      ∃ (i : P.toLocalChartFamily.edge.finite_centres.toFinset)
        (Tx : ℝ →L[ℝ] BlockSpace (fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²)),
        plane x = LinearMap.range
          (Tx : ℝ →ₗ[ℝ] BlockSpace (fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²)) ∧
        ∀ q : X,
        cgpProjMap P.toLocalChartFamily P.zero (cgpQ2Tags P.toLocalChartFamily P.zero) q = x →
        (∀ w : TangentSpace 𝓘(ℝ, E3) q, (ρ i.1)⁻¹ ^ 2 * g.inner q w w = 1 →
          ‖(ρ i.1)⁻¹ • mvfderiv 𝓘(ℝ, E3) (cgpProjMap P.toLocalChartFamily P.zero
              (cgpQ2Tags P.toLocalChartFamily P.zero)) q w -
            (LinearMap.range (Tx : ℝ →ₗ[ℝ]
              BlockSpace (fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²))).starProjection
              ((ρ i.1)⁻¹ • mvfderiv 𝓘(ℝ, E3) (cgpProjMap P.toLocalChartFamily P.zero
                (cgpQ2Tags P.toLocalChartFamily P.zero)) q w)‖ < eg) ∧
        (∀ w : TangentSpace 𝓘(ℝ, E3) q, (ρ i.1)⁻¹ ^ 2 * g.inner q w w = 1 →
          ‖(LinearMap.range (Tx : ℝ →ₗ[ℝ]
              BlockSpace (fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²))).starProjection
              ((ρ i.1)⁻¹ • mvfderiv 𝓘(ℝ, E3) (cgpProjMap P.toLocalChartFamily P.zero
                (cgpQ2Tags P.toLocalChartFamily P.zero)) q w)‖ ≤ 3 * egpGraphConst) ∧
        (∃ w₀ : TangentSpace 𝓘(ℝ, E3) q, (ρ i.1)⁻¹ ^ 2 * g.inner q w₀ w₀ = 1 ∧
          1 / 2 ≤ ‖(LinearMap.range (Tx : ℝ →ₗ[ℝ]
              BlockSpace (fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²))).starProjection
              ((ρ i.1)⁻¹ • mvfderiv 𝓘(ℝ, E3) (cgpProjMap P.toLocalChartFamily P.zero
                (cgpQ2Tags P.toLocalChartFamily P.zero)) q w₀)‖) ∧
        ∀ k ∈ LinearMap.range (Tx : ℝ →ₗ[ℝ]
            BlockSpace (fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²)),
          ∃ w : TangentSpace 𝓘(ℝ, E3) q,
            (LinearMap.range (Tx : ℝ →ₗ[ℝ]
              BlockSpace (fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²))).starProjection
              ((ρ i.1)⁻¹ • mvfderiv 𝓘(ℝ, E3) (cgpProjMap P.toLocalChartFamily P.zero
                (cgpQ2Tags P.toLocalChartFamily P.zero)) q w) = k

/-- The conclusion of `sgp06_row_C14` (verbatim) on `P`. -/
def Sgp06OutV2
    (P : LocalChartPacketsC14 X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T
      V vs ζ Λz)
    (Γ sg eg : ℝ) : Prop :=
  ∃ plane : BlockSpace (fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²) →
      Submodule ℝ (BlockSpace (fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²)),
    (∀ x ∈ cgpProjMap P.toLocalChartFamily P.zero (cgpQ3Tags P.toLocalChartFamily P.zero) ''
        fc27SlimSet P.toLocalChartFamily 7, Module.finrank ℝ (plane x) = 1) ∧
    (∀ select : BlockSpace (fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²) → X,
      (∀ x ∈ cgpProjMap P.toLocalChartFamily P.zero (cgpQ3Tags P.toLocalChartFamily P.zero) ''
          fc27SlimSet P.toLocalChartFamily 8,
        cgpProjMap P.toLocalChartFamily P.zero (cgpQ3Tags P.toLocalChartFamily P.zero)
          (select x) = x) →
      ∀ x ∈ cgpProjMap P.toLocalChartFamily P.zero (cgpQ3Tags P.toLocalChartFamily P.zero) ''
          fc27SlimSet P.toLocalChartFamily 7,
        hausdorffEDist (cgpProjMap P.toLocalChartFamily P.zero
            (cgpQ3Tags P.toLocalChartFamily P.zero) '' fc27SlimSet P.toLocalChartFamily 8 ∩
            ball x (sg * ρ (select x) / Γ))
          ((AffineSubspace.mk' x (plane x) :
              Set (BlockSpace (fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²))) ∩
            ball x (sg * ρ (select x) / Γ)) ≤ ENNReal.ofReal (Γ * (sg * ρ (select x)))) ∧
    ∀ x ∈ cgpProjMap P.toLocalChartFamily P.zero (cgpQ3Tags P.toLocalChartFamily P.zero) ''
        fc27SlimSet P.toLocalChartFamily 7,
      ∃ i : P.toLocalChartFamily.slim.finite_centres.toFinset,
      ∀ q, cgpProjMap P.toLocalChartFamily P.zero (cgpQ3Tags P.toLocalChartFamily P.zero) q =
        x →
      let Pq := (plane x).orthogonalProjectionOnto.comp ((ρ i.1)⁻¹ • mvfderiv 𝓘(ℝ, E3)
        (cgpProjMap P.toLocalChartFamily P.zero (cgpQ3Tags P.toLocalChartFamily P.zero)) q)
      Function.Surjective Pq ∧
      (∀ v, ‖(ρ i.1)⁻¹ • mvfderiv 𝓘(ℝ, E3) (cgpProjMap P.toLocalChartFamily P.zero
          (cgpQ3Tags P.toLocalChartFamily P.zero)) q v - (Pq v : BlockSpace _)‖ ≤
        eg * Real.sqrt ((ρ i.1)⁻¹ ^ 2 * g.inner q v v)) ∧
      (∀ v, (∀ k, Pq k = 0 → g.inner q v k = 0) →
        1 / 2 * Real.sqrt ((ρ i.1)⁻¹ ^ 2 * g.inner q v v) ≤ ‖Pq v‖) ∧
      ∀ v, ‖Pq v‖ ≤ 3 * sgpGraphBound * Real.sqrt ((ρ i.1)⁻¹ ^ 2 * g.inner q v v)

end Outs

/-- **Verbatim check**: `tcp05_row` concludes the `Out` above. -/
theorem tcp05_row_out_VAL3 {eg ν : ℝ} (heg : 0 < eg) (heg1 : eg < 1 / 100) (hν : 0 < ν)
    (hν1 : ν < 1) :
    ∃ σ : ℝ, 0 < σ ∧ σ ≤ 1 / 1000 ∧ ∃ η₂ γ₀ ηc θ : ℝ, 0 < η₂ ∧ 0 < γ₀ ∧ 0 < ηc ∧ 0 < θ ∧
    θ < 1 ∧ ∀ Δ : ℝ, 1200 ≤ Δ → ∃ η₁ : ℝ, 0 < η₁ ∧
    ∀ {X : Type} [MetricSpace X] [ChartedSpace E3 X] [IsManifold 𝓘(ℝ, E3) ∞ X]
      [CompactSpace X] {g : SmoothRiemannianMetric 𝓘(ℝ, E3) X}
      {hmetric : ∀ a b : X, riemannianEDistOf g a b = ENNReal.ofReal (dist a b)}
      {ρ : X → ℝ} {hρ : ∀ p, 0 < ρ p} {Λ : ℝ} {β : ℕ → ℝ} {σs : ℝ} {K : ℕ}
      {σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V vs ζ Λz : ℝ}
      (P : LocalChartPacketsC14 X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc Lmax τ γ δ εr
        e T V vs ζ Λz),
      0 ≤ Λ → μ ≤ 1 / 100 → τ ≤ 1 / 100 → 1000000 * Δ * Λ < 1 / 100000 →
      4 * (10 + 2 * (2000000 * Δ) + Δ / 3) ≤ Lmax → e < 1 / 40 → 1600 * (1000000 * Δ) ≤ T →
      0 ≤ ε → ε ≤ 1 → 0 ≤ σc → σc ≤ θ ^ 2 / 1000 → μ * Δ ≤ θ / 100 →
      3 * ν ≤ β 3 → β 3 < 1 → 3 * β 2 ≤ σ → β 2 ≤ η₂ → γ ≤ γ₀ → 0 < γc → γc ≤ γ₀ → βc ≤ ηc →
      b ≤ η₁ → β 1 ≤ η₁ → 0 < σs → σs ≤ θ ^ 2 / 1000 → vs ≤ θ / 100 → 0 < ζ →
      ζ ≤ θ ^ 2 / 1000 → εr ≤ θ / 100 → 20 * Λz ≤ T → σ⁻¹ ≤ Lmax →
      1000 * tcpGraphConst * Δ * Λ < eg →
      Tcp05OutV2 P eg :=
  tcp05_row heg heg1 hν hν1

/-- **Verbatim check**: `egp06_row` concludes the `Out` above. -/
theorem egp06_row_out_VAL3 {Δ β₂ eg : ℝ} (hΔ : 1 ≤ Δ) (hβ₂ : 0 < β₂) (hβ₂1 : β₂ < 1 / 1000000)
    (heg : 0 < eg) (heg1 : eg < 1 / 100) :
    ∃ Lc η₀ : ℝ, 0 < Lc ∧ 0 < η₀ ∧
      ∀ (X : Type) [MetricSpace X] [ChartedSpace E3 X] [IsManifold 𝓘(ℝ, E3) ∞ X]
        [CompactSpace X] (g : SmoothRiemannianMetric 𝓘(ℝ, E3) X)
        (hmetric : ∀ a b : X, riemannianEDistOf g a b = ENNReal.ofReal (dist a b))
        (ρ : X → ℝ) (hρ : ∀ p, 0 < ρ p) (Λ : ℝ) (β : ℕ → ℝ) (σs : ℝ) (K : ℕ)
        (σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V vs ζ Λz : ℝ)
        (P : LocalChartPacketsRVZ X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc Lmax τ γ δ
          εr e T V vs ζ Λz),
        b ≤ η₀ → s < 1 / 1000000 → β 1 ≤ η₀ → Lc ≤ Lmax → 0 ≤ Λ →
        1000000 * Δ * Λ < 1 / 100000 → μ ≤ 1 / 100 → τ ≤ 1 / 100 →
        σc ≤ (eg / (20 * egpGraphConst)) ^ 2 / 10 ^ 8 →
        μ * Δ < eg / (20 * egpGraphConst) / 100 → 0 < σs →
        σs ≤ (eg / (20 * egpGraphConst)) ^ 2 / 10 ^ 8 →
        vs < eg / (20 * egpGraphConst) / 100 → e < 1 / 40 →
        1600 * (1000000 * Δ) ≤ T → 20 * Λz ≤ T → 0 < ζ →
        ζ ≤ (eg / (20 * egpGraphConst)) ^ 2 / 10 ^ 8 → ζ ≤ 1 / (1000 * (1000000 * Δ)) →
        εr < eg / (20 * egpGraphConst) / (100 * (1000000 * Δ)) →
        Egp06OutV2 P eg :=
  egp06_row hΔ hβ₂ hβ₂1 heg heg1

/-- **Verbatim check**: `sgp04_row` concludes the `Out` above. -/
theorem sgp04_row_out_VAL3 {Δ β₂ eg : ℝ} (hΔ : 1 ≤ Δ) (hβ₂ : 0 < β₂) (hβ₂1 : β₂ < 1)
    (heg : 0 < eg)
    (heg1 : eg < 1 / 100) :
    ∃ θ : ℝ, 0 < θ ∧ θ < 1 ∧ ∃ Lc η₀ : ℝ, 0 < Lc ∧ 0 < η₀ ∧
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
        Sgp04OutV2 P eg :=
  sgp04_row hΔ hβ₂ hβ₂1 heg heg1

/-- **Verbatim check**: `tcp06_row` concludes the `Out` above. -/
theorem tcp06_row_out_VAL3 {ν Γ sg eg : ℝ} (hΓ : 0 < Γ) (hΓ1 : Γ < 1) (hsg : 0 < sg)
    (hsgΓ : sg < Γ / 200) (hsgC : sg < Γ ^ 3 / (100 * tcpGraphConst)) (heg : 0 < eg)
    (heg1 : eg < 1 / 100) (hegΓ : eg < Γ * sg / 100) (hν : 0 < ν) (hν1 : ν < 1) :
    ∃ σ : ℝ, 0 < σ ∧ σ ≤ 1 / 1000 ∧ ∃ η₂ γ₀ ηc θ : ℝ, 0 < η₂ ∧ 0 < γ₀ ∧ 0 < ηc ∧ 0 < θ ∧
    θ < 1 ∧ ∀ Δ : ℝ, 1200 ≤ Δ → ∃ η₁ : ℝ, 0 < η₁ ∧
    ∀ {X : Type} [MetricSpace X] [ChartedSpace E3 X] [IsManifold 𝓘(ℝ, E3) ∞ X]
      [CompactSpace X] {g : SmoothRiemannianMetric 𝓘(ℝ, E3) X}
      {hmetric : ∀ a b : X, riemannianEDistOf g a b = ENNReal.ofReal (dist a b)}
      {ρ : X → ℝ} {hρ : ∀ p, 0 < ρ p} {Λ : ℝ} {β : ℕ → ℝ} {σs : ℝ} {K : ℕ}
      {σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V vs ζ Λz : ℝ}
      (P : LocalChartPacketsC14 X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc Lmax τ γ δ εr
        e T V vs ζ Λz),
      0 ≤ Λ → μ ≤ 1 / 100 → τ ≤ 1 / 100 → 1000000 * Δ * Λ < 1 / 100000 →
      4 * (10 + 2 * (2000000 * Δ) + Δ / 3) ≤ Lmax → e < 1 / 40 → 1600 * (1000000 * Δ) ≤ T →
      0 ≤ ε → ε ≤ 1 → 0 ≤ σc → σc ≤ θ ^ 2 / 1000 → μ * Δ ≤ θ / 100 →
      3 * ν ≤ β 3 → β 3 < 1 → 3 * β 2 ≤ σ → β 2 ≤ η₂ → γ ≤ γ₀ → 0 < γc → γc ≤ γ₀ → βc ≤ ηc →
      b ≤ η₁ → β 1 ≤ η₁ → 0 < σs → σs ≤ θ ^ 2 / 1000 → vs ≤ θ / 100 → 0 < ζ →
      ζ ≤ θ ^ 2 / 1000 → εr ≤ θ / 100 → 20 * Λz ≤ T → σ⁻¹ ≤ Lmax →
      1000 * tcpGraphConst * Δ * Λ < eg →
      Tcp06OutV2 P Γ sg eg :=
  tcp06_row hΓ hΓ1 hsg hsgΓ hsgC heg heg1 hegΓ hν hν1

/-- **Verbatim check**: `egp07_row_C14` concludes the `Out` above. -/
theorem egp07_row_C14_out_VAL3 {Δ β₂ Γ Sg eg : ℝ} (hΔ : 1 ≤ Δ) (hβ₂ : 0 < β₂)
    (hβ₂1 : β₂ < 1 / 1000000)
    (hΓ : Γ ∈ Ioo (0 : ℝ) 1) (hS : 0 < Sg)
    (hSmin : Sg < min (Γ / 200) (Γ ^ 3 / (100 * egpGraphConst)))
    (heg : 0 < eg) (hemin : eg < min (1 / 100) (min (Γ * Sg / 100) (Sg / 1000))) :
    ∃ Lc η₀ : ℝ, 0 < Lc ∧ 0 < η₀ ∧
      ∀ (X : Type) [MetricSpace X] [ChartedSpace E3 X] [IsManifold 𝓘(ℝ, E3) ∞ X]
        [CompactSpace X] (g : SmoothRiemannianMetric 𝓘(ℝ, E3) X)
        (hmetric : ∀ a b : X, riemannianEDistOf g a b = ENNReal.ofReal (dist a b))
        (ρ : X → ℝ) (hρ : ∀ p, 0 < ρ p) (Λ : ℝ) (β : ℕ → ℝ) (σs : ℝ) (K : ℕ)
        (σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V vs ζ Λz : ℝ)
        (P : LocalChartPacketsC14 X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc Lmax τ γ δ
          εr e T V vs ζ Λz),
        b ≤ η₀ → s < 1 / 1000000 → β 1 ≤ η₀ → Lc ≤ Lmax → 0 ≤ Λ →
        1000000 * Δ * Λ < 1 / 100000 → μ ≤ 1 / 100 → τ ≤ 1 / 100 →
        σc ≤ (eg / (20 * egpGraphConst)) ^ 2 / 10 ^ 8 →
        μ * Δ < eg / (20 * egpGraphConst) / 100 → 0 < σs →
        σs ≤ (eg / (20 * egpGraphConst)) ^ 2 / 10 ^ 8 →
        vs < eg / (20 * egpGraphConst) / 100 → e < 1 / 40 →
        1600 * (1000000 * Δ) ≤ T → 20 * Λz ≤ T → 0 < ζ →
        ζ ≤ (eg / (20 * egpGraphConst)) ^ 2 / 10 ^ 8 → ζ ≤ 1 / (1000 * (1000000 * Δ)) →
        εr < eg / (20 * egpGraphConst) / (100 * (1000000 * Δ)) →
        Egp07OutV2 P Γ Sg eg :=
  egp07_row_C14 hΔ hβ₂ hβ₂1 hΓ hS hSmin heg hemin

/-- **Verbatim check**: `sgp06_row_C14` concludes the `Out` above. -/
theorem sgp06_row_C14_out_VAL3 {Δ β₂ Γ sg eg : ℝ} (hΔ : 1 ≤ Δ) (hβ₂ : 0 < β₂) (hβ₂1 : β₂ < 1)
    (hΓ : 0 < Γ)
    (hΓ1 : Γ < 1) (hsg : 0 < sg) (hsgΓ : sg < Γ / 200)
    (hsgC : sg < Γ ^ 3 / (100 * sgpGraphBound)) (heg : 0 < eg) (heg1 : eg < 1 / 100)
    (hegΓ : eg < Γ * sg / 100) :
    ∃ θ : ℝ, 0 < θ ∧ θ < 1 ∧ ∃ Lc η₀ : ℝ, 0 < Lc ∧ 0 < η₀ ∧
      ∀ (X : Type) [MetricSpace X] [ChartedSpace E3 X] [IsManifold 𝓘(ℝ, E3) ∞ X]
        [CompactSpace X] (g : SmoothRiemannianMetric 𝓘(ℝ, E3) X)
        (hmetric : ∀ a b : X, riemannianEDistOf g a b = ENNReal.ofReal (dist a b))
        (ρ : X → ℝ) (hρ : ∀ p, 0 < ρ p) (Λ : ℝ) (β : ℕ → ℝ) (σs : ℝ) (K : ℕ)
        (σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V vs ζ Λz : ℝ)
        (P : LocalChartPacketsC14 X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc Lmax τ γ δ
          εr e T V vs ζ Λz),
        β 2 = β₂ → β 1 ≤ η₀ → Lc ≤ Lmax → 0 ≤ Λ → 1000000 * Δ * Λ < 1 / 100000 →
        e < 1 / 40 → 1600 * (1000000 * Δ) ≤ T → 20 * Λz ≤ T →
        0 < σs → σs < θ ^ 2 / 10 ^ 6 → vs < θ / 100 →
        0 < ζ → ζ < θ ^ 2 / 10 ^ 6 → ζ < 1 / (100 * (1000000 * Δ)) →
        εr < θ / (100 * (1000000 * Δ)) →
        Sgp06OutV2 P Γ sg eg :=
  sgp06_row_C14 hΔ hβ₂ hβ₂1 hΓ hΓ1 hsg hsgΓ hsgC heg heg1 hegΓ

end DifferentialGeometry.Geometry.Collapse
