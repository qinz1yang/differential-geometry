import DifferentialGeometry.Geometry.Collapse.LocalExport.BoundaryPortCircleTableFinal
import DifferentialGeometry.Geometry.Collapse.LocalExport.BoundaryProducerCertificateDoubleCusp

/-!
# The DP certificate on the double cusps (BAUG-C, group G8c'; D76-2 acceptance instance)

`exists_boundaryDP_doubleCusp_BAUGC`: `exists_boundaryDP_doubleCusp_of_circlePort_BAUGC` (G8c)
applied to the delivered circle port theorem `port_circle_interior_table_BAUGP`: on every tail
member of the double-cusp standing sequence all the producer premises hold at once on a supply of
the register's parameters, and the separated branch carries the augmented data at `(Γ, Σ, eg)`.
-/

set_option autoImplicit false

noncomputable section

open Set Function Metric Bundle Manifold Filter
open scoped ContDiff Manifold Topology ENNReal
open DifferentialGeometry.Topology.Ehresmann DifferentialGeometry.Topology.Manifold
open DifferentialGeometry.Geometry.Riemannian GC.MetricGeometry
open DifferentialGeometry GC.Endpoint DifferentialGeometry.Geometry.Hyperbolic
open DifferentialGeometry.Analysis

namespace DifferentialGeometry.Geometry.Collapse

local notation "E3" => EuclideanSpace ℝ (Fin 3)
local notation "ℝ²" => EuclideanSpace ℝ (Fin 2)

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace

attribute [local instance] nezero_finrank_euclideanThree_LC87

attribute [local instance] interiorCharted_BDRY1 interiorManifold_BDRY1
  connectedSpace_interior_BDRY2

attribute [local instance] BoundaryStandingSequence_BSTD1.conn

/-- **The DP certificate on the double cusps** (acceptance instance of D76-2). -/
theorem exists_boundaryDP_doubleCusp_BAUGC
    (K : ℕ) (hK : 10 ≤ K) {ν : ℝ} {Γ Sg eg : Fin 3 → ℝ} (hΓ : ∀ j, 0 < Γ j) (hΓ1 : ∀ j, Γ j < 1)
    (hsg : ∀ j, 0 < Sg j) (hsgΓ : ∀ j, Sg j < Γ j / 250)
    (hsgC0 : Sg 0 < Γ 0 ^ 3 / (125 * (tcpGraphConst + 2 * bmConst_BAUGC)))
    (hsgC1 : Sg 1 < Γ 1 ^ 3 / (125 * (egpGraphConst + 2 * bmConst_BAUGC)))
    (hsgC2 : Sg 2 < Γ 2 ^ 3 / (125 * (sgpGraphBound + 2 * bmConst_BAUGC)))
    (heg : ∀ j, 0 < eg j) (heg1 : ∀ j, eg j < 1 / 100) (hegΓ : ∀ j, eg j < Γ j * Sg j / 100)
    (hν : 0 < ν) (hν3 : 3 * ν ≤ threeSplittingExclusionThreshold.{0, 0}) :
    ∃ A : ℝ → ℝ, ∃ hA : ∀ w, 0 < w → w < euclideanThreeUnitBallVolume → 0 < A w,
    ∃ EW : BoundaryEarlyWithChoice_BSTD2 K hK A hA (fun e : Fin 3 → ℝ => fun j => e j / 2),
      ValidDPThresholds_BAUGC Γ Sg eg EW.χ ∧
      ∃ Sq : BoundaryStandingSequence_BSTD1 K A
          (bdryThresholdsBA_BSTD2 K hK A hA EW.θ EW.νBA).δStar,
        (∀ n, (Sq.B n).count = 2) ∧
        ∃ V : ℝ, ∃ R : BoundaryRegisterOverXBA_BSTD2 EW.early V, ∃ n₀ : ℕ, ∀ m, n₀ ≤ m →
          ∀ oM : ManifoldOrientation 𝓘(ℝ, E3) ((Sq.W m).pieceInterior ⊤) 3,
          ∃ Sup : BoundarySupply K A EW.early.β R.βd R.εN EW.early.Λ EW.early.w EW.early.Δ
              EW.early.σs EW.early.σc EW.early.μ EW.early.b EW.early.s EW.early.b' EW.early.s'
              EW.early.ε EW.early.γc EW.early.βc R.Lmax EW.early.τ EW.early.γ R.δlocal
              EW.early.εr EW.early.e EW.early.T V EW.early.vs EW.early.ζ EW.early.Λz EW.θ (Sq.W m)
              (Sq.g m) (boundaryCounterexampleRatio Sq.δ₀ (m + 1)) (m + 1) (Sq.B m) oM,
            ProducerPremises_BAUGC EW.χ eg EW.early.β₂ EW.early.β EW.early.Λ EW.early.μ
              EW.early.τ EW.early.Δ R.Lmax EW.early.e EW.early.T EW.early.ε EW.early.σc
              EW.early.γ EW.early.γc EW.early.βc EW.early.b EW.early.s EW.early.σs EW.early.vs
              EW.early.ζ EW.early.εr EW.early.Λz V EW.θ ∧
            (Sup.SeparatedCollarZero_BIF →
              Nonempty (BoundaryAugmentedDataPV3 Sup (actualSlotsV2_BAUGD Sup) Γ Sg eg)) :=
  exists_boundaryDP_doubleCusp_of_circlePort_BAUGC
    (by
      intro ν' Γ' sg' eg' hΓ' _ hsg' hsgΓ' _ heg' heg1' _ hν' hν1'
      exact port_circle_interior_table_BAUGP hΓ' hsg' hsgΓ' heg' heg1' hν' hν1')
    K hK hΓ hΓ1
    hsg hsgΓ hsgC0 hsgC1 hsgC2 heg heg1 hegΓ hν hν3

end DifferentialGeometry.Geometry.Collapse
