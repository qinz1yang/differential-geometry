import DifferentialGeometry.Geometry.Collapse.BoundaryRegisterRowReadyRNUM
import DifferentialGeometry.Geometry.Collapse.BoundaryRegisterChainERNUM

/-!
# The boundary chain at the register with the three row-readiness records (lane S-REG-NUM3, G8)

`exists_boundaryChainE_register_stored_RNUM` (S-REG-NUM2 G7) returns the producer's prefix `P`
with its request witness and the late request `hrd`; the rows then need those as arguments. Here
the SAME statement is returned with the three records of `BoundaryRegisterRowReadyRNUM` bound to
the SAME choice: `EarlyRowReady_RNUM EW.early (100 (b_der + 1)(1 + b_cut + c_w(0)/Σ₀))` (N76-9 at
the choice's own `c_w`, `Σ`), `RegisterRowReady_RNUM R (c 2)` (the choice's `c₂`) and, on every
tail member, `MemberRowReady_RNUM`. This is the compiled inhabitant of the three records on the
actual choice (the producer of the CHOICE, the early choice of the stored choice, the register of
every standing sequence and the chain on every tail member and supply of the separated branch).
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

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace

attribute [local instance] nezero_finrank_euclideanThree_LC87

attribute [local instance] interiorCharted_BDRY1 interiorManifold_BDRY1
  connectedSpace_interior_BDRY2

attribute [local instance] BoundaryStandingSequence_BSTD1.conn

/-- **The stored-choice early choice at a CHI record with halved `eg`, with the early evidence**
(`exists_earlyWithChoice_halved_RNUM` with `EarlyRowReady_RNUM` in place of `(P, hEP, hM)`). -/
theorem exists_earlyWithChoice_halved_ready_RNUM (K : ℕ) (hK : 10 ≤ K) (A : ℝ → ℝ)
    (hA : ∀ w, 0 < w → w < euclideanThreeUnitBallVolume → 0 < A w) (eg : Fin 3 → ℝ)
    (χ : BoundaryChainThresholds_BSTD2) (hχeg : ∀ j, χ.eg j = eg j / 2) (Cρ : ℝ) :
    ∃ EW : BoundaryEarlyWithChoice_BSTD2 K hK A hA (fun e : Fin 3 → ℝ => fun j => e j / 2),
      EW.choice = eg ∧ EW.χ = χ ∧ EarlyRowReady_RNUM EW.early.toBoundaryEarlyOverX_BSTD2 Cρ := by
  have hχeg' : χ.eg = (fun e : Fin 3 → ℝ => fun j => e j / 2) eg := funext hχeg
  have hθ0 : 0 < min (1 / 200 : ℝ) χ.ϑ₀ := lt_min (by norm_num) χ.ϑ₀_pos
  have hθ1 : min (1 / 200 : ℝ) χ.ϑ₀ < 1 / 100 := (min_le_left _ _).trans_lt (by norm_num)
  have hθ2 : min (1 / 200 : ℝ) χ.ϑ₀ ≤ χ.ϑ₀ := min_le_right _ _
  have hν0 : 0 < min χ.ν (1 / 2000000) := lt_min χ.ν_pos (by norm_num)
  have hν1 : min χ.ν (1 / 2000000) < 1 / 1000000 := (min_le_right _ _).trans_lt (by norm_num)
  have hν3 : 3 * min χ.ν (1 / 2000000) ≤ threeSplittingExclusionThreshold.{0, 0} := by
    linarith [χ.three_ν_le, min_le_left χ.ν (1 / 2000000)]
  obtain ⟨EW, hc, hχ, -, -, hea⟩ := exists_boundaryEarlyWithChoice_ready_RNUM K hK A hA
    (fun e : Fin 3 → ℝ => fun j => e j / 2) eg χ hχeg' hθ0 hθ1 hθ2 hν0 hν1 hν3 Cρ
  exact ⟨EW, hc, hχ, hea⟩

/-- **The whole chain of the boundary route at the register, with the three records bound to the
SAME choice** (`exists_boundaryChainE_register_stored_RNUM` with the records in place of
`(P, hEP, hM)` and the late request `hrd`): for every jet order `K_j` and `c_adj > 0` there are the
CHOICE with its validity record and a stored-choice early choice `EW` of it, whose early part is
`EarlyRowReady_RNUM` at `C_ρ = 100 (b_der + 1)(1 + b_cut + c_w(0)/Σ₀)` of THE choice; for every
standing sequence there are `V`, a register `R` with `RegisterRowReady_RNUM R (c 2)` and `n₀` such
that on every member `m ≥ n₀` the member output and `MemberRowReady_RNUM` hold and EVERY supply at
the register's numbers with the separated branch carries an enhanced chain with all slots active.
The rows (A4 whole, BCG06, BCG07, F1, edge parent, ZSP02, FC43) follow from the chain by the
consumers of `BoundaryRegisterRowReadyRNUM` whose hypotheses are exactly the data returned here. -/
theorem exists_boundaryChainE_register_stored_ready_RNUM (K : ℕ) (hK : 10 ≤ K) (A : ℝ → ℝ)
    (hA : ∀ w, 0 < w → w < euclideanThreeUnitBallVolume → 0 < A w) (Kj : ℕ) {cadj : ℝ}
    (hcadj : 0 < cadj) :
    ∃ (Ξ Γ Sg eg c cw : Fin 3 → ℝ), BoundaryChainChoiceValidity_BAUGD Ξ Γ Sg eg c cw cadj ∧
      ∃ EW : BoundaryEarlyWithChoice_BSTD2 K hK A hA (fun e : Fin 3 → ℝ => fun j => e j / 2),
        EW.choice = eg ∧
        EarlyRowReady_RNUM EW.early.toBoundaryEarlyOverX_BSTD2
          (100 * (boundaryDerivBound_BDFB + 1) *
            (1 + boundaryChainCutoffConst_BAUGD + cw 0 / Sg 0)) ∧
        ∀ Sq : BoundaryStandingSequence_BSTD1 K A
            (bdryThresholdsBA_BSTD2 K hK A hA EW.θ EW.νBA).δStar,
          ∃ V : ℝ, ∃ R : BoundaryRegisterOverXBA_BSTD2 EW.early V,
            RegisterRowReady_RNUM R.toBoundaryRegisterOver_BSTD1 (c 2) ∧
            ∃ n₀ : ℕ, ∀ m, n₀ ≤ m → BoundaryMemberOutputXBA_BSTD2 Sq m R ∧
              MemberRowReady_RNUM EW.early.toBoundaryEarlyOver_BSTD1 m ∧
              ∀ oM : ManifoldOrientation 𝓘(ℝ, E3) ((Sq.W m).pieceInterior ⊤) 3,
                ∀ S : BoundarySupply K A EW.early.β R.βd R.εN EW.early.Λ EW.early.w EW.early.Δ
                    EW.early.σs EW.early.σc EW.early.μ EW.early.b EW.early.s EW.early.b' EW.early.s'
                    EW.early.ε EW.early.γc EW.early.βc R.Lmax EW.early.τ EW.early.γ R.δlocal
                    EW.early.εr EW.early.e EW.early.T V EW.early.vs EW.early.ζ EW.early.Λz EW.θ
                    (Sq.W m) (Sq.g m) (boundaryCounterexampleRatio Sq.δ₀ (m + 1)) (m + 1)
                    (Sq.B m) oM,
                  S.SeparatedCollarZero_BIF →
                  ∃ DP : BoundaryAugmentedDataPV3 S (actualSlotsV2_BAUGD S) Γ Sg eg,
                    ∃ C : BoundaryGaf02ChainE DP Kj Ξ c cw boundaryChainCutoffConst_BAUGD
                        boundaryDerivBound_BDFB cutoffKappa_BAUGP2 cadj,
                      ∀ st, ∃ O, C.toChain.slot st = .active O := by
  have hall := exists_boundaryChainE_register_RNUM Kj hcadj
  obtain ⟨Ξ, Γ, Sg, eg, c, cw, χ, hval, hχeg, -, hmain⟩ := hall
  have hEW := exists_earlyWithChoice_halved_ready_RNUM K hK A hA eg χ hχeg
    (100 * (boundaryDerivBound_BDFB + 1) * (1 + boundaryChainCutoffConst_BAUGD + cw 0 / Sg 0))
  obtain ⟨EW, hc, hχ, hea⟩ := hEW
  subst hχ
  refine ⟨Ξ, Γ, Sg, eg, c, cw, hval, EW, hc, hea, fun Sq => ?_⟩
  have hreg := exists_register_ready_RNUM EW Sq (c 2)
  obtain ⟨V, R, hrr, n₀, hR⟩ := hreg
  refine ⟨V, R, hrr, n₀, fun m hm => ⟨(hR m hm).1, (hR m hm).2, fun oM S hsep => ?_⟩⟩
  exact hmain EW.early.toBoundaryEarlyOverX_BSTD2 R.toBoundaryRegisterOverX_BSTD2 EW.θ_pos.le
    EW.θ_le S hsep

end DifferentialGeometry.Geometry.Collapse
