import DifferentialGeometry.Geometry.Collapse.BoundaryRegisterA4NumericsRNUM
import DifferentialGeometry.Geometry.Collapse.BoundaryRegisterStdBSTD2
import DifferentialGeometry.Geometry.Collapse.LocalExport.BoundaryChainEProducer

/-!
# A2 v3 at the register: the enhanced boundary chain exists on every tail member (S-REG-NUM2, G7)

The A2-v3 production theorem `exists_boundaryGaf02ChainE_v3_BAUGD` takes a curried block of 78
numerical premises about the supply's parameters. The register of lane BSTD2 supplies the same
facts as `BoundaryRegisterOverX_BSTD2.std_block_BSTD2` (A2-mk's uniform block, 18) and
`BoundaryRegisterOverX_BSTD2.chi_block_BSTD2` (the closed CHI block, 51), at a CHI record `χ`.

**`exists_boundaryChainE_register_RNUM`** (boundary twin of the closed
`exists_chainThresholds_chainE_BSTD2`): for every jet order `K_j` and `c_adj > 0` there are the
CHOICE `(Ξ, Γ, Σ, eg, c, c_w)` with its validity record and a CHI record `χ` — built from A2's own
thresholds (`ν = thr/3`; `σ η₂ γ₀ η_c θ_t` constants; `η₁ θ_s L_c η₀` as functions of `(β₂, Δ)`,
`L_{c,1} = L_{c,2}`, `η_{0,1} = η_{0,2}`), with `χ.eg = eg/2` (N76-1) and `ϑ₀ ≤ min_j eg j/(16 P_*)`
(N76-2) — such that for EVERY extended early choice `E` over `χ`, every extended register `R` over
`(E, V)` and EVERY supply `S` at exactly the register's numbers with `0 ≤ θ ≤ ϑ₀` and the
separated branch, there are augmented data and an enhanced chain with all three stage slots active.
No numerical premise: the 78 premises of A2 are register facts (the premise table is in the proof:
`std_block` -> r1..r18; `chi_block` f1..f31, d1..d11, m1..m9 and `std_block` r2, r5..r9 -> the
circle / edge / slim blocks; `r1_of_theta_le_RNUM` -> (R1); `E.Δ_gt_BSTD2` -> `1200 ≤ Δ`).

Consumer `exists_boundaryChainE_register_stored_RNUM`: the CHOICE and `χ` stored in a
stored-choice early choice `EW` (halved `egOf`), with `e < 1/1000` and `C_ρ Λ Δ < 10⁻⁶` (G4); on
every tail member of every standing sequence, every supply carries the chain.
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

/-- **A2 v3 at the register** (see the module docstring). -/
theorem exists_boundaryChainE_register_RNUM (Kj : ℕ) {cadj : ℝ} (hcadj : 0 < cadj) :
    ∃ (Ξ Γ Sg eg c cw : Fin 3 → ℝ) (χ : BoundaryChainThresholds_BSTD2),
      BoundaryChainChoiceValidity_BAUGD Ξ Γ Sg eg c cw cadj ∧ (∀ j, χ.eg j = eg j / 2) ∧
      χ.ϑ₀ ≤ min (eg 0) (min (eg 1) (eg 2)) / (16 * bmConst_BAUGC) ∧
      ∀ {Θ : BoundaryProducerThresholds_BSTD1} (E : BoundaryEarlyOverX_BSTD2 Θ χ) {V : ℝ}
        (R : BoundaryRegisterOverX_BSTD2 E V) {K : ℕ} {A : ℝ → ℝ} {θ : ℝ}
        {W : CompactCarrier.{0}} [ConnectedSpace W.Carrier]
        {g : SmoothRiemannianMetric W.model W.Carrier} {δn : ℝ} {n : ℕ}
        {B : NearlyCuspidalBoundary W g K δn}
        {oM : ManifoldOrientation 𝓘(ℝ, E3) (W.pieceInterior ⊤) 3},
        0 ≤ θ → θ ≤ χ.ϑ₀ →
        ∀ S : BoundarySupply K A E.β R.βd R.εN E.Λ E.w E.Δ E.σs E.σc E.μ E.b E.s E.b' E.s' E.ε
          E.γc E.βc R.Lmax E.τ E.γ R.δlocal E.εr E.e E.T V E.vs E.ζ E.Λz θ W g δn n B oM,
        S.SeparatedCollarZero_BIF →
        ∃ DP : BoundaryAugmentedDataPV3 S (actualSlotsV2_BAUGD S) Γ Sg eg,
          ∃ C : BoundaryGaf02ChainE DP Kj Ξ c cw boundaryChainCutoffConst_BAUGD
              boundaryDerivBound_BDFB cutoffKappa_BAUGP2 cadj,
            ∀ st, ∃ O, C.toChain.slot st = .active O := by
  classical
  have hthr := threeSplittingExclusionThreshold_pos.{0, 0}
  have hthr1 := threeSplittingExclusionThreshold_lt.{0, 0}
  obtain ⟨Ξ, Γ, Sg, eg, c, cw, hval, σ, hσ, -, η₂, γ₀, ηc, θt, hη₂, hγ₀, hηc, hθt, -, hP⟩ :=
    exists_boundaryGaf02ChainE_v3_BAUGD Kj (ν := threeSplittingExclusionThreshold.{0, 0} / 3)
      hcadj (by positivity) (by linarith)
  let Cβ : ℝ → ℝ → Prop := fun β₂ Δ => 0 < β₂ ∧ β₂ < 1 / 1000000 ∧ 1200 ≤ Δ
  have hrow' : ∀ (β₂ Δ : ℝ) (_ : Cβ β₂ Δ), _ := fun β₂ Δ h => hP β₂ h.1 h.2.1 Δ h.2.2
  choose η₁ θs Lc η₀ hη₁ hθs hθs1 hLc hη₀ hS using hrow'
  clear hθs1 hLc
  have hP0 : 0 < 16 * bmConst_BAUGC := by linarith [one_le_bmConst_BAUGC]
  have hegpos : ∀ j, 0 < eg j := fun j => (hval.quality j).2.2.2.1
  let χ : BoundaryChainThresholds_BSTD2 :=
    { ν := threeSplittingExclusionThreshold.{0, 0} / 3
      eg := fun j => eg j / 2
      σ := σ
      η₂ := η₂
      γ₀ := γ₀
      ηc := ηc
      θt := θt
      ϑ₀ := min (eg 0) (min (eg 1) (eg 2)) / (16 * bmConst_BAUGC)
      η₁ := fun β₂ Δ => if h : Cβ β₂ Δ then η₁ β₂ Δ h else 1
      Lc₁ := fun β₂ Δ => if h : Cβ β₂ Δ then Lc β₂ Δ h else 1
      η₀₁ := fun β₂ Δ => if h : Cβ β₂ Δ then η₀ β₂ Δ h else 1
      θs := fun β₂ Δ => if h : Cβ β₂ Δ then θs β₂ Δ h else 1
      Lc₂ := fun β₂ Δ => if h : Cβ β₂ Δ then Lc β₂ Δ h else 1
      η₀₂ := fun β₂ Δ => if h : Cβ β₂ Δ then η₀ β₂ Δ h else 1
      ν_pos := by positivity
      three_ν_le := by linarith
      eg_pos := fun j => half_pos (hegpos j)
      σ_pos := hσ
      η₂_pos := hη₂
      γ₀_pos := hγ₀
      ηc_pos := hηc
      θt_pos := hθt
      ϑ₀_pos := div_pos (lt_min (hegpos 0) (lt_min (hegpos 1) (hegpos 2))) hP0
      η₁_pos := fun β₂ Δ => dite_mem_BSTD1 (fun x => 0 < x) (hη₁ β₂ Δ) one_pos
      η₀₁_pos := fun β₂ Δ => dite_mem_BSTD1 (fun x => 0 < x) (hη₀ β₂ Δ) one_pos
      θs_pos := fun β₂ Δ => dite_mem_BSTD1 (fun x => 0 < x) (hθs β₂ Δ) one_pos
      η₀₂_pos := fun β₂ Δ => dite_mem_BSTD1 (fun x => 0 < x) (hη₀ β₂ Δ) one_pos }
  refine ⟨Ξ, Γ, Sg, eg, c, cw, χ, hval, fun j => rfl, le_rfl, ?_⟩
  intro Θ E V R K A θ W _ g δn n B oM hθ0 hθ S hsep
  have hC : Cβ E.β₂ E.Δ := ⟨E.β₂_pos, E.β₂_lt6, by linarith [E.Δ_gt_BSTD2]⟩
  have e1 : χ.η₁ E.β₂ E.Δ = η₁ E.β₂ E.Δ hC := dite_eq_left hC
  have e2 : χ.Lc₁ E.β₂ E.Δ = Lc E.β₂ E.Δ hC := dite_eq_left hC
  have e3 : χ.η₀₁ E.β₂ E.Δ = η₀ E.β₂ E.Δ hC := dite_eq_left hC
  have e4 : χ.θs E.β₂ E.Δ = θs E.β₂ E.Δ hC := dite_eq_left hC
  obtain ⟨s1, s2, s3, s4, s5, s6, s7, s8, s9, s10, s11, s12, s13, s14, s15, s16, s17, s18⟩ :=
    R.std_block_BSTD2
  obtain ⟨f1, f2, f3, f4, f5, f6, f7, f8, f9, f10, f11, f12, f13, f14, f15, f16, f17, f18, f19,
    f20, f21, f22, f23, f24, f25, f26, f27, f28, f29, f30, f31, d1, d2, d3, d4, d5, d6, d7, d8,
    d9, d10, d11, m1, -, -, m4, m5, m6, m7, m8, m9⟩ := R.chi_block_BSTD2
  rw [e1] at f21 f22
  rw [e3] at d1 d3
  rw [e2] at d4
  rw [e4] at m4 m5 m6 m8
  have f4' : 10 ^ 6 * E.Δ * E.Λ < 1 / 10 ^ 5 := by
    have e6 : (10 : ℝ) ^ 6 = 1000000 := by norm_num
    have e5 : (1 : ℝ) / 10 ^ 5 = 1 / 100000 := by norm_num
    rw [e6, e5]
    exact f4
  exact hS E.β₂ E.Δ hC S s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 s12 s13 s14 s15 s16 s17 s18
    f1 f2 f3 f4' f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 f15 f16 f17 f18 f19 f20 f21 f22 f23 f24 f25
    f26 f27 f28 f29 f30 f31 s2 s5 s6 s7 s8 s9 d1 d2 d3 d4 d5 d6 f23 d7 d8 f26 d9 d10 d11 m1
    m4 m5 m6 m7 m8 m9 hθ0 (r1_of_theta_le_RNUM le_rfl hθ) hsep

/-- **The stored-choice early choice at a given CHI record with halved `eg`**, whose parameters are
those of a staged prefix `P` meeting `bdryRowRequests_RNUM C_ρ` (the early step of
`exists_boundaryChainE_register_stored_RNUM`). -/
theorem exists_earlyWithChoice_halved_RNUM (K : ℕ) (hK : 10 ≤ K) (A : ℝ → ℝ)
    (hA : ∀ w, 0 < w → w < euclideanThreeUnitBallVolume → 0 < A w) (eg : Fin 3 → ℝ)
    (χ : BoundaryChainThresholds_BSTD2) (hχeg : ∀ j, χ.eg j = eg j / 2) (Cρ : ℝ) :
    ∃ EW : BoundaryEarlyWithChoice_BSTD2 K hK A hA (fun e : Fin 3 → ℝ => fun j => e j / 2),
      EW.choice = eg ∧ EW.χ = χ ∧ ∃ P : C14PreFinal,
        EW.early.toBoundaryEarlyParams_BSTD1 = P.toBdryParams_BSTD1 ∧
          (bdryRowRequests_RNUM Cρ).toC14.Meets P := by
  have hχeg' : χ.eg = (fun e : Fin 3 → ℝ => fun j => e j / 2) eg := funext hχeg
  have hθ0 : 0 < min (1 / 200 : ℝ) χ.ϑ₀ := lt_min (by norm_num) χ.ϑ₀_pos
  have hθ1 : min (1 / 200 : ℝ) χ.ϑ₀ < 1 / 100 := (min_le_left _ _).trans_lt (by norm_num)
  have hθ2 : min (1 / 200 : ℝ) χ.ϑ₀ ≤ χ.ϑ₀ := min_le_right _ _
  have hν0 : 0 < min χ.ν (1 / 2000000) := lt_min χ.ν_pos (by norm_num)
  have hν1 : min χ.ν (1 / 2000000) < 1 / 1000000 := (min_le_right _ _).trans_lt (by norm_num)
  have hν3 : 3 * min χ.ν (1 / 2000000) ≤ threeSplittingExclusionThreshold.{0, 0} := by
    linarith [χ.three_ν_le, min_le_left χ.ν (1 / 2000000)]
  obtain ⟨EW, hc, hχ, -, -, P, hM, hEP⟩ := exists_boundaryEarlyWithChoice_of_BSTD2 K hK A hA
    (fun e : Fin 3 → ℝ => fun j => e j / 2) eg χ hχeg' hθ0 hθ1 hθ2 hν0 hν1 hν3
    (bdryRowRequests_RNUM Cρ)
  exact ⟨EW, hc, hχ, P, hEP, hM⟩

/-- **The register meeting the late request on `r_∂`, with the member outputs** (the register step
of `exists_boundaryChainE_register_stored_RNUM`). -/
theorem exists_register_rdRequest_RNUM {K : ℕ} {hK : 10 ≤ K} {A : ℝ → ℝ}
    {hA : ∀ w, 0 < w → w < euclideanThreeUnitBallVolume → 0 < A w} {Ch : Type}
    {egOf : Ch → Fin 3 → ℝ} (EW : BoundaryEarlyWithChoice_BSTD2 K hK A hA egOf)
    (Sq : BoundaryStandingSequence_BSTD1 K A
      (bdryThresholdsBA_BSTD2 K hK A hA EW.θ EW.νBA).δStar) (c2 : ℝ) :
    ∃ V : ℝ, ∃ R : BoundaryRegisterOverXBA_BSTD2 EW.early V,
      R.rd ≤ (bdryRdRequest_RNUM c2).rd V R.δlocal R.Lmax R.βd R.εN R.Hd ∧
      ∃ n₀ : ℕ, ∀ m, n₀ ≤ m → BoundaryMemberOutputXBA_BSTD2 Sq m R := by
  obtain ⟨V, -, R, -, -, -, -, hrd, n₀, hR⟩ :=
    exists_boundarySequenceAssignmentWC_req_BSTD2 EW Sq (bdryRdRequest_RNUM c2)
  exact ⟨V, R, hrd, n₀, hR⟩

/-- **The whole chain of the boundary route at the register** (stored CHOICE, halved `egOf`): for
every jet order `K_j` and `c_adj > 0` there are the CHOICE with its validity record and a
stored-choice early choice `EW` of it, whose parameters are those of a staged prefix `P` meeting
`bdryRowRequests_RNUM C_ρ` (`C_ρ` of N76-9: `e < 1/1000` and `C_ρ Λ Δ < 10⁻⁶`), such that for every
standing sequence there are `V`, a register `R` meeting the late request `bdryRdRequest_RNUM (c 2)`
and `n₀` such that on every member `m ≥ n₀` the member output holds and EVERY supply at the
register's numbers with the separated branch carries an enhanced chain with all slots active. The
rows (BCG04-07, F1, edge parent, ZSP02, FC43) follow from the chain by the consumers of
`BoundaryRegisterRowNumericsApplicationsRNUM` / `BoundaryRegisterA4NumericsRNUM`, whose hypotheses
`hval`, `(P, hEP, hM)`, `hrd`, `hmem` are exactly the data returned here. -/
theorem exists_boundaryChainE_register_stored_RNUM (K : ℕ) (hK : 10 ≤ K) (A : ℝ → ℝ)
    (hA : ∀ w, 0 < w → w < euclideanThreeUnitBallVolume → 0 < A w) (Kj : ℕ) {cadj : ℝ}
    (hcadj : 0 < cadj) :
    ∃ (Ξ Γ Sg eg c cw : Fin 3 → ℝ), BoundaryChainChoiceValidity_BAUGD Ξ Γ Sg eg c cw cadj ∧
      ∃ EW : BoundaryEarlyWithChoice_BSTD2 K hK A hA (fun e : Fin 3 → ℝ => fun j => e j / 2),
        EW.choice = eg ∧
        (∃ P : C14PreFinal, EW.early.toBoundaryEarlyParams_BSTD1 = P.toBdryParams_BSTD1 ∧
          (bdryRowRequests_RNUM (100 * (boundaryDerivBound_BDFB + 1) *
            (1 + boundaryChainCutoffConst_BAUGD + cw 0 / Sg 0))).toC14.Meets P) ∧
        ∀ Sq : BoundaryStandingSequence_BSTD1 K A
            (bdryThresholdsBA_BSTD2 K hK A hA EW.θ EW.νBA).δStar,
          ∃ V : ℝ, ∃ R : BoundaryRegisterOverXBA_BSTD2 EW.early V,
            R.rd ≤ (bdryRdRequest_RNUM (c 2)).rd V R.δlocal R.Lmax R.βd R.εN R.Hd ∧
            ∃ n₀ : ℕ, ∀ m, n₀ ≤ m → BoundaryMemberOutputXBA_BSTD2 Sq m R ∧
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
  have hEW := exists_earlyWithChoice_halved_RNUM K hK A hA eg χ hχeg
    (100 * (boundaryDerivBound_BDFB + 1) * (1 + boundaryChainCutoffConst_BAUGD + cw 0 / Sg 0))
  obtain ⟨EW, hc, hχ, P, hEP, hM⟩ := hEW
  subst hχ
  refine ⟨Ξ, Γ, Sg, eg, c, cw, hval, EW, hc, ⟨P, hEP, hM⟩, fun Sq => ?_⟩
  have hreg := exists_register_rdRequest_RNUM EW Sq (c 2)
  obtain ⟨V, R, hrd, n₀, hR⟩ := hreg
  refine ⟨V, R, hrd, n₀, fun m hm => ⟨hR m hm, fun oM S hsep => ?_⟩⟩
  exact hmain EW.early.toBoundaryEarlyOverX_BSTD2 R.toBoundaryRegisterOverX_BSTD2 EW.θ_pos.le
    EW.θ_le S hsep

end DifferentialGeometry.Geometry.Collapse
