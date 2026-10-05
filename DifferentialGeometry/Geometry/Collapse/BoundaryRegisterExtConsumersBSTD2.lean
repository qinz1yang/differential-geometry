import DifferentialGeometry.Geometry.Collapse.BoundaryRegisterExtBSTD2
import DifferentialGeometry.Geometry.Fibration.ActualStageChainERow

/-!
# Consumers of the extended boundary register (lane BSTD2, G1)

* `exists_chainThresholds_chainE_BSTD2` (the closed CHI instance of `χ` and the CHI block fed by the
  register): GAF01's CHOICE at `ν = thr/3` and the thresholds of `gaf02_chainE_row_GAF8` give a CHI
  record `χ` (late thresholds Skolemized in `(β₂, Δ)`); then for EVERY extended early choice over
  `χ`, every extended register and every packet of the final closed family at exactly the register's
  numbers, the enhanced chain `Gaf02ChainE` exists — every one of the row's 54 numerical premises
  is discharged by the register (`BoundaryRegisterOverX_BSTD2.chi_block_BSTD2`), none is assumed.
* `BoundaryRegisterOverX_BSTD2.isCompact_pieces_BSTD2`: BCF02's compact pieces (`M₂`, `P_e`, `R_c`,
  `P_e ∩ R_c`) on every supply at the register's parameters and an index `m` with `1140Δ ≤ 35m`,
  with no numerical premise (the eighteen of `isCompact_pieces_BCF2K` from the register).
* `exists_boundarySequenceAssignmentX_bcf02_BSTD2`: ONE assignment (extended early choice → `V` →
  extended register → `n₀`) whose every tail member `n` carries its output AND the compactness of
  BCF02's pieces on every supply at the member's data and index `n + 1`.
-/

set_option autoImplicit false

noncomputable section

open Set Function Metric Bundle Manifold Filter
open scoped ContDiff Manifold Topology ENNReal
open DifferentialGeometry.Topology.Ehresmann DifferentialGeometry.Topology.Manifold
open DifferentialGeometry.Geometry.Riemannian GC.MetricGeometry
open DifferentialGeometry GC.Endpoint DifferentialGeometry.Geometry.Hyperbolic
open DifferentialGeometry.Analysis DifferentialGeometry.Topology

namespace DifferentialGeometry.Geometry.Collapse

local notation "E3" => EuclideanSpace ℝ (Fin 3)

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace

attribute [local instance] nezero_finrank_euclideanThree_LC87

attribute [local instance] interiorCharted_BDRY1 interiorManifold_BDRY1
  connectedSpace_interior_BDRY2

attribute [local instance] BoundaryStandingSequence_BSTD1.conn

/-! ### The closed CHI instance -/

/-- **The CHI record of the closed chain producer, and the CHI block fed by the register**: for
every jet order `Kj` and target `cadj > 0` there are GAF01's moduli and CHOICE (`Ξ, c, Γ, Σ, c_w`,
`c 2 < cadj`) and a CHI record `χ` (`ν = thr/3`, `e_j` and the first thresholds of
`gaf02_chainE_row_GAF8`, its late thresholds as functions of `(β₂, Δ)`) such that for EVERY extended
early choice `E` over `χ` (any producer thresholds `Θ`), every extended register `R` over `(E, V)`
and every packet `P` of the final closed family at exactly the register's numbers, every base point
carries an enhanced chain `Gaf02ChainE` on the SAME choice. No numerical premise. -/
theorem exists_chainThresholds_chainE_BSTD2 (Kj : ℕ) {cadj : ℝ} (hcadj : 0 < cadj) :
    ∃ (Ξ : Fin 3 → ℝ → ℝ) (c Γ Sg cw : Fin 3 → ℝ) (χ : BoundaryChainThresholds_BSTD2),
      c 2 < cadj ∧
      ∀ {Θ : BoundaryProducerThresholds_BSTD1} (E : BoundaryEarlyOverX_BSTD2 Θ χ) {V : ℝ}
        (R : BoundaryRegisterOverX_BSTD2 E V)
        {X : Type} [MetricSpace X] [ChartedSpace E3 X] [IsManifold 𝓘(ℝ, E3) ∞ X]
        [CompactSpace X] {g : SmoothRiemannianMetric 𝓘(ℝ, E3) X}
        {hmetric : ∀ a b : X, riemannianEDistOf g a b = ENNReal.ofReal (dist a b)}
        {ρ : X → ℝ} {hρ : ∀ p, 0 < ρ p} {K : ℕ}
        (P : LocalChartPacketsC14 X g hmetric ρ hρ E.Λ E.β E.Δ E.σs K E.σc E.μ E.b E.s E.b'
          E.s' E.ε E.γc E.βc R.Lmax E.τ E.γ R.δlocal E.εr E.e E.T V E.vs E.ζ E.Λz) (x₀ : X),
        ∃ C : Gaf02ChainE P Kj (fun j => Ξ j (Γ j)) Γ Sg χ.eg c cw, C.x₀ = x₀ := by
  classical
  have hthr := threeSplittingExclusionThreshold_pos.{0, 0}
  have hthr1 := threeSplittingExclusionThreshold_lt.{0, 0}
  obtain ⟨θ₀, Ξ, c, Γ, Sg, eg, cw, hj, -, -, hc2, σ, η₂, γ₀, ηc, θt, hσ, -, hη₂, hγ₀, -, hηc,
    hθt, -, hrow⟩ := gaf02_chainE_row_GAF8 Kj (ν := threeSplittingExclusionThreshold.{0, 0} / 3)
      (by positivity) (by linarith) hcadj
  let Cβ : ℝ → ℝ → Prop := fun β₂ Δ => 0 < β₂ ∧ β₂ < 1 / 1000000 ∧ 1200 ≤ Δ
  have hrow' : ∀ (β₂ Δ : ℝ) (h : Cβ β₂ Δ), _ := fun β₂ Δ h => hrow β₂ h.1 h.2.1 Δ h.2.2
  choose η₁ Lc₁ η₀₁ θs Lc₂ η₀₂ hη₁ hLc₁ hη₀₁ hθs hθs1 hLc₂ hη₀₂ hP using hrow'
  clear hLc₁ hθs1 hLc₂
  let χ : BoundaryChainThresholds_BSTD2 :=
    { ν := threeSplittingExclusionThreshold.{0, 0} / 3
      eg := eg
      σ := σ
      η₂ := η₂
      γ₀ := γ₀
      ηc := ηc
      θt := θt
      ϑ₀ := 1
      η₁ := fun β₂ Δ => if h : Cβ β₂ Δ then η₁ β₂ Δ h else 1
      Lc₁ := fun β₂ Δ => if h : Cβ β₂ Δ then Lc₁ β₂ Δ h else 1
      η₀₁ := fun β₂ Δ => if h : Cβ β₂ Δ then η₀₁ β₂ Δ h else 1
      θs := fun β₂ Δ => if h : Cβ β₂ Δ then θs β₂ Δ h else 1
      Lc₂ := fun β₂ Δ => if h : Cβ β₂ Δ then Lc₂ β₂ Δ h else 1
      η₀₂ := fun β₂ Δ => if h : Cβ β₂ Δ then η₀₂ β₂ Δ h else 1
      ν_pos := by positivity
      three_ν_le := by linarith
      eg_pos := fun j => (hj j).2.2.2.2.2.2.2.1
      σ_pos := hσ
      η₂_pos := hη₂
      γ₀_pos := hγ₀
      ηc_pos := hηc
      θt_pos := hθt
      ϑ₀_pos := one_pos
      η₁_pos := fun β₂ Δ => dite_mem_BSTD1 (fun x => 0 < x) (hη₁ β₂ Δ) one_pos
      η₀₁_pos := fun β₂ Δ => dite_mem_BSTD1 (fun x => 0 < x) (hη₀₁ β₂ Δ) one_pos
      θs_pos := fun β₂ Δ => dite_mem_BSTD1 (fun x => 0 < x) (hθs β₂ Δ) one_pos
      η₀₂_pos := fun β₂ Δ => dite_mem_BSTD1 (fun x => 0 < x) (hη₀₂ β₂ Δ) one_pos }
  refine ⟨Ξ, c, Γ, Sg, cw, χ, hc2, fun {Θ} E {V} R {X} _ _ _ _ {g hmetric ρ hρ K} P x₀ => ?_⟩
  have hC : Cβ E.β₂ E.Δ := ⟨E.β₂_pos, E.β₂_lt6, by linarith [E.Δ_gt_BSTD2]⟩
  have e1 : χ.η₁ E.β₂ E.Δ = η₁ E.β₂ E.Δ hC := dite_eq_left hC
  have e2 : χ.Lc₁ E.β₂ E.Δ = Lc₁ E.β₂ E.Δ hC := dite_eq_left hC
  have e3 : χ.η₀₁ E.β₂ E.Δ = η₀₁ E.β₂ E.Δ hC := dite_eq_left hC
  have e4 : χ.θs E.β₂ E.Δ = θs E.β₂ E.Δ hC := dite_eq_left hC
  have e5 : χ.Lc₂ E.β₂ E.Δ = Lc₂ E.β₂ E.Δ hC := dite_eq_left hC
  have e6 : χ.η₀₂ E.β₂ E.Δ = η₀₂ E.β₂ E.Δ hC := dite_eq_left hC
  obtain ⟨f1, f2, f3, f4, f5, f6, f7, f8, f9, f10, f11, f12, f13, f14, f15, f16, f17, f18, f19,
    f20, f21, f22, f23, f24, f25, f26, f27, f28, f29, f30, f31, d1, d2, d3, d4, d5, d6, d7, d8,
    d9, d10, d11, m1, m2, m3, m4, m5, m6, m7, m8, m9⟩ := R.chi_block_BSTD2
  rw [e1] at f21 f22
  rw [e3] at d1 d3
  rw [e2] at d4
  rw [e6] at m2
  rw [e5] at m3
  rw [e4] at m4 m5 m6 m8
  exact hP E.β₂ E.Δ hC P f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 f15 f16 f17 f18 f19 f20
    f21 f22 f23 f24 f25 f26 f27 f28 f29 f30 f31 d1 d2 d3 d4 d5 d6 d7 d8 d9 d10 d11 m1 m2 m3 m4 m5
    m6 m7 m8 m9 x₀

/-! ### BCF02's compact pieces -/

/-- **BCF02's compact pieces at the extended register** (consumer of
`BoundaryRegisterOverX_BSTD2.bcf02_premises_BSTD2`): on every supply at the register's parameters
(any `θ`, carrier, member ratio, orientation) with an index `m` such that `1140Δ ≤ 35m`, every
compact-slim choice over the chain data has `M₂`, `P_e`, `R_c`, `P_e ∩ R_c` compact — the eighteen
numerical premises of `isCompact_pieces_BCF2K` come from the register. -/
theorem BoundaryRegisterOverX_BSTD2.isCompact_pieces_BSTD2 {Θ : BoundaryProducerThresholds_BSTD1}
    {χ : BoundaryChainThresholds_BSTD2} {E : BoundaryEarlyOverX_BSTD2 Θ χ} {V : ℝ}
    (R : BoundaryRegisterOverX_BSTD2 E V) {K : ℕ} {A : ℝ → ℝ} {θ : ℝ} {W : CompactCarrier.{0}}
    [ConnectedSpace W.Carrier] {g : SmoothRiemannianMetric W.model W.Carrier} {δn : ℝ} {m : ℕ}
    {B : NearlyCuspidalBoundary W g K δn}
    {oM : ManifoldOrientation 𝓘(ℝ, E3) (W.pieceInterior ⊤) 3}
    {S : BoundarySupply K A E.β R.βd R.εN E.Λ E.w E.Δ E.σs E.σc E.μ E.b E.s E.b' E.s' E.ε E.γc
      E.βc R.Lmax E.τ E.γ R.δlocal E.εr E.e E.T V E.vs E.ζ E.Λz θ W g δn m B oM}
    {Φ : BoundaryInteriorSlots_BIF S} {D : BoundaryAugmentedData S Φ} {Kj : ℕ}
    {Ξ Sg eg c cw : Fin 3 → ℝ} {bcut bder κ : ℝ}
    {C : BoundaryGaf02Chain D Kj Ξ Sg eg c cw bcut bder κ} {Bs : BoundaryGaf02Bases C}
    {ZC : BoundaryInitialCoresSpec C} (hm : 1140 * E.Δ ≤ 35 * (m : ℝ))
    (Kc : BoundaryCompactSlimChoice Bs ZC) :
    IsCompact Kc.M₂ ∧ IsCompact Kc.edgePiece ∧ IsCompact Kc.remainder ∧
      IsCompact (Kc.edgePiece ∩ Kc.remainder) := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18⟩ :=
    R.bcf02_premises_BSTD2 hm
  exact Kc.isCompact_pieces_BCF2K h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 h13 h14 h15 h16 h17 h18

/-- **Consumer: ONE assignment whose tail feeds BCF02** — for every extended early choice and every
standing sequence, `V`, an extended register and `n₀` such that every member `n ≥ n₀` carries the
extended output, and on EVERY supply at the member's data (carrier `W_n`, ratio `δ_{n+1}`, index
`n + 1`, the register's parameters, any `θ`, any orientation) every compact-slim choice over the
chain data has BCF02's pieces compact. -/
theorem exists_boundarySequenceAssignmentX_bcf02_BSTD2 {K : ℕ} {hK : 10 ≤ K} {A : ℝ → ℝ}
    {hA : ∀ w, 0 < w → w < euclideanThreeUnitBallVolume → 0 < A w}
    {χ : BoundaryChainThresholds_BSTD2} (E : BoundaryEarlyChoicesX_BSTD2 K hK A hA χ)
    (Sq : BoundaryStandingSequence_BSTD1 K A (bdryThresholds_BSTD1 K hK A hA).δStar) :
    ∃ V : ℝ, ∃ R : BoundaryRegisterOverX_BSTD2 E V, ∃ n₀ : ℕ, ∀ n, n₀ ≤ n →
      Nonempty (BoundaryMemberOutputX_BSTD2 Sq n R) ∧
      ∀ (θ : ℝ) (oM : ManifoldOrientation 𝓘(ℝ, E3) ((Sq.W n).pieceInterior ⊤) 3)
        (Sup : BoundarySupply K A E.β R.βd R.εN E.Λ E.w E.Δ E.σs E.σc E.μ E.b E.s E.b' E.s' E.ε
          E.γc E.βc R.Lmax E.τ E.γ R.δlocal E.εr E.e E.T V E.vs E.ζ E.Λz θ (Sq.W n) (Sq.g n)
          (boundaryCounterexampleRatio Sq.δ₀ (n + 1)) (n + 1) (Sq.B n) oM)
        (Φ : BoundaryInteriorSlots_BIF Sup) (D : BoundaryAugmentedData Sup Φ) (Kj : ℕ)
        (Ξ Sg eg c cw : Fin 3 → ℝ) (bcut bder κ : ℝ)
        (C : BoundaryGaf02Chain D Kj Ξ Sg eg c cw bcut bder κ) (Bs : BoundaryGaf02Bases C)
        (ZC : BoundaryInitialCoresSpec C) (Kc : BoundaryCompactSlimChoice Bs ZC),
        IsCompact Kc.M₂ ∧ IsCompact Kc.edgePiece ∧ IsCompact Kc.remainder ∧
          IsCompact (Kc.edgePiece ∩ Kc.remainder) := by
  obtain ⟨V, R, n₀, hR⟩ := exists_boundarySequenceAssignmentX_BSTD2 E Sq
  refine ⟨V, R, n₀, fun n hn => ⟨hR n hn, ?_⟩⟩
  obtain ⟨⟨-, hidx⟩⟩ := hR n hn
  intro θ oM Sup Φ D Kj Ξ Sg eg c cw bcut bder κ C Bs ZC Kc
  exact R.isCompact_pieces_BSTD2 hidx Kc

end DifferentialGeometry.Geometry.Collapse
