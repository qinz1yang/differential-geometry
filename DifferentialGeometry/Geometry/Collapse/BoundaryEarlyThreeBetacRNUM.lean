import DifferentialGeometry.Geometry.Collapse.BoundaryEarlyWithChoiceBSTD2

/-!
# The reservation `3 β_c ≤ β₂` carried through the three BSTD2 producers (lane S-REG-NUM3, G9)

Review 77 (D77-4, D77-13): F1 (`rim_mem_source_zero_OF1`, BCG07) needs `3 β_c ≤ β₂`, and it must be
bound at a LEGAL dependency node, not "true for large index". The three producers of the early
choice behave as follows.

* `exists_boundaryEarlyOver_staged_BSTD2` (BoundaryEarlyStagedGenericBSTD2): conjunct 9
  `3 * P.βc ≤ P.β 2` of the staged prefix `P` (HAS it).
* `exists_boundaryEarlyOverX_staged_layer_BSTD2` (same file): DROPS it
  (`obtain ⟨E, hEϑ, -, -, -, P, -, hM', -, hEP⟩`), and so do the XBA and the stored-choice
  producers built on it.

The binding node is stage 3 of the staged prefix: stage 2 (`c14_stage_collar_STG`) chooses
`β_c ≤ c14β₂Value_STG Rq g / 3`, where the value is the explicit function
`min(β₀, min(r, min(10⁻⁷, γ_T/20)))` of data fixed BEFORE `β_c` (`β₀(γ)`, `γ_T`, and the early `β₂`
request read at the prefix with `γ_c`); stage 3 (`c14_stage_excl_STG`) then sets `β₂` EXACTLY to
that value. So `β_c` is bound after the quantities that determine `β₂` and the inequality is
`h3βc` at the node `β₂`. No reordering of the dependency chain is needed: the order is
chain numbers ≺ first thresholds (`γ`, `β_c γ_c`) ≺ `β₂` (a reserved value) ≺ `Δ` ≺ ... .

This module re-exports the conjunct through the three producers (new copies of the proofs with the
extra conjunct; the old theorems are untouched):

* `exists_boundaryEarlyOverX_staged_layer_three_RNUM`;
* `exists_boundaryEarlyOverXBA_staged_three_RNUM`;
* `exists_boundaryEarlyWithChoice_of_three_RNUM` (stored CHOICE, any `Rq`) and
  `exists_boundaryEarlyWithChoice_three_RNUM` (the layer `θ = min(1/200, ϑ₀)`), both with the
  conclusion `3 * EW.early.βc ≤ EW.early.β₂`.
-/

set_option autoImplicit false

noncomputable section

open Set Function Metric Bundle Manifold Filter
open scoped ContDiff Manifold Topology ENNReal

namespace DifferentialGeometry.Geometry.Collapse

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace

/-- **The extended staged early choice with the reservation**
(`exists_boundaryEarlyOverX_staged_layer_BSTD2` with the dropped conjunct `3 β_c ≤ β 2` of the
staged prefix re-exported). -/
theorem exists_boundaryEarlyOverX_staged_layer_three_RNUM (Θ : BoundaryProducerThresholds_BSTD1)
    (χ : BoundaryChainThresholds_BSTD2) {θ₀ : ℝ} (hθ₀ : 0 < θ₀) (hθ₀1 : θ₀ < 1 / 100)
    (hθ₀ϑ : θ₀ ≤ χ.ϑ₀) (Rq : C14StagedRequestsSTG) :
    ∃ E : BoundaryEarlyOverX_BSTD2 Θ χ, E.ϑ = (fun _ => θ₀) ∧ ∃ P : C14PreFinal,
      Rq.toC14.Meets P ∧ 3 * P.βc ≤ P.β 2 ∧
        E.toBoundaryEarlyParams_BSTD1 = P.toBdryParams_BSTD1 := by
  let t : C14Tol :=
    { γT := 1
      θs := 1 / 2
      θe := 1 / 2
      θ2 := 1 / 2
      Cρ := 1
      e₁ := 1
      C₁ := 1
      γT_pos := one_pos
      γT_le := le_rfl
      θs_pos := by norm_num
      θs_lt := by norm_num
      θe_pos := by norm_num
      θe_lt := by norm_num
      θ2_pos := by norm_num
      θ2_lt := by norm_num
      Cρ_pos := one_pos
      e₁_pos := one_pos
      C₁_pos := one_pos }
  obtain ⟨E, hEϑ, -, -, -, P, -, hM', h3, hEP⟩ :=
    exists_boundaryEarlyOver_staged_BSTD2 Θ t (fun _ => θ₀)
      (fun _ => hθ₀) 0 le_rfl 1 le_rfl (tcp01SupportBound + 1) le_rfl
      ((chiRequests_BSTD2 χ).inf Rq)
  rw [C14StagedRequestsSTG.toC14_inf] at hM'
  have hM : (chiRequests_BSTD2 χ).toC14.Meets P := C14StagedRequests.Meets.inf_left hM'
  have hMR : Rq.toC14.Meets P := C14StagedRequests.Meets.inf_right hM'
  have eγ : E.γ = P.γ := congrArg (fun q : BoundaryEarlyParams_BSTD1 => q.γ) hEP
  have eβc : E.βc = P.βc := congrArg (fun q : BoundaryEarlyParams_BSTD1 => q.βc) hEP
  have eγc : E.γc = P.γc := congrArg (fun q : BoundaryEarlyParams_BSTD1 => q.γc) hEP
  have eβ₂ : E.β₂ = P.β₂ := congrArg (fun q : BoundaryEarlyParams_BSTD1 => q.β₂) hEP
  have eΔ : E.Δ = P.Δ := congrArg (fun q : BoundaryEarlyParams_BSTD1 => q.Δ) hEP
  have eσc : E.σc = P.σc := congrArg (fun q : BoundaryEarlyParams_BSTD1 => q.σc) hEP
  have eμ : E.μ = P.μ := congrArg (fun q : BoundaryEarlyParams_BSTD1 => q.μ) hEP
  have eΛ : E.Λ = P.Λ := congrArg (fun q : BoundaryEarlyParams_BSTD1 => q.Λ) hEP
  have eb : E.b = P.b := congrArg (fun q : BoundaryEarlyParams_BSTD1 => q.b) hEP
  have eσs : E.σs = P.σs := congrArg (fun q : BoundaryEarlyParams_BSTD1 => q.σs) hEP
  have evs : E.vs = P.vs := congrArg (fun q : BoundaryEarlyParams_BSTD1 => q.vs) hEP
  have eβ : E.β = P.β := congrArg (fun q : BoundaryEarlyParams_BSTD1 => q.β) hEP
  have eζ : E.ζ = P.ζ := congrArg (fun q : BoundaryEarlyParams_BSTD1 => q.ζ) hEP
  have ecap : E.cap = P.cap := congrArg (fun q : BoundaryEarlyParams_BSTD1 => q.cap) hEP
  have eT : E.T = P.T := congrArg (fun q : BoundaryEarlyParams_BSTD1 => q.T) hEP
  have hΔ := P.Δ_gt6
  have hΔ0 : 0 < P.Δ := by linarith
  have hC1 := egpGraphConst_pos_KC4
  have hC2 := sgpGraphBound_pos_GAF8
  have hC0 : 0 < tcpGraphConst := lt_of_lt_of_le one_pos one_le_tcpGraphConst
  have he0 := χ.eg_pos 0
  have he1 := χ.eg_pos 1
  have he2 := χ.eg_pos 2
  have hθs := χ.θs_pos P.β₂ P.Δ
  have hθt := χ.θt_pos
  -- the requests met by `P`, unfolded
  have hγ : P.γ ≤ χ.γ₀ := hM.γ_le
  have hγc : P.γc ≤ χ.γ₀ := hM.γc_le
  have hβc : P.βc ≤ χ.ηc := hM.βc_le
  have hβ₂ : P.β₂ ≤ min (χ.σ / 3) χ.η₂ := hM.β₂_le
  have hσc : P.σc ≤ min (1 / 1000) (min (χ.θt ^ 2 / 1000)
      ((χ.eg 1 / (20 * egpGraphConst)) ^ 2 / 10 ^ 8)) := hM.σc_le
  have hμ : P.μ ≤ min (1 / (100000 * P.Δ))
      (min (χ.θt / (100 * P.Δ)) (χ.eg 1 / (20 * egpGraphConst) / (200 * P.Δ))) := hM.μ_le
  have hΛ : P.Λ ≤ min (χ.eg 0 / (2000 * tcpGraphConst * P.Δ))
      (min (χ.eg 1 / (2000 * egpGraphConst * P.Δ)) (χ.eg 2 / (2000 * sgpGraphBound * P.Δ))) :=
    hM.Λ_le
  have hb : P.b ≤ min (bcf02Eta_BCF2K P.Δ)
      (min (bcf02Sigma_BCF2K P.Δ / 3) (min (χ.η₁ P.β₂ P.Δ) (χ.η₀₁ P.β₂ P.Δ))) := hM.b_le
  have hσs : P.σs ≤ min (χ.θt ^ 2 / 1000)
      (min ((χ.eg 1 / (20 * egpGraphConst)) ^ 2 / 10 ^ 8) (χ.θs P.β₂ P.Δ ^ 2 / (2 * 10 ^ 6))) :=
    hM.σs_le
  have hvs : P.vs ≤ min (χ.θt / 100)
      (min (χ.eg 1 / (20 * egpGraphConst) / 200) (χ.θs P.β₂ P.Δ / 200)) := hM.vs_le
  have hζ : P.ζ ≤ min (χ.θt ^ 2 / 1000) (min ((χ.eg 1 / (20 * egpGraphConst)) ^ 2 / 10 ^ 8)
      (min (1 / (1000 * (1000000 * P.Δ))) (χ.θs P.β₂ P.Δ ^ 2 / (2 * 10 ^ 6)))) := hM.ζ_le
  have hβ₁ : P.β 1 ≤ min (χ.η₁ P.β₂ P.Δ) (min (χ.η₀₁ P.β₂ P.Δ) (χ.η₀₂ P.β₂ P.Δ)) := hM.β₁_le
  have hcap : P.cap ≤ min (χ.θt / 100) (min (χ.eg 1 / (20 * egpGraphConst) /
      (100 * (1000000 * P.Δ))) (χ.θs P.β₂ P.Δ / (100 * (1000000 * P.Δ)))) := hM.cap_le
  -- the products `μΔ` and `CΔΛ`
  have hμΔ1 : P.μ * P.Δ ≤ 1 / 100000 := by
    have h := mul_le_mul_of_nonneg_right (hμ.trans (min_le_left _ _)) hΔ0.le
    have e : 1 / (100000 * P.Δ) * P.Δ = 1 / 100000 := by field_simp
    linarith
  have hμΔ2 : P.μ * P.Δ ≤ χ.θt / 100 := by
    have h := mul_le_mul_of_nonneg_right
      (hμ.trans ((min_le_right _ _).trans (min_le_left _ _))) hΔ0.le
    have e : χ.θt / (100 * P.Δ) * P.Δ = χ.θt / 100 := by field_simp
    linarith
  have hμΔ3 : P.μ * P.Δ ≤ χ.eg 1 / (20 * egpGraphConst) / 200 := by
    have h := mul_le_mul_of_nonneg_right
      (hμ.trans ((min_le_right _ _).trans (min_le_right _ _))) hΔ0.le
    have e : χ.eg 1 / (20 * egpGraphConst) / (200 * P.Δ) * P.Δ =
        χ.eg 1 / (20 * egpGraphConst) / 200 := by field_simp
    linarith
  have hgraph : ∀ (C e x : ℝ), 0 < C → 0 < e → x ≤ e / (2000 * C * P.Δ) →
      1000 * C * P.Δ * x < e := by
    intro C e x hC he hx
    have h := mul_le_mul_of_nonneg_left hx (by positivity : (0 : ℝ) ≤ 1000 * C * P.Δ)
    have e' : 1000 * C * P.Δ * (e / (2000 * C * P.Δ)) = e / 2 := by field_simp; ring
    linarith
  have hζΔ : P.ζ ≤ 1 / (1000 * (1000000 * P.Δ)) :=
    hζ.trans ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _)))
  have hϑmin : min θ₀ (min θ₀ θ₀) = θ₀ := by simp
  have hϑ0 : E.ϑ 0 = θ₀ := by rw [hEϑ]
  have hϑ1 : E.ϑ 1 = θ₀ := by rw [hEϑ]
  have hϑ2 : E.ϑ 2 = θ₀ := by rw [hEϑ]
  refine ⟨{ toBoundaryEarlyOver_BSTD1 := E
            γ_le_γ₀ := by rw [eγ]; exact hγ
            γc_le_γ₀ := by rw [eγc]; exact hγc
            βc_le_ηc := by rw [eβc]; exact hβc
            β₂_lt6 := by rw [eβ₂]; linarith [P.β₂_le7]
            three_β₂_le_σ := by rw [eβ₂]; linarith [hβ₂.trans (min_le_left _ _)]
            β₂_le_η₂ := by rw [eβ₂]; exact hβ₂.trans (min_le_right _ _)
            σc_le_milli := by rw [eσc]; exact hσc.trans (min_le_left _ _)
            σc_le_θt := by rw [eσc]; exact hσc.trans ((min_le_right _ _).trans (min_le_left _ _))
            σc_le_eg := by
              rw [eσc]; exact hσc.trans ((min_le_right _ _).trans (min_le_right _ _))
            μΔ_lt := by rw [eμ, eΔ]; linarith
            μΔ_le_θt := by rw [eμ, eΔ]; exact hμΔ2
            μΔ_lt_eg := by
              rw [eμ, eΔ]
              have : 0 < χ.eg 1 / (20 * egpGraphConst) := by positivity
              linarith
            Λ_lt_eg₀ := by
              rw [eΔ, eΛ]; exact hgraph _ _ _ hC0 he0 (hΛ.trans (min_le_left _ _))
            Λ_lt_eg₁ := by
              rw [eΔ, eΛ]
              exact hgraph _ _ _ hC1 he1 (hΛ.trans ((min_le_right _ _).trans (min_le_left _ _)))
            Λ_lt_eg₂ := by
              rw [eΔ, eΛ]
              exact hgraph _ _ _ hC2 he2 (hΛ.trans ((min_le_right _ _).trans (min_le_right _ _)))
            b_le_η := by rw [eb, eΔ]; exact hb.trans (min_le_left _ _)
            three_b_le_σ := by
              rw [eb, eΔ]; linarith [hb.trans ((min_le_right _ _).trans (min_le_left _ _))]
            b_le_η₁ := by
              rw [eb, eβ₂, eΔ]
              exact hb.trans ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _)))
            b_le_η₀₁ := by
              rw [eb, eβ₂, eΔ]
              exact hb.trans ((min_le_right _ _).trans ((min_le_right _ _).trans
                (min_le_right _ _)))
            σs_le_θt := by rw [eσs]; exact hσs.trans (min_le_left _ _)
            σs_le_eg := by rw [eσs]; exact hσs.trans ((min_le_right _ _).trans (min_le_left _ _))
            σs_lt_θs := by
              rw [eσs, eβ₂, eΔ]
              have h := hσs.trans ((min_le_right _ _).trans (min_le_right _ _))
              have : 0 < χ.θs P.β₂ P.Δ ^ 2 := by positivity
              have e : χ.θs P.β₂ P.Δ ^ 2 / (2 * 10 ^ 6) = χ.θs P.β₂ P.Δ ^ 2 / 10 ^ 6 / 2 := by ring
              have : 0 < χ.θs P.β₂ P.Δ ^ 2 / 10 ^ 6 := by positivity
              linarith
            vs_le_θt := by rw [evs]; exact hvs.trans (min_le_left _ _)
            vs_lt_eg := by
              rw [evs]
              have h := hvs.trans ((min_le_right _ _).trans (min_le_left _ _))
              have : 0 < χ.eg 1 / (20 * egpGraphConst) := by positivity
              linarith
            vs_lt_θs := by
              rw [evs, eβ₂, eΔ]
              have h := hvs.trans ((min_le_right _ _).trans (min_le_right _ _))
              linarith
            three_ν_le_β₃ := by rw [eβ, P.β_three]; exact χ.three_ν_le
            β₁_le_η₁ := by rw [eβ, eβ₂, eΔ]; exact hβ₁.trans (min_le_left _ _)
            β₁_le_η₀₁ := by
              rw [eβ, eβ₂, eΔ]; exact hβ₁.trans ((min_le_right _ _).trans (min_le_left _ _))
            β₁_le_η₀₂ := by
              rw [eβ, eβ₂, eΔ]; exact hβ₁.trans ((min_le_right _ _).trans (min_le_right _ _))
            ζ_le_θt := by rw [eζ]; exact hζ.trans (min_le_left _ _)
            ζ_le_eg := by rw [eζ]; exact hζ.trans ((min_le_right _ _).trans (min_le_left _ _))
            ζ_le_Δ := by rw [eζ, eΔ]; exact hζΔ
            ζ_lt_θs := by
              rw [eζ, eβ₂, eΔ]
              have h := hζ.trans ((min_le_right _ _).trans ((min_le_right _ _).trans
                (min_le_right _ _)))
              have : 0 < χ.θs P.β₂ P.Δ ^ 2 / 10 ^ 6 := by positivity
              have e : χ.θs P.β₂ P.Δ ^ 2 / (2 * 10 ^ 6) = χ.θs P.β₂ P.Δ ^ 2 / 10 ^ 6 / 2 := by ring
              linarith
            cap_le_θt := by rw [ecap]; exact hcap.trans (min_le_left _ _)
            cap_le_eg := by
              rw [ecap, eΔ]; exact hcap.trans ((min_le_right _ _).trans (min_le_left _ _))
            cap_le_θs := by
              rw [ecap, eβ₂, eΔ]; exact hcap.trans ((min_le_right _ _).trans (min_le_right _ _))
            T_ge_Δ := by rw [eT, eΔ]; exact P.T_Δ
            ϑmin_lt := by
              rw [hϑ0, hϑ1, hϑ2, hϑmin]
              exact hθ₀1
            ϑmin_le := by
              rw [hϑ0, hϑ1, hϑ2, hϑmin]
              exact hθ₀ϑ }, hEϑ, P, hMR, h3, hEP⟩

/-- **The combined staged early choice with the reservation**
(`exists_boundaryEarlyOverXBA_staged_BSTD2` with the conjunct `3 β_c ≤ β 2` of the staged
prefix). -/
theorem exists_boundaryEarlyOverXBA_staged_three_RNUM (Θ : BoundaryProducerThresholdsBA_BSTD2)
    {θ ν : ℝ} (hθ : 0 < θ) (hθ1 : θ < 1 / 100)
    (hν : 3 * ν ≤ threeSplittingExclusionThreshold.{0, 0}) (χ : BoundaryChainThresholds_BSTD2)
    (hθχ : θ ≤ χ.ϑ₀) (Rq : C14StagedRequestsSTG) :
    ∃ E : BoundaryEarlyOverXBA_BSTD2 Θ θ ν χ, E.ϑmin = θ ∧ ∃ P : C14PreFinal,
      Rq.toC14.Meets P ∧ 3 * P.βc ≤ P.β 2 ∧
        E.toBoundaryEarlyParams_BSTD1 = P.toBdryParams_BSTD1 := by
  obtain ⟨E, hEϑ, P, hM', h3, hEP⟩ := exists_boundaryEarlyOverX_staged_layer_three_RNUM
    Θ.toBoundaryProducerThresholds_BSTD1 χ hθ hθ1 hθχ ((baRequests_BSTD2 Θ θ hθ).inf Rq)
  rw [C14StagedRequestsSTG.toC14_inf] at hM'
  have hM : (baRequests_BSTD2 Θ θ hθ).toC14.Meets P := C14StagedRequests.Meets.inf_left hM'
  have hMR : Rq.toC14.Meets P := C14StagedRequests.Meets.inf_right hM'
  have eγ : E.γ = P.γ := congrArg (fun q : BoundaryEarlyParams_BSTD1 => q.γ) hEP
  have eβ₂ : E.β₂ = P.β₂ := congrArg (fun q : BoundaryEarlyParams_BSTD1 => q.β₂) hEP
  have eΔ : E.Δ = P.Δ := congrArg (fun q : BoundaryEarlyParams_BSTD1 => q.Δ) hEP
  have eσc : E.σc = P.σc := congrArg (fun q : BoundaryEarlyParams_BSTD1 => q.σc) hEP
  have eμ : E.μ = P.μ := congrArg (fun q : BoundaryEarlyParams_BSTD1 => q.μ) hEP
  have eb : E.b = P.b := congrArg (fun q : BoundaryEarlyParams_BSTD1 => q.b) hEP
  have eσs : E.σs = P.σs := congrArg (fun q : BoundaryEarlyParams_BSTD1 => q.σs) hEP
  have evs : E.vs = P.vs := congrArg (fun q : BoundaryEarlyParams_BSTD1 => q.vs) hEP
  have eβ : E.β = P.β := congrArg (fun q : BoundaryEarlyParams_BSTD1 => q.β) hEP
  have esc : E.toBdryParamsScale_BSTD1 =
      C14PreScale.toBdryParamsScale_BSTD2 P.toC14PreScale :=
    congrArg (fun q : BoundaryEarlyParams_BSTD1 => q.toBdryParamsScale_BSTD1) hEP
  have hΔ : 0 < P.Δ := by linarith [P.Δ_gt6]
  -- the requests met by `P`, unfolded
  have hγ : P.γ ≤ θ ^ 2 / 10000000 := hM.γ_le
  have hβ₂ : P.β₂ ≤ min (Θ.σC / 3) (θ ^ 2 / 10000000) := hM.β₂_le
  have hσc : P.σc ≤ θ ^ 2 / 10000000 := hM.σc_le
  have hμ : P.μ ≤ θ / (4 * P.Δ) := hM.μ_le
  have hb : P.b ≤ min (Θ.SE (C14PreScale.toBdryParamsScale_BSTD2 P.toC14PreScale) / 3)
      (min (1 / (2 * (421 * P.Δ + 1))) (θ ^ 2 / 10000000)) := hM.b_le
  have hσs : P.σs ≤ θ ^ 2 / 10000000 := hM.σs_le
  have hvs : P.vs ≤ θ / 4 := hM.vs_le
  have hβ₁ : P.β 1 ≤ min (Θ.ηC / 2)
      (min (Θ.HE (C14PreScale.toBdryParamsScale_BSTD2 P.toC14PreScale) / 2)
        (min (Θ.HS (C14PreScale.toBdryParamsScale_BSTD2 P.toC14PreScale) / 2)
          (min (Θ.SS (C14PreScale.toBdryParamsScale_BSTD2 P.toC14PreScale) / 3)
            (min (1 / (2 * (1950002 * P.Δ + 1))) (θ ^ 2 / 10000000))))) := hM.β₁_le
  have hβ₁pos : 0 < P.β 1 := by rw [← eβ]; exact E.β₁_pos
  have hβ₁lt : P.β 1 < 1 := by rw [← eβ]; exact E.β₁_lt
  have hβ₁m : P.β 1 * (2 * (1950002 * P.Δ + 1)) ≤ 1 := by
    have h := hβ₁.trans ((min_le_right _ _).trans ((min_le_right _ _).trans
      ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _)))))
    rwa [le_div_iff₀ (by positivity)] at h
  refine ⟨{ E with
      γ_le_θ := by rw [eγ]; exact hγ
      three_β₂_le_σC := by rw [eβ₂]; linarith [hβ₂.trans (min_le_left _ _)]
      β₂_le_θ := by rw [eβ₂]; exact hβ₂.trans (min_le_right _ _)
      μΔ_le_θ := by
        rw [eμ, eΔ]
        have h := mul_le_mul_of_nonneg_right hμ hΔ.le
        have e : θ / (4 * P.Δ) * P.Δ = θ / 4 := by field_simp
        linarith
      σc_le_θ := by rw [eσc]; exact hσc
      three_b_le_σE := by rw [esc, eb]; linarith [hb.trans (min_le_left _ _)]
      b_mul_le := by
        rw [eb, eΔ]
        have h := hb.trans ((min_le_right _ _).trans (min_le_left _ _))
        rwa [le_div_iff₀ (by positivity)] at h
      b_le_θ := by rw [eb]; exact hb.trans ((min_le_right _ _).trans (min_le_right _ _))
      vs_le_θ := by rw [evs]; exact hvs
      σs_le_θ := by rw [eσs]; exact hσs
      three_ν_le := by rw [eβ, P.β_three]; exact hν
      two_β₁_le_ηC := by rw [eβ]; linarith [hβ₁.trans (min_le_left _ _)]
      two_β₁_le_ηE := by
        rw [esc, eβ]; linarith [hβ₁.trans ((min_le_right _ _).trans (min_le_left _ _))]
      two_β₁_le_ηS := by
        rw [esc, eβ]
        linarith [hβ₁.trans ((min_le_right _ _).trans ((min_le_right _ _).trans
          (min_le_left _ _)))]
      Δβ₁_lt := by
        rw [eΔ, eβ]
        have h3 : P.β 1 ^ 3 ≤ P.β 1 := pow_le_of_le_one hβ₁pos.le hβ₁lt.le (by norm_num)
        have e6 : P.β 1 * (2 * (1950002 * P.Δ + 1)) =
            1000000 * P.Δ * P.β 1 + P.β 1 * (2900004 * P.Δ + 2) := by ring
        have h6' : 0 < P.β 1 * (2900004 * P.Δ + 2) := by positivity
        have h6 : 1000000 * P.Δ * P.β 1 < P.β 1 * (2 * (1950002 * P.Δ + 1)) := by linarith
        have h7 : 1000000 * P.Δ * P.β 1 ^ 3 ≤ 1000000 * P.Δ * P.β 1 :=
          mul_le_mul_of_nonneg_left h3 (by positivity)
        linarith
      three_β₁_le_σS := by
        rw [esc, eβ]
        linarith [hβ₁.trans ((min_le_right _ _).trans ((min_le_right _ _).trans
          ((min_le_right _ _).trans (min_le_left _ _))))]
      β₁_mul_le := by rw [eβ, eΔ]; exact hβ₁m
      β₁_le_θ := by
        rw [eβ]
        exact hβ₁.trans ((min_le_right _ _).trans ((min_le_right _ _).trans
          ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_right _ _))))) }, ?_,
    P, hMR, h3, hEP⟩
  change min (E.ϑ 0) (min (E.ϑ 1) (E.ϑ 2)) = θ
  rw [hEϑ]
  simp

/-- **The stored-CHOICE early choice with `3 β_c ≤ β₂`** (`exists_boundaryEarlyWithChoice_of_BSTD2`
with the staged reservation re-exported): the early choice's own `β_c` and `β₂`. -/
theorem exists_boundaryEarlyWithChoice_of_three_RNUM (K : ℕ) (hK : 10 ≤ K) (A : ℝ → ℝ)
    (hA : ∀ w, 0 < w → w < euclideanThreeUnitBallVolume → 0 < A w) {Ch : Type}
    (egOf : Ch → Fin 3 → ℝ) (c : Ch) (χ : BoundaryChainThresholds_BSTD2) (heg : χ.eg = egOf c)
    {θ νBA : ℝ} (hθ : 0 < θ) (hθ1 : θ < 1 / 100) (hθχ : θ ≤ χ.ϑ₀) (hν : 0 < νBA)
    (hν1 : νBA < 1 / 1000000) (hν3 : 3 * νBA ≤ threeSplittingExclusionThreshold.{0, 0})
    (Rq : C14StagedRequestsSTG) :
    ∃ EW : BoundaryEarlyWithChoice_BSTD2 K hK A hA egOf, EW.choice = c ∧ EW.χ = χ ∧ EW.θ = θ ∧
      EW.νBA = νBA ∧ 3 * EW.early.βc ≤ EW.early.β₂ ∧ ∃ P : C14PreFinal, Rq.toC14.Meets P ∧
        EW.early.toBoundaryEarlyParams_BSTD1 = P.toBdryParams_BSTD1 := by
  obtain ⟨E, hEϑ, P, hM, h3, hEP⟩ := exists_boundaryEarlyOverXBA_staged_three_RNUM
    (bdryThresholdsBA_BSTD2 K hK A hA θ νBA) hθ hθ1 hν3 χ hθχ Rq
  have eβc : E.βc = P.βc := congrArg (fun q : BoundaryEarlyParams_BSTD1 => q.βc) hEP
  have eβ₂ : E.β₂ = P.β₂ := congrArg (fun q : BoundaryEarlyParams_BSTD1 => q.β₂) hEP
  refine ⟨⟨c, χ, heg, θ, hθ, hθ1, hθχ, νBA, hν, hν1, E, hEϑ⟩, rfl, rfl, rfl, rfl, ?_, P, hM, hEP⟩
  change 3 * E.βc ≤ E.β₂
  rw [eβc, eβ₂, ← P.β_two]
  exact h3

/-- **The stored-CHOICE early choice with `3 β_c ≤ β₂` for every choice and CHI record** (the layer
`θ = min(1/200, ϑ₀)`, `ν_BA = min(ν, 1/(2·10⁶))` of `exists_boundaryEarlyWithChoice_BSTD2`). -/
theorem exists_boundaryEarlyWithChoice_three_RNUM (K : ℕ) (hK : 10 ≤ K) (A : ℝ → ℝ)
    (hA : ∀ w, 0 < w → w < euclideanThreeUnitBallVolume → 0 < A w) {Ch : Type}
    (egOf : Ch → Fin 3 → ℝ) (c : Ch) (χ : BoundaryChainThresholds_BSTD2) (heg : χ.eg = egOf c) :
    ∃ EW : BoundaryEarlyWithChoice_BSTD2 K hK A hA egOf, EW.choice = c ∧ EW.χ = χ ∧
      3 * EW.early.βc ≤ EW.early.β₂ := by
  have hν3 : 3 * min χ.ν (1 / 2000000) ≤ threeSplittingExclusionThreshold.{0, 0} := by
    linarith [χ.three_ν_le, min_le_left χ.ν (1 / 2000000)]
  obtain ⟨EW, hc, hχ, -, -, h3, -⟩ := exists_boundaryEarlyWithChoice_of_three_RNUM K hK A hA egOf c
    χ heg (θ := min (1 / 200) χ.ϑ₀) (νBA := min χ.ν (1 / 2000000))
    (lt_min (by norm_num) χ.ϑ₀_pos) ((min_le_left _ _).trans_lt (by norm_num)) (min_le_right _ _)
    (lt_min χ.ν_pos (by norm_num)) ((min_le_right _ _).trans_lt (by norm_num)) hν3
    C14StagedRequestsSTG.trivial
  exact ⟨EW, hc, hχ, h3⟩

end DifferentialGeometry.Geometry.Collapse
