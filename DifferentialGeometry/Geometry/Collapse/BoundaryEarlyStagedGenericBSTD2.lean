import DifferentialGeometry.Geometry.Collapse.BoundaryRegisterExtBSTD2

/-!
# Staged inhabitants over ANY threshold record (lane BSTD2, G2-pre)

Lane BSTG-D1's staged inhabitant of the early choices (`exists_boundaryEarlyChoices_staged_BSTD1`)
and lane BSTD2's inhabitant of the extended early choices (`nonempty_boundaryEarlyChoicesX_BSTD2`)
are stated over the exported T3B-BFRZ thresholds; their proofs use only the threshold chain
`BoundaryProducerThresholds_BSTD1.chain_BSTD1` of the record. Here they are restated for ANY record
`Θ` (in particular the T3B-shaped part of the joint (BA) thresholds), the extended one meeting a
further request record:

* `exists_boundaryEarlyOver_staged_BSTD2 Θ t ϑ … Rq` (proof of BSTG-D1's, `Θ` free);
* `exists_boundaryEarlyOverX_staged_layer_BSTD2 Θ χ θ₀ … Rq` (proof of BSTD2 G1's, requests
  `chiRequests_BSTD2 χ ⊓ Rq`, the early boundary layer `ϑ ≡ θ₀` for any `0 < θ₀ < 1/100`,
  `θ₀ ≤ ϑ₀`: a number fixed before the thresholds, e.g. the (BA) error);
  `exists_boundaryEarlyOverX_staged_BSTD2 Θ χ Rq` (the layer `min(1/200, ϑ₀)`).
-/

set_option autoImplicit false

noncomputable section

open Set Function Metric Bundle Manifold Filter
open scoped ContDiff Manifold Topology ENNReal

namespace DifferentialGeometry.Geometry.Collapse

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace

/-- **Staged inhabitants of the early choices over ANY threshold record `Θ`** (lane BSTG-D1's
`exists_boundaryEarlyChoices_staged_BSTD1` with `Θ` free): for every early tolerance
record `t`, every early boundary layer (`ϑ`, `c₃ ≥ 0`, `P_* ≥ 1`, `N ≥ N_TCP + 1`) and every
interior request record `Rq`, there is an early choice with exactly this layer whose parameters are
those of ONE admissible staged prefix `P` meeting `Rq` (each request at its STG prefix) with
`3βc ≤ β 2`. -/
theorem exists_boundaryEarlyOver_staged_BSTD2 (Θ : BoundaryProducerThresholds_BSTD1) (t : C14Tol)
    (ϑ : Fin 3 → ℝ) (hϑ : ∀ j, 0 < ϑ j) (c₃ : ℝ) (hc₃ : 0 ≤ c₃) (Pstar : ℝ) (hP : 1 ≤ Pstar)
    (N : ℕ) (hN : tcp01SupportBound + 1 ≤ N) (Rq : C14StagedRequestsSTG) :
    ∃ E : BoundaryEarlyOver_BSTD1 Θ, E.ϑ = ϑ ∧ E.c₃ = c₃ ∧ E.Pstar = Pstar ∧ E.N = N ∧
      ∃ P : C14PreFinal, P.toC14Tol = t ∧ Rq.toC14.Meets P ∧ 3 * P.βc ≤ P.β 2 ∧
        E.toBoundaryEarlyParams_BSTD1 = P.toBdryParams_BSTD1 := by
  obtain ⟨a₂, ha₂e⟩ : ∃ a₂ : ℝ, Θ.a₂ = a₂ := ⟨_, rfl⟩
  have ha₂ : 0 < a₂ := ha₂e ▸ Θ.a₂_pos
  have h0 := Θ.chain_BSTD1
  rw [ha₂e] at h0
  obtain ⟨p1, rfl, rfl, h1γ, e1, h⟩ :=
    c14_stage_circ_FAM2b t ha₂ ((Rq.withBdryCaps_BSTG (ϑ 2) (hϑ 2)).γ_pos t) h0
  obtain ⟨p2, rfl, h2βc, h2γc, e2σ, e2Δ, h⟩ := c14_stage_collar_STG p1
    (fun g => min ((Rq.withBdryCaps_BSTG (ϑ 2) (hϑ 2)).βc g.toC14PreCirc)
      (c14β₂Value_STG (Rq.withBdryCaps_BSTG (ϑ 2) (hϑ 2)) g / 3))
    (fun g => lt_min ((Rq.withBdryCaps_BSTG (ϑ 2) (hϑ 2)).βc_pos _)
      (div_pos (c14β₂Value_pos_STG _ g) zero_lt_three))
    ((Rq.withBdryCaps_BSTG (ϑ 2) (hϑ 2)).γc_pos p1) h
  have h2 : p2.βc ≤ min p2.β₀ (min ((Rq.withBdryCaps_BSTG (ϑ 2) (hϑ 2)).β₂ p2.toGc_STG)
      (min (1 / 10000000) (p2.γT / 20))) / 3 :=
    h2βc.trans (min_le_right _ _)
  obtain ⟨p3, rfl, h3β₂, h3v, h⟩ :=
    c14_stage_excl_STG p2 ((Rq.withBdryCaps_BSTG (ϑ 2) (hϑ 2)).β₂_pos p2.toGc_STG) h
  have h3βc : 3 * p3.βc ≤ p3.β₂ := by
    rw [h3v]
    linarith
  obtain ⟨p4, rfl, h4Δ, e4τ, e4bc, h⟩ :=
    c14_stage_scale_FAM2b p3 ((Rq.withBdryCaps_BSTG (ϑ 2) (hϑ 2)).Δ p3) h
  obtain ⟨p5, rfl, h5σc, h5ε, h5μ, h5τ, h5s, h5b', h5s', e5a, e5b, h⟩ := c14_stage_edge_FAM2b p4
    ((Rq.withBdryCaps_BSTG (ϑ 2) (hϑ 2)).σc_pos p4) ((Rq.withBdryCaps_BSTG (ϑ 2) (hϑ 2)).ε_pos p4)
    ((Rq.withBdryCaps_BSTG (ϑ 2) (hϑ 2)).μ_pos p4) ((Rq.withBdryCaps_BSTG (ϑ 2) (hϑ 2)).τ_pos p4)
    ((Rq.withBdryCaps_BSTG (ϑ 2) (hϑ 2)).s_pos p4) ((Rq.withBdryCaps_BSTG (ϑ 2) (hϑ 2)).b'_pos p4)
    ((Rq.withBdryCaps_BSTG (ϑ 2) (hϑ 2)).s'_pos p4) h
  obtain ⟨p6, rfl, h6Λ, e6w, h⟩ :=
    c14_stage_lip_FAM2b p5 ((Rq.withBdryCaps_BSTG (ϑ 2) (hϑ 2)).Λ_pos p5) h
  obtain ⟨p7, rfl, h7w, e7bd, h⟩ :=
    c14_stage_vol_FAM2b p6 ((Rq.withBdryCaps_BSTG (ϑ 2) (hϑ 2)).w_pos p6) h
  obtain ⟨p8, rfl, h8b, h⟩ :=
    c14_stage_split_FAM2b p7 ((Rq.withBdryCaps_BSTG (ϑ 2) (hϑ 2)).b_pos p7) h
  obtain ⟨p9, rfl, h9σs, h9vs, e9b, h⟩ := c14_stage_slim_FAM2b p8
    ((Rq.withBdryCaps_BSTG (ϑ 2) (hϑ 2)).σs_pos p8) ((Rq.withBdryCaps_BSTG (ϑ 2) (hϑ 2)).vs_pos p8)
    h
  obtain ⟨p10, rfl, h10ζ, h10β, h⟩ := c14_stage_beta_FAM2b p9
    ((Rq.withBdryCaps_BSTG (ϑ 2) (hϑ 2)).ζ_pos p9) ((Rq.withBdryCaps_BSTG (ϑ 2) (hϑ 2)).β₁_pos p9)
    h
  obtain ⟨p11, rfl, h11cap, e11r, e11d, e11z⟩ :=
    c14_stage_zero_dep_BSTD1 p10 ((Rq.withBdryCaps_BSTG (ϑ 2) (hϑ 2)).cap_pos p10) h
  obtain ⟨P, rfl, h12T, h12e, -⟩ := c14_stage_final_FAM2b p11
    ((Rq.withBdryCaps_BSTG (ϑ 2) (hϑ 2)).T p11) ((Rq.withBdryCaps_BSTG (ϑ 2) (hϑ 2)).e_pos p11)
    (Q := fun _ _ => True) (fun _ _ _ _ _ _ => trivial)
  have hM : (Rq.withBdryCaps_BSTG (ϑ 2) (hϑ 2)).toC14.Meets P :=
    ⟨h1γ, h2γc, h2βc.trans (min_le_left _ _), h3β₂, h4Δ, h5σc, h5ε, h5μ, h5τ, h5s, h5b', h5s',
      h6Λ, h7w, h8b, h9σs, h9vs, h10ζ, h10β, h11cap, h12T, h12e⟩
  obtain ⟨hMR, hw2, hvs8⟩ := C14StagedRequestsSTG.meets_of_withBdryCaps_BSTG hM
  have hcap := boundaryVolumeCap_pos
  have hϑ2 := hϑ 2
  refine ⟨{ toBoundaryEarlyParams_BSTD1 := P.toBdryParams_BSTD1
            γ_pos := P.γ_pos
            γ_lt := P.γ_lt
            βc_pos := P.βc_pos
            βc_lt := P.βc_lt
            γc_pos := P.γc_pos
            γc_lt := P.γc_lt
            β₂_pos := P.β₂_pos
            β₂_le := P.β₂_le.trans_eq e1
            β₂_lt := P.β₂_lt
            Δ_gt := P.Δ_gt
            Δ_ge := e2Δ.symm.trans_le P.Δ₀_le
            σc_pos := P.σc_pos
            σc_le := P.σc_le.trans_eq e2σ
            σc_lt := P.σc_lt
            ε_pos := P.ε_pos
            ε_lt := P.ε_lt
            μ_pos := P.μ_pos
            μ_le := P.μ_le
            τ_pos := P.τ_pos
            τ_le := P.τ_le.trans_eq e4τ
            τ_sqrt := P.τ_sqrt
            ε_le8 := P.ε_le8
            μ_le8 := P.μ_le8
            s_pos := P.s_pos
            s_lt := P.s_lt
            s_lt_b' := P.s_lt_b'
            s_lt_s' := P.s_lt_s'
            b'_lt := P.b'_lt
            s'_lt := P.s'_lt
            b'_lt_τ := P.b'_lt_τ
            s'_lt_τ := P.s'_lt_τ
            σ_pos := P.σ_pos
            σ_le_a₂ := P.σ_le_a₂.trans_eq ha₂e.symm
            σ_le_thr := P.σ_le_thr
            σ_le_a₀ := P.σ_le_a₀.trans_eq e5a
            Λ_pos := P.Λ_pos
            Λ_c1 := P.Λ_c1
            Λ_c2 := P.Λ_c2
            Λ_c3 := P.Λ_c3
            budget := P.budget
            Λ_c5 := P.Λ_c5
            Λ_c6 := P.Λ_c6
            w_pos := P.w_pos
            w_lt := P.w_lt.trans_eq e6w
            w_lt_pi := P.w_lt_pi
            b_pos := P.b_pos
            b_lt_s := P.b_lt_s
            b_lt_bc₀ := P.b_lt_bc₀.trans_eq e4bc
            b_lt_b₁ := P.b_lt_b₁.trans_eq e5b
            b_inv := P.b_inv
            b_lt_bd₀ := P.b_lt_bd₀.trans_eq e7bd
            σs_pos := P.σs_pos
            σs_le := P.σs_le
            vs_pos := P.vs_pos
            β_two := P.β_two
            β₁_pos := P.β₁_pos
            β₁_lt_b₀ := P.β₁_lt_b₀.trans_eq e9b
            β₁_lt := P.β₁_lt
            β_three := P.β_three.le
            β₁_lt_ζ := P.β₁_lt_ζ
            ζ_lt := P.ζ_lt
            cap_pos := P.cap_pos
            T_pos := P.T_pos
            T_ge := (mul_le_mul_of_nonneg_left e11z.symm.le (by norm_num)).trans P.T_Λz
            e_pos := P.e_pos
            e_lt := P.e_lt
            ϑ := ϑ
            ϑ_pos := hϑ
            c₃ := c₃
            c₃_nonneg := hc₃
            Pstar := Pstar
            one_le_Pstar := hP
            N := N
            N_ge := hN
            w_lt_cap := hw2.trans_lt (half_lt_self hcap)
            vs_lt_ϑ := hvs8.trans_lt (by linarith) }, rfl, rfl, rfl, rfl, P, rfl, hMR,
    by rw [P.β_two]; exact h3βc, rfl⟩

/-- **Staged inhabitants of the extended early choices over ANY threshold record `Θ`** with the
early boundary layer `ϑ ≡ θ₀` (any `0 < θ₀ < 1/100` with `θ₀ ≤ ϑ₀`), meeting any further request
record `Rq`: lane BSTG-D1's staged inhabitant (here for `Θ` free,
`exists_boundaryEarlyOver_staged_BSTD2`) at the requests `chiRequests_BSTD2 χ ⊓ Rq` and the layer
`ϑ ≡ θ₀` carries every clause of the extension (as `nonempty_boundaryEarlyChoicesX_BSTD2`), and
its prefix meets `Rq`. -/
theorem exists_boundaryEarlyOverX_staged_layer_BSTD2 (Θ : BoundaryProducerThresholds_BSTD1)
    (χ : BoundaryChainThresholds_BSTD2) {θ₀ : ℝ} (hθ₀ : 0 < θ₀) (hθ₀1 : θ₀ < 1 / 100)
    (hθ₀ϑ : θ₀ ≤ χ.ϑ₀) (Rq : C14StagedRequestsSTG) :
    ∃ E : BoundaryEarlyOverX_BSTD2 Θ χ, E.ϑ = (fun _ => θ₀) ∧ ∃ P : C14PreFinal,
      Rq.toC14.Meets P ∧ E.toBoundaryEarlyParams_BSTD1 = P.toBdryParams_BSTD1 := by
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
  obtain ⟨E, hEϑ, -, -, -, P, -, hM', -, hEP⟩ :=
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
              exact hθ₀ϑ }, hEϑ, P, hMR, hEP⟩

/-- **Staged inhabitants of the extended early choices over ANY threshold record `Θ`** (the layer
`ϑ ≡ min(1/200, ϑ₀)`), meeting any further request record `Rq`. -/
theorem exists_boundaryEarlyOverX_staged_BSTD2 (Θ : BoundaryProducerThresholds_BSTD1)
    (χ : BoundaryChainThresholds_BSTD2) (Rq : C14StagedRequestsSTG) :
    ∃ E : BoundaryEarlyOverX_BSTD2 Θ χ, ∃ P : C14PreFinal, Rq.toC14.Meets P ∧
      E.toBoundaryEarlyParams_BSTD1 = P.toBdryParams_BSTD1 := by
  obtain ⟨E, -, P, hM, hEP⟩ := exists_boundaryEarlyOverX_staged_layer_BSTD2 Θ χ
    (θ₀ := min (1 / 200 : ℝ) χ.ϑ₀) (lt_min (by norm_num) χ.ϑ₀_pos)
    ((min_le_left _ _).trans_lt (by norm_num)) (min_le_right _ _) Rq
  exact ⟨E, P, hM, hEP⟩

end DifferentialGeometry.Geometry.Collapse
