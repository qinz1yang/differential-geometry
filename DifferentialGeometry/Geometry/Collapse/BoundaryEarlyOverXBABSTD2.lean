import DifferentialGeometry.Geometry.Collapse.BoundaryEarlyThresholdsBABSTD2
import DifferentialGeometry.Geometry.Collapse.BoundaryEarlyStagedGenericBSTD2

/-!
# The combined early choice (lane BSTD2, G2 module G)

The extended register's clauses AND the joint (BA) producer's.

Review 69 (D69-3) and lane BSTD2's order finding: the (BA) certificates of a `BoundarySupply` come
only from the joint producer `lc88_boundary_packets_BFRZ_BA_BIND`, which fixes the (BA) error `θ`
and `ν` BEFORE its thresholds and adds conditions on the early parameters that the record of lane
BSTG-D1 cannot carry (`γ ≤ θ²/10⁷` is read before every threshold; `μΔ ≤ θ/4`, `vs ≤ θ/4`,
`σs ≤ θ²/10⁷`, `3ν ≤ β 3` have no threshold slot). So the early choice of the stored CHOICE is the
COMBINED one:

* `BoundaryEarlyOverXBA_BSTD2 Θ θ ν χ`: extends BOTH the joint early choice
  `BoundaryEarlyOverBA_BSTD2 Θ θ ν` and the extended early choice
  `BoundaryEarlyOverX_BSTD2 Θ.toBoundaryProducerThresholds_BSTD1 χ` (one early choice of lane
  BSTG-D1 underneath; every clause on the node where it is read).
* `C14PreScale.toBdryParamsScale_BSTD2`, `baRequests_BSTD2 Θ θ hθ`: the joint producer's extra
  clauses as STG requests, each read at its prefix (`γ` constant; `β₂` constant; `σc, μ` at
  `C14PreScale`; `b` at `C14PreVol` through the scale parameters; `σs, vs` constant; `β₁` at
  `C14PreSlim` through the scale parameters).
* `exists_boundaryEarlyOverXBA_staged_BSTD2`: for EVERY joint record `Θ`, every `0 < θ < 1/100`
  with `θ ≤ ϑ₀`, every `ν` with `3ν ≤ thr` and every CHI record `χ`, a combined early choice with
  boundary layer `ϑ ≡ θ` (so `ϑ_min = θ`: BCG05's / A2's `θ` and the (BA) error are ONE number),
  its parameters those of one staged prefix meeting any further requests `Rq`.
-/

set_option autoImplicit false

noncomputable section

open Set Function Filter

namespace DifferentialGeometry.Geometry.Collapse

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace

/-- **The combined early choice** over the joint (BA) thresholds `Θ` at the (BA) error `θ` and
`ν`, and the CHI numbers `χ`: ONE early choice of lane BSTG-D1 over the T3B-shaped part of `Θ`
with the joint producer's extra conditions (`BoundaryEarlyOverBA_BSTD2`) and every clause of the
extended register (`BoundaryEarlyOverX_BSTD2`). -/
structure BoundaryEarlyOverXBA_BSTD2 (Θ : BoundaryProducerThresholdsBA_BSTD2) (θ ν : ℝ)
    (χ : BoundaryChainThresholds_BSTD2) extends BoundaryEarlyOverBA_BSTD2 Θ θ ν,
    BoundaryEarlyOverX_BSTD2 Θ.toBoundaryProducerThresholds_BSTD1 χ

/-- The parameters `γ βc γc β₂ Δ` of a staged prefix (read by the joint thresholds
`σE, ηE, σS, ηS`). -/
def C14PreScale.toBdryParamsScale_BSTD2 (p : C14PreScale) : BdryParamsScale_BSTD1 :=
  ⟨⟨p.γ, p.βc, p.γc⟩, p.β₂, p.Δ⟩

/-- **The joint producer's extra clauses as staged requests** (each read at its STG prefix; every
other request trivial): `γ ≤ θ²/10⁷`; `β₂ ≤ min(σC/3, θ²/10⁷)`; `σc ≤ θ²/10⁷`; `μ ≤ θ/(4Δ)`;
`b ≤ min(σE/3, 1/(2(421Δ+1)), θ²/10⁷)`; `σs ≤ θ²/10⁷`; `vs ≤ θ/4`;
`β₁ ≤ min(ηC/2, ηE/2, ηS/2, σS/3, 1/(2(1950002Δ+1)), θ²/10⁷)`. -/
def baRequests_BSTD2 (Θ : BoundaryProducerThresholdsBA_BSTD2) (θ : ℝ) (hθ : 0 < θ) :
    C14StagedRequestsSTG where
  γ _ := θ ^ 2 / 10000000
  γc _ := 1
  βc _ := 1
  β₂ _ := min (Θ.σC / 3) (θ ^ 2 / 10000000)
  Δ _ := 0
  σc _ := θ ^ 2 / 10000000
  ε _ := 1
  μ p := θ / (4 * p.Δ)
  τ _ := 1
  s _ := 1
  b' _ := 1
  s' _ := 1
  Λ _ := 1
  w _ := 1
  b p := min (Θ.SE (C14PreScale.toBdryParamsScale_BSTD2 p.toC14PreScale) / 3)
    (min (1 / (2 * (421 * p.Δ + 1))) (θ ^ 2 / 10000000))
  σs _ := θ ^ 2 / 10000000
  vs _ := θ / 4
  ζ _ := 1
  β₁ p := min (Θ.ηC / 2) (min (Θ.HE (C14PreScale.toBdryParamsScale_BSTD2 p.toC14PreScale) / 2)
    (min (Θ.HS (C14PreScale.toBdryParamsScale_BSTD2 p.toC14PreScale) / 2)
      (min (Θ.SS (C14PreScale.toBdryParamsScale_BSTD2 p.toC14PreScale) / 3)
        (min (1 / (2 * (1950002 * p.Δ + 1))) (θ ^ 2 / 10000000)))))
  cap _ := 1
  T _ := 0
  e _ := 1
  Lmax _ _ := 0
  γ_pos _ := by positivity
  γc_pos _ := one_pos
  βc_pos _ := one_pos
  β₂_pos _ := lt_min (by linarith [Θ.σC_pos]) (by positivity)
  σc_pos _ := by positivity
  ε_pos _ := one_pos
  μ_pos p := by
    have := p.Δ_gt6
    have hΔ : 0 < p.Δ := by linarith
    positivity
  τ_pos _ := one_pos
  s_pos _ := one_pos
  b'_pos _ := one_pos
  s'_pos _ := one_pos
  Λ_pos _ := one_pos
  w_pos _ := one_pos
  b_pos p := by
    have := p.Δ_gt6
    have hΔ : 0 < p.Δ := by linarith
    have := Θ.SE_pos (C14PreScale.toBdryParamsScale_BSTD2 p.toC14PreScale)
    exact lt_min (by positivity) (lt_min (by positivity) (by positivity))
  σs_pos _ := by positivity
  vs_pos _ := by positivity
  ζ_pos _ := one_pos
  β₁_pos p := by
    have := p.Δ_gt6
    have hΔ : 0 < p.Δ := by linarith
    have := Θ.ηC_pos
    have := Θ.HE_pos (C14PreScale.toBdryParamsScale_BSTD2 p.toC14PreScale)
    have := Θ.HS_pos (C14PreScale.toBdryParamsScale_BSTD2 p.toC14PreScale)
    have := Θ.SS_pos (C14PreScale.toBdryParamsScale_BSTD2 p.toC14PreScale)
    exact lt_min (by positivity) (lt_min (by positivity) (lt_min (by positivity)
      (lt_min (by positivity) (lt_min (by positivity) (by positivity)))))
  cap_pos _ := one_pos
  e_pos _ := one_pos

/-- **The combined early choices are inhabited, with the boundary layer at the (BA) error**: for
every joint record `Θ`, every `0 < θ < 1/100` with `θ ≤ ϑ₀`, every `ν` with `3ν ≤ thr`, every CHI
record `χ` and every further request record `Rq`, there is a combined early choice with
`ϑ_min = θ` whose parameters are those of ONE staged prefix `P` meeting `Rq` (lane BSTD2's staged
inhabitant over `Θ`'s T3B-shaped part at the requests `baRequests_BSTD2 ⊓ Rq` and the layer
`ϑ ≡ θ`; the STG prefix gives `β 3 = thr ≥ 3ν`). -/
theorem exists_boundaryEarlyOverXBA_staged_BSTD2 (Θ : BoundaryProducerThresholdsBA_BSTD2)
    {θ ν : ℝ} (hθ : 0 < θ) (hθ1 : θ < 1 / 100)
    (hν : 3 * ν ≤ threeSplittingExclusionThreshold.{0, 0}) (χ : BoundaryChainThresholds_BSTD2)
    (hθχ : θ ≤ χ.ϑ₀) (Rq : C14StagedRequestsSTG) :
    ∃ E : BoundaryEarlyOverXBA_BSTD2 Θ θ ν χ, E.ϑmin = θ ∧ ∃ P : C14PreFinal,
      Rq.toC14.Meets P ∧ E.toBoundaryEarlyParams_BSTD1 = P.toBdryParams_BSTD1 := by
  obtain ⟨E, hEϑ, P, hM', hEP⟩ := exists_boundaryEarlyOverX_staged_layer_BSTD2
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
    P, hMR, hEP⟩
  change min (E.ϑ 0) (min (E.ϑ 1) (E.ϑ 2)) = θ
  rw [hEϑ]
  simp

end DifferentialGeometry.Geometry.Collapse
