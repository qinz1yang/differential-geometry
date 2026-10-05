import DifferentialGeometry.Geometry.Collapse.StaticRegisterV4ChainCaps
import DifferentialGeometry.Geometry.Collapse.StaticRegisterV4ChainJA
import DifferentialGeometry.Geometry.Fibration.ActualStageChainERow

/-!
# Register V4 yields the chain on the ENHANCED planes with (JA), on its OWN stage data

Lane C14-REG-CHAIN (review 66, D66-2 / D66-3 / D66-5; coordinator 12:3x). The re-wiring of
`exists_chainStrategy_RGC` (G2, present FC27 tests) to the enhanced chain object of D66-2:

construction order (same packet, same numeric choice = the register's stage `R.stage`):
enhanced planes `A_j` (lane C14-PLANES' producers `exists_firstStagePlanes_PLN`,
`exists_edgeStagePlanes_PLN`, `exists_slimStagePlanes_PLN` at `(Γ_j, Σ_j, e_j)`) → native outputs
`O_j` whose plane slot IS `A_j.plane` and whose radius is `Σ_jρ ∘ A_j.rsel x₀`
(`ClosedStage.stageOutput_RGC`, from `earlyDataSharedV4_stageOutput_C15`, re-weighted to the PR10
constant `c_w^{(j)} = stageCwAt_V4C R.stage j`) → `Ĉ : Gaf02ChainE` by lane C14-GAF8's kernel
assembler `gaf02_chainE_mk_GAF8` (rough data: TCP05 / EGP06 / SGP04 at `e_j` and the register's
CHOICE evidence `ClosedStage.choice_RGC`) → `Ĉ.withRegisterJA_RGC` : `Gaf02ChainEJA` with the
register's early target `cadj = registerCadj_RGC K` (GAF01's (JA), lane C14-GAF-C's record).
No independent `gaf02_chainE_row_GAF8` / GAF01 existence call is spliced to the register.

The thresholds of the planes producers and of the three rough-graph rows are merged by `min`
(upper slots) and `max` (lower slots) and placed with the SAME cap layer as G2
(`ClosedThresholdsV4.withChainCaps_RGC`): first planes ⊓ TCP05 at `(st, ν = β₃/3)` (`σ, η₂, γ₀,
η_c, θ`; `η₁` at `Δ`), edge planes ⊓ EGP06 and slim planes ⊓ SGP04 at `(st, Δ, β₂)`. No order
conflict (each threshold is read after its arguments).

* `exists_chainEStrategy_RGC K U`.
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

/-- **Register V4 yields the enhanced chain with (JA)** (see the module header): for every strategy
`U` there is `U'` refining it such that at every register `R` of every strategy below `U'`, on
every packet of the final family at exactly `R`'s values (with `0 ≤ ε_r < ε₀`, `20Λ_z ≤ T₀Low`)
and for every base point `x₀`, there is
`Ĉ : Gaf02ChainEJA P K (Ξ_j(Γ_j)) Γ Σ e c (stageCwAt_V4C R.stage) (registerCadj_RGC K)`,
`Ĉ.x₀ = x₀`, on `R`'s own stage data. -/
theorem exists_chainEStrategy_RGC (K : ℕ) (U : ClosedThresholdsV4 (earlyDataSharedV4 K)) :
    ∃ U' : ClosedThresholdsV4 (earlyDataSharedV4 K), ClosedStrategyRefinesV4 U' U ∧
      ∀ T : ClosedThresholdsV4 (earlyDataSharedV4 K), ClosedStrategyBelowV4 T U' →
      ∀ R : ClosedRegisterV4 (earlyDataSharedV4 K) T,
      ∀ {X : Type} [MetricSpace X] [ChartedSpace E3 X] [IsManifold 𝓘(ℝ, E3) ∞ X]
        [CompactSpace X] {g : SmoothRiemannianMetric 𝓘(ℝ, E3) X}
        {hmetric : ∀ a b : X, riemannianEDistOf g a b = ENNReal.ofReal (dist a b)}
        {ρ : X → ℝ} {hρ : ∀ p, 0 < ρ p} {Kf : ℕ} {δ εr Λz : ℝ}
        (P : LocalChartPacketsC14 X g hmetric ρ hρ R.later.scale.Λ R.β R.later.excl.Δ
          R.later.err.co.qs Kf R.later.err.co.qe R.later.err.bd.μ R.later.split.b R.later.err.s
          R.later.err.wk.b' R.later.err.wk.s' R.later.err.co.ε R.later.circle.γc
          R.later.circle.βc R.later.Lmax R.later.err.bd.τ R.later.circle.γ δ εr
          R.later.err.co.e₀ R.later.split.T₀ R.later.split.V R.later.err.co.ve R.later.err.co.ζ
          Λz),
        0 ≤ εr → εr < R.later.err.co.ε₀ →
        20 * Λz ≤ T.T₀Low R.stage R.later.circle R.later.excl R.later.err R.later.scale
          R.later.split.b R.later.split.β₁ →
        ∀ x₀ : X,
        ∃ C : Gaf02ChainEJA P K (fun j => (earlyDataSharedV4 K).Ξ j (R.stage.Γ j)) R.stage.Γ
            R.stage.Sig R.stage.e R.stage.c (stageCwAt_V4C R.stage) (registerCadj_RGC K),
          C.x₀ = x₀ := by
  classical
  -- first planes (PLANES) at `(Γ₀, Σ₀, e₀, ν)`
  have hfirstP := fun (st : ClosedStage (earlyDataSharedV4 K)) (ν : ℝ) (hν : 0 < ν)
      (hν1 : ν < 1) =>
    exists_firstStagePlanes_PLN (st.chain_ranges_RGC 0).1 (st.chain_ranges_RGC 0).2.1
      (st.chain_ranges_RGC 0).2.2.1 (st.chain_ranges_RGC 0).2.2.2.1
      (st.chain_ranges_RGC 0).2.2.2.2.1 (st.chain_ranges_RGC 0).2.2.2.2.2.1
      (st.chain_ranges_RGC 0).2.2.2.2.2.2.1 (st.chain_ranges_RGC 0).2.2.2.2.2.2.2.1 hν hν1
  choose! σP hσP hσP1 hfirstP' using hfirstP
  choose! η₂P γ₀P ηcP θP hη₂P hγ₀P hηcP hθP hθP1 hrowP using hfirstP'
  choose! η₁P hη₁P hrowP' using hrowP
  -- TCP05 at `(e₀, ν)`
  have hfirstT := fun (st : ClosedStage (earlyDataSharedV4 K)) (ν : ℝ) (hν : 0 < ν)
      (hν1 : ν < 1) =>
    tcp05_row_out_VAL3 (st.chain_ranges_RGC 0).2.2.2.2.2.1
      (st.chain_ranges_RGC 0).2.2.2.2.2.2.1 hν hν1
  choose! σT hσT hσT1 hfirstT' using hfirstT
  choose! η₂T γ₀T ηcT θT hη₂T hγ₀T hηcT hθT hθT1 hrowT using hfirstT'
  choose! η₁T hη₁T hrowT' using hrowT
  -- edge planes and EGP06 at `(Γ₁, Σ₁, e₁, Δ, β₂)`
  have hedgeP := fun (st : ClosedStage (earlyDataSharedV4 K)) (Δ β₂ : ℝ) (hΔ : 1 ≤ Δ)
      (hβ₂ : 0 < β₂) (hβ₂1 : β₂ < 1 / 1000000) =>
    exists_edgeStagePlanes_PLN (Γ := st.Γ 1) (Sg := st.Sig 1) (eg := st.e 1) hΔ hβ₂ hβ₂1
      ⟨(st.chain_ranges_RGC 1).1, (st.chain_ranges_RGC 1).2.1⟩ (st.chain_ranges_RGC 1).2.2.1
      (lt_min (st.chain_ranges_RGC 1).2.2.2.1 (st.chain_ranges_RGC 1).2.2.2.2.1)
      (st.chain_ranges_RGC 1).2.2.2.2.2.1
      (lt_min (st.chain_ranges_RGC 1).2.2.2.2.2.2.1
        (lt_min (st.chain_ranges_RGC 1).2.2.2.2.2.2.2.1
          (st.chain_ranges_RGC 1).2.2.2.2.2.2.2.2.1))
  choose! LcE η₀E hLcE hη₀E hrowE using hedgeP
  have hedgeG := fun (st : ClosedStage (earlyDataSharedV4 K)) (Δ β₂ : ℝ) (hΔ : 1 ≤ Δ)
      (hβ₂ : 0 < β₂) (hβ₂1 : β₂ < 1 / 1000000) =>
    egp06_row_out_VAL3 (eg := st.e 1) hΔ hβ₂ hβ₂1 (st.chain_ranges_RGC 1).2.2.2.2.2.1
      (st.chain_ranges_RGC 1).2.2.2.2.2.2.1
  choose! LcG η₀G hLcG hη₀G hrowG using hedgeG
  -- slim planes and SGP04 at `(Γ₂, Σ₂, e₂, Δ, β₂)`
  have hslimP := fun (st : ClosedStage (earlyDataSharedV4 K)) (Δ β₂ : ℝ) (hΔ : 1 ≤ Δ)
      (hβ₂ : 0 < β₂) (hβ₂1 : β₂ < 1) =>
    exists_slimStagePlanes_PLN (Γ := st.Γ 2) (sg := st.Sig 2) (eg := st.e 2) hΔ hβ₂ hβ₂1
      (st.chain_ranges_RGC 2).1 (st.chain_ranges_RGC 2).2.1 (st.chain_ranges_RGC 2).2.2.1
      (st.chain_ranges_RGC 2).2.2.2.1 (st.chain_ranges_RGC 2).2.2.2.2.1
      (st.chain_ranges_RGC 2).2.2.2.2.2.1 (st.chain_ranges_RGC 2).2.2.2.2.2.2.1
      (st.chain_ranges_RGC 2).2.2.2.2.2.2.2.1
  choose! θS hθS hθS1 LcS η₀S hLcS hη₀S hrowS using hslimP
  have hslimR := fun (st : ClosedStage (earlyDataSharedV4 K)) (Δ β₂ : ℝ) (hΔ : 1 ≤ Δ)
      (hβ₂ : 0 < β₂) (hβ₂1 : β₂ < 1) =>
    sgp04_row_out_VAL3 (eg := st.e 2) hΔ hβ₂ hβ₂1 (st.chain_ranges_RGC 2).2.2.2.2.2.1
      (st.chain_ranges_RGC 2).2.2.2.2.2.2.1
  choose! θR hθR hθR1 LcR η₀R hLcR hη₀R hrowR using hslimR
  refine ⟨U.withChainCaps_RGC (fun st ν => min (σP st ν) (σT st ν))
    (fun st ν => min (η₂P st ν) (η₂T st ν)) (fun st ν => min (γ₀P st ν) (γ₀T st ν))
    (fun st ν => min (ηcP st ν) (ηcT st ν)) (fun st ν => min (θP st ν) (θT st ν))
    (fun st ν Δ => min (η₁P st ν Δ) (η₁T st ν Δ)) (fun st Δ β₂ => max (LcE st Δ β₂) (LcG st Δ β₂))
    (fun st Δ β₂ => min (η₀E st Δ β₂) (η₀G st Δ β₂)) (fun st Δ β₂ => min (θS st Δ β₂) (θR st Δ β₂))
    (fun st Δ β₂ => max (LcS st Δ β₂) (LcR st Δ β₂))
    (fun st Δ β₂ => min (η₀S st Δ β₂) (η₀R st Δ β₂)),
    U.withChainCaps_refines_RGC _ _ _ _ _ _ _ _ _ _ _, ?_⟩
  intro T hT R X _ _ _ _ g hmetric ρ hρ Kf δ εr Λz P hεr0 hεr hΛz x₀
  -- the register's arguments
  have hβ₃ := R.later.β₃_pos
  have hβ₃1 : R.later.excl.β₃ < 1 :=
    R.later.β₃_lt.trans_le (hT.lc18_le.trans (min_le_right _ _))
  have hν : 0 < R.later.excl.β₃ / 3 := by positivity
  have hν1 : R.later.excl.β₃ / 3 < 1 := by linarith
  have hΔ0 := R.later.Δ_pos_VAL6
  have hΔbig : 10 ^ 6 < R.later.excl.Δ := (le_max_left _ _).trans_lt R.later.Δ_gt
  have hΔ1200 : 1200 ≤ R.later.excl.Δ := by linarith
  have hΔ1 : 1 ≤ R.later.excl.Δ := by linarith
  have hβ₂ := R.later.β₂_pos
  have hβ₂a : R.later.excl.β₂ < 1 / 1000000 := by
    have := R.later.β₂_lt_audit_VAL6
    norm_num at this ⊢
    exact this
  have hβ₂1 : R.later.excl.β₂ < 1 := by linarith
  -- the merged thresholds at the register
  have hθm : 0 < min (θP R.stage (R.later.excl.β₃ / 3)) (θT R.stage (R.later.excl.β₃ / 3)) :=
    lt_min (hθP R.stage (R.later.excl.β₃ / 3) hν hν1) (hθT R.stage (R.later.excl.β₃ / 3) hν hν1)
  have hθsm : 0 < min (θS R.stage R.later.excl.Δ R.later.excl.β₂) (θR R.stage R.later.excl.Δ
    R.later.excl.β₂) :=
    lt_min (hθS R.stage R.later.excl.Δ R.later.excl.β₂ hΔ1 hβ₂ hβ₂1) (hθR R.stage R.later.excl.Δ
      R.later.excl.β₂ hΔ1 hβ₂ hβ₂1)
  obtain ⟨-, hσβ, hηβ, hγγ, hγcγ, hγc1, hβcη, herr, hμc, hbη, hβ₁η, hσT₀, hL₁T, hL₂T⟩ :=
    ClosedRegisterV4.chainCaps_RGC hT R
      (lt_min (hσP R.stage (R.later.excl.β₃ / 3) hν hν1) (hσT R.stage (R.later.excl.β₃ / 3) hν
        hν1)) (lt_min (hη₂P R.stage (R.later.excl.β₃ / 3) hν hν1) (hη₂T R.stage (R.later.excl.β₃ /
          3) hν hν1))
      (lt_min (hγ₀P R.stage (R.later.excl.β₃ / 3) hν hν1) (hγ₀T R.stage (R.later.excl.β₃ / 3) hν
        hν1)) (lt_min (hηcP R.stage (R.later.excl.β₃ / 3) hν hν1) (hηcT R.stage (R.later.excl.β₃ /
          3) hν hν1))
      hθm (lt_min (hη₁P R.stage (R.later.excl.β₃ / 3) hν hν1 R.later.excl.Δ hΔ1200) (hη₁T R.stage
        (R.later.excl.β₃ / 3) hν hν1 R.later.excl.Δ hΔ1200))
      (lt_min (hη₀E R.stage R.later.excl.Δ R.later.excl.β₂ hΔ1 hβ₂ hβ₂a) (hη₀G R.stage
        R.later.excl.Δ R.later.excl.β₂ hΔ1 hβ₂ hβ₂a)) hθsm
      (lt_min (hη₀S R.stage R.later.excl.Δ R.later.excl.β₂ hΔ1 hβ₂ hβ₂1) (hη₀R R.stage
        R.later.excl.Δ R.later.excl.β₂ hΔ1 hβ₂ hβ₂1))
  obtain ⟨hqe1, hqeθ, -, hqeE, -, -, -, -, -, -, -⟩ :=
    lt_of_lt_chainErrCap_RGC (herr R.later.err.co.qe (by simp))
  obtain ⟨-, hqsθ, -, hqsE, -, -, -, hqsS, -, -, -⟩ :=
    lt_of_lt_chainErrCap_RGC (herr R.later.err.co.qs (by simp))
  obtain ⟨-, -, hveθ, -, hveE, -, -, -, hveS, -, -⟩ :=
    lt_of_lt_chainErrCap_RGC (herr R.later.err.co.ve (by simp))
  obtain ⟨hε1, -, -, -, -, -, -, -, -, -, -⟩ :=
    lt_of_lt_chainErrCap_RGC (herr R.later.err.co.ε (by simp))
  obtain ⟨-, hζθ, -, hζE, -, hζΔ, -, hζS, -, hζΔ', -⟩ :=
    lt_of_lt_chainErrCap_RGC (herr R.later.err.co.ζ (by simp))
  obtain ⟨-, -, hε₀θ, -, -, -, hε₀E, -, -, -, hε₀S⟩ :=
    lt_of_lt_chainErrCap_RGC (herr R.later.err.co.ε₀ (by simp))
  obtain ⟨hμθ, hμE⟩ := mul_lt_of_lt_chainSectionCap_RGC hΔ0 hμc
  -- the merged `θ`'s against each producer's own
  have hθP' := min_le_left (θP R.stage (R.later.excl.β₃ / 3)) (θT R.stage (R.later.excl.β₃ / 3))
  have hθT' := min_le_right (θP R.stage (R.later.excl.β₃ / 3)) (θT R.stage (R.later.excl.β₃ / 3))
  have hθP2 : min (θP R.stage (R.later.excl.β₃ / 3)) (θT R.stage (R.later.excl.β₃ / 3)) ^ 2 ≤ θP
    R.stage (R.later.excl.β₃ / 3) ^ 2 := pow_le_pow_left₀ hθm.le hθP' 2
  have hθT2 : min (θP R.stage (R.later.excl.β₃ / 3)) (θT R.stage (R.later.excl.β₃ / 3)) ^ 2 ≤ θT
    R.stage (R.later.excl.β₃ / 3) ^ 2 := pow_le_pow_left₀ hθm.le hθT' 2
  have hθS' := min_le_left (θS R.stage R.later.excl.Δ R.later.excl.β₂) (θR R.stage R.later.excl.Δ
    R.later.excl.β₂)
  have hθR' := min_le_right (θS R.stage R.later.excl.Δ R.later.excl.β₂) (θR R.stage R.later.excl.Δ
    R.later.excl.β₂)
  have hθS2 : min (θS R.stage R.later.excl.Δ R.later.excl.β₂) (θR R.stage R.later.excl.Δ
    R.later.excl.β₂) ^ 2 ≤ θS R.stage R.later.excl.Δ R.later.excl.β₂ ^ 2 :=
    pow_le_pow_left₀ hθsm.le hθS' 2
  have hθR2 : min (θS R.stage R.later.excl.Δ R.later.excl.β₂) (θR R.stage R.later.excl.Δ
    R.later.excl.β₂) ^ 2 ≤ θR R.stage R.later.excl.Δ R.later.excl.β₂ ^ 2 :=
    pow_le_pow_left₀ hθsm.le hθR' 2
  have hD : (0 : ℝ) ≤ 100 * (1000000 * R.later.excl.Δ) := by positivity
  have hσPi : (σP R.stage (R.later.excl.β₃ / 3))⁻¹ ≤ (min (σP R.stage (R.later.excl.β₃ / 3)) (σT
    R.stage (R.later.excl.β₃ / 3)))⁻¹ :=
    inv_anti₀ (lt_min (hσP R.stage (R.later.excl.β₃ / 3) hν hν1) (hσT R.stage (R.later.excl.β₃ /
      3) hν hν1)) (min_le_left _ _)
  have hσTi : (σT R.stage (R.later.excl.β₃ / 3))⁻¹ ≤ (min (σP R.stage (R.later.excl.β₃ / 3)) (σT
    R.stage (R.later.excl.β₃ / 3)))⁻¹ :=
    inv_anti₀ (lt_min (hσP R.stage (R.later.excl.β₃ / 3) hν hν1) (hσT R.stage (R.later.excl.β₃ /
      3) hν hν1)) (min_le_right _ _)
  -- register facts used by the producers
  have hΛ : 0 ≤ R.later.scale.Λ := R.later.Λ_pos.le
  have hμ : R.later.err.bd.μ ≤ 1 / 100 := by linarith [R.later.μ_lt_VAL6]
  have hτ : R.later.err.bd.τ ≤ 1 / 100 := by linarith [R.later.τ_lt_VAL6]
  have h4 : 1000000 * R.later.excl.Δ * R.later.scale.Λ < 1 / 100000 := by
    have h := R.later.regScale_L
    unfold closedLongLength at h
    norm_num at h ⊢
    linarith
  have hT₀ : 1600 * (1000000 * R.later.excl.Δ) ≤ R.later.split.T₀ := by
    have h := R.later.longLength_le_T₀_VAL6
    unfold closedLongLength at h
    norm_num at h ⊢
    linarith
  have hTV := R.later.T₀_le_V_VAL6
  have hVL := R.later.Lmax_gt_VAL6
  have hT₀p := R.later.T₀_pos_VAL6
  have hT₀L : R.later.split.T₀ ≤ R.later.Lmax := by linarith
  have h5 : 4 * (10 + 2 * (2000000 * R.later.excl.Δ) + R.later.excl.Δ / 3) ≤ R.later.Lmax := by
    linarith
  have he₀ := R.later.e₀_lt_VAL6
  have hΛzT : 20 * Λz ≤ R.later.split.T₀ := hΛz.trans ((le_max_right _ _).trans R.later.T₀_ge)
  have h31 : 1000 * tcpGraphConst * R.later.excl.Δ * R.later.scale.Λ < R.stage.e 0 := by
    have h := R.later.regScale_e
    have hC : (0 : ℝ) < tcpGraphConst := lt_of_lt_of_le one_pos one_le_tcpGraphConst
    have hC' : (earlyDataSharedV4 K).C 0 = tcpGraphConst := rfl
    rw [hC', lt_div_iff₀ (by positivity)] at h
    linarith
  have hβ3 : 3 * (R.later.excl.β₃ / 3) ≤ R.β 3 := by rw [R.β_three_VAL6]; linarith
  have hβ3' : R.β 3 < 1 := by rw [R.β_three_VAL6]; exact hβ₃1
  have hβ2 : R.β 2 = R.later.excl.β₂ := R.β_two_VAL6
  have hb₁ : R.later.split.b < min (η₁P R.stage (R.later.excl.β₃ / 3) R.later.excl.Δ) (η₁T R.stage
    (R.later.excl.β₃ / 3) R.later.excl.Δ) := hbη.trans_le (min_le_left _ _)
  have hb₀ : R.later.split.b < min (η₀E R.stage R.later.excl.Δ R.later.excl.β₂) (η₀G R.stage
    R.later.excl.Δ R.later.excl.β₂) := hbη.trans_le (min_le_right _ _)
  have hq₁ : R.β 1 < min (η₁P R.stage (R.later.excl.β₃ / 3) R.later.excl.Δ) (η₁T R.stage
    (R.later.excl.β₃ / 3) R.later.excl.Δ) := by
    rw [R.β_one_VAL6]; exact hβ₁η.trans_le (min_le_left _ _)
  have hq₀₁ : R.β 1 < min (η₀E R.stage R.later.excl.Δ R.later.excl.β₂) (η₀G R.stage R.later.excl.Δ
    R.later.excl.β₂) := by
    rw [R.β_one_VAL6]; exact hβ₁η.trans_le ((min_le_right _ _).trans (min_le_left _ _))
  have hq₀₂ : R.β 1 < min (η₀S R.stage R.later.excl.Δ R.later.excl.β₂) (η₀R R.stage R.later.excl.Δ
    R.later.excl.β₂) := by
    rw [R.β_one_VAL6]; exact hβ₁η.trans_le ((min_le_right _ _).trans (min_le_right _ _))
  have hs6 : R.later.err.s < 1 / 1000000 := by
    have := R.later.s_lt_audit_VAL6
    norm_num at this ⊢
    exact this
  have hσTL : (min (σP R.stage (R.later.excl.β₃ / 3)) (σT R.stage (R.later.excl.β₃ / 3)))⁻¹ ≤
    R.later.Lmax := hσT₀.trans hT₀L
  have hLE : max (LcE R.stage R.later.excl.Δ R.later.excl.β₂) (LcG R.stage R.later.excl.Δ
    R.later.excl.β₂) ≤ R.later.Lmax := hL₁T.trans hT₀L
  have hLS : max (LcS R.stage R.later.excl.Δ R.later.excl.β₂) (LcR R.stage R.later.excl.Δ
    R.later.excl.β₂) ≤ R.later.Lmax := hL₂T.trans hT₀L
  have hεrθ : εr < min (θP R.stage (R.later.excl.β₃ / 3)) (θT R.stage (R.later.excl.β₃ / 3)) / 100
    := hεr.trans hε₀θ
  have hεrE := hεr.trans hε₀E
  have hεrS : εr < min (θS R.stage R.later.excl.Δ R.later.excl.β₂) (θR R.stage R.later.excl.Δ
    R.later.excl.β₂) / (100 * (1000000 * R.later.excl.Δ)) := hεr.trans hε₀S
  -- the enhanced planes and the rough-graph rows on `P`
  obtain ⟨A₀⟩ := hrowP' R.stage (R.later.excl.β₃ / 3) hν hν1 R.later.excl.Δ hΔ1200 P hΛ hμ hτ h4
    h5 he₀ hT₀
    R.later.ε_pos.le hε1.le R.later.qe_pos.le (by linarith only [hqeθ, hθP2])
    (by linarith only [hμθ, hθP']) hβ3 hβ3' (by rw [hβ2]; exact hσβ.trans (min_le_left _ _))
    (by rw [hβ2]; exact hηβ.trans (min_le_left _ _)) (hγγ.trans (min_le_left _ _))
    R.later.γc_pos (hγcγ.trans (min_le_left _ _)) (hβcη.trans (min_le_left _ _))
    (hb₁.trans_le (min_le_left _ _)).le (hq₁.trans_le (min_le_left _ _)).le R.later.qs_pos
    (by linarith only [hqsθ, hθP2]) (by linarith only [hveθ, hθP']) R.later.ζ_pos
    (by linarith only [hζθ, hθP2]) (by linarith only [hεrθ, hθP']) hΛzT (hσPi.trans hσTL) h31
  have hT05 := hrowT' R.stage (R.later.excl.β₃ / 3) hν hν1 R.later.excl.Δ hΔ1200 P hΛ hμ hτ h4 h5
    he₀ hT₀
    R.later.ε_pos.le hε1.le R.later.qe_pos.le (by linarith only [hqeθ, hθT2])
    (by linarith only [hμθ, hθT']) hβ3 hβ3' (by rw [hβ2]; exact hσβ.trans (min_le_right _ _))
    (by rw [hβ2]; exact hηβ.trans (min_le_right _ _)) (hγγ.trans (min_le_right _ _))
    R.later.γc_pos (hγcγ.trans (min_le_right _ _)) (hβcη.trans (min_le_right _ _))
    (hb₁.trans_le (min_le_right _ _)).le (hq₁.trans_le (min_le_right _ _)).le R.later.qs_pos
    (by linarith only [hqsθ, hθT2]) (by linarith only [hveθ, hθT']) R.later.ζ_pos
    (by linarith only [hζθ, hθT2]) (by linarith only [hεrθ, hθT']) hΛzT (hσTi.trans hσTL) h31
  obtain ⟨A₁⟩ := hrowE R.stage R.later.excl.Δ R.later.excl.β₂ hΔ1 hβ₂ hβ₂a X g hmetric ρ hρ
    R.later.scale.Λ R.β
    R.later.err.co.qs Kf R.later.err.co.qe R.later.err.bd.μ R.later.split.b R.later.err.s
    R.later.err.wk.b' R.later.err.wk.s' R.later.err.co.ε R.later.circle.γc R.later.circle.βc
    R.later.Lmax R.later.err.bd.τ R.later.circle.γ δ εr R.later.err.co.e₀ R.later.split.T₀
    R.later.split.V R.later.err.co.ve R.later.err.co.ζ Λz P
    (hb₀.trans_le (min_le_left _ _)).le hs6 (hq₀₁.trans_le (min_le_left _ _)).le
    ((le_max_left _ _).trans hLE) hΛ h4 hμ hτ hqeE.le hμE R.later.qs_pos hqsE.le hveE he₀
    hT₀ hΛzT R.later.ζ_pos hζE.le hζΔ.le hεrE
  have hE06 := hrowG R.stage R.later.excl.Δ R.later.excl.β₂ hΔ1 hβ₂ hβ₂a X g hmetric ρ hρ
    R.later.scale.Λ R.β
    R.later.err.co.qs Kf R.later.err.co.qe R.later.err.bd.μ R.later.split.b R.later.err.s
    R.later.err.wk.b' R.later.err.wk.s' R.later.err.co.ε R.later.circle.γc R.later.circle.βc
    R.later.Lmax R.later.err.bd.τ R.later.circle.γ δ εr R.later.err.co.e₀ R.later.split.T₀
    R.later.split.V R.later.err.co.ve R.later.err.co.ζ Λz P.toLocalChartPacketsRVZ
    (hb₀.trans_le (min_le_right _ _)).le hs6 (hq₀₁.trans_le (min_le_right _ _)).le
    ((le_max_right _ _).trans hLE) hΛ h4 hμ hτ hqeE.le hμE R.later.qs_pos hqsE.le hveE he₀
    hT₀ hΛzT R.later.ζ_pos hζE.le hζΔ.le hεrE
  obtain ⟨A₂⟩ := hrowS R.stage R.later.excl.Δ R.later.excl.β₂ hΔ1 hβ₂ hβ₂1 X g hmetric ρ hρ
    R.later.scale.Λ R.β
    R.later.err.co.qs Kf R.later.err.co.qe R.later.err.bd.μ R.later.split.b R.later.err.s
    R.later.err.wk.b' R.later.err.wk.s' R.later.err.co.ε R.later.circle.γc R.later.circle.βc
    R.later.Lmax R.later.err.bd.τ R.later.circle.γ δ εr R.later.err.co.e₀ R.later.split.T₀
    R.later.split.V R.later.err.co.ve R.later.err.co.ζ Λz P
    hβ2 (hq₀₂.trans_le (min_le_left _ _)).le ((le_max_left _ _).trans hLS) hΛ h4 he₀ hT₀ hΛzT
    R.later.qs_pos (by linarith only [hqsS, hθS2]) (by linarith only [hveS, hθS'])
    R.later.ζ_pos (by linarith only [hζS, hθS2]) hζΔ'
    (hεrS.trans_le (div_le_div_of_nonneg_right hθS' hD))
  have hS04 := hrowR R.stage R.later.excl.Δ R.later.excl.β₂ hΔ1 hβ₂ hβ₂1 X g hmetric ρ hρ
    R.later.scale.Λ R.β
    R.later.err.co.qs Kf R.later.err.co.qe R.later.err.bd.μ R.later.split.b R.later.err.s
    R.later.err.wk.b' R.later.err.wk.s' R.later.err.co.ε R.later.circle.γc R.later.circle.βc
    R.later.Lmax R.later.err.bd.τ R.later.circle.γ δ εr R.later.err.co.e₀ R.later.split.T₀
    R.later.split.V R.later.err.co.ve R.later.err.co.ζ Λz P.toLocalChartPacketsRVZ
    hβ2 (hq₀₂.trans_le (min_le_right _ _)).le ((le_max_right _ _).trans hLS) hΛ h4 he₀ hT₀ hΛzT
    R.later.qs_pos (by linarith only [hqsS, hθR2]) (by linarith only [hveS, hθR'])
    R.later.ζ_pos (by linarith only [hζS, hθR2]) hζΔ'
    (hεrS.trans_le (div_le_div_of_nonneg_right hθR' hD))
  -- the three native outputs at the planes' slots and radii, at the register's `Ξ_j(Γ_j)`, `c_w`
  have he8 : R.later.err.co.e₀ ≤ 1 / 8 := by linarith
  have O₀ := (R.stage.stageOutput_RGC 0 P hΛ hΔ1 hμ hτ he8 h4 (A₀.rsel x₀) (A₀.cfs15_inputs x₀).1
    A₀.plane (fun x hx => (A₀.dimension x hx).1)
    (A₀.cloudy (A₀.rsel x₀) (A₀.cfs15_inputs x₀).1)).some
  have O₁ := (R.stage.stageOutput_RGC 1 P hΛ hΔ1 hμ hτ he8 h4 (A₁.rsel x₀) (A₁.cfs15_inputs x₀).1
    A₁.plane (fun x hx => (A₁.dimension x hx).1)
    (A₁.cloudy (A₁.rsel x₀) (A₁.cfs15_inputs x₀).1)).some
  have O₂ := (R.stage.stageOutput_RGC 2 P hΛ hΔ1 hμ hτ he8 h4 (A₂.rsel x₀) (A₂.cfs15_inputs x₀).1
    A₂.plane (fun x hx => (A₂.dimension x hx).1)
    (A₂.cloudy (A₂.rsel x₀) (A₂.cfs15_inputs x₀).1)).some
  have hεr1 : εr ≤ 1 := by
    have := R.later.ε₀_lt.trans_le (min_le_left _ _)
    linarith
  obtain ⟨hos, hone, hrank, hsig, hcw⟩ := R.stage.choice_RGC
  obtain ⟨C, hC⟩ := gaf02_chainE_mk_GAF8 P
    ⟨hΛ, hΔ1, hμ, hτ, h4, h5, he₀, hT₀, R.later.qs_pos.le, R.later.qs_le_hundredth_VAL6,
      ⟨R.later.qe_pos.le, R.later.qe_lt_one_VAL6.le⟩, ⟨R.later.γc_pos.le, hγc1⟩, ⟨hεr0, hεr1⟩⟩
    R.stage.chain_numbers_RGC x₀ A₀ A₁ A₂ O₀ O₁ O₂ hT05 hE06 hS04 hos hone hrank hsig hcw
  exact ⟨C.withRegisterJA_RGC R.stage, hC⟩

end DifferentialGeometry.Geometry.Collapse
