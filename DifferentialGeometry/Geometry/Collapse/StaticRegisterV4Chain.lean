import DifferentialGeometry.Geometry.Collapse.StaticRegisterV4ChainCaps
import DifferentialGeometry.Geometry.Fibration.ActualStageChainRow

/-!
# Register V4 yields the GAF02 chain on its OWN stage data

Lane C14-REG-CHAIN (review 66, D66-2/D66-3/D66-5). For every threshold strategy `U` of register V4
on `earlyDataSharedV4 K` there is a strategy `U'` refining it (the chain caps,
`ClosedThresholdsV4.withChainCaps_RGC`, with FC27's three test thresholds chosen as functions of the
earlier register values) such that at EVERY register `R` of EVERY strategy below `U'`, on every
packet of the final family at exactly the register's values (with `0 ≤ ε_r < ε₀` and
`20Λ_z ≤ T₀Low`, the realization's prefix facts), every selection of original preimages carries a
chain object

`C : Gaf02Chain P K (Ξ_j(Γ_j)) Γ Σ e c (stageCwAt_V4C R.stage)`, `C.sel = sel`,

whose numbers ARE the register's stage values (by its type: `Ξ_j = Ξ_j(Γ_j)` of the register's
modulus, `Γ = R.stage.Γ`, `Σ = R.stage.Sig`, `e = R.stage.e`, `c = R.stage.c`, and the PR10 weight
constants `c_w^{(j)} = stageCwAt_V4C R.stage j`), whose `numbers` field is
`ClosedStage.chain_numbers_RGC` (the register's own inequalities, no second GAF01 choice), whose
planes are FC27's tests at `(Γ_j, Σ_j, e_j)` and whose slots are the native outputs of
`earlyDataSharedV4_stageOutput_C15` at the register's `Ξ_j(Γ_j)` (`ClosedStage.stageOutput_RGC`).
No independent `gaf02_chain_row_GAF8` call is spliced to the register.

* `exists_chainStrategy_RGC K U`.
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

/-- **Register V4 yields the chain** (see the module header). -/
theorem exists_chainStrategy_RGC (K : ℕ) (U : ClosedThresholdsV4 (earlyDataSharedV4 K)) :
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
        ∀ sel : Fin 3 → BlockSpace (fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²) → X,
        (∀ st, ∀ x ∈ gafCloudEnlarged P.toLocalChartFamily P.zero st,
          cgpProjMap P.toLocalChartFamily P.zero (gafStageTags P.toLocalChartFamily P.zero st)
            (sel st x) = x) →
        ∃ C : Gaf02Chain P.toLocalChartPackets K
            (fun j => (earlyDataSharedV4 K).Ξ j (R.stage.Γ j)) R.stage.Γ R.stage.Sig R.stage.e
            R.stage.c (stageCwAt_V4C R.stage),
          C.sel = sel := by
  classical
  -- FC27's first test at `(Γ₀, Σ₀, e₀, ν)`
  have hfirst := fun (st : ClosedStage (earlyDataSharedV4 K)) (ν : ℝ) (hν : 0 < ν)
      (hν1 : ν < 1) =>
    fc27_first_test_pps_GAF5 (st.chain_ranges_RGC 0).1 (st.chain_ranges_RGC 0).2.1
      (st.chain_ranges_RGC 0).2.2.1 (st.chain_ranges_RGC 0).2.2.2.1
      (st.chain_ranges_RGC 0).2.2.2.2.1 (st.chain_ranges_RGC 0).2.2.2.2.2.1
      (st.chain_ranges_RGC 0).2.2.2.2.2.2.1 (st.chain_ranges_RGC 0).2.2.2.2.2.2.2.1 hν hν1
  choose! σf hσ hσ1 hfirst' using hfirst
  choose! η₂f γ₀f ηcf θf hη₂ hγ₀ hηc hθ hθ1 hrow1 using hfirst'
  choose! η₁f hη₁ hrow1' using hrow1
  -- FC27's edge test at `(Γ₁, Σ₁, e₁, Δ, β₂)`
  have hedge := fun (st : ClosedStage (earlyDataSharedV4 K)) (Δ β₂ : ℝ) (hΔ : 1 ≤ Δ)
      (hβ₂ : 0 < β₂) (hβ₂1 : β₂ < 1 / 1000000) =>
    fc27_edge_test_pp_GAF4 (Γ := st.Γ 1) (Sg := st.Sig 1) (eg := st.e 1) hΔ hβ₂ hβ₂1
      ⟨(st.chain_ranges_RGC 1).1, (st.chain_ranges_RGC 1).2.1⟩ (st.chain_ranges_RGC 1).2.2.1
      (lt_min (st.chain_ranges_RGC 1).2.2.2.1 (st.chain_ranges_RGC 1).2.2.2.2.1)
      (st.chain_ranges_RGC 1).2.2.2.2.2.1
      (lt_min (st.chain_ranges_RGC 1).2.2.2.2.2.2.1
        (lt_min (st.chain_ranges_RGC 1).2.2.2.2.2.2.2.1
          (st.chain_ranges_RGC 1).2.2.2.2.2.2.2.2.1))
  choose! Lc₁f η₀₁f hLc₁ hη₀₁ hrowE using hedge
  -- FC27's slim test at `(Γ₂, Σ₂, e₂, Δ, β₂)`
  have hslim := fun (st : ClosedStage (earlyDataSharedV4 K)) (Δ β₂ : ℝ) (hΔ : 1 ≤ Δ)
      (hβ₂ : 0 < β₂) (hβ₂1 : β₂ < 1) =>
    fc27_slim_test_pp_C14_GAF4 (Γ := st.Γ 2) (sg := st.Sig 2) (eg := st.e 2) hΔ hβ₂ hβ₂1
      (st.chain_ranges_RGC 2).1 (st.chain_ranges_RGC 2).2.1 (st.chain_ranges_RGC 2).2.2.1
      (st.chain_ranges_RGC 2).2.2.2.1 (st.chain_ranges_RGC 2).2.2.2.2.1
      (st.chain_ranges_RGC 2).2.2.2.2.2.1 (st.chain_ranges_RGC 2).2.2.2.2.2.2.1
      (st.chain_ranges_RGC 2).2.2.2.2.2.2.2.1
  choose! θsf hθs hθs1 Lc₂f η₀₂f hLc₂ hη₀₂ hrowS using hslim
  refine ⟨U.withChainCaps_RGC σf η₂f γ₀f ηcf θf η₁f Lc₁f η₀₁f θsf Lc₂f η₀₂f,
    U.withChainCaps_refines_RGC _ _ _ _ _ _ _ _ _ _ _, ?_⟩
  intro T hT R X _ _ _ _ g hmetric ρ hρ Kf δ εr Λz P hεr0 hεr hΛz sel hsel
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
  -- the thresholds at the register
  have hσR := hσ R.stage _ hν hν1
  obtain ⟨-, hσβ, hηβ, hγγ, hγcγ, hγc1, hβcη, herr, hμc, hbη, hβ₁η, hσT, hL₁T, hL₂T⟩ :=
    ClosedRegisterV4.chainCaps_RGC hT R hσR (hη₂ R.stage _ hν hν1) (hγ₀ R.stage _ hν hν1)
      (hηc R.stage _ hν hν1) (hθ R.stage _ hν hν1) (hη₁ R.stage _ hν hν1 _ hΔ1200)
      (hη₀₁ R.stage _ _ hΔ1 hβ₂ hβ₂a) (hθs R.stage _ _ hΔ1 hβ₂ hβ₂1)
      (hη₀₂ R.stage _ _ hΔ1 hβ₂ hβ₂1)
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
  -- register facts used by the tests
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
  have hεrε₀ := hεr
  have h31 : 1000 * tcpGraphConst * R.later.excl.Δ * R.later.scale.Λ < R.stage.e 0 := by
    have h := R.later.regScale_e
    have hC : (0 : ℝ) < tcpGraphConst := lt_of_lt_of_le one_pos one_le_tcpGraphConst
    have hC' : (earlyDataSharedV4 K).C 0 = tcpGraphConst := rfl
    rw [hC', lt_div_iff₀ (by positivity)] at h
    linarith
  have hβ3 : 3 * (R.later.excl.β₃ / 3) ≤ R.β 3 := by rw [R.β_three_VAL6]; linarith
  have hβ3' : R.β 3 < 1 := by rw [R.β_three_VAL6]; exact hβ₃1
  have hβ2σ : 3 * R.β 2 ≤ σf R.stage (R.later.excl.β₃ / 3) := by rw [R.β_two_VAL6]; exact hσβ
  have hβ2η : R.β 2 ≤ η₂f R.stage (R.later.excl.β₃ / 3) := by rw [R.β_two_VAL6]; exact hηβ
  have hβ1η₁ : R.β 1 ≤ η₁f R.stage (R.later.excl.β₃ / 3) R.later.excl.Δ := by
    rw [R.β_one_VAL6]; exact (hβ₁η.trans_le (min_le_left _ _)).le
  have hβ1η₀₁ : R.β 1 ≤ η₀₁f R.stage R.later.excl.Δ R.later.excl.β₂ := by
    rw [R.β_one_VAL6]; exact (hβ₁η.trans_le ((min_le_right _ _).trans (min_le_left _ _))).le
  have hβ1η₀₂ : R.β 1 ≤ η₀₂f R.stage R.later.excl.Δ R.later.excl.β₂ := by
    rw [R.β_one_VAL6]; exact (hβ₁η.trans_le ((min_le_right _ _).trans (min_le_right _ _))).le
  have hs6 : R.later.err.s < 1 / 1000000 := by
    have := R.later.s_lt_audit_VAL6
    norm_num at this ⊢
    exact this
  -- the three stage tests on `P`
  obtain ⟨plane₀, hp₀⟩ := hrow1' R.stage _ hν hν1 _ hΔ1200 P hΛ hμ hτ h4 h5 he₀ hT₀
    R.later.ε_pos.le hε1.le R.later.qe_pos.le hqeθ.le hμθ.le hβ3 hβ3' hβ2σ hβ2η hγγ
    R.later.γc_pos hγcγ hβcη (hbη.trans_le (min_le_left _ _)).le hβ1η₁ R.later.qs_pos hqsθ.le
    hveθ.le R.later.ζ_pos hζθ.le (hεr.trans hε₀θ).le hΛzT
    (hσT.trans hT₀L) h31
  obtain ⟨plane₁, hp₁⟩ := hrowE R.stage _ _ hΔ1 hβ₂ hβ₂a X g hmetric ρ hρ R.later.scale.Λ R.β
    R.later.err.co.qs Kf R.later.err.co.qe R.later.err.bd.μ R.later.split.b R.later.err.s
    R.later.err.wk.b' R.later.err.wk.s' R.later.err.co.ε R.later.circle.γc R.later.circle.βc
    R.later.Lmax R.later.err.bd.τ R.later.circle.γ δ εr R.later.err.co.e₀ R.later.split.T₀
    R.later.split.V R.later.err.co.ve R.later.err.co.ζ Λz P
    (hbη.trans_le (min_le_right _ _)).le hs6 hβ1η₀₁ (hL₁T.trans hT₀L) hΛ h4 hμ hτ hqeE.le hμE
    R.later.qs_pos hqsE.le hveE he₀
    hT₀ hΛzT R.later.ζ_pos hζE.le hζΔ.le (hεr.trans hε₀E)
  obtain ⟨plane₂, hp₂⟩ := hrowS R.stage _ _ hΔ1 hβ₂ hβ₂1 X g hmetric ρ hρ R.later.scale.Λ R.β
    R.later.err.co.qs Kf R.later.err.co.qe R.later.err.bd.μ R.later.split.b R.later.err.s
    R.later.err.wk.b' R.later.err.wk.s' R.later.err.co.ε R.later.circle.γc R.later.circle.βc
    R.later.Lmax R.later.err.bd.τ R.later.circle.γ δ εr R.later.err.co.e₀ R.later.split.T₀
    R.later.split.V R.later.err.co.ve R.later.err.co.ζ Λz P
    R.β_two_VAL6 hβ1η₀₂ (hL₂T.trans hT₀L) hΛ h4 he₀ hT₀ hΛzT R.later.qs_pos hqsS hveS
    R.later.ζ_pos hζS hζΔ' (hεr.trans hε₀S)
  -- the three native outputs at the register's `Ξ_j(Γ_j)` and `c_w^{(j)}`
  have he8 : R.later.err.co.e₀ ≤ 1 / 8 := by linarith
  have O₀ := (R.stage.stageOutput_RGC 0 P hΛ hΔ1 hμ hτ he8 h4 (sel 0) (hsel 0) plane₀
    (fun x hx => (hp₀.1 x hx).1) (hp₀.2.1 (sel 0) (hsel 0))).some
  have O₁ := (R.stage.stageOutput_RGC 1 P hΛ hΔ1 hμ hτ he8 h4 (sel 1) (hsel 1) plane₁
    (fun x hx => (hp₁.1 x hx).1) (hp₁.2.1 (sel 1) (hsel 1))).some
  have O₂ := (R.stage.stageOutput_RGC 2 P hΛ hΔ1 hμ hτ he8 h4 (sel 2) (hsel 2) plane₂
    (fun x hx => (hp₂.1 x hx).1) (hp₂.2.1 (sel 2) (hsel 2))).some
  have hεr1 : εr ≤ 1 := by
    have := R.later.ε₀_lt.trans_le (min_le_left _ _)
    linarith
  exact ⟨{
    std := ⟨hΛ, hΔ1, hμ, hτ, h4, h5, he₀, hT₀, R.later.qs_pos.le, R.later.qs_le_hundredth_VAL6,
      ⟨R.later.qe_pos.le, R.later.qe_lt_one_VAL6.le⟩, ⟨R.later.γc_pos.le, hγc1⟩, ⟨hεr0, hεr1⟩⟩
    numbers := R.stage.chain_numbers_RGC
    sel := sel
    hsel := hsel
    plane := ![plane₀, plane₁, plane₂]
    test0 := hp₀
    test1 := hp₁
    test2 := hp₂
    slot := fun st => match st with
      | ⟨0, _⟩ => .active O₀
      | ⟨1, _⟩ => .active O₁
      | ⟨2, _⟩ => .active O₂
      | ⟨k + 3, hk⟩ => absurd hk (by omega) }, rfl⟩

end DifferentialGeometry.Geometry.Collapse
