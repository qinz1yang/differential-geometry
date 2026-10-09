import DifferentialGeometry.Geometry.Collapse.StaticRegisterV4ChainFdcFacts74
import DifferentialGeometry.Geometry.Collapse.StaticRegisterV4ChainEPbrZ

/-!
# The register's FDC head at ONE strategy, with the old PBR02 static fields kept

Lane S-FC-WRAP5 (suffix `_FCW`), group G15a. Review 78 Q12 (§12.2–12.3, D78-12): the closed rows
producer's sequence head must come from ONE strengthened implementation. The two heads of the tree
cannot be spliced: `pbr02_staticEZ_RGC` keeps the validity record
`PartialClosedThresholdValidityV4Rows`, the non-emptiness of the register and the model
identification `M.gX = pullbackMetricCross`, but its strategy is not the FDC-capped one;
`register_yields_fdcFacts_RNUM` produces the FDC facts `Htail` on the capped strategy, but its
public conclusion drops the validity record, the non-emptiness of the register, the model
identification and the fact that `n` lies beyond `R.later.tail`.

`register_yields_fdcFacts_head_FCW` is the body of `register_yields_fdcFacts_RNUM` (one strategy:
FDC caps, chain strategy, realization; then `R`, the common `ε_r, δ, Λ_z`, the realized models of
the tail, the FDC tail `n_good = max n R.later.tail`, then the member and its base point `x₀`)
with the conclusion enlarged by

* `PartialClosedThresholdValidityV4Rows K A Wseq gseq (earlyDataSharedV4 K) T` (the derivation of
  `register_yields_chainEJAZ_RGC`, from the realization's `T.H`, `T.lc18`, `ClosedFamilyAtC14ZV4`);
* `Nonempty (ClosedRegisterV4 (earlyDataSharedV4 K) T)` (`exists_closedRegisterV4`);
* the model identification `M.gX = Diffeomorph.pullbackMetricCross (gseq m) M.ψ` on every member;
* `R.later.tail ≤ n` (the actual `n_good`), before the members and before `x₀`.

The quantifier order is the one of review 78: strategy ≺ register ≺ `(ε_r, δ, Λ_z)` and `n` ≺
member ≺ base point `x₀`; `n` does not depend on `x₀`.
-/

set_option autoImplicit false

noncomputable section

open Set Function Metric Bundle Manifold Filter
open scoped ContDiff Manifold Topology
open DifferentialGeometry GC.Endpoint GC.MetricGeometry
open DifferentialGeometry.Geometry.Riemannian DifferentialGeometry.Analysis
open GC.GraphManifold.Assembly GC.GraphManifold.Assembly.FC39P0

namespace DifferentialGeometry.Geometry.Collapse

universe u

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace

/-- **The register's FDC head with the PBR02 static fields** (module header). -/
theorem register_yields_fdcFacts_head_FCW (K : ℕ) (hK : 10 ≤ K) (A : ℝ → ℝ)
    (hA : ∀ x, 0 < x → 0 < A x) (Wseq : ℕ → CompactCarrier.{u})
    (gseq : ∀ m, SmoothRiemannianMetric (Wseq m).model (Wseq m).Carrier)
    (hf : ∀ m, ClosedMemberFacts (Wseq m))
    (hg : ∀ m, closedCollapseHypotheses (Wseq m) (gseq m) K A (closedCounterexampleRatio (m + 2))) :
    ∃ T : ClosedThresholdsV4 (earlyDataSharedV4 K),
      ClosedStrategyRefinesV4 T (closedStrategyCompleteV4C (earlyDataSharedV4 K)) ∧
      PartialClosedThresholdValidityV4Rows K A Wseq gseq (earlyDataSharedV4 K) T ∧
      T.Nb = maxNb_V4C ∧ T.cw = maxCw_V4C ∧
      Nonempty (ClosedRegisterV4 (earlyDataSharedV4 K) T) ∧
      ∀ R : ClosedRegisterV4 (earlyDataSharedV4 K) T, ∃ εr δ Λz : ℝ, 0 < εr ∧ εr < 1 / 4 ∧
        ∃ n : ℕ, R.later.tail ≤ n ∧ ∀ m, n ≤ m → ∃ M : ClosedModel (Wseq m) (gseq m),
          M.gX = Diffeomorph.pullbackMetricCross (gseq m) M.ψ ∧ Nonempty M.X ∧
          ∀ x₀ : M.X, ∃ S : ClosedChainEZRowsSource_RGC K R M δ εr Λz, S.chain.x₀ = x₀ ∧
            Nonempty (ClosedRowsNumericsAt74 S) ∧ ∀ B : ClosedBases74 S,
              ClosedFdcMemberFacts74 S B := by
  classical
  -- the FDC triples at `(Δ, β₂, Λ₀)`, FIRST (D74-18: `Δ, β₂, Λ₀`, then `Lc, η₀, w₀`)
  have h2 := fun (Δ β₂ Λ : ℝ) (h : 100 ≤ Δ ∧ 0 < β₂ ∧ β₂ < 1 / 1000000 ∧ 0 < Λ) =>
    eventually_fdc02_M1_C14Z_EFC h.1 h.2.1 h.2.2.1 h.2.2.2
  choose! Lc₂ η₂ hLc₂ hη₂ w₂ hw₂ ht₂ using h2
  have h4 := fun (Δ β₂ Λ : ℝ) (h : 100 ≤ Δ ∧ 0 < β₂ ∧ β₂ < 1 / 1000000 ∧ 0 < Λ) =>
    eventually_fdc04_M1_C14Z_EFC h.1 h.2.1 h.2.2.1 h.2.2.2
  choose! Lc₄ η₄ hLc₄ hη₄ w₄ hw₄ ht₄ using h4
  -- ONE strategy: the complete one with the FDC caps, then the chain strategy, then the realization
  obtain ⟨U', hU'U, hchain⟩ := exists_chainEStrategy_RGC K
    ((closedStrategyCompleteV4C (earlyDataSharedV4 K)).withFdcCaps_RNUM
      (fun Δ β₂ Λ => max (Lc₂ Δ β₂ Λ) (Lc₄ Δ β₂ Λ))
      (fun Δ β₂ Λ => min (η₂ Δ β₂ Λ) (η₄ Δ β₂ Λ))
      (fun Δ β₂ Λ => min (w₂ Δ β₂ Λ) (w₄ Δ β₂ Λ)))
  obtain ⟨T, hTU', hH, hlc18, hfam⟩ :=
    exists_closed_realization_C14Z_RGC K hK A hA Wseq gseq hf hg U'
  have hTU := hTU'.trans_RGC hU'U
  have hT0 := hTU.trans_RGC (ClosedThresholdsV4.withFdcCaps_refines_RNUM _ _ _ _)
  -- the validity record at THIS T (the same derivation as `register_yields_chainEJAZ_RGC`)
  obtain ⟨hN, hP, hPs, hPz, hL₀, hΞ, hΞr, hC⟩ := earlyDataSharedV4_fields_VAL6 K
  have hb : ClosedStrategyBelowV4 T (closedStrategyCompleteV4C (earlyDataSharedV4 K)) :=
    hT0.below_VAL6
  obtain ⟨-, -, -, hrows⟩ := hb.complete_caps_V4C
  have hsc : ClosedStrategyBelowV4 T (scaleStrategyV4 (earlyDataSharedV4 K)) :=
    hrows.trans_VAL6 ((ClosedThresholdsV4.inf_below_left_VAL6 _ _).trans_VAL6
      (ClosedThresholdsV4.inf_below_left_VAL6 _ _))
  have hv : PartialClosedThresholdValidityV4Rows K A Wseq gseq (earlyDataSharedV4 K) T :=
    ⟨⟨hN, hP, hPs, hPz, hL₀, hΞ, hΞr, hlc18, hT0.I₁_eq, fun m p => by
      rw [hH m]
      exact closed_standing_clauses_VAL K A Wseq gseq hg m p, fun _ => hfam.toC14D_RGC.toC14_VAL6⟩,
      hC, closedScaleBudgetV4_of_below_VAL6 hsc,
      fun _ _ _ _ hεr hΛz _ _ F => closedRowOuts_of_below_VAL6 hC hrows F hεr hΛz⟩
  refine ⟨T, hT0, hv, hT0.Nb_eq, hT0.cw_eq, exists_closedRegisterV4 _ T, fun R => ?_⟩
  obtain ⟨εrF, δ'F, ΛzF, hF⟩ := hfam
  obtain ⟨hεr0, hεr14, hεrε₀, -, -, hΛz, δc, -, -, ht⟩ := hF R
  generalize εrF R.stage R.later.circle R.later.excl R.later.err R.later.scale R.later.split.b
    R.later.split.β₁ = εr at hεr0 hεr14 hεrε₀ ht
  generalize ΛzF R.stage R.later.circle R.later.excl R.later.err R.later.scale R.later.split.b
    R.later.split.β₁ = Λz at hΛz ht
  refine ⟨εr, δc, Λz, hεr0, hεr14, ?_⟩
  -- numerics from the register and the FDC caps (all read BEFORE the member)
  have hΔ100 : 100 ≤ R.later.excl.Δ := R.later.hundred_lt_Δ_VAL6.le
  have hβ₂1 : R.later.excl.β₂ < 1 / 1000000 := by
    have := R.later.β₂_lt_audit_VAL6
    norm_num at this ⊢
    exact this
  have hcond : 100 ≤ R.later.excl.Δ ∧ 0 < R.later.excl.β₂ ∧ R.later.excl.β₂ < 1 / 1000000 ∧
      0 < R.later.scale.Λ := ⟨hΔ100, R.later.β₂_pos, hβ₂1, R.later.Λ_pos⟩
  have hη₀p : 0 < min (η₂ R.later.excl.Δ R.later.excl.β₂ R.later.scale.Λ)
      (η₄ R.later.excl.Δ R.later.excl.β₂ R.later.scale.Λ) :=
    lt_min (hη₂ _ _ _ hcond) (hη₄ _ _ _ hcond)
  have hw₀p : 0 < min (w₂ R.later.excl.Δ R.later.excl.β₂ R.later.scale.Λ)
      (w₄ R.later.excl.Δ R.later.excl.β₂ R.later.scale.Λ) :=
    lt_min (hw₂ _ _ _ hcond) (hw₄ _ _ _ hcond)
  obtain ⟨hμΔ, hw, hb, hβ1, hLcT⟩ := R.fdcCaps_RNUM hTU.below_VAL6 hη₀p hw₀p
  -- the realized models of the register's tail: ONE sequence (chosen from `ht`, after `R`)
  have hne : ∀ m, Nonempty (ClosedModel (Wseq m) (gseq m)) := fun m =>
    nonempty_closedModel_VAL (Wseq m) (gseq m) (hf m)
  let M' : ∀ m, ClosedModel (Wseq m) (gseq m) := fun m =>
    if h : R.later.tail ≤ m then Classical.choose (ht m h) else Classical.choice (hne m)
  have hM' : ∀ m (h : R.later.tail ≤ m),
      Nonempty (ClosedFamilyInstanceC14ZV4 K R (M' m) δc εr Λz) := fun m h => by
    have e : M' m = Classical.choose (ht m h) := dite_eq_left h
    rw [e]
    exact (Classical.choose_spec (ht m h)).1
  have hstand : ∀ m (p : (M' m).X), ENNReal.ofReal (((m : ℝ) + 2) *
      firstVolumeScale (M' m).gX p ((m : ℝ) + 2)⁻¹) ≤ curvatureRadius (M' m).gX p := fun m p => by
    have h := (closed_standing_clauses_VAL K A Wseq gseq hg m ((M' m).ψ p)).1
    rwa [← (M' m).firstVolumeScale_eq, ← (M' m).curvatureRadius_eq] at h
  have htend : Tendsto (fun m : ℕ => (m : ℝ) + 2) atTop atTop :=
    tendsto_atTop_add_const_right _ 2 tendsto_natCast_atTop_atTop
  have hwc : R.later.scale.w < 4 * Real.pi / 3 := R.later.w_lt.trans_le (min_le_right _ _)
  have ev2 := ht₂ _ _ _ hcond R.later.scale.w R.later.w_pos
    (hw.trans_le (min_le_left _ _)) hwc (fun m => (M' m).X) (fun m => (M' m).gX)
    (fun m => (M' m).hmetric) (fun m : ℕ => (m : ℝ) + 2) htend hstand
  have ev4 := ht₄ _ _ _ hcond R.later.scale.w R.later.w_pos
    (hw.trans_le (min_le_right _ _)) hwc (fun m => (M' m).X) (fun m => (M' m).gX)
    (fun m => (M' m).hmetric) (fun m : ℕ => (m : ℝ) + 2) htend hstand
  obtain ⟨n, hn⟩ := eventually_atTop.mp (ev2.and ev4)
  refine ⟨max n R.later.tail, le_max_right _ _, fun m hm => ?_⟩
  have hmt : R.later.tail ≤ m := (le_max_right _ _).trans hm
  obtain ⟨hn2, hn4⟩ := hn m ((le_max_left _ _).trans hm)
  have hMm : M' m = Classical.choose (ht m hmt) := dite_eq_left hmt
  obtain ⟨F⟩ := hM' m hmt
  have : ConnectedSpace (Wseq m).Carrier := (hf m).connected
  refine ⟨M' m, (M' m).metric_eq, ⟨(M' m).ψ.symm (Classical.arbitrary (Wseq m).Carrier)⟩,
    fun x₀ => ?_⟩
  obtain ⟨C, hCx⟩ := hchain T hTU'.below_VAL6 R F.family.toLocalChartPacketsC14 hεr0.le hεrε₀
    hΛz x₀
  refine ⟨⟨F, C⟩, hCx, ⟨closedRowsNumerics_of_register_RNUM hT0.below_VAL6 hT0.Nb_eq hT0.cw_eq
    (by linarith) ⟨F, C⟩⟩, fun B => ⟨fun D => ?_⟩⟩
  -- the register values entering the FDC premises
  have hεr2 : εr < 1 / 2 := by linarith
  have he : R.later.err.co.e₀ ≤ 1 / 1000 := (R.later.e₀_lt.trans_le (min_le_left _ _)).le
  have hwin : ∀ p, firstVolumeScale (M' m).gX p R.later.scale.w / 2 ≤ F.ρ p ∧
      F.ρ p ≤ 2 * firstVolumeScale (M' m).gX p
        (R.later.scale.w / (2 * (1 + 2 * R.later.scale.Λ⁻¹) ^ 3)) := fun p =>
    ⟨(F.ρ_bounds p).1.le, (F.ρ_bounds p).2.le⟩
  have hβ3 : R.β 3 ≤ threeSplittingExclusionThreshold.{0, 0} := by
    rw [R.β_three_VAL6]
    exact R.later.β₃_lt.le.trans hlc18
  have hβ2 : R.β 2 < 1 / 1000000 := by
    rw [R.β_two_VAL6]
    exact hβ₂1
  have hb6 : R.later.split.b < 1 / 1000000 := by
    have := R.later.b_lt_audit_VAL6
    norm_num at this ⊢
    exact this
  have hs6 : R.later.err.s < 1 / 1000000 := by
    have := R.later.s_lt_audit_VAL6
    norm_num at this ⊢
    exact this
  have hLmax : max (Lc₂ R.later.excl.Δ R.later.excl.β₂ R.later.scale.Λ)
      (Lc₄ R.later.excl.Δ R.later.excl.β₂ R.later.scale.Λ) ≤ R.later.Lmax := by
    have h1 := R.later.T₀_le_V_VAL6
    have h2 := R.later.Lmax_gt_VAL6
    have h3 := R.later.T₀_pos_VAL6
    linarith
  have hσc : R.later.err.co.qe ≤ 1 / 10 ^ 12 := by
    have h1 : R.later.err.co.qe < R.later.circle.θe ^ 2 / 10 ^ 8 :=
      R.later.qe_lt.trans_le ((min_le_left _ _).trans (min_le_left _ _))
    have h2 := R.later.θe_lt_hundredth_VAL6
    have h3 := R.later.θe_pos
    have h4 : R.later.circle.θe ^ 2 / 10 ^ 8 ≤ 1 / 10 ^ 12 := by
      rw [div_le_iff₀ (by norm_num)]
      nlinarith
    linarith
  -- ZSP05's slim facts for THIS cut choice (every cut choice has them)
  obtain ⟨hSeq, -, hSreg, hScollar, -⟩ :=
    Gaf02ChainEJA.cutChoice_slim_spec_RNUM (P := F.family) C hεr2 D.toCutChoiceOn74
  have hSfar : ∀ q ∈ D.M₂, ∀ k (hk : k ∈ F.family.slim.centres),
      dist q k < 9 * R.later.excl.Δ * F.ρ k →
        10 * R.later.excl.Δ ≤ |(F.family.slim.centre k hk).coord q| := fun q hq k hk hd =>
    C.toGaf02ChainE.slim_far_of_relint_EFC (subset_union_left.trans D.K₃_req)
      (M₁ := C.toGaf02ChainE.cutM1_R74) (Msl := D.slimSet)
      (fun p hp hpK => by rw [hSeq]; exact ⟨hp, hpK⟩) (by rwa [D.M₂_eq] at hq) hk hd
  -- FDC02 and FDC04 at the member (the tail is taken from the realized models)
  have K2 := hn2 F.ρ F.ρ_pos hwin R.later.scale.Λ R.β R.later.err.co.qs K R.later.err.co.qe
    R.later.err.bd.μ R.later.split.b R.later.err.s R.later.err.wk.b' R.later.err.wk.s'
    R.later.err.co.ε R.later.circle.γc R.later.circle.βc R.later.Lmax R.later.err.bd.τ
    R.later.circle.γ δc εr R.later.err.co.e₀ R.later.split.T₀ R.later.split.V R.later.err.co.ve
    R.later.err.co.ζ Λz (M' m).orientation_RGC hβ3 hβ2 hb6
    (hb.trans_le (min_le_left _ _)).le hs6 (hβ1.trans_le (min_le_left _ _)).le
    ((le_max_left _ _).trans hLmax) R.later.μ_lt_VAL6.le R.later.τ_lt_VAL6.le hσc hμΔ hεr2 he
    F.family K (fun j => (earlyDataSharedV4 K).Ξ j (R.stage.Γ j)) R.stage.Γ R.stage.Sig
    R.stage.e R.stage.c (stageCwAt_V4C R.stage) C.toGaf02ChainE C.zeroUnion_ZSP35 D.slimSet
    (interior C.zeroUnion_ZSP35)ᶜ D.M₂ rfl rfl D.M₂_eq hSfar
  obtain ⟨hEq, -, -⟩ := K2
  obtain ⟨hAc, hM3c, hM2eq, -, hcov, h1, h2, h3, h4, h5, h6⟩ := hn4 F.ρ F.ρ_pos hwin
    R.later.scale.Λ R.β R.later.err.co.qs K R.later.err.co.qe
    R.later.err.bd.μ R.later.split.b R.later.err.s R.later.err.wk.b' R.later.err.wk.s'
    R.later.err.co.ε R.later.circle.γc R.later.circle.βc R.later.Lmax R.later.err.bd.τ
    R.later.circle.γ δc εr R.later.err.co.e₀ R.later.split.T₀ R.later.split.V R.later.err.co.ve
    R.later.err.co.ζ Λz (M' m).orientation_RGC hβ3 hβ2 hb6
    (hb.trans_le (min_le_right _ _)).le hs6 (hβ1.trans_le (min_le_right _ _)).le
    ((le_max_right _ _).trans hLmax) R.later.μ_lt_VAL6.le R.later.τ_lt_VAL6.le hσc hμΔ hεr2 he
    F.family K (fun j => (earlyDataSharedV4 K).Ξ j (R.stage.Γ j)) R.stage.Γ R.stage.Sig
    R.stage.e R.stage.c (stageCwAt_V4C R.stage) C.toGaf02ChainE C.zeroUnion_ZSP35 D.slimSet
    (interior C.zeroUnion_ZSP35)ᶜ D.M₂ D.edgeSet D.M₃ rfl rfl D.M₂_eq hEq D.M₃_eq
    (by rw [hSeq]; exact inter_subset_left) hSreg hScollar hSfar
  exact ⟨hAc, hM3c, hM2eq, hcov, h1, h2, h3, h4, h5, h6⟩

end DifferentialGeometry.Geometry.Collapse
