import DifferentialGeometry.Geometry.Collapse.StaticRegisterV4ChainNumerics74
import DifferentialGeometry.Geometry.Collapse.StaticRegisterV4ChainFdcCaps74
import DifferentialGeometry.Geometry.Fibration.ActualStageChainCutChoiceSlimRNUM
import DifferentialGeometry.Geometry.Fibration.ActualStageChainZeroExclusionM1Applications

/-!
# D74-18: the record `Htail = ClosedFdcMemberFacts74 S B` on the CURRENT member

Lane S-REG-NUM (`_RNUM`), G2. Draft 74 §6.3 / D74-18: the already-proved eventual FDC theorems are
instantiated on the member BUILT by the register, in the order

`Δ, β₂, Λ₀` → `(L_c, η₀, w₀)` → one strategy (the FDC caps of `StaticRegisterV4ChainFdcCaps74`
on top of the complete strategy, then the chain strategy, then the realization) → `R` → the SAME
FAMZ parameters `ε_r, δ, Λ_z` → the realized models of the tail → the FDC tail `∀ᶠ i` of the
realized model sequence → the current member `m ≥ n` → its own `F` and chain `Ĉ` → `S = ⟨F, Ĉ⟩`.

No fixed `S` is claimed to lie in the good tail after the fact: `n` is read from the models the
register itself realized (a function of `R`), before any member, and `S` is built from the
member's own family and chain. The eventual statements are `eventually_fdc02_M1_C14Z_EFC` (the
equality `M₂ ∩ X₂ = M₂ ∩ V ∩ witness`, compactness) and `eventually_fdc04_M1_C14Z_EFC` (compact
`M^edge, M₃`, `M₂ = M^edge ∪ M₃`, the four-piece cover, six disjoint interiors), with the ACTUAL
zero domains (ZSP02, `εr < 1/2`, `e ≤ 1/1000`) and the slim facts of ZSP05 which hold for EVERY cut
choice (`cutChoice_slim_spec_RNUM`), so the record keeps its `∀ D` form.

## Audit table: premise of the FDC theorems → choice node → supplier

* `100 ≤ Δ`: PR13 slot `Δ_gt` (`Δ > 10⁶`); `hundred_lt_Δ_VAL6`.
* `0 < β₂ < 10⁻⁶`: PR12 slot `β₂_lt` (CAA01); `β₂_lt_audit_VAL6`. `0 < Λ₀ := Λ`: PR19 `Λ_pos`.
* the window `ρ ∈ [w'/2.., ..]` with `Λ₀ = Λ`: `F.ρ_bounds` and `closedWPrime = w/(2(1+2Λ⁻¹)³)`.
* `w < w₀(Δ, β₂, Λ)`: PR20 `w_lt`, slot `wUp ≤ w₀` — FDC cap; `w < 4π/3`: `w_lt` (unit ball volume).
* `β₃ ≤ threeSplittingExclusionThreshold`: `β₃_lt` and `T.lc18 ≤` it (the realization's output).
* `β 2 < 10⁻⁶`: `β_two_VAL6`, `β₂_lt_audit_VAL6`; `b < 10⁻⁶`: `b_lt_audit_VAL6`; `s < 10⁻⁶`:
  `s_lt_audit_VAL6`.
* `b ≤ η₀(Δ, β₂, Λ)`, `β 1 ≤ η₀`: slots `splitUp`, `β₁Up` — FDC caps (read at the scale `∋ Λ`).
* `L_c ≤ L_max`: slot `T₀Low ≥ L_c` — FDC cap, then `T₀ ≤ V`, `400 V < L_max`.
* `μ ≤ 10⁻⁸`, `τ ≤ 10⁻⁸`: `μ_lt_VAL6`, `τ_lt_VAL6`. `σ_c = q_e ≤ 10⁻¹²`: `qe_lt` (`θ_e²/10⁸`,
  `θ_e < 1/100`).
* `μΔ < 10⁻⁴`: slot `sectionUp ≤ 1/(10⁴ Δ)` — FDC cap (V4's chain cap gives only `μΔ < θ/100`).
* `ε_r < 1/2`, `e ≤ 1/1000`: FAMZ's `ε_r < 1/4` and `e₀_lt` (record `N`, `G1`).
* the standing sequence `α m = m + 2`, `hstand`: holds for EVERY normalized model of the member
  (`closed_standing_clauses_VAL`, `ClosedModel.firstVolumeScale_eq`, `curvatureRadius_eq`).

NEW register clauses (V5 candidates, all placed in V4 slots read after their arguments, none
changes a quantifier): `sectionUp ≤ 1/(10⁴Δ)`, `wUp ≤ w₀`, `splitUp, β₁Up ≤ η₀`, `T₀Low ≥ L_c`.

* **`register_yields_fdcFacts_RNUM`**: one strategy `T` refining the complete strategy with the two
  PR10 equalities and, at every register, FAMZ's `ε_r < 1/4`, `δ`, `Λ_z`, an index `n` and on
  every member `m ≥ n`, for every base point, a source `S` carrying `N` AND `Htail` for every bases
  object.
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

/-- **The register yields `N` and `Htail` on every member of a tail `m ≥ n`** (module header). -/
theorem register_yields_fdcFacts_RNUM (K : ℕ) (hK : 10 ≤ K) (A : ℝ → ℝ)
    (hA : ∀ x, 0 < x → 0 < A x) (Wseq : ℕ → CompactCarrier.{u})
    (gseq : ∀ m, SmoothRiemannianMetric (Wseq m).model (Wseq m).Carrier)
    (hf : ∀ m, ClosedMemberFacts (Wseq m))
    (hg : ∀ m, closedCollapseHypotheses (Wseq m) (gseq m) K A (closedCounterexampleRatio (m + 2))) :
    ∃ T : ClosedThresholdsV4 (earlyDataSharedV4 K),
      ClosedStrategyRefinesV4 T (closedStrategyCompleteV4C (earlyDataSharedV4 K)) ∧
      T.Nb = maxNb_V4C ∧ T.cw = maxCw_V4C ∧
      ∀ R : ClosedRegisterV4 (earlyDataSharedV4 K) T, ∃ εr δ Λz : ℝ, 0 < εr ∧ εr < 1 / 4 ∧
        ∃ n : ℕ, ∀ m, n ≤ m → ∃ M : ClosedModel (Wseq m) (gseq m), Nonempty M.X ∧
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
  obtain ⟨T, hTU', -, hlc18, hfam⟩ :=
    exists_closed_realization_C14Z_RGC K hK A hA Wseq gseq hf hg U'
  have hTU := hTU'.trans_RGC hU'U
  have hT0 := hTU.trans_RGC (ClosedThresholdsV4.withFdcCaps_refines_RNUM _ _ _ _)
  refine ⟨T, hT0, hT0.Nb_eq, hT0.cw_eq, fun R => ?_⟩
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
  refine ⟨max n R.later.tail, fun m hm => ?_⟩
  have hmt : R.later.tail ≤ m := (le_max_right _ _).trans hm
  obtain ⟨hn2, hn4⟩ := hn m ((le_max_left _ _).trans hm)
  have hMm : M' m = Classical.choose (ht m hmt) := dite_eq_left hmt
  obtain ⟨F⟩ := hM' m hmt
  have : ConnectedSpace (Wseq m).Carrier := (hf m).connected
  refine ⟨M' m, ⟨(M' m).ψ.symm (Classical.arbitrary (Wseq m).Carrier)⟩, fun x₀ => ?_⟩
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
