import DifferentialGeometry.Geometry.Collapse.StaticRegisterV2Provenance
import DifferentialGeometry.Geometry.Collapse.LocalExport.LocalChartPacketsC14Producer
import DifferentialGeometry.Geometry.Collapse.LocalExport.LocalChartPacketsC14Staged

/-!
# The closed realization on the staged register (lane FC39-VAL3; PARTIAL)

External review 52, order of work step 3: "common threshold strategy → one admissible `R` →
analytic realization of that `R` (same family, joint witness, original smoothing, …, common
tail)", keeping the producer's prefix witnesses (`εr, δ', Λz` before `T₀`, `T₀Low` with the same
`Λz`, `δ < δ'`).

* `exists_closed_realization_VAL3`: for every threshold strategy `U` (e.g. the rows' requests) a
  common strategy `T` refining it (`ClosedStrategyRefinesV2`): the Skolem thresholds of
  `eventually_nonempty_localChartPacketsC14` (`a₂, β₀, σ₀, Δ₀, τ₀, bc₀, a₀, b₁, w₀, bd₀, b₀,
  εr, δ', Λ', V, δ`, each a total function of the register values read before it) and LC09's
  `w₀(σ_col, Λ)` added slot by slot, `H m = m + 2`, `lc18 ≤` LC18's obstruction; EVERY staged
  register at `T` is realized (`PartialClosedFamilyAtV2`): on every member of its tail the SAME
  normalized model sequence (closed standing, orientation from `W.orientation`) carries
  `LocalChartPacketsC14` with exactly the register's values, LC09 at `σ_col` and LC18's
  exclusion.
* `exists_realized_closedRegisterV2_VAL3` (consumer): one admissible register at a common
  strategy, realized on its tail.
* PARTIAL: LPA02's joint witness and the zero-ball selection are not exported by the producer
  (`PartialClosedFamilyInstanceV2` = `ClosedFamilyInstanceV2` without them;
  `ClosedFamilyAtV2.toPartial_VAL3`); the rows' strategy is not yet supplied as `U`.
-/

set_option autoImplicit false

noncomputable section

open Set Function Metric Filter Manifold
open scoped ContDiff Manifold Topology
open DifferentialGeometry GC.Endpoint GC.MetricGeometry
open DifferentialGeometry.Geometry.Riemannian DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Integral.Measure

namespace DifferentialGeometry.Geometry.Collapse

universe u

local notation "E3" => EuclideanSpace ℝ (Fin 3)

/-- `x` if it is positive, `1` otherwise (keeps a threshold slot positive). -/
def posOr_VAL3 (x : ℝ) : ℝ := if 0 < x then x else 1

theorem posOr_pos_VAL3 (x : ℝ) : 0 < posOr_VAL3 x := by
  unfold posOr_VAL3
  split_ifs with h
  exacts [h, one_pos]

theorem posOr_eq_VAL3 {x : ℝ} (h : 0 < x) : posOr_VAL3 x = x := by
  simp only [posOr_VAL3, h, ↓reduceIte]

/-- The splitting vector read off the register's values (`β 1 = β₁`, `β 2 = β₂`, `β 3 = β₃`). -/
def closedβV3 (β₁ : ℝ) (ex : ClosedExclusions) (n : ℕ) : ℝ :=
  if n = 1 then β₁ else if n = 2 then ex.β₂ else if n = 3 then ex.β₃ else 0

theorem ClosedRegisterV2.β_eq_closedβV3_VAL3 {D : ClosedEarlyData} {T : ClosedThresholdsV2 D}
    (R : ClosedRegisterV2 D T) : R.β = closedβV3 R.later.split.β₁ R.later.excl :=
  rfl

/-- The producer's `A'` is positive when `A` is. -/
theorem boundaryDerivativeConstant_pos_VAL3 {A : ℝ → ℝ} {K : ℕ} (hA : ∀ x, 0 < x → 0 < A x)
    (C v : ℝ) (hv : 0 < v) : 0 < boundaryDerivativeConstant A K C v := by
  have hD : 0 < max 1 C := lt_max_of_lt_left one_pos
  have h0 : (0 : ℕ) ∈ Finset.range (K + 1) := Finset.mem_range.mpr (Nat.succ_pos K)
  refine lt_of_lt_of_le ?_ (Finset.le_sup' (fun k => A (((max 1 C) ^ 3)⁻¹ * v) *
    ((max 1 C) ^ (k + 2))⁻¹) h0)
  exact mul_pos (hA _ (by positivity)) (by positivity)

/-- **The family part of one instance of the final family at `R`** (PARTIAL: LPA02's joint witness
and the selection of the zero balls from it are not part of it). -/
structure PartialClosedFamilyInstanceV2 (K : ℕ) {D : ClosedEarlyData} {T : ClosedThresholdsV2 D}
    (R : ClosedRegisterV2 D T) {W : CompactCarrier.{u}}
    {g : SmoothRiemannianMetric W.model W.Carrier} (M : ClosedModel W g) (δ εr Λz : ℝ) where
  /-- The scale. -/
  ρ : M.X → ℝ
  ρ_pos : ∀ p, 0 < ρ p
  /-- LPA01's window. -/
  ρ_bounds : ∀ p, firstVolumeScale M.gX p R.later.scale.w / 2 < ρ p ∧
    ρ p < 2 * firstVolumeScale M.gX p (closedWPrime R.later.scale)
  /-- The final family at the register's values. -/
  family : LocalChartPacketsC14 M.X M.gX M.hmetric ρ ρ_pos R.later.scale.Λ R.β R.later.excl.Δ
    R.later.err.co.qs K R.later.err.co.qe R.later.err.bd.μ R.later.split.b R.later.err.s
    R.later.err.wk.b' R.later.err.wk.s' R.later.err.co.ε R.later.circle.γc R.later.circle.βc
    R.later.Lmax R.later.err.bd.τ R.later.circle.γ δ εr R.later.err.co.e₀ R.later.split.T₀
    R.later.split.V R.later.err.co.ve R.later.err.co.ζ Λz

/-- Forgetting the joint witness and the selection. -/
def ClosedFamilyInstanceV2.toPartial_VAL3 {K : ℕ} {D : ClosedEarlyData} {T : ClosedThresholdsV2 D}
    {R : ClosedRegisterV2 D T} {W : CompactCarrier.{u}}
    {g : SmoothRiemannianMetric W.model W.Carrier} {M : ClosedModel W g} {δ εr Λz : ℝ}
    (F : ClosedFamilyInstanceV2 K R M δ εr Λz) : PartialClosedFamilyInstanceV2 K R M δ εr Λz :=
  ⟨F.ρ, F.ρ_pos, F.ρ_bounds, F.family⟩

/-- `ClosedFamilyOnTailV2` with the PARTIAL instance (no joint witness, no selection). -/
def PartialClosedFamilyOnTailV2 (K : ℕ) (Wseq : ℕ → CompactCarrier.{u})
    (gseq : ∀ m, SmoothRiemannianMetric (Wseq m).model (Wseq m).Carrier) {D : ClosedEarlyData}
    {T : ClosedThresholdsV2 D} (R : ClosedRegisterV2 D T) (εr δ' Λz : ℝ) : Prop :=
  0 < εr ∧ εr < 1 / 4 ∧ εr < R.later.err.co.ε₀ ∧ 0 < δ' ∧ 0 < Λz ∧
    20 * Λz ≤ T.T₀Low R.stage R.later.circle R.later.excl R.later.err R.later.scale
      R.later.split.b R.later.split.β₁ ∧
    ∃ δ : ℝ, 0 < δ ∧ δ < δ' ∧ ∀ m, R.later.tail ≤ m → ∃ M : ClosedModel (Wseq m) (gseq m),
      Nonempty (PartialClosedFamilyInstanceV2 K R M δ εr Λz) ∧
        Lc09Out R.later.err.σcol R.later.scale.Λ R.later.scale.w M ∧ Lc18ExclusionOutV2 R M

/-- `ClosedFamilyAtV2` with the PARTIAL instance: prefix witness functions `εr, δ', Λz` and the
chain on every staged register. -/
def PartialClosedFamilyAtV2 (K : ℕ) (Wseq : ℕ → CompactCarrier.{u})
    (gseq : ∀ m, SmoothRiemannianMetric (Wseq m).model (Wseq m).Carrier) {D : ClosedEarlyData}
    (T : ClosedThresholdsV2 D) : Prop :=
  ∃ εrF δ'F ΛzF : ClosedStage D → ClosedCircleRequestsV2 → ClosedExclusions → ClosedErrorsV2 →
      ClosedScales → ℝ → ℝ → ℝ,
    ∀ R : ClosedRegisterV2 D T,
      PartialClosedFamilyOnTailV2 K Wseq gseq R
        (εrF R.stage R.later.circle R.later.excl R.later.err R.later.scale R.later.split.b
          R.later.split.β₁)
        (δ'F R.stage R.later.circle R.later.excl R.later.err R.later.scale R.later.split.b
          R.later.split.β₁)
        (ΛzF R.stage R.later.circle R.later.excl R.later.err R.later.scale R.later.split.b
          R.later.split.β₁)

/-- **The joint package forgets to its partial form.** -/
theorem ClosedFamilyAtV2.toPartial_VAL3 {K : ℕ} {Wseq : ℕ → CompactCarrier.{u}}
    {gseq : ∀ m, SmoothRiemannianMetric (Wseq m).model (Wseq m).Carrier} {D : ClosedEarlyData}
    {T : ClosedThresholdsV2 D} (h : ClosedFamilyAtV2 K Wseq gseq T) :
    PartialClosedFamilyAtV2 K Wseq gseq T := by
  obtain ⟨εrF, δ'F, ΛzF, h⟩ := h
  refine ⟨εrF, δ'F, ΛzF, fun R => ?_⟩
  obtain ⟨h1, h2, h3, h4, h5, h6, δ, hδ, hδδ', ht⟩ := h R
  exact ⟨h1, h2, h3, h4, h5, h6, δ, hδ, hδδ', fun m hm =>
    (ht m hm).imp fun _ hM => ⟨hM.1.map ClosedFamilyInstanceV2.toPartial_VAL3, hM.2⟩⟩

/-- **`T` refines `U`**: `T` agrees with `U` on `N_b, c_w, I₁, L_max`'s request and the endpoint
slot, every upper slot of `T` is below `U`'s and every lower slot above it (so that every register
at `T` meets `U`'s requests, apart from `V` and `H`). -/
structure ClosedStrategyRefinesV2 {D : ClosedEarlyData} (T U : ClosedThresholdsV2 D) : Prop where
  Nb_eq : T.Nb = U.Nb
  cw_eq : T.cw = U.cw
  I₁_eq : T.I₁ = U.I₁
  LmaxLow_eq : T.LmaxLow = U.LmaxLow
  endpointUp_eq : T.endpointUp = U.endpointUp
  circleUp_le : ∀ st θs θe θ₂, T.circleUp st θs θe θ₂ ≤ U.circleUp st θs θe θ₂
  lc18_le : T.lc18 ≤ U.lc18
  β₂Up_le : ∀ st ci β₃, T.β₂Up st ci β₃ ≤ U.β₂Up st ci β₃
  ΔLow_ge : ∀ st ci β₃ β₂, U.ΔLow st ci β₃ β₂ ≤ T.ΔLow st ci β₃ β₂
  errorsUp_le : ∀ st ci ex, T.errorsUp st ci ex ≤ U.errorsUp st ci ex
  sectionUp_le : ∀ st ci ex co, T.sectionUp st ci ex co ≤ U.sectionUp st ci ex co
  lfr29W_le : ∀ st ci ex co bd, T.lfr29W st ci ex co bd ≤ U.lfr29W st ci ex co bd
  σcolUp_le : ∀ st ci ex co bd wk s, T.σcolUp st ci ex co bd wk s ≤ U.σcolUp st ci ex co bd wk s
  scaleUp_le : ∀ st ci ex er, T.scaleUp st ci ex er ≤ U.scaleUp st ci ex er
  wUp_le : ∀ st ci ex er Λ, T.wUp st ci ex er Λ ≤ U.wUp st ci ex er Λ
  splitUp_le : ∀ st ci ex er sc, T.splitUp st ci ex er sc ≤ U.splitUp st ci ex er sc
  β₁Up_le : ∀ st ci ex er sc b, T.β₁Up st ci ex er sc b ≤ U.β₁Up st ci ex er sc b
  T₀Low_ge : ∀ st ci ex er sc b β₁, U.T₀Low st ci ex er sc b β₁ ≤ T.T₀Low st ci ex er sc b β₁
  tailLow_ge : ∀ st ci ex er sc sp Lmax,
    U.tailLow st ci ex er sc sp Lmax ≤ T.tailLow st ci ex er sc sp Lmax

/-- **The closed realization** (review 52, order of work step 3, PARTIAL): for every threshold
strategy `U` there is a common strategy `T` refining it (the C14 producer's Skolem thresholds and
LC09's `w₀` added slot by slot), with `H m = m + 2` and LC18's obstruction, such that EVERY staged
register at `T` is realized: prefix witnesses `εr < cap`, `δ'`, `Λz` with `20Λz ≤ T₀Low`, one cone
error `δ < δ'`, and on every member of the register's tail a normalized model carrying the final
family `LocalChartPacketsC14` with exactly the register's values, LC09 at `σ_col` and LC18's
exclusion. Missing (PARTIAL): LPA02's joint witness and the zero-ball selection. -/
theorem exists_closed_realization_VAL3 (K : ℕ) (hK : 10 ≤ K) (A : ℝ → ℝ)
    (hA : ∀ x, 0 < x → 0 < A x) (Wseq : ℕ → CompactCarrier.{u})
    (gseq : ∀ m, SmoothRiemannianMetric (Wseq m).model (Wseq m).Carrier)
    (hf : ∀ m, ClosedMemberFacts (Wseq m))
    (hg : ∀ m, closedCollapseHypotheses (Wseq m) (gseq m) K A (closedCounterexampleRatio (m + 2)))
    {D : ClosedEarlyData} (U : ClosedThresholdsV2 D) :
    ∃ T : ClosedThresholdsV2 D, ClosedStrategyRefinesV2 T U ∧ (∀ m, T.H m = (m : ℝ) + 2) ∧
      T.lc18 ≤ threeSplittingExclusionThreshold.{0, 0} ∧ PartialClosedFamilyAtV2 K Wseq gseq T := by
  classical
  obtain ⟨M, hst, hder, hor⟩ := exists_closedModel_sequence_VAL3 K A Wseq gseq hf hg
  have htend : Tendsto (fun m : ℕ => (m : ℝ) + 2) atTop atTop :=
    tendsto_atTop_add_const_right _ 2 tendsto_natCast_atTop_atTop
  have hP := eventually_nonempty_localChartPacketsC14 K hK (boundaryDerivativeConstant A K)
    (fun C v _ hv _ => boundaryDerivativeConstant_pos_VAL3 hA C v hv)
  obtain ⟨a₂, ha₂, hP⟩ := hP
  let C1 : ℝ → Prop := fun γ =>
    0 < γ ∧ γ < 1 / 10
  have hP1 : ∀ (γ : ℝ) (hc : C1 γ), _ := fun γ hc =>
    hP γ hc.1 hc.2
  choose β₀ hβ₀ hβ₀a hP using hP1
  let B0 : ℝ → ℝ := fun γ =>
    if hc : C1 γ then β₀ γ hc else 1
  have B0_pos : ∀ (γ : ℝ), 0 < B0 γ := fun γ => by
    by_cases hc : C1 γ
    · rw [show B0 γ = β₀ γ hc from dite_eq_left hc]
      exact hβ₀ γ hc
    · rw [show B0 γ = 1 from dite_eq_right hc]
      exact one_pos
  let C2 : ℝ → ℝ → ℝ → Prop := fun γ βc γc =>
    C1 γ ∧ (0 < βc ∧ βc < γc / 1000 ∧ 0 < γc ∧ γc < 1 / 100)
  have hP2 : ∀ (γ βc γc : ℝ) (hc : C2 γ βc γc), _ := fun γ βc γc hc =>
    hP γ hc.1 βc γc hc.2.1 hc.2.2.1 hc.2.2.2.1 hc.2.2.2.2
  choose σ₀ hσ₀ Δ₀ hΔ₀ hP using hP2
  let S0 : ℝ → ℝ → ℝ → ℝ := fun γ βc γc =>
    if hc : C2 γ βc γc then σ₀ γ βc γc hc else 1
  have S0_pos : ∀ (γ βc γc : ℝ), 0 < S0 γ βc γc := fun γ βc γc => by
    by_cases hc : C2 γ βc γc
    · rw [show S0 γ βc γc = σ₀ γ βc γc hc from dite_eq_left hc]
      exact hσ₀ γ βc γc hc
    · rw [show S0 γ βc γc = 1 from dite_eq_right hc]
      exact one_pos
  let D0 : ℝ → ℝ → ℝ → ℝ := fun γ βc γc =>
    if hc : C2 γ βc γc then Δ₀ γ βc γc hc else 1
  have D0_pos : ∀ (γ βc γc : ℝ), 0 < D0 γ βc γc := fun γ βc γc => by
    by_cases hc : C2 γ βc γc
    · rw [show D0 γ βc γc = Δ₀ γ βc γc hc from dite_eq_left hc]
      exact hΔ₀ γ βc γc hc
    · rw [show D0 γ βc γc = 1 from dite_eq_right hc]
      exact one_pos
  let C3 : ℝ → ℝ → ℝ → ℝ → ℝ → Prop := fun γ βc γc β₂ Δ =>
    C2 γ βc γc ∧ (0 < β₂ ∧ β₂ ≤ B0 γ ∧ β₂ < 1 / 100 ∧ 100 / β₂ < Δ ∧ D0 γ βc γc ≤ Δ)
  have hP3 : ∀ (γ βc γc β₂ Δ : ℝ) (hc : C3 γ βc γc β₂ Δ), _ := fun γ βc γc β₂ Δ hc =>
    hP γ βc γc hc.1 β₂ Δ hc.2.1 ((hc.2.2.1).trans_eq (dite_eq_left hc.1.1)) hc.2.2.2.1 hc.2.2.2.2.1
        ((dite_eq_left hc.1).symm.trans_le (hc.2.2.2.2.2))
  choose τ₀ hτ₀ bc₀ hbc₀ hP using hP3
  let T0 : ℝ → ℝ → ℝ → ℝ → ℝ → ℝ := fun γ βc γc β₂ Δ =>
    if hc : C3 γ βc γc β₂ Δ then τ₀ γ βc γc β₂ Δ hc else 1
  have T0_pos : ∀ (γ βc γc β₂ Δ : ℝ), 0 < T0 γ βc γc β₂ Δ := fun γ βc γc β₂ Δ => by
    by_cases hc : C3 γ βc γc β₂ Δ
    · rw [show T0 γ βc γc β₂ Δ = τ₀ γ βc γc β₂ Δ hc from dite_eq_left hc]
      exact hτ₀ γ βc γc β₂ Δ hc
    · rw [show T0 γ βc γc β₂ Δ = 1 from dite_eq_right hc]
      exact one_pos
  let BC : ℝ → ℝ → ℝ → ℝ → ℝ → ℝ := fun γ βc γc β₂ Δ =>
    if hc : C3 γ βc γc β₂ Δ then bc₀ γ βc γc β₂ Δ hc else 1
  have BC_pos : ∀ (γ βc γc β₂ Δ : ℝ), 0 < BC γ βc γc β₂ Δ := fun γ βc γc β₂ Δ => by
    by_cases hc : C3 γ βc γc β₂ Δ
    · rw [show BC γ βc γc β₂ Δ = bc₀ γ βc γc β₂ Δ hc from dite_eq_left hc]
      exact hbc₀ γ βc γc β₂ Δ hc
    · rw [show BC γ βc γc β₂ Δ = 1 from dite_eq_right hc]
      exact one_pos
  let C4 : ℝ → ℝ → ℝ → ℝ → ℝ → ℝ → ℝ → ℝ → ℝ → ℝ → ℝ → ℝ → Prop := fun γ βc γc β₂ Δ σc ε μ τ s b' s'
      =>
    C3 γ βc γc β₂ Δ ∧ (0 < σc ∧ σc ≤ S0 γ βc γc ∧ σc < 1 ∧ 0 < ε ∧ ε < 1 / 100 ∧ 0 < μ ∧ μ ≤ 1 /
        1000000 ∧ 0 < τ ∧ τ ≤ T0 γ βc γc β₂ Δ ∧ 140 * Real.sqrt τ < ε ^ 2 / 20 ∧ ε ≤ 1 / 10 ^ 8 ∧ μ
        ≤ 1 / 10 ^ 8) ∧ (0 < s ∧ s < 1 / 100 ∧ s < b' / 100000 ∧ s < s' / 100000 ∧ b' < 1 / (1000000
        * Δ) ∧ s' < 1 / (1000000 * Δ) ∧ b' < τ * Δ / 1000000000 ∧ s' < τ * Δ / 1000000000)
  have hP4 : ∀ (γ βc γc β₂ Δ σc ε μ τ s b' s' : ℝ) (hc : C4 γ βc γc β₂ Δ σc ε μ τ s b' s'), _ := fun
      γ βc γc β₂ Δ σc ε μ τ s b' s' hc =>
    hP γ βc γc β₂ Δ hc.1 σc ε μ τ hc.2.1.1 ((hc.2.1.2.1).trans_eq (dite_eq_left hc.1.1))
        hc.2.1.2.2.1 hc.2.1.2.2.2.1 hc.2.1.2.2.2.2.1 hc.2.1.2.2.2.2.2.1 hc.2.1.2.2.2.2.2.2.1
        hc.2.1.2.2.2.2.2.2.2.1 ((hc.2.1.2.2.2.2.2.2.2.2.1).trans_eq (dite_eq_left hc.1))
        hc.2.1.2.2.2.2.2.2.2.2.2.1 hc.2.1.2.2.2.2.2.2.2.2.2.2.1 hc.2.1.2.2.2.2.2.2.2.2.2.2.2 s b' s'
        hc.2.2.1 hc.2.2.2.1 hc.2.2.2.2.1 hc.2.2.2.2.2.1 hc.2.2.2.2.2.2.1 hc.2.2.2.2.2.2.2.1
        hc.2.2.2.2.2.2.2.2.1 hc.2.2.2.2.2.2.2.2.2
  choose a₀ b₁ ha₀ hb₁ hP using hP4
  let A0 : ℝ → ℝ → ℝ → ℝ → ℝ → ℝ → ℝ → ℝ → ℝ → ℝ → ℝ → ℝ → ℝ := fun γ βc γc β₂ Δ σc ε μ τ s b' s' =>
    if hc : C4 γ βc γc β₂ Δ σc ε μ τ s b' s' then a₀ γ βc γc β₂ Δ σc ε μ τ s b' s' hc else 1
  have A0_pos : ∀ (γ βc γc β₂ Δ σc ε μ τ s b' s' : ℝ), 0 < A0 γ βc γc β₂ Δ σc ε μ τ s b' s' := fun γ
      βc γc β₂ Δ σc ε μ τ s b' s' => by
    by_cases hc : C4 γ βc γc β₂ Δ σc ε μ τ s b' s'
    · rw [show A0 γ βc γc β₂ Δ σc ε μ τ s b' s' = a₀ γ βc γc β₂ Δ σc ε μ τ s b' s' hc from
        dite_eq_left hc]
      exact ha₀ γ βc γc β₂ Δ σc ε μ τ s b' s' hc
    · rw [show A0 γ βc γc β₂ Δ σc ε μ τ s b' s' = 1 from dite_eq_right hc]
      exact one_pos
  let B1 : ℝ → ℝ → ℝ → ℝ → ℝ → ℝ → ℝ → ℝ → ℝ → ℝ → ℝ → ℝ → ℝ := fun γ βc γc β₂ Δ σc ε μ τ s b' s' =>
    if hc : C4 γ βc γc β₂ Δ σc ε μ τ s b' s' then b₁ γ βc γc β₂ Δ σc ε μ τ s b' s' hc else 1
  have B1_pos : ∀ (γ βc γc β₂ Δ σc ε μ τ s b' s' : ℝ), 0 < B1 γ βc γc β₂ Δ σc ε μ τ s b' s' := fun γ
      βc γc β₂ Δ σc ε μ τ s b' s' => by
    by_cases hc : C4 γ βc γc β₂ Δ σc ε μ τ s b' s'
    · rw [show B1 γ βc γc β₂ Δ σc ε μ τ s b' s' = b₁ γ βc γc β₂ Δ σc ε μ τ s b' s' hc from
        dite_eq_left hc]
      exact hb₁ γ βc γc β₂ Δ σc ε μ τ s b' s' hc
    · rw [show B1 γ βc γc β₂ Δ σc ε μ τ s b' s' = 1 from dite_eq_right hc]
      exact one_pos
  let C5 : ℝ → ℝ → ℝ → ℝ → ℝ → ℝ → ℝ → ℝ → ℝ → ℝ → ℝ → ℝ → ℝ → ℝ → Prop := fun γ βc γc β₂ Δ σc ε μ τ
      s b' s' σ Λ =>
    C4 γ βc γc β₂ Δ σc ε μ τ s b' s' ∧ (0 < σ ∧ σ ≤ a₂ ∧ σ ≤ threeSplittingExclusionThreshold.{0, 0}
        ∧ σ ≤ A0 γ βc γc β₂ Δ σc ε μ τ s b' s') ∧ (0 < Λ ∧ Δ * Λ * 2000000 ≤ 1 / 100 ∧ Λ < 1 /
        (1000000 * Δ) ∧ 100 * Δ * Λ ≤ 1 / 1000000 ∧ 2 * ε + 300 * Δ * Λ + Real.sqrt (504000 / Δ +
        3780 * τ) < γc / 1000 ∧ Λ < s' / (100000000 * Δ ^ 2) ∧ 100 * Δ * Λ ≤ 1 / 10 ^ 8)
  have hP5 : ∀ (γ βc γc β₂ Δ σc ε μ τ s b' s' σ Λ : ℝ) (hc : C5 γ βc γc β₂ Δ σc ε μ τ s b' s' σ Λ),
      _ := fun γ βc γc β₂ Δ σc ε μ τ s b' s' σ Λ hc =>
    hP γ βc γc β₂ Δ σc ε μ τ s b' s' hc.1 σ hc.2.1.1 hc.2.1.2.1 hc.2.1.2.2.1
        ((hc.2.1.2.2.2).trans_eq (dite_eq_left hc.1)) Λ hc.2.2.1 hc.2.2.2.1 hc.2.2.2.2.1
        hc.2.2.2.2.2.1 hc.2.2.2.2.2.2.1 hc.2.2.2.2.2.2.2.1 hc.2.2.2.2.2.2.2.2
  choose w₀ hw₀ hP using hP5
  let W0 : ℝ → ℝ → ℝ → ℝ → ℝ → ℝ → ℝ → ℝ → ℝ → ℝ → ℝ → ℝ → ℝ → ℝ → ℝ := fun γ βc γc β₂ Δ σc ε μ τ s
      b' s' σ Λ =>
    if hc : C5 γ βc γc β₂ Δ σc ε μ τ s b' s' σ Λ then w₀ γ βc γc β₂ Δ σc ε μ τ s b' s' σ Λ hc else 1
  have W0_pos : ∀ (γ βc γc β₂ Δ σc ε μ τ s b' s' σ Λ : ℝ), 0 < W0 γ βc γc β₂ Δ σc ε μ τ s b' s' σ Λ
      := fun γ βc γc β₂ Δ σc ε μ τ s b' s' σ Λ => by
    by_cases hc : C5 γ βc γc β₂ Δ σc ε μ τ s b' s' σ Λ
    · rw [show W0 γ βc γc β₂ Δ σc ε μ τ s b' s' σ Λ = w₀ γ βc γc β₂ Δ σc ε μ τ s b' s' σ Λ hc from
        dite_eq_left hc]
      exact hw₀ γ βc γc β₂ Δ σc ε μ τ s b' s' σ Λ hc
    · rw [show W0 γ βc γc β₂ Δ σc ε μ τ s b' s' σ Λ = 1 from dite_eq_right hc]
      exact one_pos
  let C6 : ℝ → ℝ → ℝ → ℝ → ℝ → ℝ → ℝ → ℝ → ℝ → ℝ → ℝ → ℝ → ℝ → ℝ → ℝ → Prop := fun γ βc γc β₂ Δ σc ε
      μ τ s b' s' σ Λ w =>
    C5 γ βc γc β₂ Δ σc ε μ τ s b' s' σ Λ ∧ (0 < w ∧ w < W0 γ βc γc β₂ Δ σc ε μ τ s b' s' σ Λ ∧ w < 4
        * Real.pi / 3)
  have hP6 : ∀ (γ βc γc β₂ Δ σc ε μ τ s b' s' σ Λ w : ℝ) (hc : C6 γ βc γc β₂ Δ σc ε μ τ s b' s' σ Λ
      w), _ := fun γ βc γc β₂ Δ σc ε μ τ s b' s' σ Λ w hc =>
    hP γ βc γc β₂ Δ σc ε μ τ s b' s' σ Λ hc.1 w hc.2.1 ((hc.2.2.1).trans_eq (dite_eq_left hc.1))
        hc.2.2.2
  choose bd₀ hbd₀ hP using hP6
  let BD : ℝ → ℝ → ℝ → ℝ → ℝ → ℝ → ℝ → ℝ → ℝ → ℝ → ℝ → ℝ → ℝ → ℝ → ℝ → ℝ := fun γ βc γc β₂ Δ σc ε μ
      τ s b' s' σ Λ w =>
    if hc : C6 γ βc γc β₂ Δ σc ε μ τ s b' s' σ Λ w then bd₀ γ βc γc β₂ Δ σc ε μ τ s b' s' σ Λ w hc
        else 1
  have BD_pos : ∀ (γ βc γc β₂ Δ σc ε μ τ s b' s' σ Λ w : ℝ), 0 < BD γ βc γc β₂ Δ σc ε μ τ s b' s' σ
      Λ w := fun γ βc γc β₂ Δ σc ε μ τ s b' s' σ Λ w => by
    by_cases hc : C6 γ βc γc β₂ Δ σc ε μ τ s b' s' σ Λ w
    · rw [show BD γ βc γc β₂ Δ σc ε μ τ s b' s' σ Λ w = bd₀ γ βc γc β₂ Δ σc ε μ τ s b' s' σ Λ w hc
        from dite_eq_left hc]
      exact hbd₀ γ βc γc β₂ Δ σc ε μ τ s b' s' σ Λ w hc
    · rw [show BD γ βc γc β₂ Δ σc ε μ τ s b' s' σ Λ w = 1 from dite_eq_right hc]
      exact one_pos
  let C7 : ℝ → ℝ → ℝ → ℝ → ℝ → ℝ → ℝ → ℝ → ℝ → ℝ → ℝ → ℝ → ℝ → ℝ → ℝ → ℝ → ℝ → ℝ → Prop := fun γ βc
      γc β₂ Δ σc ε μ τ s b' s' σ Λ w b σs vs =>
    C6 γ βc γc β₂ Δ σc ε μ τ s b' s' σ Λ w ∧ (0 < b ∧ b < s / 100000 ∧ b < BC γ βc γc β₂ Δ ∧ b < B1
        γ βc γc β₂ Δ σc ε μ τ s b' s' ∧ 100 * Δ < b⁻¹ ∧ b < BD γ βc γc β₂ Δ σc ε μ τ s b' s' σ Λ w)
        ∧ (0 < σs ∧ σs ≤ 1 / 100 ∧ 0 < vs)
  have hP7 : ∀ (γ βc γc β₂ Δ σc ε μ τ s b' s' σ Λ w b σs vs : ℝ) (hc : C7 γ βc γc β₂ Δ σc ε μ τ s b'
      s' σ Λ w b σs vs), _ := fun γ βc γc β₂ Δ σc ε μ τ s b' s' σ Λ w b σs vs hc =>
    hP γ βc γc β₂ Δ σc ε μ τ s b' s' σ Λ w hc.1 b hc.2.1.1 hc.2.1.2.1 ((hc.2.1.2.2.1).trans_eq
        (dite_eq_left hc.1.1.1.1)) ((hc.2.1.2.2.2.1).trans_eq (dite_eq_left hc.1.1.1))
        hc.2.1.2.2.2.2.1 ((hc.2.1.2.2.2.2.2).trans_eq (dite_eq_left hc.1)) σs vs hc.2.2.1 hc.2.2.2.1
        hc.2.2.2.2
  choose b₀ hb₀ hP using hP7
  let BZ : ℝ → ℝ → ℝ → ℝ → ℝ → ℝ → ℝ → ℝ → ℝ → ℝ → ℝ → ℝ → ℝ → ℝ → ℝ → ℝ → ℝ → ℝ → ℝ := fun γ βc γc
      β₂ Δ σc ε μ τ s b' s' σ Λ w b σs vs =>
    if hc : C7 γ βc γc β₂ Δ σc ε μ τ s b' s' σ Λ w b σs vs then b₀ γ βc γc β₂ Δ σc ε μ τ s b' s' σ Λ
        w b σs vs hc else 1
  have BZ_pos : ∀ (γ βc γc β₂ Δ σc ε μ τ s b' s' σ Λ w b σs vs : ℝ), 0 < BZ γ βc γc β₂ Δ σc ε μ τ s
      b' s' σ Λ w b σs vs := fun γ βc γc β₂ Δ σc ε μ τ s b' s' σ Λ w b σs vs => by
    by_cases hc : C7 γ βc γc β₂ Δ σc ε μ τ s b' s' σ Λ w b σs vs
    · rw [show BZ γ βc γc β₂ Δ σc ε μ τ s b' s' σ Λ w b σs vs = b₀ γ βc γc β₂ Δ σc ε μ τ s b' s' σ Λ
        w b σs vs hc from dite_eq_left hc]
      exact hb₀ γ βc γc β₂ Δ σc ε μ τ s b' s' σ Λ w b σs vs hc
    · rw [show BZ γ βc γc β₂ Δ σc ε μ τ s b' s' σ Λ w b σs vs = 1 from dite_eq_right hc]
      exact one_pos
  let C8 : ℝ → ℝ → ℝ → ℝ → ℝ → ℝ → ℝ → ℝ → ℝ → ℝ → ℝ → ℝ → ℝ → ℝ → ℝ → ℝ → ℝ → ℝ → (ℕ → ℝ) → ℝ → ℝ →
      Prop := fun γ βc γc β₂ Δ σc ε μ τ s b' s' σ Λ w b σs vs β ζ cap =>
    C7 γ βc γc β₂ Δ σc ε μ τ s b' s' σ Λ w b σs vs ∧ (β 2 = β₂ ∧ 0 < β 1 ∧ β 1 < BZ γ βc γc β₂ Δ σc
        ε μ τ s b' s' σ Λ w b σs vs ∧ β 1 < 1 ∧ β 3 ≤ threeSplittingExclusionThreshold.{0, 0}) ∧ (β
        1 < ζ ∧ ζ < 1 ∧ 0 < cap)
  have hP8 : ∀ (γ βc γc β₂ Δ σc ε μ τ s b' s' σ Λ w b σs vs : ℝ) (β : ℕ → ℝ) (ζ cap : ℝ) (hc : C8 γ
      βc γc β₂ Δ σc ε μ τ s b' s' σ Λ w b σs vs β ζ cap), _ := fun γ βc γc β₂ Δ σc ε μ τ s b' s' σ Λ
      w b σs vs β ζ cap hc =>
    hP γ βc γc β₂ Δ σc ε μ τ s b' s' σ Λ w b σs vs hc.1 β hc.2.1.1 hc.2.1.2.1
        ((hc.2.1.2.2.1).trans_eq (dite_eq_left hc.1)) hc.2.1.2.2.2.1 hc.2.1.2.2.2.2 ζ cap hc.2.2.1
        hc.2.2.2.1 hc.2.2.2.2
  choose εr δ' Λ' hεr hεr4 hεrcap hδ' hΛ' hP using hP8
  let ER : ℝ → ℝ → ℝ → ℝ → ℝ → ℝ → ℝ → ℝ → ℝ → ℝ → ℝ → ℝ → ℝ → ℝ → ℝ → ℝ → ℝ → ℝ → (ℕ → ℝ) → ℝ → ℝ →
      ℝ := fun γ βc γc β₂ Δ σc ε μ τ s b' s' σ Λ w b σs vs β ζ cap =>
    if hc : C8 γ βc γc β₂ Δ σc ε μ τ s b' s' σ Λ w b σs vs β ζ cap then εr γ βc γc β₂ Δ σc ε μ τ s
        b' s' σ Λ w b σs vs β ζ cap hc else 1
  have ER_pos : ∀ (γ βc γc β₂ Δ σc ε μ τ s b' s' σ Λ w b σs vs : ℝ) (β : ℕ → ℝ) (ζ cap : ℝ), 0 < ER
      γ βc γc β₂ Δ σc ε μ τ s b' s' σ Λ w b σs vs β ζ cap := fun γ βc γc β₂ Δ σc ε μ τ s b' s' σ Λ w
      b σs vs β ζ cap => by
    by_cases hc : C8 γ βc γc β₂ Δ σc ε μ τ s b' s' σ Λ w b σs vs β ζ cap
    · rw [show ER γ βc γc β₂ Δ σc ε μ τ s b' s' σ Λ w b σs vs β ζ cap = εr γ βc γc β₂ Δ σc ε μ τ s
        b' s' σ Λ w b σs vs β ζ cap hc from dite_eq_left hc]
      exact hεr γ βc γc β₂ Δ σc ε μ τ s b' s' σ Λ w b σs vs β ζ cap hc
    · rw [show ER γ βc γc β₂ Δ σc ε μ τ s b' s' σ Λ w b σs vs β ζ cap = 1 from dite_eq_right hc]
      exact one_pos
  let DP : ℝ → ℝ → ℝ → ℝ → ℝ → ℝ → ℝ → ℝ → ℝ → ℝ → ℝ → ℝ → ℝ → ℝ → ℝ → ℝ → ℝ → ℝ → (ℕ → ℝ) → ℝ → ℝ →
      ℝ := fun γ βc γc β₂ Δ σc ε μ τ s b' s' σ Λ w b σs vs β ζ cap =>
    if hc : C8 γ βc γc β₂ Δ σc ε μ τ s b' s' σ Λ w b σs vs β ζ cap then δ' γ βc γc β₂ Δ σc ε μ τ s
        b' s' σ Λ w b σs vs β ζ cap hc else 1
  have DP_pos : ∀ (γ βc γc β₂ Δ σc ε μ τ s b' s' σ Λ w b σs vs : ℝ) (β : ℕ → ℝ) (ζ cap : ℝ), 0 < DP
      γ βc γc β₂ Δ σc ε μ τ s b' s' σ Λ w b σs vs β ζ cap := fun γ βc γc β₂ Δ σc ε μ τ s b' s' σ Λ w
      b σs vs β ζ cap => by
    by_cases hc : C8 γ βc γc β₂ Δ σc ε μ τ s b' s' σ Λ w b σs vs β ζ cap
    · rw [show DP γ βc γc β₂ Δ σc ε μ τ s b' s' σ Λ w b σs vs β ζ cap = δ' γ βc γc β₂ Δ σc ε μ τ s
        b' s' σ Λ w b σs vs β ζ cap hc from dite_eq_left hc]
      exact hδ' γ βc γc β₂ Δ σc ε μ τ s b' s' σ Λ w b σs vs β ζ cap hc
    · rw [show DP γ βc γc β₂ Δ σc ε μ τ s b' s' σ Λ w b σs vs β ζ cap = 1 from dite_eq_right hc]
      exact one_pos
  let LZ : ℝ → ℝ → ℝ → ℝ → ℝ → ℝ → ℝ → ℝ → ℝ → ℝ → ℝ → ℝ → ℝ → ℝ → ℝ → ℝ → ℝ → ℝ → (ℕ → ℝ) → ℝ → ℝ →
      ℝ := fun γ βc γc β₂ Δ σc ε μ τ s b' s' σ Λ w b σs vs β ζ cap =>
    if hc : C8 γ βc γc β₂ Δ σc ε μ τ s b' s' σ Λ w b σs vs β ζ cap then Λ' γ βc γc β₂ Δ σc ε μ τ s
        b' s' σ Λ w b σs vs β ζ cap hc else 1
  have LZ_pos : ∀ (γ βc γc β₂ Δ σc ε μ τ s b' s' σ Λ w b σs vs : ℝ) (β : ℕ → ℝ) (ζ cap : ℝ), 0 < LZ
      γ βc γc β₂ Δ σc ε μ τ s b' s' σ Λ w b σs vs β ζ cap := fun γ βc γc β₂ Δ σc ε μ τ s b' s' σ Λ w
      b σs vs β ζ cap => by
    by_cases hc : C8 γ βc γc β₂ Δ σc ε μ τ s b' s' σ Λ w b σs vs β ζ cap
    · rw [show LZ γ βc γc β₂ Δ σc ε μ τ s b' s' σ Λ w b σs vs β ζ cap = Λ' γ βc γc β₂ Δ σc ε μ τ s
        b' s' σ Λ w b σs vs β ζ cap hc from dite_eq_left hc]
      exact hΛ' γ βc γc β₂ Δ σc ε μ τ s b' s' σ Λ w b σs vs β ζ cap hc
    · rw [show LZ γ βc γc β₂ Δ σc ε μ τ s b' s' σ Λ w b σs vs β ζ cap = 1 from dite_eq_right hc]
      exact one_pos
  let C9 : ℝ → ℝ → ℝ → ℝ → ℝ → ℝ → ℝ → ℝ → ℝ → ℝ → ℝ → ℝ → ℝ → ℝ → ℝ → ℝ → ℝ → ℝ → (ℕ → ℝ) → ℝ → ℝ →
      ℝ → ℝ → Prop := fun γ βc γc β₂ Δ σc ε μ τ s b' s' σ Λ w b σs vs β ζ cap T e =>
    C8 γ βc γc β₂ Δ σc ε μ τ s b' s' σ Λ w b σs vs β ζ cap ∧ (0 < T ∧ 20 * LZ γ βc γc β₂ Δ σc ε μ τ
        s b' s' σ Λ w b σs vs β ζ cap ≤ T) ∧ (0 < e ∧ e < 1 / 40)
  have hP9 : ∀ (γ βc γc β₂ Δ σc ε μ τ s b' s' σ Λ w b σs vs : ℝ) (β : ℕ → ℝ) (ζ cap T e : ℝ) (hc :
      C9 γ βc γc β₂ Δ σc ε μ τ s b' s' σ Λ w b σs vs β ζ cap T e), _ := fun γ βc γc β₂ Δ σc ε μ τ s
      b' s' σ Λ w b σs vs β ζ cap T e hc =>
    hP γ βc γc β₂ Δ σc ε μ τ s b' s' σ Λ w b σs vs β ζ cap hc.1 T hc.2.1.1 ((congrArg (fun x => 20 *
        x) (dite_eq_left hc.1)).symm.trans_le (hc.2.1.2)) e hc.2.2.1 hc.2.2.2 (fun m => (M m).X)
        (fun m => (M m).gX) (fun m => (M m).hmetric) (fun m => (m : ℝ) + 2) htend hst hder (fun m =>
        Classical.choice (hor m))
  choose V hV δ hδ hδδ' hev using hP9
  have hL : ∀ (σ Λ : ℝ) (hc : 0 < σ ∧ σ < 1 ∧ 0 < Λ), _ := fun σ Λ hc =>
    eventually_lc09Out_VAL.{u} hc.1 hc.2.1 hc.2.2
  choose wL hwL hL using hL
  let WL : ℝ → ℝ → ℝ := fun σ Λ => if hc : 0 < σ ∧ σ < 1 ∧ 0 < Λ then wL σ Λ hc else 1
  have WL_pos : ∀ σ Λ : ℝ, 0 < WL σ Λ := fun σ Λ => by
    by_cases hc : 0 < σ ∧ σ < 1 ∧ 0 < Λ
    · rw [show WL σ Λ = wL σ Λ hc from dite_eq_left hc]
      exact hwL σ Λ hc
    · rw [show WL σ Λ = 1 from dite_eq_right hc]
      exact one_pos
  let VV : ℝ → ℝ → ℝ → ℝ → ℝ → ℝ → ℝ → ℝ → ℝ → ℝ → ℝ → ℝ → ℝ → ℝ → ℝ → ℝ → ℝ → ℝ → (ℕ → ℝ) → ℝ → ℝ →
      ℝ → ℝ → ℝ := fun γ βc γc β₂ Δ σc ε μ τ s b' s' σ Λ w b σs vs β ζ cap T e =>
    if hc : C9 γ βc γc β₂ Δ σc ε μ τ s b' s' σ Λ w b σs vs β ζ cap T e then V γ βc γc β₂ Δ σc ε μ τ
        s b' s' σ Λ w b σs vs β ζ cap T e hc else T
  let DD : ℝ → ℝ → ℝ → ℝ → ℝ → ℝ → ℝ → ℝ → ℝ → ℝ → ℝ → ℝ → ℝ → ℝ → ℝ → ℝ → ℝ → ℝ → (ℕ → ℝ) → ℝ → ℝ →
      ℝ → ℝ → ℝ := fun γ βc γc β₂ Δ σc ε μ τ s b' s' σ Λ w b σs vs β ζ cap T e =>
    if hc : C9 γ βc γc β₂ Δ σc ε μ τ s b' s' σ Λ w b σs vs β ζ cap T e then δ γ βc γc β₂ Δ σc ε μ τ
        s b' s' σ Λ w b σs vs β ζ cap T e hc else 1
  let CT : ℝ → ℝ → ℝ → ℝ → ℝ → ℝ → ℝ → ℝ → ℝ → ℝ → ℝ → ℝ → ℝ → ℝ → ℝ → ℝ → ℝ → ℝ → (ℕ → ℝ) → ℝ → ℝ →
      ℝ → ℝ → ℝ → Prop := fun γ βc γc β₂ Δ σc ε μ τ s b' s' σ Λ w b σs vs β ζ cap T e Lmax =>
    C9 γ βc γc β₂ Δ σc ε μ τ s b' s' σ Λ w b σs vs β ζ cap T e ∧ 0 < Lmax ∧ (0 < σ ∧ σ < 1 ∧ 0 < Λ)
        ∧ 0 < w ∧ w < WL σ Λ ∧ w < 4 * Real.pi / 3
  have hTL : ∀ (γ βc γc β₂ Δ σc ε μ τ s b' s' σ Λ w b σs vs : ℝ) (β : ℕ → ℝ) (ζ cap T e : ℝ) (Lmax :
      ℝ) (hc : CT γ βc γc β₂ Δ σc ε μ τ s b' s' σ Λ w b σs vs β ζ cap T e Lmax), _ := fun γ βc γc β₂
      Δ σc ε μ τ s b' s' σ Λ w b σs vs β ζ cap T e Lmax hc =>
    Filter.eventually_atTop.mp ((hev γ βc γc β₂ Δ σc ε μ τ s b' s' σ Λ w b σs vs β ζ cap T e hc.1
        Lmax hc.2.1).and (hL σ Λ hc.2.2.1 w hc.2.2.2.1
      ((hc.2.2.2.2.1).trans_eq (dite_eq_left hc.2.2.1)) hc.2.2.2.2.2 Wseq gseq M (fun m => (m : ℝ) +
          2) htend hst))
  choose TLd hTLd using hTL
  let TL : ℝ → ℝ → ℝ → ℝ → ℝ → ℝ → ℝ → ℝ → ℝ → ℝ → ℝ → ℝ → ℝ → ℝ → ℝ → ℝ → ℝ → ℝ → (ℕ → ℝ) → ℝ → ℝ →
      ℝ → ℝ → ℝ → ℕ := fun γ βc γc β₂ Δ σc ε μ τ s b' s' σ Λ w b σs vs β ζ cap T e Lmax =>
    if hc : CT γ βc γc β₂ Δ σc ε μ τ s b' s' σ Λ w b σs vs β ζ cap T e Lmax then TLd γ βc γc β₂ Δ σc
        ε μ τ s b' s' σ Λ w b σs vs β ζ cap T e Lmax hc else 0
  have hthr : (0 : ℝ) < threeSplittingExclusionThreshold.{0, 0} :=
      threeSplittingExclusionThreshold_pos
  refine ⟨{
    Nb := U.Nb, Nb_nonneg := U.Nb_nonneg, cw := U.cw, cw_nonneg := U.cw_nonneg
    circleUp := fun st θs θe θ₂ => min (U.circleUp st θs θe θ₂) (1 / 100)
    circleUp_pos := fun st θs θe θ₂ => lt_min (U.circleUp_pos st θs θe θ₂) (by norm_num)
    lc18 := min U.lc18 threeSplittingExclusionThreshold.{0, 0}
    lc18_pos := lt_min U.lc18_pos hthr
    β₂Up := fun st ci β₃ => min (U.β₂Up st ci β₃) (B0 ci.γ)
    β₂Up_pos := fun st ci β₃ => lt_min (U.β₂Up_pos st ci β₃) (B0_pos ci.γ)
    ΔLow := fun st ci β₃ β₂ => max (U.ΔLow st ci β₃ β₂) (max (D0 ci.γ ci.βc ci.γc) (504000 * (4000 /
        ci.γc) ^ 2))
    errorsUp := fun st ci ex => min (U.errorsUp st ci ex) (min (S0 ci.γ ci.βc ci.γc) (min (1 / 10 ^
        10) (posOr_VAL3 (ci.γc / 8000))))
    errorsUp_pos := fun st ci ex => lt_min (U.errorsUp_pos st ci ex) (lt_min (S0_pos _ _ _) (lt_min
        (by norm_num) (posOr_pos_VAL3 _)))
    sectionUp := fun st ci ex co => min (U.sectionUp st ci ex co) (min (T0 ci.γ ci.βc ci.γc ex.β₂
        ex.Δ) (min (posOr_VAL3 ((co.ε ^ 2 / 2800) ^ 2)) (posOr_VAL3 ((ci.γc / 4000) ^ 2 / 3780))))
    sectionUp_pos := fun st ci ex co => lt_min (U.sectionUp_pos st ci ex co) (lt_min (T0_pos _ _ _ _
        _) (lt_min (posOr_pos_VAL3 _) (posOr_pos_VAL3 _)))
    lfr29W := fun st ci ex co bd => min (U.lfr29W st ci ex co bd) (min (posOr_VAL3 (1 / (1000000 *
        ex.Δ))) (posOr_VAL3 (bd.τ * ex.Δ / 1000000000)))
    lfr29W_pos := fun st ci ex co bd => lt_min (U.lfr29W_pos st ci ex co bd) (lt_min (posOr_pos_VAL3
        _) (posOr_pos_VAL3 _))
    endpointUp := U.endpointUp, endpointUp_pos := U.endpointUp_pos
    σcolUp := fun st ci ex co bd wk s => min (U.σcolUp st ci ex co bd wk s) (min a₂ (min
        threeSplittingExclusionThreshold.{0, 0} (A0 ci.γ ci.βc ci.γc ex.β₂ ex.Δ co.qe co.ε bd.μ bd.τ
        s wk.b' wk.s')))
    σcolUp_pos := fun st ci ex co bd wk s => lt_min (U.σcolUp_pos st ci ex co bd wk s) (lt_min ha₂
        (lt_min hthr (A0_pos _ _ _ _ _ _ _ _ _ _ _ _)))
    I₁ := U.I₁, I₁_pos := U.I₁_pos
    scaleUp := fun st ci ex er => min (U.scaleUp st ci ex er) (posOr_VAL3 (ci.γc / (1200000 *
        ex.Δ)))
    scaleUp_pos := fun st ci ex er => lt_min (U.scaleUp_pos st ci ex er) (posOr_pos_VAL3 _)
    wUp := fun st ci ex er Λ => min (U.wUp st ci ex er Λ) (min (W0 ci.γ ci.βc ci.γc ex.β₂ ex.Δ
        er.co.qe er.co.ε er.bd.μ er.bd.τ er.s er.wk.b' er.wk.s' er.σcol Λ) (WL er.σcol Λ))
    wUp_pos := fun st ci ex er Λ => lt_min (U.wUp_pos st ci ex er Λ) (lt_min (W0_pos _ _ _ _ _ _ _ _
        _ _ _ _ _ _) (WL_pos _ _))
    splitUp := fun st ci ex er sc => min (U.splitUp st ci ex er sc) (min (posOr_VAL3 (er.s /
        100000)) (min (BC ci.γ ci.βc ci.γc ex.β₂ ex.Δ) (min (B1 ci.γ ci.βc ci.γc ex.β₂ ex.Δ er.co.qe
        er.co.ε er.bd.μ er.bd.τ er.s er.wk.b' er.wk.s') (min (posOr_VAL3 (1 / (100 * ex.Δ))) (BD
        ci.γ ci.βc ci.γc ex.β₂ ex.Δ er.co.qe er.co.ε er.bd.μ er.bd.τ er.s er.wk.b' er.wk.s' er.σcol
        sc.Λ sc.w)))))
    splitUp_pos := fun st ci ex er sc => lt_min (U.splitUp_pos st ci ex er sc) (lt_min
        (posOr_pos_VAL3 _) (lt_min (BC_pos _ _ _ _ _) (lt_min (B1_pos _ _ _ _ _ _ _ _ _ _ _ _)
        (lt_min (posOr_pos_VAL3 _) (BD_pos _ _ _ _ _ _ _ _ _ _ _ _ _ _ _)))))
    β₁Up := fun st ci ex er sc b => min (U.β₁Up st ci ex er sc b) (BZ ci.γ ci.βc ci.γc ex.β₂ ex.Δ
        er.co.qe er.co.ε er.bd.μ er.bd.τ er.s er.wk.b' er.wk.s' er.σcol sc.Λ sc.w b er.co.qs
        er.co.ve)
    β₁Up_pos := fun st ci ex er sc b => lt_min (U.β₁Up_pos st ci ex er sc b) (BZ_pos _ _ _ _ _ _ _ _
        _ _ _ _ _ _ _ _ _ _)
    T₀Low := fun st ci ex er sc b β₁ => max (U.T₀Low st ci ex er sc b β₁) (20 * LZ ci.γ ci.βc ci.γc
        ex.β₂ ex.Δ er.co.qe er.co.ε er.bd.μ er.bd.τ er.s er.wk.b' er.wk.s' er.σcol sc.Λ sc.w b
        er.co.qs er.co.ve (closedβV3 β₁ ex) er.co.ζ er.co.ε₀)
    lpa02V := fun _ ci ex er sc b β₁ T₀ => VV ci.γ ci.βc ci.γc ex.β₂ ex.Δ er.co.qe er.co.ε er.bd.μ
        er.bd.τ er.s er.wk.b' er.wk.s' er.σcol sc.Λ sc.w b er.co.qs er.co.ve (closedβV3 β₁ ex)
        er.co.ζ er.co.ε₀ T₀ er.co.e₀
    T₀_le_lpa02V := fun _ ci ex er sc b β₁ T₀ => by
      by_cases hc : C9 ci.γ ci.βc ci.γc ex.β₂ ex.Δ er.co.qe er.co.ε er.bd.μ er.bd.τ er.s er.wk.b'
          er.wk.s' er.σcol sc.Λ sc.w b er.co.qs er.co.ve (closedβV3 β₁ ex) er.co.ζ er.co.ε₀ T₀
          er.co.e₀
      · rw [show VV ci.γ ci.βc ci.γc ex.β₂ ex.Δ er.co.qe er.co.ε er.bd.μ er.bd.τ er.s er.wk.b'
          er.wk.s' er.σcol sc.Λ sc.w b er.co.qs er.co.ve (closedβV3 β₁ ex) er.co.ζ er.co.ε₀ T₀
          er.co.e₀ = V ci.γ ci.βc ci.γc ex.β₂ ex.Δ er.co.qe er.co.ε er.bd.μ er.bd.τ er.s er.wk.b'
          er.wk.s' er.σcol sc.Λ sc.w b er.co.qs er.co.ve (closedβV3 β₁ ex) er.co.ζ er.co.ε₀ T₀
          er.co.e₀ hc from dite_eq_left hc]
        exact hV _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ hc
      · rw [show VV ci.γ ci.βc ci.γc ex.β₂ ex.Δ er.co.qe er.co.ε er.bd.μ er.bd.τ er.s er.wk.b'
          er.wk.s' er.σcol sc.Λ sc.w b er.co.qs er.co.ve (closedβV3 β₁ ex) er.co.ζ er.co.ε₀ T₀
          er.co.e₀ = T₀ from dite_eq_right hc]
    LmaxLow := U.LmaxLow
    tailLow := fun st ci ex er sc sp Lmax => max (U.tailLow st ci ex er sc sp Lmax) (TL ci.γ ci.βc
        ci.γc ex.β₂ ex.Δ er.co.qe er.co.ε er.bd.μ er.bd.τ er.s er.wk.b' er.wk.s' er.σcol sc.Λ sc.w
        sp.b er.co.qs er.co.ve (closedβV3 sp.β₁ ex) er.co.ζ er.co.ε₀ sp.T₀ er.co.e₀ Lmax)
    H := fun m => (m : ℝ) + 2
    H_tendsto := htend }, ?_, fun _ => rfl, min_le_right _ _, ?_⟩
  · exact ⟨rfl, rfl, rfl, rfl, rfl, fun _ _ _ _ => min_le_left _ _, min_le_left _ _,
      fun _ _ _ => min_le_left _ _, fun _ _ _ _ => le_max_left _ _, fun _ _ _ => min_le_left _ _,
      fun _ _ _ _ => min_le_left _ _, fun _ _ _ _ _ => min_le_left _ _,
      fun _ _ _ _ _ _ _ => min_le_left _ _, fun _ _ _ _ => min_le_left _ _,
      fun _ _ _ _ _ => min_le_left _ _, fun _ _ _ _ _ => min_le_left _ _,
      fun _ _ _ _ _ _ => min_le_left _ _, fun _ _ _ _ _ _ _ => le_max_left _ _,
      fun _ _ _ _ _ _ _ => le_max_left _ _⟩
  unfold PartialClosedFamilyAtV2
  refine ⟨fun _ ci ex er sc b β₁ => ER ci.γ ci.βc ci.γc ex.β₂ ex.Δ er.co.qe er.co.ε er.bd.μ er.bd.τ
      er.s er.wk.b' er.wk.s' er.σcol sc.Λ sc.w b er.co.qs er.co.ve (closedβV3 β₁ ex) er.co.ζ
      er.co.ε₀, fun _ ci ex er sc b β₁ => DP ci.γ ci.βc ci.γc ex.β₂ ex.Δ er.co.qe er.co.ε er.bd.μ
      er.bd.τ er.s er.wk.b' er.wk.s' er.σcol sc.Λ sc.w b er.co.qs er.co.ve (closedβV3 β₁ ex) er.co.ζ
      er.co.ε₀,
    fun _ ci ex er sc b β₁ => LZ ci.γ ci.βc ci.γc ex.β₂ ex.Δ er.co.qe er.co.ε er.bd.μ er.bd.τ er.s
        er.wk.b' er.wk.s' er.σcol sc.Λ sc.w b er.co.qs er.co.ve (closedβV3 β₁ ex) er.co.ζ er.co.ε₀,
        fun R => ?_⟩
  have hΔ0 : 0 < R.later.excl.Δ := R.later.Δ_pos_VAL2
  have hγc0 : 0 < R.later.circle.γc := R.later.γc_pos
  have hε0 : 0 < R.later.err.co.ε := R.later.ε_pos
  have hτ0 : 0 < R.later.err.bd.τ := R.later.τ_pos
  have hε10 : R.later.err.co.ε < 1 / 10 ^ 10 :=
    R.later.ε_lt.trans_le ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _)))
  have hζ10 : R.later.err.co.ζ < 1 / 10 ^ 10 :=
    R.later.ζ_lt.trans_le ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _)))
  have hε8000 : R.later.err.co.ε < R.later.circle.γc / 8000 :=
    (R.later.ε_lt.trans_le ((min_le_right _ _).trans ((min_le_right _ _).trans
      (min_le_right _ _)))).trans_eq (posOr_eq_VAL3 (by positivity))
  have hroot : 504000 * (4000 / R.later.circle.γc) ^ 2 < R.later.excl.Δ :=
    (((le_max_right _ _).trans (le_max_right _ _)).trans ((le_max_right _ _).trans
      (le_max_right _ _))).trans_lt R.later.Δ_gt
  have hτε : R.later.err.bd.τ < (R.later.err.co.ε ^ 2 / 2800) ^ 2 :=
    (R.later.τ_lt.trans_le ((min_le_right _ _).trans ((min_le_right _ _).trans ((min_le_right _
        _).trans
      (min_le_left _ _))))).trans_eq (posOr_eq_VAL3 (by positivity))
  have hτγc : R.later.err.bd.τ < (R.later.circle.γc / 4000) ^ 2 / 3780 :=
    (R.later.τ_lt.trans_le ((min_le_right _ _).trans ((min_le_right _ _).trans ((min_le_right _
        _).trans
      (min_le_right _ _))))).trans_eq (posOr_eq_VAL3 (by positivity))
  have hΛγc : R.later.scale.Λ < R.later.circle.γc / (1200000 * R.later.excl.Δ) :=
    (R.later.Λ_lt.trans_le (min_le_right _ _)).trans_eq (posOr_eq_VAL3 (by positivity))
  have hβ1 : closedβV3 R.later.split.β₁ R.later.excl 1 = R.later.split.β₁ := by simp [closedβV3]
  have hβ2 : closedβV3 R.later.split.β₁ R.later.excl 2 = R.later.excl.β₂ := by simp [closedβV3]
  have hβ3 : closedβV3 R.later.split.β₁ R.later.excl 3 = R.later.excl.β₃ := by simp [closedβV3]
  have hb100 : R.later.split.b < 1 / (100 * R.later.excl.Δ) :=
    (R.later.b_lt.trans_le ((min_le_left _ _).trans ((min_le_right _ _).trans ((min_le_right _
        _).trans
      ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _))))))).trans_eq
      (posOr_eq_VAL3 (by positivity))
  have h1 : C1 R.later.circle.γ := ⟨R.later.γ_pos, R.later.γ_lt.trans_le
    (((min_le_right _ _).trans (min_le_right _ _)).trans (by norm_num))⟩
  have h2 : C2 R.later.circle.γ R.later.circle.βc R.later.circle.γc := ⟨h1, R.later.βc_pos,
      R.later.βc_lt_γc_VAL2, hγc0,
    R.later.γc_lt.trans_le (min_le_right _ _)⟩
  have h3 : C3 R.later.circle.γ R.later.circle.βc R.later.circle.γc R.later.excl.β₂ R.later.excl.Δ
      := ⟨h2, R.later.β₂_pos,
    (R.later.β₂_lt.trans_le ((min_le_left _ _).trans (min_le_right _ _))).le,
    R.later.β₂_lt_audit_VAL2.trans (by norm_num), R.later.hundred_div_β₂_lt_Δ_VAL2,
    (((le_max_left _ _).trans (le_max_right _ _)).trans ((le_max_right _ _).trans
      (le_max_right _ _))).trans R.later.Δ_gt.le⟩
  have h4 : C4 R.later.circle.γ R.later.circle.βc R.later.circle.γc R.later.excl.β₂ R.later.excl.Δ
      R.later.err.co.qe R.later.err.co.ε R.later.err.bd.μ R.later.err.bd.τ R.later.err.s
      R.later.err.wk.b' R.later.err.wk.s' := ⟨h3, ⟨R.later.qe_pos,
    (R.later.qe_lt.trans_le ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _
        _)))).le,
    R.later.qe_lt_one_VAL2, hε0, hε10.trans (by norm_num), R.later.μ_pos,
    (R.later.μ_lt_VAL2.trans (by norm_num)).le, hτ0,
    (R.later.τ_lt.trans_le ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _
        _)))).le,
    c14_tau_sqrt_FAM2b hε0 hτ0.le hτε, (hε10.trans (by norm_num)).le, R.later.μ_lt_VAL2.le⟩,
    R.later.s_pos, R.later.s_lt_audit_VAL2.trans (by norm_num), R.later.s_lt_b'_VAL2,
    R.later.s_lt_s'_VAL2,
    (R.later.b'_lt.trans_le ((min_le_left _ _).trans ((min_le_right _ _).trans (min_le_left _
        _)))).trans_eq
      (posOr_eq_VAL3 (by positivity)),
    (R.later.s'_lt.trans_le ((min_le_left _ _).trans ((min_le_right _ _).trans (min_le_left _
        _)))).trans_eq
      (posOr_eq_VAL3 (by positivity)),
    (R.later.b'_lt.trans_le ((min_le_left _ _).trans ((min_le_right _ _).trans (min_le_right _
        _)))).trans_eq
      (posOr_eq_VAL3 (by positivity)),
    (R.later.s'_lt.trans_le ((min_le_left _ _).trans ((min_le_right _ _).trans (min_le_right _
        _)))).trans_eq
      (posOr_eq_VAL3 (by positivity))⟩
  have hσlt := R.later.σcol_lt
  have h5 : C5 R.later.circle.γ R.later.circle.βc R.later.circle.γc R.later.excl.β₂ R.later.excl.Δ
      R.later.err.co.qe R.later.err.co.ε R.later.err.bd.μ R.later.err.bd.τ R.later.err.s
      R.later.err.wk.b' R.later.err.wk.s' R.later.err.σcol R.later.scale.Λ := ⟨h4,
      ⟨R.later.σcol_pos,
    (hσlt.trans_le ((min_le_left _ _).trans ((min_le_right _ _).trans (min_le_left _ _)))).le,
    (hσlt.trans_le ((min_le_left _ _).trans ((min_le_right _ _).trans ((min_le_right _ _).trans
      (min_le_left _ _))))).le,
    (hσlt.trans_le ((min_le_left _ _).trans ((min_le_right _ _).trans ((min_le_right _ _).trans
      (min_le_right _ _))))).le⟩,
    R.later.Λ_pos, by linarith [R.later.regScale_two],
    by
      have h := R.later.regScale_L
      unfold closedLongLength at h
      rw [lt_div_iff₀ (by positivity)]
      nlinarith,
    (R.later.regScale_100.trans (by norm_num)).le,
    c14_staged_budget_FAM2b hγc0 hε8000 hroot hΛγc hτ0.le hτγc,
    R.later.lfr29_Λ.trans_eq (by norm_num), R.later.regScale_100.le⟩
  have h6 : C6 R.later.circle.γ R.later.circle.βc R.later.circle.γc R.later.excl.β₂ R.later.excl.Δ
      R.later.err.co.qe R.later.err.co.ε R.later.err.bd.μ R.later.err.bd.τ R.later.err.s
      R.later.err.wk.b' R.later.err.wk.s' R.later.err.σcol R.later.scale.Λ R.later.scale.w := ⟨h5,
      R.later.w_pos,
    R.later.w_lt.trans_le ((min_le_left _ _).trans ((min_le_right _ _).trans (min_le_left _ _))),
    R.later.w_lt.trans_le (min_le_right _ _)⟩
  have hblt := R.later.b_lt
  have h7 : C7 R.later.circle.γ R.later.circle.βc R.later.circle.γc R.later.excl.β₂ R.later.excl.Δ
      R.later.err.co.qe R.later.err.co.ε R.later.err.bd.μ R.later.err.bd.τ R.later.err.s
      R.later.err.wk.b' R.later.err.wk.s' R.later.err.σcol R.later.scale.Λ R.later.scale.w
      R.later.split.b R.later.err.co.qs R.later.err.co.ve := ⟨h6, ⟨R.later.b_pos,
    (hblt.trans_le ((min_le_left _ _).trans ((min_le_right _ _).trans (min_le_left _ _)))).trans_eq
      (posOr_eq_VAL3 (by have := R.later.s_pos; positivity)),
    hblt.trans_le ((min_le_left _ _).trans ((min_le_right _ _).trans ((min_le_right _ _).trans
      (min_le_left _ _)))),
    hblt.trans_le ((min_le_left _ _).trans ((min_le_right _ _).trans ((min_le_right _ _).trans
      ((min_le_right _ _).trans (min_le_left _ _))))),
    by
      have hb0 := R.later.b_pos
      have hb' : R.later.split.b < (100 * R.later.excl.Δ)⁻¹ := hb100.trans_eq (one_div _)
      exact (lt_inv_comm₀ (by positivity) hb0).mpr hb',
    hblt.trans_le ((min_le_left _ _).trans ((min_le_right _ _).trans ((min_le_right _ _).trans
      ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_right _ _))))))⟩,
    R.later.qs_pos, R.later.qs_le_hundredth_VAL2, R.later.ve_pos⟩
  have h8 : C8 R.later.circle.γ R.later.circle.βc R.later.circle.γc R.later.excl.β₂ R.later.excl.Δ
      R.later.err.co.qe R.later.err.co.ε R.later.err.bd.μ R.later.err.bd.τ R.later.err.s
      R.later.err.wk.b' R.later.err.wk.s' R.later.err.σcol R.later.scale.Λ R.later.scale.w
      R.later.split.b R.later.err.co.qs R.later.err.co.ve (closedβV3 R.later.split.β₁ R.later.excl)
      R.later.err.co.ζ R.later.err.co.ε₀ := ⟨h7, ⟨hβ2, hβ1 ▸ R.later.β₁_pos,
    hβ1 ▸ R.later.β₁_lt.trans_le ((min_le_left _ _).trans (min_le_right _ _)),
    hβ1 ▸ R.later.β₁_lt_β₂_VAL2.trans (R.later.β₂_lt_audit_VAL2.trans (by norm_num)),
    hβ3 ▸ (R.later.β₃_lt.trans_le (min_le_right _ _)).le⟩,
    hβ1 ▸ R.later.β₁_lt_ζ_VAL2, hζ10.trans (by norm_num), R.later.ε₀_pos⟩
  have h9 : C9 R.later.circle.γ R.later.circle.βc R.later.circle.γc R.later.excl.β₂ R.later.excl.Δ
      R.later.err.co.qe R.later.err.co.ε R.later.err.bd.μ R.later.err.bd.τ R.later.err.s
      R.later.err.wk.b' R.later.err.wk.s' R.later.err.σcol R.later.scale.Λ R.later.scale.w
      R.later.split.b R.later.err.co.qs R.later.err.co.ve (closedβV3 R.later.split.β₁ R.later.excl)
      R.later.err.co.ζ R.later.err.co.ε₀ R.later.split.T₀ R.later.err.co.e₀ := ⟨h8,
      ⟨R.later.T₀_pos_VAL2,
    (le_max_right _ _).trans ((le_max_right _ _).trans R.later.T₀_ge)⟩,
    R.later.e₀_pos, R.later.e₀_lt_VAL2⟩
  have hCT : CT R.later.circle.γ R.later.circle.βc R.later.circle.γc R.later.excl.β₂ R.later.excl.Δ
      R.later.err.co.qe R.later.err.co.ε R.later.err.bd.μ R.later.err.bd.τ R.later.err.s
      R.later.err.wk.b' R.later.err.wk.s' R.later.err.σcol R.later.scale.Λ R.later.scale.w
      R.later.split.b R.later.err.co.qs R.later.err.co.ve (closedβV3 R.later.split.β₁ R.later.excl)
      R.later.err.co.ζ R.later.err.co.ε₀ R.later.split.T₀ R.later.err.co.e₀ R.later.Lmax := ⟨h9,
      R.later.Lmax_pos_VAL2,
    ⟨R.later.σcol_pos, R.later.σcol_lt_one_VAL2, R.later.Λ_pos⟩, R.later.w_pos,
    R.later.w_lt.trans_le ((min_le_left _ _).trans ((min_le_right _ _).trans (min_le_right _ _))),
    R.later.w_lt.trans_le (min_le_right _ _)⟩
  have eER : ER R.later.circle.γ R.later.circle.βc R.later.circle.γc R.later.excl.β₂ R.later.excl.Δ
      R.later.err.co.qe R.later.err.co.ε R.later.err.bd.μ R.later.err.bd.τ R.later.err.s
      R.later.err.wk.b' R.later.err.wk.s' R.later.err.σcol R.later.scale.Λ R.later.scale.w
      R.later.split.b R.later.err.co.qs R.later.err.co.ve (closedβV3 R.later.split.β₁ R.later.excl)
      R.later.err.co.ζ R.later.err.co.ε₀ = εr R.later.circle.γ R.later.circle.βc R.later.circle.γc
      R.later.excl.β₂ R.later.excl.Δ R.later.err.co.qe R.later.err.co.ε R.later.err.bd.μ
      R.later.err.bd.τ R.later.err.s R.later.err.wk.b' R.later.err.wk.s' R.later.err.σcol
      R.later.scale.Λ R.later.scale.w R.later.split.b R.later.err.co.qs R.later.err.co.ve (closedβV3
      R.later.split.β₁ R.later.excl) R.later.err.co.ζ R.later.err.co.ε₀ h8 := dite_eq_left h8
  have eDP : DP R.later.circle.γ R.later.circle.βc R.later.circle.γc R.later.excl.β₂ R.later.excl.Δ
      R.later.err.co.qe R.later.err.co.ε R.later.err.bd.μ R.later.err.bd.τ R.later.err.s
      R.later.err.wk.b' R.later.err.wk.s' R.later.err.σcol R.later.scale.Λ R.later.scale.w
      R.later.split.b R.later.err.co.qs R.later.err.co.ve (closedβV3 R.later.split.β₁ R.later.excl)
      R.later.err.co.ζ R.later.err.co.ε₀ = δ' R.later.circle.γ R.later.circle.βc R.later.circle.γc
      R.later.excl.β₂ R.later.excl.Δ R.later.err.co.qe R.later.err.co.ε R.later.err.bd.μ
      R.later.err.bd.τ R.later.err.s R.later.err.wk.b' R.later.err.wk.s' R.later.err.σcol
      R.later.scale.Λ R.later.scale.w R.later.split.b R.later.err.co.qs R.later.err.co.ve (closedβV3
      R.later.split.β₁ R.later.excl) R.later.err.co.ζ R.later.err.co.ε₀ h8 := dite_eq_left h8
  have eLZ : LZ R.later.circle.γ R.later.circle.βc R.later.circle.γc R.later.excl.β₂ R.later.excl.Δ
      R.later.err.co.qe R.later.err.co.ε R.later.err.bd.μ R.later.err.bd.τ R.later.err.s
      R.later.err.wk.b' R.later.err.wk.s' R.later.err.σcol R.later.scale.Λ R.later.scale.w
      R.later.split.b R.later.err.co.qs R.later.err.co.ve (closedβV3 R.later.split.β₁ R.later.excl)
      R.later.err.co.ζ R.later.err.co.ε₀ = Λ' R.later.circle.γ R.later.circle.βc R.later.circle.γc
      R.later.excl.β₂ R.later.excl.Δ R.later.err.co.qe R.later.err.co.ε R.later.err.bd.μ
      R.later.err.bd.τ R.later.err.s R.later.err.wk.b' R.later.err.wk.s' R.later.err.σcol
      R.later.scale.Λ R.later.scale.w R.later.split.b R.later.err.co.qs R.later.err.co.ve (closedβV3
      R.later.split.β₁ R.later.excl) R.later.err.co.ζ R.later.err.co.ε₀ h8 := dite_eq_left h8
  have eV : R.later.split.V = V R.later.circle.γ R.later.circle.βc R.later.circle.γc R.later.excl.β₂
      R.later.excl.Δ R.later.err.co.qe R.later.err.co.ε R.later.err.bd.μ R.later.err.bd.τ
      R.later.err.s R.later.err.wk.b' R.later.err.wk.s' R.later.err.σcol R.later.scale.Λ
      R.later.scale.w R.later.split.b R.later.err.co.qs R.later.err.co.ve (closedβV3
      R.later.split.β₁ R.later.excl) R.later.err.co.ζ R.later.err.co.ε₀ R.later.split.T₀
      R.later.err.co.e₀ h9 := R.later.V_eq.trans (dite_eq_left h9)
  have eTL : TL R.later.circle.γ R.later.circle.βc R.later.circle.γc R.later.excl.β₂ R.later.excl.Δ
      R.later.err.co.qe R.later.err.co.ε R.later.err.bd.μ R.later.err.bd.τ R.later.err.s
      R.later.err.wk.b' R.later.err.wk.s' R.later.err.σcol R.later.scale.Λ R.later.scale.w
      R.later.split.b R.later.err.co.qs R.later.err.co.ve (closedβV3 R.later.split.β₁ R.later.excl)
      R.later.err.co.ζ R.later.err.co.ε₀ R.later.split.T₀ R.later.err.co.e₀ R.later.Lmax = TLd
      R.later.circle.γ R.later.circle.βc R.later.circle.γc R.later.excl.β₂ R.later.excl.Δ
      R.later.err.co.qe R.later.err.co.ε R.later.err.bd.μ R.later.err.bd.τ R.later.err.s
      R.later.err.wk.b' R.later.err.wk.s' R.later.err.σcol R.later.scale.Λ R.later.scale.w
      R.later.split.b R.later.err.co.qs R.later.err.co.ve (closedβV3 R.later.split.β₁ R.later.excl)
      R.later.err.co.ζ R.later.err.co.ε₀ R.later.split.T₀ R.later.err.co.e₀ R.later.Lmax hCT :=
      dite_eq_left hCT
  have hσthr : R.later.err.σcol ≤ threeSplittingExclusionThreshold.{0, 0} := h5.2.1.2.2.1
  have hβthr : R.later.excl.β₃ ≤ threeSplittingExclusionThreshold.{0, 0} := hβ3 ▸ h8.2.1.2.2.2.2
  simp only [PartialClosedFamilyOnTailV2]
  refine ⟨eER ▸ hεr _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ h8,
    eER ▸ hεr4 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ h8,
    eER ▸ hεrcap _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ h8,
    eDP ▸ hδ' _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ h8,
    eLZ ▸ hΛ' _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ h8, le_max_right _ _,
    δ R.later.circle.γ R.later.circle.βc R.later.circle.γc R.later.excl.β₂ R.later.excl.Δ
        R.later.err.co.qe R.later.err.co.ε R.later.err.bd.μ R.later.err.bd.τ R.later.err.s
        R.later.err.wk.b' R.later.err.wk.s' R.later.err.σcol R.later.scale.Λ R.later.scale.w
        R.later.split.b R.later.err.co.qs R.later.err.co.ve (closedβV3 R.later.split.β₁
        R.later.excl) R.later.err.co.ζ R.later.err.co.ε₀ R.later.split.T₀ R.later.err.co.e₀ h9, hδ _
        _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ h9,
    eDP ▸ hδδ' _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ h9, fun m hm => ?_⟩
  have hmT : TLd R.later.circle.γ R.later.circle.βc R.later.circle.γc R.later.excl.β₂ R.later.excl.Δ
      R.later.err.co.qe R.later.err.co.ε R.later.err.bd.μ R.later.err.bd.τ R.later.err.s
      R.later.err.wk.b' R.later.err.wk.s' R.later.err.σcol R.later.scale.Λ R.later.scale.w
      R.later.split.b R.later.err.co.qs R.later.err.co.ve (closedβV3 R.later.split.β₁ R.later.excl)
      R.later.err.co.ζ R.later.err.co.ε₀ R.later.split.T₀ R.later.err.co.e₀ R.later.Lmax hCT ≤ m :=
    (le_of_eq eTL.symm).trans ((le_max_right _ _).trans (R.later.tail_ge.trans hm))
  obtain ⟨⟨ρ, hρ, hwin, ⟨fam⟩⟩, hlc⟩ := hTLd _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ hCT m
      hmT
  refine ⟨M m, ?_, hlc, lc18ExclusionOutV2_of_lc09Out_VAL2 R (M m) hσthr hβthr hlc⟩
  rw [eER, eLZ]
  exact ⟨⟨ρ, hρ, hwin, by rw [eV]; exact fam⟩⟩

/-- **One admissible register, realized** (review 52's chain, consumer): a common strategy `T`
refining `U` and ONE staged register at `T` on whose tail every member carries the final family at
the register's values, with `20 Λz ≤ T₀` and `εr < ε₀`. -/
theorem exists_realized_closedRegisterV2_VAL3 (K : ℕ) (hK : 10 ≤ K) (A : ℝ → ℝ)
    (hA : ∀ x, 0 < x → 0 < A x) (Wseq : ℕ → CompactCarrier.{u})
    (gseq : ∀ m, SmoothRiemannianMetric (Wseq m).model (Wseq m).Carrier)
    (hf : ∀ m, ClosedMemberFacts (Wseq m))
    (hg : ∀ m, closedCollapseHypotheses (Wseq m) (gseq m) K A (closedCounterexampleRatio (m + 2)))
    {D : ClosedEarlyData} (U : ClosedThresholdsV2 D) :
    ∃ T : ClosedThresholdsV2 D, ClosedStrategyRefinesV2 T U ∧ ∃ R : ClosedRegisterV2 D T,
      ∃ δ εr Λz : ℝ, 20 * Λz ≤ R.later.split.T₀ ∧ εr < R.later.err.co.ε₀ ∧
        ∀ m, R.later.tail ≤ m → ∃ M : ClosedModel (Wseq m) (gseq m),
          Nonempty (PartialClosedFamilyInstanceV2 K R M δ εr Λz) := by
  obtain ⟨T, hTU, -, -, εrF, δ'F, ΛzF, h⟩ :=
    exists_closed_realization_VAL3 K hK A hA Wseq gseq hf hg U
  obtain ⟨R⟩ := exists_closedRegisterV2 D T
  obtain ⟨-, -, hcap, -, -, hT, δ, -, -, ht⟩ := h R
  exact ⟨T, hTU, R, δ, _, _, hT.trans ((le_max_right _ _).trans R.later.T₀_ge), hcap,
    fun m hm => (ht m hm).imp fun _ hM => hM.1⟩

end DifferentialGeometry.Geometry.Collapse
