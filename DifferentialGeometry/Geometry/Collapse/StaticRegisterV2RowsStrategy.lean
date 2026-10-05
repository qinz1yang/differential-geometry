import DifferentialGeometry.Geometry.Collapse.StaticRegisterV2ValidityRows
import DifferentialGeometry.Geometry.Collapse.StaticRegisterV2RealizationC14D

/-!
# A rows strategy for the staged register (lane FC39-VAL4; PARTIAL: 11 of the 15 rows)

External review 52 (`dispositions-task52-fc39-threshold-validity.md`): the `rows` field of
`PartialClosedThresholdValidityV2Rows` is discharged by a threshold strategy `U` that encodes the
rows' own early thresholds; the common strategy of the realization refines it.

* Row thresholds as total functions of the values they are read from (the accepted rows' Skolem
  witnesses, `1` outside a row's range): `tcp02σ_VAL4`, `tcp02η₂_VAL4`, `tcp02η₁_VAL4` (TCP02 at
  `E₀ = E`, `ν = β₃/3`), `egp03Lc_VAL4`/`egp03η_VAL4`, `egp04…`, `egp06…`, `egp07…`, `sgp02…`,
  `sgp03…`, `sgp04θ_VAL4`/`sgp04Lc_VAL4`/`sgp04η_VAL4`, `sgp06θ_VAL4`/`sgp06Lc_VAL4`/`sgp06η_VAL4`.
* `partialRowsStrategyV2 D`: the strategy; each slot is the minimum (upper slots) or maximum
  (lower slots) of the requests of the rows that read exactly the values before that slot.
* `PartialClosedRowOutsV2 R P`: the conclusions of TCP01 (Gram), TCP02, EGP03, EGP04, EGP06, EGP07,
  SGP01, SGP02, SGP03 (zero block), SGP04, SGP06 on a final family `P` at the register's values (as
  in `ClosedRowOutsV2`, without TCP03–TCP06); `ClosedRowOutsV2.toPartial_VAL4`.
* `partialRowOuts_of_refines_VAL4`: for every strategy `T` refining `partialRowsStrategyV2 D`
  (with `C_ge`), every staged register `R` at `T`, every `εr < ε₀`, `20Λz ≤ T₀` and every final
  family at `R`'s values, the 11 row conclusions hold.
* Consumer `exists_closed_realization_rows_C14D_VAL4`: ONE common strategy at which every staged
  register is realized on `LocalChartPacketsC14D` (FC39-VAL4 G1) and every instance carries the
  11 row conclusions.

OPEN (obstruction, recorded in `state-FC39-VAL4.md`): TCP03–TCP06 take `γ ≤ γ₀`, `γc ≤ γ₀`,
`βc ≤ ηc` with `γ₀, ηc` depending on the exclusion quality `ν` (`3ν ≤ β₃`), while the register
chooses `γ, γc, βc` (PR11) BEFORE `β₃` (PR12) with no lower bound on `β₃`; no strategy meets them
for every register unless the rows' `γ₀, ηc` are made `ν`-independent or `β₃` is fixed before PR11.
-/

set_option autoImplicit false

noncomputable section

open Set Function Metric Bundle Manifold Filter
open scoped ContDiff Manifold Topology
open DifferentialGeometry GC.Endpoint GC.MetricGeometry
open DifferentialGeometry.Geometry.Riemannian DifferentialGeometry.Analysis

namespace DifferentialGeometry.Geometry.Collapse

universe u

local notation "E3" => EuclideanSpace ℝ (Fin 3)

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace

attribute [local instance] nezero_finrank_euclideanThree_LC87

/-! ### Total threshold functions (the accepted rows' witnesses) -/

/-- Two nested witnesses of `∃ a b, P a b` satisfy `P`. -/
theorem choose₂_spec_VAL4 {P : ℝ → ℝ → Prop} (h : ∃ a b, P a b) :
    P (Classical.choose h) (Classical.choose (Classical.choose_spec h)) :=
  Classical.choose_spec (Classical.choose_spec h)

/-- A strict upper bound by `posOr` of a total witness is a bound by the witness. -/
theorem lt_of_lt_posOr_dite_VAL4 {c : Prop} [Decidable c] {f : c → ℝ} {x : ℝ} (hc : c)
    (hf : 0 < f hc) (h : x < posOr_VAL3 (dite c f fun _ => 1)) : x < f hc := by
  rwa [dite_eq_left hc, posOr_eq_VAL3 hf] at h

/-- A total witness below `x` is a witness below `x`. -/
theorem le_of_dite_le_VAL4 {c : Prop} [Decidable c] {f : c → ℝ} {x : ℝ} (hc : c)
    (h : (dite c f fun _ => 1) ≤ x) : f hc ≤ x := by
  rwa [dite_eq_left hc] at h

/-- The inverse of a total witness below `x`. -/
theorem inv_le_of_dite_le_VAL4 {c : Prop} [Decidable c] {f : c → ℝ} {x : ℝ} (hc : c)
    (h : (dite c f fun _ => 1)⁻¹ ≤ x) : (f hc)⁻¹ ≤ x := by
  rwa [dite_eq_left hc] at h

/-- TCP02's early `σ` at `(E₀, ν)`. -/
def tcp02σ_VAL4 (E ν : ℝ) : ℝ :=
  if h : 0 < E ∧ 0 < ν ∧ ν < 1 then Classical.choose (tcp02_row_out_VAL3 h.1 h.2.1 h.2.2) else 1

/-- TCP02's early circle bound `η₂` at `(E₀, ν)`. -/
def tcp02η₂_VAL4 (E ν : ℝ) : ℝ :=
  if h : 0 < E ∧ 0 < ν ∧ ν < 1 then
    Classical.choose (Classical.choose_spec (tcp02_row_out_VAL3 h.1 h.2.1 h.2.2)).2.2
  else 1

/-- TCP02's bound `η₁` at `(E₀, ν, Δ)`. -/
def tcp02η₁_VAL4 (E ν Δ : ℝ) : ℝ :=
  if h : 0 < E ∧ 0 < ν ∧ ν < 1 ∧ 1 ≤ Δ then
    Classical.choose ((Classical.choose_spec (Classical.choose_spec
      (tcp02_row_out_VAL3 h.1 h.2.1 h.2.2.1)).2.2).2 Δ h.2.2.2)
  else 1

/-- EGP03's `L_c` at `(Δ, β₂, E)`. -/
def egp03Lc_VAL4 (Δ β₂ E : ℝ) : ℝ :=
  if h : 1 ≤ Δ ∧ 0 < β₂ ∧ β₂ < 1 / 1000000 ∧ 0 < E then
    Classical.choose (egp03_row_out_VAL3 h.1 h.2.1 h.2.2.1 h.2.2.2)
  else 1

/-- EGP03's `η₀` at `(Δ, β₂, E)`. -/
def egp03η_VAL4 (Δ β₂ E : ℝ) : ℝ :=
  if h : 1 ≤ Δ ∧ 0 < β₂ ∧ β₂ < 1 / 1000000 ∧ 0 < E then
    Classical.choose (Classical.choose_spec (egp03_row_out_VAL3 h.1 h.2.1 h.2.2.1 h.2.2.2))
  else 1

/-- EGP04's `L_c` at `(Δ, β₂, θ)`. -/
def egp04Lc_VAL4 (Δ β₂ θ : ℝ) : ℝ :=
  if h : 1 ≤ Δ ∧ 0 < β₂ ∧ β₂ < 1 / 1000000 ∧ 0 < θ ∧ θ < 1 then
    Classical.choose (egp04_row_RVZ_out_VAL3 h.1 h.2.1 h.2.2.1 h.2.2.2.1 h.2.2.2.2)
  else 1

/-- EGP04's `η₀` at `(Δ, β₂, θ)`. -/
def egp04η_VAL4 (Δ β₂ θ : ℝ) : ℝ :=
  if h : 1 ≤ Δ ∧ 0 < β₂ ∧ β₂ < 1 / 1000000 ∧ 0 < θ ∧ θ < 1 then
    Classical.choose (Classical.choose_spec
      (egp04_row_RVZ_out_VAL3 h.1 h.2.1 h.2.2.1 h.2.2.2.1 h.2.2.2.2))
  else 1

/-- SGP02's `L_c` at `(Δ, β₂, E)`. -/
def sgp02Lc_VAL4 (Δ β₂ E : ℝ) : ℝ :=
  if h : 1 ≤ Δ ∧ 0 < β₂ ∧ β₂ < 1 ∧ 0 < E then
    Classical.choose (sgp02_row_out_VAL3 h.1 h.2.1 h.2.2.1 h.2.2.2)
  else 1

/-- SGP02's `η₀` at `(Δ, β₂, E)`. -/
def sgp02η_VAL4 (Δ β₂ E : ℝ) : ℝ :=
  if h : 1 ≤ Δ ∧ 0 < β₂ ∧ β₂ < 1 ∧ 0 < E then
    Classical.choose (Classical.choose_spec (sgp02_row_out_VAL3 h.1 h.2.1 h.2.2.1 h.2.2.2))
  else 1

/-- SGP03's `L_c` at `(Δ, β₂, θ, E)`. -/
def sgp03Lc_VAL4 (Δ β₂ θ E : ℝ) : ℝ :=
  if h : 1 ≤ Δ ∧ 0 < β₂ ∧ β₂ < 1 ∧ 0 < θ ∧ θ < 1 ∧ 0 < E ∧ E < θ ^ 2 / 10 ^ 6 then
    Classical.choose (sgp03_zero_row_out_VAL3 h.1 h.2.1 h.2.2.1 h.2.2.2.1 h.2.2.2.2.1
      h.2.2.2.2.2.1 h.2.2.2.2.2.2)
  else 1

/-- SGP03's `η₀` at `(Δ, β₂, θ, E)`. -/
def sgp03η_VAL4 (Δ β₂ θ E : ℝ) : ℝ :=
  if h : 1 ≤ Δ ∧ 0 < β₂ ∧ β₂ < 1 ∧ 0 < θ ∧ θ < 1 ∧ 0 < E ∧ E < θ ^ 2 / 10 ^ 6 then
    Classical.choose (Classical.choose_spec (sgp03_zero_row_out_VAL3 h.1 h.2.1 h.2.2.1
      h.2.2.2.1 h.2.2.2.2.1 h.2.2.2.2.2.1 h.2.2.2.2.2.2))
  else 1

/-- SGP04's tolerance `θ` at `(Δ, β₂, e)`. -/
def sgp04θ_VAL4 (Δ β₂ eg : ℝ) : ℝ :=
  if h : 1 ≤ Δ ∧ 0 < β₂ ∧ β₂ < 1 ∧ 0 < eg ∧ eg < 1 / 100 then
    Classical.choose (sgp04_row_out_VAL3 h.1 h.2.1 h.2.2.1 h.2.2.2.1 h.2.2.2.2)
  else 1

/-- SGP04's `L_c` at `(Δ, β₂, e)`. -/
def sgp04Lc_VAL4 (Δ β₂ eg : ℝ) : ℝ :=
  if h : 1 ≤ Δ ∧ 0 < β₂ ∧ β₂ < 1 ∧ 0 < eg ∧ eg < 1 / 100 then
    Classical.choose (Classical.choose_spec
      (sgp04_row_out_VAL3 h.1 h.2.1 h.2.2.1 h.2.2.2.1 h.2.2.2.2)).2.2
  else 1

/-- SGP04's `η₀` at `(Δ, β₂, e)`. -/
def sgp04η_VAL4 (Δ β₂ eg : ℝ) : ℝ :=
  if h : 1 ≤ Δ ∧ 0 < β₂ ∧ β₂ < 1 ∧ 0 < eg ∧ eg < 1 / 100 then
    Classical.choose (Classical.choose_spec (Classical.choose_spec
      (sgp04_row_out_VAL3 h.1 h.2.1 h.2.2.1 h.2.2.2.1 h.2.2.2.2)).2.2)
  else 1

/-- EGP06's `L_c` at `(Δ, β₂, e)`. -/
def egp06Lc_VAL4 (Δ β₂ eg : ℝ) : ℝ :=
  if h : 1 ≤ Δ ∧ 0 < β₂ ∧ β₂ < 1 / 1000000 ∧ 0 < eg ∧ eg < 1 / 100 then
    Classical.choose (egp06_row_out_VAL3 h.1 h.2.1 h.2.2.1 h.2.2.2.1 h.2.2.2.2)
  else 1

/-- EGP06's `η₀` at `(Δ, β₂, e)`. -/
def egp06η_VAL4 (Δ β₂ eg : ℝ) : ℝ :=
  if h : 1 ≤ Δ ∧ 0 < β₂ ∧ β₂ < 1 / 1000000 ∧ 0 < eg ∧ eg < 1 / 100 then
    Classical.choose (Classical.choose_spec
      (egp06_row_out_VAL3 h.1 h.2.1 h.2.2.1 h.2.2.2.1 h.2.2.2.2))
  else 1

/-- EGP07's `L_c` at `(Δ, β₂, Γ, Σ, e)`. -/
def egp07Lc_VAL4 (Δ β₂ Γ Sg eg : ℝ) : ℝ :=
  if h : 1 ≤ Δ ∧ 0 < β₂ ∧ β₂ < 1 / 1000000 ∧ Γ ∈ Ioo (0 : ℝ) 1 ∧ 0 < Sg ∧
      Sg < min (Γ / 200) (Γ ^ 3 / (100 * egpGraphConst)) ∧ 0 < eg ∧
      eg < min (1 / 100) (min (Γ * Sg / 100) (Sg / 1000)) then
    Classical.choose (egp07_row_C14_out_VAL3 h.1 h.2.1 h.2.2.1 h.2.2.2.1 h.2.2.2.2.1
      h.2.2.2.2.2.1 h.2.2.2.2.2.2.1 h.2.2.2.2.2.2.2)
  else 1

/-- EGP07's `η₀` at `(Δ, β₂, Γ, Σ, e)`. -/
def egp07η_VAL4 (Δ β₂ Γ Sg eg : ℝ) : ℝ :=
  if h : 1 ≤ Δ ∧ 0 < β₂ ∧ β₂ < 1 / 1000000 ∧ Γ ∈ Ioo (0 : ℝ) 1 ∧ 0 < Sg ∧
      Sg < min (Γ / 200) (Γ ^ 3 / (100 * egpGraphConst)) ∧ 0 < eg ∧
      eg < min (1 / 100) (min (Γ * Sg / 100) (Sg / 1000)) then
    Classical.choose (Classical.choose_spec (egp07_row_C14_out_VAL3 h.1 h.2.1 h.2.2.1
      h.2.2.2.1 h.2.2.2.2.1 h.2.2.2.2.2.1 h.2.2.2.2.2.2.1 h.2.2.2.2.2.2.2))
  else 1

/-- SGP06's tolerance `θ` at `(Δ, β₂, Γ, σ, e)`. -/
def sgp06θ_VAL4 (Δ β₂ Γ sg eg : ℝ) : ℝ :=
  if h : 1 ≤ Δ ∧ 0 < β₂ ∧ β₂ < 1 ∧ 0 < Γ ∧ Γ < 1 ∧ 0 < sg ∧ sg < Γ / 200 ∧
      sg < Γ ^ 3 / (100 * sgpGraphBound) ∧ 0 < eg ∧ eg < 1 / 100 ∧ eg < Γ * sg / 100 then
    Classical.choose (sgp06_row_C14_out_VAL3 h.1 h.2.1 h.2.2.1 h.2.2.2.1 h.2.2.2.2.1
      h.2.2.2.2.2.1 h.2.2.2.2.2.2.1 h.2.2.2.2.2.2.2.1 h.2.2.2.2.2.2.2.2.1
      h.2.2.2.2.2.2.2.2.2.1 h.2.2.2.2.2.2.2.2.2.2)
  else 1

/-- SGP06's `L_c` at `(Δ, β₂, Γ, σ, e)`. -/
def sgp06Lc_VAL4 (Δ β₂ Γ sg eg : ℝ) : ℝ :=
  if h : 1 ≤ Δ ∧ 0 < β₂ ∧ β₂ < 1 ∧ 0 < Γ ∧ Γ < 1 ∧ 0 < sg ∧ sg < Γ / 200 ∧
      sg < Γ ^ 3 / (100 * sgpGraphBound) ∧ 0 < eg ∧ eg < 1 / 100 ∧ eg < Γ * sg / 100 then
    Classical.choose (Classical.choose_spec (sgp06_row_C14_out_VAL3 h.1 h.2.1 h.2.2.1
      h.2.2.2.1 h.2.2.2.2.1 h.2.2.2.2.2.1 h.2.2.2.2.2.2.1 h.2.2.2.2.2.2.2.1
      h.2.2.2.2.2.2.2.2.1 h.2.2.2.2.2.2.2.2.2.1 h.2.2.2.2.2.2.2.2.2.2)).2.2
  else 1

/-- SGP06's `η₀` at `(Δ, β₂, Γ, σ, e)`. -/
def sgp06η_VAL4 (Δ β₂ Γ sg eg : ℝ) : ℝ :=
  if h : 1 ≤ Δ ∧ 0 < β₂ ∧ β₂ < 1 ∧ 0 < Γ ∧ Γ < 1 ∧ 0 < sg ∧ sg < Γ / 200 ∧
      sg < Γ ^ 3 / (100 * sgpGraphBound) ∧ 0 < eg ∧ eg < 1 / 100 ∧ eg < Γ * sg / 100 then
    Classical.choose (Classical.choose_spec (Classical.choose_spec (sgp06_row_C14_out_VAL3 h.1
      h.2.1 h.2.2.1 h.2.2.2.1 h.2.2.2.2.1 h.2.2.2.2.2.1 h.2.2.2.2.2.2.1 h.2.2.2.2.2.2.2.1
      h.2.2.2.2.2.2.2.2.1 h.2.2.2.2.2.2.2.2.2.1 h.2.2.2.2.2.2.2.2.2.2)).2.2)
  else 1

/-! ### The strategy -/

/-- **The rows strategy** (PARTIAL: the requests of TCP01, TCP02, EGP03, EGP04, EGP06, EGP07,
SGP01, SGP02, SGP03, SGP04, SGP06; TCP02 at `ν = β₃/3`). Each upper slot is the minimum of the
requests read from the values before it (wrapped in `posOr_VAL3`), `L_max`'s lower request is the
maximum of the rows' `L_c`, `σ⁻¹` and `4(10 + 4·10⁶Δ + Δ/3)`; the slots the 11 rows do not read
are `1` (upper), `0` (lower) or trivial. -/
def partialRowsStrategyV2 (D : ClosedEarlyData) : ClosedThresholdsV2 D where
  Nb := fun _ => 0
  Nb_nonneg := fun _ => le_rfl
  cw := fun _ => 0
  cw_nonneg := fun _ => le_rfl
  circleUp := fun _ _ _ _ => 1
  circleUp_pos := fun _ _ _ _ => one_pos
  lc18 := 1 / 2
  lc18_pos := by norm_num
  β₂Up := fun _ ci β₃ => min (1 / 10000000) (min (posOr_VAL3 (tcp02σ_VAL4 ci.E (β₃ / 3)) / 3)
    (posOr_VAL3 (tcp02η₂_VAL4 ci.E (β₃ / 3))))
  β₂Up_pos := fun _ _ _ =>
    lt_min (by norm_num) (lt_min (div_pos (posOr_pos_VAL3 _) (by norm_num)) (posOr_pos_VAL3 _))
  ΔLow := fun _ _ _ _ => 0
  errorsUp := fun st ci ex => min (posOr_VAL3 (ci.θe ^ 2 / 10 ^ 8))
    (min (posOr_VAL3 (1 / (1000 * (1000000 * ex.Δ))))
    (min (posOr_VAL3 (1 / (100 * (1000000 * ex.Δ))))
    (min (posOr_VAL3 (ci.θe / (100 * (1000000 * ex.Δ))))
    (min (posOr_VAL3 (ci.θs ^ 2 / 10 ^ 6))
    (min (posOr_VAL3 (ci.θs / 100))
    (min (posOr_VAL3 (ci.θs / (100 * (1000000 * ex.Δ))))
    (min (posOr_VAL3 (sgp04θ_VAL4 ex.Δ ex.β₂ (st.e 2) ^ 2 / 10 ^ 6))
    (min (posOr_VAL3 (sgp04θ_VAL4 ex.Δ ex.β₂ (st.e 2) / 100))
    (min (posOr_VAL3 (sgp04θ_VAL4 ex.Δ ex.β₂ (st.e 2) / (100 * (1000000 * ex.Δ))))
    (min (posOr_VAL3 (sgp06θ_VAL4 ex.Δ ex.β₂ (st.Γ 2) (st.Sig 2) (st.e 2) ^ 2 / 10 ^ 6))
    (min (posOr_VAL3 (sgp06θ_VAL4 ex.Δ ex.β₂ (st.Γ 2) (st.Sig 2) (st.e 2) / 100))
    (min (posOr_VAL3 (sgp06θ_VAL4 ex.Δ ex.β₂ (st.Γ 2) (st.Sig 2) (st.e 2) /
      (100 * (1000000 * ex.Δ))))
    (min (posOr_VAL3 ((st.e 1 / (20 * egpGraphConst)) ^ 2 / 10 ^ 8))
    (min (posOr_VAL3 (st.e 1 / (20 * egpGraphConst) / 100))
      (posOr_VAL3 (st.e 1 / (20 * egpGraphConst) / (100 * (1000000 * ex.Δ))))))))))))))))))
  errorsUp_pos := fun _ _ _ => by simp only [lt_min_iff, posOr_pos_VAL3, and_self]
  sectionUp := fun st ci ex _ => min (posOr_VAL3 (ci.θe / 100 / ex.Δ))
    (posOr_VAL3 (st.e 1 / (20 * egpGraphConst) / 100 / ex.Δ))
  sectionUp_pos := fun _ _ _ _ => by simp only [lt_min_iff, posOr_pos_VAL3, and_self]
  lfr29W := fun _ _ _ _ _ => 1
  lfr29W_pos := fun _ _ _ _ _ => one_pos
  endpointUp := fun _ _ _ _ _ _ => 1
  endpointUp_pos := fun _ _ _ _ _ _ => one_pos
  σcolUp := fun _ _ _ _ _ _ _ => 1
  σcolUp_pos := fun _ _ _ _ _ _ _ => one_pos
  I₁ := 1
  I₁_pos := one_pos
  scaleUp := fun _ _ _ _ => 1
  scaleUp_pos := fun _ _ _ _ => one_pos
  wUp := fun _ _ _ _ _ => 1
  wUp_pos := fun _ _ _ _ _ => one_pos
  splitUp := fun st ci ex _ _ => min (posOr_VAL3 (tcp02η₁_VAL4 ci.E (ex.β₃ / 3) ex.Δ))
    (min (posOr_VAL3 (egp03η_VAL4 ex.Δ ex.β₂ ci.E))
    (min (posOr_VAL3 (egp04η_VAL4 ex.Δ ex.β₂ ci.θe))
    (min (posOr_VAL3 (egp06η_VAL4 ex.Δ ex.β₂ (st.e 1)))
      (posOr_VAL3 (egp07η_VAL4 ex.Δ ex.β₂ (st.Γ 1) (st.Sig 1) (st.e 1))))))
  splitUp_pos := fun _ _ _ _ _ => by simp only [lt_min_iff, posOr_pos_VAL3, and_self]
  β₁Up := fun st ci ex _ _ _ => min (posOr_VAL3 (tcp02η₁_VAL4 ci.E (ex.β₃ / 3) ex.Δ))
    (min (posOr_VAL3 (egp03η_VAL4 ex.Δ ex.β₂ ci.E))
    (min (posOr_VAL3 (egp04η_VAL4 ex.Δ ex.β₂ ci.θe))
    (min (posOr_VAL3 (egp06η_VAL4 ex.Δ ex.β₂ (st.e 1)))
    (min (posOr_VAL3 (egp07η_VAL4 ex.Δ ex.β₂ (st.Γ 1) (st.Sig 1) (st.e 1)))
    (min (posOr_VAL3 (sgp02η_VAL4 ex.Δ ex.β₂ ci.E))
    (min (posOr_VAL3 (sgp03η_VAL4 ex.Δ ex.β₂ ci.θs (ci.θs ^ 2 / (2 * 10 ^ 6))))
    (min (posOr_VAL3 (sgp04η_VAL4 ex.Δ ex.β₂ (st.e 2)))
      (posOr_VAL3 (sgp06η_VAL4 ex.Δ ex.β₂ (st.Γ 2) (st.Sig 2) (st.e 2))))))))))
  β₁Up_pos := fun _ _ _ _ _ _ => by simp only [lt_min_iff, posOr_pos_VAL3, and_self]
  T₀Low := fun _ _ _ _ _ _ _ => 0
  lpa02V := fun _ _ _ _ _ _ _ T₀ => T₀
  T₀_le_lpa02V := fun _ _ _ _ _ _ _ _ => le_rfl
  LmaxLow := fun st ci ex _ _ _ => max (4 * (10 + 2 * (2000000 * ex.Δ) + ex.Δ / 3))
    (max (tcp02σ_VAL4 ci.E (ex.β₃ / 3))⁻¹
    (max (egp03Lc_VAL4 ex.Δ ex.β₂ ci.E)
    (max (egp04Lc_VAL4 ex.Δ ex.β₂ ci.θe)
    (max (egp06Lc_VAL4 ex.Δ ex.β₂ (st.e 1))
    (max (egp07Lc_VAL4 ex.Δ ex.β₂ (st.Γ 1) (st.Sig 1) (st.e 1))
    (max (sgp02Lc_VAL4 ex.Δ ex.β₂ ci.E)
    (max (sgp03Lc_VAL4 ex.Δ ex.β₂ ci.θs (ci.θs ^ 2 / (2 * 10 ^ 6)))
    (max (sgp04Lc_VAL4 ex.Δ ex.β₂ (st.e 2))
      (sgp06Lc_VAL4 ex.Δ ex.β₂ (st.Γ 2) (st.Sig 2) (st.e 2))))))))))
  tailLow := fun _ _ _ _ _ _ _ => 0
  H := fun m => (m : ℝ)
  H_tendsto := tendsto_natCast_atTop_atTop

/-! ### The 11 row conclusions on a family at the register's values -/

/-- **The row conclusions met by the rows strategy** (PARTIAL: `ClosedRowOutsV2` without
TCP03–TCP06) on a final family `P` at the register's values. -/
def PartialClosedRowOutsV2 {K : ℕ} {D : ClosedEarlyData} {T : ClosedThresholdsV2 D}
    (R : ClosedRegisterV2 D T) {X : Type} [MetricSpace X] [ChartedSpace E3 X]
    [IsManifold 𝓘(ℝ, E3) ∞ X] [CompactSpace X] {g : SmoothRiemannianMetric 𝓘(ℝ, E3) X}
    {hmetric : ∀ a b : X, riemannianEDistOf g a b = ENNReal.ofReal (dist a b)}
    {ρ : X → ℝ} {hρ : ∀ p, 0 < ρ p} {δ εr Λz : ℝ}
    (P : LocalChartPacketsC14 X g hmetric ρ hρ R.later.scale.Λ R.β R.later.excl.Δ
      R.later.err.co.qs K R.later.err.co.qe R.later.err.bd.μ R.later.split.b R.later.err.s
      R.later.err.wk.b' R.later.err.wk.s' R.later.err.co.ε R.later.circle.γc R.later.circle.βc
      R.later.Lmax R.later.err.bd.τ R.later.circle.γ δ εr R.later.err.co.e₀ R.later.split.T₀
      R.later.split.V R.later.err.co.ve R.later.err.co.ζ Λz) : Prop :=
  Tcp01GramOutV2 P.toLocalChartPackets ∧
  Tcp02OutV2 P.toLocalChartPackets R.later.circle.E ∧
  Egp03OutV2 P.toLocalChartFamilyE R.later.circle.E ∧
  Egp04OutV2 P.toLocalChartPacketsRVZ R.later.circle.θe ∧
  Egp06OutV2 P.toLocalChartPacketsRVZ (R.stage.e 1) ∧
  Egp07OutV2 P (R.stage.Γ 1) (R.stage.Sig 1) (R.stage.e 1) ∧
  Sgp01OutV2 P.toLocalChartPacketsR ∧
  Sgp02OutV2 P.toLocalChartFamilyQ R.later.circle.E ∧
  Sgp03ZeroOutV2 P.toLocalChartPacketsRVZ R.later.circle.θs
    (R.later.circle.θs ^ 2 / (2 * 10 ^ 6)) ∧
  Sgp04OutV2 P.toLocalChartPacketsRVZ (R.stage.e 2) ∧
  Sgp06OutV2 P (R.stage.Γ 2) (R.stage.Sig 2) (R.stage.e 2)

/-- The full row conclusions contain the partial ones. -/
theorem ClosedRowOutsV2.toPartial_VAL4 {K : ℕ} {D : ClosedEarlyData} {T : ClosedThresholdsV2 D}
    {R : ClosedRegisterV2 D T} {W : CompactCarrier.{u}}
    {g : SmoothRiemannianMetric W.model W.Carrier} {M : ClosedModel W g} {δ εr Λz : ℝ}
    {F : ClosedFamilyInstanceV2 K R M δ εr Λz} (h : ClosedRowOutsV2 F) :
    PartialClosedRowOutsV2 R F.family := by
  obtain ⟨h1, h2, -, -, -, -, h7, h8, h9, h10, h11, h12, h13, h14, h15⟩ := h
  unfold PartialClosedRowOutsV2
  exact ⟨h1, h2, h7, h8, h9, h10, h11, h12, h13, h14, h15⟩

/-! ### The rows strategy discharges the 11 rows -/

/-- **The 11 rows at every register of a strategy refining the rows strategy** (review 52's `rows`
field, PARTIAL: TCP03–TCP06 are open, see the module docstring): with `C_ge`, for every staged
register `R` at `T`, every `εr < ε₀`, `20Λz ≤ T₀` and every final family at `R`'s values, the
conclusions of TCP01, TCP02, EGP03, EGP04, EGP06, EGP07, SGP01, SGP02, SGP03, SGP04, SGP06 hold at
the register's tolerances. -/
theorem partialRowOuts_of_refines_VAL4 {D : ClosedEarlyData} (hC : ∀ j, gafGraphConst j ≤ D.C j)
    {T : ClosedThresholdsV2 D} (hTU : ClosedStrategyRefinesV2 T (partialRowsStrategyV2 D))
    (R : ClosedRegisterV2 D T) {K : ℕ} {X : Type} [MetricSpace X] [ChartedSpace E3 X]
    [IsManifold 𝓘(ℝ, E3) ∞ X] [CompactSpace X] {g : SmoothRiemannianMetric 𝓘(ℝ, E3) X}
    {hmetric : ∀ a b : X, riemannianEDistOf g a b = ENNReal.ofReal (dist a b)}
    {ρ : X → ℝ} {hρ : ∀ p, 0 < ρ p} {δ εr Λz : ℝ} (hεr : εr < R.later.err.co.ε₀)
    (hΛz : 20 * Λz ≤ R.later.split.T₀)
    (P : LocalChartPacketsC14 X g hmetric ρ hρ R.later.scale.Λ R.β R.later.excl.Δ
      R.later.err.co.qs K R.later.err.co.qe R.later.err.bd.μ R.later.split.b R.later.err.s
      R.later.err.wk.b' R.later.err.wk.s' R.later.err.co.ε R.later.circle.γc R.later.circle.βc
      R.later.Lmax R.later.err.bd.τ R.later.circle.γ δ εr R.later.err.co.e₀ R.later.split.T₀
      R.later.split.V R.later.err.co.ve R.later.err.co.ζ Λz) :
    PartialClosedRowOutsV2 R P := by
  -- the register's ranges
  have hΔ0 : 0 < R.later.excl.Δ := R.later.Δ_pos_VAL2
  have hΔ1 : 1 ≤ R.later.excl.Δ :=
    ((by norm_num : (1 : ℝ) < 100).trans R.later.hundred_lt_Δ_VAL2).le
  have hβ₂0 := R.later.β₂_pos
  have hβ₂6 : R.later.excl.β₂ < 1 / 1000000 := R.later.β₂_lt_audit_VAL2.trans_eq (by norm_num)
  have hβ₂1 : R.later.excl.β₂ < 1 := hβ₂6.trans (by norm_num)
  have hβ₃0 := R.later.β₃_pos
  have hβ₃ : R.later.excl.β₃ < 1 / 2 := R.later.β₃_lt.trans_le hTU.lc18_le
  have hΛ0 : 0 ≤ R.later.scale.Λ := R.later.Λ_pos.le
  have hLΛ : 1000000 * R.later.excl.Δ * R.later.scale.Λ < 1 / 100000 := by
    have h := R.later.regScale_L
    unfold closedLongLength at h
    linarith
  have hT1600 : 1600 * (1000000 * R.later.excl.Δ) ≤ R.later.split.T₀ := by
    have h := (le_max_left _ _).trans R.later.T₀_ge
    unfold closedLongLength at h
    linarith
  have he40 : R.later.err.co.e₀ < 1 / 40 := R.later.e₀_lt_VAL2
  have hμ : R.later.err.bd.μ ≤ 1 / 100 := (R.later.μ_lt_VAL2.trans (by norm_num)).le
  have hτ : R.later.err.bd.τ ≤ 1 / 100 := (R.later.τ_lt_VAL2.trans (by norm_num)).le
  have hs6 : R.later.err.s < 1 / 1000000 := R.later.s_lt_audit_VAL2.trans_eq (by norm_num)
  have hσs0 := R.later.qs_pos
  have hζ0 := R.later.ζ_pos
  have hE0 := R.later.E_pos
  have hθe0 := R.later.θe_pos
  have hθe1 : R.later.circle.θe < 1 := R.later.θe_lt_hundredth_VAL2.trans (by norm_num)
  have hθs0 := R.later.θs_pos
  have hrange2 := R.stage.stage_range_VAL3 hC 2
  have hrange1 := R.stage.stage_range_VAL3 hC 1
  have hθs1 : R.later.circle.θs < 1 := by
    have h := R.later.θs_lt
    have hC2 : sgpGraphBound ≤ D.C 2 := hC 2
    have h4 := four_le_sgpGraphBound_SGP4
    have he2 := hrange2.2.2.2.2.2.2.1
    have hD : 0 < 10 * D.C 2 := by linarith
    calc R.later.circle.θs < R.stage.e 2 / (10 * D.C 2) := h
      _ < 1 := by rw [div_lt_one hD]; linarith
  have hκ : 0 < R.stage.e 1 / (20 * egpGraphConst) :=
    div_pos hrange1.2.2.2.2.2.1 (mul_pos (by norm_num) egpGraphConst_pos_KC4)
  -- the strategy's slots at the register
  have hβ₂U : R.later.excl.β₂ < (partialRowsStrategyV2 D).β₂Up R.stage R.later.circle
      R.later.excl.β₃ := (R.later.β₂_lt.trans_le (min_le_left _ _)).trans_le (hTU.β₂Up_le _ _ _)
  simp only [partialRowsStrategyV2, lt_min_iff] at hβ₂U
  obtain ⟨hβ₂7, hβ₂σ, hβ₂η⟩ := hβ₂U
  have hζU := R.later.ζ_lt.trans_le (hTU.errorsUp_le _ _ _)
  have hqsU := (R.later.qs_lt.trans_le (min_le_right _ _)).trans_le (hTU.errorsUp_le _ _ _)
  have hqeU := (R.later.qe_lt.trans_le (min_le_right _ _)).trans_le (hTU.errorsUp_le _ _ _)
  have hveU := (R.later.ve_lt.trans_le (min_le_right _ _)).trans_le (hTU.errorsUp_le _ _ _)
  have hε₀U := (R.later.ε₀_lt.trans_le (min_le_right _ _)).trans_le (hTU.errorsUp_le _ _ _)
  have hve := R.later.ve_lt.trans_le (min_le_left _ _)
  simp only [partialRowsStrategyV2, lt_min_iff] at hζU hqsU hqeU hveU hε₀U
  obtain ⟨hζA1, hζA2, hζA2b, -, hζB1, -, -, hζC1, -, -, hζD1, -, -, hζK1, -, -⟩ := hζU
  obtain ⟨hqsA1, -, -, -, hqsB1, -, -, hqsC1, -, -, hqsD1, -, -, hqsK1, -, -⟩ := hqsU
  obtain ⟨hqeA1, -, -, -, -, -, -, -, -, -, -, -, -, hqeK1, -, -⟩ := hqeU
  obtain ⟨-, -, -, -, -, hveB2, -, -, hveC2, -, -, hveD2, -, -, hveK2, -⟩ := hveU
  obtain ⟨-, -, -, hε₀A3, -, -, hε₀B3, -, -, hε₀C3, -, -, hε₀D3, -, -, hε₀K3⟩ := hε₀U
  have hμU := (R.later.μ_lt.trans_le (min_le_right _ _)).trans_le (hTU.sectionUp_le _ _ _ _)
  simp only [partialRowsStrategyV2, lt_min_iff] at hμU
  obtain ⟨hμA, hμK⟩ := hμU
  have hbU := (R.later.b_lt.trans_le (min_le_left _ _)).trans_le (hTU.splitUp_le _ _ _ _ _)
  simp only [partialRowsStrategyV2, lt_min_iff] at hbU
  obtain ⟨hbT2, hbE3, hbE4, hbE6, hbE7⟩ := hbU
  have hβ₁U := (R.later.β₁_lt.trans_le (min_le_left _ _)).trans_le (hTU.β₁Up_le _ _ _ _ _ _)
  simp only [partialRowsStrategyV2, lt_min_iff] at hβ₁U
  obtain ⟨h1T2, h1E3, h1E4, h1E6, h1E7, h1S2, h1S3, h1S4, h1S6⟩ := hβ₁U
  have hLU := R.later.Lmax_gt
  rw [hTU.LmaxLow_eq] at hLU
  simp only [partialRowsStrategyV2, max_lt_iff] at hLU
  obtain ⟨-, hL4, hLσ, hLE3, hLE4, hLE6, hLE7, hLS2, hLS3, hLS4, hLS6⟩ := hLU
  -- stripping `posOr` at the explicit tolerances
  have hp : ∀ {x y : ℝ}, 0 < y → x < posOr_VAL3 y → x < y := fun hy h =>
    h.trans_eq (posOr_eq_VAL3 hy)
  have hΔL : 0 < 1000000 * R.later.excl.Δ := by positivity
  unfold PartialClosedRowOutsV2
  refine ⟨tcp01_gram_out_VAL3 P.toLocalChartPackets R.later.γ_pos.le
    (R.β_two_VAL2.trans_le hβ₂7.le), ?_, ?_, ?_, ?_, ?_,
    sgp01_row_out_VAL3 P.toLocalChartPacketsR hΛ0 hΔ1 hLΛ he40 hT1600 hσs0.le
      R.later.qs_le_hundredth_VAL2, ?_, ?_, ?_, ?_⟩
  · -- TCP02 at `E₀ = E`, `ν = β₃ / 3`
    have hc : 0 < R.later.circle.E ∧ 0 < R.later.excl.β₃ / 3 ∧ R.later.excl.β₃ / 3 < 1 :=
      ⟨hE0, by positivity, by linarith only [hβ₃]⟩
    obtain ⟨sσ, -, s2⟩ := Classical.choose_spec (tcp02_row_out_VAL3 hc.1 hc.2.1 hc.2.2)
    have s2' := Classical.choose_spec s2
    have s3 := Classical.choose_spec (s2'.2 _ hΔ1)
    have hc1 : 0 < R.later.circle.E ∧ 0 < R.later.excl.β₃ / 3 ∧ R.later.excl.β₃ / 3 < 1 ∧
        1 ≤ R.later.excl.Δ := ⟨hc.1, hc.2.1, hc.2.2, hΔ1⟩
    have hν3 : 3 * (R.later.excl.β₃ / 3) ≤ R.β 3 := by
      rw [R.β_three_VAL2]
      linarith only []
    have hβ3 : R.β 3 < 1 := by
      rw [R.β_three_VAL2]
      linarith only [hβ₃]
    have h3σ : 3 * R.later.excl.β₂ < posOr_VAL3 (tcp02σ_VAL4 R.later.circle.E
        (R.later.excl.β₃ / 3)) := (lt_div_iff₀' three_pos).mp hβ₂σ
    have hσ : 3 * R.later.excl.β₂ <
        Classical.choose (tcp02_row_out_VAL3 hc.1 hc.2.1 hc.2.2) :=
      lt_of_lt_posOr_dite_VAL4 hc sσ h3σ
    have hη : R.later.excl.β₂ < Classical.choose s2 := lt_of_lt_posOr_dite_VAL4 hc s2'.1 hβ₂η
    have hη1 : R.later.split.β₁ < Classical.choose (s2'.2 _ hΔ1) :=
      lt_of_lt_posOr_dite_VAL4 hc1 s3.1 h1T2
    have hb1 : R.later.split.b < Classical.choose (s2'.2 _ hΔ1) :=
      lt_of_lt_posOr_dite_VAL4 hc1 s3.1 hbT2
    have hσL : (Classical.choose (tcp02_row_out_VAL3 hc.1 hc.2.1 hc.2.2))⁻¹ ≤ R.later.Lmax :=
      inv_le_of_dite_le_VAL4 hc hLσ.le
    exact s3.2 P.toLocalChartPackets hΛ0 hμ hτ hLΛ hL4.le he40 hT1600 hν3 hβ3
      (R.β_two_VAL2 ▸ hσ.le) (R.β_two_VAL2 ▸ hη.le) (R.β_one_VAL2.trans_le hη1.le) hb1.le hσL
  · -- EGP03 at `E`
    have hc : 1 ≤ R.later.excl.Δ ∧ 0 < R.later.excl.β₂ ∧ R.later.excl.β₂ < 1 / 1000000 ∧
        0 < R.later.circle.E := ⟨hΔ1, hβ₂0, hβ₂6, hE0⟩
    have s := choose₂_spec_VAL4 (egp03_row_out_VAL3 hc.1 hc.2.1 hc.2.2.1 hc.2.2.2)
    exact s.2.2 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
      P.toLocalChartFamilyE (lt_of_lt_posOr_dite_VAL4 hc s.2.1 hbE3).le hs6
      (R.β_one_VAL2.trans_le (lt_of_lt_posOr_dite_VAL4 hc s.2.1 h1E3).le)
      (le_of_dite_le_VAL4 hc hLE3.le) hΛ0 hLΛ hμ hτ
  · -- EGP04 at `θ_e`
    have hc : 1 ≤ R.later.excl.Δ ∧ 0 < R.later.excl.β₂ ∧ R.later.excl.β₂ < 1 / 1000000 ∧
        0 < R.later.circle.θe ∧ R.later.circle.θe < 1 := ⟨hΔ1, hβ₂0, hβ₂6, hθe0, hθe1⟩
    have s := choose₂_spec_VAL4 (egp04_row_RVZ_out_VAL3 hc.1 hc.2.1 hc.2.2.1 hc.2.2.2.1
      hc.2.2.2.2)
    have hA1 : 0 < R.later.circle.θe ^ 2 / 10 ^ 8 := by positivity
    exact s.2.2 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
      P.toLocalChartPacketsRVZ (lt_of_lt_posOr_dite_VAL4 hc s.2.1 hbE4).le hs6
      (R.β_one_VAL2.trans_le (lt_of_lt_posOr_dite_VAL4 hc s.2.1 h1E4).le)
      (le_of_dite_le_VAL4 hc hLE4.le) hΛ0 hLΛ hμ hτ (hp hA1 hqeA1).le
      ((lt_div_iff₀ hΔ0).mp (hp (by positivity) hμA)) hσs0 (hp hA1 hqsA1).le hve he40 hT1600
      hΛz hζ0 (hp hA1 hζA1).le (hp (by positivity) hζA2).le
      (hεr.trans (hp (by positivity) hε₀A3))
  · -- EGP06 at `e₁`
    have hc : 1 ≤ R.later.excl.Δ ∧ 0 < R.later.excl.β₂ ∧ R.later.excl.β₂ < 1 / 1000000 ∧
        0 < R.stage.e 1 ∧ R.stage.e 1 < 1 / 100 :=
      ⟨hΔ1, hβ₂0, hβ₂6, hrange1.2.2.2.2.2.1, hrange1.2.2.2.2.2.2.1⟩
    have s := choose₂_spec_VAL4 (egp06_row_out_VAL3 hc.1 hc.2.1 hc.2.2.1 hc.2.2.2.1 hc.2.2.2.2)
    have hK1 : 0 < (R.stage.e 1 / (20 * egpGraphConst)) ^ 2 / 10 ^ 8 := by positivity
    exact s.2.2 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
      P.toLocalChartPacketsRVZ (lt_of_lt_posOr_dite_VAL4 hc s.2.1 hbE6).le hs6
      (R.β_one_VAL2.trans_le (lt_of_lt_posOr_dite_VAL4 hc s.2.1 h1E6).le)
      (le_of_dite_le_VAL4 hc hLE6.le) hΛ0 hLΛ hμ hτ (hp hK1 hqeK1).le
      ((lt_div_iff₀ hΔ0).mp (hp (by positivity) hμK)) hσs0 (hp hK1 hqsK1).le
      (hp (by positivity) hveK2) he40 hT1600 hΛz hζ0 (hp hK1 hζK1).le
      (hp (by positivity) hζA2).le (hεr.trans (hp (by positivity) hε₀K3))
  · -- EGP07 at the edge stage values
    have hc : 1 ≤ R.later.excl.Δ ∧ 0 < R.later.excl.β₂ ∧ R.later.excl.β₂ < 1 / 1000000 ∧
        R.stage.Γ 1 ∈ Ioo (0 : ℝ) 1 ∧ 0 < R.stage.Sig 1 ∧
        R.stage.Sig 1 < min (R.stage.Γ 1 / 200) (R.stage.Γ 1 ^ 3 / (100 * egpGraphConst)) ∧
        0 < R.stage.e 1 ∧
        R.stage.e 1 < min (1 / 100) (min (R.stage.Γ 1 * R.stage.Sig 1 / 100)
          (R.stage.Sig 1 / 1000)) := ⟨hΔ1, hβ₂0, hβ₂6, R.stage.egp07_range_VAL3 hC⟩
    have s := choose₂_spec_VAL4 (egp07_row_C14_out_VAL3 hc.1 hc.2.1 hc.2.2.1 hc.2.2.2.1
      hc.2.2.2.2.1 hc.2.2.2.2.2.1 hc.2.2.2.2.2.2.1 hc.2.2.2.2.2.2.2)
    have hK1 : 0 < (R.stage.e 1 / (20 * egpGraphConst)) ^ 2 / 10 ^ 8 := by positivity
    exact s.2.2 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
      P (lt_of_lt_posOr_dite_VAL4 hc s.2.1 hbE7).le hs6
      (R.β_one_VAL2.trans_le (lt_of_lt_posOr_dite_VAL4 hc s.2.1 h1E7).le)
      (le_of_dite_le_VAL4 hc hLE7.le) hΛ0 hLΛ hμ hτ (hp hK1 hqeK1).le
      ((lt_div_iff₀ hΔ0).mp (hp (by positivity) hμK)) hσs0 (hp hK1 hqsK1).le
      (hp (by positivity) hveK2) he40 hT1600 hΛz hζ0 (hp hK1 hζK1).le
      (hp (by positivity) hζA2).le (hεr.trans (hp (by positivity) hε₀K3))
  · -- SGP02 at `E`
    have hc : 1 ≤ R.later.excl.Δ ∧ 0 < R.later.excl.β₂ ∧ R.later.excl.β₂ < 1 ∧
        0 < R.later.circle.E := ⟨hΔ1, hβ₂0, hβ₂1, hE0⟩
    have s := choose₂_spec_VAL4 (sgp02_row_out_VAL3 hc.1 hc.2.1 hc.2.2.1 hc.2.2.2)
    exact s.2.2 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
      P.toLocalChartFamilyQ R.β_two_VAL2
      (R.β_one_VAL2.trans_le (lt_of_lt_posOr_dite_VAL4 hc s.2.1 h1S2).le)
      (le_of_dite_le_VAL4 hc hLS2.le) hΛ0 hLΛ
  · -- SGP03 at `θ_s` with accuracy `θ_s² / (2·10⁶)`
    have hθ2 : 0 < R.later.circle.θs ^ 2 := by positivity
    have hc : 1 ≤ R.later.excl.Δ ∧ 0 < R.later.excl.β₂ ∧ R.later.excl.β₂ < 1 ∧
        0 < R.later.circle.θs ∧ R.later.circle.θs < 1 ∧
        0 < R.later.circle.θs ^ 2 / (2 * 10 ^ 6) ∧
        R.later.circle.θs ^ 2 / (2 * 10 ^ 6) < R.later.circle.θs ^ 2 / 10 ^ 6 :=
      ⟨hΔ1, hβ₂0, hβ₂1, hθs0, hθs1, by positivity, by linarith only [hθ2]⟩
    have s := choose₂_spec_VAL4 (sgp03_zero_row_out_VAL3 hc.1 hc.2.1 hc.2.2.1 hc.2.2.2.1
      hc.2.2.2.2.1 hc.2.2.2.2.2.1 hc.2.2.2.2.2.2)
    have hB1 : 0 < R.later.circle.θs ^ 2 / 10 ^ 6 := by positivity
    exact s.2.2 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
      P.toLocalChartPacketsRVZ R.β_two_VAL2
      (R.β_one_VAL2.trans_le (lt_of_lt_posOr_dite_VAL4 hc s.2.1 h1S3).le)
      (le_of_dite_le_VAL4 hc hLS3.le) hΛ0 hLΛ he40 hT1600 hΛz hσs0 (hp hB1 hqsB1)
      (hp (by positivity) hveB2) hζ0 (hp hB1 hζB1) (hp (by positivity) hζA2b)
      (hεr.trans (hp (by positivity) hε₀B3))
  · -- SGP04 at `e₂`
    have hc : 1 ≤ R.later.excl.Δ ∧ 0 < R.later.excl.β₂ ∧ R.later.excl.β₂ < 1 ∧
        0 < R.stage.e 2 ∧ R.stage.e 2 < 1 / 100 :=
      ⟨hΔ1, hβ₂0, hβ₂1, hrange2.2.2.2.2.2.1, hrange2.2.2.2.2.2.2.1⟩
    have s := Classical.choose_spec (sgp04_row_out_VAL3 hc.1 hc.2.1 hc.2.2.1 hc.2.2.2.1
      hc.2.2.2.2)
    have s' := choose₂_spec_VAL4 s.2.2
    have e : sgp04θ_VAL4 R.later.excl.Δ R.later.excl.β₂ (R.stage.e 2) =
        Classical.choose (sgp04_row_out_VAL3 hc.1 hc.2.1 hc.2.2.1 hc.2.2.2.1 hc.2.2.2.2) :=
      dite_eq_left hc
    rw [e] at hqsC1 hveC2 hζC1 hε₀C3
    have hC1 : 0 < Classical.choose (sgp04_row_out_VAL3 hc.1 hc.2.1 hc.2.2.1 hc.2.2.2.1
        hc.2.2.2.2) ^ 2 / 10 ^ 6 := by have := s.1; positivity
    exact s'.2.2 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
      P.toLocalChartPacketsRVZ R.β_two_VAL2
      (R.β_one_VAL2.trans_le (lt_of_lt_posOr_dite_VAL4 hc s'.2.1 h1S4).le)
      (le_of_dite_le_VAL4 hc hLS4.le) hΛ0 hLΛ he40 hT1600 hΛz hσs0 (hp hC1 hqsC1)
      (hp (by have := s.1; positivity) hveC2) hζ0 (hp hC1 hζC1) (hp (by positivity) hζA2b)
      (hεr.trans (hp (by have := s.1; positivity) hε₀C3))
  · -- SGP06 at the slim stage values
    have hc : 1 ≤ R.later.excl.Δ ∧ 0 < R.later.excl.β₂ ∧ R.later.excl.β₂ < 1 ∧
        0 < R.stage.Γ 2 ∧ R.stage.Γ 2 < 1 ∧ 0 < R.stage.Sig 2 ∧
        R.stage.Sig 2 < R.stage.Γ 2 / 200 ∧
        R.stage.Sig 2 < R.stage.Γ 2 ^ 3 / (100 * sgpGraphBound) ∧ 0 < R.stage.e 2 ∧
        R.stage.e 2 < 1 / 100 ∧ R.stage.e 2 < R.stage.Γ 2 * R.stage.Sig 2 / 100 :=
      ⟨hΔ1, hβ₂0, hβ₂1, R.stage.sgp06_range_VAL3 hC⟩
    have s := Classical.choose_spec (sgp06_row_C14_out_VAL3 hc.1 hc.2.1 hc.2.2.1 hc.2.2.2.1
      hc.2.2.2.2.1 hc.2.2.2.2.2.1 hc.2.2.2.2.2.2.1 hc.2.2.2.2.2.2.2.1 hc.2.2.2.2.2.2.2.2.1
      hc.2.2.2.2.2.2.2.2.2.1 hc.2.2.2.2.2.2.2.2.2.2)
    have s' := choose₂_spec_VAL4 s.2.2
    have e : sgp06θ_VAL4 R.later.excl.Δ R.later.excl.β₂ (R.stage.Γ 2) (R.stage.Sig 2)
        (R.stage.e 2) = Classical.choose (sgp06_row_C14_out_VAL3 hc.1 hc.2.1 hc.2.2.1
          hc.2.2.2.1 hc.2.2.2.2.1 hc.2.2.2.2.2.1 hc.2.2.2.2.2.2.1 hc.2.2.2.2.2.2.2.1
          hc.2.2.2.2.2.2.2.2.1 hc.2.2.2.2.2.2.2.2.2.1 hc.2.2.2.2.2.2.2.2.2.2) :=
      dite_eq_left hc
    rw [e] at hqsD1 hveD2 hζD1 hε₀D3
    have hD1 := s.1
    exact s'.2.2 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
      P R.β_two_VAL2
      (R.β_one_VAL2.trans_le (lt_of_lt_posOr_dite_VAL4 hc s'.2.1 h1S6).le)
      (le_of_dite_le_VAL4 hc hLS6.le) hΛ0 hLΛ he40 hT1600 hΛz hσs0 (hp (by positivity) hqsD1)
      (hp (by positivity) hveD2) hζ0 (hp (by positivity) hζD1) (hp (by positivity) hζA2b)
      (hεr.trans (hp (by positivity) hε₀D3))

/-- **The realization with the 11 rows on `LocalChartPacketsC14D`** (review 52, order of work steps
3–4, PARTIAL): with `C_ge`, ONE common strategy `T` (refining the rows strategy) at which every
staged register is realized on its tail by the final family `LocalChartPacketsC14D`
(FC39-VAL4 G1), and every instance at every register carries the conclusions of TCP01, TCP02,
EGP03, EGP04, EGP06, EGP07, SGP01, SGP02, SGP03, SGP04, SGP06 at the register's values. -/
theorem exists_closed_realization_rows_C14D_VAL4 (K : ℕ) (hK : 10 ≤ K) (A : ℝ → ℝ)
    (hA : ∀ x, 0 < x → 0 < A x) (Wseq : ℕ → CompactCarrier.{u})
    (gseq : ∀ m, SmoothRiemannianMetric (Wseq m).model (Wseq m).Carrier)
    (hf : ∀ m, ClosedMemberFacts (Wseq m))
    (hg : ∀ m, closedCollapseHypotheses (Wseq m) (gseq m) K A (closedCounterexampleRatio (m + 2)))
    {D : ClosedEarlyData} (hC : ∀ j, gafGraphConst j ≤ D.C j) :
    ∃ T : ClosedThresholdsV2 D, (∀ m, T.H m = (m : ℝ) + 2) ∧
      T.lc18 ≤ threeSplittingExclusionThreshold.{0, 0} ∧
      PartialClosedFamilyAtC14DV2 K Wseq gseq T ∧
      ∀ (R : ClosedRegisterV2 D T) (δ εr Λz : ℝ), εr < R.later.err.co.ε₀ →
        20 * Λz ≤ R.later.split.T₀ → ∀ m (M : ClosedModel (Wseq m) (gseq m))
        (F : PartialClosedFamilyInstanceC14DV2 K R M δ εr Λz),
        PartialClosedRowOutsV2 R F.family.toLocalChartPacketsC14 := by
  obtain ⟨T, hTU, hH, hlc, hfam⟩ :=
    exists_closed_realization_C14D_VAL4 K hK A hA Wseq gseq hf hg (partialRowsStrategyV2 D)
  exact ⟨T, hH, hlc, hfam, fun R _ _ _ hεr hΛz _ _ F =>
    partialRowOuts_of_refines_VAL4 hC hTU R hεr hΛz F.family.toLocalChartPacketsC14⟩

end DifferentialGeometry.Geometry.Collapse
