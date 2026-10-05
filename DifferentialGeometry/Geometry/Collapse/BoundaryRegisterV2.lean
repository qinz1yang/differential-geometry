import DifferentialGeometry.Geometry.Collapse.StaticRegisterV2
import DifferentialGeometry.Geometry.Collapse.BoundaryRegister

/-!
# The boundary static register on the staged closed register (BBR01; review 52, R-a)

Review 52, item R-a: "`BoundaryRegister` and the seven wrappers follow" the staged closed register
`ClosedRegisterV2`. BBR01 (B:10356–10565) retains the whole closed register PR01–PR28 for the
original interior blocks (B:10530–10532); this file is `BoundaryRegister.lean` (kept unchanged as
history; its `BoundaryEarlyData`, `boundaryVolumeCap` and `boundaryPhysicalBound` are reused) with
the interior part replaced by the staged `ClosedLaterV2`. The boundary choices BR11–BR25 and their
displayed inequalities are verbatim; the later boundary slots read the staged values
`ClosedLaterValuesV2` (which include `σ_col` and `L_max`). As before the interior `w` threshold is
intersected with `w_cap = ω₃/4` (BR20, B:10445–10447) and the interior test radius is
`H_n = n/4` (BR25, B:10494). Nothing here mentions a carrier.
-/

set_option autoImplicit false

noncomputable section

open Filter Set
open scoped Topology

namespace DifferentialGeometry.Geometry.Collapse

/-- The plain values of the staged later closed choices (no inequalities): what a later boundary
producer threshold may read. -/
structure ClosedLaterValuesV2 where
  circle : ClosedCircleRequestsV2
  excl : ClosedExclusions
  err : ClosedErrorsV2
  scale : ClosedScales
  split : ClosedSplittings
  Lmax : ℝ
  tail : ℕ

/-- The values of a staged later closed choice. -/
def ClosedLaterV2.values {D : ClosedEarlyData} {T : ClosedThresholdsV2 D} {st : ClosedStage D}
    (la : ClosedLaterV2 D T st) : ClosedLaterValuesV2 :=
  ⟨la.circle, la.excl, la.err, la.scale, la.split, la.Lmax, la.tail⟩

/-- The producer thresholds consumed by the boundary register on the staged closed register. -/
structure BoundaryThresholdsV2 (D : BoundaryEarlyData) where
  /-- BR11 (B:10404–10406): the square-sum budget of BCG02–BCG03 for `ϑ_j`. -/
  ϑUp : ClosedStage D.toClosedEarlyData → ℝ
  ϑUp_pos : ∀ st, 0 < ϑUp st
  /-- BR13 (B:10409–10411): the short circle-axis raw/value/norm error request at the original
  short test radii 5000/1000. -/
  shortUp : ClosedStage D.toClosedEarlyData → (Fin 3 → ℝ) → ℝ
  shortUp_pos : ∀ st ϑ, 0 < shortUp st ϑ
  /-- BR14–BR19 (B:10418–10424): BCG02's one-vector test request at `ϑ₂, ϑ₃`. -/
  bcgUp : ClosedStage D.toClosedEarlyData → (Fin 3 → ℝ) → ℝ
  bcgUp_pos : ∀ st ϑ, 0 < bcgUp st ϑ
  /-- BR04–BR23 (B:10389–10450): the staged closed slots of the original interior producers,
  augmented by the boundary producers, as a function of the boundary requests. -/
  interior : (Fin 3 → ℝ) → ℝ → ℝ → ClosedThresholdsV2 D.toClosedEarlyData
  /-- BR24 (B:10455–10463): the cusp splitting, norm and buffer thresholds. -/
  cuspUp : ClosedStage D.toClosedEarlyData → (Fin 3 → ℝ) → ℝ → ℝ → ClosedLaterValuesV2 → ℝ
  cuspUp_pos : ∀ st ϑ sh bc v, 0 < cuspUp st ϑ sh bc v
  /-- BR24 (B:10464–10465): the cusp test radii and first-exit buffers (lower bound for `H_∂`). -/
  cuspRadii : ClosedStage D.toClosedEarlyData → (Fin 3 → ℝ) → ℝ → ℝ → ClosedLaterValuesV2 →
    ℝ → ℝ
  /-- BR24 (B:10466–10471): BCP02's positive product and first-exit bounds on `r_∂`. -/
  productUp : ClosedStage D.toClosedEarlyData → (Fin 3 → ℝ) → ℝ → ℝ → ClosedLaterValuesV2 →
    ℝ → ℝ → ℝ
  productUp_pos : ∀ st ϑ sh bc v q H, 0 < productUp st ϑ sh bc v q H
  /-- BR25 (B:10488–10496): the finite maximum of the local/overlap and boundary producer tails. -/
  tailLow : ClosedStage D.toClosedEarlyData → (Fin 3 → ℝ) → ℝ → ℝ → ClosedLaterValuesV2 →
    ℝ → ℝ → ℝ → ℕ
  /-- BR25 (B:10500–10505): the finitely many fixed constants of (BRegInterior). -/
  fixedConstants : Finset ℝ

/-- BR20 and BR25: the staged closed slots actually used by the boundary register (interior `w`
threshold intersected with `w_cap`, test radius `H_n = n/4`). -/
def BoundaryThresholdsV2.toClosed {D : BoundaryEarlyData} (T : BoundaryThresholdsV2 D)
    (ϑ : Fin 3 → ℝ) (sh bc : ℝ) : ClosedThresholdsV2 D.toClosedEarlyData :=
  { T.interior ϑ sh bc with
    wUp := fun st ci ex er Λ => min ((T.interior ϑ sh bc).wUp st ci ex er Λ) boundaryVolumeCap
    wUp_pos := fun st ci ex er Λ =>
      lt_min ((T.interior ϑ sh bc).wUp_pos st ci ex er Λ) boundaryVolumeCap_pos
    H := fun n => (n : ℝ) / 4
    H_tendsto := tendsto_natCast_atTop_atTop.atTop_div_const (by norm_num) }

/-- BBR01's register BR00–BR31 on the staged closed register. -/
structure BoundaryRegisterV2 (D : BoundaryEarlyData) (T : BoundaryThresholdsV2 D) where
  stage : ClosedStage D.toClosedEarlyData
  ϑ : Fin 3 → ℝ
  shortErr : ℝ
  bcgErr : ℝ
  later : ClosedLaterV2 D.toClosedEarlyData (T.toClosed ϑ shortErr bcgErr) stage
  cuspQuality : ℝ
  cuspRadius : ℝ
  physicalScale : ℝ
  tail : ℕ
  -- BR11 (B:10403–10408)
  ϑ_pos : ∀ j, 0 < ϑ j
  ϑ_lt : ∀ j, ϑ j < min (1 / 100) (T.ϑUp stage)
  ϑ_e : ∀ j, 3 * D.P * ϑ j < stage.e j / 4
  -- BR13 (B:10409–10411)
  shortErr_pos : 0 < shortErr
  shortErr_lt : shortErr < min (ϑ 0 ^ 2 / 10 ^ 8) (T.shortUp stage ϑ)
  -- BR14–BR19 (B:10418–10424)
  bcgErr_pos : 0 < bcgErr
  bcgErr_lt : bcgErr < min (min (ϑ 1 ^ 2 / 10 ^ 8) (ϑ 2 ^ 2 / 10 ^ 8)) (T.bcgUp stage ϑ)
  -- BR24 (B:10455–10466)
  cuspQuality_pos : 0 < cuspQuality
  cuspQuality_lt : cuspQuality < min (T.cuspUp stage ϑ shortErr bcgErr later.values)
    later.split.β₁
  cuspRadius_ge : max 1 (T.cuspRadii stage ϑ shortErr bcgErr later.values cuspQuality) ≤
    cuspRadius
  -- BR24 (BRegPhysical, B:10473–10484)
  physicalScale_pos : 0 < physicalScale
  physicalScale_lt : physicalScale <
    min (boundaryPhysicalBound (closedLongLength later.excl) (stage.c 2) cuspRadius ϑ)
      (T.productUp stage ϑ shortErr bcgErr later.values cuspQuality cuspRadius)
  -- BR25 (B:10486–10512)
  tail_ge_later : later.tail ≤ tail
  tail_ge : T.tailLow stage ϑ shortErr bcgErr later.values cuspQuality cuspRadius physicalScale ≤
    tail
  tail_wPrime : ∀ n : ℕ, tail ≤ n → (n : ℝ)⁻¹ ≤ closedWPrime later.scale
  tail_testRadius : ∀ n : ℕ, tail ≤ n → 400 * later.split.V < (n : ℝ) / 4
  tail_fixed : ∀ n : ℕ, tail ≤ n → ∀ C ∈ T.fixedConstants, 16 * C / 5 < n
  tail_edgeCollar : ∀ n : ℕ, tail ≤ n → 16 * (100 * later.excl.Δ) / 5 < n
  tail_Δ : ∀ n : ℕ, tail ≤ n → 48 * later.excl.Δ < n

/-! ### Existence (BBR01) -/

private theorem natCast_gt_of_ceil_add_one_le_VAL2 {M : ℝ} {n : ℕ} (h : ⌈M⌉₊ + 1 ≤ n) :
    M < n := by
  have h1 : M ≤ (⌈M⌉₊ : ℝ) := Nat.le_ceil M
  have h2 : ((⌈M⌉₊ + 1 : ℕ) : ℝ) ≤ n := by exact_mod_cast h
  push_cast at h2
  linarith

/-- **BBR01 on the staged register** (B:10356): for every augmented early data and every positive
boundary threshold record the boundary register admits one assignment. -/
theorem exists_boundaryRegisterV2 (D : BoundaryEarlyData) (T : BoundaryThresholdsV2 D) :
    Nonempty (BoundaryRegisterV2 D T) := by
  obtain ⟨st⟩ := exists_closedStage D.toClosedEarlyData
  have hP : 0 < D.P := D.toClosedEarlyData.P_pos
  -- BR11
  let ϑ : Fin 3 → ℝ := fun j => min (min (1 / 100) (T.ϑUp st)) (st.e j / (12 * D.P)) / 2
  have hϑb : ∀ j, 0 < min (min (1 / 100) (T.ϑUp st)) (st.e j / (12 * D.P)) := fun j => by
    have := st.e_pos j
    exact lt_min (lt_min (by norm_num) (T.ϑUp_pos st)) (by positivity)
  have hϑ : ∀ j, 0 < ϑ j := fun j => half_pos (hϑb j)
  have hϑl : ∀ j, ϑ j < min (min (1 / 100) (T.ϑUp st)) (st.e j / (12 * D.P)) :=
    fun j => half_lt_self (hϑb j)
  -- BR13, BR14–BR19
  have hshb : 0 < min (ϑ 0 ^ 2 / 10 ^ 8) (T.shortUp st ϑ) :=
    lt_min (by have := hϑ 0; positivity) (T.shortUp_pos st ϑ)
  have hbcb : 0 < min (min (ϑ 1 ^ 2 / 10 ^ 8) (ϑ 2 ^ 2 / 10 ^ 8)) (T.bcgUp st ϑ) :=
    lt_min (lt_min (by have := hϑ 1; positivity) (by have := hϑ 2; positivity))
      (T.bcgUp_pos st ϑ)
  set sh := min (ϑ 0 ^ 2 / 10 ^ 8) (T.shortUp st ϑ) / 2 with hsh
  set bc := min (min (ϑ 1 ^ 2 / 10 ^ 8) (ϑ 2 ^ 2 / 10 ^ 8)) (T.bcgUp st ϑ) / 2 with hbc
  -- BR04–BR23
  obtain ⟨la⟩ := exists_closedLaterV2 D.toClosedEarlyData (T.toClosed ϑ sh bc) st
  -- BR24
  have hqb : 0 < min (T.cuspUp st ϑ sh bc la.values) la.split.β₁ :=
    lt_min (T.cuspUp_pos st ϑ sh bc la.values) la.β₁_pos
  set q := min (T.cuspUp st ϑ sh bc la.values) la.split.β₁ / 2 with hq
  set H := max 1 (T.cuspRadii st ϑ sh bc la.values q) with hH
  have hHpos : 0 < H := zero_lt_one.trans_le (le_max_left _ _)
  have hLpos : 0 < closedLongLength la.excl := la.longLength_pos_VAL2
  have hrb : 0 < min (boundaryPhysicalBound (closedLongLength la.excl) (st.c 2) H ϑ)
      (T.productUp st ϑ sh bc la.values q H) :=
    lt_min (boundaryPhysicalBound_pos hLpos (st.c_pos 2) hHpos hϑ)
      (T.productUp_pos st ϑ sh bc la.values q H)
  set r := min (boundaryPhysicalBound (closedLongLength la.excl) (st.c 2) H ϑ)
      (T.productUp st ϑ sh bc la.values q H) / 2 with hr
  -- BR25
  obtain ⟨x, hx⟩ := Finset.exists_gt_bounds T.fixedConstants (fun C => 16 * C / 5)
  set M : ℝ := max ((closedWPrime la.scale)⁻¹) (max (1600 * la.split.V)
    (max x (max (16 * (100 * la.excl.Δ) / 5) (48 * la.excl.Δ)))) with hM
  have hw' := la.wPrime_pos_VAL2
  refine ⟨{
    stage := st, ϑ := ϑ, shortErr := sh, bcgErr := bc, later := la
    cuspQuality := q, cuspRadius := H, physicalScale := r
    tail := max (max la.tail (T.tailLow st ϑ sh bc la.values q H r)) (⌈M⌉₊ + 1)
    ϑ_pos := hϑ
    ϑ_lt := fun j => (hϑl j).trans_le (min_le_left _ _)
    ϑ_e := ?_
    shortErr_pos := half_pos hshb, shortErr_lt := half_lt_self hshb
    bcgErr_pos := half_pos hbcb, bcgErr_lt := half_lt_self hbcb
    cuspQuality_pos := half_pos hqb, cuspQuality_lt := half_lt_self hqb
    cuspRadius_ge := le_rfl
    physicalScale_pos := half_pos hrb, physicalScale_lt := half_lt_self hrb
    tail_ge_later := (le_max_left _ _).trans (le_max_left _ _)
    tail_ge := (le_max_right _ _).trans (le_max_left _ _)
    tail_wPrime := ?_, tail_testRadius := ?_, tail_fixed := ?_
    tail_edgeCollar := ?_, tail_Δ := ?_ }⟩
  · intro j
    have h := (hϑl j).trans_le (min_le_right _ _)
    rw [lt_div_iff₀ (by positivity)] at h
    linarith
  all_goals intro n hn
  all_goals have hMn : M < n := natCast_gt_of_ceil_add_one_le_VAL2 ((le_max_right _ _).trans hn)
  · have h1 : (closedWPrime la.scale)⁻¹ < n := (le_max_left _ _).trans_lt hMn
    have hn0 : (0 : ℝ) < n := (inv_pos.mpr hw').trans h1
    exact (inv_le_comm₀ hn0 hw').mpr h1.le
  · have h1 : 1600 * la.split.V < n :=
      ((le_max_left _ _).trans (le_max_right _ _)).trans_lt hMn
    linarith
  · intro C hC
    exact (hx C hC).trans (((le_max_left _ _).trans ((le_max_right _ _).trans
      (le_max_right _ _))).trans_lt hMn)
  · exact ((le_max_left _ _).trans ((le_max_right _ _).trans ((le_max_right _ _).trans
      (le_max_right _ _)))).trans_lt hMn
  · exact ((le_max_right _ _).trans ((le_max_right _ _).trans ((le_max_right _ _).trans
      (le_max_right _ _)))).trans_lt hMn

/-! ### Elementary consequences -/

namespace BoundaryRegisterV2

variable {D : BoundaryEarlyData} {T : BoundaryThresholdsV2 D}

/-- BR20 (B:10446): the chosen volume parameter lies below `w_cap`. -/
theorem w_lt_cap_VAL2 (R : BoundaryRegisterV2 D T) : R.later.scale.w < boundaryVolumeCap := by
  have h := R.later.w_lt
  simp only [BoundaryThresholdsV2.toClosed, lt_min_iff] at h
  exact h.1.2

/-- BR24 (B:10463): the cusp splitting quality is below `β₁`. -/
theorem cuspQuality_lt_β₁_VAL2 (R : BoundaryRegisterV2 D T) :
    R.cuspQuality < R.later.split.β₁ :=
  R.cuspQuality_lt.trans_le (min_le_right _ _)

theorem one_le_cuspRadius_VAL2 (R : BoundaryRegisterV2 D T) : 1 ≤ R.cuspRadius :=
  (le_max_left _ _).trans R.cuspRadius_ge

/-- (BRegPhysical) (B:10477): `r_∂ < 1/(1000L)`. -/
theorem physicalScale_lt_long_VAL2 (R : BoundaryRegisterV2 D T) :
    R.physicalScale < 1 / (1000 * closedLongLength R.later.excl) :=
  R.physicalScale_lt.trans_le ((min_le_left _ _).trans (min_le_left _ _))

/-- (BRegPhysical) (B:10477): `r_∂ < 10⁻⁴`. -/
theorem physicalScale_lt_small_VAL2 (R : BoundaryRegisterV2 D T) :
    R.physicalScale < 1 / 10 ^ 4 :=
  R.physicalScale_lt.trans_le ((min_le_left _ _).trans
    ((min_le_right _ _).trans (min_le_left _ _)))

/-- CAA01 (B:10679–10710) in the staged boundary register: EGP01's four-target error is below
`10⁻³`. -/
theorem edgeError_lt_obstruction_VAL2 (R : BoundaryRegisterV2 D T) :
    5 * R.later.excl.β₂ + R.later.split.b + R.later.err.s < 1 / 1000 :=
  R.later.edgeError_lt_obstruction_VAL2

/-- The interior test radius of the boundary register is `H_n = n/4` (BR25, B:10494). -/
theorem interior_H_VAL2 (R : BoundaryRegisterV2 D T) (n : ℕ) :
    (T.toClosed R.ϑ R.shortErr R.bcgErr).H n = (n : ℝ) / 4 := rfl

end BoundaryRegisterV2

/-- CAA01 for both staged registers (B:10787, B:10794): for the same early data, both refined
assignments exist. -/
theorem exists_closed_and_boundary_registersV2 (D : BoundaryEarlyData)
    (Tc : ClosedThresholdsV2 D.toClosedEarlyData) (Tb : BoundaryThresholdsV2 D) :
    Nonempty (ClosedRegisterV2 D.toClosedEarlyData Tc × BoundaryRegisterV2 D Tb) := by
  obtain ⟨Rc⟩ := exists_closedRegisterV2 D.toClosedEarlyData Tc
  obtain ⟨Rb⟩ := exists_boundaryRegisterV2 D Tb
  exact ⟨(Rc, Rb)⟩

end DifferentialGeometry.Geometry.Collapse
