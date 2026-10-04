import DifferentialGeometry.Geometry.Collapse.StaticRegister
import DifferentialGeometry.Analysis.ParameterSelection.Acyclic

/-!
# The boundary static register (chapter 14, BBR01 and CAA01)

Blueprint 207B, `prop:fibration-boundary-register-admissibility` (BBR01, B:10356–10565), with
the active edge-exclusion reading of CAA01 (B:10679–10722). The boundary register retains the
whole closed register PR01–PR28 for the original interior blocks (B:10530–10532), on the
augmented early constants, and adds the boundary free choices BR11–BR25: the early circle
requests `ϑ_j`, the short circle-axis and BCG02 one-vector requests, the late cusp quality, the
common cusp test radius `H_∂`, the physical boundary scale `r_∂` and one uniform tail.

As in `StaticRegister`, the register is DATA. The producers' positive thresholds are slots of
`BoundaryThresholds`, each a function of the earlier register values only. The interior slots may
depend on the boundary requests `ϑ, shortErr, bcgErr` (BR11–BR19 precede `Δ` and `b`); before `w`
is chosen the interior `w` threshold is intersected with `w_cap = ω₃/4` (BR20, B:10445–10447),
and the interior test radius is the explicit `H_n = n/4` (BR25, B:10494).
The assignment is independent of the sequence member, point and boundary component
(B:10362–10363): nothing here mentions a carrier.
-/

set_option autoImplicit false

noncomputable section

open Filter Set
open scoped Topology

namespace DifferentialGeometry.Geometry.Collapse

/-- BR00 (B:10371) and the boundary scope (B:10351): the auxiliary cap `w_cap = ω₃/4`. -/
def boundaryVolumeCap : ℝ := euclideanThreeUnitBallVolume / 4

theorem boundaryVolumeCap_pos : 0 < boundaryVolumeCap := by
  unfold boundaryVolumeCap euclideanThreeUnitBallVolume
  positivity

theorem boundaryVolumeCap_lt : boundaryVolumeCap < euclideanThreeUnitBallVolume := by
  have : 0 < euclideanThreeUnitBallVolume := by
    unfold euclideanThreeUnitBallVolume
    positivity
  unfold boundaryVolumeCap
  linarith

/-- The plain values of the later closed choices PR11–PR25 (no inequalities): what a later
producer threshold may read. -/
structure ClosedLaterValues where
  circle : ClosedCircleRequests
  excl : ClosedExclusions
  err : ClosedErrors
  scale : ClosedScales
  split : ClosedSplittings
  tail : ℕ

/-- The values of a later closed choice. -/
def ClosedLater.values {D : ClosedEarlyData} {T : ClosedThresholds D} {st : ClosedStage D}
    (la : ClosedLater D T st) : ClosedLaterValues :=
  ⟨la.circle, la.excl, la.err, la.scale, la.split, la.tail⟩

/-- BR00–BR03 (B:10370–10388): the augmented early constants. The closed part is PR01's data
with one more whole-list slot for the boundary blocks (BCG01) and `P` also bounding
`‖𝓑'‖∞, ‖𝓑''‖∞` (BCG.0); `δStar, C₀` are BSA01's numerical constants. -/
structure BoundaryEarlyData extends ClosedEarlyData where
  δStar : ℝ
  δStar_pos : 0 < δStar
  C₀ : ℝ
  C₀_pos : 0 < C₀

/-- The producer thresholds consumed by the boundary register. -/
structure BoundaryThresholds (D : BoundaryEarlyData) where
  /-- BR11 (B:10404–10406): the square-sum budget of BCG02–BCG03 for `ϑ_j`. -/
  ϑUp : ClosedStage D.toClosedEarlyData → ℝ
  ϑUp_pos : ∀ st, 0 < ϑUp st
  /-- BR13 (B:10409–10411): the producer request for the short circle-axis raw/value/norm
  errors at the original short test radii 5000/1000. -/
  shortUp : ClosedStage D.toClosedEarlyData → (Fin 3 → ℝ) → ℝ
  shortUp_pos : ∀ st ϑ, 0 < shortUp st ϑ
  /-- BR14–BR19 (B:10418–10424): BCG02's one-vector test request at `ϑ₂, ϑ₃`. -/
  bcgUp : ClosedStage D.toClosedEarlyData → (Fin 3 → ℝ) → ℝ
  bcgUp_pos : ∀ st ϑ, 0 < bcgUp st ϑ
  /-- BR04–BR23 (B:10389–10450): the closed slots PR04–PR28 of the original interior producers,
  augmented by the boundary producers (AC76/FC20 in `β₂Up`, BCG02's original qualities at the
  long radius `30L` in `errorsUp`, BCP04's local threshold in `wUp`, the edge and slim AC76/FC20
  requests in `splitUp`/`β₁Up`, BCP04's interior producer tails), as a function of the boundary
  requests `ϑ, shortErr, bcgErr`. -/
  interior : (Fin 3 → ℝ) → ℝ → ℝ → ClosedThresholds D.toClosedEarlyData
  /-- BR24 (B:10455–10463): the cusp splitting, norm and buffer thresholds of BCG02, BCP05,
  BCP02 and BCG01–BCG03. -/
  cuspUp : ClosedStage D.toClosedEarlyData → (Fin 3 → ℝ) → ℝ → ℝ → ClosedLaterValues → ℝ
  cuspUp_pos : ∀ st ϑ sh bc v, 0 < cuspUp st ϑ sh bc v
  /-- BR24 (B:10464–10465): the resulting cusp test radii and first-exit buffers at the cusp
  quality (a finite lower bound for `H_∂`). -/
  cuspRadii : ClosedStage D.toClosedEarlyData → (Fin 3 → ℝ) → ℝ → ℝ → ClosedLaterValues → ℝ → ℝ
  /-- BR24 (B:10466–10471): BCP02's positive product and first-exit bounds on `r_∂`. -/
  productUp : ClosedStage D.toClosedEarlyData → (Fin 3 → ℝ) → ℝ → ℝ → ClosedLaterValues →
    ℝ → ℝ → ℝ
  productUp_pos : ∀ st ϑ sh bc v q H, 0 < productUp st ϑ sh bc v q H
  /-- BR25 (B:10488–10496): the finite maximum of the local/overlap tails and those of
  BSA01–BSA06, BCP01–BCP05, BCG01–BCG07, splitting/inverse-quality and packing radii. -/
  tailLow : ClosedStage D.toClosedEarlyData → (Fin 3 → ℝ) → ℝ → ℝ → ClosedLaterValues →
    ℝ → ℝ → ℝ → ℕ
  /-- BR25 (B:10500–10505): the finitely many fixed constants `C` of the producers and witness
  comparisons in (BRegInterior). -/
  fixedConstants : Finset ℝ

/-- BR20 and BR25: the closed slots actually used by the boundary register. The interior `w`
threshold is intersected with `w_cap` (B:10445–10447) and the test radius is `H_n = n/4`
(B:10494). -/
def BoundaryThresholds.toClosed {D : BoundaryEarlyData} (T : BoundaryThresholds D)
    (ϑ : Fin 3 → ℝ) (sh bc : ℝ) : ClosedThresholds D.toClosedEarlyData :=
  { T.interior ϑ sh bc with
    wUp := fun st ci ex er Λ => min ((T.interior ϑ sh bc).wUp st ci ex er Λ) boundaryVolumeCap
    wUp_pos := fun st ci ex er Λ =>
      lt_min ((T.interior ϑ sh bc).wUp_pos st ci ex er Λ) boundaryVolumeCap_pos
    H := fun n => (n : ℝ) / 4
    H_tendsto := tendsto_natCast_atTop_atTop.atTop_div_const (by norm_num) }

/-- (BRegPhysical), B:10476–10481, with `ϑ = min_j ϑ_j`. -/
def boundaryPhysicalBound (L c₃ H : ℝ) (ϑ : Fin 3 → ℝ) : ℝ :=
  min (1 / (1000 * L)) (min (1 / 10 ^ 4) (min (1 / (100 * H))
    (min ((min (ϑ 0) (min (ϑ 1) (ϑ 2))) ^ 2 / (4 * 10 ^ 8 * (12 * L + 1000)))
      (1 / 10 ^ 6 / (20 * (c₃ + 1))))))

/-- BBR01's register BR00–BR31: the closed register on the augmented constants, retained for the
interior blocks, together with every boundary free choice. -/
structure BoundaryRegister (D : BoundaryEarlyData) (T : BoundaryThresholds D) where
  stage : ClosedStage D.toClosedEarlyData
  ϑ : Fin 3 → ℝ
  shortErr : ℝ
  bcgErr : ℝ
  later : ClosedLater D.toClosedEarlyData (T.toClosed ϑ shortErr bcgErr) stage
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

/-- The name used by W4-BCG's BCF04 sheet for BBR01's admissible assignment. -/
abbrev BoundaryAssignment (D : BoundaryEarlyData) (T : BoundaryThresholds D) : Type :=
  BoundaryRegister D T

/-! ### Existence (BBR01) -/

theorem boundaryPhysicalBound_pos {L c₃ H : ℝ} {ϑ : Fin 3 → ℝ} (hL : 0 < L) (hc : 0 < c₃)
    (hH : 0 < H) (hϑ : ∀ j, 0 < ϑ j) : 0 < boundaryPhysicalBound L c₃ H ϑ := by
  have hm : 0 < min (ϑ 0) (min (ϑ 1) (ϑ 2)) := lt_min (hϑ 0) (lt_min (hϑ 1) (hϑ 2))
  unfold boundaryPhysicalBound
  exact lt_min (by positivity) (lt_min (by norm_num) (lt_min (by positivity)
    (lt_min (by positivity) (by positivity))))

private theorem natCast_gt_of_ceil_add_one_le {M : ℝ} {n : ℕ} (h : ⌈M⌉₊ + 1 ≤ n) : M < n := by
  have h1 : M ≤ (⌈M⌉₊ : ℝ) := Nat.le_ceil M
  have h2 : ((⌈M⌉₊ + 1 : ℕ) : ℝ) ≤ n := by exact_mod_cast h
  push_cast at h2
  linarith

/-- **BBR01** (B:10356): for every augmented early data and every positive producer-threshold
record the boundary register admits one assignment, independent of member, point and boundary
component. -/
theorem exists_boundaryRegister (D : BoundaryEarlyData) (T : BoundaryThresholds D) :
    Nonempty (BoundaryRegister D T) := by
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
  obtain ⟨la⟩ := exists_closedLater D.toClosedEarlyData (T.toClosed ϑ sh bc) st
  -- BR24
  have hqb : 0 < min (T.cuspUp st ϑ sh bc la.values) la.split.β₁ :=
    lt_min (T.cuspUp_pos st ϑ sh bc la.values) la.β₁_pos
  set q := min (T.cuspUp st ϑ sh bc la.values) la.split.β₁ / 2 with hq
  set H := max 1 (T.cuspRadii st ϑ sh bc la.values q) with hH
  have hHpos : 0 < H := zero_lt_one.trans_le (le_max_left _ _)
  have hLpos : 0 < closedLongLength la.excl := by
    have := la.Δ_pos
    unfold closedLongLength
    positivity
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
  have hw' := la.wPrime_pos
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
  all_goals have hMn : M < n := natCast_gt_of_ceil_add_one_le ((le_max_right _ _).trans hn)
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

namespace BoundaryRegister

variable {D : BoundaryEarlyData} {T : BoundaryThresholds D}

/-- BR20 (B:10446): the chosen volume parameter lies below `w_cap`. -/
theorem w_lt_cap (R : BoundaryRegister D T) : R.later.scale.w < boundaryVolumeCap := by
  have h := R.later.w_lt
  simp only [BoundaryThresholds.toClosed, lt_min_iff] at h
  exact h.1.2

/-- BR24 (B:10463): the cusp splitting quality is below `β₁`. -/
theorem cuspQuality_lt_β₁ (R : BoundaryRegister D T) : R.cuspQuality < R.later.split.β₁ :=
  R.cuspQuality_lt.trans_le (min_le_right _ _)

theorem one_le_cuspRadius (R : BoundaryRegister D T) : 1 ≤ R.cuspRadius :=
  (le_max_left _ _).trans R.cuspRadius_ge

/-- (BRegPhysical) (B:10477): `r_∂ < 1/(1000L)`. -/
theorem physicalScale_lt_long (R : BoundaryRegister D T) :
    R.physicalScale < 1 / (1000 * closedLongLength R.later.excl) :=
  R.physicalScale_lt.trans_le ((min_le_left _ _).trans (min_le_left _ _))

/-- (BRegPhysical) (B:10477): `r_∂ < 10⁻⁴`. -/
theorem physicalScale_lt_small (R : BoundaryRegister D T) : R.physicalScale < 1 / 10 ^ 4 :=
  R.physicalScale_lt.trans_le ((min_le_left _ _).trans
    ((min_le_right _ _).trans (min_le_left _ _)))

/-- (BRegPhysical) (B:10478): `100 H_∂ r_∂ < 1`. -/
theorem hundred_cuspRadius_mul_lt (R : BoundaryRegister D T) :
    100 * R.cuspRadius * R.physicalScale < 1 := by
  have h : R.physicalScale < 1 / (100 * R.cuspRadius) :=
    R.physicalScale_lt.trans_le ((min_le_left _ _).trans ((min_le_right _ _).trans
      ((min_le_right _ _).trans (min_le_left _ _))))
  have hH : 0 < 100 * R.cuspRadius := by have := R.one_le_cuspRadius; positivity
  rw [lt_div_iff₀ hH] at h
  linarith

/-- (BRegPhysical) (B:10484): `20 c₃ r_∂ < 10⁻⁶` for the actual torus core. -/
theorem twenty_c₃_mul_lt (R : BoundaryRegister D T) :
    20 * R.stage.c 2 * R.physicalScale < 1 / 10 ^ 6 := by
  have h : R.physicalScale < 1 / 10 ^ 6 / (20 * (R.stage.c 2 + 1)) :=
    R.physicalScale_lt.trans_le ((min_le_left _ _).trans ((min_le_right _ _).trans
      ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_right _ _)))))
  have hc := R.stage.c_pos 2
  rw [lt_div_iff₀ (by positivity)] at h
  nlinarith [R.physicalScale_pos]

/-- CAA01 (B:10679–10710) in the boundary register (BR12/BR21 carry the same refined bounds):
EGP01's four-target error is below `7·10⁻⁶ < 10⁻³`. -/
theorem edgeError_lt (R : BoundaryRegister D T) :
    5 * R.later.excl.β₂ + R.later.split.b + R.later.err.s < 7 / 10 ^ 6 :=
  R.later.edgeError_lt

theorem edgeError_lt_obstruction (R : BoundaryRegister D T) :
    5 * R.later.excl.β₂ + R.later.split.b + R.later.err.s < 1 / 1000 :=
  R.later.edgeError_lt_obstruction

end BoundaryRegister

/-- CAA01 for both registers and CAA02's register part (B:10787, B:10794): for the same early
data, both refined assignments exist. -/
theorem exists_closed_and_boundary_registers (D : BoundaryEarlyData)
    (Tc : ClosedThresholds D.toClosedEarlyData) (Tb : BoundaryThresholds D) :
    Nonempty (ClosedRegister D.toClosedEarlyData Tc × BoundaryRegister D Tb) := by
  obtain ⟨Rc⟩ := exists_closedRegister D.toClosedEarlyData Tc
  obtain ⟨Rb⟩ := exists_boundaryRegister D Tb
  exact ⟨(Rc, Rb)⟩

end DifferentialGeometry.Geometry.Collapse
