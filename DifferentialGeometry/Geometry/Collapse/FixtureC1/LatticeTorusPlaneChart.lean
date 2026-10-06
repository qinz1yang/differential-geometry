import DifferentialGeometry.Geometry.Collapse.FixtureC1.LatticeTorusMetric
import DifferentialGeometry.Topology.Manifold.LocalDiffeomorph.Coordinates

/-!
# Plane distance estimates on the lattice torus (S-FIXTURE-C1, K1, file 3)

With the planar periods `L₀, L₁` large and the third period `L₂` small, the torus is a thin
product `T²_{L₀,L₁} × S¹(L₂)`: write `planeL : ℝ³ → ℝ²` for the projection to the first two
coordinates and `Lp = min(L₀, L₁)`.

* `norm_planeL_le_dist_torPi_FXC1`: if `‖planeL(x - y)‖ ≤ Lp/2` then `‖planeL(x - y)‖ ≤ d(πx, πy)`
  (no planar wrap-around shortcut: `le_edist_torPi_FXC1`);
* `dist_torPi_le_FXC1`: for all `x, y`, `d(πx, πy) ≤ ‖planeL(x - y)‖ + L₂/2` (shift the third
  coordinate by a multiple of `L₂`);
* `ell_FXC1 Λ p̃`: the plane chart at the lift `p̃` of a point `p`: `ell (π y) = planeL(y - p̃)` for
  every `y` with `‖planeL(y - p̃)‖ < Lp/2` (planar uniqueness of such a lift), smooth there.
-/

set_option autoImplicit false

noncomputable section

open Set Function Metric
open scoped Manifold ContDiff Topology ENNReal

namespace DifferentialGeometry.Geometry.Collapse

local notation "E3" => EuclideanSpace ℝ (Fin 3)
local notation "ℝ²" => EuclideanSpace ℝ (Fin 2)

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace

attribute [local instance] torMS_FXC1

/-- The projection `ℝ³ → ℝ²` to the first two coordinates. -/
def planeL_FXC1 : E3 →L[ℝ] ℝ² :=
  LinearMap.toContinuousLinearMap
    { toFun := fun x => WithLp.toLp 2 fun i : Fin 2 => x (Fin.castSucc i)
      map_add' := fun x y => by ext i; simp
      map_smul' := fun c x => by ext i; simp }

@[simp] theorem planeL_apply_FXC1 (x : E3) (i : Fin 2) :
    planeL_FXC1 x i = x (Fin.castSucc i) := rfl

theorem norm_sq_planeL_FXC1 (x : E3) : ‖x‖ ^ 2 = ‖planeL_FXC1 x‖ ^ 2 + (x 2) ^ 2 := by
  rw [EuclideanSpace.norm_sq_eq, EuclideanSpace.norm_sq_eq]
  simp [Fin.sum_univ_three, Fin.sum_univ_two]

theorem norm_planeL_le_FXC1 (x : E3) : ‖planeL_FXC1 x‖ ≤ ‖x‖ := by
  refine abs_le_of_sq_le_sq' ?_ (norm_nonneg _) |>.2
  rw [norm_sq_planeL_FXC1 x]
  nlinarith [sq_nonneg (x 2)]

theorem norm_le_norm_planeL_add_FXC1 (x : E3) : ‖x‖ ≤ ‖planeL_FXC1 x‖ + |x 2| := by
  refine abs_le_of_sq_le_sq' ?_ (by positivity) |>.2
  rw [norm_sq_planeL_FXC1 x]
  nlinarith [norm_nonneg (planeL_FXC1 x), abs_nonneg (x 2), sq_abs (x 2)]


/-- The smaller of the two planar periods. -/
def planePeriod_FXC1 (Λ : TorusPeriods_FXC1) : ℝ := min (Λ.L 0) (Λ.L 1)

theorem planePeriod_pos_FXC1 (Λ : TorusPeriods_FXC1) : 0 < planePeriod_FXC1 Λ :=
  lt_min (Λ.pos 0) (Λ.pos 1)

theorem planeL_latticeVec_eq_zero_FXC1 (Λ : TorusPeriods_FXC1) (n : TorusGroup_FXC1 Λ)
    (h0 : n.toInts 0 = 0) (h1 : n.toInts 1 = 0) : planeL_FXC1 (latticeVec_FXC1 Λ n) = 0 := by
  ext i
  fin_cases i
  · simp [latticeVec_apply_FXC1, h0]
  · simp only [planeL_apply_FXC1]
    change latticeVec_FXC1 Λ n 1 = _
    simp [latticeVec_apply_FXC1, h1]

theorem planePeriod_le_norm_planeL_latticeVec_FXC1 (Λ : TorusPeriods_FXC1)
    (n : TorusGroup_FXC1 Λ) (h : n.toInts 0 ≠ 0 ∨ n.toInts 1 ≠ 0) :
    planePeriod_FXC1 Λ ≤ ‖planeL_FXC1 (latticeVec_FXC1 Λ n)‖ := by
  rcases h with h | h
  · have h1 : (1 : ℝ) ≤ |((n.toInts 0 : ℤ) : ℝ)| := by exact_mod_cast Int.one_le_abs h
    have h2 := PiLp.norm_apply_le (planeL_FXC1 (latticeVec_FXC1 Λ n)) 0
    simp only [planeL_apply_FXC1] at h2
    change ‖latticeVec_FXC1 Λ n 0‖ ≤ _ at h2
    rw [latticeVec_apply_FXC1, Real.norm_eq_abs, abs_mul, abs_of_pos (Λ.pos 0)] at h2
    have h3 := Λ.pos 0
    exact (min_le_left _ _).trans (by nlinarith)
  · have h1 : (1 : ℝ) ≤ |((n.toInts 1 : ℤ) : ℝ)| := by exact_mod_cast Int.one_le_abs h
    have h2 := PiLp.norm_apply_le (planeL_FXC1 (latticeVec_FXC1 Λ n)) 1
    simp only [planeL_apply_FXC1] at h2
    change ‖latticeVec_FXC1 Λ n 1‖ ≤ _ at h2
    rw [latticeVec_apply_FXC1, Real.norm_eq_abs, abs_mul, abs_of_pos (Λ.pos 1)] at h2
    have h3 := Λ.pos 1
    exact (min_le_right _ _).trans (by nlinarith)

theorem le_dist_of_ofReal_le_FXC1 (Λ : TorusPeriods_FXC1) (a b : Tor_FXC1 Λ) (r : ℝ)
    (h : ENNReal.ofReal r ≤ riemannianEDistOf (torMetric_FXC1 Λ) a b) : r ≤ dist a b := by
  rw [torMS_hmetric_FXC1 Λ a b] at h
  exact (ENNReal.ofReal_le_ofReal_iff dist_nonneg).mp h

theorem dist_le_of_edist_le_FXC1 (Λ : TorusPeriods_FXC1) (a b : Tor_FXC1 Λ) (r : ℝ) (hr : 0 ≤ r)
    (h : riemannianEDistOf (torMetric_FXC1 Λ) a b ≤ ENNReal.ofReal r) : dist a b ≤ r := by
  rw [torMS_hmetric_FXC1 Λ a b] at h
  exact (ENNReal.ofReal_le_ofReal_iff hr).mp h

/-- **No planar shortcut**: planar separation `≤ Lp/2` is a lower bound for the torus distance. -/
theorem norm_planeL_le_dist_torPi_FXC1 (Λ : TorusPeriods_FXC1) (x y : E3)
    (h : ‖planeL_FXC1 (x - y)‖ ≤ planePeriod_FXC1 Λ / 2) :
    ‖planeL_FXC1 (x - y)‖ ≤ dist (torPi_FXC1 Λ x) (torPi_FXC1 Λ y) := by
  refine le_dist_of_ofReal_le_FXC1 Λ _ _ _ (le_edist_torPi_FXC1 Λ x y _ fun n => ?_)
  have hsplit : planeL_FXC1 (x - (y + latticeVec_FXC1 Λ n)) =
      planeL_FXC1 (x - y) - planeL_FXC1 (latticeVec_FXC1 Λ n) := by
    rw [← map_sub]; congr 1; abel
  by_cases hn : n.toInts 0 = 0 ∧ n.toInts 1 = 0
  · have h0 := planeL_latticeVec_eq_zero_FXC1 Λ n hn.1 hn.2
    calc ‖planeL_FXC1 (x - y)‖ = ‖planeL_FXC1 (x - (y + latticeVec_FXC1 Λ n))‖ := by
          rw [hsplit, h0, sub_zero]
      _ ≤ ‖x - (y + latticeVec_FXC1 Λ n)‖ := norm_planeL_le_FXC1 _
  · have hp := planePeriod_le_norm_planeL_latticeVec_FXC1 Λ n (by tauto)
    have h1 : ‖planeL_FXC1 (latticeVec_FXC1 Λ n)‖ ≤
        ‖planeL_FXC1 (x - y)‖ + ‖planeL_FXC1 (x - (y + latticeVec_FXC1 Λ n))‖ := by
      have e : planeL_FXC1 (latticeVec_FXC1 Λ n) = planeL_FXC1 (x - y) -
          planeL_FXC1 (x - (y + latticeVec_FXC1 Λ n)) := by rw [hsplit]; abel
      rw [e]
      exact norm_sub_le _ _
    have h2 := norm_planeL_le_FXC1 (x - (y + latticeVec_FXC1 Λ n))
    linarith

/-- **Thin circle direction**: the torus distance exceeds the planar separation by at most
`L₂/2`. -/
theorem dist_torPi_le_FXC1 (Λ : TorusPeriods_FXC1) (x y : E3) :
    dist (torPi_FXC1 Λ x) (torPi_FXC1 Λ y) ≤ ‖planeL_FXC1 (x - y)‖ + Λ.L 2 / 2 := by
  let k : ℤ := ⌊(x 2 - y 2) / Λ.L 2 + 1 / 2⌋
  let n : TorusGroup_FXC1 Λ := TorusGroup_FXC1.ofInts Λ fun i => if i = 2 then k else 0
  have hn0 : n.toInts 0 = 0 := by simp [n, TorusGroup_FXC1.toInts, TorusGroup_FXC1.ofInts]
  have hn1 : n.toInts 1 = 0 := by simp [n, TorusGroup_FXC1.toInts, TorusGroup_FXC1.ofInts]
  have hn2 : n.toInts 2 = k := by simp [n, TorusGroup_FXC1.toInts, TorusGroup_FXC1.ofInts]
  have hπ : torPi_FXC1 Λ (y + latticeVec_FXC1 Λ n) = torPi_FXC1 Λ y :=
    (torPi_eq_iff_FXC1.mpr ⟨n, rfl⟩).symm
  have hpl : planeL_FXC1 (x - (y + latticeVec_FXC1 Λ n)) = planeL_FXC1 (x - y) := by
    have e : x - (y + latticeVec_FXC1 Λ n) = (x - y) - latticeVec_FXC1 Λ n := by abel
    rw [e, map_sub, planeL_latticeVec_eq_zero_FXC1 Λ n hn0 hn1, sub_zero]
  have h3 : |(x - (y + latticeVec_FXC1 Λ n)) 2| ≤ Λ.L 2 / 2 := by
    have hL := Λ.pos 2
    have hk1 := Int.floor_le ((x 2 - y 2) / Λ.L 2 + 1 / 2)
    have hk2 := Int.lt_floor_add_one ((x 2 - y 2) / Λ.L 2 + 1 / 2)
    have hv : (x - (y + latticeVec_FXC1 Λ n)) 2 = x 2 - y 2 - (k : ℝ) * Λ.L 2 := by
      simp [latticeVec_apply_FXC1, hn2]
      ring
    rw [hv, abs_le]
    have e1 : (k : ℝ) ≤ (x 2 - y 2) / Λ.L 2 + 1 / 2 := hk1
    have e2 : (x 2 - y 2) / Λ.L 2 + 1 / 2 < (k : ℝ) + 1 := hk2
    have hdiv : (x 2 - y 2) / Λ.L 2 * Λ.L 2 = x 2 - y 2 := div_mul_cancel₀ _ hL.ne'
    constructor <;> nlinarith
  have h4 := edist_torPi_le_FXC1 Λ x (y + latticeVec_FXC1 Λ n)
  rw [hπ] at h4
  refine (dist_le_of_edist_le_FXC1 Λ _ _ _ (norm_nonneg _) h4).trans ?_
  calc ‖x - (y + latticeVec_FXC1 Λ n)‖
      ≤ ‖planeL_FXC1 (x - (y + latticeVec_FXC1 Λ n))‖ + |(x - (y + latticeVec_FXC1 Λ n)) 2| :=
        norm_le_norm_planeL_add_FXC1 _
    _ ≤ ‖planeL_FXC1 (x - y)‖ + Λ.L 2 / 2 := by rw [hpl]; linarith

end DifferentialGeometry.Geometry.Collapse
