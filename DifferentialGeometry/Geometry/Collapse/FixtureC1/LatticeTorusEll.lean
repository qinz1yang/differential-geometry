import DifferentialGeometry.Geometry.Collapse.FixtureC1.LatticeTorusPlaneChart

/-!
# The plane chart `ell` of the lattice torus (S-FIXTURE-C1, K1, file 4)

For a lift `pt ∈ ℝ³` of a point `p`, `ell_FXC1 Λ pt : T³ → ℝ²` is the planar coordinate relative to
`pt`, defined on the planar slab `ellDom = {y | ‖planeL(y - pt)‖ < Lp/2}` (a fundamental domain of
the planar periods; the third coordinate is free) by `ell (π y) = planeL(y - pt)`. It is
well defined (planar uniqueness of the lift), smooth on `π(ellDom)` with surjective differential,
and satisfies the two-sided distance bound of file 3.

* `exists_lift_of_dist_lt_FXC1`: a point of the torus within `r` of `π x` has a lift within `r` of
  `x`;
* `ell_torPi_FXC1`, `contMDiffOn_ell_FXC1`, `surjective_mfderiv_ell_FXC1`;
* `ell_dist_bounds_FXC1`: for `q, q'` within `Lp/4` of `p`:
  `‖ell q - ell q'‖ ≤ d(q, q') ≤ ‖ell q - ell q'‖ + L₂/2`;
* `exists_ell_eq_FXC1`: every `u ∈ ℝ²` with `‖u‖ < Lp/2` is the chart value of a point at
  distance `≤ ‖u‖` from `p`.
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

/-- A point of the torus at distance `< r` from `π x` has a lift at distance `< r` from `x`. -/
theorem exists_lift_of_dist_lt_FXC1 (Λ : TorusPeriods_FXC1) (x : E3) (q : Tor_FXC1 Λ) {r : ℝ}
    (h : dist (torPi_FXC1 Λ x) q < r) : ∃ y, torPi_FXC1 Λ y = q ∧ ‖x - y‖ < r := by
  by_contra hcon
  simp only [not_exists, not_and, not_lt] at hcon
  obtain ⟨y₀, rfl⟩ := torPi_surjective_FXC1 Λ q
  have hle := le_dist_of_ofReal_le_FXC1 Λ _ _ r
    (le_edist_torPi_FXC1 Λ x y₀ r fun n =>
      hcon (y₀ + latticeVec_FXC1 Λ n) (torPi_eq_iff_FXC1.mpr ⟨n, rfl⟩).symm)
  exact absurd h (not_lt.mpr hle)

/-- The planar slab around the lift `pt`. -/
def ellDom_FXC1 (Λ : TorusPeriods_FXC1) (pt : E3) : Set E3 :=
  {y | ‖planeL_FXC1 (y - pt)‖ < planePeriod_FXC1 Λ / 2}

theorem isOpen_ellDom_FXC1 (Λ : TorusPeriods_FXC1) (pt : E3) : IsOpen (ellDom_FXC1 Λ pt) :=
  isOpen_lt (planeL_FXC1.continuous.comp (continuous_id.sub continuous_const)).norm
    continuous_const

/-- Planar uniqueness: two lifts of the same point in the slab have the same plane part. -/
theorem planeL_eq_of_torPi_eq_FXC1 (Λ : TorusPeriods_FXC1) {pt y y' : E3}
    (hy : y ∈ ellDom_FXC1 Λ pt) (hy' : y' ∈ ellDom_FXC1 Λ pt)
    (h : torPi_FXC1 Λ y = torPi_FXC1 Λ y') : planeL_FXC1 y = planeL_FXC1 y' := by
  obtain ⟨n, hn⟩ := torPi_eq_iff_FXC1.mp h
  by_cases hz : n.toInts 0 = 0 ∧ n.toInts 1 = 0
  · rw [hn, map_add, planeL_latticeVec_eq_zero_FXC1 Λ n hz.1 hz.2, add_zero]
  · exfalso
    have hp := planePeriod_le_norm_planeL_latticeVec_FXC1 Λ n (by tauto)
    have e : planeL_FXC1 (latticeVec_FXC1 Λ n) =
        planeL_FXC1 (y' - pt) - planeL_FXC1 (y - pt) := by
      rw [← map_sub, show y' - pt - (y - pt) = y' - y by abel, hn]; congr 1; abel
    have h2 : ‖planeL_FXC1 (latticeVec_FXC1 Λ n)‖ ≤
        ‖planeL_FXC1 (y' - pt)‖ + ‖planeL_FXC1 (y - pt)‖ := by
      rw [e]; exact norm_sub_le _ _
    have h3 : ‖planeL_FXC1 (y' - pt)‖ < planePeriod_FXC1 Λ / 2 := hy'
    have h4 : ‖planeL_FXC1 (y - pt)‖ < planePeriod_FXC1 Λ / 2 := hy
    linarith

open scoped Classical in
/-- The plane chart at the lift `pt` (value `0` outside the image of the slab). -/
def ell_FXC1 (Λ : TorusPeriods_FXC1) (pt : E3) (q : Tor_FXC1 Λ) : ℝ² :=
  if h : ∃ y ∈ ellDom_FXC1 Λ pt, torPi_FXC1 Λ y = q then planeL_FXC1 (h.choose - pt) else 0

theorem ell_torPi_FXC1 (Λ : TorusPeriods_FXC1) {pt y : E3} (hy : y ∈ ellDom_FXC1 Λ pt) :
    ell_FXC1 Λ pt (torPi_FXC1 Λ y) = planeL_FXC1 (y - pt) := by
  have hex : ∃ y' ∈ ellDom_FXC1 Λ pt, torPi_FXC1 Λ y' = torPi_FXC1 Λ y := ⟨y, hy, rfl⟩
  unfold ell_FXC1
  split
  · rename_i h
    obtain ⟨hc1, hc2⟩ := h.choose_spec
    rw [map_sub, map_sub, planeL_eq_of_torPi_eq_FXC1 Λ hc1 hy hc2]
  · rename_i h
    exact absurd hex h

theorem ell_base_FXC1 (Λ : TorusPeriods_FXC1) (pt : E3) : ell_FXC1 Λ pt (torPi_FXC1 Λ pt) = 0 := by
  have hp : pt ∈ ellDom_FXC1 Λ pt := by
    change ‖planeL_FXC1 (pt - pt)‖ < _
    rw [sub_self, map_zero, norm_zero]
    exact half_pos (planePeriod_pos_FXC1 Λ)
  rw [ell_torPi_FXC1 Λ hp, sub_self, map_zero]

theorem contMDiffOn_ell_FXC1 (Λ : TorusPeriods_FXC1) (pt : E3) :
    ContMDiffOn 𝓘(ℝ, E3) 𝓘(ℝ, ℝ²) ∞ (ell_FXC1 Λ pt) (torPi_FXC1 Λ '' ellDom_FXC1 Λ pt) := by
  refine (torPi_isLocalDiffeomorph_FXC1 Λ).contMDiffOn_of_comp (isOpen_ellDom_FXC1 Λ pt) ?_
  have hs : ContMDiff 𝓘(ℝ, E3) 𝓘(ℝ, ℝ²) ∞ (fun y : E3 => planeL_FXC1 (y - pt)) :=
    (planeL_FXC1.contDiff.comp (contDiff_id.sub contDiff_const)).contMDiff
  exact hs.contMDiffOn.congr fun y hy => ell_torPi_FXC1 Λ hy

theorem isOpen_image_ellDom_FXC1 (Λ : TorusPeriods_FXC1) (pt : E3) :
    IsOpen (torPi_FXC1 Λ '' ellDom_FXC1 Λ pt) :=
  (torPi_isLocalDiffeomorph_FXC1 Λ).isLocalHomeomorph.isOpenMap _ (isOpen_ellDom_FXC1 Λ pt)

theorem surjective_mfderiv_ell_FXC1 (Λ : TorusPeriods_FXC1) (pt : E3) {y : E3}
    (hy : y ∈ ellDom_FXC1 Λ pt) :
    Surjective (mfderiv 𝓘(ℝ, E3) 𝓘(ℝ, ℝ²) (ell_FXC1 Λ pt) (torPi_FXC1 Λ y)) := by
  have hmem : torPi_FXC1 Λ y ∈ torPi_FXC1 Λ '' ellDom_FXC1 Λ pt := ⟨y, hy, rfl⟩
  have hell : MDifferentiableAt 𝓘(ℝ, E3) 𝓘(ℝ, ℝ²) (ell_FXC1 Λ pt) (torPi_FXC1 Λ y) :=
    ((contMDiffOn_ell_FXC1 Λ pt).contMDiffAt
      ((isOpen_image_ellDom_FXC1 Λ pt).mem_nhds hmem)).mdifferentiableAt (by simp)
  have hpi : MDifferentiableAt 𝓘(ℝ, E3) 𝓘(ℝ, E3) (torPi_FXC1 Λ) y :=
    ((contMDiff_torPi_FXC1 Λ) y).mdifferentiableAt (by simp)
  have hev : (ell_FXC1 Λ pt ∘ torPi_FXC1 Λ) =ᶠ[nhds y] fun z : E3 => planeL_FXC1 (z - pt) := by
    filter_upwards [(isOpen_ellDom_FXC1 Λ pt).mem_nhds hy] with z hz
    exact ell_torPi_FXC1 Λ hz
  have hcomp := mfderiv_comp y hell hpi
  have hD : mfderiv 𝓘(ℝ, E3) 𝓘(ℝ, ℝ²) (ell_FXC1 Λ pt ∘ torPi_FXC1 Λ) y =
      (planeL_FXC1 : E3 →L[ℝ] ℝ²) := by
    rw [hev.mfderiv_eq, mfderiv_eq_fderiv]
    exact ((planeL_FXC1.hasFDerivAt.comp y ((hasFDerivAt_id y).sub_const pt))).fderiv
  intro v
  let v' : ℝ² := v
  obtain ⟨u, hu⟩ : ∃ u : E3, planeL_FXC1 u = v' := by
    refine ⟨WithLp.toLp 2 ![v' 0, v' 1, 0], ?_⟩
    ext i
    fin_cases i <;> simp
  refine ⟨mfderiv 𝓘(ℝ, E3) 𝓘(ℝ, E3) (torPi_FXC1 Λ) y u, ?_⟩
  have h2 := DFunLike.congr_fun hcomp u
  rw [hD] at h2
  exact h2.symm.trans hu


/-- **Two-sided distance bound of the plane chart** on the ball of radius `Lp/4` around `π pt`. -/
theorem ell_dist_bounds_FXC1 (Λ : TorusPeriods_FXC1) (pt : E3) (q q' : Tor_FXC1 Λ) {r : ℝ}
    (hr : r ≤ planePeriod_FXC1 Λ / 4) (hq : dist (torPi_FXC1 Λ pt) q < r)
    (hq' : dist (torPi_FXC1 Λ pt) q' < r) :
    ‖ell_FXC1 Λ pt q - ell_FXC1 Λ pt q'‖ ≤ dist q q' ∧
      dist q q' ≤ ‖ell_FXC1 Λ pt q - ell_FXC1 Λ pt q'‖ + Λ.L 2 / 2 := by
  obtain ⟨y, rfl, hy⟩ := exists_lift_of_dist_lt_FXC1 Λ pt q hq
  obtain ⟨y', rfl, hy'⟩ := exists_lift_of_dist_lt_FXC1 Λ pt q' hq'
  have hLp := planePeriod_pos_FXC1 Λ
  have hdy : ‖planeL_FXC1 (y - pt)‖ < r := by
    rw [norm_sub_rev] at hy
    exact (norm_planeL_le_FXC1 _).trans_lt hy
  have hdy' : ‖planeL_FXC1 (y' - pt)‖ < r := by
    rw [norm_sub_rev] at hy'
    exact (norm_planeL_le_FXC1 _).trans_lt hy'
  have hmy : y ∈ ellDom_FXC1 Λ pt := by
    change ‖planeL_FXC1 (y - pt)‖ < _
    linarith
  have hmy' : y' ∈ ellDom_FXC1 Λ pt := by
    change ‖planeL_FXC1 (y' - pt)‖ < _
    linarith
  rw [ell_torPi_FXC1 Λ hmy, ell_torPi_FXC1 Λ hmy', ← map_sub,
    show y - pt - (y' - pt) = y - y' by abel]
  have hsep : ‖planeL_FXC1 (y - y')‖ ≤ planePeriod_FXC1 Λ / 2 := by
    have e : planeL_FXC1 (y - y') = planeL_FXC1 (y - pt) - planeL_FXC1 (y' - pt) := by
      rw [← map_sub]; congr 1; abel
    rw [e]
    have := norm_sub_le (planeL_FXC1 (y - pt)) (planeL_FXC1 (y' - pt))
    linarith
  exact ⟨norm_planeL_le_dist_torPi_FXC1 Λ y y' hsep, dist_torPi_le_FXC1 Λ y y'⟩

/-- **Coverage of the plane chart**: every `u` of norm `< Lp/2` is a chart value, at distance
`≤ ‖u‖` from `π pt`. -/
theorem exists_ell_eq_FXC1 (Λ : TorusPeriods_FXC1) (pt : E3) (u : ℝ²)
    (hu : ‖u‖ < planePeriod_FXC1 Λ / 2) :
    ∃ q : Tor_FXC1 Λ, ell_FXC1 Λ pt q = u ∧ dist (torPi_FXC1 Λ pt) q ≤ ‖u‖ := by
  let w : E3 := WithLp.toLp 2 ![u 0, u 1, 0]
  have hw : planeL_FXC1 w = u := by
    ext i
    fin_cases i <;> simp [w]
  have hnorm : ‖w‖ = ‖u‖ := by
    have h := norm_sq_planeL_FXC1 w
    have h2 : w 2 = 0 := by simp [w]
    rw [hw, h2] at h
    exact (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp (by rw [h]; ring)
  have hmem : pt + w ∈ ellDom_FXC1 Λ pt := by
    change ‖planeL_FXC1 (pt + w - pt)‖ < _
    rw [add_sub_cancel_left, hw]
    exact hu
  refine ⟨torPi_FXC1 Λ (pt + w), ?_, ?_⟩
  · rw [ell_torPi_FXC1 Λ hmem, add_sub_cancel_left, hw]
  · have h := edist_torPi_le_FXC1 Λ pt (pt + w)
    have h2 := dist_le_of_edist_le_FXC1 Λ _ _ _ (norm_nonneg _) h
    rwa [show pt - (pt + w) = -w by abel, norm_neg, hnorm] at h2

end DifferentialGeometry.Geometry.Collapse
