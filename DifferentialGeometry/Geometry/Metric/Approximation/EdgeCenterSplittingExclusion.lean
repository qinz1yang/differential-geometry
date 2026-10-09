import DifferentialGeometry.Geometry.Metric.Approximation.EdgeHalfPlaneModel
import DifferentialGeometry.Geometry.Metric.Approximation.SplittingRank
import DifferentialGeometry.Geometry.Metric.HalfPlanePacking
import DifferentialGeometry.Geometry.Collapse.RankStrata

/-!
# Actual edge centers exclude a two-splitting (EGP01)

Blueprint `master207B.tex`, EGP01 (`lem:fibration-edge-exclusion`, lines 4820–4843). At a strong
edge point (the edge predicate `isEdgePoint` with qualities `b, s < 10⁻⁶`) there is no
`(2, β)`-splitting for `β < 10⁻⁶`. The proof lifts the four unit-cross targets `(±e₁, y₀), (±e₂, y₀)`
through the splitting (LFR30's buffered lifts, here the KL coverage witnesses with error `< 2β`),
and maps the witnesses by the composite half-plane chart of LFR30
(`isEdgePoint.exists_local_half_plane_model`, distortion `≤ b + s` on the radius-two ball); the
resulting four points of the closed upper half-plane contradict LFR29
(`WithLp.not_approximate_orthogonal_cross_in_half_plane`) with error `5β + b + s ≤ 10⁻³`.

The binding is stated at the point's own scale (the metric divided by `ρ p`), and gives the
consequence for the LC16 rank strata: the scaled splitting rank of a strong edge center is not two.
Neither `Δ`, nor LFR29.1, nor the order of the later qualities is used (a strengthening).
-/

set_option autoImplicit false

noncomputable section

open Set Metric

namespace GC.MetricGeometry

universe u v w

section Targets

/-- The signed unit vectors `±eᵢ` of the Euclidean plane (`true` is the negative sign). -/
def unitCrossTarget (i : Fin 2 × Bool) : EuclideanSpace ℝ (Fin 2) :=
  (if i.2 then (-1 : ℝ) else 1) • EuclideanSpace.single i.1 (1 : ℝ)

theorem norm_euclideanSpace_fin_two (x : EuclideanSpace ℝ (Fin 2)) :
    ‖x‖ = Real.sqrt (x 0 ^ 2 + x 1 ^ 2) := by
  rw [EuclideanSpace.norm_eq, Fin.sum_univ_two, Real.norm_eq_abs, Real.norm_eq_abs, sq_abs,
    sq_abs]

theorem norm_unitCrossTarget (i : Fin 2 × Bool) : ‖unitCrossTarget i‖ = 1 := by
  rcases i with ⟨i, t⟩
  rw [unitCrossTarget, norm_smul, PiLp.norm_single, norm_one, mul_one]
  cases t <;> simp

theorem dist_unitCrossTarget_opposite (i : Fin 2) :
    dist (unitCrossTarget (i, false)) (unitCrossTarget (i, true)) = 2 := by
  rw [dist_eq_norm, unitCrossTarget, unitCrossTarget]
  simp only [Bool.false_eq_true, ↓reduceIte, one_smul, neg_smul, sub_neg_eq_add]
  rw [← two_smul ℝ, norm_smul, PiLp.norm_single, norm_one, mul_one, Real.norm_two]

theorem dist_unitCrossTarget_cross (s t : Bool) :
    dist (unitCrossTarget (0, s)) (unitCrossTarget (1, t)) = Real.sqrt 2 := by
  rw [dist_eq_norm, norm_euclideanSpace_fin_two]
  congr 1
  cases s <;> cases t <;> simp [unitCrossTarget] <;> norm_num

end Targets

variable {X : Type u} [m : MetricSpace X]

/-- EGP01, kernel form: a strong edge point admits no `(2, β)`-splitting. -/
theorem not_hasEuclideanSplitting_two_of_isEdgePoint {p : X} {Δ b s β : ℝ}
    (hedge : isEdgePoint.{u, v} p Δ b s) (hb : b < 1 / 1000000) (hs : s < 1 / 1000000)
    (hβ : β < 1 / 1000000) : ¬ HasEuclideanSplitting.{u, w} p 2 β := by
  rintro ⟨Y, mY, q, ⟨F⟩⟩
  let := mY
  have hpos : 0 < b ∧ 0 < s := by
    obtain ⟨Y', mY', q', C, hC, _, ⟨E⟩, ⟨G⟩⟩ := hedge
    let := mY'
    exact ⟨E.error_pos, G.error_pos⟩
  have hb0 : 0 < b := hpos.1
  have hs0 : 0 < s := hpos.2
  have hβ0 : 0 < β := F.error_pos
  have hbinv : 1000000 < b⁻¹ := by
    rw [lt_inv_comm₀ (by norm_num) hb0]; simpa using hb
  have hsinv : 1000000 < s⁻¹ := by
    rw [lt_inv_comm₀ (by norm_num) hs0]; simpa using hs
  have hβinv : 1000000 < β⁻¹ := by
    rw [lt_inv_comm₀ (by norm_num) hβ0]; simpa using hβ
  obtain ⟨W, hWp, hWheight, hWdist⟩ :=
    isEdgePoint.exists_local_half_plane_model (S := 2) hedge
      (by rw [lt_min_iff]; constructor <;> linarith)
  -- the four targets and their witnesses
  let T : Fin 2 × Bool → WithLp 2 (EuclideanSpace ℝ (Fin 2) × Y) :=
    fun i => WithLp.toLp 2 (unitCrossTarget i, q)
  have hTdist (i j : Fin 2 × Bool) :
      dist (T i) (T j) = dist (unitCrossTarget i) (unitCrossTarget j) :=
    (WithLp.isometry_prodMk_right (E := EuclideanSpace ℝ (Fin 2)) q).dist_eq
      (unitCrossTarget i) (unitCrossTarget j)
  have hT0 (i : Fin 2 × Bool) :
      dist (T i) (WithLp.toLp 2 ((0 : EuclideanSpace ℝ (Fin 2)), q)) = 1 := by
    have h := (WithLp.isometry_prodMk_right (E := EuclideanSpace ℝ (Fin 2)) q).dist_eq
      (unitCrossTarget i) 0
    rw [dist_zero_right, norm_unitCrossTarget] at h
    exact h
  have hwit (i : Fin 2 × Bool) : ∃ x ∈ ball p β⁻¹, dist (T i) (F.toFun x) < 2 * β :=
    F.coverage_witness (T i) (by rw [hT0]; linarith)
  choose x hxball hxT using hwit
  -- radii and pairwise distances of the witnesses
  have hrad (i : Fin 2 × Bool) : |dist (x i) p - 1| ≤ 3 * β := by
    have h1 := F.radial_error (x i) (hxball i)
    have h2 := dist_triangle (T i) (F.toFun (x i)) (WithLp.toLp 2 ((0 : EuclideanSpace ℝ (Fin 2)), q))
    have h3 := dist_triangle (F.toFun (x i)) (T i) (WithLp.toLp 2 ((0 : EuclideanSpace ℝ (Fin 2)), q))
    rw [hT0] at h2 h3
    rw [dist_comm (F.toFun (x i)) (T i)] at h3
    have h4 := hxT i
    rw [abs_le] at h1 ⊢
    constructor <;> linarith [h1.1, h1.2]
  have hpair (i j : Fin 2 × Bool) :
      |dist (x i) (x j) - dist (unitCrossTarget i) (unitCrossTarget j)| ≤ 5 * β := by
    have h1 := F.distortion (x i) (hxball i) (x j) (hxball j)
    have h2 := dist_dist_dist_le (F.toFun (x i)) (F.toFun (x j)) (T i) (T j)
    rw [Real.dist_eq, dist_comm (F.toFun (x i)) (T i), dist_comm (F.toFun (x j)) (T j)] at h2
    rw [← hTdist]
    have hi := hxT i
    have hj := hxT j
    rw [abs_le] at h1 h2 ⊢
    constructor <;> linarith [h1.1, h1.2, h2.1, h2.2]
  have hxS (i : Fin 2 × Bool) : x i ∈ ball p 2 := by
    have h := (abs_le.mp (hrad i)).2
    change dist (x i) p < 2
    linarith
  have hpS : p ∈ ball p 2 := mem_ball_self (by norm_num)
  -- the four half-plane images
  apply WithLp.not_approximate_orthogonal_cross_in_half_plane (fun i => W (x i))
    (ε := 5 * β + (b + s)) (by positivity) (by linarith) (fun i => hWheight (x i))
  · intro i
    have h1 := hWdist (x i) (hxS i) p hpS
    rw [hWp, dist_zero_right] at h1
    have h2 := hrad i
    rw [abs_le] at h1 h2 ⊢
    constructor <;> linarith [h1.1, h1.2, h2.1, h2.2]
  · intro i
    have h1 := hWdist (x (i, false)) (hxS _) (x (i, true)) (hxS _)
    have h2 := hpair (i, false) (i, true)
    rw [dist_unitCrossTarget_opposite] at h2
    rw [abs_le] at h1 h2 ⊢
    constructor <;> linarith [h1.1, h1.2, h2.1, h2.2]
  · intro s' t'
    have h1 := hWdist (x (0, s')) (hxS _) (x (1, t')) (hxS _)
    have h2 := hpair (0, s') (1, t')
    rw [dist_unitCrossTarget_cross] at h2
    rw [abs_le] at h1 h2 ⊢
    constructor <;> linarith [h1.1, h1.2, h2.1, h2.2]

/-- EGP01 at the point's own scale (the metric divided by `ρ p`). -/
theorem not_scaled_two_splitting_of_scaled_edge (ρ : X → ℝ) (hρ : ∀ x, 0 < ρ x) {p : X}
    {Δ b s β : ℝ}
    (hedge : @isEdgePoint.{u, v} X (m.rescale (ρ p)⁻¹ (inv_pos.mpr (hρ p))) p Δ b s)
    (hb : b < 1 / 1000000) (hs : s < 1 / 1000000) (hβ : β < 1 / 1000000) :
    ¬ @HasEuclideanSplitting.{u, w} X (m.rescale (ρ p)⁻¹ (inv_pos.mpr (hρ p))) p 2 β :=
  @not_hasEuclideanSplitting_two_of_isEdgePoint X (m.rescale (ρ p)⁻¹ (inv_pos.mpr (hρ p)))
    p Δ b s β hedge hb hs hβ

/-- EGP01 for the LC16 strata: the scaled splitting rank of a strong edge center is not two. -/
theorem scaledSplittingRank_ne_two_of_scaled_edge (ρ : X → ℝ) (hρ : ∀ x, 0 < ρ x) {p : X}
    {Δ b s : ℝ} (β : ℕ → ℝ)
    (hedge : @isEdgePoint.{u, v} X (m.rescale (ρ p)⁻¹ (inv_pos.mpr (hρ p))) p Δ b s)
    (hb : b < 1 / 1000000) (hs : s < 1 / 1000000) (hβ : β 2 < 1 / 1000000) :
    scaledSplittingRank.{u, w} ρ hρ β p ≠ 2 := by
  intro hrank
  have h := (scaledSplittingRank_eq_iff.mp hrank).2.1 (by norm_num)
  exact not_scaled_two_splitting_of_scaled_edge.{u, v, w} ρ hρ hedge hb hs hβ h

end GC.MetricGeometry
