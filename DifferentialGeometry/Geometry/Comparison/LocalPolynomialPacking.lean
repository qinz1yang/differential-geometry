import DifferentialGeometry.Topology.MetricSpace.BilipschitzBallPacking
import DifferentialGeometry.Geometry.Comparison.RadialEuclideanPacking
import DifferentialGeometry.Geometry.Comparison.CenteredPairedChart

set_option autoImplicit false

open Set Metric Real

namespace DifferentialGeometry.Geometry.Comparison.Toponogov

variable {X : Type*} [MetricSpace X] [Nontrivial X]

theorem exists_local_polynomial_packing_of_fourPointComparison
    (hcurves : ∀ x y : X, ∀ η : ℝ, 0 < η →
      ∃ c : unitInterval → X, Continuous c ∧ c 0 = x ∧ c 1 = y ∧
        eVariationOn c univ < ENNReal.ofReal (dist x y + η))
    {Ω : Set X} (hΩ : IsOpen Ω) (hcomp : fourPointComparison 1 Ω)
    (hcomplete : ∀ z ∈ Ω, ∃ R : ℝ, 0 < R ∧ IsComplete (closedBall z R))
    {n : ℕ} (hn : 1 ≤ n) (hdim : dimH Ω ≤ n) {p : X} (hp : p ∈ Ω) :
    ∃ h : ℝ, 0 < h ∧ ball p h ⊆ Ω ∧ ∃ m : ℕ, 1 ≤ m ∧ m ≤ n ∧
      ∃ C : ℝ, 0 < C ∧ ∀ ε : ℝ, 0 < ε →
        finitePackingNumber ε (ball p h) ≤ (⌊(1 + C / ε) ^ m⌋₊ : ℕ∞) := by
  obtain ⟨m, hm, hmn, q, hq, _, _, ρ, hρ, hBΩ, U, _, e, _, he0, hlo, hhi⟩ :=
    exists_centered_distance_chart_in_open_set hcurves hcomp (Subset.refl Ω) hΩ
      ⟨p, hp⟩ hcomplete hn hdim
  let L := pairedChartDistortion n
  have hL : 0 < L := pairedChartDistortion_pos n
  have hmpos : 0 < (m : ℝ) := by exact_mod_cast (show 0 < m by omega)
  let f : ball q ρ → PiLp 2 (fun _ : Fin m => ℝ) := fun z => e z
  have hnorm (x : ball q ρ) : ‖f x‖ ≤ L * ρ := by
    calc
      ‖f x‖ = dist (f x) (f ⟨q, mem_ball_self hρ⟩) := by rw [show f ⟨q, mem_ball_self hρ⟩ = 0 from he0, dist_zero_right]
      _ ≤ L * dist (x : X) q := hhi x ⟨q, mem_ball_self hρ⟩
      _ ≤ L * ρ := mul_le_mul_of_nonneg_left (mem_ball.mp x.property).le hL.le
  by_cases hpq : p = q
  · subst p
    refine ⟨ρ, hρ, hBΩ, m, hm, hmn, 4 * L ^ 2 * ρ * sqrt m, by positivity, ?_⟩
    intro ε hε
    exact finitePackingNumber_le_floor_of_centered_dist_bounds hρ (by omega) hL hε he0 hlo hhi
  have hd : 0 < dist q p := dist_pos.mpr (Ne.symm hpq)
  obtain ⟨R, hR, hRΩ⟩ := Metric.isOpen_iff.mp hΩ p hp
  let h := min (R / 2) (dist q p / 4)
  have hh : 0 < h := lt_min (half_pos hR) (by positivity)
  have hhR : h < R := (min_le_left _ _).trans_lt (half_lt_self hR)
  have hhd : h ≤ dist q p / 4 := min_le_right _ _
  let a := dist q p - h
  let D := dist q p + h
  have ha : 0 < a := by dsimp [a]; linarith
  have haD : a ≤ D := by dsimp [a, D]; linarith
  have hD : 0 < D := ha.trans_le haD
  let t := min (1 / 2) (ρ / (2 * D))
  have ht : t ∈ Ioo 0 1 := ⟨lt_min (by norm_num) (by positivity),
    (min_le_left _ _).trans_lt (by norm_num)⟩
  have htD : t * D < ρ := by
    have hb := mul_le_mul_of_nonneg_right (min_le_right (1 / 2) (ρ / (2 * D))) hD.le
    have he : ρ / (2 * D) * D = ρ / 2 := by field_simp
    rw [he] at hb
    exact hb.trans_lt (half_lt_self hρ)
  have hWΩ : ball p h ⊆ Ω := (ball_subset_ball hhR.le).trans hRΩ
  have hrad (x : X) (hx : x ∈ ball p h) : dist q x ∈ Icc a D := by
    have hpx : dist p x < h := by simpa only [mem_ball, dist_comm] using hx
    have htri := dist_triangle q p x
    have hrev := dist_triangle q x p
    rw [dist_comm x p] at hrev
    constructor <;> dsimp [a, D] <;> linarith
  have hLambda : 0 < t * D / sinh D :=
    div_pos (mul_pos ht.1 hD) (sinh_pos_iff.mpr hD)
  let C := 8 * (L * ρ) * sqrt m / (L⁻¹ * (t * D / sinh D))
  have hC : 0 < C := by dsimp [C]; positivity
  refine ⟨h, hh, hWΩ, m, hm, hmn, C, hC, ?_⟩
  intro ε hε
  have hb := finitePackingNumber_le_of_radial_bounded_map hcurves hcomp hq ha haD
    ht htD hε hBΩ hWΩ hrad (by omega : 0 < m) (mul_pos hL hρ).le
    (inv_pos.mpr hL) hnorm hlo
  have he : 8 * (L * ρ) * sqrt m / (L⁻¹ * (t * D / sinh D) * ε) = C / ε := by
    dsimp [C]
    rw [div_div]
  simpa only [he] using hb

end DifferentialGeometry.Geometry.Comparison.Toponogov
