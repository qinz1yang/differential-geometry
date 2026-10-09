import DifferentialGeometry.Geometry.Comparison.LocalDenseEuclideanTangents
import DifferentialGeometry.Geometry.Comparison.IntrinsicAngularObstruction
import DifferentialGeometry.Geometry.Comparison.EuclideanTangentChart
import DifferentialGeometry.Topology.MetricSpace.LocalCurveDimension
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds

set_option autoImplicit false

open Set Metric Real
open scoped NNReal ENNReal Topology

namespace DifferentialGeometry.Geometry.Comparison.Toponogov

theorem exists_dense_uniform_strut_charts_of_intrinsic_eight_comparison_and_dimH
    {X : Type*} [MetricSpace X] [CompleteSpace X] [Nontrivial X]
    (hcurves : ∀ a b : X, ∀ ε : ℝ, 0 < ε →
      ∃ c : unitInterval → X, Continuous c ∧ c 0 = a ∧ c 1 = b ∧
        eVariationOn c univ < ENNReal.ofReal (dist a b + ε))
    (p : X) {R : ℝ} (hR : 0 < R) {n : ℕ}
    (hdim : dimH (ball p (8 * R)) ≤ n)
    (hlocal : ∀ z : ball p (8 * R), ∃ Ω : Set (ball p (8 * R)),
      @IsOpen (ball p (8 * R))
        (intrinsicBallMetricSpace hcurves p (by positivity : 0 < 8 * R)).toUniformSpace.toTopologicalSpace Ω ∧
      @fourPointComparison (ball p (8 * R))
        (intrinsicBallMetricSpace hcurves p (by positivity : 0 < 8 * R)) 1 Ω ∧ z ∈ Ω) :
    ∃ m : ℕ, 0 < m ∧ m ≤ n ∧ dimH (closedBall p R) = m ∧
      (∀ V : Set X, IsOpen V → V.Nonempty → V ⊆ ball p (R / 2) → dimH V = m) ∧
      (∀ (q : X) (hq : q ∈ ball p (R / 2)),
        letI : HasAnglesAt q := hasAnglesAt_of_intrinsic_ball_local_comparison hcurves p
          (by positivity : 0 < 8 * R) (by norm_num : (0 : ℝ) ≤ 1) hlocal
          (by change dist q p < 8 * R; have hh : dist q p < R / 2 := hq; linarith)
        dimH (univ : Set (TangentCone q)) = m) ∧
      ∃ S : Set (ball p (R / 2)), IsGδ S ∧ Dense S ∧
        ∀ q ∈ S,
          letI : HasAnglesAt q.val := hasAnglesAt_of_intrinsic_ball_local_comparison hcurves p
            (by positivity : 0 < 8 * R) (by norm_num : (0 : ℝ) ≤ 1) hlocal
            (by change dist q.val p < 8 * R; have hh : dist q.val p < R / 2 := q.property; linarith)
          ∃ e : TangentCone q.val ≃ᵢ EuclideanSpace ℝ (Fin m),
            e EuclideanCone.tip = 0 ∧ ∀ η : ℝ, 0 < η →
              ∃ (d : Fin (m + 1) → GeodesicRepresentative q.val) (s ρ : ℝ), 0 < s ∧ s < R / 8 ∧
                (∀ i, s ≤ (d i).length) ∧ (∀ i, dist q.val ((d i).path s) = s) ∧
                ∃ hρ : 0 < ρ, ρ < s / 8 ∧ ρ < η ∧
                (∀ i, (d i).path s ∈ ball p R) ∧ ball q.val ρ ⊆ ball p (R / 2) ∧
                1 ≤ strutChartDistortion n ∧
                ∃ (E : EuclideanSpace ℝ (Fin m) →ₗᵢ[ℝ] EuclideanSpace ℝ (Fin n))
                  (F : ball q.val ρ → EuclideanSpace ℝ (Fin n)),
                  (∀ x, F x = E (distanceCoordinates 2 (fun j : Fin m => (d j.succ).path s) x.val -
                    distanceCoordinates 2 (fun j : Fin m => (d j.succ).path s) q.val)) ∧
                  F ⟨q.val, mem_ball_self hρ⟩ = 0 ∧
                  (∀ x y, (strutChartDistortion n)⁻¹ * dist x y ≤ dist (F x) (F y) ∧
                    dist (F x) (F y) ≤ strutChartDistortion n * dist x y) ∧
                  ∃ e : ball q.val ρ ≃ₜ range F, ∀ x, (e x : EuclideanSpace ℝ (Fin n)) = F x := by
  obtain ⟨m, hmn, hclosed, hopen, htangent, S, hGS, hDS, hregular⟩ :=
    exists_dense_euclidean_tangents_of_intrinsic_eight_comparison_and_dimH
      hcurves p hR hdim hlocal
  have hm : 0 < m := by
    obtain ⟨x, hx⟩ := exists_ne p
    obtain ⟨c, hc, hc0, hc1, _⟩ := hcurves p x 1 zero_lt_one
    have hlow := one_le_dimH_ball_of_continuous_curve (by positivity : 0 < R / 2)
      c hc hc0 (by simpa only [hc1] using hx)
    have hhalf := hopen (ball p (R / 2)) isOpen_ball
      ⟨p, mem_ball_self (by positivity)⟩ Subset.rfl
    rw [hhalf] at hlow
    have hmone : 1 ≤ m := by exact_mod_cast hlow
    omega
  obtain ⟨k, _, hkclosed, _, _, hangular⟩ :=
    exists_local_integer_dimH_and_angularObstruction_of_intrinsic_eight_comparison_and_dimH
      hcurves p hR hdim hlocal
  have hkm : k = m := by
    exact_mod_cast hkclosed.symm.trans hclosed
  subst k
  let : LocallyCompactSpace (ball p (8 * R)) :=
    locallyCompactSpace_ball_of_intrinsic_local_comparison_and_dimH hcurves p
      (by positivity : 0 < 8 * R) hdim hlocal
  have hn : 0 < n := lt_of_lt_of_le hm hmn
  have hnR : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hθ : 0 ≤ (8 * (n : ℝ))⁻¹ := by positivity
  have hθpi : (8 * (n : ℝ))⁻¹ ≤ Real.pi / 2 := by
    have hle : (8 * (n : ℝ))⁻¹ ≤ 1 := by
      apply (inv_le_one₀ (by positivity : 0 < 8 * (n : ℝ))).mpr
      linarith
    have hpi : 1 < Real.pi / 2 := by
      simpa only [Real.sin_pi_div_two] using Real.sin_lt Real.pi_div_two_pos
    exact hle.trans hpi.le
  refine ⟨m, hm, hmn, hclosed, hopen, htangent, S, hGS, hDS, ?_⟩
  intro q hqS
  let : HasAnglesAt q.val := hasAnglesAt_of_intrinsic_ball_local_comparison hcurves p
    (by positivity : 0 < 8 * R) (by norm_num : (0 : ℝ) ≤ 1) hlocal
    (by change dist q.val p < 8 * R
        have hh : dist q.val p < R / 2 := q.property
        linarith)
  obtain ⟨e, he⟩ := hregular q hqS
  refine ⟨e, he, ?_⟩
  intro η hη
  have hqp : dist q.val p < R / 2 := q.property
  let η' : ℝ := min η ((R / 2 - dist q.val p) / 2)
  have hη' : 0 < η' := lt_min hη (by linarith)
  have hball (x : X) (hx : dist x q.val < η') : x ∈ ball p (R / 2) := by
    have hbound : η' ≤ (R / 2 - dist q.val p) / 2 := min_le_right _ _
    have htri := dist_triangle x q.val p
    change dist x p < R / 2
    linarith
  obtain ⟨d, s, ρ, hs, hsR, hlength, hrad, hρ, hρs, hρη, hanchors, _, hL,
      E, F, hF, hFq, hdist, hhomeo⟩ :=
    exists_uniform_strut_chart_of_euclidean_tangent hcurves hm hmn hR hqp hη' hlocal
      e he (fun x hx => hangular x.val (hball x.val hx) _ hθ hθpi)
  exact ⟨d, s, ρ, hs, hsR, hlength, hrad, hρ, hρs,
    hρη.trans_le (min_le_left _ _), hanchors,
    (fun x hx => hball x (lt_trans hx hρη)), hL, E, F, hF, hFq, hdist, hhomeo⟩

end DifferentialGeometry.Geometry.Comparison.Toponogov
