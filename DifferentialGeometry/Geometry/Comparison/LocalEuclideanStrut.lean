import DifferentialGeometry.Geometry.Comparison.LocalDenseEuclideanTangents
import DifferentialGeometry.Geometry.Comparison.EuclideanTangentStrut
import DifferentialGeometry.Topology.MetricSpace.LocalCurveDimension

set_option autoImplicit false

open Set Metric Real
open scoped NNReal ENNReal Topology

namespace DifferentialGeometry.Geometry.Comparison.Toponogov

theorem exists_dense_common_shortening_struts_of_intrinsic_eight_comparison_and_dimH
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
            e EuclideanCone.tip = 0 ∧ ∀ S : ℝ, 0 < S →
              ∃ (σ : Fin (m + 1) → GeodesicRepresentative q.val) (s : ℝ),
                0 < s ∧ s < S ∧ (∀ i, s ≤ (σ i).length) ∧
                (∀ i, dist q.val ((σ i).path s) = s) ∧
                (∀ i j, i ≠ j → Real.pi / 2 + 5 * (8 * (n : ℝ))⁻¹ <
                  comparisonAngleNegCurvature 1 (dist q.val ((σ i).path s))
                    (dist q.val ((σ j).path s)) (dist ((σ i).path s) ((σ j).path s))) ∧
                ∀ cap : ℝ, 0 < cap → ∃ ρ : ℝ, 0 < ρ ∧ ρ < s / 8 ∧ ρ < cap ∧
                  (∀ x ∈ ball q.val ρ, ∀ i, s / 2 < dist x ((σ i).path s)) ∧
                  ∀ x ∈ ball q.val ρ, ∀ i j, i ≠ j →
                    Real.pi / 2 + 4 * (8 * (n : ℝ))⁻¹ <
                      comparisonAngleNegCurvature 1 (dist x ((σ i).path s))
                        (dist x ((σ j).path s)) (dist ((σ i).path s) ((σ j).path s)) := by
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
  refine ⟨m, hm, hmn, hclosed, hopen, htangent, S, hGS, hDS, ?_⟩
  intro q hq
  let : HasAnglesAt q.val := hasAnglesAt_of_intrinsic_ball_local_comparison hcurves p
    (by positivity : 0 < 8 * R) (by norm_num : (0 : ℝ) ≤ 1) hlocal
    (by change dist q.val p < 8 * R; have hh : dist q.val p < R / 2 := q.property; linarith)
  obtain ⟨e, he⟩ := hregular q hq
  refine ⟨e, he, ?_⟩
  intro cap hcap
  exact exists_common_shortening_strut_neighborhood_of_euclidean_tangent hm hmn e he hcap

end DifferentialGeometry.Geometry.Comparison.Toponogov
