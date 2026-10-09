import DifferentialGeometry.Geometry.Comparison.LocalDenseEuclideanTangents
import DifferentialGeometry.Geometry.Comparison.IntrinsicPacketDirections
import DifferentialGeometry.Geometry.Comparison.FiniteAnglePattern
import DifferentialGeometry.Geometry.Comparison.EuclideanAngularObstruction

set_option autoImplicit false

open Set Metric Real
open scoped NNReal ENNReal Topology

namespace DifferentialGeometry.Geometry.Comparison.Toponogov

theorem exists_local_integer_dimH_and_angularObstruction_of_intrinsic_eight_comparison_and_dimH
    {X : Type*} [MetricSpace X] [CompleteSpace X]
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
    ∃ m : ℕ, m ≤ n ∧ dimH (closedBall p R) = m ∧
      (∀ V : Set X, IsOpen V → V.Nonempty → V ⊆ ball p (R / 2) → dimH V = m) ∧
      (∀ (q : X) (hq : q ∈ ball p (R / 2)),
        letI : HasAnglesAt q := hasAnglesAt_of_intrinsic_ball_local_comparison hcurves p
          (by positivity : 0 < 8 * R) (by norm_num : (0 : ℝ) ≤ 1) hlocal
          (by change dist q p < 8 * R; have hh : dist q p < R / 2 := hq; linarith)
        dimH (univ : Set (TangentCone q)) = m) ∧
      ∀ (q : X) (hq : q ∈ ball p (R / 2)),
        letI : HasAnglesAt q := hasAnglesAt_of_intrinsic_ball_local_comparison hcurves p
          (by positivity : 0 < 8 * R) (by norm_num : (0 : ℝ) ≤ 1) hlocal
          (by change dist q p < 8 * R; have hh : dist q p < R / 2 := hq; linarith)
        ∀ θ : ℝ, 0 ≤ θ → θ ≤ Real.pi / 2 →
          AngularObstruction (SpaceOfDirections q) m θ := by
  classical
  obtain ⟨m, hmn, hclosed, hopen, htangent, S, _, hDS, hregular⟩ :=
    exists_dense_euclidean_tangents_of_intrinsic_eight_comparison_and_dimH
      hcurves p hR hdim hlocal
  let : LocallyCompactSpace (ball p (8 * R)) :=
    locallyCompactSpace_ball_of_intrinsic_local_comparison_and_dimH hcurves p
      (by positivity : 0 < 8 * R) hdim hlocal
  refine ⟨m, hmn, hclosed, hopen, htangent, ?_⟩
  intro q hq
  let : HasAnglesAt q := hasAnglesAt_of_intrinsic_ball_local_comparison hcurves p
    (by positivity : 0 < 8 * R) (by norm_num : (0 : ℝ) ≤ 1) hlocal
    (by change dist q p < 8 * R; have hh : dist q p < R / 2 := hq; linarith)
  intro θ hθ hθpi
  rintro ⟨ξ, ζ, hζ, hξ⟩
  let χ : Option (Fin (m + 1)) → SpaceOfDirections q := fun i => i.elim ξ ζ
  let b : Option (Fin (m + 1)) → Option (Fin (m + 1)) → ℝ := fun i j =>
    match i, j with
    | some _, some _ => Real.pi / 2 + θ
    | _, _ => Real.pi / 2 - θ
  have hsep : ∀ i j, i ≠ j → b i j < dist (χ i) (χ j) := by
    rintro (_ | i) (_ | j) hij
    · exact (hij rfl).elim
    · exact hξ j
    · simpa only [χ, Option.elim, dist_comm] using hξ i
    · exact hζ i j (fun h => hij (congrArg some h))
  obtain ⟨σ, s, η, hs, hsR, hη, _, _, hrad, _, _, hstable⟩ :=
    exists_common_shortening_angle_pattern (by norm_num : (0 : ℝ) ≤ 1)
      zero_lt_one (by positivity : 0 < R / 2) χ b hsep
  let a : Option (Fin (m + 1)) → X := fun i => (σ i).path s
  have haR (i : Option (Fin (m + 1))) : a i ∈ ball p R := by
    have htri := dist_triangle (a i) q p
    have hd : dist (a i) q = s := by rw [dist_comm]; exact hrad i
    rw [hd] at htri
    change dist (a i) p < R
    have hqp : dist q p < R / 2 := hq
    linarith
  obtain ⟨ρ, hρ, _, _, haway, hnear⟩ := hstable (R / 2) (by positivity)
  obtain ⟨u, huS, hu⟩ := hDS.exists_mem_open
    (isOpen_ball : IsOpen (ball (⟨q, hq⟩ : ball p (R / 2)) ρ))
    ⟨⟨q, hq⟩, mem_ball_self hρ⟩
  have huq : u.val ∈ ball q ρ := hu
  let : HasAnglesAt u.val := hasAnglesAt_of_intrinsic_ball_local_comparison hcurves p
    (by positivity : 0 < 8 * R) (by norm_num : (0 : ℝ) ≤ 1) hlocal
    (by change dist u.val p < 8 * R
        have hh : dist u.val p < R / 2 := u.property
        linarith)
  obtain ⟨e, he⟩ := hregular u huS
  have hne (i : Option (Fin (m + 1))) : u.val ≠ a i :=
    dist_pos.mp (lt_trans (by linarith : 0 < s / 2) (haway u.val huq i))
  obtain ⟨τ, _, hbound⟩ := exists_endpoint_representatives_of_intrinsic_eight_comparison
    hcurves p hR hlocal u.property a haR hne
  have hobs : AngularObstruction (SpaceOfDirections u.val) m θ := by
    simpa only [finrank_euclideanSpace_fin] using
      TangentCone.angularObstruction_of_pointed_isometry e he hθ hθpi
  apply hobs
  refine ⟨(τ none).direction, (fun i => (τ (some i)).direction), ?_, ?_⟩
  · intro i j hij
    have hc := hnear u.val huq (some i) (some j)
      (fun h => hij (Option.some.inj h))
    have hb := hbound (some i) (some j)
    change Real.pi / 2 + θ + 4 * η < comparisonAngleNegCurvature 1
      (dist u.val (a (some i))) (dist u.val (a (some j)))
      (dist (a (some i)) (a (some j))) at hc
    exact (by linarith : Real.pi / 2 + θ < comparisonAngleNegCurvature 1
      (dist u.val (a (some i))) (dist u.val (a (some j)))
      (dist (a (some i)) (a (some j)))).trans_le hb
  · intro j
    have hc := hnear u.val huq none (some j) (by simp)
    have hb := hbound none (some j)
    change Real.pi / 2 - θ + 4 * η < comparisonAngleNegCurvature 1
      (dist u.val (a none)) (dist u.val (a (some j)))
      (dist (a none) (a (some j))) at hc
    exact (by linarith : Real.pi / 2 - θ < comparisonAngleNegCurvature 1
      (dist u.val (a none)) (dist u.val (a (some j)))
      (dist (a none) (a (some j)))).trans_le hb

end DifferentialGeometry.Geometry.Comparison.Toponogov
