import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.StandardSolution.StandardScalarGeodesic
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.StandardSolution.StandardScaledTerminalRay
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.FixedDepthEscape

noncomputable section

open Set Filter
open DifferentialGeometry.Geometry.Curvature
open scoped Manifold ContDiff Topology ENNReal

namespace DifferentialGeometry.PDE.RicciFlow

private abbrev E3 := EuclideanSpace ℝ (Fin 3)

theorem exists_standard_scalar_level_radius_escape_of_not_bounded
    {tau A B D : ℝ} (htau : 0 < tau) (hAB : A ≤ B) (hD : 0 ≤ D)
    (hnot : ¬ ∃ C : ℝ, ∀ (S : PartialStandardSolution) (t : ℝ),
      t ∈ S.domain → tau ≤ t → t < 1 → ∀ p y : E3,
        metricScalarAt (S.metric t) p ≤ A →
        riemannianEDistOf (S.metric t) p y ≤ ENNReal.ofReal D →
        metricScalarAt (S.metric t) y ≤ C) :
    ∃ (S : ℕ → PartialStandardSolution) (time : ℕ → ℝ) (q y : ℕ → E3) (rho : ℝ),
      0 < rho ∧
      (∀ i, time i ∈ (S i).domain ∧ tau ≤ time i ∧ time i < 1) ∧
      (∀ i, metricScalarAt ((S i).metric (time i)) (q i) = B) ∧
      (∀ r : ℝ, 0 < r → r < rho → ∃ C : ℝ,
        ∀ᶠ i in atTop, ∀ z ∈ riemannianClosedBallOf ((S i).metric (time i)) (q i) r,
          metricScalarAt ((S i).metric (time i)) z ≤ C) ∧
      Tendsto (fun i => (riemannianEDistOf ((S i).metric (time i)) (q i) (y i)).toReal)
        atTop (𝓝 rho) ∧
      Tendsto (fun i => metricScalarAt ((S i).metric (time i)) (y i)) atTop atTop := by
  classical
  have hchoose (i : ℕ) : ∃ (S : PartialStandardSolution) (t : ℝ) (p y : E3),
      t ∈ S.domain ∧ tau ≤ t ∧ t < 1 ∧ metricScalarAt (S.metric t) p ≤ A ∧
        riemannianEDistOf (S.metric t) p y ≤ ENNReal.ofReal D ∧
        (i : ℝ) < metricScalarAt (S.metric t) y := by
    by_contra hn
    push Not at hn
    apply hnot
    refine ⟨i, ?_⟩
    intro S t ht htaut ht1 p y hbase hdist
    exact hn S t p y ht htaut ht1 hbase hdist
  choose S time point target htime hlate htime1 hbase hdist hhigh using hchoose
  have hblow : Tendsto (fun i => metricScalarAt ((S i).metric (time i)) (target i))
      atTop atTop := by
    apply tendsto_atTop_mono' atTop (Eventually.of_forall fun i => (hhigh i).le)
    exact tendsto_natCast_atTop_atTop
  have hdistReal (i : ℕ) :
      (riemannianEDistOf ((S i).metric (time i)) (point i) (target i)).toReal ≤ D := by
    have h := ENNReal.toReal_mono ENNReal.ofReal_ne_top (hdist i)
    simpa only [ENNReal.toReal_ofReal hD] using h
  obtain ⟨ind, q, y, rho, hind, hrho, hq, hinner, hdisty, hblowy⟩ :=
    exists_standard_scalar_level_radius_escape S time point target htau hAB hD
      (fun i => ⟨htime i, hlate i, htime1 i⟩) hbase hdistReal hblow
  exact ⟨S ∘ ind, time ∘ ind, q, y, rho, hrho,
    fun i => ⟨htime (ind i), hlate (ind i), htime1 (ind i)⟩,
    hq, hinner, hdisty, hblowy⟩

open DifferentialGeometry.CheegerGromovCompactness
open DifferentialGeometry.PDE.RicciFlow.Perelman
open DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn

attribute [local instance] PointedFlowData.topology PointedFlowData.charted
  PointedFlowData.smooth PointedFlowData.t2 PointedFlowData.sigmaCompact
  PointedRiemannianManifold.topology PointedRiemannianManifold.charted
  PointedRiemannianManifold.smooth PointedRiemannianManifold.t2
  PointedRiemannianManifold.sigmaCompact PointedRiemannianManifold.t2TangentBundle

theorem exists_standard_scalar_bound_at_bounded_distance (A D : ℝ) (hD : 0 ≤ D) :
    ∃ C : ℝ, ∀ (S : PartialStandardSolution) (t : ℝ),
      t ∈ S.domain → 3 / 4 ≤ t → t < 1 → ∀ p y : E3,
        metricScalarAt (S.metric t) p ≤ A →
        riemannianEDistOf (S.metric t) p y ≤ ENNReal.ofReal D →
        metricScalarAt (S.metric t) y ≤ C := by
  classical
  let kappa := standardModelKappa
  have hkappa : 0 < kappa := standardModelKappa_pos
  obtain ⟨epsStar, hepsStar, hexclude⟩ :=
    finite_ray_exclusion_of_minimizing_segment_convergence hkappa
  let eps := min (epsStar / 2) (1 / 2)
  have heps : 0 < eps := lt_min (half_pos hepsStar) (by norm_num)
  have heps1 : eps < 1 := (min_le_right _ _).trans_lt (by norm_num)
  have hepsStar' : eps ≤ epsStar := (min_le_left _ _).trans (by linarith)
  obtain ⟨B0, hB0, hnormalize⟩ := exists_standard_parabolic_sequence_model_threshold heps heps1
  let B := max B0 A
  have hB0B : B0 ≤ B := le_max_left _ _
  have hAB : A ≤ B := le_max_right _ _
  by_contra hnot
  obtain ⟨S, time, point, y, rho, hrho, htime, hpoint, hinner, hdist, hblow⟩ :=
    exists_standard_scalar_level_radius_escape_of_not_bounded
      (by norm_num : (0 : ℝ) < 3 / 4) hAB hD hnot
  obtain ⟨hB, hcarrier, hregular, hconnected, hcomplete, hsource, _, hnc, hpinch,
    orientation, hgood⟩ := hnormalize B hB0B S time point htime hpoint
  let X := standardParabolicSequence B hB S time point htime
  obtain ⟨f, hf, L, hL, maps, C, hcanonical, hcompact, hradial, hsec, hrest⟩ :=
    exists_standard_parabolic_isometric_segment_of_scalar_escape B hB S time point y
      hrho htime hinner hdist hblow
  let _ : PathConnectedSpace L.M := hL
  let _ : EMetricSpace L.M := L.emetricSpace
  let _ : MetricSpace L.M := EMetricSpace.toMetricSpace
    (fun x y => riemannianEDistOf_ne_top L.metric x y)
  obtain ⟨gamma, ell, g, hell, hgamma, hendpoint, hg, _, _, hconv, _, hscalar,
    q, hq, _, _⟩ := hrest
  have hdepth : 0 < B / 4 := div_pos hB (by norm_num)
  have hPhi : AdmissiblePinchingFunction (fun _ : ℝ => 1) :=
    admissiblePinchingFunction_const zero_lt_one
  apply hexclude eps heps hepsStar' (Real.sqrt 1250) (by positivity) (fun _ => 1)
    hPhi X (fun _ => B / 4) (fun _ => B) (B / 4) B hdepth hB
    (fun _ => le_rfl) (fun _ => le_rfl) ?_ ?_ hconnected orientation hcomplete hsource
    (fun i => by
      change ParabolicallyKappaNoncollapsedBelowScale _
        (modelNoncollapseFactor * standardModelKappa) _
      rw [modelNoncollapseFactor_mul_standardModelKappa]
      exact parabolicallyKappaNoncollapsedBelowScale_of_spatially (hnc i))
    hpinch hgood f L maps C.metrics hcanonical hL (Real.sqrt B * rho)
    (mul_pos (Real.sqrt_pos.mpr hB) hrho) ell hell hcompact gamma
    (fun n => (hgamma n).2.1) (fun n => (hgamma n).2.2.2.2) hsec g hg hconv
    hendpoint hscalar q hq
  · intro i
    rw [hcarrier i]
    congr 2
    ring
  · intro i
    rw [hregular i]
    congr 2
    ring


end DifferentialGeometry.PDE.RicciFlow
