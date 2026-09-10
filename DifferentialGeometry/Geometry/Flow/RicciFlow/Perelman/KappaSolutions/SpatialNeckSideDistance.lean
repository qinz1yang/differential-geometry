import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.KappaSolutions.SpatialNeckOrderedSides
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.KappaSolutions.SpatialNeckBandBounds

set_option autoImplicit false

noncomputable section

open Bundle Manifold Set
open DifferentialGeometry.Geometry.Riemannian
open scoped Manifold ContDiff Topology ENNReal

namespace DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [CompleteSpace E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {N : Type*} [MetricSpace N] [ChartedSpace H N] [IsManifold I ∞ N]
  [T2Space N] [SigmaCompactSpace N]

private local instance sideDistanceC1 : IsManifold I 1 N :=
  IsManifold.of_le (n := ∞) (by decide)

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace

variable [RiemannianBundle (fun q : N => TangentSpace I q)]
  [IsContinuousRiemannianBundle E (fun q : N => TangentSpace I q)]
  [IsRiemannianManifold I N]

namespace SpatialNeckSideData

variable {h : SmoothRiemannianMetric I N} {yStar : SpatialNeckSphere}
  {p : N} {epsilon : ℝ} {W : SpatialNeckWitness h yStar p epsilon}
  (D : SpatialNeckSideData W)

theorem exists_slice_distance_add (hEnorm : IsMetricNorm (I := I) h)
    (s : ℝ) (hs : |s| < epsilon⁻¹ + 1)
    {x y : N} (hx : x ∈ D.lower s) (hy : y ∈ D.upper s) :
    ∃ z ∈ W.embedding '' {q : spatialNeckBuffer epsilon | q.val.2 = s},
      dist x z + dist z y = dist x y := by
  let _ : NeZero (Module.finrank ℝ E) := ⟨by rw [W.dimension_three]; norm_num⟩
  have hdist (a b : N) : riemannianEDistOf (I := I) h a b = edist a b :=
    (riemannianEDistOf_eq_riemannianEDist h hEnorm a b).trans
      (IsRiemannianManifold.out (I := I) a b).symm
  have hfin : riemannianEDistOf (I := I) h x y ≠ ⊤ := by
    rw [hdist]
    exact edist_ne_top x y
  obtain ⟨γ, hγ, hγ0, hγ1, hlength⟩ :=
    completeMetric_exists_minimizing_curve h W.complete x y hfin
  have hleft : γ 0 ∈ D.lower s := by rw [hγ0]; exact hx
  have hright : γ 1 ∈ D.upper s := by rw [hγ1]; exact hy
  obtain ⟨u, hu, hslice⟩ := D.continuous_curve_crosses_slice s hs zero_le_one
    hγ.continuousOn hleft hright
  have hl := edistOf_le_metricPathELength h hu.1
    (hγ.mono (Icc_subset_Icc le_rfl hu.2))
  have hr := edistOf_le_metricPathELength h hu.2
    (hγ.mono (Icc_subset_Icc hu.1 le_rfl))
  have hadd : metricPathELength (I := I) h γ 0 u +
      metricPathELength (I := I) h γ u 1 = metricPathELength (I := I) h γ 0 1 := by
    let _ : RiemannianBundle (fun q : N => TangentSpace I q) := ⟨h.toRiemannianMetric⟩
    exact Manifold.pathELength_add hu.1 hu.2
  have hsum := (add_le_add hl hr).trans_eq (hadd.trans hlength)
  rw [hγ0, hγ1, hdist, hdist, hdist] at hsum
  have hreal := ENNReal.toReal_mono (edist_ne_top x y) hsum
  rw [ENNReal.toReal_add (edist_ne_top x (γ u)) (edist_ne_top (γ u) y),
    ← dist_edist, ← dist_edist, ← dist_edist] at hreal
  exact ⟨γ u, hslice, le_antisymm hreal (dist_triangle x (γ u) y)⟩

theorem inward_center_distance_lower (hEnorm : IsMetricNorm (I := I) h)
    (hsmall : epsilon ≤ spatialNeckControlEpsilon)
    {q : N} (hq : q ∈ D.lower (-(5 * Real.pi)))
    (z : spatialNeckBuffer epsilon) (hz : z.val.2 = 0) :
    11 / 12 * spatialNeckScale h p * (5 * Real.pi) ≤ dist q (W.embedding z) := by
  have hgap := spatialNeckControlEpsilon_inverse_gap W.epsilon_pos hsmall
  have hslice : |-(5 * Real.pi)| < epsilon⁻¹ + 1 := by
    rw [abs_neg, abs_of_pos (by positivity : 0 < 5 * Real.pi)]
    linarith [Real.pi_pos]
  have hzupper : W.embedding z ∈ D.upper (-(5 * Real.pi)) := by
    apply D.positive _ hslice z
    rw [hz]
    linarith [Real.pi_pos]
  obtain ⟨w, ⟨v, hv, rfl⟩, hadd⟩ := D.exists_slice_distance_add hEnorm
    (-(5 * Real.pi)) hslice hq hzupper
  have hvband : |v.val.2| ≤ 5 * Real.pi := by
    rw [hv, abs_neg, abs_of_pos (by positivity : 0 < 5 * Real.pi)]
  have hzband : |z.val.2| ≤ 5 * Real.pi := by
    rw [hz, abs_zero]
    positivity
  have hedist := W.band_axial_edist_lower hsmall v z hvband hzband
  rw [hz, hv, sub_neg_eq_add, zero_add,
    abs_of_pos (by positivity : 0 < 5 * Real.pi),
    riemannianEDistOf_eq_riemannianEDist h hEnorm,
    ← IsRiemannianManifold.out (I := I), edist_dist] at hedist
  have hlower := (ENNReal.ofReal_le_ofReal_iff dist_nonneg).mp hedist
  linarith [dist_nonneg (x := q) (y := W.embedding v)]

end SpatialNeckSideData

end DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions
