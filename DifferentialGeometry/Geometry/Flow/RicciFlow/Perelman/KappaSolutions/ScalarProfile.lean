import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.KappaSolutions.RoundFlowMixedJets
import DifferentialGeometry.Geometry.Metric.Sphere.Quotient.ScalarCurvature

set_option autoImplicit false
noncomputable section

namespace DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions

open Bundle Filter Set
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.CheegerGromovCompactness
open CanonicalNeighborhood
open scoped _root_.Manifold ContDiff _root_.Topology

universe u uE uH

variable {E : Type uE} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [CompleteSpace E]
  {H : Type uH} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  (F : PointedFlowData.{u, uE, uH} (I := I) ancientTimeInterval)

local instance scalarProfileTopology : TopologicalSpace F.M := F.topology
local instance scalarProfileCharted : ChartedSpace H F.M := F.charted
local instance scalarProfileSmooth : IsManifold I ∞ F.M := F.smooth
local instance scalarProfileC1 : IsManifold I 1 F.M := IsManifold.of_le (n := ∞) (by decide)
local instance scalarProfileT2 : T2Space F.M := F.t2
local instance scalarProfileSigma : SigmaCompactSpace F.M := F.sigmaCompact

theorem scalar_profile_eq_of_shrinking_spherical_space_form_flow
    (hround : IsShrinkingSphericalSpaceFormFlow (I := I) F) :
    ∃ T : ℝ, 0 < T ∧ ∀ t : ℝ, t ≤ 0 → ∀ x : F.M,
      F.S.scalar t x = 3 / (2 * (T - t)) := by
  obtain ⟨T, hT, Dq, e, hmetric⟩ := hround
  refine ⟨T, hT, ?_⟩
  intro t ht x
  have hscale : 0 < 4 * (T - t) := by nlinarith
  have hm : F.S.base.metric t = scaleMetric (4 * (T - t)) hscale
      (Diffeomorph.pullbackMetricCross Dq.gQuot e) := hmetric t ht
  change metricScalarAt (I := I) (F.S.base.metric t) x = _
  rw [hm, metricScalarAt_scaleMetric, metricScalar_cross, Dq.gQuot_scalar]
  norm_num
  field_simp
  ring

theorem scalar_eq_of_normalized_shrinking_spherical_space_form_flow
    (hround : IsShrinkingSphericalSpaceFormFlow (I := I) F)
    (hbase : PointedFlowScalarAtBase (I := I) F 1)
    {t : ℝ} (ht : t ≤ 0) (x : F.M) :
    F.S.scalar t x = 1 / (1 - (2 / 3 : ℝ) * t) := by
  obtain ⟨T, hT, hscalar⟩ := scalar_profile_eq_of_shrinking_spherical_space_form_flow F hround
  have hnorm := hscalar 0 le_rfl F.basepoint
  change F.S.scalar 0 F.basepoint = 1 at hbase
  rw [hbase, sub_zero] at hnorm
  have hmul : 1 * (2 * T) = (3 : ℝ) :=
    (eq_div_iff (by positivity : 2 * T ≠ 0)).mp hnorm
  have hTnorm : T = 3 / 2 := by linarith
  rw [hscalar t ht x, hTnorm]
  field_simp

theorem scalar_hasDerivWithinAt_of_shrinking_spherical_space_form_flow
    (hround : IsShrinkingSphericalSpaceFormFlow (I := I) F)
    {t : ℝ} (ht : t ≤ 0) (x : F.M) :
    HasDerivWithinAt (fun s => F.S.scalar s x)
      ((2 / 3 : ℝ) * F.S.scalar t x ^ 2) (Iic t) t := by
  obtain ⟨T, hT, hscalar⟩ := scalar_profile_eq_of_shrinking_spherical_space_form_flow F hround
  have hne : 2 * (T - t) ≠ 0 := by nlinarith
  have hden : HasDerivAt (fun s : ℝ => 2 * (T - s)) (-2) t := by
    convert! ((hasDerivAt_id t).const_sub T).const_mul 2 using 1
    norm_num
  have hd := (hasDerivAt_const t (3 : ℝ)).div hden hne
  have hd' : HasDerivAt (fun s : ℝ => 3 / (2 * (T - s)))
      ((2 / 3 : ℝ) * F.S.scalar t x ^ 2) t := by
    apply hd.congr_deriv
    rw [hscalar t ht x]
    field_simp
    ring
  exact hd'.hasDerivWithinAt.congr (fun s hs => hscalar s (hs.trans ht) x) (hscalar t ht x)

theorem abs_scalar_derivWithin_of_shrinking_spherical_space_form_flow
    (hround : IsShrinkingSphericalSpaceFormFlow (I := I) F)
    {t : ℝ} (ht : t ≤ 0) (x : F.M) :
    |derivWithin (fun s => F.S.scalar s x) (Iic t) t| =
      (2 / 3 : ℝ) * F.S.scalar t x ^ 2 := by
  rw [(scalar_hasDerivWithinAt_of_shrinking_spherical_space_form_flow F hround ht x).derivWithin
    (uniqueDiffWithinAt_Iic t), abs_of_nonneg (by positivity)]

theorem scalar_derivWithin_terminal_of_normalized_shrinking_spherical_space_form_flow
    (hround : IsShrinkingSphericalSpaceFormFlow (I := I) F)
    (hbase : PointedFlowScalarAtBase (I := I) F 1) (x : F.M) :
    derivWithin (fun s => F.S.scalar s x) (Iic 0) 0 = 2 / 3 := by
  rw [(scalar_hasDerivWithinAt_of_shrinking_spherical_space_form_flow F hround le_rfl
    x).derivWithin (uniqueDiffWithinAt_Iic 0),
    scalar_eq_of_normalized_shrinking_spherical_space_form_flow F hround hbase le_rfl x]
  norm_num

theorem scalar_profile_of_shrinking_spherical_space_form_flow
    (hround : IsShrinkingSphericalSpaceFormFlow (I := I) F) :
    ∀ t : ℝ, t ≤ 0 → ∃ R : ℝ, 0 < R ∧ ∀ x : F.M, F.S.scalar t x = R := by
  obtain ⟨T, hT, hscalar⟩ := scalar_profile_eq_of_shrinking_spherical_space_form_flow F hround
  intro t ht
  refine ⟨3 / (2 * (T - t)), ?_, hscalar t ht⟩
  have hpos : 0 < T - t := by linarith
  positivity

end DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions
