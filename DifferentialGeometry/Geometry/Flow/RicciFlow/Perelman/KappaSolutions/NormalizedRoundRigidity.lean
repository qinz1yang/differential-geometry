import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.KappaSolutions.BackwardHomotheticRicci
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.KappaSolutions.CurvatureNormalization


set_option autoImplicit false
noncomputable section

namespace DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions

open Bundle Set
open DifferentialGeometry.Geometry
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.CheegerGromovCompactness
open CanonicalNeighborhood
open scoped _root_.Manifold ContDiff

universe u uE uH

private instance normalizedRoundSphere4 :
    Fact (Module.finrank ℝ (EuclideanSpace ℝ (Fin 4)) = 3 + 1) :=
  ⟨by norm_num [finrank_euclideanSpace_fin]⟩

variable {E : Type uE} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [CompleteSpace E]
  {H : Type uH} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  (F : PointedFlowData.{u, uE, uH} (I := I) ancientTimeInterval)

local instance normalizedRoundTopology : TopologicalSpace F.M := F.topology
local instance normalizedRoundCharted : ChartedSpace H F.M := F.charted
local instance normalizedRoundSmooth : IsManifold I ∞ F.M := F.smooth
local instance normalizedRoundC1 : IsManifold I 1 F.M := IsManifold.of_le (n := ∞) (by decide)
local instance normalizedRoundT2 : T2Space F.M := F.t2
local instance normalizedRoundSigma : SigmaCompactSpace F.M := F.sigmaCompact


theorem round_of_curvatureNormalizedFlow_round
    (hdim : Module.finrank ℝ E = 3) (hconn : ConnectedSpace F.M)
    (t0 Q : ℝ) (hQ : 0 < Q) (ht0 : t0 ≤ 0) (p : F.M)
    (hround : IsShrinkingSphericalSpaceFormFlow
      (curvatureNormalizedFlow F rfl rfl t0 Q hQ ht0 p)) :
    IsShrinkingSphericalSpaceFormFlow F := by
  obtain ⟨T, hT, D, e, hmetric⟩ := hround
  have hsurj : Function.Surjective D.proj := by
    intro y
    exact ⟨_, (D.sectionAt y).proj_localSection
      ⟨y, (D.sectionAt y).mem_baseNeighborhood⟩⟩
  let _ : CompactSpace D.Q := hsurj.compactSpace D.proj_smooth.continuous
  have hcompact : CompactSpace F.M := e.symm.surjective.compactSpace e.symm.continuous
  let g : SmoothRiemannianMetric I F.M := Diffeomorph.pullbackMetricCross D.gQuot e
  let Tpast : ℝ := T / Q + t0
  have hTpast : t0 < Tpast := by
    have hpos := div_pos hT hQ
    dsimp only [Tpast]
    linarith
  have hpast (t : ℝ) (ht : t ≤ t0) : F.S.family.metric t =
      scaleMetric (4 * (Tpast - t))
        (mul_pos (by norm_num) (sub_pos.mpr (ht.trans_lt hTpast))) g := by
    have hs : Q * (t - t0) ≤ 0 :=
      mul_nonpos_of_nonneg_of_nonpos hQ.le (sub_nonpos.mpr ht)
    have htime : parabolicTime t0 Q (Q * (t - t0)) = t := by
      unfold parabolicTime
      field_simp [hQ.ne']
      ring
    have h := hmetric (Q * (t - t0)) hs
    change scaleMetric Q hQ (F.S.family.metric (parabolicTime t0 Q (Q * (t - t0)))) =
      scaleMetric (4 * (T - Q * (t - t0)))
        (mul_pos (by norm_num) (sub_pos.mpr (hs.trans_lt hT))) g at h
    rw [htime] at h
    apply SmoothRiemannianMetric.ext_inner
    intro x v w
    have hv := congrArg (fun gm : SmoothRiemannianMetric I F.M => gm.inner x v w) h
    simp only [scaleMetric_inner] at hv ⊢
    apply mul_left_cancel₀ hQ.ne'
    rw [hv]
    dsimp only [Tpast]
    field_simp [hQ.ne']
    ring
  exact ancient_sphericalSpaceFormFlow_of_backward_homothety F hdim hconn hcompact
    g ht0 hTpast hpast

end DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions
