import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.KappaSolutions.AncientSplitSurface
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.KappaSolutions.CylinderAsymptoticVolumeRatio

set_option autoImplicit false

noncomputable section

namespace DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions

open Bundle
open DifferentialGeometry.Geometry
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Geometry.Riemannian.Topology
open DifferentialGeometry.CheegerGromovCompactness
open CanonicalNeighborhood
open scoped Manifold ContDiff ENNReal

local notation "SphereTwo" => Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1

private local instance ancientSplitAvrSphereDimension :
    Fact (Module.finrank ℝ (EuclideanSpace ℝ (Fin 3)) = 2 + 1) := ⟨by simp⟩

universe u uE uH

variable {E : Type uE} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [CompleteSpace E]
  {H : Type uH} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  (F : PointedFlowData.{u, uE, uH} (I := I) ancientTimeInterval)

local instance ancientSplitAvrBaseTopology : TopologicalSpace F.M := F.topology
local instance ancientSplitAvrBaseCharted : ChartedSpace H F.M := F.charted
local instance ancientSplitAvrBaseSmooth : IsManifold I ∞ F.M := F.smooth
local instance ancientSplitAvrBaseT2 : T2Space F.M := F.t2
local instance ancientSplitAvrBaseSigma : SigmaCompactSpace F.M := F.sigmaCompact
local instance ancientSplitAvrBaseInhabited : Inhabited F.M := ⟨F.basepoint⟩
local instance ancientSplitAvrBaseLocallyPathConnected : LocallyPathConnectedSpace F.M := by
  let _ : LocallyPathConnectedSpace H :=
    I.toHomeomorph.isOpenEmbedding.locallyPathConnectedSpace
  exact ChartedSpace.locallyPathConnectedSpace H F.M
local instance ancientSplitAvrBaseSemilocallySimplyConnected :
    SemilocallySimplyConnectedSpace F.M :=
  manifold_semilocallySimplyConnectedSpace (I := I) (M := F.M)

theorem ancientKappa_null_plane_asymptoticVolumeRatio_eq_zero {kappa : ℝ}
    (hF : IsAncientKappaSolution (I := I) kappa F) (hdim : Module.finrank ℝ E = 3)
    (t₀ : ℝ) (ht₀ : t₀ ≤ 0) (x₀ : F.M) (v₀ w₀ : TangentSpace I x₀)
    (hplane : 0 <
      (F.S.family.metric t₀).inner x₀ v₀ v₀ *
        (F.S.family.metric t₀).inner x₀ w₀ w₀ -
          ((F.S.family.metric t₀).inner x₀ v₀ w₀) ^ 2)
    (hnull : F.S.base.rm04 t₀ x₀ (vec4 (I := I) v₀ w₀ w₀ v₀) = 0) :
    ∀ t : ℝ, t ≤ 0 → ∀ p : F.M,
      asymptoticVolumeRatio (I := I) (F.S.base.metric t) p = 0 := by
  obtain ⟨T, hT, Psi, hproduct⟩ := ancientKappa_null_plane_fixed_round_cylinder
    F hF hdim t₀ ht₀ x₀ v₀ w₀ hplane hnull
  let _ : ConnectedSpace F.M := hF.connected
  intro t ht p
  have hscale : 0 < 2 * (T - t) := by linarith
  let hSphere : SmoothRiemannianMetric (𝓡 2) SphereTwo :=
    scaleMetric (2 * (T - t)) hscale
      (roundMetric (E := EuclideanSpace ℝ (Fin 3)) (n := 2))
  have hslice : ∀ (x : SphereTwo) (s : ℝ)
      (v w : TangentSpace (𝓡 2) x) (a b : ℝ),
      (UniversalCover.liftedMetric (I := I) (F.S.family.metric t)).inner (Psi (x, s))
          (mfderiv ((𝓡 2).prod 𝓘(ℝ, ℝ)) I Psi (x, s) (v, a))
          (mfderiv ((𝓡 2).prod 𝓘(ℝ, ℝ)) I Psi (x, s) (w, b)) =
        hSphere.inner x v w + a * b := by
    intro x s v w a b
    simpa only [hSphere, scaleMetric_inner] using hproduct t ht x s v w a b
  exact cylinderCover_asymptoticVolumeRatio_eq_zero (I := I)
    (F.S.family.metric t) hdim hSphere Psi hslice p

end DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions

end
