import DifferentialGeometry.Geometry.Metric.UniversalCover.CylinderDescent
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.KappaSolutions.CylinderDeckRecentering
import DifferentialGeometry.Topology.ProjectiveSpace.CylinderDiagonalQuotient

set_option autoImplicit false

noncomputable section

namespace DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions

open Bundle
open DifferentialGeometry.Geometry
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Geometry.Riemannian.Topology
open DifferentialGeometry.CheegerGromovCompactness
open CanonicalNeighborhood
open scoped Manifold ContDiff

local notation "SphereAmbient" => EuclideanSpace ℝ (Fin 3)
local notation "SphereTwo" => Metric.sphere (0 : SphereAmbient) 1
local notation "Cylinder" => SphereTwo × ℝ
local notation "CylinderI" => ModelWithCorners.prod (𝓡 2) 𝓘(ℝ, ℝ)
local notation "sphereMetric" => roundMetric (E := SphereAmbient) (n := 2)

private local instance ancientCylinderModelsSphereDimension :
    Fact (Module.finrank ℝ SphereAmbient = 2 + 1) := ⟨by simp⟩

private theorem ancientCylinderModels_antipodal (x : SphereTwo) :
    sphereDiffeo (n := 2) (LinearIsometryEquiv.neg ℝ : SphereAmbient ≃ₗᵢ[ℝ] SphereAmbient)
        x = -x := by
  apply Subtype.ext
  rfl

universe u uE uH

variable {E : Type uE} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [CompleteSpace E]
  {H : Type uH} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  (F : PointedFlowData.{u, uE, uH} (I := I) ancientTimeInterval)

local instance ancientCylinderModelsTopology : TopologicalSpace F.M := F.topology
local instance ancientCylinderModelsCharted : ChartedSpace H F.M := F.charted
local instance ancientCylinderModelsSmooth : IsManifold I ∞ F.M := F.smooth
local instance ancientCylinderModelsInhabited : Inhabited F.M := ⟨F.basepoint⟩
local instance ancientCylinderModelsT2 : T2Space F.M := F.t2
local instance ancientCylinderModelsSigma : SigmaCompactSpace F.M := F.sigmaCompact
local instance ancientCylinderModelsLocallyPathConnected : LocallyPathConnectedSpace F.M := by
  let _ : LocallyPathConnectedSpace H := I.toHomeomorph.isOpenEmbedding.locallyPathConnectedSpace
  exact ChartedSpace.locallyPathConnectedSpace H F.M
local instance ancientCylinderModelsSemilocallySimplyConnected :
    SemilocallySimplyConnectedSpace F.M :=
  manifold_semilocallySimplyConnectedSpace (I := I) (M := F.M)

private theorem ancientCylinderModels_local
    (Psi : Cylinder ≃ₘ⟮CylinderI, I⟯ UniversalCover F.M) :
    IsLocalDiffeomorph CylinderI I ∞
      (fun p : Cylinder => UniversalCover.proj (Psi p)) :=
  isLocalDiffeomorph_comp (UniversalCover.proj_localDiffeo (I := I) (M := F.M))
    Psi.isLocalDiffeomorph

private theorem ancientCylinderModels_metric (T : ℝ)
    (Psi : Cylinder ≃ₘ⟮CylinderI, I⟯ UniversalCover F.M)
    (hproduct : ∀ t : ℝ, t ≤ 0 → ∀ (x : SphereTwo) (s : ℝ)
      (v w : TangentSpace (𝓡 2) x) (a b : ℝ),
      (UniversalCover.liftedMetric (I := I) (F.S.family.metric t)).inner (Psi (x, s))
          (mfderiv CylinderI I Psi (x, s) (v, a))
          (mfderiv CylinderI I Psi (x, s) (w, b)) =
        (2 * (T - t)) * (sphereMetric).inner x v w + a * b) :
    ∀ t : ℝ, t ≤ 0 → ∀ (x : SphereTwo) (s : ℝ)
      (v w : TangentSpace (𝓡 2) x) (a b : ℝ),
      (F.S.family.metric t).inner (UniversalCover.proj (Psi (x, s)))
          (mfderiv CylinderI I (fun p : Cylinder => UniversalCover.proj (Psi p))
            (x, s) (v, a))
          (mfderiv CylinderI I (fun p : Cylinder => UniversalCover.proj (Psi p))
            (x, s) (w, b)) =
        (2 * (T - t)) * (sphereMetric).inner x v w + a * b := by
  intro t ht x s v w a b
  exact (cylinderCover_projection_inner (F.S.family.metric t) Psi
    (x, s) (v, a) (w, b)).trans (hproduct t ht x s v w a b)

theorem ancientKappa_null_plane_cylinder_topological_models {kappa : ℝ}
    (hF : IsAncientKappaSolution (I := I) kappa F) (hdim : Module.finrank ℝ E = 3)
    (t₀ : ℝ) (ht₀ : t₀ ≤ 0) (x₀ : F.M) (v₀ w₀ : TangentSpace I x₀)
    (hplane : 0 <
      (F.S.family.metric t₀).inner x₀ v₀ v₀ *
        (F.S.family.metric t₀).inner x₀ w₀ w₀ -
          ((F.S.family.metric t₀).inner x₀ v₀ w₀) ^ 2)
    (hnull : F.S.base.rm04 t₀ x₀ (vec4 (I := I) v₀ w₀ w₀ v₀) = 0) :
    ∃ T : ℝ, 0 < T ∧ ∃ pi : Cylinder → F.M,
      IsLocalDiffeomorph CylinderI I ∞ pi ∧ Function.Surjective pi ∧
      (∀ t : ℝ, t ≤ 0 → ∀ (x : SphereTwo) (s : ℝ)
        (v w : TangentSpace (𝓡 2) x) (a b : ℝ),
        (F.S.family.metric t).inner (pi (x, s))
            (mfderiv CylinderI I pi (x, s) (v, a))
            (mfderiv CylinderI I pi (x, s) (w, b)) =
          (2 * (T - t)) * (sphereMetric).inner x v w + a * b) ∧
      ((∃ d : Cylinder ≃ₘ⟮CylinderI, I⟯ F.M, ∀ p : Cylinder, d p = pi p) ∨
        (∃ d : (SphereAntipodalQuotient × ℝ) ≃ₜ F.M,
          ∀ p : Cylinder, d (SphereAntipodalQuotient.productProjection p) = pi p) ∨
        ∃ d : CylinderDiagonalQuotient ≃ₜ F.M,
          ∀ p : Cylinder, d (CylinderDiagonalQuotient.proj p) = pi p) := by
  obtain ⟨T, hT, Psi, hproduct, hsurjective, hcases⟩ :=
    ancientKappa_null_plane_fixed_cylinder_deck_fibres F hF hdim
      t₀ ht₀ x₀ v₀ w₀ hplane hnull
  have hlocal := ancientCylinderModels_local F Psi
  rcases hcases with ⟨_, hsingle⟩ | ⟨_, hsphere | ⟨c, hdiagonal⟩⟩
  · have hinjective : Function.Injective
        (fun p : Cylinder => UniversalCover.proj (Psi p)) :=
      fun p q hpq => ((hsingle p q).mp hpq).symm
    obtain ⟨d, hd⟩ := cylinderCover_exists_diffeomorph_of_injective
      Psi hinjective hsurjective
    exact ⟨T, hT, _, hlocal, hsurjective,
      ancientCylinderModels_metric F T Psi hproduct, Or.inl ⟨d, hd⟩⟩
  · have hfibres : ∀ p q : Cylinder,
        UniversalCover.proj (Psi p) = UniversalCover.proj (Psi q) ↔
          q = p ∨ q = (-p.1, p.2) := by
      simpa only [ancientCylinderModels_antipodal] using hsphere
    obtain ⟨d, hd⟩ := SphereAntipodalQuotient.exists_product_homeomorph
      (fun p : Cylinder => UniversalCover.proj (Psi p))
      hlocal.contMDiff.continuous hlocal.isOpenMap hsurjective hfibres
    exact ⟨T, hT, _, hlocal, hsurjective,
      ancientCylinderModels_metric F T Psi hproduct, Or.inr (Or.inl ⟨d, hd⟩)⟩
  · let Psi' := (cylinderLineTranslation c).trans Psi
    have hlocal' := ancientCylinderModels_local F Psi'
    have hsurjective' := cylinderDeck_recenter_surjective Psi hsurjective c
    have hfibres : ∀ p q : Cylinder,
        UniversalCover.proj (Psi' p) = UniversalCover.proj (Psi' q) ↔
          q = p ∨ q = (-p.1, -p.2) := by
      simpa only [ancientCylinderModels_antipodal] using
        cylinderDeck_recenter_fibres Psi c hdiagonal
    obtain ⟨d, hd⟩ := CylinderDiagonalQuotient.exists_homeomorph
      (fun p : Cylinder => UniversalCover.proj (Psi' p))
      hlocal'.contMDiff.continuous hlocal'.isOpenMap hsurjective' hfibres
    have hproduct' := cylinderLineTranslation_trans_pullback
      F.S.family.metric T Psi hproduct c
    exact ⟨T, hT, _, hlocal', hsurjective',
      ancientCylinderModels_metric F T Psi' hproduct', Or.inr (Or.inr ⟨d, hd⟩)⟩

end DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions

end
