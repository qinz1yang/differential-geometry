import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.KappaSolutions.AncientCylinderTopologicalModels
import DifferentialGeometry.Topology.ProjectiveSpace.CylinderQuotientSmoothModels
import DifferentialGeometry.Topology.Manifold.LocalDiffeomorph.Descent

set_option autoImplicit false

noncomputable section

namespace DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions

open Bundle
open DifferentialGeometry.Geometry
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.CheegerGromovCompactness
open CanonicalNeighborhood
open scoped Manifold ContDiff

local notation "SphereAmbient" => EuclideanSpace ℝ (Fin 3)
local notation "SphereTwo" => Metric.sphere (0 : SphereAmbient) 1
local notation "Cylinder" => SphereTwo × ℝ
local notation "CylinderI" => ModelWithCorners.prod (𝓡 2) 𝓘(ℝ, ℝ)
local notation "sphereMetric" => roundMetric (E := SphereAmbient) (n := 2)

private local instance ancientCylinderSmoothSphereDimension :
    Fact (Module.finrank ℝ SphereAmbient = 2 + 1) := ⟨by simp⟩

universe u uE uH

variable {E : Type uE} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [CompleteSpace E]
  {H : Type uH} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  (F : PointedFlowData.{u, uE, uH} (I := I) ancientTimeInterval)

local instance ancientCylinderSmoothTopology : TopologicalSpace F.M := F.topology
local instance ancientCylinderSmoothCharted : ChartedSpace H F.M := F.charted
local instance ancientCylinderSmoothManifold : IsManifold I ∞ F.M := F.smooth
local instance ancientCylinderSmoothT2 : T2Space F.M := F.t2

theorem ancientKappa_null_plane_cylinder_smooth_models {kappa : ℝ}
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
        (∃ d : (SphereAntipodalQuotient × ℝ) ≃ₘ⟮CylinderI, I⟯ F.M,
          ∀ p : Cylinder, d (SphereAntipodalQuotient.productProjection p) = pi p) ∨
        ∃ d : CylinderDiagonalQuotient ≃ₘ⟮CylinderI, I⟯ F.M,
          ∀ p : Cylinder, d (CylinderDiagonalQuotient.proj p) = pi p) := by
  obtain ⟨T, hT, pi, hlocal, hsurj, hmetric, hcases⟩ :=
    ancientKappa_null_plane_cylinder_topological_models F hF hdim
      t₀ ht₀ x₀ v₀ w₀ hplane hnull
  refine ⟨T, hT, pi, hlocal, hsurj, hmetric, ?_⟩
  rcases hcases with htrivial | ⟨d, hd⟩ | ⟨d, hd⟩
  · exact Or.inl htrivial
  · have hq : IsLocalDiffeomorph CylinderI CylinderI ∞
        SphereAntipodalQuotient.productProjection :=
      isLocalDiffeomorph_prod_real SphereAntipodalQuotient.proj
        SphereAntipodalQuotient.isLocalDiffeomorph_proj
    obtain ⟨D, hD⟩ := exists_diffeomorph_of_homeomorph_comp_localDiffeomorph
      SphereAntipodalQuotient.productProjection hq
      SphereAntipodalQuotient.surjective_productProjection pi hlocal d hd
    refine Or.inr (Or.inl ⟨D, ?_⟩)
    intro p
    rw [hD]
    exact hd p
  · obtain ⟨D, hD⟩ := exists_diffeomorph_of_homeomorph_comp_localDiffeomorph
      CylinderDiagonalQuotient.proj CylinderDiagonalQuotient.isLocalDiffeomorph_proj
      CylinderDiagonalQuotient.surjective_proj pi hlocal d hd
    refine Or.inr (Or.inr ⟨D, ?_⟩)
    intro p
    rw [hD]
    exact hd p

end DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions

end
