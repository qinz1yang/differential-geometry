import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.KappaSolutions.AncientSurfaceFixedCover
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
open scoped Manifold ContDiff _root_.Topology

local notation "SphereTwo" => Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1

private local instance ancientSurfaceModelsSphereDimension :
    Fact (Module.finrank ℝ (EuclideanSpace ℝ (Fin 3)) = 2 + 1) := ⟨by simp⟩

theorem exists_antipodal_quotient_diffeomorph
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
    (pi : SphereTwo → M) (hlocal : IsLocalDiffeomorph (𝓡 2) I ∞ pi)
    (hsurj : Function.Surjective pi)
    (hfibres : ∀ x y : SphereTwo, pi x = pi y ↔ y = x ∨ y = -x) :
    ∃ d : SphereAntipodalQuotient ≃ₘ⟮𝓡 2, I⟯ M,
      ∀ x : SphereTwo, d (SphereAntipodalQuotient.proj x) = pi x := by
  obtain ⟨d, hd⟩ := SphereAntipodalQuotient.exists_homeomorph pi
    hlocal.isLocalHomeomorph.continuous hlocal.isLocalHomeomorph.isOpenMap hsurj hfibres
  obtain ⟨D, hD⟩ := exists_diffeomorph_of_homeomorph_comp_localDiffeomorph
    SphereAntipodalQuotient.proj SphereAntipodalQuotient.isLocalDiffeomorph_proj
    SphereAntipodalQuotient.surjective_proj pi hlocal d hd
  refine ⟨D, ?_⟩
  intro x
  rw [hD]
  exact hd x

universe u uE uH

variable {E : Type uE} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [CompleteSpace E]
  {H : Type uH} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  (F : PointedFlowData.{u, uE, uH} (I := I) ancientTimeInterval)

private local instance ancientSurfaceModelsTopology : TopologicalSpace F.M := F.topology
private local instance ancientSurfaceModelsCharted : ChartedSpace H F.M := F.charted
private local instance ancientSurfaceModelsSmooth : IsManifold I ∞ F.M := F.smooth

theorem ancientKappaSurface_fixed_smooth_models
    {kappa : ℝ} (hF : IsAncientKappaSolution kappa F)
    (hdim : Module.finrank ℝ E = 2) :
    ∃ T : ℝ, 0 < T ∧ ∃ pi : SphereTwo → F.M,
      IsLocalDiffeomorph (𝓡 2) I ∞ pi ∧ IsCoveringMap pi ∧ Function.Surjective pi ∧
      (∀ t : ℝ, t ≤ 0 → ∀ (x : SphereTwo) (v w : TangentSpace (𝓡 2) x),
        (F.S.family.metric t).inner (pi x)
            (mfderiv (𝓡 2) I pi x v) (mfderiv (𝓡 2) I pi x w) =
          (2 * (T - t)) * (roundMetric (E := EuclideanSpace ℝ (Fin 3)) (n := 2)).inner
            x v w) ∧
      ((∃ d : SphereTwo ≃ₘ⟮𝓡 2, I⟯ F.M, ∀ x : SphereTwo, d x = pi x) ∨
        ∃ d : SphereAntipodalQuotient ≃ₘ⟮𝓡 2, I⟯ F.M,
          ∀ x : SphereTwo, d (SphereAntipodalQuotient.proj x) = pi x) ∧
      (∀ d : SphereTwo ≃ₜ SphereTwo, pi ∘ d = pi →
        d = Homeomorph.refl SphereTwo ∨ ∀ x : SphereTwo, d x = -x) := by
  let _ : CompactSpace F.M := ancientKappaSurface_compact F hF hdim
  obtain ⟨hT, pi, hlocal, hcover, hsurj, hmetric, hcases, hdeck⟩ :=
    ancientKappaSurface_fixed_round_cover F hF hdim
  refine ⟨_, hT, pi, hlocal, hcover, hsurj, hmetric, ?_, hdeck⟩
  rcases hcases with hsphere | hfibres
  · exact Or.inl hsphere
  · exact Or.inr (exists_antipodal_quotient_diffeomorph pi hlocal hsurj hfibres)

end DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions

end
