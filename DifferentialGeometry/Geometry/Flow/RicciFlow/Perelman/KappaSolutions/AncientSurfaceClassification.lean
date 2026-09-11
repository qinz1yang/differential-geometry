import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.KappaSolutions.AncientSurfaceSmoothModels
import DifferentialGeometry.Topology.ProjectiveSpace.AntipodalSurfaceOrientation

set_option autoImplicit false

noncomputable section

namespace DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions

open Bundle
open DifferentialGeometry.Geometry
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.CheegerGromovCompactness
open CanonicalNeighborhood
open scoped Manifold ContDiff Topology

local notation "SphereTwo" => Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1

private local instance surfaceClassificationSphereDimension :
    Fact (Module.finrank ℝ (EuclideanSpace ℝ (Fin 3)) = 2 + 1) := ⟨by simp⟩

universe u uE uH

variable {E : Type uE} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [CompleteSpace E]
  {H : Type uH} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  (F : PointedFlowData.{u, uE, uH} (I := I) ancientTimeInterval)

private local instance surfaceClassificationTopology : TopologicalSpace F.M := F.topology
private local instance surfaceClassificationCharted : ChartedSpace H F.M := F.charted
private local instance surfaceClassificationSmooth : IsManifold I ∞ F.M := F.smooth

theorem ancientKappaSurface_two_dimensional_classification
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
        d = Homeomorph.refl SphereTwo ∨ ∀ x : SphereTwo, d x = -x) ∧
      (Nonempty (SurfaceOrientation I F.M) →
        ∃ d : SphereTwo ≃ₘ⟮𝓡 2, I⟯ F.M, ∀ x : SphereTwo, d x = pi x) := by
  let _ : CompactSpace F.M := ancientKappaSurface_compact F hF hdim
  obtain ⟨hT, pi, hlocal, hcover, hsurj, hmetric, hcases, hdeck⟩ :=
    ancientKappaSurface_fixed_round_cover F hF hdim
  refine ⟨_, hT, pi, hlocal, hcover, hsurj, hmetric, ?_, hdeck, ?_⟩
  · rcases hcases with hsphere | hfibres
    · exact Or.inl hsphere
    · exact Or.inr (exists_antipodal_quotient_diffeomorph pi hlocal hsurj hfibres)
  · rintro ⟨o⟩
    rcases hcases with hsphere | hfibres
    · exact hsphere
    · exact (o.not_antipodal_localDiffeomorph pi hlocal (fun x =>
        ((hfibres x (-x)).mpr (Or.inr rfl)).symm)).elim

end DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions

end
