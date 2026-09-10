import DifferentialGeometry.Topology.VectorField.RegularIndexComparison
import DifferentialGeometry.Topology.VectorField.FinitePerturbationIndexSum

set_option autoImplicit false
noncomputable section
open Set Filter Bundle
open scoped Manifold ContDiff Topology
namespace Poincare.VectorField
variable {d : ℕ} {H M : Type*} [TopologicalSpace H] [TopologicalSpace M]
  [ChartedSpace H M] [T2Space M] [CompactSpace M]
  (I : ModelWithCorners ℝ (EuclideanSpace ℝ (Fin (d + 1))) H) [IsManifold I ∞ M]

theorem interiorIndexSum_eq_of_boundary_germ
    (V W : ∀ x : M, TangentSpace I x)
    (hV : ContMDiff I I.tangent ∞ (fun x => (⟨x, V x⟩ : TangentBundle I M)))
    (hW : ContMDiff I I.tangent ∞ (fun x => (⟨x, W x⟩ : TangentBundle I M)))
    (hVfinite : {x | V x = 0}.Finite)
    (hVisolated : ∀ x, V x = 0 → HasContinuousIsolatedZero I V x)
    (hVint : ∀ x, V x = 0 → I.IsInteriorPoint x)
    (hWfinite : {x | W x = 0}.Finite)
    (hWisolated : ∀ x, W x = 0 → HasContinuousIsolatedZero I W x)
    (hWint : ∀ x, W x = 0 → I.IsInteriorPoint x)
    (hboundary : ∀ x, ¬I.IsInteriorPoint x → V =ᶠ[𝓝 x] W) :
    interiorIndexSum I V hVfinite hVisolated hVint =
      interiorIndexSum I W hWfinite hWisolated hWint := by
  obtain ⟨_, F, hF, hFfinite, hFisolated, hFint, _, _, hFgerm, hFreg, hFindex⟩ :=
    exists_regular_perturbation_interiorIndexSum_eq I V hV hVfinite hVint
  obtain ⟨_, G, hG, hGfinite, hGisolated, hGint, _, _, hGgerm, hGreg, hGindex⟩ :=
    exists_regular_perturbation_interiorIndexSum_eq I W hW hWfinite hWint
  have hboundaryFG : ∀ x, ¬I.IsInteriorPoint x → F =ᶠ[𝓝 x] G := by
    intro x hx
    filter_upwards [hFgerm x hx, hGgerm x hx, hboundary x hx] with y hyF hyG hy
    exact (TotalSpace.mk_injective y hyF).trans (hy.trans (TotalSpace.mk_injective y hyG).symm)
  have he := interiorIndexSum_eq_of_regular_boundary_germ I F G hF hG hFreg hGreg
    hFfinite hFisolated hFint hGfinite hGisolated hGint hboundaryFG
  exact hFindex.symm.trans (he.trans hGindex)

end Poincare.VectorField
