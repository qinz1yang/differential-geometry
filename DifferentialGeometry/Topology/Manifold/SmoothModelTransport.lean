import DifferentialGeometry.Topology.Manifold.ModelTransport
import Mathlib.Geometry.Manifold.IsManifold.ExtChartAt

set_option autoImplicit false
noncomputable section
open Set Function
open scoped Manifold ContDiff
namespace DifferentialGeometry.Manifold

theorem isManifold_transHomeomorph
    {𝕜 E F H H' M : Type*} [NontriviallyNormedField 𝕜]
    [NormedAddCommGroup E] [NormedSpace 𝕜 E]
    [NormedAddCommGroup F] [NormedSpace 𝕜 F]
    [TopologicalSpace H] [TopologicalSpace H'] [TopologicalSpace M] [ChartedSpace H M]
    (I : ModelWithCorners 𝕜 E H) (J : ModelWithCorners 𝕜 F H')
    (e : H ≃ₜ H') (L : E ≃L[𝕜] F)
    (hc : ∀ y, J (e y) = L (I y)) [IsManifold I ∞ M] :
    let _ := chartedSpaceTransHomeomorph (M := M) e
    IsManifold J ∞ M := by
  let _ := chartedSpaceTransHomeomorph (M := M) e
  have hInv (x : F) (hx : x ∈ range J) : I.symm (L.symm x) = e.symm (J.symm x) := by
    obtain ⟨y, rfl⟩ := hx
    have hy : J y = L (I (e.symm y)) := by rw [← hc, e.apply_symm_apply]
    rw [hy, L.symm_apply_apply, I.left_inv]
    rw [← hy, J.left_inv]
  apply isManifold_of_contDiffOn
  rintro _ _ ⟨f, hf, u, hu, rfl⟩ ⟨g, hg, v, hv, rfl⟩
  have hu' : u = e.toOpenPartialHomeomorph := hu
  have hv' : v = e.toOpenPartialHomeomorph := hv
  subst u v
  have hfg := (StructureGroupoid.compatible (G := contDiffGroupoid ∞ I) hf hg).1
  let s := J.symm ⁻¹' ((f.trans e.toOpenPartialHomeomorph).symm.trans
    (g.trans e.toOpenPartialHomeomorph)).source ∩ range J
  have hmaps : MapsTo L.symm s (I.symm ⁻¹' (f.symm.trans g).source ∩ range I) := by
    intro x hx
    have he := hInv x hx.2
    refine ⟨?_, ?_⟩
    · change I.symm (L.symm x) ∈ (f.symm.trans g).source
      rw [he]
      simpa only [s, mfld_simps] using hx.1
    · obtain ⟨y, hy⟩ := hx.2
      refine ⟨e.symm y, ?_⟩
      apply L.injective
      rw [L.apply_symm_apply, ← hc, e.apply_symm_apply, hy]
  have hs := L.contDiff.comp_contDiffOn (hfg.comp L.symm.contDiff.contDiffOn hmaps)
  apply hs.congr
  intro x hx
  have he := hInv x hx.2
  change J (e (g (f.symm (e.symm (J.symm x))))) =
    L (I (g (f.symm (I.symm (L.symm x)))))
  rw [he, hc]

end DifferentialGeometry.Manifold
