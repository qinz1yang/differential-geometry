import DifferentialGeometry.Topology.Manifold.ModelTransport
import Mathlib.Geometry.Manifold.IsManifold.ExtChartAt
import Mathlib.Geometry.Manifold.MFDeriv.Basic
import Mathlib.Geometry.Manifold.MFDeriv.FDeriv
import Mathlib.Analysis.Calculus.FDeriv.Equiv

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

variable {𝕜 E F H H' M N X H₀ : Type*} [NontriviallyNormedField 𝕜]
  [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  [NormedAddCommGroup F] [NormedSpace 𝕜 F]
  [TopologicalSpace H] [TopologicalSpace H'] [TopologicalSpace M] [ChartedSpace H M]
  [NormedAddCommGroup X] [NormedSpace 𝕜 X] [TopologicalSpace H₀] [TopologicalSpace N]
  [ChartedSpace H₀ N]

variable (I : ModelWithCorners 𝕜 E H) (J : ModelWithCorners 𝕜 F H')
  (e : H ≃ₜ H') (L : E ≃L[𝕜] F)
  (hcompat : ∀ y, J (e y) = L (I y))
  (I₀ : ModelWithCorners 𝕜 X H₀)

include hcompat in
theorem coe_extChartAt_chartedSpaceTransHomeomorph (x : M) :
    let _ := chartedSpaceTransHomeomorph (M := M) e
    ⇑(extChartAt J x) = L ∘ ⇑(extChartAt I x) := by
  let _ := chartedSpaceTransHomeomorph (M := M) e
  dsimp only []
  funext y
  rw [Function.comp_apply, extChartAt_coe, extChartAt_coe, Function.comp_apply,
    chartAt_transHomeomorph, OpenPartialHomeomorph.coe_trans, Function.comp_apply]
  exact hcompat _

include hcompat I₀ in
theorem writtenInExtChartAt_chartedSpaceTransHomeomorph (x : N) (f : N → M) :
    let _ := chartedSpaceTransHomeomorph (M := M) e
    writtenInExtChartAt I₀ J x f = L ∘ writtenInExtChartAt I₀ I x f := by
  let _ := chartedSpaceTransHomeomorph (M := M) e
  dsimp only []
  funext y
  rw [Function.comp_apply, writtenInExtChartAt, writtenInExtChartAt, Function.comp_apply,
    Function.comp_apply]
  rw [coe_extChartAt_chartedSpaceTransHomeomorph I J e L hcompat (f x), Function.comp_apply]
  rfl

include hcompat I₀ in
theorem contMDiffWithinAt_chartedSpaceTransHomeomorph_iff {n : ℕ∞ω} {f : N → M}
    {s : Set N} {x : N} :
    let _ := chartedSpaceTransHomeomorph (M := M) e
    ContMDiffWithinAt I₀ J n f s x ↔ ContMDiffWithinAt I₀ I n f s x := by
  let _ := chartedSpaceTransHomeomorph (M := M) e
  dsimp only []
  rw [contMDiffWithinAt_iff, contMDiffWithinAt_iff]
  refine and_congr_right fun _ => ?_
  rw [coe_extChartAt_chartedSpaceTransHomeomorph I J e L hcompat (f x), ← Function.comp_assoc]
  exact L.comp_contDiffWithinAt_iff

include hcompat I₀ in
theorem contMDiffAt_chartedSpaceTransHomeomorph_iff {n : ℕ∞ω} {f : N → M} {x : N} :
    let _ := chartedSpaceTransHomeomorph (M := M) e
    ContMDiffAt I₀ J n f x ↔ ContMDiffAt I₀ I n f x := by
  let _ := chartedSpaceTransHomeomorph (M := M) e
  dsimp only []
  exact contMDiffWithinAt_chartedSpaceTransHomeomorph_iff I J e L hcompat I₀

include hcompat I₀ in
theorem contMDiffOn_chartedSpaceTransHomeomorph_iff {n : ℕ∞ω} {f : N → M} {s : Set N} :
    let _ := chartedSpaceTransHomeomorph (M := M) e
    ContMDiffOn I₀ J n f s ↔ ContMDiffOn I₀ I n f s := by
  let _ := chartedSpaceTransHomeomorph (M := M) e
  dsimp only []
  refine ⟨fun h x hx => ?_, fun h x hx => ?_⟩
  · exact (contMDiffWithinAt_chartedSpaceTransHomeomorph_iff I J e L hcompat I₀ (f := f) (s := s)
      (x := x)).mp (h x hx)
  · exact (contMDiffWithinAt_chartedSpaceTransHomeomorph_iff I J e L hcompat I₀ (f := f) (s := s)
      (x := x)).mpr (h x hx)

include hcompat I₀ in
theorem contMDiff_chartedSpaceTransHomeomorph_iff {n : ℕ∞ω} {f : N → M} :
    let _ := chartedSpaceTransHomeomorph (M := M) e
    ContMDiff I₀ J n f ↔ ContMDiff I₀ I n f := by
  let _ := chartedSpaceTransHomeomorph (M := M) e
  dsimp only []
  refine ⟨fun h x => ?_, fun h x => ?_⟩
  · exact (contMDiffAt_chartedSpaceTransHomeomorph_iff I J e L hcompat I₀ (f := f) (x := x)).mp (h x)
  · exact (contMDiffAt_chartedSpaceTransHomeomorph_iff I J e L hcompat I₀ (f := f) (x := x)).mpr (h x)

include hcompat I₀ in
theorem mdifferentiableAt_chartedSpaceTransHomeomorph_iff {f : N → M} {x : N} :
    let _ := chartedSpaceTransHomeomorph (M := M) e
    MDifferentiableAt I₀ J f x ↔ MDifferentiableAt I₀ I f x := by
  let _ := chartedSpaceTransHomeomorph (M := M) e
  dsimp only []
  rw [mdifferentiableAt_iff f x, mdifferentiableAt_iff f x]
  refine and_congr_right fun _ => ?_
  rw [writtenInExtChartAt_chartedSpaceTransHomeomorph I J e L hcompat I₀ x f]
  exact L.comp_differentiableWithinAt_iff

include hcompat I₀ in
theorem hasMFDerivAt_chartedSpaceTransHomeomorph_iff {f : N → M} {x : N}
    {f' : TangentSpace I₀ x →L[𝕜] E} :
    let _ := chartedSpaceTransHomeomorph (M := M) e
    HasMFDerivAt I₀ J f x (L.toContinuousLinearMap.comp f') ↔ HasMFDerivAt I₀ I f x f' := by
  let _ := chartedSpaceTransHomeomorph (M := M) e
  dsimp only []
  unfold HasMFDerivAt
  refine and_congr_right fun _ => ?_
  rw [writtenInExtChartAt_chartedSpaceTransHomeomorph I J e L hcompat I₀ x f]
  exact L.comp_hasFDerivWithinAt_iff

include hcompat I₀ in
theorem mfderiv_chartedSpaceTransHomeomorph {f : N → M} {x : N} :
    let _ := chartedSpaceTransHomeomorph (M := M) e
    mfderiv I₀ J f x = L.toContinuousLinearMap.comp (mfderiv I₀ I f x) := by
  let _ := chartedSpaceTransHomeomorph (M := M) e
  dsimp only []
  by_cases h : MDifferentiableAt I₀ I f x
  · have h' : MDifferentiableAt I₀ J f x :=
      (mdifferentiableAt_chartedSpaceTransHomeomorph_iff I J e L hcompat I₀).mpr h
    exact ((hasMFDerivAt_chartedSpaceTransHomeomorph_iff I J e L hcompat I₀
      (f := f) (x := x) (f' := mfderiv I₀ I f x)).mpr h.hasMFDerivAt).mfderiv
  · have h' : ¬ MDifferentiableAt I₀ J f x := fun hh =>
      h ((mdifferentiableAt_chartedSpaceTransHomeomorph_iff I J e L hcompat I₀).mp hh)
    rw [mfderiv_zero_of_not_mdifferentiableAt h', mfderiv_zero_of_not_mdifferentiableAt h]
    exact (ContinuousLinearMap.comp_zero L.toContinuousLinearMap).symm

include hcompat I₀ in
theorem bijective_mfderiv_chartedSpaceTransHomeomorph_iff {f : N → M} {x : N} :
    let _ := chartedSpaceTransHomeomorph (M := M) e
    Function.Bijective (mfderiv I₀ J f x) ↔ Function.Bijective (mfderiv I₀ I f x) := by
  let _ := chartedSpaceTransHomeomorph (M := M) e
  dsimp only []
  rw [mfderiv_chartedSpaceTransHomeomorph I J e L hcompat I₀]
  exact Function.Bijective.of_comp_iff' L.bijective (mfderiv I₀ I f x)

end DifferentialGeometry.Manifold
