import DifferentialGeometry.Topology.Manifold.InteriorChart
import DifferentialGeometry.Topology.Manifold.ImmersionDifferential
import DifferentialGeometry.Topology.Manifold.InverseFunction.ContDiffOn
import DifferentialGeometry.Topology.Manifold.LocalDiffeomorph.PartialDiffeomorph

set_option autoImplicit false
noncomputable section

open Set Manifold Filter Function
open scoped Manifold ContDiff Topology

namespace DifferentialGeometry.Topology.Manifold

variable {E F H H' S M : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
  [TopologicalSpace H] [TopologicalSpace H']
  {I : ModelWithCorners ℝ E H} {J : ModelWithCorners ℝ F H'} [J.Boundaryless]
  [TopologicalSpace S] [ChartedSpace H S] [IsManifold I ∞ S]
  [TopologicalSpace M] [ChartedSpace H' M] [IsManifold J ∞ M]

theorem isLocalDiffeomorphAt_of_isInteriorPoint_of_injective_mfderiv
    {f : S → M} (hf : ContMDiff I J ∞ f) {x : S} (hx : I.IsInteriorPoint x)
    (hdim : Module.finrank ℝ E = Module.finrank ℝ F)
    (hinj : Injective (mfderiv I J f x)) : IsLocalDiffeomorphAt I J ∞ f x := by
  let c := DifferentialGeometry.Manifold.interiorChart I ∞ x
  have hxc : x ∈ c.source :=
    (DifferentialGeometry.Manifold.mem_interiorChart_source_iff I ∞ x).mpr hx
  have hcx : c.symm (c x) = x := c.left_inv' hxc
  let g : E → M := f ∘ c.symm
  have hg : ContMDiffOn 𝓘(ℝ, E) J ∞ g c.target := hf.comp_contMDiffOn c.contMDiffOn_invFun
  have hcs := c.symm.isLocalDiffeomorphAt 𝓘(ℝ, E) I ∞ (c.map_source hxc)
  have hgD : Injective (mfderiv 𝓘(ℝ, E) J g (c x)) := by
    rw [show g = f ∘ c.symm from rfl,
      mfderiv_comp (c x) (hf.mdifferentiableAt (by simp)) (hcs.mdifferentiableAt (by simp)), hcx]
    exact hinj.comp (hcs.mfderivToContinuousLinearEquiv (by simp)).injective
  let D : E →L[ℝ] F := mfderiv 𝓘(ℝ, E) J g (c x)
  have hD : Injective D := hgD
  let A : E ≃L[ℝ] F := (D.toLinearMap.linearEquivOfInjective hD hdim).toContinuousLinearEquiv
  have hloc : IsLocalDiffeomorphAt 𝓘(ℝ, E) J ∞ g (c x) :=
    isLocalDiffeomorphAt_of_contMDiffOn_of_hasMFDerivAt_equiv g hg c.open_target
      (c x) (c.map_source hxc) A
      ((hg.contMDiffAt (c.open_target.mem_nhds (c.map_source hxc))).mdifferentiableAt
        (by simp)).hasMFDerivAt
  have hcomp := (c.isLocalDiffeomorphAt I 𝓘(ℝ, E) ∞ hxc).comp J M hloc
  apply DifferentialGeometry.IsLocalDiffeomorphAt.of_eventuallyEq (g := g ∘ c) _ hcomp
  filter_upwards [c.open_source.mem_nhds hxc] with y hy
  change f y = f (c.symm (c y))
  exact congrArg f (c.left_inv' hy).symm

theorem isLocalDiffeomorphAt_of_isInteriorPoint_of_isImmersion
    {f : S → M} (hf : IsImmersion I J ∞ f) {x : S} (hx : I.IsInteriorPoint x)
    (hdim : Module.finrank ℝ E = Module.finrank ℝ F) : IsLocalDiffeomorphAt I J ∞ f x :=
  isLocalDiffeomorphAt_of_isInteriorPoint_of_injective_mfderiv hf.contMDiff hx hdim
    ((hf.isImmersionAt x).mfderiv_injective (by simp))

variable {G H'' N : Type*} [NormedAddCommGroup G] [NormedSpace ℝ G] [FiniteDimensional ℝ G]
  [TopologicalSpace H''] {K : ModelWithCorners ℝ G H''} [K.Boundaryless]
  [TopologicalSpace N] [ChartedSpace H'' N] [IsManifold K ∞ N]

theorem exists_partialDiffeomorph_comp_eq_of_isInteriorPoint
    {f : S → M} {g : S → N} (hf : IsImmersion I J ∞ f) (hg : IsImmersion I K ∞ g)
    {x : S} (hx : I.IsInteriorPoint x)
    (hdimf : Module.finrank ℝ E = Module.finrank ℝ F)
    (hdimg : Module.finrank ℝ E = Module.finrank ℝ G) :
    ∃ (Φ : _root_.PartialDiffeomorph J K M N ∞) (U : Set S),
      IsOpen U ∧ x ∈ U ∧ f x ∈ Φ.source ∧
      ∀ y ∈ U, f y ∈ Φ.source ∧ Φ (f y) = g y := by
  obtain ⟨φ, hxφ, hφ⟩ := isLocalDiffeomorphAt_of_isInteriorPoint_of_isImmersion hf hx hdimf
  obtain ⟨ψ, hxψ, hψ⟩ := isLocalDiffeomorphAt_of_isInteriorPoint_of_isImmersion hg hx hdimg
  let Φ := φ.symm.trans ψ
  have hsource (y : S) (hy : y ∈ φ.source ∩ ψ.source) : f y ∈ Φ.source := by
    change f y ∈ φ.target ∧ φ.symm (f y) ∈ ψ.source
    have hleft : φ.symm (φ y) = y := φ.left_inv' hy.1
    rw [hφ hy.1, hleft]
    exact ⟨φ.map_source hy.1, hy.2⟩
  refine ⟨Φ, φ.source ∩ ψ.source, φ.open_source.inter ψ.open_source,
    ⟨hxφ, hxψ⟩, hsource x ⟨hxφ, hxψ⟩, ?_⟩
  intro y hy
  refine ⟨hsource y hy, ?_⟩
  change ψ (φ.symm (f y)) = g y
  have hleft : φ.symm (φ y) = y := φ.left_inv' hy.1
  rw [hφ hy.1, hleft, ← hψ hy.2]

end DifferentialGeometry.Topology.Manifold
