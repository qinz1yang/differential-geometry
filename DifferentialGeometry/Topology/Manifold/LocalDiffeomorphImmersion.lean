import Mathlib.Geometry.Manifold.LocalDiffeomorph
import Mathlib.Geometry.Manifold.SmoothEmbedding
import DifferentialGeometry.Topology.Manifold.OpenEmbedding

set_option autoImplicit false

noncomputable section

open Set Function TopologicalSpace Manifold IsManifold
open scoped Manifold ContDiff Topology

namespace DifferentialGeometry.Topology.Manifold

variable {E F H H' M N : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]
  [TopologicalSpace H] [TopologicalSpace H']
  {I : ModelWithCorners ℝ E H} {J : ModelWithCorners ℝ F H'}
  [TopologicalSpace M] [ChartedSpace H M]
  [TopologicalSpace N] [ChartedSpace H' N]

private def extendedChartPartialDiffeomorph [I.Boundaryless] [IsManifold I ∞ M] (x : M) :
    PartialDiffeomorph I 𝓘(ℝ, E) M E ∞ where
  toPartialEquiv := extChartAt I x
  open_source := isOpen_extChartAt_source x
  open_target := isOpen_extChartAt_target x
  contMDiffOn_toFun := by
    simpa only [extChartAt_source] using contMDiffOn_extChartAt (I := I) (x := x)
  contMDiffOn_invFun := contMDiffOn_extChartAt_symm x

private def boundarylessModelInverse [I.Boundaryless] :
    PartialDiffeomorph 𝓘(ℝ, E) I E H ∞ where
  toPartialEquiv := I.toHomeomorph.symm.toPartialEquiv
  open_source := isOpen_univ
  open_target := isOpen_univ
  contMDiffOn_toFun := by
    change ContMDiffOn 𝓘(ℝ, E) I ∞ I.symm univ
    simpa only [I.range_eq_univ] using I.contMDiffOn_symm (n := ∞)
  contMDiffOn_invFun := I.contMDiff.contMDiffOn

private theorem isImmersionAtOfComplement_unit_of_isLocalDiffeomorphAt
    [I.Boundaryless] [J.Boundaryless] [IsManifold I ∞ M] [IsManifold J ∞ N]
    {f : M → N} {x : M} (hf : IsLocalDiffeomorphAt I J ∞ f x) :
    IsImmersionAtOfComplement PUnit.{1} I J ∞ f x := by
  classical
  let L : E ≃L[ℝ] F := hf.mfderivToContinuousLinearEquiv (by decide)
  obtain ⟨φ, hxφ, hφ⟩ := hf
  let α : OpenPartialHomeomorph M H := (chartAt H x).restr φ.source
  let β := extendedChartPartialDiffeomorph (I := I) x
  let ψD := ((φ.symm.trans β).trans L.toDiffeomorph.toPartialDiffeomorph).trans
    (boundarylessModelInverse (I := J))
  let ψ : OpenPartialHomeomorph N H' := ψD.toOpenPartialHomeomorph
  have hαsource : α.source = (chartAt H x).source ∩ φ.source :=
    (chartAt H x).restr_source' φ.source φ.open_source
  have hxα : x ∈ α.source := by
    rw [hαsource]
    exact ⟨mem_chart_source H x, hxφ⟩
  have hαmax : α ∈ IsManifold.maximalAtlas I ∞ M :=
    restr_mem_maximalAtlas (contDiffGroupoid ∞ I)
      (IsManifold.chart_mem_maximalAtlas x) φ.open_source
  have hψmax : ψ ∈ IsManifold.maximalAtlas J ∞ N :=
    ψ.mem_maximalAtlas_of_contMDiffOn ψD.contMDiffOn_toFun ψD.contMDiffOn_invFun
  have hψsource (y : M) (hy : y ∈ α.source) : f y ∈ ψ.source := by
    rw [hαsource] at hy
    change ((f y ∈ φ.target ∧ φ.symm (f y) ∈ (extChartAt I x).source) ∧ True) ∧ True
    refine ⟨⟨⟨?_, ?_⟩, trivial⟩, trivial⟩
    · rw [hφ hy.2]
      exact φ.map_source hy.2
    · have hleft : φ.symm.toPartialEquiv (φ.toPartialEquiv y) = y :=
        φ.toPartialEquiv.left_inv hy.2
      rw [hφ hy.2, hleft]
      simpa only [extChartAt_source] using hy.1
  have hψformula (y : M) (hy : y ∈ α.source) :
      (ψ.extend J) (f y) = L ((α.extend I) y) := by
    have hyφ : y ∈ φ.source := (hαsource ▸ hy).2
    have hleft : φ.symm.toPartialEquiv (φ.toPartialEquiv y) = y :=
      φ.toPartialEquiv.left_inv hyφ
    change J (J.symm (L ((extChartAt I x) (φ.symm (f y))))) = L ((α.extend I) y)
    rw [J.right_inv (by rw [J.range_eq_univ]; trivial), hφ hyφ, hleft]
    rfl
  refine IsImmersionAtOfComplement.mk_of_charts
    ((ContinuousLinearEquiv.prodUnique ℝ E PUnit.{1}).trans L) α ψ
    hxα (hψsource x hxα) hαmax hψmax hψsource ?_
  intro u hu
  let y := (α.extend I).symm u
  have hy : y ∈ α.source := by
    simpa only [OpenPartialHomeomorph.extend_source] using (α.extend I).map_target hu
  change (ψ.extend J) (f y) = L u
  rw [hψformula y hy]
  exact congrArg L ((α.extend I).right_inv hu)

theorem isImmersionAt_of_isLocalDiffeomorphAt
    [I.Boundaryless] [J.Boundaryless] [IsManifold I ∞ M] [IsManifold J ∞ N]
    {f : M → N} {x : M} (hf : IsLocalDiffeomorphAt I J ∞ f x) :
    IsImmersionAt I J ∞ f x :=
  (isImmersionAtOfComplement_unit_of_isLocalDiffeomorphAt hf).isImmersionAt

theorem isImmersion_of_isLocalDiffeomorph
    [I.Boundaryless] [J.Boundaryless] [IsManifold I ∞ M] [IsManifold J ∞ N]
    {f : M → N} (hf : IsLocalDiffeomorph I J ∞ f) : IsImmersion I J ∞ f :=
  IsImmersionOfComplement.isImmersion fun x =>
    isImmersionAtOfComplement_unit_of_isLocalDiffeomorphAt (hf x)

theorem isSmoothEmbedding_of_isLocalDiffeomorph_of_injective
    [I.Boundaryless] [J.Boundaryless] [IsManifold I ∞ M] [IsManifold J ∞ N]
    {f : M → N} (hf : IsLocalDiffeomorph I J ∞ f) (hinj : Injective f) :
    IsSmoothEmbedding I J ∞ f :=
  ⟨isImmersion_of_isLocalDiffeomorph hf,
    (hf.isLocalHomeomorph.isOpenEmbedding_of_injective hinj).isEmbedding⟩

theorem isSmoothEmbedding_of_injective_mfderiv
    [FiniteDimensional ℝ E] [FiniteDimensional ℝ F] [I.Boundaryless] [J.Boundaryless]
    [IsManifold I ∞ M] [IsManifold J ∞ N]
    {f : M → N} (hf : ContMDiff I J ∞ f) (hinj : Injective f)
    (himm : ∀ x, Injective (mfderiv I J f x))
    (hdim : Module.finrank ℝ E = Module.finrank ℝ F) : IsSmoothEmbedding I J ∞ f := by
  have hloc := isLocalDiffeomorph_of_injective_mfderiv f hf himm hdim
  exact ⟨isImmersion_of_isLocalDiffeomorph hloc,
    (hloc.isLocalHomeomorph.isOpenEmbedding_of_injective hinj).isEmbedding⟩

end DifferentialGeometry.Topology.Manifold
