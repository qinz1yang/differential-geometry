import Mathlib.Geometry.Manifold.LocalDiffeomorph
import Mathlib.Geometry.Manifold.SmoothEmbedding

set_option autoImplicit false

noncomputable section

namespace DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions

open Function Manifold Set
open scoped ContDiff Manifold _root_.Topology

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

private def neckExtendedChartDiffeomorph (x : M) :
    PartialDiffeomorph I 𝓘(ℝ, E) M E ∞ where
  toPartialEquiv := extChartAt I x
  open_source := isOpen_extChartAt_source x
  open_target := isOpen_extChartAt_target x
  contMDiffOn_toFun := by
    simpa only [extChartAt_source] using contMDiffOn_extChartAt (I := I) (x := x)
  contMDiffOn_invFun := contMDiffOn_extChartAt_symm x

private def neckBoundarylessModelInverse : PartialDiffeomorph 𝓘(ℝ, E) I E H ∞ where
  toPartialEquiv := I.toHomeomorph.symm.toPartialEquiv
  open_source := isOpen_univ
  open_target := isOpen_univ
  contMDiffOn_toFun := by
    change ContMDiffOn 𝓘(ℝ, E) I ∞ I.symm univ
    simpa only [I.range_eq_univ] using I.contMDiffOn_symm (n := ∞)
  contMDiffOn_invFun := I.contMDiff.contMDiffOn

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
  {G : Type*} [TopologicalSpace G] {J : ModelWithCorners ℝ F G} [J.Boundaryless]
  {N : Type*} [TopologicalSpace N] [ChartedSpace G N] [IsManifold J ∞ N]

theorem localDiffeomorphAt_isImmersionAtOfComplement {f : M → N} {x : M}
    (hf : IsLocalDiffeomorphAt I J ∞ f x) :
    IsImmersionAtOfComplement PUnit.{1} I J ∞ f x := by
  classical
  let L : E ≃L[ℝ] F := hf.mfderivToContinuousLinearEquiv (by decide)
  obtain ⟨φ, hxφ, hφ⟩ := hf
  let α : OpenPartialHomeomorph M H := (chartAt H x).restr φ.source
  let β := neckExtendedChartDiffeomorph (I := I) x
  let ψD := ((φ.symm.trans β).trans L.toDiffeomorph.toPartialDiffeomorph).trans
    (neckBoundarylessModelInverse (I := J))
  let ψ : OpenPartialHomeomorph N G := ψD.toOpenPartialHomeomorph
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
    rw [J.right_inv (by rw [J.range_eq_univ]; trivial), hφ hyφ,
      hleft]
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

theorem localDiffeomorph_isSmoothEmbedding_of_injective {f : M → N}
    (hf : IsLocalDiffeomorph I J ∞ f) (hinj : Injective f) :
    IsSmoothEmbedding I J ∞ f := by
  have himm : IsImmersionOfComplement PUnit.{1} I J ∞ f :=
    fun x => localDiffeomorphAt_isImmersionAtOfComplement (hf x)
  exact ⟨himm.isImmersion,
    (hf.isLocalHomeomorph.isOpenEmbedding_of_injective hinj).isEmbedding⟩

theorem diffeomorph_isSmoothEmbedding (f : M ≃ₘ⟮I, J⟯ N) :
    IsSmoothEmbedding I J ∞ f :=
  localDiffeomorph_isSmoothEmbedding_of_injective f.isLocalDiffeomorph f.injective

end DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions

end
