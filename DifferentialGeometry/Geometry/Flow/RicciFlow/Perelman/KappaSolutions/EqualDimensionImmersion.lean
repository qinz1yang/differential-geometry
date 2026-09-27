import Mathlib.Geometry.Manifold.Immersion
import Mathlib.Geometry.Manifold.LocalDiffeomorph
import Mathlib.Geometry.Manifold.SmoothEmbedding
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.LinearAlgebra.FiniteDimensional.Basic

set_option autoImplicit false

noncomputable section

open Manifold Set
open scoped Manifold ContDiff _root_.Topology

namespace DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]
  {H G : Type*} [TopologicalSpace H] [TopologicalSpace G]
  {I : ModelWithCorners ℝ E H} {J : ModelWithCorners ℝ F G}
  {M N : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [TopologicalSpace N] [ChartedSpace G N]

private def smoothChartPartialDiffeomorph [I.Boundaryless]
    (φ : OpenPartialHomeomorph M H) (hφ : φ ∈ IsManifold.maximalAtlas I ∞ M) :
    PartialDiffeomorph I 𝓘(ℝ, E) M E ∞ where
  toPartialEquiv := φ.extend I
  open_source := φ.isOpen_extend_source
  open_target := φ.isOpen_extend_target
  contMDiffOn_toFun := by
    simpa only [OpenPartialHomeomorph.extend_source] using φ.contMDiffOn_extend hφ
  contMDiffOn_invFun := by
    have hsymm : ((φ.extend I).symm : E → M) = (φ.extend I).invFun := rfl
    rw [← hsymm]
    simpa only [OpenPartialHomeomorph.extend_target'] using contMDiffOn_extend_symm hφ

theorem immersionAt_isLocalDiffeomorphAt_of_finrank_eq
    [FiniteDimensional ℝ E] [FiniteDimensional ℝ F] [I.Boundaryless] [J.Boundaryless]
    (hdim : Module.finrank ℝ E = Module.finrank ℝ F)
    {f : M → N} {x : M} (hf : IsImmersionAt I J ∞ f x) :
    IsLocalDiffeomorphAt I J ∞ f x := by
  let h := hf.isImmersionAtOfComplement_complement
  have : FiniteDimensional ℝ hf.complement :=
    FiniteDimensional.of_injective
      (h.equiv.toLinearEquiv.toLinearMap.comp (LinearMap.inr ℝ E hf.complement))
      (h.equiv.injective.comp (LinearMap.inr_injective))
  have hzero : Module.finrank ℝ hf.complement = 0 := by
    have heq := h.equiv.toLinearEquiv.finrank_eq
    rw [Module.finrank_prod] at heq
    omega
  have : Subsingleton hf.complement := Module.finrank_zero_iff.mp hzero
  have : Unique hf.complement := ⟨⟨0⟩, fun _ => Subsingleton.elim _ _⟩
  let L : E ≃L[ℝ] F :=
    (ContinuousLinearEquiv.prodUnique ℝ E hf.complement).symm.trans h.equiv
  let d := smoothChartPartialDiffeomorph h.domChart h.domChart_mem_maximalAtlas
  let c := smoothChartPartialDiffeomorph h.codChart h.codChart_mem_maximalAtlas
  let Φ : PartialDiffeomorph I J M N ∞ :=
    (d.trans L.toDiffeomorph.toPartialDiffeomorph).trans c.symm
  have hdsource : d.source = h.domChart.source := by
    change (h.domChart.extend I).source = h.domChart.source
    exact OpenPartialHomeomorph.extend_source _
  have hcsource : c.source = h.codChart.source := by
    change (h.codChart.extend J).source = h.codChart.source
    exact OpenPartialHomeomorph.extend_source _
  have hchart (y : M) (hy : y ∈ h.domChart.source) : c (f y) = L (d y) := by
    have hyext : y ∈ (h.domChart.extend I).source := by
      rwa [OpenPartialHomeomorph.extend_source]
    have hc := h.writtenInCharts ((h.domChart.extend I).map_source hyext)
    dsimp only [Function.comp_apply] at hc
    rw [h.domChart.extend_left_inv hy] at hc
    have hdefault : (default : hf.complement) = 0 := Subsingleton.elim _ _
    change (h.codChart.extend J) (f y) = L ((h.domChart.extend I) y)
    simpa only [L, ContinuousLinearEquiv.trans_apply,
      ContinuousLinearEquiv.prodUnique_symm_apply, hdefault] using hc
  refine ⟨Φ, ?_, ?_⟩
  · have hxD : x ∈ d.source := by rw [hdsource]; exact h.mem_domChart_source
    refine ⟨⟨hxD, trivial⟩, ?_⟩
    change L (d x) ∈ c.target
    rw [← hchart x h.mem_domChart_source]
    exact c.toPartialEquiv.map_source (by rw [hcsource]; exact h.mem_codChart_source)
  · intro y hy
    have hyD : y ∈ d.source := hy.1.1
    have hy' : y ∈ h.domChart.source := by rwa [hdsource] at hyD
    change f y = c.symm (L (d y))
    rw [← hchart y hy']
    exact (c.toPartialEquiv.left_inv (by
      rw [hcsource]
      exact h.source_subset_preimage_source hy')).symm

theorem smoothEmbedding_isOpenEmbedding_of_finrank_eq
    [FiniteDimensional ℝ E] [FiniteDimensional ℝ F] [I.Boundaryless] [J.Boundaryless]
    (hdim : Module.finrank ℝ E = Module.finrank ℝ F)
    {f : M → N} (hf : IsSmoothEmbedding I J ∞ f) :
    Topology.IsOpenEmbedding f := by
  have hlocal : IsLocalDiffeomorph I J ∞ f := fun x =>
    immersionAt_isLocalDiffeomorphAt_of_finrank_eq hdim (hf.isImmersion.isImmersionAt x)
  exact hlocal.isLocalHomeomorph.isOpenEmbedding_of_injective hf.isEmbedding.injective

end DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions
