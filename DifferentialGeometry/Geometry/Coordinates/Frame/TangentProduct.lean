import DifferentialGeometry.Geometry.Coordinates.Frame.Chart
import DifferentialGeometry.Topology.Manifold.ProductOrientation
import Mathlib.Geometry.Manifold.IsManifold.ExtChartAt
import Mathlib.LinearAlgebra.Basis.Prod

noncomputable section

set_option autoImplicit false

namespace DifferentialGeometry

open Bundle Manifold Set Module
open scoped Manifold ContDiff

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  {E' : Type*} [NormedAddCommGroup E'] [NormedSpace ℝ E']
  {H' : Type*} [TopologicalSpace H'] {J : ModelWithCorners ℝ E' H'}
  {N : Type*} [TopologicalSpace N] [ChartedSpace H' N] [IsManifold J ∞ N]
  [FiniteDimensional ℝ E] [FiniteDimensional ℝ E']

omit [FiniteDimensional ℝ E] [FiniteDimensional ℝ E'] in
private theorem tangentCoordChange_prod (p z : M × N)
    (hz : z ∈ (chartAt (ModelProd H H') p).source) :
    tangentCoordChange (I.prod J) z p z =
      (tangentCoordChange I z.1 p.1 z.1).prodMap
        (tangentCoordChange J z.2 p.2 z.2) := by
  have hz' : z.1 ∈ (chartAt H p.1).source ∧ z.2 ∈ (chartAt H' p.2).source := by
    simpa only [prodChartedSpace_chartAt, OpenPartialHomeomorph.prod_source, Set.mem_prod] using hz
  have hz₁ : z.1 ∈ (extChartAt I z.1).source ∩ (extChartAt I p.1).source :=
    ⟨mem_extChartAt_source .., by simpa only [extChartAt_source] using hz'.1⟩
  have hz₂ : z.2 ∈ (extChartAt J z.2).source ∩ (extChartAt J p.2).source :=
    ⟨mem_extChartAt_source .., by simpa only [extChartAt_source] using hz'.2⟩
  have hzp : z ∈ (extChartAt (I.prod J) z).source ∩ (extChartAt (I.prod J) p).source :=
    ⟨mem_extChartAt_source .., by simpa only [extChartAt_source] using hz⟩
  refine ((I.prod J).uniqueDiffWithinAt_image (x := (chartAt (ModelProd H H') z) z)).eq
    (hasFDerivWithinAt_tangentCoordChange (I := I.prod J) hzp) ?_
  have h₁ := hasFDerivWithinAt_tangentCoordChange (I := I) hz₁
  have h₂ := hasFDerivWithinAt_tangentCoordChange (I := J) hz₂
  have hs₁ : Prod.fst '' (Set.range (I.prod J)) = Set.range I := by
    rw [ModelWithCorners.range_prod]
    exact Set.fst_image_prod (Set.range I) ⟨J ((chartAt H' p.2) p.2), Set.mem_range_self _⟩
  have hs₂ : Prod.snd '' (Set.range (I.prod J)) = Set.range J := by
    rw [ModelWithCorners.range_prod]
    exact Set.snd_image_prod ⟨I ((chartAt H p.1) p.1), Set.mem_range_self _⟩ (Set.range J)
  rw [← hs₁] at h₁
  rw [← hs₂] at h₂
  have h := HasFDerivWithinAt.prodMap (p := (extChartAt I z.1 z.1, extChartAt J z.2 z.2)) h₁ h₂
  have hfun : ((extChartAt (I.prod J) p) ∘ (extChartAt (I.prod J) z).symm) =
      Prod.map ((extChartAt I p.1) ∘ (extChartAt I z.1).symm)
        ((extChartAt J p.2) ∘ (extChartAt J z.2).symm) := by
    funext q
    simp only [Function.comp_apply, extChartAt_prod, PartialEquiv.prod_symm, PartialEquiv.prod_coe]
    rfl
  have hpt : extChartAt (I.prod J) z z = (extChartAt I z.1 z.1, extChartAt J z.2 z.2) := by
    simp only [extChartAt_prod, PartialEquiv.prod_coe]
  rw [← hfun, ← hpt] at h
  exact h

omit [FiniteDimensional ℝ E] [FiniteDimensional ℝ E'] in
set_option backward.isDefEq.respectTransparency false in
private theorem tangentChartEquiv_prod (p z : M × N)
    (hz : z ∈ (trivializationAt (E × E') (TangentSpace (I.prod J)) p).baseSet)
    (h₁ : z.1 ∈ (trivializationAt E (TangentSpace I) p.1).baseSet)
    (h₂ : z.2 ∈ (trivializationAt E' (TangentSpace J) p.2).baseSet) :
    tangentChartEquiv (I.prod J) (M × N) p z hz =
      (tangentChartEquiv I M p.1 z.1 h₁).prodCongr (tangentChartEquiv J N p.2 z.2 h₂) := by
  have hzc : z ∈ (chartAt (ModelProd H H') p).source := by
    simpa only [TangentBundle.trivializationAt_baseSet] using hz
  have h₁c : z.1 ∈ (chartAt H p.1).source := h₁
  have h₂c : z.2 ∈ (chartAt H' p.2).source := h₂
  refine LinearEquiv.ext fun v => ?_
  change (Bundle.Trivialization.linearEquivAt ℝ
      (trivializationAt (E × E') (TangentSpace (I.prod J)) p) z hz) v =
    (Bundle.Trivialization.linearEquivAt ℝ (trivializationAt E (TangentSpace I) p.1) z.1 h₁ v.1,
      Bundle.Trivialization.linearEquivAt ℝ (trivializationAt E' (TangentSpace J) p.2) z.2 h₂
        v.2)
  simp only [Bundle.Trivialization.linearEquivAt_apply]
  rw [← Bundle.Trivialization.continuousLinearMapAt_apply_of_mem ℝ _ hz,
    ← Bundle.Trivialization.continuousLinearMapAt_apply_of_mem ℝ _ h₁,
    ← Bundle.Trivialization.continuousLinearMapAt_apply_of_mem ℝ _ h₂]
  rw [TangentBundle.continuousLinearMapAt_trivializationAt_eq_core hzc,
    TangentBundle.continuousLinearMapAt_trivializationAt_eq_core h₁c,
    TangentBundle.continuousLinearMapAt_trivializationAt_eq_core h₂c]
  exact congrArg (fun L => L v) (tangentCoordChange_prod (I := I) (J := J) p z hzc)

omit [FiniteDimensional ℝ E] [FiniteDimensional ℝ E'] in
set_option backward.isDefEq.respectTransparency false in
theorem trivializationAt_symmL_prod (p z : M × N)
    (hz : z ∈ (trivializationAt (E × E') (TangentSpace (I.prod J)) p).baseSet)
    (v : E × E') :
    (trivializationAt (E × E') (TangentSpace (I.prod J)) p).symmL ℝ z v =
      ((trivializationAt E (TangentSpace I) p.1).symmL ℝ z.1 v.1,
        (trivializationAt E' (TangentSpace J) p.2).symmL ℝ z.2 v.2) := by
  have hz' : z.1 ∈ (trivializationAt E (TangentSpace I) p.1).baseSet ∧
      z.2 ∈ (trivializationAt E' (TangentSpace J) p.2).baseSet := by
    have h := hz
    rw [TangentBundle.trivializationAt_baseSet, prodChartedSpace_chartAt,
      OpenPartialHomeomorph.prod_source] at h
    exact h
  have hL : (trivializationAt (E × E') (TangentSpace (I.prod J)) p).symmL ℝ z v =
      ((trivializationAt (E × E') (TangentSpace (I.prod J)) p).linearEquivAt ℝ z hz).symm v := by
    rw [Bundle.Trivialization.linearEquivAt_symm_apply (hb := hz),
      Bundle.Trivialization.symmL_apply (hb := hz)]
  have h₁ : (trivializationAt E (TangentSpace I) p.1).symmL ℝ z.1 v.1 =
      ((trivializationAt E (TangentSpace I) p.1).linearEquivAt ℝ z.1 hz'.1).symm v.1 := by
    rw [Bundle.Trivialization.linearEquivAt_symm_apply (hb := hz'.1),
      Bundle.Trivialization.symmL_apply (hb := hz'.1)]
  have h₂ : (trivializationAt E' (TangentSpace J) p.2).symmL ℝ z.2 v.2 =
      ((trivializationAt E' (TangentSpace J) p.2).linearEquivAt ℝ z.2 hz'.2).symm v.2 := by
    rw [Bundle.Trivialization.linearEquivAt_symm_apply (hb := hz'.2),
      Bundle.Trivialization.symmL_apply (hb := hz'.2)]
  rw [hL, h₁, h₂]
  change (tangentChartEquiv (I.prod J) (M × N) p z hz).symm v =
    ((tangentChartEquiv I M p.1 z.1 hz'.1).symm v.1,
      (tangentChartEquiv J N p.2 z.2 hz'.2).symm v.2)
  rw [tangentChartEquiv_prod (I := I) (J := J) p z hz hz'.1 hz'.2,
    LinearEquiv.prodCongr_symm]
  rfl

set_option backward.isDefEq.respectTransparency false in
theorem chartBasisVecFiber_prod (p z : M × N)
    (hz : z ∈ (trivializationAt (E × E') (TangentSpace (I.prod J)) p).baseSet)
    (i : Fin (Module.finrank ℝ (E × E'))) :
    Tensor.Coordinates.chartBasisVecFiber (I := I.prod J) p i z =
      ((trivializationAt E (TangentSpace I) p.1).symmL ℝ z.1
          ((Tensor.Coordinates.chartModelBasis (E × E') i).1),
        (trivializationAt E' (TangentSpace J) p.2).symmL ℝ z.2
          ((Tensor.Coordinates.chartModelBasis (E × E') i).2)) := by
  rw [Tensor.Coordinates.chartBasisVecFiber,
    trivializationAt_symmL_prod (I := I) (J := J) p z hz]

theorem chartBasisVecFiber_prod_eq_sum (p z : M × N)
    (hz : z ∈ (trivializationAt (E × E') (TangentSpace (I.prod J)) p).baseSet)
    (i : Fin (Module.finrank ℝ (E × E'))) :
    Tensor.Coordinates.chartBasisVecFiber (I := I.prod J) p i z =
      ((∑ j, (Tensor.Coordinates.chartModelBasis E).repr
            ((Tensor.Coordinates.chartModelBasis (E × E') i).1) j •
          Tensor.Coordinates.chartBasisVecFiber (I := I) p.1 j z.1),
        (∑ k, (Tensor.Coordinates.chartModelBasis E').repr
            ((Tensor.Coordinates.chartModelBasis (E × E') i).2) k •
          Tensor.Coordinates.chartBasisVecFiber (I := J) p.2 k z.2)) := by
  rw [chartBasisVecFiber_prod (I := I) (J := J) p z hz]
  congr 1
  · conv_lhs => rw [← Module.Basis.sum_repr (Tensor.Coordinates.chartModelBasis E)
      ((Tensor.Coordinates.chartModelBasis (E × E') i).1)]
    rw [map_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [map_smul]
    rfl
  · conv_lhs => rw [← Module.Basis.sum_repr (Tensor.Coordinates.chartModelBasis E')
      ((Tensor.Coordinates.chartModelBasis (E × E') i).2)]
    rw [map_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [map_smul]
    rfl

end DifferentialGeometry
