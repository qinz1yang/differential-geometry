import DifferentialGeometry.Geometry.HarmonicMap.ComplexGradientEquation
import DifferentialGeometry.Geometry.MinimalSurface.Plateau.DiskDifferential

set_option autoImplicit false

noncomputable section

open Set Manifold Bundle
open DifferentialGeometry.Tensor.Coordinates
open scoped ContDiff Manifold

namespace DifferentialGeometry.Geometry

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {M : Type*} [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]

theorem chartComplexGradient_isotropic
    (g : SmoothRiemannianMetric 𝓘(ℝ, E) M) {U : ℂ → M} {z : ℂ}
    (hU : ContMDiffAt 𝓘(ℝ, ℂ) 𝓘(ℝ, E) 1 U z) {p : M}
    (hsrc : U z ∈ (chartAt E p).source) (hconformal : DiskMapConformalAt g U z) :
    (∑ i, ∑ j, (chartGramMatrix g p (U z) i j : ℂ) *
      chartComplexGradient p U i z * chartComplexGradient p U j z) = 0 := by
  classical
  let X : ℂ → E := extChartAt 𝓘(ℝ, E) p ∘ U
  let T := trivializationAt E (TangentSpace 𝓘(ℝ, E)) p
  have hb : U z ∈ T.baseSet := by
    simpa only [T, TangentBundle.trivializationAt_baseSet] using hsrc
  have hchart := contMDiffAt_extChartAt' (I := 𝓘(ℝ, E)) (n := 1) hsrc
  have hX : ContDiffAt ℝ 1 X z := (hchart.comp z hU).contDiffAt
  have hcoord (k : Fin (Module.finrank ℝ E)) (v : ℂ) :
      fderiv ℝ (fun q => chartCoordCLM E k (X q)) z v =
        chartCoordCLM E k (fderiv ℝ X z v) := by
    have h := congrArg (fun L : ℂ →L[ℝ] ℝ => L v)
      ((chartCoordCLM E k).hasFDerivAt.comp z
        (hX.differentiableAt (by norm_num)).hasFDerivAt).fderiv
    simpa only [Function.comp_def, ContinuousLinearMap.comp_apply] using h
  have hchain (v : ℂ) :
      T.continuousLinearMapAt ℝ (U z) (diskMapPartial U z v) = fderiv ℝ X z v := by
    have h : (T.continuousLinearMapAt ℝ (U z)).comp
        (mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, E) U z) = fderiv ℝ X z := by
      dsimp only [T]
      rw [TangentBundle.continuousLinearMapAt_trivializationAt hsrc]
      exact (mfderiv_comp (I := 𝓘(ℝ, ℂ)) (I' := 𝓘(ℝ, E))
        (I'' := 𝓘(ℝ, E)) z (hchart.mdifferentiableAt (by norm_num))
        (hU.mdifferentiableAt (by norm_num))).symm.trans mfderiv_eq_fderiv
    exact congrArg (fun L => L v) h
  have hrepresent (v : ℂ) :
      (∑ k, chartCoordCLM E k (fderiv ℝ X z v) •
        chartBasisVecFiber (I := 𝓘(ℝ, E)) p k (U z)) = diskMapPartial U z v := by
    calc
      _ = T.symmL ℝ (U z)
          (∑ k, chartCoordCLM E k (fderiv ℝ X z v) • chartModelBasis E k) := by
        simp only [map_sum, map_smul, chartBasisVecFiber, T]
      _ = T.symmL ℝ (U z) (fderiv ℝ X z v) := by
        simp only [chartCoordCLM_apply, (chartModelBasis E).sum_equivFun]
      _ = T.symmL ℝ (U z)
          (T.continuousLinearMapAt ℝ (U z) (diskMapPartial U z v)) := by rw [hchain]
      _ = diskMapPartial U z v := T.symmL_continuousLinearMapAt hb _
  have hmetric (v w : ℂ) :
      (∑ i, ∑ j, chartGramMatrix g p (U z) i j *
        chartCoordCLM E i (fderiv ℝ X z v) * chartCoordCLM E j (fderiv ℝ X z w)) =
          g.inner (U z) (diskMapPartial U z v) (diskMapPartial U z w) := by
    calc
      _ = g.inner (U z)
          (∑ i, chartCoordCLM E i (fderiv ℝ X z v) •
            chartBasisVecFiber (I := 𝓘(ℝ, E)) p i (U z))
          (∑ j, chartCoordCLM E j (fderiv ℝ X z w) •
            chartBasisVecFiber (I := 𝓘(ℝ, E)) p j (U z)) := by
        simp only [chartGramMatrix_apply, map_sum, map_smul, sum_apply, smul_apply,
          smul_eq_mul, Finset.mul_sum]
        conv_rhs => rw [Finset.sum_comm]
        apply Finset.sum_congr rfl
        intro i _
        apply Finset.sum_congr rfl
        intro j _
        ring
      _ = _ := by rw [hrepresent, hrepresent]
  let a (i : Fin (Module.finrank ℝ E)) : ℝ := chartCoordCLM E i (fderiv ℝ X z 1)
  let b (i : Fin (Module.finrank ℝ E)) : ℝ := chartCoordCLM E i (fderiv ℝ X z Complex.I)
  let G (i j : Fin (Module.finrank ℝ E)) : ℝ := chartGramMatrix g p (U z) i j
  have hgrad (i : Fin (Module.finrank ℝ E)) :
      chartComplexGradient p U i z = (⟨a i / 2, -b i / 2⟩ : ℂ) := by
    change (⟨fderiv ℝ (fun q => chartCoordCLM E i (X q)) z 1 / 2,
      -fderiv ℝ (fun q => chartCoordCLM E i (X q)) z Complex.I / 2⟩ : ℂ) = _
    rw [hcoord, hcoord]
  have hequal : (∑ i, ∑ j, G i j * a i * a j) = ∑ i, ∑ j, G i j * b i * b j := by
    dsimp only [G, a, b]
    rw [hmetric, hmetric]
    exact hconformal.2
  have hab : (∑ i, ∑ j, G i j * a i * b j) = 0 := by
    dsimp only [G, a, b]
    rw [hmetric]
    exact hconformal.1
  have hba : (∑ i, ∑ j, G i j * b i * a j) = 0 := by
    dsimp only [G, a, b]
    rw [hmetric, g.symm]
    exact hconformal.1
  have hre (i j : Fin (Module.finrank ℝ E)) :
      ((G i j : ℂ) * (⟨a i / 2, -b i / 2⟩ : ℂ) *
        (⟨a j / 2, -b j / 2⟩ : ℂ)).re =
          (G i j * a i * a j - G i j * b i * b j) / 4 := by
    simp
    ring
  have him (i j : Fin (Module.finrank ℝ E)) :
      ((G i j : ℂ) * (⟨a i / 2, -b i / 2⟩ : ℂ) *
        (⟨a j / 2, -b j / 2⟩ : ℂ)).im =
          -(G i j * a i * b j + G i j * b i * a j) / 4 := by
    simp
    ring
  simp only [hgrad]
  change (∑ i, ∑ j, (G i j : ℂ) * (⟨a i / 2, -b i / 2⟩ : ℂ) *
    (⟨a j / 2, -b j / 2⟩ : ℂ)) = 0
  apply Complex.ext
  · change Complex.reCLM _ = 0
    simp only [map_sum]
    change (∑ i, ∑ j, ((G i j : ℂ) * (⟨a i / 2, -b i / 2⟩ : ℂ) *
      (⟨a j / 2, -b j / 2⟩ : ℂ)).re) = 0
    simp_rw [hre]
    simp only [← Finset.sum_div, Finset.sum_sub_distrib, hequal, sub_self, zero_div]
  · change Complex.imCLM _ = 0
    simp only [map_sum]
    change (∑ i, ∑ j, ((G i j : ℂ) * (⟨a i / 2, -b i / 2⟩ : ℂ) *
      (⟨a j / 2, -b j / 2⟩ : ℂ)).im) = 0
    simp_rw [him]
    simp only [← Finset.sum_div, Finset.sum_neg_distrib, Finset.sum_add_distrib,
      hab, hba, add_zero, neg_zero, zero_div]

end DifferentialGeometry.Geometry
