import DifferentialGeometry.Geometry.Curvature.Metric.Defs
import DifferentialGeometry.Geometry.Curvature.Product
import DifferentialGeometry.Analysis.Integration.Measure.Riemannian.Invariance
import DifferentialGeometry.Analysis.Integration.Measure.Riemannian.Product
import DifferentialGeometry.Geometry.Coordinates.Frame.TangentProduct
import Mathlib.Geometry.Manifold.Instances.Real
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.LinearAlgebra.Matrix.Block
import Mathlib.MeasureTheory.Measure.Prod

noncomputable section

namespace DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions

open MeasureTheory
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Integral.Measure
open scoped Manifold ContDiff

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

section Curvature

variable [CompleteSpace E]
variable [I.Boundaryless] [T2Space M]

private local instance upstreamRiemannianProductC1 : IsManifold I 1 M :=
  IsManifold.of_le (n := ∞) (by decide)

set_option backward.isDefEq.respectTransparency false in
theorem metricRm04At_product_real_of_inner_eq
    (h : SmoothRiemannianMetric I M)
    (gP : SmoothRiemannianMetric (I.prod 𝓘(ℝ, ℝ)) (M × ℝ))
    (hproduct : ∀ (y : M) (s : ℝ) (v w : TangentSpace I y) (a c : ℝ),
      gP.inner (y, s) (v, a) (w, c) = h.inner y v w + a * c)
    (y : M) (s : ℝ) (v : Fin 4 → TangentSpace I y) (a : Fin 4 → ℝ) :
    metricRm04At (I := I.prod 𝓘(ℝ, ℝ)) gP (y, s) (fun i => (v i, a i)) =
      metricRm04At (I := I) h y v := by
  have heq : gP = h.prod (euclideanMetric (E := ℝ)) := by
    refine SmoothRiemannianMetric.ext_inner (I := I.prod 𝓘(ℝ, ℝ)) ?_
    intro x u w
    obtain ⟨y', s'⟩ := x
    rw [SmoothRiemannianMetric.prod_inner]
    change gP.inner (y', s') u w = h.inner y' u.1 w.1 + inner ℝ u.2 w.2
    have hu : u = ((u.1, u.2) : TangentSpace (I.prod 𝓘(ℝ, ℝ)) (y', s')) := rfl
    have hw : w = ((w.1, w.2) : TangentSpace (I.prod 𝓘(ℝ, ℝ)) (y', s')) := rfl
    rw [hu, hw]
    rw [hproduct y' s' u.1 w.1 u.2 w.2]
    simp [inner, mul_comm]
  rw [heq]
  rw [metricRm04At_productMetric_apply]
  rw [metricRm04At_eq_zero_of_finrank_le_one (I := 𝓘(ℝ, ℝ)) (euclideanMetric (E := ℝ))
    (by simp) s]
  simp

end Curvature

section Gram

open scoped Matrix

variable [T2Space M]

omit [FiniteDimensional ℝ E] [T2Space M] in
private lemma inner_sum_sum (g : SmoothRiemannianMetric I M) (x : M)
    {ι κ : Type*} [Fintype ι] [Fintype κ]
    (c : ι → ℝ) (d : κ → ℝ) (u : ι → TangentSpace I x) (v : κ → TangentSpace I x) :
    g.inner x (∑ i, c i • u i) (∑ j, d j • v j) =
      ∑ i, ∑ j, c i * d j * g.inner x (u i) (v j) := by
  rw [map_sum]
  simp only [_root_.sum_apply, map_sum, map_smul, _root_.smul_apply, smul_eq_mul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  rw [Finset.mul_sum]
  exact Finset.sum_congr rfl (fun j _ => by ring)

private noncomputable def prodChartGramCoeff (i : Fin (Module.finrank ℝ (E × ℝ))) :
    Fin (Module.finrank ℝ E) ⊕ Fin (Module.finrank ℝ ℝ) → ℝ :=
  fun r => Sum.elim
    (fun a => (Tensor.Coordinates.chartModelBasis E).repr ((Tensor.Coordinates.chartModelBasis (E × ℝ) i).1) a)
    (fun k => (Tensor.Coordinates.chartModelBasis ℝ).repr ((Tensor.Coordinates.chartModelBasis (E × ℝ) i).2) k) r

theorem chartGramMatrix_prod_eq
    (h : SmoothRiemannianMetric I M)
    (gP : SmoothRiemannianMetric (I.prod 𝓘(ℝ, ℝ)) (M × ℝ))
    (hproduct : ∀ (y : M) (s : ℝ) (v w : TangentSpace I y) (a c : ℝ),
      gP.inner (y, s) (v, a) (w, c) = h.inner y v w + a * c)
    (p z : M × ℝ)
    (hz : z ∈ (trivializationAt (E × ℝ) (TangentSpace (I.prod 𝓘(ℝ, ℝ))) p).baseSet)
    (i j : Fin (Module.finrank ℝ (E × ℝ))) :
    Tensor.Coordinates.chartGramMatrix (I := I.prod 𝓘(ℝ, ℝ)) gP p z i j =
      ∑ r, ∑ s, prodChartGramCoeff (E := E) i r * prodChartGramCoeff (E := E) j s *
        (Matrix.fromBlocks (Tensor.Coordinates.chartGramMatrix (I := I) h p.1 z.1)
          (0 : Matrix (Fin (Module.finrank ℝ E)) (Fin (Module.finrank ℝ ℝ)) ℝ)
          (0 : Matrix (Fin (Module.finrank ℝ ℝ)) (Fin (Module.finrank ℝ E)) ℝ)
          (Tensor.Coordinates.chartGramMatrix (I := 𝓘(ℝ, ℝ)) (euclideanMetric (E := ℝ)) p.2 z.2)) r s := by
  have heq : gP = h.prod (euclideanMetric (E := ℝ)) := by
    refine SmoothRiemannianMetric.ext_inner (I := I.prod 𝓘(ℝ, ℝ)) ?_
    intro x u w
    obtain ⟨y₀, s₀⟩ := x
    rw [SmoothRiemannianMetric.prod_inner]
    change gP.inner (y₀, s₀) u w = h.inner y₀ u.1 w.1 + inner ℝ u.2 w.2
    have hu : u = ((u.1, u.2) : TangentSpace (I.prod 𝓘(ℝ, ℝ)) (y₀, s₀)) := rfl
    have hw : w = ((w.1, w.2) : TangentSpace (I.prod 𝓘(ℝ, ℝ)) (y₀, s₀)) := rfl
    rw [hu, hw, hproduct y₀ s₀ u.1 w.1 u.2 w.2]
    simp [inner, mul_comm]
  obtain ⟨y, s⟩ := p
  obtain ⟨y', s'⟩ := z
  rw [heq, Tensor.Coordinates.chartGramMatrix_apply,
    DifferentialGeometry.chartBasisVecFiber_prod_eq_sum (I := I) (J := 𝓘(ℝ, ℝ))
      (y, s) (y', s') hz i,
    DifferentialGeometry.chartBasisVecFiber_prod_eq_sum (I := I) (J := 𝓘(ℝ, ℝ))
      (y, s) (y', s') hz j]
  refine (SmoothRiemannianMetric.prod_inner (I := I) (J := 𝓘(ℝ, ℝ))
    (g := h) (h := euclideanMetric (E := ℝ)) (x := (y', s')) _ _).trans ?_
  rw [inner_sum_sum (g := h) (x := y'),
    inner_sum_sum (g := euclideanMetric (E := ℝ)) (x := s')]
  simp only [Fintype.sum_sum_type, prodChartGramCoeff, Sum.elim_inl, Sum.elim_inr,
    Matrix.fromBlocks_apply₁₁, Matrix.fromBlocks_apply₁₂, Matrix.fromBlocks_apply₂₁,
    Matrix.fromBlocks_apply₂₂, Matrix.zero_apply, mul_zero, Finset.sum_const_zero, add_zero,
    zero_add, Tensor.Coordinates.chartGramMatrix_apply]

private theorem prodChartGramMatrix_reindex_eq
    (h : SmoothRiemannianMetric I M)
    (gP : SmoothRiemannianMetric (I.prod 𝓘(ℝ, ℝ)) (M × ℝ))
    (hproduct : ∀ (y : M) (s : ℝ) (v w : TangentSpace I y) (a c : ℝ),
      gP.inner (y, s) (v, a) (w, c) = h.inner y v w + a * c)
    (p z : M × ℝ)
    (hz : z ∈ (trivializationAt (E × ℝ) (TangentSpace (I.prod 𝓘(ℝ, ℝ))) p).baseSet) :
    (Tensor.Coordinates.chartGramMatrix (I := I.prod 𝓘(ℝ, ℝ)) gP p z).reindex
        (finrankProdRealEquiv (E := E)) (finrankProdRealEquiv (E := E)) =
      (Matrix.of fun i r => prodChartGramCoeff (E := E) i r).reindex
          (finrankProdRealEquiv (E := E)) (Equiv.refl _) *
        (Matrix.fromBlocks (Tensor.Coordinates.chartGramMatrix (I := I) h p.1 z.1)
          (0 : Matrix (Fin (Module.finrank ℝ E)) (Fin (Module.finrank ℝ ℝ)) ℝ)
          (0 : Matrix (Fin (Module.finrank ℝ ℝ)) (Fin (Module.finrank ℝ E)) ℝ)
          (Tensor.Coordinates.chartGramMatrix (I := 𝓘(ℝ, ℝ)) (euclideanMetric (E := ℝ)) p.2 z.2)) *
        ((Matrix.of fun i r => prodChartGramCoeff (E := E) i r).reindex
          (finrankProdRealEquiv (E := E)) (Equiv.refl _))ᵀ := by
  have hentry := chartGramMatrix_prod_eq (E := E) h gP hproduct p z hz
  ext r t
  simp only [Matrix.reindex_apply, Matrix.submatrix_apply, Matrix.transpose_apply,
    Matrix.of_apply, Matrix.mul_apply, Equiv.refl_symm, Equiv.refl_apply]
  rw [hentry]
  simp only [Finset.sum_mul]
  conv_rhs => rw [Finset.sum_comm]
  refine Finset.sum_congr rfl (fun a _ => Finset.sum_congr rfl (fun b _ => ?_))
  ring

private theorem prodChartGramCoeff_det_eq :
    ((Matrix.of fun i r => prodChartGramCoeff (E := E) i r).reindex
        (finrankProdRealEquiv (E := E)) (Equiv.refl _)).det =
      ((Tensor.Coordinates.chartModelBasis E).prod (Tensor.Coordinates.chartModelBasis ℝ)).det
        ((Tensor.Coordinates.chartModelBasis (E × ℝ)).reindex (finrankProdRealEquiv (E := E))) := by
  have hmat : ((Matrix.of fun i r => prodChartGramCoeff (E := E) i r).reindex
        (finrankProdRealEquiv (E := E)) (Equiv.refl _))ᵀ =
      ((Tensor.Coordinates.chartModelBasis E).prod (Tensor.Coordinates.chartModelBasis ℝ)).toMatrix
        ((Tensor.Coordinates.chartModelBasis (E × ℝ)).reindex (finrankProdRealEquiv (E := E))) := by
    ext r s
    cases r with
    | inl a =>
      simp only [Matrix.transpose_apply, Matrix.reindex_apply, Matrix.submatrix_apply,
        Matrix.of_apply, Equiv.refl_symm, Equiv.refl_apply, Module.Basis.toMatrix_apply,
        Module.Basis.reindex_apply, prodChartGramCoeff, Sum.elim_inl,
        Module.Basis.prod_repr_inl]
    | inr k =>
      simp only [Matrix.transpose_apply, Matrix.reindex_apply, Matrix.submatrix_apply,
        Matrix.of_apply, Equiv.refl_symm, Equiv.refl_apply, Module.Basis.toMatrix_apply,
        Module.Basis.reindex_apply, prodChartGramCoeff, Sum.elim_inr,
        Module.Basis.prod_repr_inr]
  rw [← Matrix.det_transpose, hmat, Module.Basis.det_apply]

private theorem prodChartGram_det_eq
    (h : SmoothRiemannianMetric I M)
    (gP : SmoothRiemannianMetric (I.prod 𝓘(ℝ, ℝ)) (M × ℝ))
    (hproduct : ∀ (y : M) (s : ℝ) (v w : TangentSpace I y) (a c : ℝ),
      gP.inner (y, s) (v, a) (w, c) = h.inner y v w + a * c)
    (p z : M × ℝ)
    (hz : z ∈ (trivializationAt (E × ℝ) (TangentSpace (I.prod 𝓘(ℝ, ℝ))) p).baseSet) :
    (Tensor.Coordinates.chartGramMatrix (I := I.prod 𝓘(ℝ, ℝ)) gP p z).det =
      ((Tensor.Coordinates.chartModelBasis E).prod (Tensor.Coordinates.chartModelBasis ℝ)).det
          ((Tensor.Coordinates.chartModelBasis (E × ℝ)).reindex (finrankProdRealEquiv (E := E))) ^ 2 *
        ((Tensor.Coordinates.chartGramMatrix (I := I) h p.1 z.1).det *
          (Tensor.Coordinates.chartGramMatrix (I := 𝓘(ℝ, ℝ)) (euclideanMetric (E := ℝ)) p.2 z.2).det) := by
  rw [← Matrix.det_reindex_self (finrankProdRealEquiv (E := E))
    (Tensor.Coordinates.chartGramMatrix (I := I.prod 𝓘(ℝ, ℝ)) gP p z),
    prodChartGramMatrix_reindex_eq (E := E) h gP hproduct p z hz,
    Matrix.det_mul, Matrix.det_mul, Matrix.det_transpose,
    Matrix.det_fromBlocks_zero₁₂, ← prodChartGramCoeff_det_eq (E := E)]
  ring

theorem chartDensity_prod_eq
    (h : SmoothRiemannianMetric I M)
    (gP : SmoothRiemannianMetric (I.prod 𝓘(ℝ, ℝ)) (M × ℝ))
    (hproduct : ∀ (y : M) (s : ℝ) (v w : TangentSpace I y) (a c : ℝ),
      gP.inner (y, s) (v, a) (w, c) = h.inner y v w + a * c)
    (p z : M × ℝ)
    (hz : z ∈ (trivializationAt (E × ℝ) (TangentSpace (I.prod 𝓘(ℝ, ℝ))) p).baseSet) :
    chartDensity (I := I.prod 𝓘(ℝ, ℝ)) gP p z =
      |((Tensor.Coordinates.chartModelBasis E).prod (Tensor.Coordinates.chartModelBasis ℝ)).det
          ((Tensor.Coordinates.chartModelBasis (E × ℝ)).reindex (finrankProdRealEquiv (E := E)))| *
        chartDensity (I := I) h p.1 z.1 *
        chartDensity (I := 𝓘(ℝ, ℝ)) (euclideanMetric (E := ℝ)) p.2 z.2 := by
  have hz1 : z.1 ∈ (trivializationAt E (TangentSpace I) p.1).baseSet := by
    have hmem := hz
    rw [TangentBundle.trivializationAt_baseSet, prodChartedSpace_chartAt,
      OpenPartialHomeomorph.prod_source] at hmem
    exact hmem.1
  have hHpos : 0 < (Tensor.Coordinates.chartGramMatrix (I := I) h p.1 z.1).det :=
    Tensor.Coordinates.chartGramMatrix_det_pos (I := I) h p.1 hz1
  rw [chartDensity, chartDensity, chartDensity,
    prodChartGram_det_eq (E := E) h gP hproduct p z hz,
    Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq_eq_abs, Real.sqrt_mul hHpos.le]
  ring


end Gram

section Volume

variable [T2Space M] [SigmaCompactSpace M]

private local instance upstreamRiemannianProductMeasurable : MeasurableSpace M := borel M
private local instance upstreamRiemannianProductBorel : BorelSpace M := ⟨rfl⟩

theorem riemannianVolumeMeasure_product_real_of_inner_eq
    (h : SmoothRiemannianMetric I M)
    (gP : SmoothRiemannianMetric (I.prod 𝓘(ℝ, ℝ)) (M × ℝ))
    (hproduct : ∀ (y : M) (s : ℝ) (v w : TangentSpace I y) (a c : ℝ),
      gP.inner (y, s) (v, a) (w, c) = h.inner y v w + a * c) :
    riemannianVolumeMeasure (I := I.prod 𝓘(ℝ, ℝ)) (M := M × ℝ) gP =
      cast
        (congrArg (fun m : MeasurableSpace (M × ℝ) => @Measure (M × ℝ) m)
          (BorelSpace.measurable_eq (α := M × ℝ)))
        ((riemannianVolumeMeasure (I := I) (M := M) h).prod
          (volume : Measure ℝ)) := by
  sorry

end Volume

end DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions

end
