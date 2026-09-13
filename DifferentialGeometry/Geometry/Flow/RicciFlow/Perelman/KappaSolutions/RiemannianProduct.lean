import DifferentialGeometry.Geometry.Curvature.Metric.Defs
import DifferentialGeometry.Geometry.Curvature.Product
import DifferentialGeometry.Analysis.Integration.Measure.Riemannian.Invariance
import DifferentialGeometry.Analysis.Integration.Measure.Riemannian.Product
import DifferentialGeometry.Geometry.Coordinates.Frame.TangentProduct
import Mathlib.Geometry.Manifold.Instances.Real
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.LinearAlgebra.Matrix.Block
import Mathlib.MeasureTheory.Measure.Prod
import DifferentialGeometry.Analysis.Integration.Measure.Riemannian.Euclidean
import DifferentialGeometry.Analysis.Integration.Measure.Riemannian.Properties

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
private local instance upstreamRiemannianProductModelMeasurable : MeasurableSpace (E × ℝ) :=
  borel (E × ℝ)
private local instance upstreamRiemannianProductModelBorel : BorelSpace (E × ℝ) := ⟨rfl⟩

omit [T2Space M] in
private theorem riemannianMeasure_lintegral_eq_chartLocalMeasure_of_source
    (g : SmoothRiemannianMetric I M) (ρ : SmoothPartitionOfUnity M I M Set.univ)
    (hρ : ρ.IsSubordinate (fun α : M => (chartAt H α).source)) (α : M)
    {F : M → ENNReal} (hF : Measurable F)
    (hFs : ∀ x, x ∉ (chartAt H α).source → F x = 0) :
    (∫⁻ x, F x ∂(riemannianMeasure (I := I) g ρ)) =
      ∫⁻ x, F x ∂(chartLocalMeasure (I := I) g α) := by
  classical
  have hterm (β : M) :
      (∫⁻ x, ENNReal.ofReal (ρ β x) * F x ∂(chartLocalMeasure (I := I) g β)) =
        ∫⁻ x, ENNReal.ofReal (ρ β x) * F x ∂(chartLocalMeasure (I := I) g α) := by
    apply chartLocalMeasure_lintegral_eq_of_support_in_overlap (I := I) g β α
      (f := fun x => ENNReal.ofReal (ρ β x) * F x)
      ((measurable_ofReal_pou_weight (I := I) ρ β).mul hF)
    intro x hx
    by_cases hxβ : x ∈ (chartAt H β).source
    · rw [hFs x (fun hxα => hx ⟨hxβ, hxα⟩), mul_zero]
    · rw [image_eq_zero_of_notMem_tsupport (fun hxs => hxβ (hρ β hxs)),
        ENNReal.ofReal_zero, zero_mul]
  rw [riemannianMeasure_lintegral_eq (I := I) g ρ hF]
  set S : Set M := {β : M | (Function.support (ρ β)).Nonempty} with hSdef
  have hCS : S.Countable := (countable_nonempty_support_of_pou (I := I) ρ).to_subtype
  have hzero : ∀ β ∉ S,
      (∫⁻ x, ENNReal.ofReal (ρ β x) * F x ∂(chartLocalMeasure (I := I) g β)) = 0 := by
    intro β hβ
    have hρ0 : ∀ x, ρ β x = 0 := by
      intro x
      by_contra hne
      exact hβ ⟨x, hne⟩
    simp only [hρ0, ENNReal.ofReal_zero, zero_mul, lintegral_zero]
  rw [DifferentialGeometry.Integral.Measure.tsum_subtype_eq_of_support_subset (s := S)
    (f := fun β => ∫⁻ x, ENNReal.ofReal (ρ β x) * F x ∂(chartLocalMeasure (I := I) g β))
    (fun β hβ => by_contra fun h => hβ (hzero β h))]
  simp_rw [hterm]
  have hCSinst : Countable S := hCS.to_subtype
  rw [← lintegral_tsum (μ := chartLocalMeasure (I := I) g α)
    (f := fun (β : S) (x : M) => ENNReal.ofReal (ρ β.val x) * F x)
    (fun β : S => ((measurable_ofReal_pou_weight (I := I) ρ β.val).mul hF).aemeasurable
      (μ := chartLocalMeasure (I := I) g α))]
  refine lintegral_congr (fun x => ?_)
  rw [ENNReal.tsum_mul_right]
  rw [← DifferentialGeometry.Integral.Measure.tsum_subtype_eq_of_support_subset (s := S)
    (f := fun β => ENNReal.ofReal (ρ β x)) ?_]
  · rw [tsum_ofReal_pou_eq_one (I := I) ρ x, one_mul]
  · intro β hβ
    simp only [Function.mem_support, ne_eq, ENNReal.ofReal_eq_zero, not_le] at hβ
    exact ⟨x, ne_of_gt hβ⟩

private theorem riemannianVolumeMeasure_restrict_chartAt_source_eq_chartLocalMeasure_restrict
    (g : SmoothRiemannianMetric I M) (α : M) :
    (riemannianVolumeMeasure (I := I) (M := M) g).restrict (chartAt H α).source =
      (chartLocalMeasure (I := I) g α).restrict (chartAt H α).source := by
  refine Measure.ext_of_lintegral _ (fun F hF => ?_)
  rw [← lintegral_indicator (chartAt H α).open_source.measurableSet,
    ← lintegral_indicator (chartAt H α).open_source.measurableSet]
  exact riemannianMeasure_lintegral_eq_chartLocalMeasure_of_source (I := I) g
    (chartAtlasPOU I M) (chartAtlasPOU_isSubordinate I M) α
    (hF.indicator (chartAt H α).open_source.measurableSet)
    (fun x hx => Set.indicator_of_notMem (fun hxs => hx hxs) F)

private theorem cast_measure_restrict {X : Type*} {m₁ m₂ : MeasurableSpace X}
    (hm : m₁ = m₂) (μ : @Measure X m₁) (s : Set X) :
    (@Measure.restrict X m₂
        (cast (congrArg (fun m : MeasurableSpace X => @Measure X m) hm) μ) s)
      = cast (congrArg (fun m : MeasurableSpace X => @Measure X m) hm) (μ.restrict s) := by
  cases hm
  rfl

private theorem cast_measure_withDensity {X : Type*} {m₁ m₂ : MeasurableSpace X}
    (hm : m₁ = m₂) (μ : @Measure X m₁) (f : X → ENNReal) :
    (@Measure.withDensity X m₂
        (cast (congrArg (fun m : MeasurableSpace X => @Measure X m) hm) μ) f)
      = cast (congrArg (fun m : MeasurableSpace X => @Measure X m) hm)
          (@Measure.withDensity X m₁ μ f) := by
  cases hm
  rfl

private theorem cast_measure_map {X Y : Type*} {m₁ m₂ : MeasurableSpace X} {mY : MeasurableSpace Y}
    (hm : m₁ = m₂) (μ : @Measure X m₁) (f : X → Y) :
    @Measure.map X Y m₂ mY f (cast (congrArg (fun m : MeasurableSpace X => @Measure X m) hm) μ)
      = @Measure.map X Y m₁ mY f μ := by
  cases hm
  rfl

private theorem cast_map_codomain {X Y : Type*} {mX : MeasurableSpace X} {m₁ m₂ : MeasurableSpace Y}
    (hm : m₁ = m₂) (μ : @Measure X mX) (f : X → Y) :
    cast (congrArg (fun m : MeasurableSpace Y => @Measure Y m) hm)
        (@Measure.map X Y mX m₁ f μ)
      = @Measure.map X Y mX m₂ f μ := by
  cases hm
  rfl

private theorem prodMap_ae_eq {α β γ δ : Type*} [MeasurableSpace α] [MeasurableSpace β]
    {μ : Measure α} {ν : Measure β} [SFinite ν] {f f' : α → γ} {g g' : β → δ}
    (hf : f =ᵐ[μ] f') (hg : g =ᵐ[ν] g') :
    Prod.map f g =ᵐ[μ.prod ν] Prod.map f' g' := by
  rw [Filter.EventuallyEq, ae_iff] at hf hg ⊢
  have hsub : {z : α × β | ¬Prod.map f g z = Prod.map f' g' z} ⊆
      {x | ¬f x = f' x} ×ˢ Set.univ ∪ Set.univ ×ˢ {y | ¬g y = g' y} := by
    rintro z hz
    by_cases h1 : f z.1 = f' z.1
    · exact Or.inr ⟨trivial, fun h2 => hz (Prod.ext h1 h2)⟩
    · exact Or.inl ⟨h1, trivial⟩
  apply measure_mono_null (μ := μ.prod ν) hsub
  refine le_antisymm ?_ zero_le
  calc (μ.prod ν) ({x | ¬f x = f' x} ×ˢ Set.univ ∪ Set.univ ×ˢ {y | ¬g y = g' y})
      ≤ (μ.prod ν) ({x | ¬f x = f' x} ×ˢ Set.univ) +
          (μ.prod ν) (Set.univ ×ˢ {y | ¬g y = g' y}) :=
        measure_union_le _ _
    _ = 0 := by rw [Measure.prod_prod, Measure.prod_prod, hf, hg, zero_mul, mul_zero, add_zero]

omit [SigmaCompactSpace M] in
private theorem chartLocalMeasure_prod_real_of_inner_eq
    (h : SmoothRiemannianMetric I M)
    (gP : SmoothRiemannianMetric (I.prod 𝓘(ℝ, ℝ)) (M × ℝ))
    (hproduct : ∀ (y : M) (s : ℝ) (v w : TangentSpace I y) (a c : ℝ),
      gP.inner (y, s) (v, a) (w, c) = h.inner y v w + a * c)
    (p : M × ℝ) :
    chartLocalMeasure (I := I.prod 𝓘(ℝ, ℝ)) gP p =
      cast (congrArg (fun m : MeasurableSpace (M × ℝ) => @Measure (M × ℝ) m)
        (BorelSpace.measurable_eq (α := M × ℝ)))
        ((chartLocalMeasure (I := I) h p.1).prod
          (chartLocalMeasure (I := 𝓘(ℝ, ℝ)) (euclideanMetric (E := ℝ)) p.2)) := by
  classical
  rw [chartLocalMeasure_def, chartLocalMeasure_def, chartLocalMeasure_def]
  set t₁ : Set E := (extChartAt I p.1).target with ht₁def
  set t₂ : Set ℝ := (extChartAt 𝓘(ℝ, ℝ) p.2).target with ht₂def
  have ht₁ : MeasurableSet t₁ := measurableSet_extChartAt_target (I := I) p.1
  have ht₂ : MeasurableSet t₂ := measurableSet_extChartAt_target (I := 𝓘(ℝ, ℝ)) p.2
  set d₁ : E → ENNReal :=
    fun x => ENNReal.ofReal (chartDensity (I := I) h p.1 (⇑(extChartAt I p.1).symm x)) with hd₁def
  set d₂ : ℝ → ENNReal :=
    fun y => ENNReal.ofReal (chartDensity (I := 𝓘(ℝ, ℝ)) (euclideanMetric (E := ℝ)) p.2
      (⇑(extChartAt 𝓘(ℝ, ℝ) p.2).symm y)) with hd₂def
  set Q : Measure E := ((modelHaar (E := E)).restrict t₁).withDensity d₁ with hQdef
  set Q₂ : Measure ℝ := ((modelHaar (E := ℝ)).restrict t₂).withDensity d₂ with hQ₂def
  set P := (modelHaar (E := E)).prod (modelHaar (E := ℝ)) with hPdef
  set Y :=
    ((modelHaar (E := E)).restrict t₁).prod ((modelHaar (E := ℝ)).restrict t₂) with hYdef
  set c : ℝ := ((Tensor.Coordinates.chartModelBasis E).prod
      (Tensor.Coordinates.chartModelBasis ℝ)).det
      ⇑((Tensor.Coordinates.chartModelBasis (E × ℝ)).reindex (finrankProdRealEquiv (E := E)))
    with hcdef
  have hc_ne : c ≠ 0 := by
    rw [hcdef, Module.Basis.det_apply]
    have h1 := Module.Basis.toMatrix_mul_toMatrix_flip
      ((Tensor.Coordinates.chartModelBasis E).prod (Tensor.Coordinates.chartModelBasis ℝ))
      ((Tensor.Coordinates.chartModelBasis (E × ℝ)).reindex (finrankProdRealEquiv (E := E)))
    have h2 := congrArg Matrix.det h1
    rw [Matrix.det_mul, Matrix.det_one] at h2
    exact left_ne_zero_of_mul_eq_one h2
  have hr0 : ENNReal.ofReal |c| ≠ 0 :=
    ENNReal.ofReal_ne_zero_iff.mpr (abs_pos.mpr hc_ne)
  have hrtop : ENNReal.ofReal |c| ≠ ⊤ := ENNReal.ofReal_ne_top
  have hd₁ : AEMeasurable d₁ ((modelHaar (E := E)).restrict t₁) := by
    rw [hd₁def, ht₁def]
    exact aemeasurable_chartDensity_symm_pullback (I := I) h p.1
  have hd₂ : AEMeasurable d₂ ((modelHaar (E := ℝ)).restrict t₂) := by
    rw [hd₂def, ht₂def]
    exact aemeasurable_chartDensity_symm_pullback (I := 𝓘(ℝ, ℝ)) (euclideanMetric (E := ℝ)) p.2
  have hpMeas : @Prod.instMeasurableSpace E ℝ (borel E) (borel ℝ) = borel (E × ℝ) :=
    @BorelSpace.measurable_eq (E × ℝ) _ (@Prod.instMeasurableSpace E ℝ (borel E) (borel ℝ))
      (Prod.borelSpace)
  have hhaar : modelHaar (E := E × ℝ) = (ENNReal.ofReal |c|)⁻¹ •
      cast (congrArg (fun m : MeasurableSpace (E × ℝ) => @Measure (E × ℝ) m) hpMeas) P := by
    conv_rhs => rw [hPdef, modelHaar_prod_real (E := E)]
    rw [← hcdef, ← smul_assoc, smul_eq_mul, ENNReal.inv_mul_cancel hr0 hrtop, one_smul]
  have hsymm_apply : ∀ w : E × ℝ,
      ⇑(extChartAt (I.prod 𝓘(ℝ, ℝ)) p).symm w =
        ((⇑(extChartAt I p.1).symm w.1, ⇑(extChartAt 𝓘(ℝ, ℝ) p.2).symm w.2) : M × ℝ) := by
    intro w
    rw [extChartAt_prod (I := I) (I' := 𝓘(ℝ, ℝ)) (x := p), PartialEquiv.prod_symm,
      PartialEquiv.prod_coe]
  have hsymm_fun : ⇑(extChartAt (I.prod 𝓘(ℝ, ℝ)) p).symm =
      Prod.map ⇑(extChartAt I p.1).symm ⇑(extChartAt 𝓘(ℝ, ℝ) p.2).symm := by
    funext w
    rw [hsymm_apply w]
    rfl
  have htarget : MeasurableSet (extChartAt (I.prod 𝓘(ℝ, ℝ)) p).target :=
    measurableSet_extChartAt_target (I := I.prod 𝓘(ℝ, ℝ)) p
  have htarget_eq : (extChartAt (I.prod 𝓘(ℝ, ℝ)) p).target = t₁ ×ˢ t₂ := by
    rw [extChartAt_prod (I := I) (I' := 𝓘(ℝ, ℝ)) (x := p), PartialEquiv.prod_target,
      ← ht₁def, ← ht₂def]
  have hmeas₁ : Measurable (t₁.piecewise (⇑(extChartAt I p.1).symm) (fun _ : E => p.1)) :=
    ContinuousOn.measurable_piecewise (continuousOn_extChartAt_symm (I := I) p.1)
      continuousOn_const ht₁
  have hmeas₂ : Measurable (t₂.piecewise (⇑(extChartAt 𝓘(ℝ, ℝ) p.2).symm) (fun _ : ℝ => p.2)) :=
    ContinuousOn.measurable_piecewise (continuousOn_extChartAt_symm (I := 𝓘(ℝ, ℝ)) p.2)
      continuousOn_const ht₂
  have hae₁ : t₁.piecewise (⇑(extChartAt I p.1).symm) (fun _ : E => p.1)
      =ᵐ[Q] ⇑(extChartAt I p.1).symm := by
    have hae : ∀ᵐ x ∂Q, x ∈ t₁ :=
      (MeasureTheory.withDensity_absolutelyContinuous _ d₁).ae_le (ae_restrict_mem ht₁)
    filter_upwards [hae] with x hx
    exact Set.piecewise_eq_of_mem _ _ _ hx
  have hae₂ : t₂.piecewise (⇑(extChartAt 𝓘(ℝ, ℝ) p.2).symm) (fun _ : ℝ => p.2)
      =ᵐ[Q₂] ⇑(extChartAt 𝓘(ℝ, ℝ) p.2).symm := by
    have hae : ∀ᵐ x ∂Q₂, x ∈ t₂ :=
      (MeasureTheory.withDensity_absolutelyContinuous _ d₂).ae_le (ae_restrict_mem ht₂)
    filter_upwards [hae] with x hx
    exact Set.piecewise_eq_of_mem _ _ _ hx
  have hdens : (fun w : E × ℝ => ENNReal.ofReal
        (chartDensity (I := I.prod 𝓘(ℝ, ℝ)) gP p
          (⇑(extChartAt (I.prod 𝓘(ℝ, ℝ)) p).symm w)))
      =ᵐ[(modelHaar (E := E × ℝ)).restrict (extChartAt (I.prod 𝓘(ℝ, ℝ)) p).target]
      (fun w : E × ℝ => ENNReal.ofReal |c| * (d₁ w.1 * d₂ w.2)) := by
    filter_upwards [ae_restrict_mem htarget] with w hw
    have hbase : (⇑(extChartAt I p.1).symm w.1, ⇑(extChartAt 𝓘(ℝ, ℝ) p.2).symm w.2) ∈
        (trivializationAt (E × ℝ) (TangentSpace (I.prod 𝓘(ℝ, ℝ))) p).baseSet := by
      rw [← hsymm_apply w]
      rw [TangentBundle.trivializationAt_baseSet,
        ← extChartAt_source_eq_chartAt_source (I := I.prod 𝓘(ℝ, ℝ))]
      exact (extChartAt (I.prod 𝓘(ℝ, ℝ)) p).map_target hw
    rw [hsymm_apply w]
    rw [chartDensity_prod_eq (E := E) h gP hproduct p _ hbase]
    dsimp only
    have hd1nn : (0 : ℝ) ≤ chartDensity (I := I) h p.1 (⇑(extChartAt I p.1).symm w.1) :=
      Real.sqrt_nonneg _
    have hd2nn : (0 : ℝ) ≤ chartDensity (I := 𝓘(ℝ, ℝ)) (euclideanMetric (E := ℝ)) p.2
        (⇑(extChartAt 𝓘(ℝ, ℝ) p.2).symm w.2) := Real.sqrt_nonneg _
    rw [← hcdef, ENNReal.ofReal_mul (mul_nonneg (abs_nonneg c) hd1nn),
      ENNReal.ofReal_mul (abs_nonneg c)]
    simp only [hd₁def, hd₂def]
    ring
  set X : Measure (E × ℝ) := ((modelHaar (E := E × ℝ)).restrict
      (extChartAt (I.prod 𝓘(ℝ, ℝ)) p).target).withDensity (fun w : E × ℝ => ENNReal.ofReal
        (chartDensity (I := I.prod 𝓘(ℝ, ℝ)) gP p
          (⇑(extChartAt (I.prod 𝓘(ℝ, ℝ)) p).symm w))) with hXdef
  set X' : Measure (E × ℝ) := ((modelHaar (E := E × ℝ)).restrict
      (extChartAt (I.prod 𝓘(ℝ, ℝ)) p).target).withDensity
      ((ENNReal.ofReal |c|) • (fun w : E × ℝ => d₁ w.1 * d₂ w.2)) with hX'def
  have hX : X = X' := by
    rw [hXdef, hX'def]
    exact MeasureTheory.withDensity_congr_ae hdens
  have hX₂ : X' = cast (congrArg (fun m : MeasurableSpace (E × ℝ) => @Measure (E × ℝ) m) hpMeas)
      (Y.withDensity (fun w : E × ℝ => d₁ w.1 * d₂ w.2)) := by
    rw [hX'def, hhaar, Measure.restrict_smul,
      cast_measure_restrict hpMeas P (extChartAt (I.prod 𝓘(ℝ, ℝ)) p).target,
      htarget_eq, ← Measure.prod_restrict, ← hYdef]
    rw [MeasureTheory.withDensity_smul_measure, MeasureTheory.withDensity_smul' _ _ hrtop,
      ← smul_assoc, smul_eq_mul, ENNReal.inv_mul_cancel hr0 hrtop, one_smul,
      cast_measure_withDensity hpMeas Y (fun w : E × ℝ => d₁ w.1 * d₂ w.2)]
  have hX₃ : Y.withDensity (fun w : E × ℝ => d₁ w.1 * d₂ w.2) = Q.prod Q₂ := by
    rw [hYdef, ← MeasureTheory.prod_withDensity₀ hd₁ hd₂, ← hQdef, ← hQ₂def]
  rw [hX, hX₂, hX₃]
  rw [cast_measure_map hpMeas (Q.prod Q₂) (⇑(extChartAt (I.prod 𝓘(ℝ, ℝ)) p).symm), hsymm_fun]
  rw [← cast_map_codomain (BorelSpace.measurable_eq (α := M × ℝ)) (Q.prod Q₂)
    (Prod.map ⇑(extChartAt I p.1).symm ⇑(extChartAt 𝓘(ℝ, ℝ) p.2).symm)]
  congr 1
  rw [← Measure.map_congr (prodMap_ae_eq hae₁ hae₂), ← Measure.map_prod_map Q Q₂ hmeas₁ hmeas₂,
    Measure.map_congr hae₁, Measure.map_congr hae₂]

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
  classical
  set ρ : SmoothPartitionOfUnity (M × ℝ) (I.prod 𝓘(ℝ, ℝ)) (M × ℝ) Set.univ :=
    chartAtlasPOU (I.prod 𝓘(ℝ, ℝ)) (M × ℝ) with hρ
  set S : Set (M × ℝ) := {α : M × ℝ | (Function.support (ρ α)).Nonempty} with hS
  have hCS : S.Countable :=
    (countable_nonempty_support_of_pou (I := I.prod 𝓘(ℝ, ℝ)) ρ).to_subtype
  have hcover : (⋃ α ∈ S, (chartAt (ModelProd H ℝ) α).source) = Set.univ := by
    refine Set.eq_univ_of_forall (fun x => ?_)
    obtain ⟨α, hα⟩ := ρ.exists_pos_of_mem (Set.mem_univ x)
    exact Set.mem_iUnion₂.mpr ⟨α, ⟨x, hα.ne'⟩,
      chartAtlasPOU_isSubordinate (I := I.prod 𝓘(ℝ, ℝ)) (M × ℝ) α
        (subset_tsupport (ρ α) hα.ne')⟩
  have hlocal : ∀ α : M × ℝ,
      (riemannianVolumeMeasure (I := I.prod 𝓘(ℝ, ℝ)) (M := M × ℝ) gP).restrict
          (chartAt (ModelProd H ℝ) α).source =
        (cast
          (congrArg (fun m : MeasurableSpace (M × ℝ) => @Measure (M × ℝ) m)
            (BorelSpace.measurable_eq (α := M × ℝ)))
          ((riemannianVolumeMeasure (I := I) (M := M) h).prod (volume : Measure ℝ))).restrict
          (chartAt (ModelProd H ℝ) α).source := by
    intro α
    have hU : (chartAt (ModelProd H ℝ) α).source =
        (chartAt H α.1).source ×ˢ (chartAt ℝ α.2).source := by
      rw [prodChartedSpace_chartAt, OpenPartialHomeomorph.prod_source]
    have hσM : SigmaFinite (riemannianVolumeMeasure (I := I) (M := M) h) :=
      riemannianVolumeMeasure_sigmaFinite (I := I) (M := M) h
    have hsfQ : SFinite (chartLocalMeasure (I := I) h α.1) := by
      rw [chartLocalMeasure_def]
      infer_instance
    have hsfQ₂ : SFinite (chartLocalMeasure (I := 𝓘(ℝ, ℝ)) (euclideanMetric (E := ℝ)) α.2) := by
      rw [chartLocalMeasure_euclideanMetric]
      infer_instance
    rw [riemannianVolumeMeasure_restrict_chartAt_source_eq_chartLocalMeasure_restrict
        (I := I.prod 𝓘(ℝ, ℝ)) gP α,
      cast_measure_restrict (BorelSpace.measurable_eq (α := M × ℝ))
        ((riemannianVolumeMeasure (I := I) (M := M) h).prod (volume : Measure ℝ))
        (chartAt (ModelProd H ℝ) α).source,
      hU, ← Measure.prod_restrict,
      riemannianVolumeMeasure_restrict_chartAt_source_eq_chartLocalMeasure_restrict (I := I) h α.1,
      ← chartLocalMeasure_euclideanMetric (E := ℝ) (x₀ := α.2),
      Measure.prod_restrict,
      ← cast_measure_restrict (BorelSpace.measurable_eq (α := M × ℝ))
        ((chartLocalMeasure (I := I) h α.1).prod
          (chartLocalMeasure (I := 𝓘(ℝ, ℝ)) (euclideanMetric (E := ℝ)) α.2))
        ((chartAt H α.1).source ×ˢ (chartAt ℝ α.2).source),
      ← hU,
      ← chartLocalMeasure_prod_real_of_inner_eq (E := E) h gP hproduct α]
  have hmain := (Measure.restrict_biUnion_congr (s := S)
      (t := fun α : M × ℝ => (chartAt (ModelProd H ℝ) α).source) hCS).mpr
    (fun α _ => hlocal α)
  rw [hcover, Measure.restrict_univ, Measure.restrict_univ] at hmain
  exact hmain

end Volume

end DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions

end
