import DifferentialGeometry.Analysis.Elliptic.WithBoundary.DirichletSeparability
import Mathlib.Analysis.InnerProductSpace.GramSchmidtOrtho
import Mathlib.Order.Filter.AtTopBot.Finset

noncomputable section

open Bundle Manifold MeasureTheory Set Filter
open scoped Manifold Topology ContDiff ENNReal BigOperators
  RealInnerProductSpace InnerProductSpace

namespace DifferentialGeometry
namespace Analysis
namespace Laplacian
namespace WithBoundary
namespace Dirichlet

attribute [local instance] IsWellOrder.toHasWellFounded

variable {n : ℕ} [NeZero n]
variable {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanHalfSpace n) M]
  [IsManifold (modelWithCornersEuclideanHalfSpace n) ∞ M]

private abbrev I_half (n : ℕ) [NeZero n] :
    ModelWithCorners ℝ (EuclideanSpace ℝ (Fin n)) (EuclideanHalfSpace n) :=
  modelWithCornersEuclideanHalfSpace n

variable [T2Space M] [CompactSpace M]

open DifferentialGeometry.Integral.Measure

private local instance : MeasurableSpace M := borel M
private local instance : BorelSpace M := ⟨rfl⟩

private theorem exists_smoothDirichletH1DenseSeq
    (g : SmoothRiemannianMetric (I_half n) M) :
    ∃ φ : ℕ → SmoothScalarDirichlet g,
      DenseRange (fun i => smoothToH1ComplDirichlet g (φ i)) := by
  have hd := denseRange_smoothToH1ComplDirichlet g
  obtain ⟨t, htrange, htcount, htdense⟩ := hd.exists_countable_dense_subset
  obtain ⟨u, hu⟩ := htcount.exists_eq_range htdense.nonempty
  have hu_mem : ∀ i, u i ∈ t := by
    intro i
    rw [hu]
    exact Set.mem_range_self i
  have hpre : ∀ i, ∃ f : SmoothScalarDirichlet g,
      smoothToH1ComplDirichlet g f = u i := by
    intro i
    simpa only [Set.mem_range] using htrange (hu_mem i)
  choose φ hφ using hpre
  refine ⟨φ, ?_⟩
  rw [show (fun i => smoothToH1ComplDirichlet g (φ i)) = u by
    funext i
    exact hφ i]
  change Dense (Set.range u)
  rw [← hu]
  exact htdense

noncomputable def smoothDirichletH1DenseSeq
    (g : SmoothRiemannianMetric (I_half n) M) :
    ℕ → SmoothScalarDirichlet g :=
  Classical.choose (exists_smoothDirichletH1DenseSeq g)

theorem denseRange_smoothToH1ComplDirichlet_smoothDirichletH1DenseSeq
    (g : SmoothRiemannianMetric (I_half n) M) :
    DenseRange (fun i =>
      smoothToH1ComplDirichlet g (smoothDirichletH1DenseSeq g i)) :=
  Classical.choose_spec (exists_smoothDirichletH1DenseSeq g)

theorem denseRange_smoothToLpDirichlet_smoothDirichletH1DenseSeq
    (g : SmoothRiemannianMetric (I_half n) M) :
    DenseRange (fun i => smoothToLpDirichlet g (smoothDirichletH1DenseSeq g i)) := by
  rw [show (fun i => smoothToLpDirichlet g (smoothDirichletH1DenseSeq g i)) =
      (H1ComplDirichletToLp g) ∘ (fun i =>
        smoothToH1ComplDirichlet g (smoothDirichletH1DenseSeq g i)) by
    funext i
    exact (H1ComplDirichletToLp_smoothToH1ComplDirichlet g _).symm]
  exact (denseRange_H1ComplDirichletToLp g).comp
    (denseRange_smoothToH1ComplDirichlet_smoothDirichletH1DenseSeq g)
    (H1ComplDirichletToLp g).continuous

section OrderedFamily

variable {ι : Type*} [LinearOrder ι] [LocallyFiniteOrderBot ι] [WellFoundedLT ι]

noncomputable def smoothDirichletL2GramSchmidt
    {g : SmoothRiemannianMetric (I_half n) M}
    (φ : ι → SmoothScalarDirichlet g) (i : ι) : SmoothScalarDirichlet g :=
  φ i - ∑ j : Finset.Iio i,
    (⟪InnerProductSpace.gramSchmidt ℝ
          (fun k => smoothToLpDirichlet g (φ k)) j,
        smoothToLpDirichlet g (φ i)⟫_ℝ /
      (‖InnerProductSpace.gramSchmidt ℝ
          (fun k => smoothToLpDirichlet g (φ k)) j‖ : ℝ) ^ 2) •
        smoothDirichletL2GramSchmidt φ j
termination_by i
decreasing_by exact Finset.mem_Iio.mp j.2

theorem smoothToLpDirichlet_smoothDirichletL2GramSchmidt
    {g : SmoothRiemannianMetric (I_half n) M}
    (φ : ι → SmoothScalarDirichlet g) (i : ι) :
    smoothToLpDirichlet g (smoothDirichletL2GramSchmidt φ i) =
      InnerProductSpace.gramSchmidt ℝ
        (fun k => smoothToLpDirichlet g (φ k)) i := by
  apply wellFounded_lt.induction i
  intro i ih
  rw [smoothDirichletL2GramSchmidt]
  rw [map_sub, map_sum]
  have h := InnerProductSpace.gramSchmidt_def'' ℝ
    (fun k => smoothToLpDirichlet g (φ k)) i
  rw [← Finset.sum_attach, Finset.attach_eq_univ] at h
  rw [eq_sub_of_add_eq h.symm]
  congr 1
  apply Finset.sum_congr rfl
  intro j _
  rw [map_smul, ih j (Finset.mem_Iio.mp j.2)]
  rfl

noncomputable def smoothDirichletL2GramSchmidtNormed
    {g : SmoothRiemannianMetric (I_half n) M}
    (φ : ι → SmoothScalarDirichlet g) (i : ι) : SmoothScalarDirichlet g :=
  (‖InnerProductSpace.gramSchmidt ℝ
      (fun k => smoothToLpDirichlet g (φ k)) i‖ : ℝ)⁻¹ •
    smoothDirichletL2GramSchmidt φ i

theorem smoothToLpDirichlet_smoothDirichletL2GramSchmidtNormed
    {g : SmoothRiemannianMetric (I_half n) M}
    (φ : ι → SmoothScalarDirichlet g) (i : ι) :
    smoothToLpDirichlet g (smoothDirichletL2GramSchmidtNormed φ i) =
      InnerProductSpace.gramSchmidtNormed ℝ
        (fun k => smoothToLpDirichlet g (φ k)) i := by
  rw [smoothDirichletL2GramSchmidtNormed, map_smul,
    smoothToLpDirichlet_smoothDirichletL2GramSchmidt]
  rfl

theorem smoothDirichletL2GramSchmidtNormed_orthonormal
    {g : SmoothRiemannianMetric (I_half n) M}
    (φ : ι → SmoothScalarDirichlet g) :
    Orthonormal ℝ (fun i : {i : ι |
        InnerProductSpace.gramSchmidtNormed ℝ
          (fun k => smoothToLpDirichlet g (φ k)) i ≠ 0} =>
      smoothToLpDirichlet g (smoothDirichletL2GramSchmidtNormed φ i)) := by
  simpa only [smoothToLpDirichlet_smoothDirichletL2GramSchmidtNormed] using
    (InnerProductSpace.gramSchmidtNormed_orthonormal'
      (fun k => smoothToLpDirichlet g (φ k)))

theorem span_smoothToLpDirichlet_smoothDirichletL2GramSchmidtNormed
    {g : SmoothRiemannianMetric (I_half n) M}
    (φ : ι → SmoothScalarDirichlet g) :
    Submodule.span ℝ (Set.range (fun i =>
        smoothToLpDirichlet g (smoothDirichletL2GramSchmidtNormed φ i))) =
      Submodule.span ℝ (Set.range (fun i => smoothToLpDirichlet g (φ i))) := by
  simp_rw [smoothToLpDirichlet_smoothDirichletL2GramSchmidtNormed]
  exact (InnerProductSpace.span_gramSchmidtNormed_range
      (fun k => smoothToLpDirichlet g (φ k))).trans
    (InnerProductSpace.span_gramSchmidt ℝ
      (fun k => smoothToLpDirichlet g (φ k)))

private theorem span_smoothDirichletL2GramSchmidtNormed
    {g : SmoothRiemannianMetric (I_half n) M}
    (φ : ι → SmoothScalarDirichlet g) :
    Submodule.span ℝ (Set.range (smoothDirichletL2GramSchmidtNormed φ)) =
      Submodule.span ℝ (Set.range φ) := by
  apply (Submodule.map_injective_of_injective
    (f := (smoothToLpDirichlet g).toLinearMap)
    (smoothToLpDirichlet_injective g))
  rw [Submodule.map_span, Submodule.map_span, ← Set.range_comp', ← Set.range_comp']
  simpa only [ContinuousLinearMap.coe_coe, Function.comp_apply] using
    span_smoothToLpDirichlet_smoothDirichletL2GramSchmidtNormed φ

end OrderedFamily

abbrev SmoothDirichletBasisIndex
    (g : SmoothRiemannianMetric (I_half n) M) :=
  {i : ℕ | InnerProductSpace.gramSchmidtNormed ℝ
    (fun k => smoothToLpDirichlet g (smoothDirichletH1DenseSeq g k)) i ≠ 0}

noncomputable def smoothDirichletBasisFunction
    (g : SmoothRiemannianMetric (I_half n) M)
    (i : SmoothDirichletBasisIndex g) : SmoothScalarDirichlet g :=
  smoothDirichletL2GramSchmidtNormed (smoothDirichletH1DenseSeq g) i

theorem smoothDirichletBasisFunction_orthonormal
    (g : SmoothRiemannianMetric (I_half n) M) :
    Orthonormal ℝ (fun i =>
      smoothToLpDirichlet g (smoothDirichletBasisFunction g i)) := by
  simpa only [smoothDirichletBasisFunction] using
    smoothDirichletL2GramSchmidtNormed_orthonormal
      (smoothDirichletH1DenseSeq g)

private theorem span_smoothDirichletBasisFunction_eq
    (g : SmoothRiemannianMetric (I_half n) M) :
    Submodule.span ℝ (Set.range (fun i =>
        smoothToLpDirichlet g (smoothDirichletBasisFunction g i))) =
      Submodule.span ℝ (Set.range (fun i =>
        smoothToLpDirichlet g
          (smoothDirichletL2GramSchmidtNormed (smoothDirichletH1DenseSeq g) i))) := by
  apply le_antisymm
  · apply Submodule.span_mono
    rintro _ ⟨i, rfl⟩
    change smoothToLpDirichlet g
        (smoothDirichletL2GramSchmidtNormed (smoothDirichletH1DenseSeq g) i.1) ∈
      Set.range (fun i : ℕ => smoothToLpDirichlet g
        (smoothDirichletL2GramSchmidtNormed (smoothDirichletH1DenseSeq g) i))
    exact Set.mem_range_self (i.1 : ℕ)
  · apply Submodule.span_le.2
    rintro _ ⟨i, rfl⟩
    by_cases hi : InnerProductSpace.gramSchmidtNormed ℝ
        (fun k => smoothToLpDirichlet g (smoothDirichletH1DenseSeq g k)) i = 0
    · change smoothToLpDirichlet g
        (smoothDirichletL2GramSchmidtNormed (smoothDirichletH1DenseSeq g) i) ∈ _
      rw [smoothToLpDirichlet_smoothDirichletL2GramSchmidtNormed, hi]
      exact Submodule.zero_mem _
    · exact Submodule.subset_span ⟨⟨i, hi⟩, rfl⟩

private theorem span_smoothDirichletBasisFunction_eq_smooth
    (g : SmoothRiemannianMetric (I_half n) M) :
    Submodule.span ℝ (Set.range (smoothDirichletBasisFunction g)) =
      Submodule.span ℝ (Set.range (fun i =>
        smoothDirichletL2GramSchmidtNormed (smoothDirichletH1DenseSeq g) i)) := by
  apply (Submodule.map_injective_of_injective
    (f := (smoothToLpDirichlet g).toLinearMap)
    (smoothToLpDirichlet_injective g))
  rw [Submodule.map_span, Submodule.map_span, ← Set.range_comp', ← Set.range_comp']
  simpa only [ContinuousLinearMap.coe_coe, Function.comp_apply] using
    span_smoothDirichletBasisFunction_eq g

theorem dense_span_smoothToH1ComplDirichlet_smoothDirichletBasisFunction
    (g : SmoothRiemannianMetric (I_half n) M) :
    Dense (Submodule.span ℝ (Set.range (fun i =>
      smoothToH1ComplDirichlet g (smoothDirichletBasisFunction g i))) :
        Set (H1ComplDirichlet g)) := by
  have hsmooth :
      Submodule.span ℝ (Set.range (smoothDirichletBasisFunction g)) =
        Submodule.span ℝ (Set.range (smoothDirichletH1DenseSeq g)) := by
    exact (span_smoothDirichletBasisFunction_eq_smooth g).trans
      (span_smoothDirichletL2GramSchmidtNormed (smoothDirichletH1DenseSeq g))
  have hmap := congrArg
    (fun p : Submodule ℝ (SmoothScalarDirichlet g) =>
      p.map (smoothToH1ComplDirichlet g).toLinearMap) hsmooth
  have hspan :
      Submodule.span ℝ (Set.range (fun i =>
        smoothToH1ComplDirichlet g (smoothDirichletBasisFunction g i))) =
        Submodule.span ℝ (Set.range (fun i =>
          smoothToH1ComplDirichlet g (smoothDirichletH1DenseSeq g i))) := by
    rw [Submodule.map_span, Submodule.map_span, ← Set.range_comp', ← Set.range_comp'] at hmap
    simpa only [ContinuousLinearMap.coe_coe, Function.comp_apply] using hmap
  rw [hspan]
  exact (denseRange_smoothToH1ComplDirichlet_smoothDirichletH1DenseSeq g).mono
    Submodule.subset_span

private theorem span_smoothDirichletBasisFunction_orthogonal_eq_bot
    (g : SmoothRiemannianMetric (I_half n) M) :
    (Submodule.span ℝ (Set.range (fun i =>
      smoothToLpDirichlet g (smoothDirichletBasisFunction g i))))ᗮ = ⊥ := by
  rw [span_smoothDirichletBasisFunction_eq]
  rw [span_smoothToLpDirichlet_smoothDirichletL2GramSchmidtNormed]
  apply le_antisymm
  · intro x hx
    rw [Submodule.mem_bot]
    apply (denseRange_smoothToLpDirichlet_smoothDirichletH1DenseSeq g).eq_zero_of_inner_left
      (𝕜 := ℝ)
    intro i
    exact (Submodule.mem_orthogonal' _ x).mp hx _
      (Submodule.subset_span ⟨i, rfl⟩)
  · exact bot_le

noncomputable def smoothDirichletHilbertBasis
    (g : SmoothRiemannianMetric (I_half n) M) :
    HilbertBasis (SmoothDirichletBasisIndex g) ℝ
      (Lp ℝ 2 (riemannianVolumeMeasure (I := I_half n) (M := M) g)) :=
  HilbertBasis.mkOfOrthogonalEqBot
    (smoothDirichletBasisFunction_orthonormal g)
    (span_smoothDirichletBasisFunction_orthogonal_eq_bot g)

@[simp] theorem smoothDirichletHilbertBasis_apply
    (g : SmoothRiemannianMetric (I_half n) M)
    (i : SmoothDirichletBasisIndex g) :
    smoothDirichletHilbertBasis g i =
      smoothToLpDirichlet g (smoothDirichletBasisFunction g i) := by
  unfold smoothDirichletHilbertBasis
  exact congr_fun
    (HilbertBasis.coe_mkOfOrthogonalEqBot
      (smoothDirichletBasisFunction_orthonormal g)
      (span_smoothDirichletBasisFunction_orthogonal_eq_bot g)) i

noncomputable def smoothDirichletBasisFinset
    (g : SmoothRiemannianMetric (I_half n) M) (m : ℕ) :
    Finset (SmoothDirichletBasisIndex g) :=
  (Finset.range m).preimage
    ((↑) : SmoothDirichletBasisIndex g → ℕ) Subtype.val_injective.injOn

@[simp] theorem mem_smoothDirichletBasisFinset_iff
    (g : SmoothRiemannianMetric (I_half n) M) (m : ℕ)
    (i : SmoothDirichletBasisIndex g) :
    i ∈ smoothDirichletBasisFinset g m ↔ i.1 < m := by
  simp only [smoothDirichletBasisFinset, Finset.mem_preimage, Finset.mem_range]

theorem tendsto_smoothDirichletBasisFinset_atTop
    (g : SmoothRiemannianMetric (I_half n) M) :
    Tendsto (smoothDirichletBasisFinset g) atTop atTop := by
  unfold smoothDirichletBasisFinset
  exact (tendsto_finset_preimage_atTop_atTop
      (α := SmoothDirichletBasisIndex g) (β := ℕ)
      (f := ((↑) : SmoothDirichletBasisIndex g → ℕ))
      Subtype.val_injective).comp tendsto_finset_range

noncomputable def smoothDirichletBasisApproximation
    (g : SmoothRiemannianMetric (I_half n) M) (m : ℕ)
    (f : Lp ℝ 2 (riemannianVolumeMeasure (I := I_half n) (M := M) g)) :
    SmoothScalarDirichlet g :=
  ∑ i ∈ smoothDirichletBasisFinset g m,
    (smoothDirichletHilbertBasis g).repr f i • smoothDirichletBasisFunction g i

theorem tendsto_smoothToLpDirichlet_smoothDirichletBasisApproximation
    (g : SmoothRiemannianMetric (I_half n) M)
    (f : Lp ℝ 2 (riemannianVolumeMeasure (I := I_half n) (M := M) g)) :
    Tendsto (fun m =>
      smoothToLpDirichlet g (smoothDirichletBasisApproximation g m f))
      atTop (𝓝 f) := by
  have hsum := (smoothDirichletHilbertBasis g).hasSum_repr f
  have hpartial := hsum.comp (tendsto_smoothDirichletBasisFinset_atTop g)
  convert hpartial using 1
  funext m
  simp only [Function.comp_apply, smoothDirichletBasisApproximation,
    map_sum, map_smul, smoothDirichletHilbertBasis_apply]

theorem norm_smoothToLpDirichlet_smoothDirichletBasisApproximation_le
    (g : SmoothRiemannianMetric (I_half n) M) (m : ℕ)
    (f : Lp ℝ 2 (riemannianVolumeMeasure (I := I_half n) (M := M) g)) :
    ‖smoothToLpDirichlet g (smoothDirichletBasisApproximation g m f)‖ ≤ ‖f‖ := by
  let b := smoothDirichletHilbertBasis g
  let s := smoothDirichletBasisFinset g m
  have hsum :
      smoothToLpDirichlet g (smoothDirichletBasisApproximation g m f) =
        ∑ i ∈ s, b.repr f i • b i := by
    simp only [smoothDirichletBasisApproximation, map_sum, map_smul,
      smoothDirichletHilbertBasis_apply, b, s]
  rw [hsum]
  have hnormSq :
      ‖∑ i ∈ s, b.repr f i • b i‖ ^ 2 =
        ∑ i ∈ s, ‖b.repr f i‖ ^ 2 := by
    calc
      ‖∑ i ∈ s, b.repr f i • b i‖ ^ 2 =
          inner ℝ (∑ i ∈ s, b.repr f i • b i)
            (∑ i ∈ s, b.repr f i • b i) :=
        (real_inner_self_eq_norm_sq _).symm
      _ = ∑ i ∈ s, b.repr f i * b.repr f i := by
        convert b.orthonormal.inner_sum
          (fun i ↦ b.repr f i) (fun i ↦ b.repr f i) s using 1
        simp
      _ = ∑ i ∈ s, ‖b.repr f i‖ ^ 2 := by
        refine Finset.sum_congr rfl (fun i _ ↦ ?_)
        rw [Real.norm_eq_abs, sq_abs, pow_two]
  have hbessel : ∑ i ∈ s, ‖b.repr f i‖ ^ 2 ≤ ‖f‖ ^ 2 := by
    simpa only [b.repr_apply_apply] using b.orthonormal.sum_inner_products_le f
  have hsquare : ‖∑ i ∈ s, b.repr f i • b i‖ ^ 2 ≤ ‖f‖ ^ 2 := by
    rw [hnormSq]
    exact hbessel
  nlinarith [norm_nonneg (∑ i ∈ s, b.repr f i • b i), norm_nonneg f]

end Dirichlet
end WithBoundary
end Laplacian
end Analysis
end DifferentialGeometry

end
