import DifferentialGeometry.Analysis.Elliptic.WithBoundary.DirichletEigenBasis
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

private theorem exists_smoothDirichletL2DenseSeq
    (g : SmoothRiemannianMetric (I_half n) M) :
    ∃ φ : ℕ → SmoothScalarDirichlet g,
      DenseRange (fun i => smoothToLpDirichlet g (φ i)) := by
  let b := dirichletLaplacianHilbertBasis g
  have hrange : TopologicalSpace.IsSeparable (Set.range b) :=
    Set.countable_range b |>.isSeparable
  have hspan : TopologicalSpace.IsSeparable
      (Submodule.span ℝ (Set.range b) : Set
        (Lp ℝ 2 (riemannianVolumeMeasure (I := I_half n) (M := M) g))) :=
    hrange.span
  have hclosure : closure (Submodule.span ℝ (Set.range b) : Set
      (Lp ℝ 2 (riemannianVolumeMeasure (I := I_half n) (M := M) g))) = Set.univ := by
    change closure (Submodule.span ℝ (Set.range b) : Set
      (Lp ℝ 2 (riemannianVolumeMeasure (I := I_half n) (M := M) g))) =
        (↑(⊤ : Submodule ℝ
          (Lp ℝ 2 (riemannianVolumeMeasure (I := I_half n) (M := M) g))) : Set _)
    simpa only [Submodule.topologicalClosure_coe] using
      congrArg SetLike.coe b.dense_span
  let _ : TopologicalSpace.SeparableSpace
      (Lp ℝ 2 (riemannianVolumeMeasure (I := I_half n) (M := M) g)) :=
    TopologicalSpace.isSeparable_univ_iff.mp (by
      rw [← hclosure]
      exact hspan.closure)
  have hd := denseRange_smoothToLpDirichlet g
  obtain ⟨t, htrange, htcount, htdense⟩ := hd.exists_countable_dense_subset
  obtain ⟨u, hu⟩ := htcount.exists_eq_range htdense.nonempty
  have hu_mem : ∀ i, u i ∈ t := by
    intro i
    rw [hu]
    exact Set.mem_range_self i
  have hpre : ∀ i, ∃ f : SmoothScalarDirichlet g,
      smoothToLpDirichlet g f = u i := by
    intro i
    simpa only [Set.mem_range] using htrange (hu_mem i)
  choose φ hφ using hpre
  refine ⟨φ, ?_⟩
  rw [show (fun i => smoothToLpDirichlet g (φ i)) = u by
    funext i
    exact hφ i]
  change Dense (Set.range u)
  rw [← hu]
  exact htdense

noncomputable def smoothDirichletL2DenseSeq
    (g : SmoothRiemannianMetric (I_half n) M) :
    ℕ → SmoothScalarDirichlet g :=
  Classical.choose (exists_smoothDirichletL2DenseSeq g)

theorem denseRange_smoothToLpDirichlet_smoothDirichletL2DenseSeq
    (g : SmoothRiemannianMetric (I_half n) M) :
    DenseRange (fun i => smoothToLpDirichlet g (smoothDirichletL2DenseSeq g i)) :=
  Classical.choose_spec (exists_smoothDirichletL2DenseSeq g)

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

end OrderedFamily

abbrev SmoothDirichletBasisIndex
    (g : SmoothRiemannianMetric (I_half n) M) :=
  {i : ℕ | InnerProductSpace.gramSchmidtNormed ℝ
    (fun k => smoothToLpDirichlet g (smoothDirichletL2DenseSeq g k)) i ≠ 0}

noncomputable def smoothDirichletBasisFunction
    (g : SmoothRiemannianMetric (I_half n) M)
    (i : SmoothDirichletBasisIndex g) : SmoothScalarDirichlet g :=
  smoothDirichletL2GramSchmidtNormed (smoothDirichletL2DenseSeq g) i

theorem smoothDirichletBasisFunction_orthonormal
    (g : SmoothRiemannianMetric (I_half n) M) :
    Orthonormal ℝ (fun i =>
      smoothToLpDirichlet g (smoothDirichletBasisFunction g i)) := by
  simpa only [smoothDirichletBasisFunction] using
    smoothDirichletL2GramSchmidtNormed_orthonormal
      (smoothDirichletL2DenseSeq g)

private theorem span_smoothDirichletBasisFunction_eq
    (g : SmoothRiemannianMetric (I_half n) M) :
    Submodule.span ℝ (Set.range (fun i =>
        smoothToLpDirichlet g (smoothDirichletBasisFunction g i))) =
      Submodule.span ℝ (Set.range (fun i =>
        smoothToLpDirichlet g
          (smoothDirichletL2GramSchmidtNormed (smoothDirichletL2DenseSeq g) i))) := by
  apply le_antisymm
  · apply Submodule.span_mono
    rintro _ ⟨i, rfl⟩
    change smoothToLpDirichlet g
        (smoothDirichletL2GramSchmidtNormed (smoothDirichletL2DenseSeq g) i.1) ∈
      Set.range (fun i : ℕ => smoothToLpDirichlet g
        (smoothDirichletL2GramSchmidtNormed (smoothDirichletL2DenseSeq g) i))
    exact Set.mem_range_self (i.1 : ℕ)
  · apply Submodule.span_le.2
    rintro _ ⟨i, rfl⟩
    by_cases hi : InnerProductSpace.gramSchmidtNormed ℝ
        (fun k => smoothToLpDirichlet g (smoothDirichletL2DenseSeq g k)) i = 0
    · change smoothToLpDirichlet g
        (smoothDirichletL2GramSchmidtNormed (smoothDirichletL2DenseSeq g) i) ∈ _
      rw [smoothToLpDirichlet_smoothDirichletL2GramSchmidtNormed, hi]
      exact Submodule.zero_mem _
    · exact Submodule.subset_span ⟨⟨i, hi⟩, rfl⟩

private theorem span_smoothDirichletBasisFunction_orthogonal_eq_bot
    (g : SmoothRiemannianMetric (I_half n) M) :
    (Submodule.span ℝ (Set.range (fun i =>
      smoothToLpDirichlet g (smoothDirichletBasisFunction g i))))ᗮ = ⊥ := by
  rw [span_smoothDirichletBasisFunction_eq]
  rw [span_smoothToLpDirichlet_smoothDirichletL2GramSchmidtNormed]
  apply le_antisymm
  · intro x hx
    rw [Submodule.mem_bot]
    apply (denseRange_smoothToLpDirichlet_smoothDirichletL2DenseSeq g).eq_zero_of_inner_left
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

end Dirichlet
end WithBoundary
end Laplacian
end Analysis
end DifferentialGeometry

end
