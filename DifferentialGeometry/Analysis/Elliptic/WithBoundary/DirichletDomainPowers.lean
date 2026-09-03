import DifferentialGeometry.Analysis.Elliptic.WithBoundary.DirichletSpectrum
import DifferentialGeometry.Analysis.Elliptic.WithBoundary.DirichletVariationalLaplacian

noncomputable section

open Bundle Manifold MeasureTheory Set Filter
open scoped Manifold Topology ContDiff ENNReal BigOperators
  RealInnerProductSpace InnerProductSpace

namespace DifferentialGeometry
namespace Analysis
namespace Laplacian
namespace WithBoundary
namespace Dirichlet

variable {n : ℕ} [NeZero n]
variable {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanHalfSpace n) M]
  [IsManifold (modelWithCornersEuclideanHalfSpace n) ∞ M]
  [T2Space M] [CompactSpace M]

private abbrev I_half (n : ℕ) [NeZero n] :
    ModelWithCorners ℝ (EuclideanSpace ℝ (Fin n)) (EuclideanHalfSpace n) :=
  modelWithCornersEuclideanHalfSpace n

open DifferentialGeometry.Integral.Measure

def iteratedDirichletResolventL2
    (g : SmoothRiemannianMetric (I_half n) M) (k : ℕ) :
    Lp ℝ 2 (riemannianVolumeMeasure (I := I_half n) (M := M) g) →L[ℝ]
      Lp ℝ 2 (riemannianVolumeMeasure (I := I_half n) (M := M) g) :=
  Nat.recAux (motive := fun _ =>
    Lp ℝ 2 (riemannianVolumeMeasure (I := I_half n) (M := M) g) →L[ℝ]
      Lp ℝ 2 (riemannianVolumeMeasure (I := I_half n) (M := M) g))
    (ContinuousLinearMap.id ℝ _)
    (fun _ previous => (resolventDirichletL2 g).comp previous) k

@[simp] theorem iteratedDirichletResolventL2_zero
    (g : SmoothRiemannianMetric (I_half n) M) :
    iteratedDirichletResolventL2 g 0 = ContinuousLinearMap.id ℝ _ :=
  rfl

@[simp] theorem iteratedDirichletResolventL2_succ
    (g : SmoothRiemannianMetric (I_half n) M) (k : ℕ) :
    iteratedDirichletResolventL2 g (k + 1) =
      (resolventDirichletL2 g).comp (iteratedDirichletResolventL2 g k) :=
  rfl

theorem iteratedDirichletResolventL2_one
    (g : SmoothRiemannianMetric (I_half n) M) :
    iteratedDirichletResolventL2 g 1 = resolventDirichletL2 g := by
  rw [iteratedDirichletResolventL2_succ,
    iteratedDirichletResolventL2_zero]
  exact ContinuousLinearMap.comp_id _

@[simp] theorem iteratedDirichletResolventL2_zero_apply
    (g : SmoothRiemannianMetric (I_half n) M)
    (f : Lp ℝ 2 (riemannianVolumeMeasure (I := I_half n) (M := M) g)) :
    iteratedDirichletResolventL2 g 0 f = f :=
  rfl

theorem iteratedDirichletResolventL2_succ_apply
    (g : SmoothRiemannianMetric (I_half n) M) (k : ℕ)
    (f : Lp ℝ 2 (riemannianVolumeMeasure (I := I_half n) (M := M) g)) :
    iteratedDirichletResolventL2 g (k + 1) f =
      resolventDirichletL2 g (iteratedDirichletResolventL2 g k f) :=
  rfl

theorem iteratedDirichletResolventL2_add
    (g : SmoothRiemannianMetric (I_half n) M) (j k : ℕ) :
    iteratedDirichletResolventL2 g (j + k) =
      (iteratedDirichletResolventL2 g j).comp
        (iteratedDirichletResolventL2 g k) := by
  induction j with
  | zero => simp
  | succ j ih =>
    rw [Nat.succ_add, iteratedDirichletResolventL2_succ,
      iteratedDirichletResolventL2_succ, ih,
      ContinuousLinearMap.comp_assoc]

def dirichletLaplacianDomainPow
    (g : SmoothRiemannianMetric (I_half n) M) (k : ℕ) :
    Submodule ℝ (H1ComplDirichlet g) :=
  Nat.recAux (motive := fun _ => Submodule ℝ (H1ComplDirichlet g))
    ⊤
    (fun k _ => LinearMap.range
      ((resolventDirichlet g).toLinearMap.comp
        (iteratedDirichletResolventL2 g k).toLinearMap)) k

@[simp] theorem dirichletLaplacianDomainPow_zero
    (g : SmoothRiemannianMetric (I_half n) M) :
    dirichletLaplacianDomainPow g 0 = ⊤ :=
  rfl

theorem dirichletLaplacianDomainPow_succ
    (g : SmoothRiemannianMetric (I_half n) M) (k : ℕ) :
    dirichletLaplacianDomainPow g (k + 1) =
      LinearMap.range
        ((resolventDirichlet g).toLinearMap.comp
          (iteratedDirichletResolventL2 g k).toLinearMap) :=
  rfl

theorem dirichletLaplacianDomainPow_one
    (g : SmoothRiemannianMetric (I_half n) M) :
    dirichletLaplacianDomainPow g 1 = dirichletLaplacianDomain g := by
  rw [dirichletLaplacianDomainPow_succ,
    iteratedDirichletResolventL2_zero]
  rfl

theorem dirichletLaplacianDomainPow_succ_mem_iff
    (g : SmoothRiemannianMetric (I_half n) M) (k : ℕ)
    {u : H1ComplDirichlet g} :
    u ∈ dirichletLaplacianDomainPow g (k + 1) ↔
      ∃ f : Lp ℝ 2 (riemannianVolumeMeasure (I := I_half n) (M := M) g),
        u = resolventDirichlet g (iteratedDirichletResolventL2 g k f) := by
  rw [dirichletLaplacianDomainPow_succ, LinearMap.mem_range]
  constructor
  · rintro ⟨f, hf⟩
    exact ⟨f, hf.symm⟩
  · rintro ⟨f, hf⟩
    exact ⟨f, hf.symm⟩

theorem dirichletLaplacianDomainPow_succ_subset_dirichletLaplacianDomain
    (g : SmoothRiemannianMetric (I_half n) M) (k : ℕ) :
    (dirichletLaplacianDomainPow g (k + 1) : Set (H1ComplDirichlet g)) ⊆
      (dirichletLaplacianDomain g : Set (H1ComplDirichlet g)) := by
  intro u hu
  rw [SetLike.mem_coe, dirichletLaplacianDomainPow_succ_mem_iff] at hu
  obtain ⟨f, hf⟩ := hu
  rw [SetLike.mem_coe, dirichletLaplacianDomain_mem_iff]
  exact ⟨iteratedDirichletResolventL2 g k f, hf⟩

theorem dirichletLaplacianDomainPow_succ_preimage_mem_range
    (g : SmoothRiemannianMetric (I_half n) M) (k : ℕ)
    {u : H1ComplDirichlet g}
    (hu : u ∈ dirichletLaplacianDomainPow g (k + 1)) :
    dirichletLaplacianDomain.preimage g
        ⟨u, dirichletLaplacianDomainPow_succ_subset_dirichletLaplacianDomain
          g k hu⟩ ∈
      LinearMap.range (iteratedDirichletResolventL2 g k).toLinearMap := by
  rw [dirichletLaplacianDomainPow_succ_mem_iff] at hu
  obtain ⟨f, hf⟩ := hu
  rw [LinearMap.mem_range]
  refine ⟨f, ?_⟩
  apply resolventDirichlet_injective g
  rw [resolventDirichlet_preimage_eq]
  exact hf.symm

end Dirichlet
end WithBoundary
end Laplacian
end Analysis
end DifferentialGeometry
