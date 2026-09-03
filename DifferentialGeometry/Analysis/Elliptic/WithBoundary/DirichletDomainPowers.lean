import DifferentialGeometry.Analysis.Elliptic.WithBoundary.DirichletEigenBasis

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

private theorem one_add_pow_mul_resolvent_pow_cancel
    (r lambda x : ℝ) (k : ℕ) (h : r * (1 + lambda) = 1) :
    (1 + lambda) ^ k * x * r ^ k = x := by
  have hpow : (1 + lambda) ^ k * r ^ k = 1 := by
    rw [← mul_pow, mul_comm, h, one_pow]
  calc
    (1 + lambda) ^ k * x * r ^ k =
        ((1 + lambda) ^ k * r ^ k) * x := by ring
    _ = x := by rw [hpow, one_mul]

private theorem map_eq_of_hilbertBasis_diagonal
    {ι X : Type*} [NormedAddCommGroup X] [InnerProductSpace ℝ X]
    (b : HilbertBasis ι ℝ X) (T : X →L[ℝ] X) (d : ι → ℝ) (u v : X)
    (hbasis : ∀ i, T (b i) = d i • b i)
    (hcoeff : ∀ i, (b.repr v) i * d i = (b.repr u) i) :
    T v = u := by
  have hmap : HasSum (fun i => (b.repr v) i • T (b i)) (T v) := by
    simpa only [map_smul] using (b.hasSum_repr v).mapL T
  have hsummand : (fun i => (b.repr v) i • T (b i)) =
      fun i => (b.repr u) i • b i := by
    funext i
    rw [hbasis i, smul_smul, hcoeff i]
  rw [hsummand] at hmap
  exact HasSum.unique hmap (b.hasSum_repr u)

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

theorem iteratedDirichletResolventL2_apply_dirichletLaplacianHilbertBasis
    (g : SmoothRiemannianMetric (I_half n) M) (k : ℕ)
    (i : DirichletLaplacianEigenindex g) :
    iteratedDirichletResolventL2 g k
        (dirichletLaplacianHilbertBasis g i) =
      (i.1.val ^ k) • dirichletLaplacianHilbertBasis g i := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [iteratedDirichletResolventL2_succ,
      ContinuousLinearMap.comp_apply, ih,
      (resolventDirichletL2 g).map_smul,
      resolventDirichletL2_apply_dirichletLaplacianHilbertBasis,
      smul_smul]
    congr 1

theorem exists_iteratedDirichletResolventL2_preimage_of_weighted_coeff_summable
    (g : SmoothRiemannianMetric (I_half n) M)
    (u : Lp ℝ 2 (riemannianVolumeMeasure (I := I_half n) (M := M) g))
    (k : ℕ)
    (hsum : Summable (fun i : DirichletLaplacianEigenindex g =>
      (1 + dirichletLaplacianEigenvalue i) ^ (2 * k) *
        ⟪dirichletLaplacianHilbertBasis g i, u⟫_ℝ ^ 2)) :
    ∃ v : Lp ℝ 2 (riemannianVolumeMeasure (I := I_half n) (M := M) g),
      iteratedDirichletResolventL2 g k v = u := by
  classical
  set b := dirichletLaplacianHilbertBasis g
  let c : DirichletLaplacianEigenindex g → ℝ := fun i =>
    (1 + dirichletLaplacianEigenvalue i) ^ k * (b.repr u) i
  have hc_sq : Summable (fun i => (c i) ^ 2) := by
    have heq : (fun i => (c i) ^ 2) = fun i =>
        (1 + dirichletLaplacianEigenvalue i) ^ (2 * k) *
          ⟪b i, u⟫_ℝ ^ 2 := by
      funext i
      simp only [c]
      rw [b.repr_apply_apply, mul_pow, ← pow_mul]
      congr 2
      omega
    rw [heq]
    exact hsum
  have hc_mem : Memℓp c 2 := by
    apply memℓp_gen
    have hpr : (2 : ℝ≥0∞).toReal = 2 := by norm_num
    have heq : (fun i => ‖c i‖ ^ (2 : ℝ≥0∞).toReal) =
        fun i => (c i) ^ 2 := by
      funext i
      rw [hpr, Real.norm_eq_abs, ← sq_abs]
      norm_num
    rw [heq]
    exact hc_sq
  let v : Lp ℝ 2 (riemannianVolumeMeasure (I := I_half n) (M := M) g) :=
    b.repr.symm ⟨c, hc_mem⟩
  have hv_coeff : ∀ i, (b.repr v) i = c i := by
    intro i
    have hv_repr : b.repr v = ⟨c, hc_mem⟩ :=
      LinearIsometryEquiv.apply_symm_apply _ _
    exact congrArg (fun w => w i) hv_repr
  refine ⟨v, map_eq_of_hilbertBasis_diagonal b
    (iteratedDirichletResolventL2 g k) (fun i => i.1.val ^ k) u v
    (iteratedDirichletResolventL2_apply_dirichletLaplacianHilbertBasis g k) ?_⟩
  intro i
  calc
    (b.repr v) i * i.1.val ^ k = c i * i.1.val ^ k :=
      congrArg (fun z => z * i.1.val ^ k) (hv_coeff i)
    _ = (b.repr u) i := one_add_pow_mul_resolvent_pow_cancel i.1.val
      (dirichletLaplacianEigenvalue i) ((b.repr u) i) k (by
        rw [one_add_dirichletLaplacianEigenvalue_eq_inv,
          mul_inv_cancel₀ i.1.val_ne_zero])

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

theorem exists_dirichletLaplacianDomainPow_succ_lift_of_weighted_coeff_summable
    (g : SmoothRiemannianMetric (I_half n) M)
    (u : Lp ℝ 2 (riemannianVolumeMeasure (I := I_half n) (M := M) g))
    (k : ℕ)
    (hsum : Summable (fun i : DirichletLaplacianEigenindex g =>
      (1 + dirichletLaplacianEigenvalue i) ^ (2 * (k + 1)) *
        ⟪dirichletLaplacianHilbertBasis g i, u⟫_ℝ ^ 2)) :
    ∃ u_h : H1ComplDirichlet g,
      u_h ∈ dirichletLaplacianDomainPow g (k + 1) ∧
        H1ComplDirichletToLp g u_h = u := by
  obtain ⟨v, hv⟩ :=
    exists_iteratedDirichletResolventL2_preimage_of_weighted_coeff_summable
      g u (k + 1) hsum
  refine ⟨resolventDirichlet g (iteratedDirichletResolventL2 g k v), ?_, ?_⟩
  · rw [dirichletLaplacianDomainPow_succ_mem_iff]
    exact ⟨v, rfl⟩
  · rw [← resolventDirichletL2_apply,
      ← iteratedDirichletResolventL2_succ_apply]
    exact hv

end Dirichlet
end WithBoundary
end Laplacian
end Analysis
end DifferentialGeometry
