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

theorem resolventDirichletL2_pow_apply_dirichletLaplacianHilbertBasis
    (g : SmoothRiemannianMetric (I_half n) M) (k : ℕ)
    (i : DirichletLaplacianEigenIndex g) :
    ((resolventDirichletL2 g) ^ k) (dirichletLaplacianHilbertBasis g i) =
      (i.1.1 ^ k) • dirichletLaplacianHilbertBasis g i := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [pow_succ', mul_apply_eq_comp, ih,
      (resolventDirichletL2 g).map_smul,
      resolventDirichletL2_apply_dirichletLaplacianHilbertBasis,
      smul_smul, pow_succ]

theorem inner_dirichletLaplacianHilbertBasis_resolventDirichletL2_pow
    (g : SmoothRiemannianMetric (I_half n) M) (k : ℕ)
    (f : Lp ℝ 2 (riemannianVolumeMeasure (I := I_half n) (M := M) g))
    (i : DirichletLaplacianEigenIndex g) :
    ⟪dirichletLaplacianHilbertBasis g i,
        ((resolventDirichletL2 g) ^ k) f⟫_ℝ =
      i.1.1 ^ k * ⟪dirichletLaplacianHilbertBasis g i, f⟫_ℝ := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [pow_succ', mul_apply_eq_comp, ← resolventDirichletL2_symm,
      resolventDirichletL2_apply_dirichletLaplacianHilbertBasis,
      real_inner_smul_left, ih, pow_succ']
    ring

theorem exists_resolventDirichletL2_pow_preimage_of_weighted_coeff_summable
    (g : SmoothRiemannianMetric (I_half n) M)
    (u : Lp ℝ 2 (riemannianVolumeMeasure (I := I_half n) (M := M) g))
    (k : ℕ)
    (hsum : Summable (fun i : DirichletLaplacianEigenIndex g =>
      (1 + dirichletLaplacianEigenvalue i) ^ (2 * k) *
        ⟪dirichletLaplacianHilbertBasis g i, u⟫_ℝ ^ 2)) :
    ∃ v : Lp ℝ 2 (riemannianVolumeMeasure (I := I_half n) (M := M) g),
      ((resolventDirichletL2 g) ^ k) v = u := by
  classical
  set b := dirichletLaplacianHilbertBasis g
  let c : DirichletLaplacianEigenIndex g → ℝ := fun i =>
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
    (((resolventDirichletL2 g) ^ k)) (fun i => i.1.1 ^ k) u v
    (resolventDirichletL2_pow_apply_dirichletLaplacianHilbertBasis g k) ?_⟩
  intro i
  calc
    (b.repr v) i * i.1.1 ^ k = c i * i.1.1 ^ k :=
      congrArg (fun z => z * i.1.1 ^ k) (hv_coeff i)
    _ = (b.repr u) i := one_add_pow_mul_resolvent_pow_cancel i.1.1
      (dirichletLaplacianEigenvalue i) ((b.repr u) i) k (by
        rw [one_add_dirichletLaplacianEigenvalue_eq_inv,
          mul_inv_cancel₀ (ne_of_gt (resolvent_eigenvalue_pos g i.1.property))])

def dirichletLaplacianDomainPow
    (g : SmoothRiemannianMetric (I_half n) M) (k : ℕ) :
    Submodule ℝ (H1ComplDirichlet g) :=
  Nat.recAux (motive := fun _ => Submodule ℝ (H1ComplDirichlet g))
    ⊤
    (fun k _ => LinearMap.range
      ((resolventDirichlet g).toLinearMap.comp
        (((resolventDirichletL2 g) ^ k)).toLinearMap)) k

@[simp] theorem dirichletLaplacianDomainPow_zero
    (g : SmoothRiemannianMetric (I_half n) M) :
    dirichletLaplacianDomainPow g 0 = ⊤ :=
  rfl

theorem dirichletLaplacianDomainPow_succ
    (g : SmoothRiemannianMetric (I_half n) M) (k : ℕ) :
    dirichletLaplacianDomainPow g (k + 1) =
      LinearMap.range
        ((resolventDirichlet g).toLinearMap.comp
          (((resolventDirichletL2 g) ^ k)).toLinearMap) :=
  rfl

theorem dirichletLaplacianDomainPow_one
    (g : SmoothRiemannianMetric (I_half n) M) :
    dirichletLaplacianDomainPow g 1 = dirichletLaplacianDomain g := by
  rw [dirichletLaplacianDomainPow_succ,
    pow_zero]
  rfl

theorem dirichletLaplacianDomainPow_succ_mem_iff
    (g : SmoothRiemannianMetric (I_half n) M) (k : ℕ)
    {u : H1ComplDirichlet g} :
    u ∈ dirichletLaplacianDomainPow g (k + 1) ↔
      ∃ f : Lp ℝ 2 (riemannianVolumeMeasure (I := I_half n) (M := M) g),
        u = resolventDirichlet g (((resolventDirichletL2 g) ^ k) f) := by
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
  exact ⟨((resolventDirichletL2 g) ^ k) f, hf⟩

theorem dirichletLaplacianDomainPow_succ_le
    (g : SmoothRiemannianMetric (I_half n) M) (k : ℕ) :
    dirichletLaplacianDomainPow g (k + 1) ≤
      dirichletLaplacianDomainPow g k := by
  cases k with
  | zero =>
      rw [dirichletLaplacianDomainPow_zero]
      exact le_top
  | succ k =>
      intro u hu
      rw [dirichletLaplacianDomainPow_succ_mem_iff] at hu ⊢
      obtain ⟨f, hf⟩ := hu
      refine ⟨resolventDirichletL2 g f, ?_⟩
      have hiter :
          ((resolventDirichletL2 g) ^ (k + 1)) f =
            ((resolventDirichletL2 g) ^ k)
              (resolventDirichletL2 g f) := by
        rw [pow_succ, mul_apply_eq_comp]
      exact hf.trans (congrArg (resolventDirichlet g) hiter)

theorem dirichletLaplacianDomainPow_antitone
    (g : SmoothRiemannianMetric (I_half n) M) :
    Antitone (dirichletLaplacianDomainPow g) := by
  intro j k hjk
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hjk
  clear hjk
  induction d with
  | zero => exact le_rfl
  | succ d ih =>
      rw [Nat.add_succ]
      exact (dirichletLaplacianDomainPow_succ_le g (j + d)).trans ih

theorem dirichletLaplacianDomainPow_le_of_le
    (g : SmoothRiemannianMetric (I_half n) M) {j k : ℕ} (hjk : j ≤ k) :
    dirichletLaplacianDomainPow g k ≤
      dirichletLaplacianDomainPow g j :=
  dirichletLaplacianDomainPow_antitone g hjk

theorem dirichletLaplacianDomainPow_succ_preimage_mem_range
    (g : SmoothRiemannianMetric (I_half n) M) (k : ℕ)
    {u : H1ComplDirichlet g}
    (hu : u ∈ dirichletLaplacianDomainPow g (k + 1)) :
    (dirichletResolventEquiv g).symm
        ⟨u, dirichletLaplacianDomainPow_succ_subset_dirichletLaplacianDomain
          g k hu⟩ ∈
      LinearMap.range (((resolventDirichletL2 g) ^ k)).toLinearMap := by
  rw [dirichletLaplacianDomainPow_succ_mem_iff] at hu
  obtain ⟨f, hf⟩ := hu
  rw [LinearMap.mem_range]
  refine ⟨f, ?_⟩
  apply resolventDirichlet_injective g
  rw [resolventDirichlet_dirichletResolventEquiv_symm]
  exact hf.symm

theorem exists_dirichletLaplacianDomainPow_succ_lift_of_weighted_coeff_summable
    (g : SmoothRiemannianMetric (I_half n) M)
    (u : Lp ℝ 2 (riemannianVolumeMeasure (I := I_half n) (M := M) g))
    (k : ℕ)
    (hsum : Summable (fun i : DirichletLaplacianEigenIndex g =>
      (1 + dirichletLaplacianEigenvalue i) ^ (2 * (k + 1)) *
        ⟪dirichletLaplacianHilbertBasis g i, u⟫_ℝ ^ 2)) :
    ∃ u_h : H1ComplDirichlet g,
      u_h ∈ dirichletLaplacianDomainPow g (k + 1) ∧
        H1ComplDirichletToLp g u_h = u := by
  obtain ⟨v, hv⟩ :=
    exists_resolventDirichletL2_pow_preimage_of_weighted_coeff_summable
      g u (k + 1) hsum
  refine ⟨resolventDirichlet g (((resolventDirichletL2 g) ^ k) v), ?_, ?_⟩
  · rw [dirichletLaplacianDomainPow_succ_mem_iff]
    exact ⟨v, rfl⟩
  · rw [← resolventDirichletL2_apply]
    simpa only [pow_succ', mul_apply_eq_comp] using hv

end Dirichlet
end WithBoundary
end Laplacian
end Analysis
end DifferentialGeometry
