import DifferentialGeometry.Analysis.Elliptic.WithBoundary.DirichletDensity

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

private abbrev I_half (n : ℕ) [NeZero n] :
    ModelWithCorners ℝ (EuclideanSpace ℝ (Fin n)) (EuclideanHalfSpace n) :=
  modelWithCornersEuclideanHalfSpace n

variable [T2Space M] [CompactSpace M]

open DifferentialGeometry.Integral.Measure

private local instance : MeasurableSpace M := borel M
private local instance : BorelSpace M := ⟨rfl⟩

def dirichletLaplacianDomain
    (g : SmoothRiemannianMetric (I_half n) M) :
    Submodule ℝ (H1ComplDirichlet g) :=
  LinearMap.range (resolventDirichlet g).toLinearMap

lemma dirichletLaplacianDomain_mem_iff
    (g : SmoothRiemannianMetric (I_half n) M) {u : H1ComplDirichlet g} :
    u ∈ dirichletLaplacianDomain g ↔
      ∃ f : Lp ℝ 2 (riemannianVolumeMeasure (I := I_half n) (M := M) g),
        u = resolventDirichlet g f := by
  unfold dirichletLaplacianDomain
  rw [LinearMap.mem_range]
  constructor
  · rintro ⟨f, hf⟩
    exact ⟨f, hf.symm⟩
  · rintro ⟨f, hf⟩
    exact ⟨f, hf.symm⟩

def dirichletResolventEquiv
    (g : SmoothRiemannianMetric (I_half n) M) :
    Lp ℝ 2 (riemannianVolumeMeasure (I := I_half n) (M := M) g) ≃ₗ[ℝ]
      dirichletLaplacianDomain g :=
  LinearEquiv.ofInjective (resolventDirichlet g).toLinearMap
    (resolventDirichlet_injective g)

@[simp] theorem dirichletResolventEquiv_apply
    (g : SmoothRiemannianMetric (I_half n) M)
    (f : Lp ℝ 2 (riemannianVolumeMeasure (I := I_half n) (M := M) g)) :
    (dirichletResolventEquiv g f : H1ComplDirichlet g) =
      resolventDirichlet g f := rfl

@[simp] theorem resolventDirichlet_dirichletResolventEquiv_symm
    (g : SmoothRiemannianMetric (I_half n) M)
    (u : dirichletLaplacianDomain g) :
    resolventDirichlet g ((dirichletResolventEquiv g).symm u) =
      (u : H1ComplDirichlet g) :=
  LinearEquiv.ofInjective_symm_apply _ _

def dirichletLaplacian
    (g : SmoothRiemannianMetric (I_half n) M) :
    dirichletLaplacianDomain g →ₗ[ℝ]
      Lp ℝ 2 (riemannianVolumeMeasure (I := I_half n) (M := M) g) :=
  ((H1ComplDirichletToLp g).toLinearMap.comp
    (dirichletLaplacianDomain g).subtype) -
  (dirichletResolventEquiv g).symm.toLinearMap

@[simp] lemma dirichletLaplacian_apply
    (g : SmoothRiemannianMetric (I_half n) M)
    (u : dirichletLaplacianDomain g) :
    dirichletLaplacian g u =
      H1ComplDirichletToLp g (u : H1ComplDirichlet g) -
        (dirichletResolventEquiv g).symm u := by
  unfold dirichletLaplacian
  rw [LinearMap.sub_apply]
  rfl

theorem dirichletLaplacian_resolvent
    (g : SmoothRiemannianMetric (I_half n) M)
    (f : Lp ℝ 2 (riemannianVolumeMeasure (I := I_half n) (M := M) g)) :
    dirichletLaplacian g
        ⟨resolventDirichlet g f,
          (dirichletLaplacianDomain_mem_iff g).mpr ⟨f, rfl⟩⟩ =
      H1ComplDirichletToLp g (resolventDirichlet g f) - f := by
  rw [dirichletLaplacian_apply]
  have hpreimage :
      (dirichletResolventEquiv g).symm
          ⟨resolventDirichlet g f,
            (dirichletLaplacianDomain_mem_iff g).mpr ⟨f, rfl⟩⟩ = f := by
    apply resolventDirichlet_injective g
    rw [resolventDirichlet_dirichletResolventEquiv_symm]
  rw [hpreimage]

lemma smoothToH1ComplDirichlet_mem_dirichletLaplacianDomain
    {g : SmoothRiemannianMetric (I_half n) M}
    (u : SmoothScalarDirichlet g) :
    smoothToH1ComplDirichlet g u ∈ dirichletLaplacianDomain g := by
  rw [dirichletLaplacianDomain_mem_iff]
  exact ⟨u.oneSubLapClassicalLp,
    smoothToH1ComplDirichlet_eq_resolventDirichlet_oneSubLap u⟩

theorem dirichletLaplacian_smoothToH1ComplDirichlet
    {g : SmoothRiemannianMetric (I_half n) M}
    (u : SmoothScalarDirichlet g) :
    dirichletLaplacian g
        ⟨smoothToH1ComplDirichlet g u,
          smoothToH1ComplDirichlet_mem_dirichletLaplacianDomain u⟩ =
      smoothToLpDirichlet g u - u.oneSubLapClassicalLp := by
  rw [show (⟨smoothToH1ComplDirichlet g u,
        smoothToH1ComplDirichlet_mem_dirichletLaplacianDomain u⟩ :
        dirichletLaplacianDomain g) =
      ⟨resolventDirichlet g u.oneSubLapClassicalLp,
        (dirichletLaplacianDomain_mem_iff g).mpr
          ⟨u.oneSubLapClassicalLp, rfl⟩⟩ from ?_]
  · rw [dirichletLaplacian_resolvent]
    rw [← smoothToH1ComplDirichlet_eq_resolventDirichlet_oneSubLap u]
    rw [H1ComplDirichletToLp_smoothToH1ComplDirichlet]
  · apply Subtype.ext
    exact smoothToH1ComplDirichlet_eq_resolventDirichlet_oneSubLap u

private lemma h1Inner_eq_lpInner_with_dirichletPreimage
    (g : SmoothRiemannianMetric (I_half n) M)
    (u v : dirichletLaplacianDomain g) :
    ⟪(u : H1ComplDirichlet g), (v : H1ComplDirichlet g)⟫_ℝ =
      ⟪H1ComplDirichletToLp g (v : H1ComplDirichlet g),
        (dirichletResolventEquiv g).symm u⟫_ℝ := by
  have hu : (u : H1ComplDirichlet g) =
      resolventDirichlet g ((dirichletResolventEquiv g).symm u) :=
    (resolventDirichlet_dirichletResolventEquiv_symm g u).symm
  rw [hu]
  exact resolventDirichlet_inner_eq_lpFunctional g
    ((dirichletResolventEquiv g).symm u) (v : H1ComplDirichlet g)

private lemma lpInner_dirichletPreimage_swap
    (g : SmoothRiemannianMetric (I_half n) M)
    (u v : dirichletLaplacianDomain g) :
    ⟪H1ComplDirichletToLp g (v : H1ComplDirichlet g),
        (dirichletResolventEquiv g).symm u⟫_ℝ =
      ⟪H1ComplDirichletToLp g (u : H1ComplDirichlet g),
        (dirichletResolventEquiv g).symm v⟫_ℝ := by
  rw [← h1Inner_eq_lpInner_with_dirichletPreimage g u v]
  rw [← h1Inner_eq_lpInner_with_dirichletPreimage g v u]
  exact real_inner_comm _ _

theorem dirichletLaplacian_symmetric
    (g : SmoothRiemannianMetric (I_half n) M)
    (u v : dirichletLaplacianDomain g) :
    ⟪H1ComplDirichletToLp g (u : H1ComplDirichlet g),
        dirichletLaplacian g v⟫_ℝ =
      ⟪dirichletLaplacian g u,
        H1ComplDirichletToLp g (v : H1ComplDirichlet g)⟫_ℝ := by
  rw [dirichletLaplacian_apply, dirichletLaplacian_apply]
  rw [inner_sub_right, inner_sub_left]
  have hswap := lpInner_dirichletPreimage_swap g v u
  have hswap' :
      ⟪H1ComplDirichletToLp g (u : H1ComplDirichlet g),
          (dirichletResolventEquiv g).symm v⟫_ℝ =
        ⟪(dirichletResolventEquiv g).symm u,
          H1ComplDirichletToLp g (v : H1ComplDirichlet g)⟫_ℝ := by
    rw [hswap, real_inner_comm]
  linarith [hswap']

theorem inner_resolventDirichlet_oneSubLap
    (g : SmoothRiemannianMetric (I_half n) M)
    (f : Lp ℝ 2 (riemannianVolumeMeasure (I := I_half n) (M := M) g))
    (φ : SmoothScalarDirichlet g) :
    ⟪H1ComplDirichletToLp g (resolventDirichlet g f), φ.oneSubLapClassicalLp⟫_ℝ =
      ⟪f, smoothToLpDirichlet g φ⟫_ℝ := by
  rw [← resolventDirichlet_inner_eq_lpFunctional g φ.oneSubLapClassicalLp,
    ← smoothToH1ComplDirichlet_eq_resolventDirichlet_oneSubLap φ, real_inner_comm,
    resolventDirichlet_inner_eq_lpFunctional,
    H1ComplDirichletToLp_smoothToH1ComplDirichlet, real_inner_comm]

theorem dirichletLaplacian_inner_smooth
    (g : SmoothRiemannianMetric (I_half n) M)
    (u : dirichletLaplacianDomain g) (φ : SmoothScalarDirichlet g) :
    ⟪dirichletLaplacian g u, smoothToLpDirichlet g φ⟫_ℝ =
      ⟪H1ComplDirichletToLp g u,
        smoothToLpDirichlet g φ - φ.oneSubLapClassicalLp⟫_ℝ := by
  let v : dirichletLaplacianDomain g :=
    ⟨smoothToH1ComplDirichlet g φ,
      smoothToH1ComplDirichlet_mem_dirichletLaplacianDomain φ⟩
  have h := dirichletLaplacian_symmetric g u v
  rw [show H1ComplDirichletToLp g (v : H1ComplDirichlet g) =
      smoothToLpDirichlet g φ from
        H1ComplDirichletToLp_smoothToH1ComplDirichlet g φ,
    show dirichletLaplacian g v =
      smoothToLpDirichlet g φ - φ.oneSubLapClassicalLp from
        dirichletLaplacian_smoothToH1ComplDirichlet φ] at h
  exact h.symm

theorem integral_resolventDirichlet_oneSubLap
    (g : SmoothRiemannianMetric (I_half n) M)
    (f : Lp ℝ 2 (riemannianVolumeMeasure (I := I_half n) (M := M) g))
    (φ : SmoothScalarDirichlet g) :
    (∫ x, H1ComplDirichletToLp g (resolventDirichlet g f) x *
        (φ.toFun x - DifferentialGeometry.Geometry.Operator.WithBoundary.ΔGWithBoundary
          (I := I_half n) g φ.smooth φ.interior_support x)
      ∂(riemannianVolumeMeasure (I := I_half n) (M := M) g)) =
      ∫ x, f x * φ.toFun x
        ∂(riemannianVolumeMeasure (I := I_half n) (M := M) g) := by
  have h := inner_resolventDirichlet_oneSubLap g f φ
  simp only [L2.inner_def, RCLike.inner_apply, conj_trivial] at h
  have hφ := MemLp.coeFn_toLp φ.memLp_two
  have hΔφ := MemLp.coeFn_toLp φ.oneSubLap_memLp
  calc
    _ = ∫ x, φ.oneSubLapClassicalLp x *
        H1ComplDirichletToLp g (resolventDirichlet g f) x
          ∂(riemannianVolumeMeasure (I := I_half n) (M := M) g) := by
      apply integral_congr_ae
      filter_upwards [hΔφ] with x hx
      change (φ.oneSubLapClassicalLp : M → ℝ) x = _ at hx
      rw [hx, mul_comm]
    _ = ∫ x, smoothToLpDirichlet g φ x * f x
        ∂(riemannianVolumeMeasure (I := I_half n) (M := M) g) := h
    _ = _ := by
      apply integral_congr_ae
      filter_upwards [hφ] with x hx
      change smoothToLpDirichlet g φ x = φ.toFun x at hx
      rw [hx, mul_comm]

theorem integral_dirichletLaplacian_mul_smooth
    (g : SmoothRiemannianMetric (I_half n) M)
    (u : dirichletLaplacianDomain g) (φ : SmoothScalarDirichlet g) :
    (∫ x, dirichletLaplacian g u x * φ.toFun x
      ∂(riemannianVolumeMeasure (I := I_half n) (M := M) g)) =
      ∫ x, H1ComplDirichletToLp g u x *
        DifferentialGeometry.Geometry.Operator.WithBoundary.ΔGWithBoundary
          (I := I_half n) g φ.smooth φ.interior_support x
        ∂(riemannianVolumeMeasure (I := I_half n) (M := M) g) := by
  have h := dirichletLaplacian_inner_smooth g u φ
  simp only [L2.inner_def, RCLike.inner_apply, conj_trivial] at h
  have hφ := MemLp.coeFn_toLp φ.memLp_two
  have hΔφ := MemLp.coeFn_toLp φ.oneSubLap_memLp
  calc
    _ = ∫ x, smoothToLpDirichlet g φ x * dirichletLaplacian g u x
        ∂(riemannianVolumeMeasure (I := I_half n) (M := M) g) := by
      apply integral_congr_ae
      filter_upwards [hφ] with x hx
      change smoothToLpDirichlet g φ x = φ.toFun x at hx
      rw [hx, mul_comm]
    _ = ∫ x, (smoothToLpDirichlet g φ - φ.oneSubLapClassicalLp) x *
        H1ComplDirichletToLp g u x
          ∂(riemannianVolumeMeasure (I := I_half n) (M := M) g) := h
    _ = _ := by
      apply integral_congr_ae
      filter_upwards [Lp.coeFn_sub (smoothToLpDirichlet g φ) φ.oneSubLapClassicalLp,
        hφ, hΔφ] with x hsub hx hΔx
      change smoothToLpDirichlet g φ x = φ.toFun x at hx
      change (φ.oneSubLapClassicalLp : M → ℝ) x = _ at hΔx
      rw [hsub, Pi.sub_apply, hx, hΔx]
      ring

end Dirichlet
end WithBoundary
end Laplacian
end Analysis
end DifferentialGeometry

end
