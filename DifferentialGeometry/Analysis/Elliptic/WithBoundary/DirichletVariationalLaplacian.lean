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

def dirichletLaplacianDomain.preimage
    (g : SmoothRiemannianMetric (I_half n) M)
    (u : dirichletLaplacianDomain g) :
    Lp ℝ 2 (riemannianVolumeMeasure (I := I_half n) (M := M) g) :=
  Classical.choose ((dirichletLaplacianDomain_mem_iff g).mp u.2)

@[simp] lemma resolventDirichlet_preimage_eq
    (g : SmoothRiemannianMetric (I_half n) M)
    (u : dirichletLaplacianDomain g) :
    resolventDirichlet g (dirichletLaplacianDomain.preimage g u) =
      (u : H1ComplDirichlet g) :=
  (Classical.choose_spec ((dirichletLaplacianDomain_mem_iff g).mp u.2)).symm

lemma dirichletLaplacianDomain_preimage_zero
    (g : SmoothRiemannianMetric (I_half n) M) :
    dirichletLaplacianDomain.preimage g
      (0 : dirichletLaplacianDomain g) = 0 := by
  apply resolventDirichlet_injective g
  rw [resolventDirichlet_preimage_eq]
  rw [(resolventDirichlet g).map_zero]
  rfl

lemma dirichletLaplacianDomain_preimage_add
    (g : SmoothRiemannianMetric (I_half n) M)
    (u v : dirichletLaplacianDomain g) :
    dirichletLaplacianDomain.preimage g (u + v) =
      dirichletLaplacianDomain.preimage g u +
        dirichletLaplacianDomain.preimage g v := by
  apply resolventDirichlet_injective g
  rw [resolventDirichlet_preimage_eq]
  rw [(resolventDirichlet g).map_add]
  rw [resolventDirichlet_preimage_eq, resolventDirichlet_preimage_eq]
  rfl

lemma dirichletLaplacianDomain_preimage_smul
    (g : SmoothRiemannianMetric (I_half n) M)
    (c : ℝ) (u : dirichletLaplacianDomain g) :
    dirichletLaplacianDomain.preimage g (c • u) =
      c • dirichletLaplacianDomain.preimage g u := by
  apply resolventDirichlet_injective g
  rw [resolventDirichlet_preimage_eq]
  rw [(resolventDirichlet g).map_smul]
  rw [resolventDirichlet_preimage_eq]
  rfl

def dirichletLaplacianDomain.preimageLin
    (g : SmoothRiemannianMetric (I_half n) M) :
    dirichletLaplacianDomain g →ₗ[ℝ]
      Lp ℝ 2 (riemannianVolumeMeasure (I := I_half n) (M := M) g) where
  toFun := dirichletLaplacianDomain.preimage g
  map_add' := dirichletLaplacianDomain_preimage_add g
  map_smul' c u := dirichletLaplacianDomain_preimage_smul g c u

def dirichletLaplacian
    (g : SmoothRiemannianMetric (I_half n) M) :
    dirichletLaplacianDomain g →ₗ[ℝ]
      Lp ℝ 2 (riemannianVolumeMeasure (I := I_half n) (M := M) g) :=
  ((H1ComplDirichletToLp g).toLinearMap.comp
    (dirichletLaplacianDomain g).subtype) -
  dirichletLaplacianDomain.preimageLin g

@[simp] lemma dirichletLaplacian_apply
    (g : SmoothRiemannianMetric (I_half n) M)
    (u : dirichletLaplacianDomain g) :
    dirichletLaplacian g u =
      H1ComplDirichletToLp g (u : H1ComplDirichlet g) -
        dirichletLaplacianDomain.preimage g u := by
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
      dirichletLaplacianDomain.preimage g
          ⟨resolventDirichlet g f,
            (dirichletLaplacianDomain_mem_iff g).mpr ⟨f, rfl⟩⟩ = f := by
    apply resolventDirichlet_injective g
    rw [resolventDirichlet_preimage_eq]
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
        dirichletLaplacianDomain.preimage g u⟫_ℝ := by
  have hu : (u : H1ComplDirichlet g) =
      resolventDirichlet g (dirichletLaplacianDomain.preimage g u) :=
    (resolventDirichlet_preimage_eq g u).symm
  rw [hu]
  exact resolventDirichlet_inner_eq_lpFunctional g
    (dirichletLaplacianDomain.preimage g u) (v : H1ComplDirichlet g)

private lemma lpInner_dirichletPreimage_swap
    (g : SmoothRiemannianMetric (I_half n) M)
    (u v : dirichletLaplacianDomain g) :
    ⟪H1ComplDirichletToLp g (v : H1ComplDirichlet g),
        dirichletLaplacianDomain.preimage g u⟫_ℝ =
      ⟪H1ComplDirichletToLp g (u : H1ComplDirichlet g),
        dirichletLaplacianDomain.preimage g v⟫_ℝ := by
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
          dirichletLaplacianDomain.preimage g v⟫_ℝ =
        ⟪dirichletLaplacianDomain.preimage g u,
          H1ComplDirichletToLp g (v : H1ComplDirichlet g)⟫_ℝ := by
    rw [hswap, real_inner_comm]
  linarith [hswap']

end Dirichlet
end WithBoundary
end Laplacian
end Analysis
end DifferentialGeometry

end
