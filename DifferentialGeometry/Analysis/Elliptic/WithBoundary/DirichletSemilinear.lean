import DifferentialGeometry.Analysis.Calculus.RegularizedExp
import DifferentialGeometry.Analysis.Elliptic.WithBoundary.DirichletWeightedResolvent
import Mathlib.Topology.MetricSpace.Contracting

noncomputable section

set_option autoImplicit false

namespace DifferentialGeometry.Analysis.Laplacian.WithBoundary.Dirichlet

open MeasureTheory
open scoped Manifold ContDiff ENNReal NNReal
open DifferentialGeometry.Integral.Measure

variable {n : ℕ} [NeZero n]
variable {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanHalfSpace n) M]
  [IsManifold (modelWithCornersEuclideanHalfSpace n) ∞ M]
  [T2Space M] [CompactSpace M]

private local instance : MeasurableSpace M := borel M
private local instance : BorelSpace M := ⟨rfl⟩

theorem exists_dirichlet_semilinear_solution_of_lipschitz
    (g : SmoothRiemannianMetric (modelWithCornersEuclideanHalfSpace n) M)
    (τ : ℝ) (hτ : 0 < τ)
    {F : ℝ → ℝ} {L : ℝ≥0} (hF : LipschitzWith L F) (hFzero : F 0 = 0)
    (hL : L < 1)
    (f : Lp ℝ 2 (riemannianVolumeMeasure (I := modelWithCornersEuclideanHalfSpace n) (M := M) g)) :
    ∃ u : dirichletLaplacianDomain g,
      τ • dirichletLaplacian g u =
        H1ComplDirichletToLp g (u : H1ComplDirichlet g) +
          hF.compLp hFzero (H1ComplDirichletToLp g (u : H1ComplDirichlet g)) - f := by
  let N : Lp ℝ 2 (riemannianVolumeMeasure (I := modelWithCornersEuclideanHalfSpace n) (M := M) g) →
      Lp ℝ 2 (riemannianVolumeMeasure (I := modelWithCornersEuclideanHalfSpace n) (M := M) g) := hF.compLp hFzero
  let Ψ : Lp ℝ 2 (riemannianVolumeMeasure (I := modelWithCornersEuclideanHalfSpace n) (M := M) g) →
      Lp ℝ 2 (riemannianVolumeMeasure (I := modelWithCornersEuclideanHalfSpace n) (M := M) g) := fun u => weightedResolventDirichletL2 g τ hτ (f - N u)
  have hN : LipschitzWith L N := hF.lipschitzWith_compLp hFzero
  have hΨ : LipschitzWith L Ψ := by
    apply LipschitzWith.of_dist_le_mul
    intro u v
    calc
      dist (Ψ u) (Ψ v) ≤ 1 * dist (f - N u) (f - N v) := (weightedResolventDirichletL2_lipschitzWith g τ hτ).dist_le_mul _ _
      _ = dist (N u) (N v) := by rw [one_mul, dist_sub_left]
      _ ≤ L * dist u v := hN.dist_le_mul u v
  have hcon : ContractingWith L Ψ := ⟨hL, hΨ⟩
  let u₀ := ContractingWith.fixedPoint Ψ hcon
  have hfix : Ψ u₀ = u₀ := ContractingWith.fixedPoint_isFixedPt hcon
  let u : dirichletLaplacianDomain g :=
    ⟨weightedResolventDirichlet g τ hτ (f - N u₀),
      weightedResolventDirichlet_mem_dirichletLaplacianDomain g τ hτ (f - N u₀)⟩
  have hu : H1ComplDirichletToLp g (u : H1ComplDirichlet g) = u₀ := hfix
  refine ⟨u, ?_⟩
  change τ • dirichletLaplacian g
    ⟨weightedResolventDirichlet g τ hτ (f - N u₀), _⟩ = _
  rw [smul_dirichletLaplacian_weightedResolventDirichlet]
  change H1ComplDirichletToLp g (u : H1ComplDirichlet g) - (f - N u₀) = _
  rw [hu]
  dsimp [N]
  abel

private theorem resolventDirichletL2_fixedPoint_of_semilinear_solution
    (g : SmoothRiemannianMetric (modelWithCornersEuclideanHalfSpace n) M)
    (τ : ℝ) (hτ : 0 < τ)
    {F : ℝ → ℝ} {L : ℝ≥0} (hF : LipschitzWith L F) (hFzero : F 0 = 0)
    (f : Lp ℝ 2 (riemannianVolumeMeasure (I := modelWithCornersEuclideanHalfSpace n) (M := M) g))
    (u : dirichletLaplacianDomain g)
    (hu : τ • dirichletLaplacian g u =
      H1ComplDirichletToLp g (u : H1ComplDirichlet g) +
        hF.compLp hFzero (H1ComplDirichletToLp g (u : H1ComplDirichlet g)) - f) :
    weightedResolventDirichletL2 g τ hτ
      (f - hF.compLp hFzero (H1ComplDirichletToLp g (u : H1ComplDirichlet g))) =
      H1ComplDirichletToLp g (u : H1ComplDirichlet g) := by
  have heq : H1ComplDirichletToLp g (u : H1ComplDirichlet g) -
      τ • dirichletLaplacian g u =
      f - hF.compLp hFzero (H1ComplDirichletToLp g (u : H1ComplDirichlet g)) := by
    rw [hu]
    abel
  change H1ComplDirichletToLp g (weightedResolventDirichlet g τ hτ
      (f - hF.compLp hFzero (H1ComplDirichletToLp g (u : H1ComplDirichlet g)))) = _
  rw [← heq, weightedResolventDirichlet_oneSub_smul_dirichletLaplacian]

theorem dirichlet_semilinear_solution_unique_of_lipschitz
    (g : SmoothRiemannianMetric (modelWithCornersEuclideanHalfSpace n) M)
    (τ : ℝ) (hτ : 0 < τ)
    {F : ℝ → ℝ} {L : ℝ≥0} (hF : LipschitzWith L F) (hFzero : F 0 = 0)
    (hL : L < 1)
    (f : Lp ℝ 2 (riemannianVolumeMeasure (I := modelWithCornersEuclideanHalfSpace n) (M := M) g))
    (u v : dirichletLaplacianDomain g)
    (hu : τ • dirichletLaplacian g u =
      H1ComplDirichletToLp g (u : H1ComplDirichlet g) +
        hF.compLp hFzero (H1ComplDirichletToLp g (u : H1ComplDirichlet g)) - f)
    (hv : τ • dirichletLaplacian g v =
      H1ComplDirichletToLp g (v : H1ComplDirichlet g) +
        hF.compLp hFzero (H1ComplDirichletToLp g (v : H1ComplDirichlet g)) - f) :
    u = v := by
  let U := H1ComplDirichletToLp g (u : H1ComplDirichlet g)
  let V := H1ComplDirichletToLp g (v : H1ComplDirichlet g)
  let N : Lp ℝ 2 (riemannianVolumeMeasure (I := modelWithCornersEuclideanHalfSpace n) (M := M) g) →
      Lp ℝ 2 (riemannianVolumeMeasure (I := modelWithCornersEuclideanHalfSpace n) (M := M) g) := hF.compLp hFzero
  have hfu := resolventDirichletL2_fixedPoint_of_semilinear_solution g τ hτ hF hFzero f u hu
  have hfv := resolventDirichletL2_fixedPoint_of_semilinear_solution g τ hτ hF hFzero f v hv
  have hdist : dist U V ≤ L * dist U V := by
    calc
      dist U V = dist (weightedResolventDirichletL2 g τ hτ (f - N U))
          (weightedResolventDirichletL2 g τ hτ (f - N V)) := by rw [hfu, hfv]
      _ ≤ 1 * dist (f - N U) (f - N V) :=
        (weightedResolventDirichletL2_lipschitzWith g τ hτ).dist_le_mul _ _
      _ = dist (N U) (N V) := by rw [one_mul, dist_sub_left]
      _ ≤ L * dist U V := (hF.lipschitzWith_compLp hFzero).dist_le_mul U V
  have hUV : U = V := by
    apply dist_eq_zero.mp
    have hL' : (L : ℝ) < 1 := hL
    nlinarith [dist_nonneg (x := U) (y := V)]
  apply Subtype.ext
  rw [← weightedResolventDirichlet_oneSub_smul_dirichletLaplacian g τ hτ u,
    ← weightedResolventDirichlet_oneSub_smul_dirichletLaplacian g τ hτ v, hu, hv]
  change weightedResolventDirichlet g τ hτ (U - (U + N U - f)) =
    weightedResolventDirichlet g τ hτ (V - (V + N V - f))
  rw [hUV]

theorem exists_unique_dirichlet_semilinear_solution_of_lipschitz
    (g : SmoothRiemannianMetric (modelWithCornersEuclideanHalfSpace n) M)
    (τ : ℝ) (hτ : 0 < τ)
    {F : ℝ → ℝ} {L : ℝ≥0} (hF : LipschitzWith L F) (hFzero : F 0 = 0)
    (hL : L < 1)
    (f : Lp ℝ 2 (riemannianVolumeMeasure (I := modelWithCornersEuclideanHalfSpace n) (M := M) g)) :
    ∃! u : dirichletLaplacianDomain g,
      τ • dirichletLaplacian g u =
        H1ComplDirichletToLp g (u : H1ComplDirichlet g) +
          hF.compLp hFzero (H1ComplDirichletToLp g (u : H1ComplDirichlet g)) - f := by
  obtain ⟨u, hu⟩ := exists_dirichlet_semilinear_solution_of_lipschitz g τ hτ hF hFzero hL f
  exact ⟨u, hu, fun v hv => dirichlet_semilinear_solution_unique_of_lipschitz
    g τ hτ hF hFzero hL f v u hv hu⟩

end DifferentialGeometry.Analysis.Laplacian.WithBoundary.Dirichlet

end

noncomputable section

namespace DifferentialGeometry.Analysis.Laplacian.WithBoundary.Dirichlet

open MeasureTheory Filter
open scoped Manifold ContDiff ENNReal NNReal
open DifferentialGeometry.Integral.Measure

variable {n : ℕ} [NeZero n]
variable {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanHalfSpace n) M]
  [IsManifold (modelWithCornersEuclideanHalfSpace n) ∞ M]
  [T2Space M] [CompactSpace M]

private local instance : MeasurableSpace M := borel M
private local instance : BorelSpace M := ⟨rfl⟩

theorem exists_regularizedExp_dirichlet_solution
    (g : SmoothRiemannianMetric (modelWithCornersEuclideanHalfSpace n) M)
    (τ : ℝ) (hτ : 0 < τ)
    (f : Lp ℝ 2 (riemannianVolumeMeasure (I := modelWithCornersEuclideanHalfSpace n) (M := M) g)) :
    ∃ u : dirichletLaplacianDomain g,
      (fun x => Real.regularizedExp (H1ComplDirichletToLp g (u : H1ComplDirichlet g) x) -
        1 - τ * dirichletLaplacian g u x) =ᵐ[riemannianVolumeMeasure (I := modelWithCornersEuclideanHalfSpace n) (M := M) g] f := by
  have hzero : (fun r : ℝ => Real.regularizedExp r - 1 - r) 0 = 0 := by simp
  obtain ⟨u, hu⟩ := exists_dirichlet_semilinear_solution_of_lipschitz g τ hτ
    Real.regularizedExp_sub_one_sub_lipschitzWith hzero (by norm_num) f
  refine ⟨u, ?_⟩
  let U := H1ComplDirichletToLp g (u : H1ComplDirichlet g)
  let N := Real.regularizedExp_sub_one_sub_lipschitzWith.compLp hzero U
  have hN := Real.regularizedExp_sub_one_sub_lipschitzWith.coeFn_compLp hzero U
  have hsum := Lp.coeFn_add U N
  have hsub := Lp.coeFn_sub (U + N) f
  filter_upwards [hN, hsum, hsub, Lp.coeFn_smul τ (dirichletLaplacian g u)] with x hxN hxsum hxsub hxsmul
  have heq := congrArg (fun a : Lp ℝ 2
    (riemannianVolumeMeasure (I := modelWithCornersEuclideanHalfSpace n) (M := M) g) => a x) hu
  change (τ • dirichletLaplacian g u) x = (U + N - f) x at heq
  rw [hxsmul] at heq
  rw [hxsub] at heq
  change τ * dirichletLaplacian g u x = (U + N) x - f x at heq
  rw [hxsum] at heq
  change τ * dirichletLaplacian g u x = U x + N x - f x at heq
  change N x = Real.regularizedExp (U x) - 1 - U x at hxN
  change Real.regularizedExp (U x) - 1 - τ * dirichletLaplacian g u x = f x
  rw [heq, hxN]
  ring

end DifferentialGeometry.Analysis.Laplacian.WithBoundary.Dirichlet

end
