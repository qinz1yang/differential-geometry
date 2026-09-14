import DifferentialGeometry.Geometry.Flow.RicciFlow.Extinction.CurveShortening.CalculusGeometry
import DifferentialGeometry.Geometry.Submanifold.SecondFundamentalForm.Pointwise
import DifferentialGeometry.Geometry.Curvature.Metric.Defs

set_option autoImplicit false

noncomputable section

open Bundle Function Manifold Set
open scoped ContDiff Manifold Topology

open DifferentialGeometry
open DifferentialGeometry.Geometry
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Geometry.IsRiemannianIsometricImmersion

namespace DifferentialGeometry.Geometry

variable {EN HN N E H M : Type*}
  [NormedAddCommGroup EN] [NormedSpace ℝ EN] [FiniteDimensional ℝ EN] [CompleteSpace EN]
  [TopologicalSpace HN] {IN : ModelWithCorners ℝ EN HN}
  [TopologicalSpace N] [ChartedSpace HN N] [IsManifold IN ∞ N]
  [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

def IsRiemannianIsometricImmersion.hasGaussEquation
    {gN : SmoothRiemannianMetric IN N} {gM : SmoothRiemannianMetric I M} {iota : N → M}
    (h : IsRiemannianIsometricImmersion gN gM iota) : Prop :=
  ∀ (x : N) (X Y Z W : TangentSpace IN x),
    metricRm04StandardAt gN x X Y Z W =
      metricRm04StandardAt gM (iota x)
        (mfderiv IN I iota x X) (mfderiv IN I iota x Y)
        (mfderiv IN I iota x Z) (mfderiv IN I iota x W) +
      gM.inner (iota x) (h.secondFundamentalFormAt x X W) (h.secondFundamentalFormAt x Y Z) -
      gM.inner (iota x) (h.secondFundamentalFormAt x X Z) (h.secondFundamentalFormAt x Y W)

theorem IsRiemannianIsometricImmersion.hasGaussEquation_id
    (g : SmoothRiemannianMetric I M) :
    (isRiemannianIsometricImmersion_id g).hasGaussEquation := by
  intro x X Y Z W
  have hzero : (isRiemannianIsometricImmersion_id g).secondFundamentalFormAt x = 0 :=
    hasVanishingSecondFundamentalForm_id g x
  rw [hzero]
  simp

theorem IsRiemannianIsometricImmersion.metricRm04StandardAt_eq_of_hasGaussEquation_of_hasVanishingSecondFundamentalForm
    {gN : SmoothRiemannianMetric IN N} {gM : SmoothRiemannianMetric I M} {iota : N → M}
    {h : IsRiemannianIsometricImmersion gN gM iota}
    (hgauss : h.hasGaussEquation) (hII : h.hasVanishingSecondFundamentalForm)
    (x : N) (X Y Z W : TangentSpace IN x) :
    metricRm04StandardAt gN x X Y Z W =
      metricRm04StandardAt gM (iota x)
        (mfderiv IN I iota x X) (mfderiv IN I iota x Y)
        (mfderiv IN I iota x Z) (mfderiv IN I iota x W) := by
  have h1 := hgauss x X Y Z W
  rw [hII x] at h1
  simpa using h1

end DifferentialGeometry.Geometry

namespace DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [CompleteSpace E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

def hasAmbientGaussEquation {m : ℕ} (U : TopologicalSpace.Opens (EuclideanSpace ℝ (Fin m)))
    (F : EuclideanSpace ℝ (Fin m) → M) (g : SmoothRiemannianMetric I M)
    (h : SmoothRiemannianMetric 𝓘(ℝ, EuclideanSpace ℝ (Fin m)) U) : Prop :=
  ∀ (x : U) (X Y Z W : EuclideanSpace ℝ (Fin m)),
    metricRm04StandardAt h x X Y Z W =
      metricRm04StandardAt g (F x)
        (mfderiv 𝓘(ℝ, EuclideanSpace ℝ (Fin m)) I F x X)
        (mfderiv 𝓘(ℝ, EuclideanSpace ℝ (Fin m)) I F x Y)
        (mfderiv 𝓘(ℝ, EuclideanSpace ℝ (Fin m)) I F x Z)
        (mfderiv 𝓘(ℝ, EuclideanSpace ℝ (Fin m)) I F x W) +
      g.inner (F x) (secondFundamentalFormAmbientAt h g (fun y : U => F y) x X W)
        (secondFundamentalFormAmbientAt h g (fun y : U => F y) x Y Z) -
      g.inner (F x) (secondFundamentalFormAmbientAt h g (fun y : U => F y) x X Z)
        (secondFundamentalFormAmbientAt h g (fun y : U => F y) x Y W)

def immersionSecondFundamental_eq_secondFundamentalFormAmbientAt {m : ℕ}
    (U : TopologicalSpace.Opens (EuclideanSpace ℝ (Fin m)))
    (F : EuclideanSpace ℝ (Fin m) → M) (g : SmoothRiemannianMetric I M)
    (h : SmoothRiemannianMetric 𝓘(ℝ, EuclideanSpace ℝ (Fin m)) U) : Prop :=
  ∀ (x : U) (X Y : EuclideanSpace ℝ (Fin m)),
    immersionSecondFundamental U F g h x X Y =
      secondFundamentalFormAmbientAt h g (fun y : U => F y) x X Y

theorem local_immersion_gauss_of_hasAmbientGaussEquation
    {m : ℕ} (U : TopologicalSpace.Opens (EuclideanSpace ℝ (Fin m)))
    (F : EuclideanSpace ℝ (Fin m) → M) (g : SmoothRiemannianMetric I M)
    (h : SmoothRiemannianMetric 𝓘(ℝ, EuclideanSpace ℝ (Fin m)) U)
    (hgauss : hasAmbientGaussEquation U F g h)
    (hdef : immersionSecondFundamental_eq_secondFundamentalFormAmbientAt U F g h)
    (x : U) (X Y Z W : EuclideanSpace ℝ (Fin m)) :
    metricRm04StandardAt h x X Y Z W =
      metricRm04StandardAt g (F x)
        (mfderiv 𝓘(ℝ, EuclideanSpace ℝ (Fin m)) I F x X)
        (mfderiv 𝓘(ℝ, EuclideanSpace ℝ (Fin m)) I F x Y)
        (mfderiv 𝓘(ℝ, EuclideanSpace ℝ (Fin m)) I F x Z)
        (mfderiv 𝓘(ℝ, EuclideanSpace ℝ (Fin m)) I F x W) +
      g.inner (F x) (immersionSecondFundamental U F g h x X W)
        (immersionSecondFundamental U F g h x Y Z) -
      g.inner (F x) (immersionSecondFundamental U F g h x X Z)
        (immersionSecondFundamental U F g h x Y W) := by
  have h1 := hgauss x X Y Z W
  rw [← hdef x X W, ← hdef x Y Z, ← hdef x X Z, ← hdef x Y W] at h1
  exact h1

theorem local_immersion_gauss_of_hasGaussEquation
    [I.Boundaryless]
    {m : ℕ} (U : TopologicalSpace.Opens (EuclideanSpace ℝ (Fin m)))
    (F : EuclideanSpace ℝ (Fin m) → M)
    (hF : ContMDiffOn 𝓘(ℝ, EuclideanSpace ℝ (Fin m)) I ∞ F U)
    (g : SmoothRiemannianMetric I M)
    (h : SmoothRiemannianMetric 𝓘(ℝ, EuclideanSpace ℝ (Fin m)) U)
    (himmersion : IsRiemannianIsometricImmersion h g (fun y : U => F y))
    (hgauss : himmersion.hasGaussEquation)
    (hdef : immersionSecondFundamental_eq_secondFundamentalFormAmbientAt U F g h)
    (x : U) (X Y Z W : EuclideanSpace ℝ (Fin m)) :
    metricRm04StandardAt h x X Y Z W =
      metricRm04StandardAt g (F x)
        (mfderiv 𝓘(ℝ, EuclideanSpace ℝ (Fin m)) I F x X)
        (mfderiv 𝓘(ℝ, EuclideanSpace ℝ (Fin m)) I F x Y)
        (mfderiv 𝓘(ℝ, EuclideanSpace ℝ (Fin m)) I F x Z)
        (mfderiv 𝓘(ℝ, EuclideanSpace ℝ (Fin m)) I F x W) +
      g.inner (F x) (immersionSecondFundamental U F g h x X W)
        (immersionSecondFundamental U F g h x Y Z) -
      g.inner (F x) (immersionSecondFundamental U F g h x X Z)
        (immersionSecondFundamental U F g h x Y W) := by
  have hmf : ∀ y : U, mfderiv 𝓘(ℝ, EuclideanSpace ℝ (Fin m)) I (fun z : U => F z) y =
      mfderiv 𝓘(ℝ, EuclideanSpace ℝ (Fin m)) I F ↑y := by
    intro y
    have hy : MDifferentiableAt 𝓘(ℝ, EuclideanSpace ℝ (Fin m)) I F ↑y :=
      ((hF y y.2).mdifferentiableWithinAt (by norm_num)).mdifferentiableAt (U.2.mem_nhds y.2)
    have hs : MDifferentiableAt 𝓘(ℝ, EuclideanSpace ℝ (Fin m))
        𝓘(ℝ, EuclideanSpace ℝ (Fin m)) (Subtype.val : U → EuclideanSpace ℝ (Fin m)) y :=
      (contMDiff_subtype_val (I := 𝓘(ℝ, EuclideanSpace ℝ (Fin m))) (U := U) (n := ∞)).mdifferentiable
        (by simp) y
    have hcomp := mfderiv_comp (I := 𝓘(ℝ, EuclideanSpace ℝ (Fin m)))
      (I' := 𝓘(ℝ, EuclideanSpace ℝ (Fin m))) (I'' := I) y hy hs
    rw [mfderiv_subtype_val (I := 𝓘(ℝ, EuclideanSpace ℝ (Fin m))) U y] at hcomp
    apply ContinuousLinearMap.ext
    intro v
    have h := congrArg (fun L : EuclideanSpace ℝ (Fin m) →L[ℝ] TangentSpace I (F ↑y) => L v) hcomp
    exact h.trans (by rfl)
  refine local_immersion_gauss_of_hasAmbientGaussEquation U F g h ?_ hdef x X Y Z W
  intro x' X' Y' Z' W'
  have h1 := hgauss x' X' Y' Z' W'
  rw [hmf x', secondFundamentalFormAt_coe_eq_ambient himmersion x' X' W',
    secondFundamentalFormAt_coe_eq_ambient himmersion x' Y' Z',
    secondFundamentalFormAt_coe_eq_ambient himmersion x' X' Z',
    secondFundamentalFormAt_coe_eq_ambient himmersion x' Y' W'] at h1
  exact h1

end DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening
