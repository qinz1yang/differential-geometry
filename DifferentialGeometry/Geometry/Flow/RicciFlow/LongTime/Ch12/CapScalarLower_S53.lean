import DifferentialGeometry.Geometry.Flow.RicciFlow.Extinction.Families.SlabScalarLowerBarrier
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.StandardCap.InitialWindowBounds
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.HistorySurvivorIncoming
import DifferentialGeometry.Geometry.Curvature.OpenEmbeddingPullback
import DifferentialGeometry.Geometry.Metric.OpenEmbeddingPullback

/-!
# CH12-S53, group 1: the ODE part of `q/4 ≤ R` on a flowed cap

* `scalar_ge_of_lapR_S53`: along a smooth Ricci-flow solution on `[0, T]`, if
  `|Δ R| ≤ c √(|∇² Rm|²)` at a fixed point `y` and `|∇² Rm|² ≤ B` there, then
  `R(T, y) ≥ R(0, y) - c √B T` (from `∂ₜ R = Δ R + 2 |Ric|²` and `|Ric|² ≥ 0`).
* `scalar_eq_of_scaled_inner_local_S53`: scalar curvature of a metric which is the `q`-scaled
  pullback of `h` under an injective local diffeomorphism.
-/

set_option autoImplicit false

noncomputable section

open Set Filter
open DifferentialGeometry DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Geometry.Riemannian DifferentialGeometry.Geometry.Metric
open DifferentialGeometry.Topology.Manifold
open DifferentialGeometry.PDE.RicciFlow
open DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
open scoped Manifold ContDiff Topology

namespace GC.LongTime.Ch12

/-- The ODE comparison: `R(T) ≥ R(0) - c √B T`. -/
theorem scalar_ge_of_lapR_S53 {N : Type} [TopologicalSpace N] [ChartedSpace ThreeSpace N]
    [IsManifold ThreeModel ∞ N] [T2Space N] (c B T : ℝ) (hT : 0 ≤ T)
    (S : SolutionOn (I := ThreeModel) (M := N) (RealTimeInterval.closed 0 T hT))
    (hS : IsSolutionOn (I := ThreeModel) S) (y : N)
    (hlap : ∀ t ∈ Icc 0 T, |laplacianAt (I := ThreeModel) (flowG (I := ThreeModel) S) t
        (S.scalar t) y| ≤ c * Real.sqrt (CheegerGromovCompactness.curvDerivNormSq (I := ThreeModel)
          2 (S.base.metric t) y))
    (hB : ∀ t ∈ Icc 0 T, CheegerGromovCompactness.curvDerivNormSq (I := ThreeModel) 2
        (S.base.metric t) y ≤ B)
    (hc : 0 ≤ c) :
    S.scalar 0 y - c * Real.sqrt B * T ≤ S.scalar T y := by
  have hevol := scalarEvolutionEquationOn_of_isSolutionOn (I := ThreeModel) S hS
  set κ : ℝ := c * Real.sqrt B with hκ
  let g : ℝ → ℝ := fun t => S.scalar t y + κ * t
  have hcarr : (RealTimeInterval.closed 0 T hT).carrier = Icc 0 T := rfl
  have hcont : ContinuousOn g (Icc 0 T) := by
    have h1 : ContinuousOn (fun t : ℝ => S.scalar t y) (Icc 0 T) := by
      have h := hS.scalarCont.comp (f := fun t : ℝ => (t, y))
        (s := Icc 0 T) (by fun_prop) (fun t ht => ⟨ht, mem_univ _⟩)
      exact h
    exact h1.add (by fun_prop)
  have hderiv : ∀ t ∈ Ioo 0 T, HasDerivAt g
      (laplacianAt (I := ThreeModel) (flowG (I := ThreeModel) S) t (S.scalar t) y +
        2 * ricciNorm (I := ThreeModel) S t y + κ) t := by
    intro t ht
    have h := hevol ⟨t, ht⟩ y
    have h' : HasDerivAt (fun s : ℝ => S.scalar s y) _ t :=
      h.hasDerivAt (Icc_mem_nhds ht.1 ht.2)
    exact h'.add ((hasDerivAt_id t).const_mul κ |>.congr_deriv (by simp))
  have hmono : MonotoneOn g (Icc 0 T) := by
    apply monotoneOn_of_deriv_nonneg (convex_Icc 0 T) hcont
    · intro t ht
      rw [interior_Icc] at ht
      exact (hderiv t ht).differentiableAt.differentiableWithinAt
    · intro t ht
      rw [interior_Icc] at ht
      rw [(hderiv t ht).deriv]
      have hl := (abs_le.mp ((hlap t ⟨ht.1.le, ht.2.le⟩))).1
      have hs : c * Real.sqrt (CheegerGromovCompactness.curvDerivNormSq (I := ThreeModel) 2
          (S.base.metric t) y) ≤ κ := by
        rw [hκ]
        exact mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt (hB t ⟨ht.1.le, ht.2.le⟩)) hc
      have hric : 0 ≤ ricciNorm (I := ThreeModel) S t y := by
        have hfr : Module.finrank ℝ ThreeSpace = 3 := by simp [ThreeSpace]
        have h := ricciNorm_ge_scalar_sq_div_finrank (D := RealTimeInterval.closed 0 T hT) S t y
        rw [hfr] at h
        have : (0 : ℝ) ≤ (1 / ((3 : ℕ) : ℝ)) * S.scalar t y ^ 2 := by positivity
        linarith
      linarith
  have h := hmono ⟨le_rfl, hT⟩ ⟨hT, le_rfl⟩ hT
  simp only [g] at h
  linarith

/-- Scalar curvature of the `q`-scaled pullback of `h` under an injective local diffeomorphism. -/
theorem scalar_eq_of_scaled_inner_local_S53 {M N : Type*} [TopologicalSpace M]
    [ChartedSpace ThreeSpace M] [IsManifold ThreeModel ∞ M] [T2Space M] [SigmaCompactSpace M]
    [TopologicalSpace N] [ChartedSpace ThreeSpace N] [IsManifold ThreeModel ∞ N] [T2Space N]
    (gW : SmoothRiemannianMetric ThreeModel M) (h : SmoothRiemannianMetric ThreeModel N)
    (J : M → N) (hJ : IsLocalDiffeomorph ThreeModel ThreeModel ∞ J)
    (hinj : Function.Injective J) {q : ℝ} (hq : 0 < q)
    (hinner : ∀ x (v z : TangentSpace ThreeModel x), gW.inner x v z =
      q * h.inner (J x) (mfderiv ThreeModel ThreeModel J x v) (mfderiv ThreeModel ThreeModel J x z))
    (x : M) : metricScalarAt gW x = metricScalarAt h (J x) / q := by
  have heq : gW = pullbackMetricOfInjectiveLocalDiffeomorph (scaleMetric q hq h) J hJ hinj := by
    apply SmoothRiemannianMetric.ext_inner
    intro y v z
    rw [pullbackMetricOfInjectiveLocalDiffeomorph_inner, scaleMetric_inner]
    exact hinner y v z
  rw [heq]
  exact metricScalarAt_pullbackMetricOfInjectiveLocalDiffeomorph_scale h J hJ hinj q hq x

end GC.LongTime.Ch12
