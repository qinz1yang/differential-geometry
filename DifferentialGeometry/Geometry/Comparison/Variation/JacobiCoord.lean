import DifferentialGeometry.Geometry.Comparison.Variation.JacobiField
import DifferentialGeometry.Geometry.Comparison.Variation.FirstVariation
import DifferentialGeometry.Geometry.Metric.FiberExpansion
import DifferentialGeometry.Analysis.ODE.SecondOrderLinearExistence

set_option autoImplicit false
set_option linter.unusedSectionVars false

/-!
# Frame coordinates of a Jacobi field: derivative identities

Along a curve `γ`, pair a section `Y` against a **parallel** section `Fi`.
The scalar coordinate `t ↦ g.inner (γ t) (Fi t) (Y t)` then differentiates
without any curvature of `Fi` entering:

* first derivative — `g.inner (Fi t) (D_t Y t)` (metric compatibility plus
  parallelism kills the `g(D_t Fi, Y)` term);
* second derivative, when `Y` is Jacobi at `t` — `-g(Fi, R(Y, γ̇)γ̇)`
  (the Jacobi equation read through `jacobi_d2_eq`).

These are the scalar identities behind the frame-coordinate representation
`yᵢ'' = -(A t) y` of a Jacobi field in a parallel orthonormal frame — brick
"J-remaining" (uniqueness/representation) of the option-1 route in
`Geometry/Comparison/VOLUME_COMPARISON_PLAN.md`.  Existence of the comparison
solutions is `forward_ode2_of_bound`; the Grönwall closer is
`norm_le_gronwall_secondOrder`.
-/

open Set Function Manifold Bundle
open scoped Topology Manifold ContDiff

namespace DifferentialGeometry
namespace Geometry
namespace Riemannian
namespace Variation

open DifferentialGeometry.Geometry.Riemannian.AlongCurve
open DifferentialGeometry.Geometry.Riemannian.CovariantDerivativeAlong

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [I.Boundaryless]
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [T2Space M] [SigmaCompactSpace M]

/-- **Coordinate against a parallel section: first derivative.**  If `Fi` is
parallel at `t` and both chart representations differentiate, then
`s ↦ g.inner (γ s) (Fi s) (Y s)` has derivative
`g.inner (γ t) (Fi t) (D_t Y t)` at `t`. -/
theorem parInner_deriv
    {n : WithTop ℕ∞} (hn : 1 ≤ n)
    (g : SmoothRiemannianMetric I M) (γ : ℝ → M)
    (Fi Y : ∀ t : ℝ, TangentSpace I (γ t)) (t : ℝ)
    (hγ : ContMDiffAt 𝓘(ℝ, ℝ) I n γ t)
    (hFdiff : DifferentiableAt ℝ (chartRepAt (I := I) γ Fi t) t)
    (hYdiff : DifferentiableAt ℝ (chartRepAt (I := I) γ Y t) t)
    (hFpar : covDerivAlong (I := I) g γ Fi t = 0) :
    HasDerivAt (fun s : ℝ => g.inner (γ s) (Fi s) (Y s))
      (g.inner (γ t) (Fi t) (covDerivAlong (I := I) g γ Y t)) t := by
  have h := inner_deriv_at (I := I) hn g γ Fi Y t hγ hFdiff hYdiff
  rw [hFpar] at h
  simpa using h

/-- **Coordinate against a parallel section: second derivative through the
Jacobi equation.**  If additionally the chart representation of `D_t Y`
differentiates and `Y` is Jacobi at `t`, then
`s ↦ g.inner (γ s) (Fi s) (D_t Y s)` has derivative
`-g.inner (γ t) (Fi t) (R(Y t, γ̇)γ̇)` at `t`. -/
theorem parInner_d2
    {n : WithTop ℕ∞} (hn : 1 ≤ n)
    (g : SmoothRiemannianMetric I M) (γ : ℝ → M)
    (Fi Y : ∀ t : ℝ, TangentSpace I (γ t)) (t : ℝ)
    (hγ : ContMDiffAt 𝓘(ℝ, ℝ) I n γ t)
    (hFdiff : DifferentiableAt ℝ (chartRepAt (I := I) γ Fi t) t)
    (hDYdiff : DifferentiableAt ℝ
      (chartRepAt (I := I) γ
        (fun s : ℝ => covDerivAlong (I := I) g γ Y s) t) t)
    (hFpar : covDerivAlong (I := I) g γ Fi t = 0)
    (hY : IsJacobiAt (I := I) g γ Y t) :
    HasDerivAt
      (fun s : ℝ => g.inner (γ s) (Fi s) (covDerivAlong (I := I) g γ Y s))
      (- g.inner (γ t) (Fi t)
        ((DifferentialGeometry.Integral.Connection.riemannOp
            (DifferentialGeometry.Integral.Connection.LeviCivita (I := I) g)
            (γ t))
          (Y t) (curveVelocity (I := I) γ t) (curveVelocity (I := I) γ t)))
      t := by
  have h := parInner_deriv (I := I) hn g γ Fi
    (fun s : ℝ => covDerivAlong (I := I) g γ Y s) t hγ hFdiff hDYdiff hFpar
  rw [jacobi_d2_eq (I := I) g γ Y hY] at h
  simpa using h

attribute [-instance] Tensor0SBundle.tangentSpace_normedAddCommGroup
  Tensor0SBundle.tangentSpace_normedSpace in
set_option synthInstance.maxHeartbeats 400000 in
/-- **Curvature term in frame coordinates.**  Expanding `Y t` in a full
`g`-orthonormal family `F · t` at `γ t`, the curvature pairing
`g(F i, R(Y, γ̇)γ̇)` is the linear combination
`∑ j, g(F j, Y) · g(F i, R(F j, γ̇)γ̇)` — the `(A t) y` form of the
frame-coordinate Jacobi system. -/
theorem parInner_curv_expand
    (g : SmoothRiemannianMetric I M) (γ : ℝ → M) (t : ℝ)
    {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]
    (F : ι → ∀ s : ℝ, TangentSpace I (γ s)) (Y : ∀ s : ℝ, TangentSpace I (γ s))
    (hON : ∀ i j, g.inner (γ t) (F i t) (F j t) = if i = j then (1 : ℝ) else 0)
    (hcard : Fintype.card ι = Module.finrank ℝ (TangentSpace I (γ t)))
    (i : ι) :
    g.inner (γ t) (F i t)
      ((DifferentialGeometry.Integral.Connection.riemannOp
          (DifferentialGeometry.Integral.Connection.LeviCivita (I := I) g)
          (γ t))
        (Y t) (curveVelocity (I := I) γ t) (curveVelocity (I := I) γ t))
    = ∑ j, g.inner (γ t) (F j t) (Y t) *
        g.inner (γ t) (F i t)
          ((DifferentialGeometry.Integral.Connection.riemannOp
              (DifferentialGeometry.Integral.Connection.LeviCivita (I := I) g)
              (γ t))
            (F j t) (curveVelocity (I := I) γ t)
            (curveVelocity (I := I) γ t)) := by
  classical
  have hexp := gON_expand (I := I) g (γ t) (fun j => F j t) hON hcard (Y t)
  conv_lhs => rw [hexp]
  simp only [map_sum, map_smul, ContinuousLinearMap.coe_sum', Finset.sum_apply,
    ContinuousLinearMap.coe_smul', Pi.smul_apply, smul_eq_mul]

attribute [-instance] Tensor0SBundle.tangentSpace_normedAddCommGroup
  Tensor0SBundle.tangentSpace_normedSpace in
set_option synthInstance.maxHeartbeats 400000 in
/-- **Uniqueness of Jacobi fields with given initial data.**  Along a curve
carrying a parallel `g`-orthonormal frame of full cardinality on `[0, b]`,
two fields that are Jacobi on `[0, b]`, have the required chart-representation
differentiability, and agree in value and covariant derivative at `0`, agree
on all of `[0, b]` — provided the frame curvature entries are bounded by a
constant.  Grönwall closer: `ode2_pi_zero` on the coordinate differences. -/
theorem jacobi_unique
    {n : WithTop ℕ∞} (hn : 1 ≤ n)
    (g : SmoothRiemannianMetric I M) (γ : ℝ → M) {b : ℝ}
    {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]
    (F : ι → ∀ s : ℝ, TangentSpace I (γ s))
    (Y₁ Y₂ : ∀ s : ℝ, TangentSpace I (γ s))
    {C : ℝ} (hC : 0 ≤ C)
    (hγ : ∀ t ∈ Icc (0 : ℝ) b, ContMDiffAt 𝓘(ℝ, ℝ) I n γ t)
    (hFdiff : ∀ i, ∀ t ∈ Icc (0 : ℝ) b,
      DifferentiableAt ℝ (chartRepAt (I := I) γ (F i) t) t)
    (hFpar : ∀ i, ∀ t ∈ Icc (0 : ℝ) b,
      covDerivAlong (I := I) g γ (F i) t = 0)
    (hON : ∀ t ∈ Icc (0 : ℝ) b, ∀ i j,
      g.inner (γ t) (F i t) (F j t) = if i = j then (1 : ℝ) else 0)
    (hcard : ∀ t ∈ Icc (0 : ℝ) b,
      Fintype.card ι = Module.finrank ℝ (TangentSpace I (γ t)))
    (hY₁diff : ∀ t ∈ Icc (0 : ℝ) b,
      DifferentiableAt ℝ (chartRepAt (I := I) γ Y₁ t) t)
    (hY₂diff : ∀ t ∈ Icc (0 : ℝ) b,
      DifferentiableAt ℝ (chartRepAt (I := I) γ Y₂ t) t)
    (hDY₁diff : ∀ t ∈ Icc (0 : ℝ) b,
      DifferentiableAt ℝ (chartRepAt (I := I) γ
        (fun s : ℝ => covDerivAlong (I := I) g γ Y₁ s) t) t)
    (hDY₂diff : ∀ t ∈ Icc (0 : ℝ) b,
      DifferentiableAt ℝ (chartRepAt (I := I) γ
        (fun s : ℝ => covDerivAlong (I := I) g γ Y₂ s) t) t)
    (hJ₁ : ∀ t ∈ Icc (0 : ℝ) b, IsJacobiAt (I := I) g γ Y₁ t)
    (hJ₂ : ∀ t ∈ Icc (0 : ℝ) b, IsJacobiAt (I := I) g γ Y₂ t)
    (hCbound : ∀ t ∈ Icc (0 : ℝ) b, ∀ i j,
      |g.inner (γ t) (F i t)
        ((DifferentialGeometry.Integral.Connection.riemannOp
            (DifferentialGeometry.Integral.Connection.LeviCivita (I := I) g)
            (γ t))
          (F j t) (curveVelocity (I := I) γ t)
          (curveVelocity (I := I) γ t))| ≤ C)
    (hb : (0 : ℝ) ≤ b)
    (h0 : Y₁ 0 = Y₂ 0)
    (h0' : covDerivAlong (I := I) g γ Y₁ 0 = covDerivAlong (I := I) g γ Y₂ 0) :
    ∀ t ∈ Icc (0 : ℝ) b, Y₁ t = Y₂ t := by
  classical
  have h0mem : (0 : ℝ) ∈ Icc (0 : ℝ) b := ⟨le_rfl, hb⟩
  -- the scalar coordinate system of the difference
  have hzero := DifferentialGeometry.Analysis.ODE.ode2_pi_zero
    (y := fun t i => g.inner (γ t) (F i t) (Y₁ t) - g.inner (γ t) (F i t) (Y₂ t))
    (v := fun t i =>
      g.inner (γ t) (F i t) (covDerivAlong (I := I) g γ Y₁ t)
        - g.inner (γ t) (F i t) (covDerivAlong (I := I) g γ Y₂ t))
    (w := fun t i =>
      (- g.inner (γ t) (F i t)
          ((DifferentialGeometry.Integral.Connection.riemannOp
              (DifferentialGeometry.Integral.Connection.LeviCivita (I := I) g)
              (γ t))
            (Y₁ t) (curveVelocity (I := I) γ t) (curveVelocity (I := I) γ t)))
        - (- g.inner (γ t) (F i t)
            ((DifferentialGeometry.Integral.Connection.riemannOp
                (DifferentialGeometry.Integral.Connection.LeviCivita (I := I) g)
                (γ t))
              (Y₂ t) (curveVelocity (I := I) γ t)
              (curveVelocity (I := I) γ t))))
    (b := b) (C := C) hC
    (fun i => fun t ht =>
      (((parInner_deriv (I := I) hn g γ (F i) Y₁ t (hγ t ht) (hFdiff i t ht)
          (hY₁diff t ht) (hFpar i t ht)).sub
        (parInner_deriv (I := I) hn g γ (F i) Y₂ t (hγ t ht) (hFdiff i t ht)
          (hY₂diff t ht) (hFpar i t ht))).continuousAt).continuousWithinAt)
    (fun i => fun t ht =>
      (((parInner_d2 (I := I) hn g γ (F i) Y₁ t (hγ t ht) (hFdiff i t ht)
          (hDY₁diff t ht) (hFpar i t ht) (hJ₁ t ht)).sub
        (parInner_d2 (I := I) hn g γ (F i) Y₂ t (hγ t ht) (hFdiff i t ht)
          (hDY₂diff t ht) (hFpar i t ht) (hJ₂ t ht))).continuousAt).continuousWithinAt)
    (fun t ht i => by
      have hIcc : t ∈ Icc (0 : ℝ) b := ⟨ht.1, le_of_lt ht.2⟩
      exact ((parInner_deriv (I := I) hn g γ (F i) Y₁ t (hγ t hIcc)
          (hFdiff i t hIcc) (hY₁diff t hIcc) (hFpar i t hIcc)).sub
        (parInner_deriv (I := I) hn g γ (F i) Y₂ t (hγ t hIcc)
          (hFdiff i t hIcc) (hY₂diff t hIcc)
          (hFpar i t hIcc))).hasDerivWithinAt)
    (fun t ht i => by
      have hIcc : t ∈ Icc (0 : ℝ) b := ⟨ht.1, le_of_lt ht.2⟩
      exact ((parInner_d2 (I := I) hn g γ (F i) Y₁ t (hγ t hIcc)
          (hFdiff i t hIcc) (hDY₁diff t hIcc) (hFpar i t hIcc)
          (hJ₁ t hIcc)).sub
        (parInner_d2 (I := I) hn g γ (F i) Y₂ t (hγ t hIcc)
          (hFdiff i t hIcc) (hDY₂diff t hIcc) (hFpar i t hIcc)
          (hJ₂ t hIcc))).hasDerivWithinAt)
    (fun t ht i => by
      have hIcc : t ∈ Icc (0 : ℝ) b := ⟨ht.1, le_of_lt ht.2⟩
      have hexp₁ := parInner_curv_expand (I := I) g γ t F Y₁
        (hON t hIcc) (hcard t hIcc) i
      have hexp₂ := parInner_curv_expand (I := I) g γ t F Y₂
        (hON t hIcc) (hcard t hIcc) i
      have hw :
          (- g.inner (γ t) (F i t)
              ((DifferentialGeometry.Integral.Connection.riemannOp
                  (DifferentialGeometry.Integral.Connection.LeviCivita
                    (I := I) g) (γ t))
                (Y₁ t) (curveVelocity (I := I) γ t)
                (curveVelocity (I := I) γ t)))
            - (- g.inner (γ t) (F i t)
                ((DifferentialGeometry.Integral.Connection.riemannOp
                    (DifferentialGeometry.Integral.Connection.LeviCivita
                      (I := I) g) (γ t))
                  (Y₂ t) (curveVelocity (I := I) γ t)
                  (curveVelocity (I := I) γ t)))
          = ∑ j, (g.inner (γ t) (F j t) (Y₂ t)
                - g.inner (γ t) (F j t) (Y₁ t))
              * g.inner (γ t) (F i t)
                ((DifferentialGeometry.Integral.Connection.riemannOp
                    (DifferentialGeometry.Integral.Connection.LeviCivita
                      (I := I) g) (γ t))
                  (F j t) (curveVelocity (I := I) γ t)
                  (curveVelocity (I := I) γ t)) := by
        rw [neg_sub_neg, hexp₁, hexp₂, ← Finset.sum_sub_distrib]
        refine Finset.sum_congr rfl fun j _ => ?_
        ring
      simp only []
      rw [hw]
      calc |∑ j, (g.inner (γ t) (F j t) (Y₂ t)
                - g.inner (γ t) (F j t) (Y₁ t))
              * g.inner (γ t) (F i t)
                ((DifferentialGeometry.Integral.Connection.riemannOp
                    (DifferentialGeometry.Integral.Connection.LeviCivita
                      (I := I) g) (γ t))
                  (F j t) (curveVelocity (I := I) γ t)
                  (curveVelocity (I := I) γ t))|
          ≤ ∑ j, |(g.inner (γ t) (F j t) (Y₂ t)
                - g.inner (γ t) (F j t) (Y₁ t))
              * g.inner (γ t) (F i t)
                ((DifferentialGeometry.Integral.Connection.riemannOp
                    (DifferentialGeometry.Integral.Connection.LeviCivita
                      (I := I) g) (γ t))
                  (F j t) (curveVelocity (I := I) γ t)
                  (curveVelocity (I := I) γ t))| :=
            Finset.abs_sum_le_sum_abs _ _
        _ ≤ ∑ j, |g.inner (γ t) (F j t) (Y₂ t)
                - g.inner (γ t) (F j t) (Y₁ t)| * C := by
            refine Finset.sum_le_sum fun j _ => ?_
            rw [abs_mul]
            exact mul_le_mul_of_nonneg_left (hCbound t hIcc i j) (abs_nonneg _)
        _ = C * ∑ j, |g.inner (γ t) (F j t) (Y₁ t)
                - g.inner (γ t) (F j t) (Y₂ t)| := by
            rw [Finset.mul_sum]
            refine Finset.sum_congr rfl fun j _ => ?_
            rw [abs_sub_comm]; ring)
    (fun i => by simp only []; rw [h0, sub_self])
    (fun i => by simp only []; rw [h0', sub_self])
  intro t ht
  have hexp₁ := gON_expand (I := I) g (γ t) (fun j => F j t)
    (hON t ht) (hcard t ht) (Y₁ t)
  have hexp₂ := gON_expand (I := I) g (γ t) (fun j => F j t)
    (hON t ht) (hcard t ht) (Y₂ t)
  calc Y₁ t = ∑ j, g.inner (γ t) (F j t) (Y₁ t) • F j t := hexp₁
    _ = ∑ j, g.inner (γ t) (F j t) (Y₂ t) • F j t := by
        refine Finset.sum_congr rfl fun j _ => ?_
        have hz := hzero t ht j
        have : g.inner (γ t) (F j t) (Y₁ t) = g.inner (γ t) (F j t) (Y₂ t) :=
          sub_eq_zero.mp hz
        rw [this]
    _ = Y₂ t := hexp₂.symm

end Variation
end Riemannian
end Geometry
end DifferentialGeometry
