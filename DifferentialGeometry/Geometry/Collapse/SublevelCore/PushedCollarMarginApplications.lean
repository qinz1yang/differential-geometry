import DifferentialGeometry.Geometry.Collapse.SublevelCore.PushedCollarPacket
import DifferentialGeometry.Geometry.Collapse.RiemannianOutwardPoint

/-!
# Consumer of LC51 on the real line

On `N = ℝ` with the Euclidean metric, the open buffer `U = (-11, 11)`, the constant sequence of
inclusion maps and the outward unit field `V = 1`, the only inward unit minimizing direction at
`1` towards `0` is `-1` (derived from the geodesic's displacement bound and initial velocity).
LC51's first half (`eventually_pushed_field_collar_margin`) then gives, on one tail, the pushed
field bound `|Z| ≤ 2` and the margin `g(Z, w) ≤ -1/2` for every inward direction `w`.
-/

set_option autoImplicit false

noncomputable section

open Set Filter Bundle
open scoped Manifold ContDiff Topology

namespace DifferentialGeometry.Geometry.Collapse

open DifferentialGeometry.CheegerGromovCompactness
open DifferentialGeometry.Geometry.Riemannian
open DifferentialGeometry.Geometry.Riemannian.Exponential

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace

private instance realFinrankPos : NeZero (Module.finrank ℝ ℝ) := ⟨by simp⟩

private theorem realEuclideanNorm : IsMetricNorm (euclideanMetric (E := ℝ)) := by
  intro x v
  rw [← ofReal_norm, euclideanMetric_inner, real_inner_self_eq_norm_sq,
    Real.sqrt_sq_eq_abs, abs_of_nonneg (norm_nonneg v)]

private instance realContinuousRiemannian :
    IsContinuousRiemannianBundle ℝ (fun x : ℝ => TangentSpace 𝓘(ℝ, ℝ) x) :=
  realEuclideanNorm.isContinuousRiemannianBundle

/-- On the Euclidean line, the inward unit minimizing directions at `1` towards `0` are `-1`. -/
theorem real_inwardMinimizingDirections_one {v : TangentSpace 𝓘(ℝ, ℝ) (1 : ℝ)}
    (hv : v ∈ inwardMinimizingDirections (euclideanMetric (E := ℝ)) realEuclideanNorm 0 1) :
    (v : ℝ) = -1 := by
  obtain ⟨hunit, hend⟩ := hv
  let g := euclideanMetric (E := ℝ)
  let γ : ℝ → ℝ := intrinsicGeodesic g realEuclideanNorm (1 : ℝ) v
  let x : ℝ := v
  have hpm : x = 1 ∨ x = -1 := by
    have h : inner ℝ x x = 1 := hunit
    simpa using h
  have hd01 : dist (0 : ℝ) 1 = 1 := by norm_num [Real.dist_eq]
  rw [hd01] at hend
  have hsqrt : Real.sqrt (g.inner (1 : ℝ) v v) = 1 := by
    change Real.sqrt (euclideanMetric.inner (1 : ℝ) v v) = 1
    rw [hunit, Real.sqrt_one]
  -- displacement bound: `γ t ≤ 1 - t` on `[0, 1]`
  have hbound : ∀ t ∈ Icc (0 : ℝ) 1, γ t + t ≤ 1 := by
    intro t ht
    have h := dist_intrinsicGeodesic_le_mul g realEuclideanNorm (1 : ℝ) v ht.2
    rw [hsqrt, one_mul] at h
    change dist (γ t) (γ 1) ≤ 1 - t at h
    have h1 : γ 1 = 0 := hend
    rw [h1, Real.dist_eq, sub_zero] at h
    linarith [le_abs_self (γ t)]
  -- initial velocity
  have hdiff : MDifferentiableAt 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) γ 0 :=
    ((intrinsicGeodesic_contMDiffOn g realEuclideanNorm (1 : ℝ) v).contMDiffAt
      univ_mem).mdifferentiableAt one_ne_zero
  have hvel : (mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) γ 0 : ℝ →L[ℝ] ℝ) 1 = x :=
    intrinsicGeodesic_mfderiv_zero g realEuclideanNorm (1 : ℝ) v
  have hderiv : deriv γ 0 = x := by
    rw [← hvel, mfderiv_eq_fderiv]
    rfl
  have hD : HasDerivAt γ x 0 := hderiv ▸ hdiff.differentiableAt.hasDerivAt
  have h0 : γ 0 = 1 := intrinsicGeodesic_zero g realEuclideanNorm (1 : ℝ) v
  have hslope : Tendsto (slope γ 0) (𝓝[>] 0) (𝓝 x) := by
    have h := hasDerivWithinAt_iff_tendsto_slope.mp (hD.hasDerivWithinAt (s := Ioi 0))
    have hs : Ioi (0 : ℝ) \ {0} = Ioi 0 := sdiff_singleton_eq_self (lt_irrefl (0 : ℝ))
    rwa [hs] at h
  have hle : x ≤ -1 := by
    apply le_of_tendsto hslope
    filter_upwards [Ioo_mem_nhdsGT (by norm_num : (0 : ℝ) < 1)] with t ht
    rw [slope_def_field, h0, sub_zero, div_le_iff₀ ht.1]
    linarith [hbound t ⟨ht.1.le, ht.2.le⟩]
  change x = -1
  rcases hpm with h | h
  · linarith
  · exact h

/-- **Consumer of LC51 (first half).** The real-line instance of
`eventually_pushed_field_collar_margin`: constant inclusions of `(-11, 11)`, collar `{1}`, field
`V = 1`, constants `α = 1/2`, `B = 1`. -/
theorem realOpen_pushed_field_collar_margin :
    let U : TopologicalSpace.Opens ℝ := ⟨Ioo (-11) 11, isOpen_Ioo⟩
    let n : U := ⟨0, by constructor <;> norm_num⟩
    let q : U := ⟨1, by constructor <;> norm_num⟩
    let j := DifferentialGeometry.Topology.PartialDiffeomorph.subtypeVal (I := 𝓘(ℝ, ℝ)) U ⟨q⟩
    ∀ᶠ _i : ℕ in atTop,
      √((euclideanMetric (E := ℝ)).inner (j q) (mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) (j : U → ℝ) q (1 : ℝ))
          (mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) (j : U → ℝ) q (1 : ℝ))) ≤ (2 : ℝ) * 1 ∧
      ∀ w ∈ inwardMinimizingDirections (euclideanMetric (E := ℝ)) realEuclideanNorm (j n) (j q),
        (euclideanMetric (E := ℝ)).inner (j q)
          (mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) (j : U → ℝ) q (1 : ℝ)) w ≤ -(1 / 2) := by
  intro U n q j
  let g := euclideanMetric (E := ℝ)
  have hbuffer : Metric.closedBall (n : ℝ) 10 ⊆ U := by
    intro x hx
    rw [Metric.mem_closedBall, Real.dist_eq, sub_zero, abs_le] at hx
    exact ⟨by linarith [hx.1], by linarith [hx.2]⟩
  have hV : ContinuousOn (fun x : U => (⟨x, (1 : ℝ)⟩ : TangentBundle 𝓘(ℝ, ℝ) U)) {q} :=
    continuousOn_singleton _ _
  filter_upwards [eventually_pushed_field_collar_margin (M := fun _i : ℕ => ℝ) g realEuclideanNorm U n
    hbuffer (fun _i : ℕ => g.restrictOpen U) (fun _i : ℕ => g)
    (fun _i : ℕ => realEuclideanNorm) (fun _i : ℕ => j) (fun _i : ℕ => rfl)
    (fun _i x v u => by
      change g.inner (x : ℝ) v u = g.inner (x : ℝ)
        (mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) (Subtype.val : U → ℝ) x v)
        (mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) (Subtype.val : U → ℝ) x u)
      rw [DifferentialGeometry.mfderiv_subtype_val_apply,
        DifferentialGeometry.mfderiv_subtype_val_apply])
    (fun C _hC epsilon hepsilon => ⟨0, fun _i _hi => by
      rw [metricDerivNormSupOn_self]; exact hepsilon⟩)
    (C := {q}) isCompact_singleton
    (fun x hx => by rw [mem_singleton_iff] at hx; subst x; norm_num [Metric.mem_ball, n, q])
    (fun x hx => by rw [mem_singleton_iff] at hx; subst x; norm_num [n, q])
    (fun _x => (1 : ℝ)) hV (by norm_num : (0 : ℝ) < 1 / 2) (by norm_num : (0 : ℝ) ≤ 1)
    (fun x hx => by
      rw [mem_singleton_iff] at hx; subst x
      change inner ℝ (1 : ℝ) (1 : ℝ) ≤ 1 ^ 2
      simp)
    (fun x hx v hv => by
      rw [mem_singleton_iff] at hx; subst x
      have hv' := real_inwardMinimizingDirections_one hv
      have key : ∀ y : ℝ, y = -1 → inner ℝ (1 : ℝ) y ≤ -(2 * (1 / 2)) := by
        rintro y rfl
        simp
      exact key v hv')] with i hi
  exact hi q (mem_singleton q)

end DifferentialGeometry.Geometry.Collapse
