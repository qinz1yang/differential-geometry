import DifferentialGeometry.Geometry.Flow.RicciFlow.Extension.Maximal.Flow
import DifferentialGeometry.Geometry.Flow.RicciFlow.Estimates.Shi.CompleteGlobal
import DifferentialGeometry.Geometry.Flow.RicciFlow.Evolution.Curvature.IteratedCovariantDerivativeBridge

/-!
# Uniform all-order curvature control at positive time (LFR50 part D, Shi step)

For a Ricci flow `P : FlowTo g₀ τ` on a closed manifold (domain `closedOpen 0 τ`) with `T < τ` and
`|Rm| ≤ B` on `[0, T]`, Shi's estimate (`shi_positive_slab_of_solution`,
`Estimates/Shi/CompleteGlobal.lean`) at the times `0 < T/4 < T/2` gives, for every order `m`,

  `|∇^m Rm| ≤ shiCompleteGlobalBound (dim M) m · B · (1/√(T/4) + √B)^m` on `[T/2, T]`.

The compact time-`T/4` slice is complete (`RiemannianMetricComplete.of_compact`). The Shi output is
stated for `nablaKRm04NormSqIntrinsic`; the exact bridge `sqrt_nablaKRm04NormSqIntrinsic_eq_curvDerivNorm`
turns it into `curvDerivNorm`, the norm used by `SeqBoundedGeometry`, without any constant.

* `curvDerivNorm_le_of_flowTo_curvature_bound`: one flow, explicit constant;
* `exists_uniform_positive_time_curvature_derivatives`: the frozen §5 contract of the merged LFR50
  design, for a sequence of flows with the part-B bounds; the constants depend only on
  `m`, `dim M`, `B`, `T`, not on the index of the flow.
-/

set_option autoImplicit false

noncomputable section

open Set
open DifferentialGeometry DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.CheegerGromovCompactness
open scoped Manifold ContDiff

namespace DifferentialGeometry.PDE.RicciFlow

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)] [CompleteSpace E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [SigmaCompactSpace M] [T2Space M] [CompactSpace M] [BoundarylessManifold I M]

omit [SigmaCompactSpace M] in
/-- **Shi at positive time, one flow.** A Ricci flow on `[0, τ)` of a closed manifold with
`|Rm| ≤ B` on `[0, T]`, `T < τ`, satisfies on `[T/2, T]`, for every `m`,
`|∇^m Rm| ≤ shiCompleteGlobalBound (dim M) m · B · (1/√(T/4) + √B)^m`. -/
theorem curvDerivNorm_le_of_flowTo_curvature_bound {g₀ : SmoothRiemannianMetric I M} {τ : ℝ}
    (P : FlowTo (I := I) (M := M) g₀ τ) {T B : ℝ} (hT : 0 < T) (hB : 0 < B) (hTτ : T < τ)
    (hcurv : ∀ t ∈ Icc 0 T, ∀ x : M,
      Real.sqrt (Tensor0SBundle.normSq0S (P.S.base.metric t) x 4
        (metricRm04 (P.S.base.metric t) x)) ≤ B) :
    ∀ m : ℕ, ∀ t ∈ Icc (T / 2) T, ∀ x : M,
      curvDerivNorm (I := I) m (P.S.base.metric t) x ≤
        shiCompleteGlobalBound (Module.finrank ℝ E) m * B *
          (1 / Real.sqrt (T / 4) + Real.sqrt B) ^ m := by
  intro m t ht x
  have hcurv' : ∀ s ∈ Icc (T / 4) T, ∀ y : M,
      nablaKRm04NormSqIntrinsic (I := I) P.S 0 s y ≤ B ^ 2 := by
    intro s hs y
    have h := hcurv s ⟨by linarith [hs.1], hs.2⟩ y
    exact (Real.sqrt_le_iff.mp h).2
  have hshi := shi_positive_slab_of_solution (I := I) P.S P.isSolution
    (a₀ := T / 4) (a := T / 2) (b := T) (K := B) (by positivity) (by linarith) hTτ hB
    (RiemannianMetricComplete.of_compact (I := I) _) hcurv' m t ht x
  rw [sqrt_nablaKRm04NormSqIntrinsic_eq_curvDerivNorm,
    show T / 2 - T / 4 = T / 4 by ring] at hshi
  exact hshi

omit [SigmaCompactSpace M] in
/-- **D2, the frozen §5 contract.** For a sequence of Ricci flows `F n : FlowTo (gSeq n) (τ n)` on
a closed manifold with `T < τ n` and `|Rm| ≤ B` on `[0, T]` (the output shape of part B), every
covariant derivative `∇^m Rm` is bounded on `[T/2, T]` by a constant `A m` independent of `n`. -/
theorem exists_uniform_positive_time_curvature_derivatives
    (gSeq : ℕ → SmoothRiemannianMetric I M)
    (T B : ℝ) (hT : 0 < T) (hB : 0 < B)
    (τ : ℕ → ℝ) (hτ : ∀ n, T < τ n)
    (F : (n : ℕ) → FlowTo (I := I) (M := M) (gSeq n) (τ n))
    (hcurv : ∀ n t, t ∈ Icc 0 T → ∀ x : M,
      Real.sqrt (DifferentialGeometry.Tensor0SBundle.normSq0S
        ((F n).S.base.metric t) x 4
        (metricRm04 ((F n).S.base.metric t) x)) ≤ B) :
    ∃ A : ℕ → ℝ, (∀ m, 0 ≤ A m) ∧
      ∀ m n t, t ∈ Icc (T / 2) T → ∀ x : M,
        curvDerivNorm (I := I) m ((F n).S.base.metric t) x ≤ A m := by
  refine ⟨fun m => shiCompleteGlobalBound (Module.finrank ℝ E) m * B *
      (1 / Real.sqrt (T / 4) + Real.sqrt B) ^ m, fun m => ?_, ?_⟩
  · have hC := shiCompleteGlobalBound_nonneg (Module.finrank ℝ E) m
    positivity
  · intro m n t ht x
    exact curvDerivNorm_le_of_flowTo_curvature_bound (F n) hT hB (hτ n)
      (fun s hs y => hcurv n s hs y) m t ht x

end DifferentialGeometry.PDE.RicciFlow
