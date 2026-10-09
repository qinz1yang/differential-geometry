import DifferentialGeometry.Geometry.Metric.Pullback.PartialDiffeomorph.Basic
import DifferentialGeometry.Geometry.Metric.Convergence.Scaling
import DifferentialGeometry.Topology.Manifold.OpenSubtypeDiffeomorph
import DifferentialGeometry.Topology.Manifold.PartialDiffeomorphTrans

/-!
# LC56's maps at a fixed scale `R`: the buffered LC50 data (GAP A2)

Master207A, after LC56 (A:23060–23075): "for every fixed `R > 0`, properness and item (2) give a
common restriction `O_R = B_g(n, 11R) ⊂ U_i` on a tail … after the FIXED rescaling
`g_R = R⁻² g`, `g_{i,R} = R⁻² g_i`, these restricted embeddings meet LC50's open-neighbourhood
requirement for the CLOSED radius-10 ball, with the same `C¹` convergence."

LC56 item (2) is encoded (A1, accepted) by actual partial diffeomorphisms `j i : N ⇀ M i` and, for
every radius `r > 0`, a shift `i₀` after which the ball `B(n, r)` lies in every source and the
pullbacks `(j (k + i₀))^* g_{k+i₀}` (`PartialDiffeomorph.pullbackMetricOn`) converge to `g` in `C¹`
on the compact subsets of `B(n, r)`. At a fixed `R > 0` this gives, on `U = B(n, 11R)`:
* the restricted maps `jU k = (U ↪ N) ≫ j (k + i₀) : U ⇀ M (k + i₀)` with source everything;
* the pullback identity for the scaled tensors `R⁻² (jU k)^* g_{k+i₀} = jU k^* (R⁻² g_{k+i₀})`;
* `C¹` convergence of the scaled pullbacks to `(R⁻² g)|_U` on compact subsets of `U`;
* `closedBall(n, 10 R) ⊆ U` (the closed radius-10 ball of `R⁻¹ d`).
The conclusions are instance-free (no rescaled metric-space structure is needed to state them).
-/

set_option autoImplicit false

noncomputable section

open Set Filter Bundle
open scoped Manifold ContDiff Topology

namespace DifferentialGeometry.Geometry.Collapse

open DifferentialGeometry.CheegerGromovCompactness
open DifferentialGeometry.Manifold

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}

/-- Restricting a scaled metric to an open set is scaling the restriction. -/
theorem restrictOpen_scaleMetric {N : Type*} [TopologicalSpace N] [ChartedSpace H N]
    [IsManifold I ∞ N] [T2Space N] (g : SmoothRiemannianMetric I N) {c : ℝ} (hc : 0 < c)
    (U : TopologicalSpace.Opens N) :
    (scaleMetric c hc g).restrictOpen U = scaleMetric c hc (g.restrictOpen U) := by
  apply SmoothRiemannianMetric.ext_inner
  intro x v w
  rfl

/-- **GAP A2: LC56's maps give the buffered LC50 data at scale `R`.** Under the A1 encoding of
LC56 item (2), for every `R > 0` there is a shift `i₀` such that `U = B(n, 11R)` lies in every
source after `i₀`, the restricted maps `U ⇀ M (k + i₀)` have source everything, the scaled
pullback identity holds, the scaled pullbacks converge in `C¹` to `(R⁻² g)|_U` on every compact
subset of `U`, and `closedBall(n, 10R) ⊆ U`. -/
theorem exists_shifted_buffered_maps_at_scale {N : Type*} [MetricSpace N] [ChartedSpace H N]
    [IsManifold I ∞ N] {M : ℕ → Type*} [∀ i, TopologicalSpace (M i)]
    [∀ i, ChartedSpace H (M i)] [∀ i, IsManifold I ∞ (M i)] [∀ i, T2Space (M i)]
    (g : SmoothRiemannianMetric I N) (gSeq : ∀ i, SmoothRiemannianMetric I (M i)) (n : N)
    (j : ∀ i, PartialDiffeomorph I I N (M i) ∞)
    (hC1 : ∀ r : ℝ, 0 < r → ∃ i₀ : ℕ, ∃ hsub : ∀ k,
      ((⟨Metric.ball n r, Metric.isOpen_ball⟩ : TopologicalSpace.Opens N) : Set N) ⊆
        (j (k + i₀)).source,
      ∀ C : Set (⟨Metric.ball n r, Metric.isOpen_ball⟩ : TopologicalSpace.Opens N),
        IsCompact C → MetricCPConvergenceOn C 1
          (fun k => PartialDiffeomorph.pullbackMetricOn (j (k + i₀)) _ (hsub k) (gSeq (k + i₀)))
          (g.restrictOpen _) (g.restrictOpen _))
    {R : ℝ} (hR : 0 < R) :
    ∃ i₀ : ℕ, ∃ hsub : ∀ k,
      ((⟨Metric.ball n (11 * R), Metric.isOpen_ball⟩ : TopologicalSpace.Opens N) : Set N) ⊆
        (j (k + i₀)).source,
      ∃ hU : Nonempty (⟨Metric.ball n (11 * R), Metric.isOpen_ball⟩ : TopologicalSpace.Opens N),
      (∀ k, ((openSubtypePartialDiffeomorph I _ hU).trans (j (k + i₀))).source = univ) ∧
      (∀ k (x : (⟨Metric.ball n (11 * R), Metric.isOpen_ball⟩ : TopologicalSpace.Opens N))
          (v w : TangentSpace I x),
        (scaleMetric (R⁻¹ ^ 2) (pow_pos (inv_pos.mpr hR) 2)
          (PartialDiffeomorph.pullbackMetricOn (j (k + i₀)) _ (hsub k) (gSeq (k + i₀)))).inner
            x v w =
          (scaleMetric (R⁻¹ ^ 2) (pow_pos (inv_pos.mpr hR) 2) (gSeq (k + i₀))).inner
            (((openSubtypePartialDiffeomorph I _ hU).trans (j (k + i₀))) x)
            (mfderiv I I ((openSubtypePartialDiffeomorph I _ hU).trans (j (k + i₀))) x v)
            (mfderiv I I ((openSubtypePartialDiffeomorph I _ hU).trans (j (k + i₀))) x w)) ∧
      (∀ C : Set (⟨Metric.ball n (11 * R), Metric.isOpen_ball⟩ : TopologicalSpace.Opens N),
        IsCompact C → MetricCPConvergenceOn C 1
          (fun k => scaleMetric (R⁻¹ ^ 2) (pow_pos (inv_pos.mpr hR) 2)
            (PartialDiffeomorph.pullbackMetricOn (j (k + i₀)) _ (hsub k) (gSeq (k + i₀))))
          ((scaleMetric (R⁻¹ ^ 2) (pow_pos (inv_pos.mpr hR) 2) g).restrictOpen _)
          ((scaleMetric (R⁻¹ ^ 2) (pow_pos (inv_pos.mpr hR) 2) g).restrictOpen _)) ∧
      Metric.closedBall n (10 * R) ⊆
        ((⟨Metric.ball n (11 * R), Metric.isOpen_ball⟩ : TopologicalSpace.Opens N) : Set N) := by
  obtain ⟨i₀, hsub, hconv⟩ := hC1 (11 * R) (by positivity)
  set U : TopologicalSpace.Opens N := ⟨Metric.ball n (11 * R), Metric.isOpen_ball⟩ with hUdef
  have hU : Nonempty U := ⟨⟨n, Metric.mem_ball_self (by positivity)⟩⟩
  have hc : 0 < R⁻¹ ^ 2 := pow_pos (inv_pos.mpr hR) 2
  refine ⟨i₀, hsub, hU, fun k => ?_, fun k x v w => ?_, fun C hC => ?_, ?_⟩
  · rw [PartialDiffeomorph.trans_source, openSubtypePartialDiffeomorph_source]
    refine eq_univ_of_forall fun x => ⟨mem_univ x, hsub k x.2⟩
  · have hfun : (((openSubtypePartialDiffeomorph I U hU).trans (j (k + i₀))) : U → M (k + i₀)) =
        (j (k + i₀) : N → M (k + i₀)) ∘ Subtype.val := rfl
    have hjd : MDifferentiableAt I I (j (k + i₀) : N → M (k + i₀)) (x : N) :=
      (j (k + i₀)).mdifferentiableAt (by decide) (hsub k x.2)
    have hvd : MDifferentiableAt I I (Subtype.val : U → N) x :=
      (contMDiff_subtype_val (I := I) (n := ∞)).mdifferentiableAt (by decide)
    have hmf : ∀ u : TangentSpace I x,
        mfderiv I I (((openSubtypePartialDiffeomorph I U hU).trans (j (k + i₀))) : U → M (k + i₀))
          x u = mfderiv I I (j (k + i₀) : N → M (k + i₀)) (x : N) u := by
      intro u
      rw [hfun, mfderiv_comp x hjd hvd, ContinuousLinearMap.comp_apply,
        mfderiv_subtype_val_apply]
    rw [scaleMetric_inner, scaleMetric_inner, PartialDiffeomorph.pullbackMetricOn_inner, hmf v,
      hmf w]
    rfl
  · rw [restrictOpen_scaleMetric g hc U]
    exact metricCPConvOn_scale_all (R⁻¹ ^ 2) hc hC 1 _ _ _ (hconv C hC)
  · intro x hx
    rw [Metric.mem_closedBall] at hx
    change dist x n < 11 * R
    linarith

end DifferentialGeometry.Geometry.Collapse
