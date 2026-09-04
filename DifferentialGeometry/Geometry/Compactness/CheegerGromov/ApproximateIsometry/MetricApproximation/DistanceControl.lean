import DifferentialGeometry.Geometry.Compactness.CheegerGromov.ApproximateIsometry.MetricApproximation.Defs
import DifferentialGeometry.Geometry.Metric.Comparison.PathLength

set_option autoImplicit false

namespace DifferentialGeometry
namespace CheegerGromovCompactness

open Bundle Manifold
open scoped Manifold ContDiff ENNReal

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace

universe u uE uH

section BallImage

variable {E : Type uE} [NormedAddCommGroup E] [NormedSpace Real E]
variable [FiniteDimensional Real E] [CompleteSpace E]
variable {H : Type uH} [TopologicalSpace H]
variable {I : ModelWithCorners Real E H}
variable {M : Type u} [TopologicalSpace M] [ChartedSpace H M] [T2Space M]
  [IsManifold I ∞ M] [SigmaCompactSpace M]
variable {N : Type u} [TopologicalSpace N] [ChartedSpace H N] [IsManifold I ∞ N]

omit [SigmaCompactSpace M] in
theorem MapMetricApproximationOn.image_eball_subset_closedEBall
    [PseudoEMetricSpace M] [RiemannianBundle (fun x : M => TangentSpace I x)]
    [IsRiemannianManifold I M]
    [PseudoEMetricSpace N] [RiemannianBundle (fun y : N => TangentSpace I y)]
    [IsRiemannianManifold I N]
    (Φ : PartialDiffeomorph I I M N (∞ : WithTop ℕ∞)) {O : M} {r r₂ ε : ℝ} {p : ℕ}
    {g : SmoothRiemannianMetric I M} {h : SmoothRiemannianMetric I N}
    (hgnorm : ∀ (x : M) (v : TangentSpace I x),
      ‖v‖ₑ = ENNReal.ofReal (Real.sqrt (g.inner x v v)))
    (hhnorm : ∀ (y : N) (w : TangentSpace I y),
      ‖w‖ₑ = ENNReal.ofReal (Real.sqrt (h.inner y w w)))
    (hrr₂ : r ≤ r₂) (hε0 : 0 ≤ ε)
    (hdata : MapMetricApproximationOn (I := I)
      (Metric.closedEBall O (ENNReal.ofReal r₂)) ε p (Φ : M → N) g h)
    (hsub : Metric.closedEBall O (ENNReal.ofReal r₂) ⊆ Φ.source) :
    (Φ : M → N) '' Metric.eball O (ENNReal.ofReal r) ⊆
      Metric.closedEBall ((Φ : M → N) O)
        (ENNReal.ofReal (Real.sqrt (1 + ε) * r)) := by
  rw [ENNReal.ofReal_mul (Real.sqrt_nonneg _)]
  refine Geometry.Riemannian.image_eball_subset_closedEBall_of_path_length_le
    (I := I) (K := ENNReal.ofReal (Real.sqrt (1 + ε))) (Φ : M → N) O ?_
  intro y γ hγC hγ0 hγ1 hγlen
  have hrange : ∀ t ∈ Set.Icc (0 : ℝ) 1,
      γ t ∈ Metric.closedEBall O (ENNReal.ofReal r₂) := by
    intro t ht
    rw [Metric.mem_closedEBall, edist_comm, IsRiemannianManifold.out (I := I) O (γ t)]
    calc
      Manifold.riemannianEDist I O (γ t)
          ≤ Manifold.pathELength (I := I) γ 0 t := by
        refine Manifold.riemannianEDist_le_pathELength
          (hγC.mono (Set.Icc_subset_Icc le_rfl ht.2)) hγ0 rfl ht.1
      _ ≤ Manifold.pathELength (I := I) γ 0 1 :=
        Manifold.pathELength_mono (I := I) (γ := γ) (a' := 0) (b' := 1) le_rfl ht.2
      _ ≤ ENNReal.ofReal r := le_of_lt hγlen
      _ ≤ ENNReal.ofReal r₂ := ENNReal.ofReal_le_ofReal hrr₂
  refine ⟨(Φ : M → N) ∘ γ, ?_, by simp [Function.comp, hγ0],
    by simp [Function.comp, hγ1], ?_⟩
  · exact (Φ.contMDiffOn_toFun.of_le (by exact_mod_cast le_top)).comp hγC
      (fun t ht => hsub (hrange t ht))
  · rw [Manifold.pathELength_eq_lintegral_mfderiv_Ioo,
      Manifold.pathELength_eq_lintegral_mfderiv_Ioo,
      ← MeasureTheory.lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    refine MeasureTheory.lintegral_mono_ae
      (Filter.eventually_of_mem
        (MeasureTheory.self_mem_ae_restrict measurableSet_Ioo) ?_)
    intro t ht
    have htIcc : t ∈ Set.Icc (0 : ℝ) 1 := Set.mem_Icc_of_Ioo ht
    have hγt : γ t ∈ Metric.closedEBall O (ENNReal.ofReal r₂) := hrange t htIcc
    have hγd : MDifferentiableAt 𝓘(ℝ, ℝ) I γ t := by
      refine ((hγC.contMDiffAt ?_).mdifferentiableAt (by norm_num))
      exact Icc_mem_nhds ht.1 ht.2
    have hΦd : MDifferentiableAt I I (Φ : M → N) (γ t) :=
      (Φ.contMDiffOn_toFun.contMDiffAt
        (Φ.open_source.mem_nhds (hsub hγt))).mdifferentiableAt
        (by decide : (∞ : WithTop ℕ∞) ≠ 0)
    have hchain := mfderiv_comp t hΦd hγd
    have happ : mfderiv 𝓘(ℝ, ℝ) I ((Φ : M → N) ∘ γ) t 1 =
        mfderiv I I (Φ : M → N) (γ t) (mfderiv 𝓘(ℝ, ℝ) I γ t 1) := by
      rw [hchain]
      rfl
    rw [happ]
    set w := mfderiv 𝓘(ℝ, ℝ) I γ t 1 with hw
    have hPval : h.inner ((Φ : M → N) (γ t))
        (mfderiv I I (Φ : M → N) (γ t) w) (mfderiv I I (Φ : M → N) (γ t) w) =
        hdata.pullback (γ t) (fun _ => w) := by
      rw [hdata.pullback_apply (γ t) hγt (fun _ => w)]
    have hquad : hdata.pullback (γ t) (fun _ => w) ≤
        (1 + ε) * g.inner (γ t) w w :=
      (tensor_apply_bounds_of_metricTensorErrorNorm_le (I := I) hdata.pullback g
        (hdata.c0_small (γ t) hγt) w).2
    calc
      ‖mfderiv I I (Φ : M → N) (γ t) w‖ₑ =
          ENNReal.ofReal (Real.sqrt (h.inner ((Φ : M → N) (γ t))
            (mfderiv I I (Φ : M → N) (γ t) w)
            (mfderiv I I (Φ : M → N) (γ t) w))) := hhnorm _ _
      _ ≤ ENNReal.ofReal (Real.sqrt ((1 + ε) * g.inner (γ t) w w)) := by
        refine ENNReal.ofReal_le_ofReal (Real.sqrt_le_sqrt ?_)
        rw [hPval]
        exact hquad
      _ = ENNReal.ofReal (Real.sqrt (1 + ε))
          * ENNReal.ofReal (Real.sqrt (g.inner (γ t) w w)) := by
        rw [Real.sqrt_mul (by linarith : (0 : ℝ) ≤ 1 + ε),
          ENNReal.ofReal_mul (Real.sqrt_nonneg _)]
      _ = ENNReal.ofReal (Real.sqrt (1 + ε)) * ‖w‖ₑ := by
        rw [hgnorm (γ t) w]

end BallImage

end CheegerGromovCompactness
end DifferentialGeometry
