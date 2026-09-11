import DifferentialGeometry.Geometry.Exponential.Inverse.Radius
import DifferentialGeometry.Geometry.Comparison.Distance.Calabi
import Mathlib.Topology.Sequences

set_option autoImplicit false

noncomputable section

open Bundle Filter Manifold Set
open scoped Topology ContDiff Manifold
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Geometry.Riemannian
open DifferentialGeometry.Geometry.Riemannian.Exponential
open DifferentialGeometry.Geometry.Riemannian.HopfRinow

namespace DifferentialGeometry.Geometry.Topology

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {M : Type*} [MetricSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M] [SigmaCompactSpace M]

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace

variable [RiemannianBundle (fun x : M => TangentSpace I x)]
  [IsRiemannianManifold I M] [CompleteSpace M]
  [IsContinuousRiemannianBundle E (fun x : M => TangentSpace I x)]

omit [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)] [I.Boundaryless]
  [IsManifold I ∞ M] [SigmaCompactSpace M] [CompleteSpace M]
  [IsContinuousRiemannianBundle E (fun x : M => TangentSpace I x)] in
private theorem riemannian_toReal_eq_dist (p q : M) :
    (riemannianEDist I p q).toReal = dist p q := by
  rw [← IsRiemannianManifold.out (I := I), edist_dist,
    ENNReal.toReal_ofReal dist_nonneg]

theorem tendsto_minimizing_vectors_of_unique
    (g : SmoothRiemannianMetric I M) (hEnorm : IsMetricNorm (I := I) (M := M) g)
    (p q : M) (u : TangentSpace I p) (v : M → TangentSpace I p)
    (hexp : ∀ y, expMapIntrinsic (I := I) g hEnorm p (v y) = y)
    (hlen : ∀ y, Real.sqrt (g.inner p (v y) (v y)) = dist p y)
    (huniq : ∀ w : TangentSpace I p,
      expMapIntrinsic (I := I) g hEnorm p w = q →
      Real.sqrt (g.inner p w w) = dist p q → w = u) :
    Tendsto v (𝓝 q) (𝓝 u) := by
  rw [Filter.tendsto_iff_seq_tendsto]
  intro seq hseq
  apply Filter.tendsto_of_subseq_tendsto
  intro ns hns
  have hz : Tendsto (fun n => seq (ns n)) atTop (𝓝 q) := hseq.comp hns
  have hdseq : Tendsto (fun n => dist p (seq (ns n))) atTop (𝓝 (dist p q)) :=
    tendsto_const_nhds.dist hz
  have hdbdd := Metric.isBounded_range_of_tendsto _ hdseq
  rw [isBounded_iff_forall_norm_le] at hdbdd
  obtain ⟨C, hC⟩ := hdbdd
  let K : Set (TangentSpace I p) := {w | Real.sqrt (g.inner p w w) ≤ max 0 C}
  have hK : IsCompact K := gLenBall_isCompact (I := I) g p (max 0 C)
  have hvK (n : ℕ) : v (seq (ns n)) ∈ K := by
    change Real.sqrt (g.inner p (v (seq (ns n))) (v (seq (ns n)))) ≤ max 0 C
    rw [hlen]
    have hbound := hC _ ⟨n, rfl⟩
    rw [Real.norm_eq_abs, abs_of_nonneg dist_nonneg] at hbound
    exact hbound.trans (le_max_right _ _)
  obtain ⟨w, _, phi, hphi, hw⟩ := hK.tendsto_subseq hvK
  have hzphi : Tendsto (fun n => seq (ns (phi n))) atTop (𝓝 q) :=
    hz.comp hphi.tendsto_atTop
  have hmap : Tendsto (fun n => expMapIntrinsic (I := I) g hEnorm p
      (v (seq (ns (phi n))))) atTop (𝓝 (expMapIntrinsic (I := I) g hEnorm p w)) := by
    simpa only [Function.comp_def] using
      ((expMapIntrinsic_continuous (I := I) g hEnorm p).tendsto w).comp hw
  have hmapq : Tendsto (fun n => expMapIntrinsic (I := I) g hEnorm p
      (v (seq (ns (phi n))))) atTop (𝓝 q) := by
    simpa only [hexp] using hzphi
  have hwend : expMapIntrinsic (I := I) g hEnorm p w = q :=
    tendsto_nhds_unique hmap hmapq
  have hnorm : Tendsto (fun n => Real.sqrt
      (g.inner p (v (seq (ns (phi n)))) (v (seq (ns (phi n))))))
      atTop (𝓝 (Real.sqrt (g.inner p w w))) := by
    simpa only [Function.comp_def] using
      ((continuous_sqrt_gInner_self (I := I) g p).tendsto w).comp hw
  have hnormq : Tendsto (fun n => Real.sqrt
      (g.inner p (v (seq (ns (phi n)))) (v (seq (ns (phi n))))))
      atTop (𝓝 (dist p q)) := by
    simpa only [hlen] using
      (tendsto_const_nhds : Tendsto (fun _ : ℕ => p) atTop (𝓝 p)).dist hzphi
  have hwlen : Real.sqrt (g.inner p w w) = dist p q :=
    tendsto_nhds_unique hnorm hnormq
  refine ⟨phi, ?_⟩
  rw [huniq w hwend hwlen] at hw
  exact hw

theorem contMDiffAt_dist_of_unique_minimizing_exp
    (g : SmoothRiemannianMetric I M) (hEnorm : IsMetricNorm (I := I) (M := M) g)
    (p q : M) (u : TangentSpace I p)
    (hexp : expMapIntrinsic (I := I) g hEnorm p u = q)
    (hupos : 0 < g.inner p u u)
    (hnot : ¬ IsConjVec (I := I) g hEnorm p
      (tangentSpaceModelContinuousLinearEquiv (I := I) p u))
    (huniq : ∀ w : TangentSpace I p,
      expMapIntrinsic (I := I) g hEnorm p w = q →
      Real.sqrt (g.inner p w w) = dist p q → w = u) :
    ContMDiffAt I 𝓘(ℝ, ℝ) ∞ (fun y : M => dist p y) q := by
  classical
  have hmin (y : M) : ∃ w : TangentSpace I p,
      expMapIntrinsic (I := I) g hEnorm p w = y ∧
        Real.sqrt (g.inner p w w) = dist p y := by
    have hfin : riemannianEDist I p y ≠ ⊤ := by
      rw [← IsRiemannianManifold.out (I := I)]
      exact edist_ne_top p y
    simpa only [riemannian_toReal_eq_dist (I := I)] using
      minExp_of_ne_top (I := I) g hEnorm p y hfin
  choose v hv hlen using hmin
  have hvlim := tendsto_minimizing_vectors_of_unique (I := I) g hEnorm p q u v hv hlen huniq
  obtain ⟨B, huB⟩ := branch_of_not_conj (I := I) g hEnorm hnot
  have hmem : ∀ᶠ y in 𝓝 q,
      tangentSpaceModelContinuousLinearEquiv (I := I) p (v y) ∈ B.hom.source :=
    ((tangentSpaceModelContinuousLinearEquiv (I := I) p).continuous.tendsto u).comp hvlim
      (B.hom.open_source.mem_nhds huB)
  have hagree : branchRadius (I := I) g B =ᶠ[𝓝 q] fun y => dist p y := by
    filter_upwards [hmem] with y hy
    calc
      _ = branchRadius (I := I) g B (expMapIntrinsic (I := I) g hEnorm p (v y)) := by rw [hv]
      _ = Real.sqrt (g.inner p (v y) (v y)) := branchRadius_exp (I := I) B hy
      _ = dist p y := hlen y
  have hsmooth := branchRadius_infAt (I := I) B huB hupos
  rw [hexp] at hsmooth
  exact hsmooth.congr_of_eventuallyEq hagree.symm

end DifferentialGeometry.Geometry.Topology

end
