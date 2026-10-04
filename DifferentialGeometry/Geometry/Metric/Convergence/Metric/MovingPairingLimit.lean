import DifferentialGeometry.Geometry.Metric.Convergence.Metric.Evaluation
import DifferentialGeometry.Geometry.Metric.Convergence.Time.Lipschitz
import DifferentialGeometry.Geometry.Metric.Convergence.DerivativeNorm.Arity
import DifferentialGeometry.Geometry.Metric.Euclidean

/-!
# Moving pairings under compact metric convergence

If metrics `hSeq i` converge to `hInf` in `C⁰` on a compact set `C`, a section `V` is continuous
on `C` and tangent vectors `p i` over `C` converge in the tangent bundle, then the moving pairings
`hSeq i (V, p i)` converge to `hInf (V, pInf)`. This is the pairing step of LC51 (master207A,
A:22607); it supersedes the uncompiled draft `MovingPairing.lean` of Codex X84.
-/

set_option autoImplicit false

noncomputable section

open Set Filter Bundle
open scoped Manifold ContDiff Topology

namespace DifferentialGeometry.CheegerGromovCompactness

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {N : Type*} [TopologicalSpace N] [ChartedSpace H N] [IsManifold I ∞ N] [T2Space N]

theorem MetricCPConvergenceOn.tendsto_inner_section_of_tendsto
    (hSeq : ℕ → SmoothRiemannianMetric I N) (hInf : SmoothRiemannianMetric I N)
    {C : Set N} (hC : IsCompact C) (hconv : MetricCPConvergenceOn C 0 hSeq hInf hInf)
    (V : (q : N) → TangentSpace I q)
    (hV : ContinuousOn (fun q => (⟨q, V q⟩ : TangentBundle I N)) C)
    (p : ℕ → TangentBundle I N) (pInf : TangentBundle I N)
    (hp : ∀ i, (p i).proj ∈ C) (hlim : Tendsto p atTop (𝓝 pInf)) :
    Tendsto (fun i => (hSeq i).inner (p i).proj (V (p i).proj) (p i).snd)
      atTop (𝓝 (hInf.inner pInf.proj (V pInf.proj) pInf.snd)) := by
  let : RiemannianBundle (fun x : N => TangentSpace I x) := ⟨hInf.toRiemannianMetric⟩
  let : IsContinuousRiemannianBundle E (fun x : N => TangentSpace I x) :=
    ⟨⟨hInf.inner, hInf.contMDiff.continuous, fun x v w => rfl⟩⟩
  have hbase : Tendsto (fun i => (p i).proj) atTop (𝓝 pInf.proj) :=
    (FiberBundle.continuous_proj E (TangentSpace I)).tendsto pInf |>.comp hlim
  have hpInf : pInf.proj ∈ C :=
    hC.isClosed.mem_of_tendsto hbase (Eventually.of_forall hp)
  have hwithin : Tendsto (fun i => (p i).proj) atTop (𝓝[C] pInf.proj) :=
    tendsto_nhdsWithin_iff.mpr ⟨hbase, Eventually.of_forall hp⟩
  have hVlim := (hV pInf.proj hpInf).tendsto.comp hwithin
  have hquad : Continuous (fun x : TangentBundle I N => hInf.inner x.proj x.snd x.snd) :=
    continuous_id.inner_bundle continuous_id
  have hnormP := (Real.continuous_sqrt.comp hquad).tendsto pInf |>.comp hlim
  have hnormV := (Real.continuous_sqrt.comp hquad).tendsto
    (⟨pInf.proj, V pInf.proj⟩ : TangentBundle I N) |>.comp hVlim
  let A := Real.sqrt (hInf.inner pInf.proj pInf.snd pInf.snd) + 1
  let B := Real.sqrt (hInf.inner pInf.proj (V pInf.proj) (V pInf.proj)) + 1
  have hA : 0 < A := by dsimp [A]; positivity
  have hB : 0 < B := by dsimp [B]; positivity
  have hAp : ∀ᶠ i in atTop,
      Real.sqrt (hInf.inner (p i).proj (p i).snd (p i).snd) < A :=
    hnormP.eventually (gt_mem_nhds (lt_add_one _))
  have hBV : ∀ᶠ i in atTop,
      Real.sqrt (hInf.inner (p i).proj (V (p i).proj) (V (p i).proj)) < B :=
    hnormV.eventually (gt_mem_nhds (lt_add_one _))
  have hpairCont : ContinuousOn
      (fun x : TangentBundle I N => hInf.inner x.proj (V x.proj) x.snd)
      (TotalSpace.proj ⁻¹' C) :=
    (hV.comp (FiberBundle.continuous_proj E (TangentSpace I)).continuousOn
      (fun x hx => hx)).inner_bundle continuous_id.continuousOn
  have hpWithin : Tendsto p atTop (𝓝[TotalSpace.proj ⁻¹' C] pInf) :=
    tendsto_nhdsWithin_iff.mpr ⟨hlim, Eventually.of_forall hp⟩
  have hpairLim := (hpairCont pInf hpInf).tendsto.comp hpWithin
  rw [Metric.tendsto_nhds] at hpairLim ⊢
  intro epsilon hepsilon
  obtain ⟨i0, hi0⟩ := hconv (epsilon / (2 * B * A)) (by positivity)
  filter_upwards [eventually_ge_atTop i0, hAp, hBV,
    hpairLim (epsilon / 2) (half_pos hepsilon)] with i hi hpi hvi hpair
  have hdiff := metricDifference_abs_le (hSeq i) hInf hInf (p i).proj
    (V (p i).proj) (p i).snd
  have hderiv := (derivNorm_le_sup hC le_rfl (hSeq i) hInf hInf (hp i)).trans_lt (hi0 i hi)
  have hdn : 0 ≤ metricDerivNorm 0 (hSeq i) hInf hInf (p i).proj := Real.sqrt_nonneg _
  have herr : |(hSeq i).inner (p i).proj (V (p i).proj) (p i).snd -
      hInf.inner (p i).proj (V (p i).proj) (p i).snd| < epsilon / 2 := by
    apply lt_of_le_of_lt hdiff
    calc
      _ ≤ metricDerivNorm 0 (hSeq i) hInf hInf (p i).proj * B * A := by
        gcongr
      _ < (epsilon / (2 * B * A)) * B * A := by gcongr
      _ = epsilon / 2 := by field_simp
  simp only [Function.comp_apply] at hpair
  rw [Real.dist_eq] at hpair ⊢
  exact lt_of_le_of_lt
    (abs_sub_le _ (hInf.inner (p i).proj (V (p i).proj) (p i).snd) _) (by linarith)

theorem realConstant_inner_section_limit :
    Tendsto (fun _i : ℕ => (euclideanMetric (E := ℝ)).inner (0 : ℝ) (2 : ℝ) (1 : ℝ))
      atTop (𝓝 ((euclideanMetric (E := ℝ)).inner (0 : ℝ) (2 : ℝ) (1 : ℝ))) := by
  let g := euclideanMetric (E := ℝ)
  apply MetricCPConvergenceOn.tendsto_inner_section_of_tendsto (fun _i : ℕ => g) g
    (C := {0}) isCompact_singleton
    (fun epsilon hepsilon => ⟨0, fun _i _hi => by
      rw [metricDerivNormSupOn_self]; exact hepsilon⟩)
    (fun _q => (2 : ℝ))
    (continuousOn_singleton _ _)
    (fun _i : ℕ => (⟨0, (1 : ℝ)⟩ : TangentBundle 𝓘(ℝ, ℝ) ℝ))
    (⟨0, (1 : ℝ)⟩ : TangentBundle 𝓘(ℝ, ℝ) ℝ)
    (fun _i : ℕ => mem_singleton 0) tendsto_const_nhds

end DifferentialGeometry.CheegerGromovCompactness
