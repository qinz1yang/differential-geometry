import DifferentialGeometry.Geometry.Geodesic.Convergence.BufferedGeodesicEquation
import DifferentialGeometry.Geometry.Metric.Convergence.Metric.QuadraticBounds
import DifferentialGeometry.Geometry.Metric.Convergence.DerivativeNorm.Arity
import DifferentialGeometry.Topology.VectorBundle.Compactness
import Mathlib.Topology.Sequences

/-!
# Compact initial tangent extraction for the original converging metrics

Covariant order-zero convergence bounds the actual unit vectors in the fixed native bundle norm.
Compactness and continuity give a genuine unit limit in that same tangent bundle. The inverse
partial-diffeomorphism adapter retains the original target vectors and derivative-square metric.
-/

set_option autoImplicit false

noncomputable section

open Set Filter Bundle
open scoped Manifold ContDiff ENNReal Topology

namespace DifferentialGeometry.Geometry.Riemannian.Geodesic

open DifferentialGeometry.CheegerGromovCompactness

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {N : Type*} [TopologicalSpace N] [ChartedSpace H N] [IsManifold I ∞ N] [T3Space N]

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace

omit [NeZero (Module.finrank ℝ E)] [I.Boundaryless] [T3Space N] in
private theorem tangent_firstCountable : FirstCountableTopology (TangentBundle I N) := by
  let : SecondCountableTopology H := I.secondCountableTopology
  let : FirstCountableTopology (ModelProd H E) := by
    change FirstCountableTopology (H × E)
    infer_instance
  refine ⟨fun x => ?_⟩
  rw [(chartAt (ModelProd H E) x).nhds_eq_comap_inf_principal
    (mem_chart_source (ModelProd H E) x)]
  infer_instance

variable [RiemannianBundle (fun x : N => TangentSpace I x)]
  [IsContinuousRiemannianBundle E (fun x : N => TangentSpace I x)]

omit [NeZero (Module.finrank ℝ E)] [I.Boundaryless]
  [RiemannianBundle (fun x : N => TangentSpace I x)]
  [IsContinuousRiemannianBundle E (fun x : N => TangentSpace I x)] in
private theorem metricUnit_quad_tendsto
    (hSeq : ℕ → SmoothRiemannianMetric I N) (hInf : SmoothRiemannianMetric I N)
    {C : Set N} (hC : IsCompact C)
    (hconv : MetricCPConvergenceOn C 0 hSeq hInf hInf)
    (x : ℕ → TangentBundle I N) (hx : ∀ i, (x i).proj ∈ C)
    (hunit : ∀ i, (hSeq i).inner (x i).proj (x i).snd (x i).snd = 1) :
    Tendsto (fun i => hInf.inner (x i).proj (x i).snd (x i).snd) atTop (𝓝 1) := by
  have hhalf := hconv.eventually_quadratic_bounds hC (by norm_num : (0 : ℝ) < 1 / 2)
  rw [Metric.tendsto_nhds]
  intro epsilon hepsilon
  have heps := hconv.eventually_quadratic_bounds hC
    (by positivity : 0 < epsilon / 4)
  filter_upwards [hhalf, heps] with i hi hsmall
  have hh := (hi (x i).proj (hx i) (x i).snd).1
  have h1 := (hsmall (x i).proj (hx i) (x i).snd).1
  have h2 := (hsmall (x i).proj (hx i) (x i).snd).2
  rw [hunit i] at hh h1 h2
  have hbound : hInf.inner (x i).proj (x i).snd (x i).snd ≤ 2 := by linarith
  rw [Real.dist_eq, abs_lt]
  constructor <;> nlinarith

omit [NeZero (Module.finrank ℝ E)] [I.Boundaryless] in
theorem exists_metricUnit_tangent_subsequence
    (hSeq : ℕ → SmoothRiemannianMetric I N) (hInf : SmoothRiemannianMetric I N)
    (hNorm : DifferentialGeometry.Geometry.Riemannian.IsMetricNorm hInf)
    {C : Set N} (hC : IsCompact C)
    (hconv : MetricCPConvergenceOn C 0 hSeq hInf hInf)
    (x : ℕ → TangentBundle I N) (hx : ∀ i, (x i).proj ∈ C)
    (hunit : ∀ i, (hSeq i).inner (x i).proj (x i).snd (x i).snd = 1) :
    ∃ xInf : TangentBundle I N, xInf.proj ∈ C ∧
      hInf.inner xInf.proj xInf.snd xInf.snd = 1 ∧
      ∃ phi : ℕ → ℕ, StrictMono phi ∧ Tendsto (x ∘ phi) atTop (𝓝 xInf) := by
  let : ProperSpace E := FiniteDimensional.proper ℝ E
  let : FirstCountableTopology (TangentBundle I N) := tangent_firstCountable
  have hhalf := hconv.eventually_quadratic_bounds hC (by norm_num : (0 : ℝ) < 1 / 2)
  have hbounded : ∀ᶠ i in atTop, (x i).proj ∈ C ∧ ‖(x i).snd‖ ≤ 2 := by
    filter_upwards [hhalf] with i hi
    have hh := (hi (x i).proj (hx i) (x i).snd).1
    rw [hunit i, ← hNorm.inner_eq, real_inner_self_eq_norm_sq] at hh
    exact ⟨hx i, by nlinarith [norm_nonneg (x i).snd]⟩
  obtain ⟨xInf, hxInf, phi, hphi, hlim⟩ :=
    (hC.bundle_norm_le (F := E) (V := TangentSpace I) 2).tendsto_subseq' hbounded.frequently
  have hcontinuous : Continuous (fun y : TangentBundle I N =>
      hInf.inner y.proj y.snd y.snd) := by
    have hinner : Continuous (fun y : TangentBundle I N => inner ℝ y.snd y.snd) :=
      continuous_id.inner_bundle continuous_id
    exact hinner.congr (fun y => hNorm.inner_eq y.proj y.snd y.snd)
  have hmetriclim := (hcontinuous.tendsto xInf).comp hlim
  have hunitlim := (metricUnit_quad_tendsto hSeq hInf hC hconv x hx hunit).comp
    hphi.tendsto_atTop
  exact ⟨xInf, hxInf.1, tendsto_nhds_unique hmetriclim hunitlim, phi, hphi, hlim⟩

omit [NeZero (Module.finrank ℝ E)] [I.Boundaryless] in
theorem exists_inverse_metricUnit_tangent_subsequence
    {M : ℕ → Type*} [∀ i, MetricSpace (M i)] [∀ i, ChartedSpace H (M i)]
    [∀ i, IsManifold I ∞ (M i)]
    (hSeq : ℕ → SmoothRiemannianMetric I N) (hInf : SmoothRiemannianMetric I N)
    (hNorm : DifferentialGeometry.Geometry.Riemannian.IsMetricNorm hInf)
    {C : Set N} (hC : IsCompact C)
    (hconv : MetricCPConvergenceOn C 0 hSeq hInf hInf)
    (g : ∀ i, SmoothRiemannianMetric I (M i))
    (j : ∀ i, PartialDiffeomorph I I N (M i) ∞)
    (q : ℕ → N) (w : ∀ i, TangentSpace I (j i (q i)))
    (hqC : ∀ i, q i ∈ C) (hqSource : ∀ i, q i ∈ (j i).source)
    (hmetric : ∀ i, ∀ x ∈ (j i).source, ∀ v u : TangentSpace I x,
      (hSeq i).inner x v u = (g i).inner (j i x)
        (mfderiv I I (j i : N → M i) x v) (mfderiv I I (j i : N → M i) x u))
    (hunit : ∀ i, (g i).inner (j i (q i)) (w i) (w i) = 1) :
    ∃ xInf : TangentBundle I N, xInf.proj ∈ C ∧
      hInf.inner xInf.proj xInf.snd xInf.snd = 1 ∧
      ∃ phi : ℕ → ℕ, StrictMono phi ∧ Tendsto
        (fun n => (⟨q (phi n), mfderiv I I ((j (phi n)).symm : M (phi n) → N)
          (j (phi n) (q (phi n))) (w (phi n))⟩ : TangentBundle I N)) atTop (𝓝 xInf) := by
  let x (i : ℕ) : TangentBundle I N :=
    ⟨q i, mfderiv I I ((j i).symm : M i → N) (j i (q i)) (w i)⟩
  have hxunit (i : ℕ) : (hSeq i).inner (x i).proj (x i).snd (x i).snd = 1 := by
    have heq := metric_identity_of_partialDiffeomorph_inverse (hSeq i) (g i) (j i)
      (hmetric i) (j i (q i)) ((j i).map_source (hqSource i)) (w i) (w i)
    calc
      _ = (hSeq i).inner ((j i).symm (j i (q i))) (x i).snd (x i).snd :=
        congrArg (fun y : N => (hSeq i).inner y (x i).snd (x i).snd)
          ((j i).left_inv (hqSource i)).symm
      _ = (g i).inner (j i (q i)) (w i) (w i) := heq.symm
      _ = 1 := hunit i
  exact exists_metricUnit_tangent_subsequence hSeq hInf hNorm hC hconv x hqC hxunit

private instance realFinrankPositive : NeZero (Module.finrank ℝ ℝ) := ⟨by simp⟩

private theorem realMetricNorm : DifferentialGeometry.Geometry.Riemannian.IsMetricNorm
    (euclideanMetric (E := ℝ)) := by
  intro x v
  rw [← ofReal_norm, euclideanMetric_inner, real_inner_self_eq_norm_sq,
    Real.sqrt_sq_eq_abs, abs_of_nonneg (norm_nonneg v)]

private instance realRiemannianContinuous :
    IsContinuousRiemannianBundle ℝ (fun x : ℝ => TangentSpace 𝓘(ℝ, ℝ) x) :=
  realMetricNorm.isContinuousRiemannianBundle

theorem realUnit_tangent_subsequence :
    let g := euclideanMetric (E := ℝ)
    let j := (Diffeomorph.refl 𝓘(ℝ, ℝ) ℝ ∞).toPartialDiffeomorph
    ∃ xInf : TangentBundle 𝓘(ℝ, ℝ) ℝ, xInf.proj ∈ ({0} : Set ℝ) ∧
      g.inner xInf.proj xInf.snd xInf.snd = 1 ∧
      ∃ phi : ℕ → ℕ, StrictMono phi ∧ Tendsto
        (fun (_n : ℕ) => (⟨0, mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) (j.symm : ℝ → ℝ) 0 1⟩ :
          TangentBundle 𝓘(ℝ, ℝ) ℝ)) atTop (𝓝 xInf) := by
  let g := euclideanMetric (E := ℝ)
  let j := (Diffeomorph.refl 𝓘(ℝ, ℝ) ℝ ∞).toPartialDiffeomorph
  dsimp only
  refine exists_inverse_metricUnit_tangent_subsequence (M := fun i => ℝ)
    (fun i => g) g realMetricNorm (show IsCompact ({0} : Set ℝ) from isCompact_singleton)
    ?_ (fun i => g) (fun i => j) (fun i => 0) (fun i => 1) ?_ ?_ ?_ ?_
  · intro epsilon hepsilon
    exact ⟨0, fun i hi => by rw [metricDerivNormSupOn_self]; exact hepsilon⟩
  · intro i
    exact mem_singleton 0
  · intro i
    trivial
  · intro i y hy v w
    change g.inner y v w = g.inner y (mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) id y v)
      (mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) id y w)
    rw [mfderiv_id]
    rfl
  · intro i
    change inner ℝ (1 : ℝ) 1 = 1
    rw [real_inner_self_eq_norm_sq]
    norm_num

end DifferentialGeometry.Geometry.Riemannian.Geodesic
