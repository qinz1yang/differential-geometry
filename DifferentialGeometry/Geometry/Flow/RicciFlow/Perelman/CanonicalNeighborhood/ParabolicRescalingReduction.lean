import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.ConeBlowupLimitReduction
import DifferentialGeometry.Geometry.Flow.RicciFlow.Scaling.Parabolic
import DifferentialGeometry.Geometry.Metric.RicciSoliton.Models

set_option autoImplicit false
noncomputable section
open scoped Topology

namespace DifferentialGeometry.CheegerGromovCompactness

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace Real E]
variable [FiniteDimensional Real E] [CompleteSpace E]
variable {H : Type*} [TopologicalSpace H]
variable {I : ModelWithCorners Real E H}

theorem metricPullbackTendsto_reindex
    {X : PointedFlowSeq (I := I)}
    {L : PointedFlowData (I := I) X.D}
    {subseq : Nat → Nat}
    {Φ : PointedCGHMaps (I := I) X (L.atTime 0) subseq}
    (h : MetricPullbackTendsto (I := I) Φ)
    (φ : Nat → Nat) (hφ : StrictMono φ) :
    MetricPullbackTendsto (I := I) (Φ.compSubseq φ hφ) := by
  intro t ht x v w
  exact (h t ht x v w).comp hφ.tendsto_atTop

theorem scalarPullbackTendsto_reindex
    {X : PointedFlowSeq (I := I)}
    {L : PointedFlowData (I := I) X.D}
    {subseq : Nat → Nat}
    {Φ : PointedCGHMaps (I := I) X (L.atTime 0) subseq}
    (h : ScalarPullbackTendsto (I := I) Φ)
    (φ : Nat → Nat) (hφ : StrictMono φ) :
    ScalarPullbackTendsto (I := I) (Φ.compSubseq φ hφ) := by
  intro t ht x
  exact (h t ht x).comp hφ.tendsto_atTop

theorem ricciPullbackTendsto_reindex
    {X : PointedFlowSeq (I := I)}
    {L : PointedFlowData (I := I) X.D}
    {subseq : Nat → Nat}
    {Φ : PointedCGHMaps (I := I) X (L.atTime 0) subseq}
    (h : RicciPullbackTendsto (I := I) Φ)
    (φ : Nat → Nat) (hφ : StrictMono φ) :
    RicciPullbackTendsto (I := I) (Φ.compSubseq φ hφ) := by
  intro t ht x v w
  exact (h t ht x v w).comp hφ.tendsto_atTop

theorem ricNormPullback_reindex
    {X : PointedFlowSeq (I := I)}
    {L : PointedFlowData (I := I) X.D}
    {subseq : Nat → Nat}
    {Φ : PointedCGHMaps (I := I) X (L.atTime 0) subseq}
    (h : RicNormPullback (I := I) Φ)
    (φ : Nat → Nat) (hφ : StrictMono φ) :
    RicNormPullback (I := I) (Φ.compSubseq φ hφ) := by
  intro t ht x
  exact (h t ht x).comp hφ.tendsto_atTop

def SourceDomainMetricDataReindexing
    {X : PointedFlowSeq (I := I)}
    {P : PointedRiemannianManifold (I := I)}
    {subseq : Nat → Nat}
    (Φ : PointedCGHMaps (I := I) X P subseq) (φ : Nat → Nat) (hφ : StrictMono φ) : Prop :=
  ∀ D : ∀ k : Nat, SourceDomainMetricData (I := I) Φ k,
    ∃ D' : ∀ k : Nat, SourceDomainMetricData (I := I) (Φ.compSubseq φ hφ) k,
      ∀ (k : Nat) (K : Set P.M) (p : Nat) (t : Real),
        (D' k).derivNormSupOn (I := I) K p t = (D (φ k)).derivNormSupOn (I := I) K p t

theorem smoothCGHConverges_compSubseq_of_sourceDomainMetricDataReindexing
    {X : PointedFlowSeq (I := I)}
    {L : PointedFlowData (I := I) X.D}
    {subseq : Nat → Nat}
    (hc : SmoothCGHConverges (I := I) X L subseq)
    (φ : Nat → Nat) (hφ : StrictMono φ)
    (h : SourceDomainMetricDataReindexing (I := I) hc.spatial.maps φ hφ) :
    Nonempty (SmoothCGHConverges (I := I) X L (subseq ∘ φ)) := by
  obtain ⟨D', hD'⟩ := h hc.spatial.metrics.domain
  refine ⟨{
    spatial := {
      maps := hc.spatial.maps.compSubseq φ hφ
      metrics := {
        domain := D'
        converges := by
          intro K hK p t ht ε hε
          obtain ⟨k0, hk0⟩ := hc.spatial.metrics.converges K hK p t ht ε hε
          refine ⟨k0, fun k hk => ?_⟩
          obtain ⟨hsrc, hbound⟩ := hk0 (φ k) (le_trans hk hφ.le_apply)
          exact ⟨by simpa only [PointedCGHMaps.compSubseq_source] using hsrc,
            by rw [hD' k K p t]; exact hbound⟩ } }
    metric_converges := metricPullbackTendsto_reindex (I := I) hc.metric_converges φ hφ
    scalar_converges := scalarPullbackTendsto_reindex (I := I) hc.scalar_converges φ hφ
    ricci_converges := ricciPullbackTendsto_reindex (I := I) hc.ricci_converges φ hφ
    ricciNorm_converges := ricNormPullback_reindex (I := I) hc.ricciNorm_converges φ hφ
    spacetime := {
      converges_on_windows := by
        intro K hK p a b hab ε hε
        obtain ⟨k0, hk0⟩ := hc.spacetime.converges_on_windows K hK p a b hab ε hε
        refine ⟨k0, fun k hk => ?_⟩
        obtain ⟨hsrc, hbound⟩ := hk0 (φ k) (le_trans hk hφ.le_apply)
        exact ⟨by simpa only [PointedCGHMaps.compSubseq_source] using hsrc,
          fun t ht => by rw [hD' k K p t]; exact hbound t ht⟩ } }⟩

end DifferentialGeometry.CheegerGromovCompactness

namespace DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn

open DifferentialGeometry.Geometry.Curvature DifferentialGeometry.CheegerGromovCompactness
open DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
open scoped Manifold ContDiff ENNReal

universe u

attribute [local instance] PointedFlowData.topology PointedFlowData.charted
  PointedFlowData.smooth PointedFlowData.t2 PointedFlowData.sigmaCompact

noncomputable abbrev parabolicRescale {D : RealTimeInterval}
    (F : PointedFlowData.{u, 0, 0} I3 D) (t Q : ℝ) (hQ : 0 < Q) (ht : t ∈ D.carrier) :
    PointedFlowData.{u, 0, 0} I3 (parabolicInterval D t Q ht) where
  M := F.M
  topology := F.topology
  charted := F.charted
  smooth := F.smooth
  sigmaCompact := F.sigmaCompact
  t2 := F.t2
  t2TangentBundle := F.t2TangentBundle
  basepoint := F.basepoint
  S := parabolicSolution (I := I3) F.S t Q hQ ht
  isSolution := parabolicSolution_isSolutionOn (I := I3) F.S F.isSolution t Q hQ ht

@[simp] theorem parabolicRescale_basepoint {D : RealTimeInterval}
    (F : PointedFlowData.{u, 0, 0} I3 D) (t Q : ℝ) (hQ : 0 < Q) (ht : t ∈ D.carrier) :
    (parabolicRescale F t Q hQ ht).basepoint = F.basepoint := rfl

@[simp] theorem parabolicRescale_solution {D : RealTimeInterval}
    (F : PointedFlowData.{u, 0, 0} I3 D) (t Q : ℝ) (hQ : 0 < Q) (ht : t ∈ D.carrier) :
    (parabolicRescale F t Q hQ ht).S =
      parabolicSolution (I := I3) F.S t Q hQ ht := rfl

theorem parabolicRescale_metric {D : RealTimeInterval}
    (F : PointedFlowData.{u, 0, 0} I3 D) (t Q : ℝ) (hQ : 0 < Q) (ht : t ∈ D.carrier)
    (s : ℝ) :
    (parabolicRescale F t Q hQ ht).S.base.metric s =
      DifferentialGeometry.scaleMetric (I := I3) Q hQ
        (F.S.base.metric (parabolicTime t Q s)) := by
  rw [parabolicRescale_solution, parabolicSolution_metric]

@[simp] theorem parabolicRescale_metric_zero {D : RealTimeInterval}
    (F : PointedFlowData.{u, 0, 0} I3 D) (t Q : ℝ) (hQ : 0 < Q) (ht : t ∈ D.carrier) :
    (parabolicRescale F t Q hQ ht).S.base.metric 0 =
      DifferentialGeometry.scaleMetric (I := I3) Q hQ (F.S.base.metric t) := by
  rw [parabolicRescale_metric, parabolicTime_zero]

theorem parabolicRescale_scalar {D : RealTimeInterval}
    (F : PointedFlowData.{u, 0, 0} I3 D) (t Q : ℝ) (hQ : 0 < Q) (ht : t ∈ D.carrier)
    (s : ℝ) (x : F.M) :
    (parabolicRescale F t Q hQ ht).S.scalar s x =
      Q⁻¹ * F.S.scalar (parabolicTime t Q s) x := by
  rw [parabolicRescale_solution, parabolicSolution_scalar]

theorem parabolicRescale_rm04 {D : RealTimeInterval}
    (F : PointedFlowData.{u, 0, 0} I3 D) (t Q : ℝ) (hQ : 0 < Q) (ht : t ∈ D.carrier)
    (s : ℝ) (x : F.M) (v : Fin 4 → TangentSpace I3 x) :
    metricRm04At (I := I3) ((parabolicRescale F t Q hQ ht).S.base.metric s) x v =
      Q * metricRm04At (I := I3) (F.S.base.metric (parabolicTime t Q s)) x v := by
  have h := congrArg (fun A : Tensor04At (I := I3) (M := F.M) x => A v)
    (parabolicSolution_rm04 (I := I3) F.S t Q hQ ht s x)
  simpa only [parabolicRescale_solution, SolutionFamily.rm04, metricRm04_apply,
    smul_apply, smul_eq_mul] using h

theorem parabolicRescale_rmNormSq {D : RealTimeInterval}
    (F : PointedFlowData.{u, 0, 0} I3 D) (t Q : ℝ) (hQ : 0 < Q) (ht : t ∈ D.carrier)
    (s : ℝ) (x : F.M) :
    Tensor0SBundle.normSq0S (I := I3) ((parabolicRescale F t Q hQ ht).S.base.metric s) x 4
        (metricRm04At (I := I3) ((parabolicRescale F t Q hQ ht).S.base.metric s) x) =
      (Q⁻¹) ^ 2 * Tensor0SBundle.normSq0S (I := I3)
        (F.S.base.metric (parabolicTime t Q s)) x 4
        (metricRm04At (I := I3) (F.S.base.metric (parabolicTime t Q s)) x) := by
  have h := parabolicRmNormSq (I := I3) F.S t Q hQ ht s x
  simpa only [parabolicRescale_solution, SolutionFamily.rm04, metricRm04_apply] using h

theorem parabolicRescale_scalarAtBase {D : RealTimeInterval}
    (F : PointedFlowData.{u, 0, 0} I3 D) (t Q : ℝ) (hQ : 0 < Q) (ht : t ∈ D.carrier)
    (hbase : F.S.scalar t F.basepoint = Q) :
    PointedFlowScalarAtBase (parabolicRescale F t Q hQ ht) 1 := by
  have hcoe : (parabolicRescale F t Q hQ ht).basepoint = F.basepoint := rfl
  change (parabolicRescale F t Q hQ ht).S.scalar 0
    (parabolicRescale F t Q hQ ht).basepoint = 1
  rw [hcoe, parabolicRescale_scalar, parabolicTime_zero, hbase]
  field_simp

theorem parabolicRescale_curvDerivNormSq {D : RealTimeInterval}
    (F : PointedFlowData.{u, 0, 0} I3 D) (t Q : ℝ) (hQ : 0 < Q) (ht : t ∈ D.carrier)
    (s : ℝ) (y : F.M) :
    curvDerivNormSq (I := I3) 0 ((parabolicRescale F t Q hQ ht).S.base.metric s) y =
      (Q⁻¹) ^ 2 * curvDerivNormSq (I := I3) 0
        (F.S.base.metric (parabolicTime t Q s)) y := by
  have h₁ : curvCovDeriv (I := I3) (M := F.M)
      ((parabolicRescale F t Q hQ ht).S.base.metric s) 0 =
      metricRm04 (I := I3) (M := F.M)
        ((parabolicRescale F t Q hQ ht).S.base.metric s) := rfl
  have h₂ : curvCovDeriv (I := I3) (M := F.M)
      (F.S.base.metric (parabolicTime t Q s)) 0 =
      metricRm04 (I := I3) (M := F.M) (F.S.base.metric (parabolicTime t Q s)) := rfl
  rw [curvDerivNormSq, curvDerivNormSq, h₁, h₂, metricRm04_apply, metricRm04_apply]
  exact parabolicRescale_rmNormSq F t Q hQ ht s y

theorem secLower_scaleMetric {M : Type u} [TopologicalSpace M] [ChartedSpace ThreeSpace M]
    [IsManifold I3 ∞ M] [IsManifold I3 1 M] [T2Space M] [SigmaCompactSpace M]
    (g : SmoothRiemannianMetric I3 M) (c a : ℝ) (hc : 0 < c) (U : Set M) :
    SecLower (DifferentialGeometry.scaleMetric (I := I3) c hc g) a U ↔
      SecLower g (c * a) U := by
  have hrm : ∀ x : M, metricRm04At (I := I3)
      (DifferentialGeometry.scaleMetric (I := I3) c hc g) x =
        c • metricRm04At (I := I3) g x := fun x =>
    (by simpa only [metricRm04_apply] using metricRm_scale (I := I3) c hc g x)
  constructor
  · intro h x hx v w
    have h₁ := h x hx v w
    have h₂ := congrArg (fun A : Tensor04At (I := I3) (M := M) x =>
      A (fun i : Fin 4 => ![v, w, w, v] i)) (hrm x)
    simp only [smul_apply, smul_eq_mul] at h₂
    simp only [scaleMetric_inner] at h₁
    rw [h₂] at h₁
    refine (mul_le_mul_iff_of_pos_left hc).mp ?_
    have heq : a * (c * g.inner x v v * (c * g.inner x w w) -
        (c * g.inner x v w) ^ 2) =
        c * (c * a * (g.inner x v v * g.inner x w w - (g.inner x v w) ^ 2)) := by
      ring
    rw [heq] at h₁
    exact h₁
  · intro h x hx v w
    have h₁ := h x hx v w
    have h₂ := congrArg (fun A : Tensor04At (I := I3) (M := M) x =>
      A (fun i : Fin 4 => ![v, w, w, v] i)) (hrm x)
    simp only [smul_apply, smul_eq_mul] at h₂
    simp only [scaleMetric_inner]
    rw [h₂]
    have heq : a * (c * g.inner x v v * (c * g.inner x w w) -
        (c * g.inner x v w) ^ 2) =
        c * (c * a * (g.inner x v v * g.inner x w w - (g.inner x v w) ^ 2)) := by
      ring
    rw [heq]
    exact mul_le_mul_of_nonneg_left h₁ hc.le

theorem secLower_scaleMetric_zero {M : Type u} [TopologicalSpace M] [ChartedSpace ThreeSpace M]
    [IsManifold I3 ∞ M] [IsManifold I3 1 M] [T2Space M] [SigmaCompactSpace M]
    (g : SmoothRiemannianMetric I3 M) (c : ℝ) (hc : 0 < c) (U : Set M) :
    SecLower (DifferentialGeometry.scaleMetric (I := I3) c hc g) 0 U ↔ SecLower g 0 U := by
  simpa using secLower_scaleMetric g c 0 hc U

theorem secLower_parabolicRescale {D : RealTimeInterval}
    (F : PointedFlowData.{u, 0, 0} I3 D) (t Q : ℝ) (hQ : 0 < Q) (ht : t ∈ D.carrier)
    (s : ℝ) (U : Set F.M) :
    SecLower ((parabolicRescale F t Q hQ ht).S.base.metric s) 0 U ↔
      SecLower (F.S.base.metric (parabolicTime t Q s)) 0 U := by
  rw [parabolicRescale_metric]
  exact secLower_scaleMetric_zero (F.S.base.metric (parabolicTime t Q s)) Q hQ U

def ParabolicRmBallBound {D : RealTimeInterval} (F : PointedFlowData.{u, 0, 0} I3 D)
    (s scale ρ C : ℝ) : Prop :=
  ∀ y : F.M,
    ENNReal.ofReal scale *
        riemannianEDistOf (I := I3) (F.S.base.metric s) F.basepoint y ≤
      ENNReal.ofReal ρ →
    curvDerivNormSq (I := I3) 0 (F.S.base.metric s) y ≤ C

theorem parabolicRescale_rmBallBound_iff {D : RealTimeInterval}
    (F : PointedFlowData.{u, 0, 0} I3 D) (t Q : ℝ) (hQ : 0 < Q) (ht : t ∈ D.carrier)
    (s scale ρ C : ℝ) :
    ParabolicRmBallBound (parabolicRescale F t Q hQ ht) s scale ρ C ↔
      ParabolicRmBallBound F (parabolicTime t Q s) (Real.sqrt Q * scale) ρ (Q ^ 2 * C) := by
  have hcoef : Q ^ 2 * (Q⁻¹) ^ 2 = 1 := by
    field_simp
  have hcoef' : (Q⁻¹) ^ 2 * Q ^ 2 = 1 := by
    rw [mul_comm, hcoef]
  have hdist : ∀ y : F.M,
      riemannianEDistOf (I := I3) ((parabolicRescale F t Q hQ ht).S.base.metric s)
          (parabolicRescale F t Q hQ ht).basepoint y =
        ENNReal.ofReal (Real.sqrt Q) *
          riemannianEDistOf (I := I3) (F.S.base.metric (parabolicTime t Q s))
            F.basepoint y := by
    intro y
    rw [parabolicRescale_basepoint, parabolicRescale_metric, edistOf_scale]
  have hkey : ∀ e : ℝ≥0∞,
      ENNReal.ofReal (Real.sqrt Q * scale) * e =
        ENNReal.ofReal scale * (ENNReal.ofReal (Real.sqrt Q) * e) := by
    intro e
    calc ENNReal.ofReal (Real.sqrt Q * scale) * e
        = (ENNReal.ofReal (Real.sqrt Q) * ENNReal.ofReal scale) * e := by
          rw [ENNReal.ofReal_mul (Real.sqrt_nonneg Q)]
      _ = ENNReal.ofReal scale * (ENNReal.ofReal (Real.sqrt Q) * e) := by
          rw [mul_comm (ENNReal.ofReal (Real.sqrt Q)) (ENNReal.ofReal scale), mul_assoc]
  have hscaled : ∀ y : F.M,
      ENNReal.ofReal scale *
          riemannianEDistOf (I := I3) ((parabolicRescale F t Q hQ ht).S.base.metric s)
            (parabolicRescale F t Q hQ ht).basepoint y ≤ ENNReal.ofReal ρ ↔
        ENNReal.ofReal (Real.sqrt Q * scale) *
          riemannianEDistOf (I := I3) (F.S.base.metric (parabolicTime t Q s)) F.basepoint y ≤
            ENNReal.ofReal ρ := by
    intro y
    rw [hdist y]
    exact ⟨fun h => by
      rw [hkey]
      exact h, fun h => by
      rw [← hkey]
      exact h⟩
  constructor
  · intro h y hy
    have hy' := (hscaled y).mpr hy
    have h₁ := h y hy'
    rw [parabolicRescale_curvDerivNormSq] at h₁
    calc curvDerivNormSq (I := I3) 0 (F.S.base.metric (parabolicTime t Q s)) y
        = Q ^ 2 * ((Q⁻¹) ^ 2 *
            curvDerivNormSq (I := I3) 0 (F.S.base.metric (parabolicTime t Q s)) y) := by
          rw [← mul_assoc, hcoef, one_mul]
      _ ≤ Q ^ 2 * C := mul_le_mul_of_nonneg_left h₁ (by positivity)
  · intro h y hy
    have hy' := (hscaled y).mp hy
    have h₁ := h y hy'
    rw [parabolicRescale_curvDerivNormSq]
    calc (Q⁻¹) ^ 2 * curvDerivNormSq (I := I3) 0
          (F.S.base.metric (parabolicTime t Q s)) y
        ≤ (Q⁻¹) ^ 2 * (Q ^ 2 * C) := mul_le_mul_of_nonneg_left h₁ (by positivity)
      _ = C := by rw [← mul_assoc, hcoef', one_mul]

theorem normalizedSequence_zero_mem {eps kappa sigma : ℝ} {Phi : ℝ → ℝ}
    (X : NormalizedSequence.{u} eps kappa sigma Phi) (i : ℕ) :
    0 ∈ (X.interval i).carrier := by
  rw [X.carrier_eq i]
  exact ⟨by linarith [X.depth_pos i], le_rfl⟩

noncomputable abbrev parabolicRescaledSlice {eps kappa sigma : ℝ} {Phi : ℝ → ℝ}
    (X : NormalizedSequence.{u} eps kappa sigma Phi) (i : ℕ) :
    PointedFlowData.{u, 0, 0} I3
      (parabolicInterval (X.interval i) 0 (X.scale i) (normalizedSequence_zero_mem X i)) :=
  parabolicRescale (X.term i) 0 (X.scale i) (X.scale_pos i) (normalizedSequence_zero_mem X i)

theorem parabolicRescaledSlice_metric_eq_rescaledMetric {eps kappa sigma : ℝ} {Phi : ℝ → ℝ}
    (X : NormalizedSequence.{u} eps kappa sigma Phi) (i : ℕ) (s : ℝ) :
    (parabolicRescaledSlice X i).S.base.metric s =
      rescaledMetric (I := I3) (X.term i).S 0 (X.scale i) (X.scale_pos i) s := by
  rw [parabolicRescale_metric]
  rfl

theorem parabolicRescaledSlice_rmBallBound_iff {eps kappa sigma : ℝ} {Phi : ℝ → ℝ}
    (X : NormalizedSequence.{u} eps kappa sigma Phi) (i : ℕ) (s scale ρ C : ℝ) :
    ParabolicRmBallBound (parabolicRescaledSlice X i) s scale ρ C ↔
      ParabolicRmBallBound (X.term i) (parabolicTime 0 (X.scale i) s)
        (Real.sqrt (X.scale i) * scale) ρ ((X.scale i) ^ 2 * C) :=
  parabolicRescale_rmBallBound_iff (X.term i) 0 (X.scale i) (X.scale_pos i)
    (normalizedSequence_zero_mem X i) s scale ρ C

def TerminalScaledRmBallBound {eps kappa sigma : ℝ} {Phi : ℝ → ℝ}
    (X : NormalizedSequence.{u} eps kappa sigma Phi) (start ρ C : ℝ) : Prop :=
  ∀ i, ∀ s ∈ Set.Icc start 0,
    ParabolicRmBallBound (X.term i) (parabolicTime 0 (X.scale i) s)
      (Real.sqrt (X.scale i)) ρ ((X.scale i) ^ 2 * C)

theorem parabolicRescaledSlice_rmBallBound_of_terminalScaledRmBallBound
    {eps kappa sigma : ℝ} {Phi : ℝ → ℝ}
    (X : NormalizedSequence.{u} eps kappa sigma Phi) {start ρ C : ℝ}
    (h : TerminalScaledRmBallBound X start ρ C) :
    ∀ i, ∀ s ∈ Set.Icc start 0,
      ParabolicRmBallBound (parabolicRescaledSlice X i) s 1 ρ C := by
  intro i s hs
  rw [parabolicRescaledSlice_rmBallBound_iff, mul_one]
  exact h i s hs

structure RescaledLimitFlow {eps kappa sigma : ℝ} {Phi : ℝ → ℝ}
    (X : NormalizedSequence.{u} eps kappa sigma Phi) where
  delta : ℝ
  delta_pos : 0 < delta
  flow : PointedFlowData.{u, 0, 0} I3 (RealTimeInterval.closed (-delta) 0 (by linarith))
  limit_complete : MetricComplete (flow.atTime 0)
  normalized : PointedFlowScalarAtBase flow 1
  subseq : ℕ → ℕ
  strictMono : StrictMono subseq
  scale : ℕ → ℝ
  scale_pos : ∀ i, 0 < scale i
  scale_tendsto : Filter.Tendsto scale Filter.atTop Filter.atTop
  scale_eq : ∀ i, scale i = X.scale (subseq i)
  map : ∀ i, PartialDiffeomorph I3 I3 flow.M (X.term (subseq i)).M ∞
  window : ∀ᶠ i in Filter.atTop,
    Set.Icc (-delta / scale i) 0 ⊆ (X.interval (subseq i)).carrier
  rate : ℕ → ℝ
  rate_pos : ∀ i, 0 < rate i
  rate_tendsto : Filter.Tendsto rate Filter.atTop (nhds 0)
  annular_convergence : ∀ K : Set flow.M, IsCompact K → ∀ m : ℕ,
    ∀ᶠ i in Filter.atTop, Nonempty (MetricComparisonOn (fun s => flow.S.base.metric s)
      (rescaledMetric (X.term (subseq i)).S 0 (scale i) (scale_pos i))
      (map i) K (Set.Icc (-delta) 0) m (rate i))

structure LimitConeData {eps kappa sigma : ℝ} {Phi : ℝ → ℝ}
    {X : NormalizedSequence.{u} eps kappa sigma Phi} (L : RescaledLimitFlow X) where
  patch : Set L.flow.M
  open_patch : IsOpen patch
  compact_patch : IsCompact (closure patch)
  connected_patch : IsConnected patch
  base_mem : L.flow.basepoint ∈ patch
  cone : ConeChart (L.flow.S.base.metric 0) patch
  nonflat : ∃ x ∈ patch, metricScalarAt (L.flow.S.base.metric 0) x ≠ 0
  nonnegative : ∀ s ∈ Set.Icc (-L.delta) 0, SecLower (L.flow.S.base.metric s) 0 patch
  contains_patch : ∀ i, patch ⊆ (L.map i).source

namespace RescaledLimitFlow

variable {eps kappa sigma : ℝ} {Phi : ℝ → ℝ}
  {X : NormalizedSequence.{u} eps kappa sigma Phi}

noncomputable def toConeBlowupLimit (L : RescaledLimitFlow X) (D : LimitConeData L) :
    ConeBlowupLimit X where
  delta := L.delta
  delta_pos := L.delta_pos
  flow := L.flow
  limit_complete := L.limit_complete
  patch := D.patch
  open_patch := D.open_patch
  compact_patch := D.compact_patch
  connected_patch := D.connected_patch
  base_mem := D.base_mem
  cone := D.cone
  nonflat := D.nonflat
  nonnegative := D.nonnegative
  normalized := L.normalized
  subseq := L.subseq
  strictMono := L.strictMono
  scale := L.scale
  scale_pos := L.scale_pos
  scale_tendsto := L.scale_tendsto
  map := L.map
  contains_patch := D.contains_patch
  window := L.window
  rate := L.rate
  rate_pos := L.rate_pos
  rate_tendsto := L.rate_tendsto
  annular_convergence := fun K hK _ m => L.annular_convergence K hK m

theorem false (L : RescaledLimitFlow X) (D : LimitConeData L) : False :=
  (L.toConeBlowupLimit D).false

end RescaledLimitFlow

def ParabolicConeUpgradeRealization.{v} (kappa sigma : ℝ) (Phi : ℝ → ℝ) : Prop :=
  ∃ epsStar : ℝ, 0 < epsStar ∧ ∀ eps : ℝ, 0 < eps → eps ≤ epsStar →
    ∀ X : NormalizedSequence.{v} eps kappa sigma Phi, SubsequenceCurvatureEscape X →
      ∃ L : RescaledLimitFlow X, Nonempty (LimitConeData L)

theorem coneBlowupLimitRealization_of_parabolicConeUpgradeRealization
    {kappa sigma : ℝ} {Phi : ℝ → ℝ}
    (h : ParabolicConeUpgradeRealization.{u} kappa sigma Phi) :
    ConeBlowupLimitRealization.{u} kappa sigma Phi := by
  obtain ⟨e, he, hb⟩ := h
  refine ⟨e, he, fun eps hp hle X hsub => ?_⟩
  obtain ⟨L, ⟨D⟩⟩ := hb eps hp hle X hsub
  exact ⟨L.toConeBlowupLimit D⟩

theorem noSubsequenceCurvatureEscapeShell_of_parabolicConeUpgradeRealization
    {kappa sigma : ℝ} {Phi : ℝ → ℝ}
    (h : ParabolicConeUpgradeRealization.{u} kappa sigma Phi) :
    NoSubsequenceCurvatureEscapeShell.{u} kappa sigma Phi := by
  obtain ⟨e, he, hb⟩ := h
  exact ⟨e, he, fun eps hp hle X hsub => by
    obtain ⟨L, ⟨D⟩⟩ := hb eps hp hle X hsub
    exact L.false D⟩

theorem coneLimitEscapeShell_of_parabolicConeUpgradeRealization
    {kappa sigma : ℝ} {Phi : ℝ → ℝ}
    (h : ParabolicConeUpgradeRealization.{u} kappa sigma Phi) :
    ConeLimitEscapeShell.{u} kappa sigma Phi :=
  coneLimitEscapeShell_of_coneBlowupLimitRealization
    (coneBlowupLimitRealization_of_parabolicConeUpgradeRealization h)

theorem parabolicConeUpgradeRealization_iff_noSubsequenceCurvatureEscapeShell
    {kappa sigma : ℝ} {Phi : ℝ → ℝ} :
    ParabolicConeUpgradeRealization.{u} kappa sigma Phi ↔
      NoSubsequenceCurvatureEscapeShell.{u} kappa sigma Phi := by
  constructor
  · exact noSubsequenceCurvatureEscapeShell_of_parabolicConeUpgradeRealization
  · rintro ⟨e, he, hno⟩
    exact ⟨e, he, fun eps hp hle X hsub => (hno eps hp hle X hsub).elim⟩

theorem not_nonempty_limitConeData {eps kappa sigma : ℝ} {Phi : ℝ → ℝ}
    {X : NormalizedSequence.{u} eps kappa sigma Phi} (L : RescaledLimitFlow X) :
    ¬ Nonempty (LimitConeData L) :=
  fun h => h.elim fun D => L.false D

theorem secLower_zero_euclideanMetric (U : Set ThreeSpace) :
    SecLower (euclideanMetric (E := ThreeSpace)) 0 U := by
  intro x _ v w
  rw [DifferentialGeometry.Geometry.euclideanMetric_metricRm04At_eq_zero x]
  simp

theorem secLower_zero_scaleMetric_euclideanMetric (c : ℝ) (hc : 0 < c)
    (U : Set ThreeSpace) :
    SecLower
      (DifferentialGeometry.scaleMetric (I := I3) c hc (euclideanMetric (E := ThreeSpace)))
      0 U :=
  (secLower_scaleMetric_zero (euclideanMetric (E := ThreeSpace)) c hc U).mpr
    (secLower_zero_euclideanMetric U)

theorem parabolicRmBallBound_of_flat_slice {D : RealTimeInterval}
    (F : PointedFlowData.{u, 0, 0} I3 D) (s scale ρ : ℝ)
    (hflat : ∀ y : F.M, metricRm04At (I := I3) (F.S.base.metric s) y = 0) :
    ParabolicRmBallBound F s scale ρ 0 := by
  intro y _
  rw [curvDerivNormSq]
  have hzero : curvCovDeriv (I := I3) (M := F.M) (F.S.base.metric s) 0 =
      metricRm04 (I := I3) (M := F.M) (F.S.base.metric s) := rfl
  rw [hzero, metricRm04_apply, hflat y]
  simpa using ((Tensor0SBundle.normSq0S_eq_zero_iff (I := I3)
    (F.S.base.metric s) y 4 0).mpr rfl).le

end DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn
