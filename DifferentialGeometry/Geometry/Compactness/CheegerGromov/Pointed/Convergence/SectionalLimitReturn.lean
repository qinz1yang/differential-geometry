import DifferentialGeometry.Geometry.Compactness.CheegerGromov.Pointed.Convergence.CompactWholeGauge
import DifferentialGeometry.Geometry.Metric.Convergence.Curvature.SectionalLimit
import DifferentialGeometry.Geometry.Curvature.Naturality.Pullback.Sectional

set_option autoImplicit false

noncomputable section

namespace DifferentialGeometry.CheegerGromovCompactness

open Set Filter
open DifferentialGeometry.Geometry.Riemannian
open scoped Manifold ContDiff _root_.Topology ENNReal

universe u uE uH uF uG

variable {E : Type uE} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)] [CompleteSpace E]
  {H : Type uH} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {M : Type u} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [T2Space M] [SigmaCompactSpace M] [ConnectedSpace M]

theorem exists_sectional_nonneg_of_bounded_geometry_limit
    (p : M) (gSeq : ℕ → SmoothRiemannianMetric I M)
    (hcomplete : SeqMetricComplete (I := I) (pointedMetricSeq p gSeq))
    (hgeom : SeqBoundedGeometry (I := I) (pointedMetricSeq p gSeq))
    (hinj : BaseInjBound (I := I) (pointedMetricSeq p gSeq))
    (D : ℝ)
    (hdiam : ∀ n (x y : M), riemannianEDistOf (I := I) (gSeq n) x y ≤ ENNReal.ofReal D)
    (ε : ℕ → ℝ) (hεlim : Tendsto ε atTop (𝓝 0))
    (hsec : ∀ n, SectionalBoundedBelow (gSeq n) (-ε n)) :
    ∃ h : SmoothRiemannianMetric I M, SectionalBoundedBelow h 0 := by
  obtain ⟨L, f, hf, hgauge⟩ :=
    exists_compact_whole_pullback_gauge p gSeq hcomplete hgeom hinj D hdiam
  let : TopologicalSpace L.M := L.topology
  let : ChartedSpace H L.M := L.charted
  let : IsManifold I ∞ L.M := L.smooth
  let : SigmaCompactSpace L.M := L.sigmaCompact
  let : T2Space L.M := L.t2
  obtain ⟨hcpt, -, e, hconv⟩ := hgauge
  have hL : SectionalBoundedBelow L.metric 0 :=
    sectional_nonneg_of_metricCInfConvergenceOnCompacts L.metric
      (fun n => Diffeomorph.pullbackMetricCross (gSeq (f n)) (e n)) (fun n => ε (f n))
      (hεlim.comp hf.tendsto_atTop) hconv
      (fun n => sectionalBoundedBelow_pullbackMetricCross (gSeq (f n)) (e n) (hsec (f n)))
  exact exists_sectionalBoundedBelow_of_diffeomorph (e 0).symm L.metric hL

theorem exists_sectional_nonneg_of_bounded_geometry_limit_of_exp_error
    (p : M) (gSeq : ℕ → SmoothRiemannianMetric I M)
    (hcomplete : SeqMetricComplete (I := I) (pointedMetricSeq p gSeq))
    (hgeom : SeqBoundedGeometry (I := I) (pointedMetricSeq p gSeq))
    (hinj : BaseInjBound (I := I) (pointedMetricSeq p gSeq))
    (D : ℝ)
    (hdiam : ∀ n (x y : M), riemannianEDistOf (I := I) (gSeq n) x y ≤ ENNReal.ofReal D)
    (ε : ℕ → ℝ) (hεlim : Tendsto ε atTop (𝓝 0)) (C B t : ℝ)
    (hsec : ∀ n, SectionalBoundedBelow (gSeq n) (-ε n * Real.exp (C * B * t))) :
    ∃ h : SmoothRiemannianMetric I M, SectionalBoundedBelow h 0 := by
  have hlim : Tendsto (fun n => ε n * Real.exp (C * B * t)) atTop (𝓝 0) := by
    simpa using hεlim.mul_const (Real.exp (C * B * t))
  refine exists_sectional_nonneg_of_bounded_geometry_limit p gSeq hcomplete hgeom hinj D hdiam
    (fun n => ε n * Real.exp (C * B * t)) hlim (fun n => ?_)
  simpa only [neg_mul] using hsec n

theorem exists_sectional_nonneg_of_bounded_geometry_limit_of_diffeomorph
    {F : Type uF} [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
    {G : Type uG} [TopologicalSpace G] {J : ModelWithCorners ℝ F G}
    {W : Type*} [TopologicalSpace W] [ChartedSpace G W] [IsManifold J ∞ W] [T2Space W]
    (Ψ : W ≃ₘ⟮J, I⟯ M)
    (p : M) (gSeq : ℕ → SmoothRiemannianMetric I M)
    (hcomplete : SeqMetricComplete (I := I) (pointedMetricSeq p gSeq))
    (hgeom : SeqBoundedGeometry (I := I) (pointedMetricSeq p gSeq))
    (hinj : BaseInjBound (I := I) (pointedMetricSeq p gSeq))
    (D : ℝ)
    (hdiam : ∀ n (x y : M), riemannianEDistOf (I := I) (gSeq n) x y ≤ ENNReal.ofReal D)
    (ε : ℕ → ℝ) (hεlim : Tendsto ε atTop (𝓝 0))
    (hsec : ∀ n, SectionalBoundedBelow (gSeq n) (-ε n)) :
    ∃ h : SmoothRiemannianMetric J W, SectionalBoundedBelow h 0 := by
  obtain ⟨hM, hhM⟩ := exists_sectional_nonneg_of_bounded_geometry_limit p gSeq hcomplete hgeom
    hinj D hdiam ε hεlim hsec
  exact exists_sectionalBoundedBelow_of_diffeomorph Ψ hM hhM

end DifferentialGeometry.CheegerGromovCompactness

end
