import DifferentialGeometry.Geometry.Hyperbolic.MostowRigidity
import DifferentialGeometry.Geometry.Hyperbolic.Isometry
import DifferentialGeometry.Geometry.Metric.Approximation.Isometry
import DifferentialGeometry.Geometry.Metric.Approximation.TargetDiffeomorph

open scoped Manifold ContDiff ENNReal

namespace DifferentialGeometry.Geometry.Hyperbolic

universe u v

local notation "E3" => EuclideanSpace ℝ (Fin 3)

variable {M : Type u} [TopologicalSpace M] [ChartedSpace E3 M]
  [IsManifold (𝓡 3) ∞ M] [T2Space M] [SigmaCompactSpace M] [ConnectedSpace M]

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
theorem exists_isometry_close_of_homeomorph_of_metric_approximation
    (g : SmoothRiemannianMetric (𝓡 3) M) (hg : RiemannianMetricComplete g)
    (hvolg : Integral.Measure.riemannianVolumeMeasure (𝓡 3) M g Set.univ < ⊤)
    (κ : ℝ) (hκ : κ < 0)
    (hsecg : ∀ (x : M) (v w : TangentSpace (𝓡 3) x),
      Curvature.metricRm04StandardAt g x v w w v =
        κ * (g.inner x v v * g.inner x w w - g.inner x v w * g.inner x v w))
    (o : M) {ζ : ℝ} (hζ : 0 < ζ) :
    letI : TopologicalSpace.MetrizableSpace M := Manifold.metrizableSpace (𝓡 3) M
    letI : PseudoMetricSpace M := g.toPseudoMetricSpace
    letI : MetricSpace M := MetricSpace.ofT0PseudoMetricSpace M
    ∃ s : ℕ, 1 ≤ s ∧ ζ⁻¹ < (s : ℝ) + 1 ∧
      ∀ (N : Type v) [TopologicalSpace N] [ChartedSpace E3 N]
        [IsManifold (𝓡 3) ∞ N] [T2Space N] [SigmaCompactSpace N] [ConnectedSpace N]
        (h : SmoothRiemannianMetric (𝓡 3) N),
        RiemannianMetricComplete h →
        Integral.Measure.riemannianVolumeMeasure (𝓡 3) N h Set.univ < ⊤ →
        (∀ (y : N) (v w : TangentSpace (𝓡 3) y),
          Curvature.metricRm04StandardAt h y v w w v =
            κ * (h.inner y v v * h.inner y w w - h.inner y v w * h.inner y v w)) →
        (M ≃ₜ N) → ∀ Φ : PartialDiffeomorph (𝓡 3) (𝓡 3) M N ∞,
          PartialDiffeomorph.isMetricApproximationOn Φ
            (riemannianClosedBallOf g o (s + 1 : ℝ)) (s + 1) (1 / (s + 1 : ℝ)) g h →
          letI : TopologicalSpace.MetrizableSpace N := Manifold.metrizableSpace (𝓡 3) N
          letI : PseudoMetricSpace N := h.toPseudoMetricSpace
          letI : MetricSpace N := MetricSpace.ofT0PseudoMetricSpace N
          ∃ e : M ≃ᵢ N,
            sSup ((fun p => dist (e p) (Φ p)) '' Metric.closedBall o ζ⁻¹) < ζ := by
  let _ : NeZero (Module.finrank ℝ E3) := ⟨by simp⟩
  let _ : TopologicalSpace.MetrizableSpace M := Manifold.metrizableSpace (𝓡 3) M
  let _ : PseudoMetricSpace M := g.toPseudoMetricSpace
  let _ : MetricSpace M := MetricSpace.ofT0PseudoMetricSpace M
  obtain ⟨s, hs, hsr, hself⟩ :=
    PartialDiffeomorph.exists_isometry_close_of_metric_approximation g hg hvolg o hζ
  refine ⟨s, hs, hsr, ?_⟩
  intro N _ _ _ _ _ _ h hh hvolh hsech u Φ hΦ
  let _ : TopologicalSpace.MetrizableSpace N := Manifold.metrizableSpace (𝓡 3) N
  let _ : PseudoMetricSpace N := h.toPseudoMetricSpace
  let _ : MetricSpace N := MetricSpace.ofT0PseudoMetricSpace N
  obtain ⟨a, _, _⟩ := mostow_prasad_rigidity g h κ u.toHomotopyEquiv
    hκ hg hh hvolg hvolh hsecg hsech
  let d : N ≃ₘ⟮𝓡 3, 𝓡 3⟯ M :=
    { toEquiv := a.symm.toEquiv
      contMDiff_toFun := contMDiff_isometryEquiv h g κ hκ hh hg hsech hsecg a.symm
      contMDiff_invFun := contMDiff_isometryEquiv g h κ hκ hg hh hsecg hsech a }
  have hpull : Diffeomorph.pullbackMetric g d = h := by
    apply SmoothRiemannianMetric.ext_inner
    intro y v w
    rw [Diffeomorph.pullbackMetric_inner]
    have hi := Riemannian.inner_mfderiv_eq_mul_of_eventually_riemannian_distance_eq
      h g d y 1 (d.contMDiff.contMDiffAt.mdifferentiableAt (by decide))
      (Filter.Eventually.of_forall fun z => by
        have hd : riemannianEDistOf g (d z) (d y) = riemannianEDistOf h z y :=
          a.symm.edist_eq z y
        rw [hd, one_mul]) v w
    simpa only [one_pow, one_mul] using hi
  let Ψ : PartialDiffeomorph (𝓡 3) (𝓡 3) M M ∞ :=
    PartialDiffeomorph.transDiffeomorph Φ d
  have hΨ : PartialDiffeomorph.isMetricApproximationOn Ψ
      (riemannianClosedBallOf g o (s + 1 : ℝ)) (s + 1) (1 / (s + 1 : ℝ)) g g := by
    change PartialDiffeomorph.isMetricApproximationOn
      (PartialDiffeomorph.transDiffeomorph Φ d) _ _ _ _ _
    rw [PartialDiffeomorph.isMetricApproximationOn_transDiffeomorph_iff, hpull]
    exact hΦ
  obtain ⟨b, hb⟩ := hself Ψ hΨ
  refine ⟨b.trans a, ?_⟩
  have heq (p : M) : dist ((b.trans a) p) (Φ p) = dist (b p) (Ψ p) := by
    change dist (a (b p)) (Φ p) = dist (b p) (a.symm (Φ p))
    calc
      dist (a (b p)) (Φ p) = dist (a (b p)) (a (a.symm (Φ p))) := by
        rw [a.apply_symm_apply]
      _ = dist (b p) (a.symm (Φ p)) := a.dist_eq _ _
  simpa only [heq] using hb

end DifferentialGeometry.Geometry.Hyperbolic
