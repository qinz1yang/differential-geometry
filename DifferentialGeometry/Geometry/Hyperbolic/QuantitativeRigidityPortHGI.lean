import DifferentialGeometry.Geometry.Hyperbolic.RigidityProofHGI
import DifferentialGeometry.Geometry.Hyperbolic.Rigidity
import DifferentialGeometry.Geometry.Metric.Approximation.Isometry
import DifferentialGeometry.Geometry.Metric.Approximation.TargetDiffeomorph

set_option autoImplicit false
noncomputable section
open scoped Manifold ContDiff ENNReal
open Set

namespace DifferentialGeometry.Geometry.Hyperbolic

universe u v
variable {M : Type u}
  [TopologicalSpace M] [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
  [IsManifold (𝓡 3) ∞ M] [T2Space M] [SigmaCompactSpace M] [ConnectedSpace M]

private theorem comparison_transport
    {N : Type v}
    [TopologicalSpace N] [ChartedSpace (EuclideanSpace ℝ (Fin 3)) N]
    [IsManifold (𝓡 3) ∞ N] [T2Space N] [SigmaCompactSpace N] [ConnectedSpace N]
    (g : SmoothRiemannianMetric (𝓡 3) M) (h : SmoothRiemannianMetric (𝓡 3) N)
    (f : M ≃ₘ⟮𝓡 3, 𝓡 3⟯ N)
    (hf : Diffeomorph.pullbackMetric h f = g)
    (o : M) (n : ℕ) (η : ℝ)
    (hself :
      letI : TopologicalSpace.MetrizableSpace M := Manifold.metrizableSpace (𝓡 3) M
      letI : PseudoMetricSpace M := g.toPseudoMetricSpace
      letI : MetricSpace M := MetricSpace.ofT0PseudoMetricSpace M
      ∀ Ψ : PartialDiffeomorph (𝓡 3) (𝓡 3) M M ∞,
        PartialDiffeomorph.isMetricApproximationOn Ψ
          (riemannianClosedBallOf g o (n + 1 : ℝ)) (n + 1) (1 / (n + 1 : ℝ)) g g →
        ∃ e : M ≃ᵢ M,
          sSup ((fun p => dist (e p) (Ψ p)) '' Metric.closedBall o η⁻¹) < η)
    (Φ : PartialDiffeomorph (𝓡 3) (𝓡 3) M N ∞)
    (hΦ : PartialDiffeomorph.isMetricApproximationOn Φ
      (riemannianClosedBallOf g o (n + 1 : ℝ)) (n + 1) (1 / (n + 1 : ℝ)) g h) :
    letI : TopologicalSpace.MetrizableSpace M := Manifold.metrizableSpace (𝓡 3) M
    letI : PseudoMetricSpace M := g.toPseudoMetricSpace
    letI : MetricSpace M := MetricSpace.ofT0PseudoMetricSpace M
    letI : TopologicalSpace.MetrizableSpace N := Manifold.metrizableSpace (𝓡 3) N
    letI : PseudoMetricSpace N := h.toPseudoMetricSpace
    letI : MetricSpace N := MetricSpace.ofT0PseudoMetricSpace N
    ∃ e : M ≃ᵢ N,
      sSup ((fun p => dist (e p) (Φ p)) '' Metric.closedBall o η⁻¹) < η := by
  let _ : TopologicalSpace.MetrizableSpace M := Manifold.metrizableSpace (𝓡 3) M
  let _ : PseudoMetricSpace M := g.toPseudoMetricSpace
  let _ : MetricSpace M := MetricSpace.ofT0PseudoMetricSpace M
  let _ : TopologicalSpace.MetrizableSpace N := Manifold.metrizableSpace (𝓡 3) N
  let _ : PseudoMetricSpace N := h.toPseudoMetricSpace
  let _ : MetricSpace N := MetricSpace.ofT0PseudoMetricSpace N
  have hinv : Diffeomorph.pullbackMetric g f.symm = h := by
    rw [← hf, Diffeomorph.pullbackMetric_trans, Diffeomorph.symm_trans_self,
      Diffeomorph.pullbackMetric_refl]
  have hΨ : PartialDiffeomorph.isMetricApproximationOn
      (PartialDiffeomorph.transDiffeomorph Φ f.symm)
      (riemannianClosedBallOf g o (n + 1 : ℝ)) (n + 1) (1 / (n + 1 : ℝ)) g g := by
    rw [PartialDiffeomorph.isMetricApproximationOn_transDiffeomorph_iff, hinv]
    exact hΦ
  obtain ⟨e, he⟩ := hself _ hΨ
  let a : M ≃ᵢ N := {
    f.toEquiv with
    isometry_toFun := fun x y => by
      change riemannianEDistOf h (f x) (f y) = riemannianEDistOf g x y
      rw [← Metric.edistOf_pullbackMetricCross h f,
        Diffeomorph.pullbackMetricCross_eq_pullbackMetric, hf] }
  refine ⟨e.trans a, ?_⟩
  have hd (p : M) : dist ((e.trans a) p) (Φ p) =
      dist (e p) ((PartialDiffeomorph.transDiffeomorph Φ f.symm) p) := by
    change dist (a (e p)) (Φ p) = dist (e p) (f.symm (Φ p))
    rw [← a.dist_eq (e p) (f.symm (Φ p))]
    congr 1
    exact (f.apply_symm_apply (Φ p)).symm
  simpa only [hd] using he


theorem exists_isometry_close_of_homotopyEquiv
    (g : SmoothRiemannianMetric (𝓡 3) M) (K : ℝ) (hK : K < 0)
    (hgcurvature : hasConstantSectionalCurvature g K)
    (hgcomplete : RiemannianMetricComplete g)
    (hgvolume : Integral.Measure.riemannianVolumeMeasure (𝓡 3) M g univ < ⊤)
    (o : M) {η : ℝ} (hη : 0 < η) :
    letI : TopologicalSpace.MetrizableSpace M := Manifold.metrizableSpace (𝓡 3) M
    letI : PseudoMetricSpace M := g.toPseudoMetricSpace
    letI : MetricSpace M := MetricSpace.ofT0PseudoMetricSpace M
    ∃ δ : ℝ, 0 < δ ∧ δ < η ∧
      ∀ (N : Type v) [TopologicalSpace N]
        [ChartedSpace (EuclideanSpace ℝ (Fin 3)) N]
        [IsManifold (𝓡 3) ∞ N] [T2Space N] [SigmaCompactSpace N] [ConnectedSpace N]
        (h : SmoothRiemannianMetric (𝓡 3) N),
      hasConstantSectionalCurvature h K → RiemannianMetricComplete h →
      Integral.Measure.riemannianVolumeMeasure (𝓡 3) N h univ < ⊤ →
      ContinuousMap.HomotopyEquiv M N →
      letI : TopologicalSpace.MetrizableSpace N := Manifold.metrizableSpace (𝓡 3) N
      letI : PseudoMetricSpace N := h.toPseudoMetricSpace
      letI : MetricSpace N := MetricSpace.ofT0PseudoMetricSpace N
      ∀ (ε : ℝ), 0 < ε → ε ≤ δ →
      ∀ (Φ : PartialDiffeomorph (𝓡 3) (𝓡 3) M N ∞) (k : ℕ),
        ⌈ε⁻¹⌉₊ ≤ k →
        PartialDiffeomorph.isMetricApproximationOn Φ (Metric.ball o ε⁻¹) k ε g h →
        ∃ e : M ≃ᵢ N,
          sSup ((fun p => dist (e p) (Φ p)) '' Metric.ball o η⁻¹) < η := by
  let _ : TopologicalSpace.MetrizableSpace M := Manifold.metrizableSpace (𝓡 3) M
  let _ : PseudoMetricSpace M := g.toPseudoMetricSpace
  let _ : MetricSpace M := MetricSpace.ofT0PseudoMetricSpace M
  obtain ⟨n, hn, hR, hself⟩ :=
    PartialDiffeomorph.exists_isometry_close_of_metric_approximation
      g hgcomplete hgvolume o hη
  let δ : ℝ := 1 / (n + 2 : ℝ)
  have hnpos : (0 : ℝ) < n + 1 := by positivity
  have hδpos : 0 < δ := by dsimp [δ]; positivity
  have hδinv : δ⁻¹ = n + 2 := by simp [δ]
  have hδη : δ < η := by
    apply (inv_lt_inv₀ hη hδpos).mp
    rw [hδinv]
    linarith
  refine ⟨δ, hδpos, hδη, ?_⟩
  intro N _ _ _ _ _ _ h hhcurvature hhcomplete hhvolume u
  let _ : TopologicalSpace.MetrizableSpace N := Manifold.metrizableSpace (𝓡 3) N
  let _ : PseudoMetricSpace N := h.toPseudoMetricSpace
  let _ : MetricSpace N := MetricSpace.ofT0PseudoMetricSpace N
  intro ε hεpos hεδ Φ k hk hΦ
  have hinv : δ⁻¹ ≤ ε⁻¹ := (inv_le_inv₀ hδpos hεpos).mpr hεδ
  have hclosed (r : ℝ) (hr : 0 ≤ r) :
      riemannianClosedBallOf g o r = Metric.closedBall o r := by
    ext p
    change edist o p ≤ ENNReal.ofReal r ↔ dist p o ≤ r
    rw [edist_dist, dist_comm, ENNReal.ofReal_le_ofReal_iff hr]
  have hsub : riemannianClosedBallOf g o (n + 1 : ℝ) ⊆ Metric.ball o ε⁻¹ := by
    rw [hclosed _ hnpos.le]
    intro p hp
    apply lt_of_lt_of_le _ hinv
    rw [hδinv]
    exact lt_of_le_of_lt hp (by linarith)
  have horder : n + 1 ≤ k := by
    apply le_trans _ hk
    apply le_trans _ (Nat.ceil_mono hinv)
    rw [hδinv]
    have hc : (n : ℝ) + 2 = ((n + 2 : ℕ) : ℝ) := by norm_cast
    rw [hc, Nat.ceil_natCast]
    omega
  have hε : ε ≤ 1 / (n + 1 : ℝ) := by
    apply hεδ.trans
    exact one_div_le_one_div_of_le hnpos (by linarith)
  have happ := hΦ.mono hsub horder hε
  obtain ⟨f, hf, _⟩ := mostow_prasad_HGI g h K hK hgcurvature hhcurvature
    hgcomplete hhcomplete hgvolume hhvolume u
  have hfmetric : Diffeomorph.pullbackMetric h f = g := by
    apply SmoothRiemannianMetric.ext_inner
    intro p v w
    rw [Diffeomorph.pullbackMetric_inner]
    exact hf.1 p v w
  obtain ⟨e, he⟩ := comparison_transport g h f hfmetric o n η hself Φ happ
  have hcompact : IsCompact (Metric.closedBall o η⁻¹) := by
    rw [← hclosed _ (inv_pos.mpr hη).le]
    exact hgcomplete.closedEBall_isCompact o η⁻¹
  have hdomain : Metric.closedBall o η⁻¹ ⊆ Φ.source := by
    apply Subset.trans _ hΦ.1
    intro p hp
    exact lt_of_le_of_lt hp ((hR.trans (by rw [hδinv]; linarith)).trans_le hinv)
  have hcont : ContinuousOn (fun p => dist (e p) (Φ p)) (Metric.closedBall o η⁻¹) :=
    fun p hp => (e.continuous.continuousAt.continuousWithinAt).dist
      (Φ.contMDiffOn_toFun.continuousOn.mono hdomain p hp)
  refine ⟨e, lt_of_le_of_lt ?_ he⟩
  apply csSup_le_csSup (hcompact.bddAbove_image hcont)
  · exact (Metric.nonempty_ball.mpr (inv_pos.mpr hη)).image _
  · exact image_mono Metric.ball_subset_closedBall

end DifferentialGeometry.Geometry.Hyperbolic
