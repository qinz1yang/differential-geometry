import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.AncientPointedFlowLimitTransfer
import DifferentialGeometry.Geometry.Metric.Pullback.LocalDistance
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.CrossModelBallCapture

set_option autoImplicit false

noncomputable section
open Set Function
open DifferentialGeometry.Geometry.Curvature
open scoped Manifold ContDiff
open DifferentialGeometry.PDE.RicciFlow.Surgery.Topology (ThreeSpace)

namespace DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn

universe v

theorem exists_neckAlternatives_localPull_of_metric_lower :
    ∃ D : ℝ, 0 < D ∧ ∀ {M N : Type v} [TopologicalSpace M] [ChartedSpace ThreeSpace M]
      [IsManifold I3 ∞ M] [T2Space M] [TopologicalSpace N]
      [ChartedSpace ThreeSpace N] [IsManifold I3 ∞ N] [T2Space N]
      (g : SmoothRiemannianMetric I3 M) (h0 : SmoothRiemannianMetric I3 N) {f : N → M}
      (hf : IsLocalDiffeomorph I3 I3 ∞ f), Injective f → ∀ (z : N) {r L eps C : ℝ},
      0 < r → 0 < L → 1 ≤ C → IsCompact (riemannianClosedBallOf h0 z r) →
      (∀ y ∈ riemannianClosedBallOf h0 z r, ∀ u : TangentSpace I3 y,
        h0.inner y u u ≤ L ^ 2 * (localPullMetric g f hf).inner y u u) →
      0 < metricScalarAt g (f z) →
      L * (C + (D + 2 * eps⁻¹) * Real.sqrt C) < r * Real.sqrt (metricScalarAt g (f z)) →
      (Nonempty (SpatialNeck g eps (f z)) ∨
        (∃ w : M, Nonempty (SpatialNeck g eps w) ∧
          metricScalarAt g (f z) ≤ C * metricScalarAt g w ∧
          metricScalarAt g w ≤ C * metricScalarAt g (f z) ∧
          riemannianEDistOf g (f z) w < ENNReal.ofReal (C / Real.sqrt (metricScalarAt g (f z)))) ∨
        ∀ y ∈ connectedComponent (f z), metricScalarAt g y ≤ C * metricScalarAt g (f z)) →
      Nonempty (SpatialNeck (localPullMetric g f hf) eps z) ∨
        (∃ w : N, Nonempty (SpatialNeck (localPullMetric g f hf) eps w) ∧
          metricScalarAt (localPullMetric g f hf) z ≤
            C * metricScalarAt (localPullMetric g f hf) w ∧
          metricScalarAt (localPullMetric g f hf) w ≤
            C * metricScalarAt (localPullMetric g f hf) z ∧
          riemannianEDistOf (localPullMetric g f hf) z w <
            ENNReal.ofReal (C / Real.sqrt (metricScalarAt (localPullMetric g f hf) z))) ∨
        ∀ y ∈ connectedComponent z, metricScalarAt (localPullMetric g f hf) y ≤
          C * metricScalarAt (localPullMetric g f hf) z := by
  obtain ⟨D, hD, hwin⟩ := exists_spatialNeck_window_edist_le.{v}
  refine ⟨D, hD, ?_⟩
  intro M N _ _ _ _ _ _ _ _ g h0 f hf hinj z r L eps C hr hL hC hcpt hlower hQ hsmall halt
  set gp := localPullMetric g f hf with hgp
  set Q := metricScalarAt g (f z) with hQdef
  obtain ⟨Φ, hs, ht, hΦ⟩ := IsLocalDiffeomorphOn.exists_partialDiffeomorph_of_injOn
    (hf.isLocalDiffeomorphOn univ) isOpen_univ ⟨z, trivial⟩ hinj.injOn
  have hΦf : (Φ : N → M) = f := hΦ
  have hsrc : Φ.source = univ := hs
  have htgt : Φ.target = range f := by rw [← image_univ]; exact ht
  have hiso : ∀ y ∈ Φ.source, ∀ v w : TangentSpace I3 y,
      g.inner (Φ y) (mfderiv I3 I3 Φ y v) (mfderiv I3 I3 Φ y w) = gp.inner y v w := by
    intro y _ v w
    rw [hgp, localPullMetric_inner, hΦf]
  have hisoS := isometryOn_symm_of_isometryOn Φ hiso
  have hleft : ∀ y : N, (Φ.symm : M → N) (f y) = y := fun y => by
    rw [← hΦf]
    exact Φ.left_inv' (by rw [hsrc]; exact mem_univ y)
  have hsc : ∀ y : N, metricScalarAt gp y = metricScalarAt g (f y) := fun y =>
    metricScalarAt_localPull g f hf y
  have hcap : riemannianBallOf g (f z) (r / L) ⊆ range f := by
    have h1 := ball_subset_image_of_metric_lower_crossModel h0 g Φ z hr hL hcpt
      (by rw [hsrc]; exact subset_univ _) (fun y hy u => by
        rw [hΦf]
        have h2 := hlower y hy u
        rwa [localPullMetric_inner] at h2)
    rw [hΦf] at h1
    exact h1.trans (image_subset_range _ _)
  have hpull : ∀ {p : M} (nk : SpatialNeck g eps p),
      (∀ y ∈ univ ×ˢ Ioo (-eps⁻¹) eps⁻¹, nk.map y ∈ range f) →
        Nonempty (SpatialNeck gp eps ((Φ.symm : M → N) p)) := fun nk hw =>
    ⟨nk.pushforward Φ.symm hisoS (fun y hy => by
      change _ ∈ Φ.target
      rw [htgt]
      exact hw y hy)⟩
  have hsQ : 0 < Real.sqrt Q := Real.sqrt_pos.mpr hQ
  have hsC : 1 ≤ Real.sqrt C := Real.one_le_sqrt.mpr hC
  have hρ : (C + (D + 2 * eps⁻¹) * Real.sqrt C) / Real.sqrt Q < r / L := by
    rw [div_lt_div_iff₀ hsQ hL]
    linarith
  have hrL : 0 < r / L := div_pos hr hL
  rcases halt with hnk | ⟨w, ⟨nk⟩, hQw, hwQ, hd⟩ | hall
  · obtain ⟨nk⟩ := hnk
    have he : 0 < eps := nk.eps_pos
    have hA : 0 < D + 2 * eps⁻¹ := by positivity
    have hin : ∀ y ∈ univ ×ˢ Ioo (-eps⁻¹) eps⁻¹, nk.map y ∈ range f := by
      intro y hy
      apply hcap
      refine lt_of_le_of_lt (hwin g nk y hy) ((ENNReal.ofReal_lt_ofReal_iff hrL).mpr ?_)
      refine lt_of_le_of_lt (div_le_div_of_nonneg_right ?_ hsQ.le) hρ
      nlinarith
    have hn := hpull nk hin
    rw [hleft z] at hn
    exact Or.inl hn
  · have he : 0 < eps := nk.eps_pos
    have hA : 0 < D + 2 * eps⁻¹ := by positivity
    have hRw : 0 < metricScalarAt g w := nk.Q_pos
    have hsRw : 0 < Real.sqrt (metricScalarAt g w) := Real.sqrt_pos.mpr hRw
    have hsq : Real.sqrt Q ≤ Real.sqrt C * Real.sqrt (metricScalarAt g w) := by
      rw [← Real.sqrt_mul (by linarith)]
      exact Real.sqrt_le_sqrt hQw
    have hwb : (D + 2 * eps⁻¹) / Real.sqrt (metricScalarAt g w) ≤
        (D + 2 * eps⁻¹) * Real.sqrt C / Real.sqrt Q := by
      rw [div_le_div_iff₀ hsRw hsQ]
      nlinarith
    have hC0 : 0 ≤ C / Real.sqrt Q := div_nonneg (by linarith) hsQ.le
    have hsum : C / Real.sqrt Q + (D + 2 * eps⁻¹) / Real.sqrt (metricScalarAt g w) ≤
        (C + (D + 2 * eps⁻¹) * Real.sqrt C) / Real.sqrt Q := by
      rw [add_div C]
      linarith
    have hin : ∀ y ∈ univ ×ˢ Ioo (-eps⁻¹) eps⁻¹, nk.map y ∈ range f := by
      intro y hy
      apply hcap
      have h1 := hwin g nk y hy
      change riemannianEDistOf g (f z) (nk.map y) < ENNReal.ofReal (r / L)
      calc riemannianEDistOf g (f z) (nk.map y)
          ≤ riemannianEDistOf g (f z) w + riemannianEDistOf g w (nk.map y) :=
            DifferentialGeometry.riemannianEDistOf_triangle _ _ _ _
        _ < ENNReal.ofReal (C / Real.sqrt Q) +
              ENNReal.ofReal ((D + 2 * eps⁻¹) / Real.sqrt (metricScalarAt g w)) :=
            ENNReal.add_lt_add_of_lt_of_le (ne_top_of_le_ne_top ENNReal.ofReal_ne_top h1) hd h1
        _ = ENNReal.ofReal (C / Real.sqrt Q +
              (D + 2 * eps⁻¹) / Real.sqrt (metricScalarAt g w)) :=
            (ENNReal.ofReal_add hC0 (div_nonneg hA.le hsRw.le)).symm
        _ < ENNReal.ofReal (r / L) :=
            (ENNReal.ofReal_lt_ofReal_iff hrL).mpr (lt_of_le_of_lt hsum hρ)
    have hwball : riemannianEDistOf g (f z) w < ENNReal.ofReal (r / L) := by
      refine lt_of_lt_of_le hd (ENNReal.ofReal_le_ofReal ?_)
      refine le_trans ?_ hρ.le
      exact div_le_div_of_nonneg_right (by nlinarith) hsQ.le
    obtain ⟨w', hw', hdist⟩ :=
      exists_riemannianEDistOf_localPullMetric_eq_of_ball_subset_range g hf hinj z hcap hwball
    have hn := hpull nk hin
    rw [← hw', hleft w'] at hn
    refine Or.inr (Or.inl ⟨w', hn, ?_, ?_, ?_⟩)
    · rw [hsc, hsc, hw']
      exact hQw
    · rw [hsc, hsc, hw']
      exact hwQ
    · rw [hdist, hsc]
      exact hd
  · refine Or.inr (Or.inr fun y hy => ?_)
    rw [hsc, hsc]
    exact hall (f y) (hf.contMDiff.continuous.image_connectedComponent_subset z ⟨y, hy, rfl⟩)

end DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn

end
