import DifferentialGeometry.Geometry.Comparison.Distance.SegmentSmoothness
import DifferentialGeometry.Geometry.Geodesic.Minimizing.TriangleEquality
import DifferentialGeometry.Geometry.Metric.Distance.LocalCompletion
import DifferentialGeometry.Geometry.Metric.Distance.Finiteness

set_option autoImplicit false
noncomputable section
open Bundle Filter Manifold Set
open scoped Topology Manifold ContDiff ENNReal
namespace DifferentialGeometry.Geometry.Riemannian
open DifferentialGeometry.Geometry.Riemannian.Exponential
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {M : Type*} [MetricSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M] [SigmaCompactSpace M]
attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace

theorem exists_contMDiffAt_dist_of_metric_segment
    (g : SmoothRiemannianMetric I M)
    (hmetric : ∀ x y : M, edist x y = riemannianEDistOf g x y)
    (f : ℝ → M) {R : ℝ} (hR : 0 < R)
    (hdist : ∀ s ∈ Icc 0 R, ∀ v ∈ Icc 0 R, dist (f s) (f v) = |s - v|) :
    ∃ δ : ℝ, 0 < δ ∧ δ < R ∧ ∀ s ∈ Ioo 0 δ,
      ContMDiffAt I 𝓘(ℝ, ℝ) ∞ (fun x => dist x (f s)) (f 0) := by
  classical
  let d : M → M → ℝ := dist
  have hd_nonneg (x y : M) : 0 ≤ d x y := dist_nonneg
  let : PathConnectedSpace M := by
    refine ⟨⟨f 0⟩, fun x y => ?_⟩
    by_contra h
    have hp : IsEmpty (Path x y) := not_nonempty_iff.mp h
    have hinf : riemannianEDistOf g x y = ⊤ := by
      rw [edistOf_iInf]
      exact le_antisymm le_top (le_iInf fun γ => (hp.false γ).elim)
    rw [← hmetric] at hinf
    exact edist_ne_top x y hinf
  obtain ⟨g', r, U, hr, hcomplete, _, _, _, _, hlocal⟩ :=
    exists_riemannianMetricComplete_eqOn_ball g hmetric (f 0)
  let B : Set M := Metric.ball (f 0) r
  have hB : B ∈ 𝓝 (f 0) := Metric.ball_mem_nhds _ hr
  have hball (s : ℝ) (hs : s ∈ Icc 0 R) (hsr : s < r) : f s ∈ B := by
    change dist (f s) (f 0) < r
    rw [hdist s hs 0 ⟨le_rfl, hR.le⟩, sub_zero, abs_of_nonneg hs.1]
    exact hsr
  let : IsManifold I 1 M := IsManifold.of_le (n := (∞ : WithTop ℕ∞)) (by decide)
  let : TopologicalSpace.MetrizableSpace M := Manifold.metrizableSpace I M
  let : T3Space M := inferInstance
  let : RiemannianBundle (fun x : M => TangentSpace I x) := ⟨g'.toRiemannianMetric⟩
  let : IsContinuousRiemannianBundle E (fun x : M => TangentSpace I x) :=
    ⟨⟨g'.inner, g'.contMDiff.continuous, by intro x v w; rfl⟩⟩
  let em : EMetricSpace M := EMetricSpace.ofRiemannianMetric I M
  let : MetricSpace M := @EMetricSpace.toMetricSpace M em
    (fun x y => (Manifold.riemannianEDist_lt_top (I := I) x y).ne)
  let : CompleteSpace M := hcomplete.complete
  let : IsRiemannianManifold I M := ⟨fun x y => rfl⟩
  have hEnorm : IsMetricNorm (I := I) g' :=
    fun x v => tensor0SBundle_enorm_eq_riemannianBundle_enorm g' x v
  have hd (x y : M) (hx : x ∈ B) (hy : y ∈ B) : dist x y = d x y := by
    change (riemannianEDistOf g' x y).toReal = d x y
    rw [hlocal x hx y hy, ENNReal.toReal_ofReal (hd_nonneg x y)]
  let L := min (min R r) (expDiffeoRadius g' hEnorm (f 0)) / 2
  have hL : 0 < L := half_pos (lt_min (lt_min hR hr) (expDiffeoRadius_pos g' hEnorm (f 0)))
  have hLR : L < R := (half_lt_self
    (lt_min (lt_min hR hr) (expDiffeoRadius_pos g' hEnorm (f 0)))).trans_le
      ((min_le_left _ _).trans (min_le_left _ _))
  have hLr : L < r := (half_lt_self
    (lt_min (lt_min hR hr) (expDiffeoRadius_pos g' hEnorm (f 0)))).trans_le
      ((min_le_left _ _).trans (min_le_right _ _))
  have hLe : L < expDiffeoRadius g' hEnorm (f 0) := (half_lt_self
    (lt_min (lt_min hR hr) (expDiffeoRadius_pos g' hEnorm (f 0)))).trans_le (min_le_right _ _)
  have hparam (s : Icc (0 : ℝ) L) : (s : ℝ) ∈ Icc 0 R :=
    ⟨s.property.1, s.property.2.trans hLR.le⟩
  have hfb (s : Icc (0 : ℝ) L) : f s ∈ B :=
    hball s (hparam s) (s.property.2.trans_lt hLr)
  obtain ⟨v, hv, hsegment⟩ := exists_intrinsicGeodesic_eq_short_metric_segment g' hEnorm hL
    (fun s => f s) hLe (by
      intro s t
      rw [← IsRiemannianManifold.out (I := I), edist_dist, hd _ _ (hfb s) (hfb t)]
      rw [show d (f s) (f t) = |(s : ℝ) - t| from hdist s (hparam s) t (hparam t)])
  refine ⟨L / 2, half_pos hL, (half_lt_self hL).trans hLR, ?_⟩
  intro s hs
  have hsp : 0 < s := hs.1
  have hsL : s ≤ L := by linarith [hs.2]
  have h2sL : 2 * s ≤ L := by linarith [hs.2]
  have hsB := hfb ⟨s, hs.1.le, hsL⟩
  have hsEq := hsegment ⟨s, hs.1.le, hsL⟩
  have h2sEq := hsegment ⟨2 * s, by positivity, h2sL⟩
  obtain ⟨V, hV, hpV, hVsm⟩ := exists_open_smooth_dist_of_minimizing_intrinsic_segment
    g' hEnorm (f 0) v hv s hs.1 (by
      rw [← h2sEq, hd _ _ (hfb ⟨0, le_rfl, hL.le⟩) (hfb ⟨2 * s, by positivity, h2sL⟩)]
      change d (f 0) (f (2 * s)) = 2 * s
      rw [show d (f 0) (f (2 * s)) = |0 - 2 * s| from
        hdist 0 ⟨le_rfl, hR.le⟩ (2 * s) ⟨by positivity, h2sL.trans hLR.le⟩]
      simp only [zero_sub, abs_neg, abs_of_pos (by positivity : 0 < 2 * s)])
  have hat := hVsm.contMDiffAt (hV.mem_nhds hpV)
  rw [← hsEq] at hat
  apply hat.congr_of_eventuallyEq
  filter_upwards [hB] with x hx
  exact (hd x (f s) hx hsB).symm

end DifferentialGeometry.Geometry.Riemannian
