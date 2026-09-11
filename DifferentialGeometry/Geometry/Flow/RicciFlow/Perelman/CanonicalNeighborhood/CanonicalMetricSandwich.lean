import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.CompactDomainTransport
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.CollarMetricControl
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.CrossModelBallCapture


set_option autoImplicit false
noncomputable section
open Set Function
open scoped Manifold ContDiff Topology ENNReal

namespace DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn

open DifferentialGeometry.Geometry.Riemannian
open DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

universe u v

variable {M : Type u} {N : Type v} [TopologicalSpace M] [TopologicalSpace N]
  [ChartedSpace ThreeSpace M] [ChartedSpace ThreeSpace N]
  [IsManifold I3 ∞ M] [IsManifold I3 ∞ N] [T2Space M] [T2Space N]

omit [T2Space M] [T2Space N] in
attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
theorem image_ball_subset_ball_of_metric_upper
    (h : SmoothRiemannianMetric I3 N) (g : SmoothRiemannianMetric I3 M)
    (F : PartialDiffeomorph I3 I3 N M ∞) (p : N) {R L : ℝ} (hL : 0 < L)
    (hsource : riemannianBallOf h p R ⊆ F.source)
    (hupper : ∀ y ∈ riemannianBallOf h p R, ∀ v : TangentSpace I3 y,
      g.inner (F y) (mfderiv I3 I3 F y v) (mfderiv I3 I3 F y v) ≤
        L ^ 2 * h.inner y v v) :
    F '' riemannianBallOf h p R ⊆ riemannianBallOf g (F p) (L * R) := by
  rintro _ ⟨y, hy, rfl⟩
  obtain ⟨gamma, hstart, hend, hgamma, hlen⟩ := exists_lt_of_edistOf_lt h hy
  have hstay : ∀ s ∈ Icc (0 : ℝ) 1, gamma s ∈ riemannianBallOf h p R := by
    intro s hs
    have hd := edistOf_le_metricPathELength h hs.1
      (hgamma.mono (Icc_subset_Icc le_rfl hs.2))
    rw [hstart] at hd
    exact (hd.trans (metricPathELength_mono h gamma le_rfl hs.2)).trans_lt hlen
  have hFgamma : ContMDiffOn 𝓘(ℝ, ℝ) I3 1 (F ∘ gamma) (Icc 0 1) :=
    (F.contMDiffOn_toFun.of_le (by simp)).comp hgamma
      (fun s hs => hsource (hstay s hs))
  have hlength := metricPathELength_map_le h g (F : N → M) hL.le hgamma
    (fun s hs => F.mdifferentiableAt (by simp) (hsource (hstay s ⟨hs.1.le, hs.2.le⟩)))
    (fun s hs => hupper (gamma s) (hstay s ⟨hs.1.le, hs.2.le⟩))
  have hd := edistOf_le_metricPathELength g (by norm_num : (0 : ℝ) ≤ 1) hFgamma
  simp only [Function.comp_apply, hstart, hend] at hd
  change riemannianEDistOf g (F p) (F y) < ENNReal.ofReal (L * R)
  calc
    _ ≤ ENNReal.ofReal L * metricPathELength h gamma 0 1 := hd.trans hlength
    _ < ENNReal.ofReal L * ENNReal.ofReal R :=
      ENNReal.mul_lt_mul_right (ENNReal.ofReal_ne_zero_iff.mpr hL)
        ENNReal.ofReal_ne_top hlen
    _ = _ := (ENNReal.ofReal_mul hL.le).symm

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
theorem CompactDomain.map_strict_ball_sandwich
    (U : CompactDomain N) (h : SmoothRiemannianMetric I3 N)
    (g : SmoothRiemannianMetric I3 M) (F : PartialDiffeomorph I3 I3 N M ∞)
    (p : N) (hU : U.carrier ⊆ F.source) {a b A L : ℝ}
    (ha : 0 < a) (hA : 0 < A) (hL : 0 < L)
    (hinner : riemannianClosedBallOf h p a ⊆ U.carrier)
    (houter : U.carrier ⊆ riemannianBallOf h p b)
    (hsource : riemannianBallOf h p b ⊆ F.source)
    (hlower : ∀ y ∈ riemannianClosedBallOf h p a, ∀ v : TangentSpace I3 y,
      h.inner y v v ≤ A ^ 2 *
        g.inner (F y) (mfderiv I3 I3 F y v) (mfderiv I3 I3 F y v))
    (hupper : ∀ y ∈ riemannianBallOf h p b, ∀ v : TangentSpace I3 y,
      g.inner (F y) (mfderiv I3 I3 F y v) (mfderiv I3 I3 F y v) ≤
        L ^ 2 * h.inner y v v)
    (hreserve : L * b < 2 * (a / A)) :
    ∃ margin : ℝ, 0 < margin ∧ L * b < (2 - margin) * (a / A) ∧
      riemannianBallOf g (F p) (a / A) ⊆ (U.map F hU).carrier ∧
      (U.map F hU).carrier ⊆ riemannianBallOf g (F p) (L * b) := by
  have hc : IsCompact (riemannianClosedBallOf h p a) :=
    U.compact.of_isClosed_subset
      (isClosed_le (continuous_riemannianEDist h p) continuous_const) hinner
  have hcapture : riemannianBallOf g (F p) (a / A) ⊆ (U.map F hU).carrier :=
    (ball_subset_image_of_metric_lower_crossModel h g F p ha hA hc
      (hinner.trans hU) hlower).trans (image_mono hinner)
  have hmap : (U.map F hU).carrier ⊆ riemannianBallOf g (F p) (L * b) :=
    (image_mono houter).trans (image_ball_subset_ball_of_metric_upper h g F p hL hsource hupper)
  have hr : 0 < a / A := div_pos ha hA
  let margin := (2 * (a / A) - L * b) / (2 * (a / A))
  have hm : 0 < margin := div_pos (sub_pos.mpr hreserve) (by positivity)
  have hmul : margin * (a / A) = (2 * (a / A) - L * b) / 2 := by
    dsimp only [margin]
    field_simp [hr.ne']
  exact ⟨margin, hm, by nlinarith, hcapture, hmap⟩

end DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn

end
