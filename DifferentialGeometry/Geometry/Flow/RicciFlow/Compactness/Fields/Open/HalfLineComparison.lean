import DifferentialGeometry.Geometry.Flow.RicciFlow.Compactness.Fields.Open.ClosedHalfLineSolution
import DifferentialGeometry.Geometry.Flow.RicciFlow.Compactness.Fields.Open.MetricComparison
import DifferentialGeometry.Geometry.Flow.RicciFlow.Compactness.Metric.ParabolicRescaling
import DifferentialGeometry.Geometry.Metric.Convergence.DerivativeNorm.Locality
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.KappaSolutions.CurvatureNormalization

section
set_option autoImplicit false

noncomputable section

open Filter Set
open scoped Manifold ContDiff Topology

namespace DifferentialGeometry.CheegerGromovCompactness

open DifferentialGeometry.PDE.RicciFlow
open DifferentialGeometry.Geometry.Curvature
open Perelman.CanonicalNeighborhood Perelman.CanonicalNeighborhood.FiniteHorn

universe u

attribute [local instance] PointedFlowData.topology PointedFlowData.charted
  PointedFlowData.smooth PointedFlowData.t2 PointedFlowData.sigmaCompact
  PointedRiemannianManifold.topology PointedRiemannianManifold.charted
  PointedRiemannianManifold.smooth PointedRiemannianManifold.t2
  PointedRiemannianManifold.sigmaCompact

theorem HalfLineMetricConvergenceData.eventually_metric_comparison
    {X : PointedFlowSeq.{u, 0, 0} I3} {P : PointedRiemannianManifold.{u, 0, 0} I3}
    {phi : ℕ → ℕ} (Phi : PointedCGHMaps X P phi)
    {R : SmoothRiemannianMetric I3 P.M} {bf : BumpFamily Phi}
    {hsrc : SourceIsSigmaCompact Phi} {htgt : TargetIsSigmaCompact Phi}
    (co : HalfLineMetricConvergenceData Phi R bf hsrc htgt)
    (hcarrier : X.D.carrier = Iic 0) (hregular : Iio 0 ⊆ X.D.regular)
    {a b : ℝ} (hab : a ≤ b) (hb : b ≤ 0)
    (K : Set P.M) (hK : IsCompact K) (order : ℕ) (eps : ℝ) (heps : 0 < eps) :
    ∀ᶠ i in atTop, Nonempty (MetricComparisonOn co.gInf
      (fun t => (X.term (phi (co.φ i))).S.base.metric t)
      (Phi.map (co.φ i)) K (Icc a b) order eps) := by
  let _ : NeZero (Module.finrank ℝ Surgery.Topology.ThreeSpace) :=
    ⟨by simp [Surgery.Topology.ThreeSpace]⟩
  let L : SolutionOn (I := I3) (M := P.M) X.D := { base := { metric := co.gInf } }
  have hL : IsSolutionOn L := co.isSolutionOn Phi hcarrier hregular
  obtain ⟨n, hn⟩ := exists_nat_ge (1 - a)
  have hnb : -(n : ℝ) < 0 := by linarith
  have hslab : Icc (-(n : ℝ) - 1) 0 ⊆ X.D.carrier := by
    rw [hcarrier]
    exact Icc_subset_Iic_self
  have hreg : Ioo (-(n : ℝ) - 1) 0 ⊆ X.D.regular :=
    Ioo_subset_Iio_self.trans hregular
  exact (co.convergenceOn n).eventually_metric_comparison Phi R bf hsrc htgt
    co.strictMono L hL (by linarith : -(n : ℝ) - 1 < -(n : ℝ)) hnb
    hslab hreg hslab hreg Subset.rfl hab
    (fun t ht => ⟨by linarith [ht.1], ht.2.trans hb⟩) K hK order eps heps

end DifferentialGeometry.CheegerGromovCompactness

end

end

section
set_option autoImplicit false

noncomputable section

open Filter Set
open scoped Manifold ContDiff Topology

namespace DifferentialGeometry.CheegerGromovCompactness

open DifferentialGeometry.PDE.RicciFlow DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Geometry.Metric
open Perelman.CanonicalNeighborhood Perelman.CanonicalNeighborhood.FiniteHorn

universe u

attribute [local instance] PointedFlowData.topology PointedFlowData.charted
  PointedFlowData.smooth PointedFlowData.t2 PointedFlowData.sigmaCompact
  PointedRiemannianManifold.topology PointedRiemannianManifold.charted
  PointedRiemannianManifold.smooth PointedRiemannianManifold.t2
  PointedRiemannianManifold.sigmaCompact

theorem HalfLineMetricConvergenceData.parabolicRescale_extension_converges
    {X : PointedFlowSeq.{u, 0, 0} I3} {P : PointedRiemannianManifold.{u, 0, 0} I3}
    {phi : ℕ → ℕ} (Phi : PointedCGHMaps X P phi)
    {R : SmoothRiemannianMetric I3 P.M} {bf : BumpFamily Phi}
    {hsrc : SourceIsSigmaCompact Phi} {htgt : TargetIsSigmaCompact Phi}
    (co : HalfLineMetricConvergenceData Phi R bf hsrc htgt)
    (hcarrier : X.D.carrier = Iic 0) (hregular : Iio 0 ⊆ X.D.regular)
    (c : ℕ → ℝ) (hc : ∀ i, 0 < c i) (hctop : Tendsto c atTop (𝓝 1))
    (T : ℝ) (hT : 0 < T) (K : Set P.M) (hK : IsCompact K) (order : ℕ) :
    ∀ eps : ℝ, 0 < eps → ∀ᶠ i in atTop, ∀ s ∈ Icc (-T) 0,
      metricDerivNormSupOn K order
        (scaleMetric (c i) (hc i) (gSeqExt Phi R bf hsrc htgt (co.φ i) (s / c i)))
        (co.gInf s) R < eps := by
  let _ : NeZero (Module.finrank ℝ Surgery.Topology.ThreeSpace) :=
    ⟨by simp [Surgery.Topology.ThreeSpace]⟩
  let L : SolutionOn (I := I3) (M := P.M) ancientTimeInterval := { base := { metric := co.gInf } }
  have hL : IsSolutionOn L := by
    have hsol := co.isSolutionOn Phi hcarrier hregular
    apply isSolutionOn_timeRestrict hsol
    · rw [hcarrier]; exact Subset.rfl
    · exact hregular
  have hhalf : ∀ᶠ i in atTop, (1 / 2 : ℝ) ≤ c i :=
    ((tendsto_order.1 hctop).1 (1 / 2) (by norm_num)).mono fun _ hi => hi.le
  have htwo : ∀ᶠ i in atTop, c i ≤ 2 :=
    ((tendsto_order.1 hctop).2 2 (by norm_num)).mono fun _ hi => hi.le
  obtain ⟨n, hn⟩ := exists_nat_ge (2 * T)
  intro eps heps
  obtain ⟨N, hN⟩ := (co.convergenceOn n).convergence K hK order (eps / 8) (by positivity)
  filter_upwards [hhalf, htwo, eventually_ge_atTop N,
    parabolicRescale_metricDerivNormSupOn_tendsto_zero L hL c hc hctop R T hT K hK
      order (eps / 4) (by positivity)] with i hi hi2 hNi hreference
  intro s hs
  have ht : s / c i ∈ Icc (-(n : ℝ)) 0 := by
    refine ⟨(le_div_iff₀ (hc i)).mpr ?_, div_nonpos_of_nonpos_of_nonneg hs.2 (hc i).le⟩
    have hh : -2 * T * c i ≤ s := by nlinarith [hs.1]
    exact (mul_le_mul_of_nonneg_right (by linarith : -(n : ℝ) ≤ -2 * T) (hc i).le).trans hh
  have href := hreference s hs
  apply lt_of_le_of_lt (metricDerivNormSupOn_le_of_forall K order _ _ R
    (eps / 2) (by positivity) ?_) (by linarith)
  intro q hq x hx
  have hseq : metricDerivNorm q (gSeqExt Phi R bf hsrc htgt (co.φ i) (s / c i))
      (co.gInf (s / c i)) R x < eps / 8 :=
    (derivNorm_le_sup hK hq _ _ _ hx).trans_lt (hN i hNi _ ht)
  have hrefx : metricDerivNorm q (scaleMetric (c i) (hc i) (co.gInf (s / c i)))
      (co.gInf s) R x < eps / 4 := (derivNorm_le_sup hK hq _ _ _ hx).trans_lt href
  have hh := metricDerivNorm_triangle q
    (scaleMetric (c i) (hc i) (gSeqExt Phi R bf hsrc htgt (co.φ i) (s / c i)))
    (scaleMetric (c i) (hc i) (co.gInf (s / c i))) (co.gInf s) R x
  rw [metricDerivNorm_scaleMetric_both_left] at hh
  have hmul := mul_le_mul_of_nonneg_left hseq.le (hc i).le
  have hmul2 := mul_le_mul_of_nonneg_right hi2 (show 0 ≤ eps / 8 by positivity)
  linarith

end DifferentialGeometry.CheegerGromovCompactness

end

end

section
set_option autoImplicit false

noncomputable section

open Filter Set
open scoped Manifold ContDiff Topology

namespace DifferentialGeometry.CheegerGromovCompactness

open DifferentialGeometry.PDE.RicciFlow DifferentialGeometry.Geometry.Curvature
open Perelman.CanonicalNeighborhood Perelman.CanonicalNeighborhood.FiniteHorn
open Perelman.KappaSolutions

universe u

attribute [local instance] PointedFlowData.topology PointedFlowData.charted
  PointedFlowData.smooth PointedFlowData.t2 PointedFlowData.sigmaCompact
  PointedFlowData.t2TangentBundle
  PointedRiemannianManifold.topology PointedRiemannianManifold.charted
  PointedRiemannianManifold.smooth PointedRiemannianManifold.t2
  PointedRiemannianManifold.sigmaCompact

theorem HalfLineMetricConvergenceData.eventually_parabolicRescale_fixed_metric_comparison
    {X : PointedFlowSeq.{u, 0, 0} I3} {P : PointedRiemannianManifold.{u, 0, 0} I3}
    {phi : ℕ → ℕ} (Phi : PointedCGHMaps X P phi)
    {R : SmoothRiemannianMetric I3 P.M} {bf : BumpFamily Phi}
    {hsrc : SourceIsSigmaCompact Phi} {htgt : TargetIsSigmaCompact Phi}
    (co : HalfLineMetricConvergenceData Phi R bf hsrc htgt)
    (hcarrier : X.D.carrier = Iic 0) (hregular : X.D.regular = Iio 0)
    (c : ℕ → ℝ) (hc : ∀ i, 0 < c i) (hctop : Tendsto c atTop (𝓝 1))
    (T : ℝ) (hT : 0 < T) (K : Set P.M) (hK : IsCompact K)
    (order : ℕ) (eps : ℝ) (heps : 0 < eps) :
    ∀ᶠ i in atTop, Nonempty (MetricComparisonOn co.gInf
      (fun s => scaleMetric (c i) (hc i)
        ((X.term (phi (co.φ i))).S.base.metric (s / c i)))
      (Phi.map (co.φ i)) K (Icc (-T) 0) order eps) := by
  let _ : NeZero (Module.finrank ℝ Surgery.Topology.ThreeSpace) :=
    ⟨by simp [Surgery.Topology.ThreeSpace]⟩
  have hzero : (0 : ℝ) ∈ X.D.carrier := by rw [hcarrier]; exact (le_rfl : (0 : ℝ) ≤ 0)
  let Y : PointedFlowSeq.{u, 0, 0} I3 := {
    D := ancientTimeInterval
    term i := curvatureNormalizedFlow (X.term (phi (co.φ i))) hcarrier hregular
      0 (c i) (hc i) hzero (X.term (phi (co.φ i))).basepoint }
  let Psi : PointedCGHMaps Y P id := {
    partialDiffeomorph i := Phi.partialDiffeomorph (co.φ i)
    source_exhausts := (Phi.compSubseq co.φ co.strictMono).source_exhausts
    base_mem i := Phi.base_mem (co.φ i)
    basepoint_map i := Phi.basepoint_map (co.φ i) }
  have hsrc' : SourceIsSigmaCompact Psi := fun i => hsrc (co.φ i)
  have htgt' : TargetIsSigmaCompact Psi := fun i => htgt (co.φ i)
  obtain ⟨bf'⟩ := nonempty_bumpFamily Psi
  let L : SolutionOn (I := I3) (M := P.M) ancientTimeInterval := { base := { metric := co.gInf } }
  have hL : IsSolutionOn L := by
    have hsol := co.isSolutionOn Phi hcarrier hregular.symm.subset
    apply isSolutionOn_timeRestrict hsol
    · rw [hcarrier]; exact Subset.rfl
    · rw [hregular]; exact Subset.rfl
  have hsourceMetric (i : ℕ) (s : ℝ) : (Y.term i).S.base.metric s =
      scaleMetric (c i) (hc i) ((X.term (phi (co.φ i))).S.base.metric (s / c i)) := by
    change scaleMetric (c i) (hc i) ((X.term (phi (co.φ i))).S.base.metric
      (parabolicTime 0 (c i) s)) = _
    rw [parabolicTime, zero_add]
  have hnorm : ∀ Q : Set P.M, IsCompact Q → ∀ r : ℕ, ∀ eta : ℝ, 0 < eta →
      ∃ N : ℕ, ∀ i ≥ N, ∀ s ∈ Icc (-T) 0,
        metricDerivNormSupOn Q r (gSeqExt Psi R bf' hsrc' htgt' i s) (co.gInf s) R < eta := by
    intro Q hQ r eta heta
    have hconv := co.parabolicRescale_extension_converges Phi hcarrier hregular.symm.subset
      c hc hctop T hT Q hQ r (eta / 2) (by positivity)
    have hold := co.strictMono.tendsto_atTop.eventually
      (eventually_gSeqExt_eq_pullback Phi R bf hsrc htgt Q hQ)
    have hnew := eventually_gSeqExt_eq_pullback Psi R bf' hsrc' htgt' Q hQ
    obtain ⟨N, hN⟩ := eventually_atTop.mp (hconv.and (hold.and hnew))
    refine ⟨N, fun i hi s hs => ?_⟩
    obtain ⟨hconv, ⟨U, hU, hQU, _hUsrc, hUeq⟩, V, hV, hQV, _hVsrc, hVeq⟩ := hN i hi
    apply lt_of_le_of_lt (metricDerivNormSupOn_le_of_forall Q r _ _ R
      (eta / 2) (by positivity) ?_) (by linarith)
    intro a ha x hx
    have hlocal : ∀ᶠ y in 𝓝 x, ∀ v w : TangentSpace I3 y,
        (gSeqExt Psi R bf' hsrc' htgt' i s).inner y v w =
          (scaleMetric (c i) (hc i)
            (gSeqExt Phi R bf hsrc htgt (co.φ i) (s / c i))).inner y v w := by
      filter_upwards [(hU.inter hV).mem_nhds ⟨hQU hx, hQV hx⟩] with y hy
      intro v w
      rw [hVeq s y hy.2 v w, hsourceMetric]
      change (c i) * ((X.term (phi (co.φ i))).S.base.metric (s / c i)).inner
        (Phi.map (co.φ i) y) (mfderiv I3 I3 (Phi.map (co.φ i)) y v)
        (mfderiv I3 I3 (Phi.map (co.φ i)) y w) =
          (c i) * (gSeqExt Phi R bf hsrc htgt (co.φ i) (s / c i)).inner y v w
      rw [hUeq (s / c i) y hy.1 v w]
    rw [metricDerivNorm_eq_of_metric_eventuallyEq a _ _ _ R x hlocal]
    exact ((derivNorm_le_sup hQ ha _ _ _ hx).trans_lt (hconv s hs)).le
  have hh := eventually_metric_comparison_of_extension_convergence Psi R bf' hsrc' htgt'
    L hL (by linarith : -T - 1 < -T) (by linarith : -T < 0)
    (by intro s hs; exact hs.2) (by intro s hs; exact hs.2)
    (by intro s hs; exact hs.2) (by intro s hs; exact hs.2)
    (by linarith : -T < 0) Subset.rfl R hnorm K hK order eps heps
  filter_upwards [hh] with i hi
  have heq : (fun s => (Y.term (id i)).S.base.metric s) =
      (fun s => scaleMetric (c i) (hc i)
        ((X.term (phi (co.φ i))).S.base.metric (s / c i))) := funext (hsourceMetric i)
  rw [heq] at hi
  exact hi

end DifferentialGeometry.CheegerGromovCompactness

end

end
