import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.KappaSolutions.PoleEndpointTimeChartRegularity
import Mathlib.Analysis.Calculus.ContDiff.RCLike
import Mathlib.Analysis.SpecialFunctions.Log.Deriv

noncomputable section

namespace DifferentialGeometry.CheegerGromovCompactness

open Bundle Filter _root_.Manifold MeasureTheory Set
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.PDE.RicciFlow.Perelman
open DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions
open CanonicalNeighborhood
open scoped _root_.Manifold ContDiff _root_.Topology ENNReal

universe u uE uH

variable {E : Type uE} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]
  {H : Type uH} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {D : RealTimeInterval} (F : PointedFlowData.{u, uE, uH} (I := I) D)
  (hcar : D.carrier = Iic 0) (hreg : D.regular = Iio 0)
  (b : ℝ) (hbmem : b ∈ D.carrier) (tau : ℕ → ℝ) (q : ℕ → F.M)
  (hsigma : ∀ i, 0 < tau i + b)
  {P : PointedRiemannianManifold.{u, uE, uH} (I := I)} {phi : ℕ → ℕ}

private local instance : TopologicalSpace F.M := F.topology
private local instance : ChartedSpace H F.M := F.charted
private local instance : IsManifold I ∞ F.M := F.smooth
private local instance : SigmaCompactSpace F.M := F.sigmaCompact
private local instance : T2Space F.M := F.t2

attribute [local instance] PointedRiemannianManifold.topology
  PointedRiemannianManifold.charted PointedRiemannianManifold.smooth
  PointedRiemannianManifold.t2 PointedRiemannianManifold.sigmaCompact
  PointedRiemannianManifold.t2TangentBundle

private local instance : MeasurableSpace E := borel E
private local instance : BorelSpace E := ⟨rfl⟩

local notation "U" => poleRescaledFlowSeq F hcar hreg b hbmem tau q hsigma
local notation "Y" => poleEndpointRescaledFlowSeq F hcar hreg b hbmem tau q hsigma

namespace HalfLineMetricConvergenceData

theorem locallyLipschitzOn_poleEndpoint_redDensity_limit_time_chart
    [ConnectedSpace P.M]
    (Phi : PointedCGHMaps Y P phi) (R : SmoothRiemannianMetric I P.M)
    (hR : RiemannianMetricComplete R)
    {bf : BumpFamily Phi} {hsrc : SourceIsSigmaCompact Phi} {htgt : TargetIsSigmaCompact Phi}
    (co : HalfLineMetricConvergenceData Phi R bf hsrc htgt)
    (kappa : ℕ → ℝ) (hancient : ∀ i, IsAncientKappaSolution (kappa i) ((U).term i))
    (p : F.M) {J : Set P.M} (hJ : IsCompact J) {A a c : ℝ} (ha : 1 ≤ a)
    (hbase : ∀ᶠ k in atTop, redLength ((U).term (phi (co.φ k))).S 0 p
      (q (phi (co.φ k))) 1 ≤ A)
    (rho : ℕ → ℕ) (hrho : Tendsto rho atTop atTop)
    (ell : P.M × ℝ → ℝ)
    (hconv : ∀ y ∈ J, ∀ t ∈ Icc a c,
      Tendsto (fun k => redLength ((U).term (phi (co.φ (rho k)))).S 0 p
        (Phi.map (co.φ (rho k)) y) t) atTop (𝓝 (ell (y, t))))
    (x : P.M) {W : Set E} (hWt : W ⊆ (extChartAt I x).target)
    (hWJ : MapsTo (extChartAt I x).symm W J) :
    LocallyLipschitzOn (Icc a c ×ˢ W)
      (fun v : ℝ × E => Real.exp (-ell ((extChartAt I x).symm v.2, v.1) -
        (Module.finrank ℝ E : ℝ) / 2 * Real.log v.1 -
        (Module.finrank ℝ E : ℝ) / 2 * Real.log (4 * Real.pi))) := by
  let S := Icc a c ×ˢ W
  let f := fun v : ℝ × E => ell ((extChartAt I x).symm v.2, v.1)
  let n : ℝ := Module.finrank ℝ E
  have hf : LocallyLipschitzOn S f :=
    locallyLipschitzOn_poleEndpoint_redLength_limit_time_chart
      F hcar hreg b hbmem tau q hsigma Phi R hR co kappa hancient p hJ ha hbase
      rho hrho ell hconv x hWt hWJ
  have hw : LocallyLipschitzOn S (fun v : ℝ × E => n / 2 * Real.log v.1) := by
    intro v hv
    have ht : 0 < v.1 := zero_lt_one.trans_le (ha.trans hv.1.1)
    have hs : ContDiffAt ℝ 1 (fun v : ℝ × E => n / 2 * Real.log v.1) v :=
      contDiffAt_const.mul ((Real.contDiffAt_log.mpr ht.ne').comp v contDiffAt_fst)
    obtain ⟨L, T, hT, hLip⟩ := hs.exists_lipschitzOnWith
    exact ⟨L, T, mem_nhdsWithin_of_mem_nhds hT, hLip⟩
  have hc : LocallyLipschitzOn S (fun _ : ℝ × E => n / 2 * Real.log (4 * Real.pi)) :=
    (LipschitzWith.const _).locallyLipschitz.locallyLipschitzOn
  have hg := (hf.neg.sub hw).sub hc
  apply locallyLipschitzOn_iff_restrict.mpr
  exact (Real.contDiff_exp : ContDiff ℝ 1 Real.exp).locallyLipschitz.comp hg.restrict

end HalfLineMetricConvergenceData

end DifferentialGeometry.CheegerGromovCompactness
