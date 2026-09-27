import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.KappaSolutions.PoleEndpointDirectionalDerivativeConvergence
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.KappaSolutions.PoleEndpointJointDifferentiability
import DifferentialGeometry.Geometry.Coordinates.Calculus.SpatialDerivative
import DifferentialGeometry.Geometry.Geodesic.LocalSegment

noncomputable section

namespace DifferentialGeometry.CheegerGromovCompactness

open Filter Set TopologicalSpace MeasureTheory
open DifferentialGeometry.Analysis.Calculus
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Geometry.Connection
open DifferentialGeometry.Geometry.Riemannian.Geodesic
open DifferentialGeometry.PDE.RicciFlow.Perelman
open DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions
open CanonicalNeighborhood
open scoped _root_.Manifold ContDiff _root_.Topology ENNReal

universe u uE uH

variable {E : Type uE} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
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

local notation "U" => poleRescaledFlowSeq F hcar hreg b hbmem tau q hsigma
local notation "Y" => poleEndpointRescaledFlowSeq F hcar hreg b hbmem tau q hsigma

private local instance : MeasurableSpace E := borel E
private local instance : BorelSpace E := ⟨rfl⟩

namespace HalfLineMetricConvergenceData

theorem ae_tendsto_fderiv_poleEndpoint_redLength_chart_apply
    [ConnectedSpace P.M]
    (Phi : PointedCGHMaps Y P phi)
    (R : SmoothRiemannianMetric I P.M) (hR : RiemannianMetricComplete R)
    (bf : BumpFamily Phi) (hsrc : SourceIsSigmaCompact Phi) (htgt : TargetIsSigmaCompact Phi)
    (co : HalfLineMetricConvergenceData Phi R bf hsrc htgt)
    (hcomplete : MetricComplete
      ({ P with metric := co.gInf 0 } : PointedRiemannianManifold I))
    (hboundary : BoundarylessManifold I P.M)
    (kappa : ℕ → ℝ) (hF : ∀ i, IsAncientKappaSolution (kappa i) ((U).term i))
    (p : F.M) {J : Set P.M} (hJ : IsCompact J) {a c A : ℝ}
    (ha : 1 < a)
    (hbase : ∀ᶠ k in atTop, redLength ((U).term (phi (co.φ k))).S 0
      p (q (phi (co.φ k))) 1 ≤ A)
    (rho : ℕ → ℕ) (hrho : Tendsto rho atTop atTop)
    (ell : P.M × ℝ → ℝ)
    (hconv : ∀ y ∈ J, ∀ t ∈ Icc a c,
      Tendsto (fun k => redLength ((U).term (phi (co.φ (rho k)))).S 0 p
        (Phi.map (co.φ (rho k)) y) t) atTop (𝓝 (ell (y, t))))
    (x : P.M) {W : Set E} (hW : IsOpen W)
    (hWt : W ⊆ (extChartAt I x).target)
    (hWJ : MapsTo (extChartAt I x).symm W J) :
    ∀ᵐ z ∂(DifferentialGeometry.Integral.Measure.modelHaar (E := E)).prod volume,
      z ∈ W ×ˢ Ioo a c → ∀ v : E,
        Tendsto (fun k =>
          ((fderiv ℝ (fun w : E × ℝ =>
            redLength ((U).term (phi (co.φ (rho k)))).S 0 p
              (Phi.map (co.φ (rho k)) ((extChartAt I x).symm w.1)) w.2) z).comp
                (ContinuousLinearMap.inl ℝ E ℝ)) v) atTop
          (𝓝 (((fderiv ℝ
            (fun w : E × ℝ => ell ((extChartAt I x).symm w.1, w.2)) z).comp
              (ContinuousLinearMap.inl ℝ E ℝ)) v)) := by
  have hsource := ae_eventually_differentiableAt_poleEndpoint_redLength_chart
    F hcar hreg b hbmem tau q hsigma Phi R hR co kappa hF p hJ (c := c) ha.le hbase x hW hWt hWJ
  have hlimit := ae_differentiableAt_poleEndpoint_redLength_limit_chart
    F hcar hreg b hbmem tau q hsigma Phi R hR co kappa hF p hJ ha.le hbase
      rho hrho ell hconv x hW hWt hWJ
  filter_upwards [hsource, hlimit] with z hsz hlz
  intro hz v
  let y := (extChartAt I x).symm z.1
  have hy : y ∈ (chartAt H x).source := by
    simpa only [y, extChartAt_source] using (extChartAt I x).map_target (hWt hz.1)
  have hchart : extChartAt I x y = z.1 := (extChartAt I x).right_inv (hWt hz.1)
  have hseqJoint : ∀ᶠ k in atTop, DifferentiableAt ℝ
      (fun w : E × ℝ => redLength ((U).term (phi (co.φ (rho k)))).S 0 p
        (Phi.map (co.φ (rho k)) ((extChartAt I x).symm w.1)) w.2)
      (extChartAt I x y, z.2) := by
    simpa only [hchart, Prod.eta] using hrho.eventually (hsz hz)
  have hlimJoint : DifferentiableAt ℝ
      (fun w : E × ℝ => ell ((extChartAt I x).symm w.1, w.2))
      (extChartAt I x y, z.2) := by
    simpa only [hchart, Prod.eta] using hlz hz
  have hslice {f : P.M → ℝ → ℝ}
      (hj : DifferentiableAt ℝ (fun w : E × ℝ =>
        f ((extChartAt I x).symm w.1) w.2) (extChartAt I x y, z.2)) :
      MDifferentiableAt I 𝓘(ℝ, ℝ) (fun u => f u z.2) y := by
    apply (mdifferentiableAt_iff_source_of_mem_source
      (I := I) (I' := 𝓘(ℝ, ℝ)) (x := x) (x' := y) hy).mpr
    have hspatial := hj.hasFDerivAt.comp (extChartAt I x y)
      (hasFDerivAt_prodMk_left (𝕜 := ℝ) (extChartAt I x y) z.2)
    exact hspatial.differentiableAt.mdifferentiableAt.mdifferentiableWithinAt
  let V : Set P.M := (chartAt H x).source ∩ (extChartAt I x) ⁻¹' W
  have hV : IsOpen V := isOpen_extChartAt_preimage x hW
  have hyV : y ∈ V := by
    refine ⟨hy, ?_⟩
    change extChartAt I x y ∈ W
    simpa only [hchart] using hz.1
  have hVJ : V ⊆ J := by
    intro w hw
    have hwSource : w ∈ (extChartAt I x).source := by
      simpa only [extChartAt_source] using hw.1
    have h := hWJ hw.2
    simpa only [(extChartAt I x).left_inv hwSource] using h
  let w := TensorLieDeriv.tangentConstInChart (𝕜 := ℝ) (I := I) x v y
  obtain ⟨beta, eps, heps, hbeta0, hvel, hgeo, hbetaV, _hcompact, hspeed⟩ :=
    exists_geodesic_segment_with_initial_velocity R y w (hV.mem_nhds hyV)
  have hzero : (0 : ℝ) ∈ interior (Icc (-eps) eps) := by
    rw [interior_Icc]
    exact ⟨by linarith, heps⟩
  have hsourceSlice : ∀ᶠ k in atTop, MDifferentiableAt I 𝓘(ℝ, ℝ)
      (fun u => redLength ((U).term (phi (co.φ (rho k)))).S 0 p
        (Phi.map (co.φ (rho k)) u) z.2) (beta 0) := by
    filter_upwards [hseqJoint] with k hk
    rw [hbeta0]
    exact hslice hk
  have hlimitSlice : MDifferentiableAt I 𝓘(ℝ, ℝ)
      (fun u => ell (u, z.2)) (beta 0) := by
    rw [hbeta0]
    exact hslice (f := fun u t => ell (u, t)) hlimJoint
  have hdir := tendsto_mvfderiv_poleEndpoint_redLength_along_of_geodesic
    F hcar hreg b hbmem tau q hsigma Phi R hR bf hsrc htgt co hcomplete hboundary
    kappa hF p hJ ha hbase rho hrho (fun _ => z.2)
    (Eventually.of_forall fun _ => ⟨hz.2.1.le, hz.2.2.le⟩) beta hzero hgeo
    (fun s hs => hVJ (hbetaV hs)) hspeed (fun u => ell (u, z.2))
    (fun s hs => hconv (beta s) (hVJ (hbetaV hs)) z.2 ⟨hz.2.1.le, hz.2.2.le⟩)
    hsourceSlice hlimitSlice
  have htransport (f : P.M → ℝ) :
      mvfderiv (I := I) f (beta 0) (lVelocity beta 0) = mvfderiv (I := I) f y w := by
    calc
      _ = mvfderiv (I := I) f (beta 0) (w : E) :=
        congrArg (mvfderiv (I := I) f (beta 0)) hvel
      _ = _ := congrArg (fun a : P.M => mvfderiv (I := I) f a (w : E)) hbeta0
  have hdir' : Tendsto (fun k => mvfderiv (I := I)
      (fun u => redLength ((U).term (phi (co.φ (rho k)))).S 0 p
        (Phi.map (co.φ (rho k)) u) z.2) y w) atTop
      (𝓝 (mvfderiv (I := I) (fun u => ell (u, z.2)) y w)) := by
    simpa only [htransport] using hdir
  have h := DifferentialGeometry.tendsto_fderiv_chart_comp_inl_apply
    (F := fun k u t => redLength ((U).term (phi (co.φ (rho k)))).S 0 p
      (Phi.map (co.φ (rho k)) u) t)
    (f := fun u t => ell (u, t)) (x := x) (p := y) (t := z.2)
    hy hseqJoint hlimJoint v hdir'
  simpa only [hchart, Prod.eta] using h

end HalfLineMetricConvergenceData

end DifferentialGeometry.CheegerGromovCompactness
