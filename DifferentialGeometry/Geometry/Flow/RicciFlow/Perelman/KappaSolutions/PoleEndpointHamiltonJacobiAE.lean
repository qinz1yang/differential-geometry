import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.KappaSolutions.PoleEndpointJointDifferentiability
import DifferentialGeometry.Topology.Manifold.ProductDifferentiability
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.KappaSolutions.AncientHamiltonJacobiEquality
import Mathlib.Analysis.Calculus.Deriv.Prod


noncomputable section

namespace DifferentialGeometry.CheegerGromovCompactness

open Bundle Filter _root_.Manifold MeasureTheory Set
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Geometry.Operator
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

private local instance : CompleteSpace E := FiniteDimensional.complete ℝ E

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

theorem ae_eventually_poleEndpoint_redLength_hamilton_jacobi_eq_chart
    [ConnectedSpace P.M]
    (Phi : PointedCGHMaps Y P phi) (R : SmoothRiemannianMetric I P.M)
    (hR : RiemannianMetricComplete R)
    {bf : BumpFamily Phi} {hsrc : SourceIsSigmaCompact Phi} {htgt : TargetIsSigmaCompact Phi}
    (co : HalfLineMetricConvergenceData Phi R bf hsrc htgt)
    (kappa : ℕ → ℝ) (hancient : ∀ i, IsAncientKappaSolution (kappa i) ((U).term i))
    (p : F.M) {J : Set P.M} (hJ : IsCompact J) {A a c : ℝ} (ha : 1 ≤ a)
    (hbase : ∀ᶠ k in atTop, redLength ((U).term (phi (co.φ k))).S 0 p
      (q (phi (co.φ k))) 1 ≤ A)
    (x : P.M) {W : Set E} (hW : IsOpen W) (hWt : W ⊆ (extChartAt I x).target)
    (hWJ : MapsTo (extChartAt I x).symm W J) :
    ∀ᵐ z ∂(DifferentialGeometry.Integral.Measure.modelHaar (E := E)).prod volume,
      z ∈ W ×ˢ Ioo a c → ∀ᶠ k in atTop,
        let i := phi (co.φ k)
        let y := Phi.map (co.φ k) ((extChartAt I x).symm z.1)
        let g := ((U).term i).S.base.metric (-z.2)
        let ell := fun v : E × ℝ => redLength ((U).term i).S 0 p
          (Phi.map (co.φ k) ((extChartAt I x).symm v.1)) v.2
        let grad := gradientFun g (fun w => redLength ((U).term i).S 0 p w z.2) y
        fderiv ℝ ell z (0, 1) + (1 / 2 : ℝ) * g.inner y grad grad -
          (1 / 2 : ℝ) * ((U).term i).S.scalar (-z.2) y + ell z / (2 * z.2) = 0 := by
  have hae := ae_eventually_differentiableAt_poleEndpoint_redLength_chart
    F hcar hreg b hbmem tau q hsigma Phi R hR co kappa hancient p hJ (c := c) ha hbase
    x hW hWt hWJ
  obtain ⟨N, hN⟩ := Phi.source_subset hJ
  have hsource : ∀ᶠ k in atTop, J ⊆ Phi.source (co.φ k) :=
    (co.strictMono.tendsto_atTop.eventually (eventually_ge_atTop N)).mono
      fun k hk => hN (co.φ k) hk
  filter_upwards [hae] with z hz
  intro hzw
  filter_upwards [hz hzw, hsource] with k hk hksource
  let i := phi (co.φ k)
  let y := Phi.map (co.φ k) ((extChartAt I x).symm z.1)
  let ell := fun v : E × ℝ => redLength ((U).term i).S 0 p
    (Phi.map (co.φ k) ((extChartAt I x).symm v.1)) v.2
  have hcoord : DifferentiableAt ℝ ell z := hk
  have hpull : MDifferentiableAt (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ)
      (fun v : ℝ × P.M => redLength ((U).term i).S 0 p
        (Phi.map (co.φ k) v.2) v.1) (z.2, (extChartAt I x).symm z.1) :=
    DifferentialGeometry.Topology.Manifold.mdifferentiableAt_prod_of_differentiableAt_chart
      (fun v : ℝ × P.M => redLength ((U).term i).S 0 p (Phi.map (co.φ k) v.2) v.1)
      x (hWt hzw.1) z.2 hcoord
  have hlocal := (Phi.partialDiffeomorph (co.φ k)).isLocalDiffeomorphAt I I ∞
    (hksource (hWJ hzw.1))
  have hdiff : MDifferentiableAt (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ)
      (fun v : ℝ × F.M => redLength ((U).term i).S 0 p v.2 v.1) (z.2, y) :=
    hlocal.mdifferentiableAt_prodMap_of_comp (by simp) z.2 hpull
  have hpos : 0 < z.2 := (zero_lt_one.trans_le ha).trans hzw.2.1
  have hHJ := ancient_redLength_hamilton_jacobi_eq_of_mdifferentiableAt
    ((U).term i) (hancient i) hpos p y hdiff
  have htime : deriv (fun s => redLength ((U).term i).S 0 p y s) z.2 =
      fderiv ℝ ell z (0, 1) := by
    exact (hcoord.hasFDerivAt.comp_hasDerivAt z.2
      ((hasDerivAt_const z.2 z.1).prodMk (hasDerivAt_id z.2))).deriv
  rw [htime] at hHJ
  exact hHJ

end HalfLineMetricConvergenceData

end DifferentialGeometry.CheegerGromovCompactness
