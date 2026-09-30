import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.KappaSolutions.PoleEndpointDensityLipschitz
import DifferentialGeometry.Analysis.Parabolic.WeakEquation.GaussianDensity
import DifferentialGeometry.Geometry.Flow.RicciFlow.Compactness.Fields.Open.HalfLineTimeReversal

noncomputable section

private theorem locallyLipschitzOn_comp_lipschitzWith
    {X Y Z : Type*} [PseudoEMetricSpace X] [PseudoEMetricSpace Y] [PseudoEMetricSpace Z]
    {S : Set X} {T : Set Y} {f : Y → Z} {g : X → Y} {C : NNReal}
    (hf : LocallyLipschitzOn T f) (hg : LipschitzWith C g) (hmap : Set.MapsTo g S T) :
    LocallyLipschitzOn S (f ∘ g) := by
  apply locallyLipschitzOn_iff_restrict.mpr
  exact hf.restrict.comp (hg.lipschitzOnWith.mapsToRestrict hmap).locallyLipschitz

namespace DifferentialGeometry.CheegerGromovCompactness

open Bundle Filter _root_.Manifold MeasureTheory Set
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.PDE.RicciFlow.Perelman
open DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions
open CanonicalNeighborhood
open DifferentialGeometry.Analysis.Sobolev.Euclidean
  (spatial_fderiv_exp_gaussian_normalization_ae_of_locallyLipschitzOn)
open DifferentialGeometry.Analysis.Parabolic
  (exists_lp_weak_equation_exp_gaussian_of_chartResidual_eq_zero)
open DifferentialGeometry.Analysis.Laplacian.MetricExtension
open DifferentialGeometry.Geometry.Operator
open DifferentialGeometry.Integral.Measure
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
  PointedRiemannianManifold.t2TangentBundle

private local instance : MeasurableSpace E := borel E
private local instance : BorelSpace E := ⟨rfl⟩

local notation "U" => poleRescaledFlowSeq F hcar hreg b hbmem tau q hsigma
local notation "Y" => poleEndpointRescaledFlowSeq F hcar hreg b hbmem tau q hsigma

namespace HalfLineMetricConvergenceData

local notation "EuStd" => EuclideanSpace ℝ (Fin (Module.finrank ℝ E))

private local instance : MeasurableSpace EuStd :=
  WithLp.measurableSpace 2 ((i : Fin (Module.finrank ℝ E)) → ℝ)

theorem exists_lp_weak_equation_poleEndpoint_redDensity_limit_of_chartResidual_eq_zero
    [ConnectedSpace P.M]
    (Phi : PointedCGHMaps Y P phi) (R : SmoothRiemannianMetric I P.M)
    (hR : RiemannianMetricComplete R)
    {bf : BumpFamily Phi} {hsrc : SourceIsSigmaCompact Phi} {htgt : TargetIsSigmaCompact Phi}
    (co : HalfLineMetricConvergenceData Phi R bf hsrc htgt)
    (kappa : ℕ → ℝ) (hancient : ∀ i, IsAncientKappaSolution (kappa i) ((U).term i))
    (p : F.M) {J : Set P.M} (hJ : IsCompact J) {A a c : ℝ} (ha : 1 < a)
    (hbase : ∀ᶠ k in atTop, redLength ((U).term (phi (co.φ k))).S 0 p
      (q (phi (co.φ k))) 1 ≤ A)
    (rho : ℕ → ℕ) (hrho : Tendsto rho atTop atTop)
    (ell : P.M × ℝ → ℝ)
    (hconv : ∀ y ∈ J, ∀ t ∈ Icc a c,
      Tendsto (fun k => redLength ((U).term (phi (co.φ (rho k)))).S 0 p
        (Phi.map (co.φ (rho k)) y) t) atTop (𝓝 (ell (y, t))))
    (x : P.M) {Ω : Set EuStd} (hΩ : IsOpen Ω) (hΩc : IsCompact (closure Ω))
    (hΩt : (toEuclidean (E := E)).symm '' closure Ω ⊆ (extChartAt I x).target)
    (hΩJ : MapsTo (extChartAt I x).symm ((toEuclidean (E := E)).symm '' closure Ω) J) :
    let ν := (volume.restrict (Icc a c)).prod (volume.restrict Ω)
    let f := fun z : ℝ × E => ell ((extChartAt I x).symm z.2, z.1)
    let u := fun z : ℝ × E => Real.exp (-f z -
      (Module.finrank ℝ E : ℝ) / 2 * Real.log z.1 -
      (Module.finrank ℝ E : ℝ) / 2 * Real.log (4 * Real.pi))
    let uV := fun v : ℝ × EuStd => u (v.1, (toEuclidean (E := E)).symm v.2)
    (∀ ψ : ℝ × E → ℝ, ContDiff ℝ (⊤ : ℕ∞) ψ → HasCompactSupport ψ →
      tsupport ψ ⊆ Ioo a c ×ˢ ((toEuclidean (E := E)) ⁻¹' Ω) →
      (∫ z, chartDensity (co.gInf (1 - z.1)) x ((extChartAt I x).symm z.2) * u z *
        (deriv (fun t => ψ (t, z.2)) z.1 +
          chartGradientBilin (co.gInf (1 - z.1)) x ((extChartAt I x).symm z.2)
            (fderiv ℝ (fun y => f (z.1, y)) z.2)
            (fderiv ℝ (fun y => ψ (z.1, y)) z.2))
        ∂(volume.restrict (Ioc a c)).prod
          ((modelHaar (E := E)).restrict ((toEuclidean (E := E)) ⁻¹' Ω))) = 0) →
    ∃ V : Lp ℝ 2 ν, ∃ K : Fin (Module.finrank ℝ E) → Lp ℝ 2 ν,
      (V =ᵐ[ν] uV) ∧
      (∀ i, K i =ᵐ[ν] fun v =>
        fderiv ℝ (fun y => uV (v.1, y)) v.2 (EuclideanSpace.single i 1)) ∧
      (∀ i, K i =ᵐ[ν] fun v => -uV v *
        fderiv ℝ (fun y => f (v.1, (toEuclidean (E := E)).symm y)) v.2
          (EuclideanSpace.single i 1)) ∧
      (∀ i, ∀ᵐ t ∂volume.restrict (Icc a c), DeGiorgi.HasWeakPartialDeriv i
        (fun y => K i (t, y)) (fun y => V (t, y)) Ω) ∧
      ∀ φ : ℝ × EuStd → ℝ, ContDiff ℝ (⊤ : ℕ∞) φ → HasCompactSupport φ →
        tsupport φ ⊆ Ioo a c ×ˢ Ω →
        (∫ v, densityOnEuclid (co.gInf (1 - v.1)) x v.2 * V v *
          fderiv ℝ φ v (1, 0) ∂ν) =
            ∑ j, ∫ v, (∑ i, weightedInvGramOnEuclid
              (co.gInf (1 - v.1)) x i j v.2 * K i v) *
                fderiv ℝ φ v (0, EuclideanSpace.single j 1) ∂ν := by
  intro ν f u uV hresidual
  let W := (toEuclidean (E := E)).symm '' closure Ω
  have hfchart := locallyLipschitzOn_poleEndpoint_redLength_limit_time_chart
    F hcar hreg b hbmem tau q hsigma Phi R hR co kappa hancient p hJ ha.le hbase
      rho hrho ell hconv x hΩt hΩJ
  let T : ℝ × EuStd → ℝ × E := fun v => (v.1, (toEuclidean (E := E)).symm v.2)
  have hT : LipschitzWith (max 1 ‖(toEuclidean (E := E)).symm.toContinuousLinearMap‖₊) T :=
    by
      simpa only [mul_one, T, Function.comp_def] using
        (LipschitzWith.prod_fst : LipschitzWith 1 (Prod.fst : ℝ × EuStd → ℝ)).prodMk
          ((toEuclidean (E := E)).symm.lipschitzWith.comp
            (LipschitzWith.prod_snd : LipschitzWith 1 (Prod.snd : ℝ × EuStd → EuStd)))
  have hmaps : MapsTo T (Icc a c ×ˢ closure Ω) (Icc a c ×ˢ W) :=
    fun v hv => ⟨hv.1, ⟨v.2, hv.2, rfl⟩⟩
  have hf : LocallyLipschitzOn (Icc a c ×ˢ closure Ω)
      (fun v : ℝ × EuStd => f (v.1, (toEuclidean (E := E)).symm v.2)) := by
    simpa only [Function.comp_def, T, f] using
      locallyLipschitzOn_comp_lipschitzWith hfchart hT hmaps
  let Dτ := RealTimeInterval.openInfinite 1 a ha
  have hYreg : Iio 0 ⊆ (Y).D.regular := by
    change Iio 0 ⊆ ancientTimeInterval.regular
    rw [ancientTimeInterval_regular]
  have hg : MetricFamilySmoothOn (I := I) Dτ (fun t => co.gInf (1 - t)) :=
    co.metric_smooth_time_sub (Φ := Phi) hYreg 1 (fun _ ht => ht)
  have hinterval : Icc a c ⊆ Dτ.regular := fun _ ht => ha.trans_le ht.1
  have hΩtV : closure Ω ⊆ chartTargetEuclid (I := I) x := by
    intro v hv
    exact ⟨(toEuclidean (E := E)).symm v, hΩt ⟨v, hv, rfl⟩,
      (toEuclidean (E := E)).apply_symm_apply v⟩
  obtain ⟨V, K, hV, hK, hspatial, hweak⟩ :=
    exists_lp_weak_equation_exp_gaussian_of_chartResidual_eq_zero Dτ
      (fun t => co.gInf (1 - t)) hg x (zero_lt_one.trans ha) hinterval
      hΩ hΩc hΩtV f (Module.finrank ℝ E) hf hresidual
  refine ⟨V, K, hV, hK, ?_, hspatial, hweak⟩
  intro i
  exact (hK i).trans
    (spatial_fderiv_exp_gaussian_normalization_ae_of_locallyLipschitzOn
      (zero_lt_one.trans ha) hΩ hΩc hf (Module.finrank ℝ E) i)

end HalfLineMetricConvergenceData

end DifferentialGeometry.CheegerGromovCompactness
