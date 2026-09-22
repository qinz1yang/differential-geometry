import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.KappaSolutions.PoleEndpointResidualVanishing
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.KappaSolutions.PoleEndpointCutoffResidualLimit
import DifferentialGeometry.Analysis.Calculus.Cutoff.Compact
import Mathlib.Order.Filter.AtTopBot.Archimedean


noncomputable section

namespace DifferentialGeometry.CheegerGromovCompactness

open Filter MeasureTheory Set
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Geometry.Operator
open DifferentialGeometry.Geometry.Riemannian
open DifferentialGeometry.Integral.Measure
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
private local instance : MeasurableSpace E := borel E
private local instance : BorelSpace E := ⟨rfl⟩
private local instance : TopologicalSpace F.M := F.topology
private local instance : ChartedSpace H F.M := F.charted
private local instance : IsManifold I ∞ F.M := F.smooth
private local instance : SigmaCompactSpace F.M := F.sigmaCompact
private local instance : T2Space F.M := F.t2
private local instance : MeasurableSpace F.M := borel F.M
private local instance : BorelSpace F.M := ⟨rfl⟩

attribute [local instance] PointedRiemannianManifold.topology
  PointedRiemannianManifold.charted PointedRiemannianManifold.smooth
  PointedRiemannianManifold.t2 PointedRiemannianManifold.sigmaCompact

private local instance : MeasurableSpace P.M := borel P.M
private local instance : BorelSpace P.M := ⟨rfl⟩

local notation "U" => poleRescaledFlowSeq F hcar hreg b hbmem tau q hsigma
local notation "Y" => poleEndpointRescaledFlowSeq F hcar hreg b hbmem tau q hsigma

attribute [local instance] MeasureTheory.Measure.Subtype.measureSpace

namespace HalfLineMetricConvergenceData

theorem integral_poleEndpoint_redDensity_limit_residual_eq_zero_of_const_mass
    [ConnectedSpace P.M]
    (Phi : PointedCGHMaps Y P phi)
    (R : SmoothRiemannianMetric I P.M) (hR : RiemannianMetricComplete R)
    (bf : BumpFamily Phi) (hsrc : SourceIsSigmaCompact Phi) (htgt : TargetIsSigmaCompact Phi)
    (co : HalfLineMetricConvergenceData Phi R bf hsrc htgt)
    (hcomplete : MetricComplete
      ({ P with metric := co.gInf 0 } : PointedRiemannianManifold I))
    (hboundary : BoundarylessManifold I P.M)
    (kappa : ℕ → ℝ) (hF : ∀ i, IsAncientKappaSolution (kappa i) ((U).term i))
    (p : F.M) {a c A : ℝ} (ha : 1 < a)
    (hbase : ∀ i, redLength ((U).term i).S 0 p (q i) 1 ≤ A)
    (psi : ℕ → ℕ) (hpsi : StrictMono psi) (ellC : C(P.M × Ici (1 : ℝ), ℝ))
    (hconv : TendstoLocallyUniformly
      (fun k (z : P.M × Ici (1 : ℝ)) =>
        redLength ((U).term (phi (co.φ (psi k)))).S 0 p
          (Phi.map (co.φ (psi k)) z.1) z.2) ellC atTop)
    (ell : P.M × ℝ → ℝ)
    (hagree : ∀ (y : P.M) (t : ℝ) (ht : 1 ≤ t), ell (y, t) = ellC (y, ⟨t, ht⟩))
    (hlog : ∀ (x : P.M) (W : Set E), IsOpen W → IsCompact (closure W) →
      closure W ⊆ (extChartAt I x).target →
      ∀ v : ℝ × E → ℝ, ContDiff ℝ ∞ v → HasCompactSupport v →
        tsupport v ⊆ Ioo a c ×ˢ W → (∀ z, 0 ≤ v z) →
      let f := fun z : ℝ × E => ell ((extChartAt I x).symm z.2, z.1)
      let d := fun z => fderiv ℝ (fun y : E => f (z.1, y)) z.2
      let B := fun z => chartGradientBilin (co.gInf (1 - z.1)) x
        ((extChartAt I x).symm z.2)
      let ρ := fun z => chartDensity (co.gInf (1 - z.1)) x
        ((extChartAt I x).symm z.2)
      let S := fun z => metricScalarAt (co.gInf (1 - z.1)) ((extChartAt I x).symm z.2)
      0 ≤ ∫ z, ρ z *
        (((1 / 2 : ℝ) * B z (d z) (d z) - (1 / 2 : ℝ) * S z +
            ((Module.finrank ℝ E : ℝ) - f z) / (2 * z.1)) * v z +
          B z (d z) (fderiv ℝ (fun y => v (z.1, y)) z.2))
        ∂(volume : Measure ℝ).prod (modelHaar (E := E)))
    {a' c' : ℝ} (haa : a < a') (hac : a' ≤ c') (hcc : c' < c)
    (hcompleteOn : ∀ t ∈ Icc a' c', MetricComplete (I := I)
      ({ P with metric := co.gInf (1 - t) } : PointedRiemannianManifold (I := I)))
    (m : ℝ)
    (hmass : ∀ᵐ s : Ioo a' c', (∫ y,
      Real.exp (-ellC (y, (⟨(s : ℝ), (ha.le.trans haa.le).trans s.property.1.le⟩ : Ici (1 : ℝ))) -
        ((Module.finrank ℝ E : ℝ) / 2) * Real.log (s : ℝ) -
        ((Module.finrank ℝ E : ℝ) / 2) * Real.log (4 * Real.pi))
      ∂riemannianVolumeMeasure (I := I) (M := P.M) (co.gInf (1 - (s : ℝ)))) = m)
    (ψ : ℝ × P.M → ℝ)
    (hψ : ContMDiff ((𝓘(ℝ, ℝ)).prod I) 𝓘(ℝ, ℝ) 1 ψ)
    (hψc : HasCompactSupport ψ)
    (hψsupp : tsupport ψ ⊆ Ioo a' c' ×ˢ (univ : Set P.M)) :
    let g := fun t : ℝ => co.gInf (1 - t)
    let density := fun z : ℝ × P.M => Real.exp (-ell (z.2, z.1) -
      (Module.finrank ℝ E : ℝ) / 2 * Real.log z.1 -
      (Module.finrank ℝ E : ℝ) / 2 * Real.log (4 * Real.pi))
    let residual := fun (t : ℝ) (x : P.M) => density (t, x) *
      (deriv (fun s => ψ (s, x)) t +
        (g t).inner x (gradientFun (g t) (fun y => ell (y, t)) x)
          (gradientFun (g t) (fun y => ψ (t, y)) x))
    (∀ᵐ t ∂volume.restrict (Ioc a' c'),
      Integrable (residual t) (riemannianVolumeMeasure (I := I) (M := P.M) (g t))) ∧
      Integrable (fun t => ∫ x, residual t x
        ∂riemannianVolumeMeasure (I := I) (M := P.M) (g t))
        (volume.restrict (Ioc a' c')) ∧
      (∫ t in Ioc a' c', ∫ x, residual t x
        ∂riemannianVolumeMeasure (I := I) (M := P.M) (g t)) = 0 := by
  have ha' : 1 ≤ a' := ha.le.trans haa.le
  have hbaseSelected : ∀ᶠ k in atTop,
      redLength ((U).term (phi (co.φ k))).S 0 p (q (phi (co.φ k))) 1 ≤ A :=
    Eventually.of_forall fun k => hbase (phi (co.φ k))
  have hconvPointwise : ∀ y : P.M, ∀ t ∈ Icc a c,
      Tendsto (fun k => redLength ((U).term (phi (co.φ (psi k)))).S 0 p
        (Phi.map (co.φ (psi k)) y) t) atTop (𝓝 (ell (y, t))) := by
    intro y t ht
    have htOne : 1 ≤ t := ha.le.trans ht.1
    have hpt := hconv.tendstoLocallyUniformlyOn.tendsto_at
      (mem_univ (y, (⟨t, htOne⟩ : Ici (1 : ℝ))))
    rw [hagree y t htOne]
    exact hpt
  have hK : IsCompact (Prod.fst '' tsupport ψ) := hψc.image continuous_fst
  have hKac : Prod.fst '' tsupport ψ ⊆ Ioo a' c' := by
    rintro t ⟨q, hq, rfl⟩
    exact (hψsupp hq).1
  obtain ⟨η, hη, hηc, hηone, hηsupp, hηrange⟩ :=
    DifferentialGeometry.Analysis.exists_bump_compact hK isOpen_Ioo hKac
  have hηC1 : ContDiff ℝ 1 η := hη.of_le (by simp)
  have hηnonneg : ∀ t, 0 ≤ η t := fun t => (hηrange ⟨t, rfl⟩).1
  have hηoneOn : ∀ z ∈ tsupport ψ, η z.1 = 1 :=
    fun z hz => hηone.self_of_nhdsSet ⟨z, hz, rfl⟩
  let radii : ℕ → ℝ := fun n => (n : ℝ) + 1
  have hradii : Tendsto radii atTop atTop :=
    tendsto_atTop_mono (fun n : ℕ =>
      (show (n : ℝ) ≤ (n : ℝ) + 1 from le_add_of_nonneg_right zero_le_one))
      (tendsto_natCast_atTop_atTop (R := ℝ))
  have hqref : RiemannianMetricComplete (co.gInf (1 - a')) :=
    ⟨hcompleteOn a' ⟨le_rfl, hac⟩⟩
  have hagreeOn (s : Ioo a' c') (y : P.M) :
      ell (y, (s : ℝ)) = ellC (y, ⟨(s : ℝ), ha'.trans s.property.1.le⟩) :=
    hagree y s (ha'.trans s.property.1.le)
  have hcutoff := co.tendsto_integral_poleEndpoint_radialDistanceCutoff_residual_of_const_mass
    F hcar hreg b hbmem tau q hsigma Phi kappa hF p hbase psi hpsi ellC hconv
    ha' hac hcompleteOn ell hagreeOn m hmass P.basepoint η hηC1 hηsupp hradii
  exact co.integral_poleEndpoint_redDensity_limit_residual_eq_zero_of_radial_cutoff_limit
    F hcar hreg b hbmem tau q hsigma Phi R hR bf hsrc htgt
    hcomplete hboundary kappa hF p ha hbaseSelected psi hpsi.tendsto_atTop
    ell hconvPointwise hlog haa hac hcc ψ hψ hψc hψsupp
    η hηC1 hηc hηsupp hηnonneg hηoneOn (co.gInf (1 - a')) hqref P.basepoint
    hradii hcutoff.1

end HalfLineMetricConvergenceData

end DifferentialGeometry.CheegerGromovCompactness

end
