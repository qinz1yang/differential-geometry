import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.KappaSolutions.PoleEndpointDensityGlobalLipschitz
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.KappaSolutions.PoleEndpointDensityGlobalIntegrability
import DifferentialGeometry.Analysis.Parabolic.WeakEquation.GradientIntegralLinearity
import DifferentialGeometry.Geometry.Metric.Distance.RadialCutoff.CompactBounds
import DifferentialGeometry.Geometry.Metric.Distance.RadialCutoff.SpacetimeLipschitz
import DifferentialGeometry.Geometry.Comparison.HopfRinow.Proper
import DifferentialGeometry.Topology.Manifold.ZeroDimensional
import DifferentialGeometry.Geometry.Coordinates.Fields.Scalar
import DifferentialGeometry.Geometry.Measure.ManifoldRademacher
import Mathlib.Analysis.Normed.Group.Uniform
import Mathlib.Topology.Algebra.Support


noncomputable section

namespace DifferentialGeometry.Geometry.Riemannian

open Set Function _root_.Manifold
open scoped _root_.Manifold ContDiff _root_.Topology

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] {H : Type*} [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [T2Space M] [T2Space (TangentBundle I M)] [SigmaCompactSpace M]
  [PreconnectedSpace M]

private theorem radial_test_data
    (g : SmoothRiemannianMetric I M) (hg : RiemannianMetricComplete g)
    (p : M) {R : ℝ} (hR : 0 < R)
    {a c a' c' : ℝ} {η : ℝ → ℝ}
    (hη : ContDiff ℝ 1 η) (hηc : HasCompactSupport η)
    (hηsupp : tsupport η ⊆ Ioo a' c') :
    let φ := fun z : ℝ × M => η z.1 * radialDistanceCutoff g p R z.2
    (∀ α : M,
      LocallyLipschitzOn (Ioo a c ×ˢ (extChartAt I α).target)
        (fun z : ℝ × E => φ (z.1, (extChartAt I α).symm z.2))) ∧
    HasCompactSupport φ ∧
    tsupport φ ⊆ Ioo a' c' ×ˢ (univ : Set M) := by
  let φ := fun z : ℝ × M => η z.1 * radialDistanceCutoff g p R z.2
  change (∀ α : M,
      LocallyLipschitzOn (Ioo a c ×ˢ (extChartAt I α).target)
        (fun z : ℝ × E => φ (z.1, (extChartAt I α).symm z.2))) ∧
    HasCompactSupport φ ∧ tsupport φ ⊆ Ioo a' c' ×ˢ (univ : Set M)
  have hball : IsCompact (riemannianClosedBallOf g p R) := by
    by_cases hdim : Module.finrank ℝ E = 0
    · let _ : Subsingleton M := subsingleton_of_preconnected_of_finrank_eq_zero I hdim
      exact (Set.toFinite _).isCompact
    · let _ : NeZero (Module.finrank ℝ E) := ⟨hdim⟩
      exact hg.closedEBall_isCompact p R
  have hφsupport : tsupport φ ⊆ tsupport η ×ˢ riemannianClosedBallOf g p R := by
    apply closure_minimal _ ((isClosed_tsupport η).prod hball.isClosed)
    rintro ⟨t, x⟩ hx
    have hηx : η t ≠ 0 := by
      intro hzero
      exact hx (by simp only [φ, hzero, zero_mul])
    refine ⟨subset_tsupport η hηx, ?_⟩
    by_contra hout
    exact hx (by
      change η t * radialDistanceCutoff g p R x = 0
      rw [radialDistanceCutoff_eq_zero_of_not_mem_closedBall g p hR hout, mul_zero])
  have hφc : HasCompactSupport φ :=
    (hηc.isCompact.prod hball).of_isClosed_subset (isClosed_tsupport φ) hφsupport
  refine ⟨?_, hφc, ?_⟩
  · intro α
    exact locallyLipschitzOn_mul_radialDistanceCutoff_comp_extChartAt_symm
      g p α hR hη.locallyLipschitz.locallyLipschitzOn
  · intro z hz
    exact ⟨hηsupp (hφsupport hz).1, mem_univ _⟩

private theorem signed_radial_test_data
    (g : SmoothRiemannianMetric I M) (hg : RiemannianMetricComplete g)
    (p : M) {R : ℝ} (hR : 0 < R) (d e : ℝ)
    {a c a' c' : ℝ} {η : ℝ → ℝ}
    (hη : ContDiff ℝ 1 η) (hηc : HasCompactSupport η)
    (hηsupp : tsupport η ⊆ Ioo a' c')
    {ψ : ℝ × M → ℝ}
    (hψ : ContMDiff (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) 1 ψ)
    (hψc : HasCompactSupport ψ)
    (hψsupp : tsupport ψ ⊆ Ioo a' c' ×ˢ (univ : Set M)) :
    let φ := fun z : ℝ × M =>
      d * (η z.1 * radialDistanceCutoff g p R z.2) + e * ψ z
    (∀ α : M,
      LocallyLipschitzOn (Ioo a c ×ˢ (extChartAt I α).target)
        (fun z : ℝ × E => φ (z.1, (extChartAt I α).symm z.2))) ∧
    HasCompactSupport φ ∧
    tsupport φ ⊆ Ioo a' c' ×ˢ (univ : Set M) := by
  let φ₀ := fun z : ℝ × M => η z.1 * radialDistanceCutoff g p R z.2
  obtain ⟨hφ₀LL, hφ₀c, hφ₀supp⟩ :=
    radial_test_data g hg p hR (a := a) (c := c) hη hηc hηsupp
  have hdc : HasCompactSupport (fun z => d * φ₀ z) := by
    change HasCompactSupport ((fun _ : ℝ × M => d) * φ₀)
    exact hφ₀c.mul_left
  have hec : HasCompactSupport (fun z => e * ψ z) := by
    change HasCompactSupport ((fun _ : ℝ × M => e) * ψ)
    exact hψc.mul_left
  have hdsupp : tsupport (fun z => d * φ₀ z) ⊆ Ioo a' c' ×ˢ (univ : Set M) :=
    tsupport_mul_subset_right.trans hφ₀supp
  have hesupp : tsupport (fun z => e * ψ z) ⊆ Ioo a' c' ×ˢ (univ : Set M) :=
    tsupport_mul_subset_right.trans hψsupp
  have hψLL (α : M) :
      LocallyLipschitzOn (Ioo a c ×ˢ (extChartAt I α).target)
        (fun z : ℝ × E => ψ (z.1, (extChartAt I α).symm z.2)) := by
    have hfst :
        ContMDiffOn (𝓘(ℝ, ℝ).prod 𝓘(ℝ, E)) 𝓘(ℝ, ℝ) 1
          (fun z : ℝ × E => z.1) (univ ×ˢ (extChartAt I α).target) := contMDiffOn_fst
    have hsnd :
        ContMDiffOn (𝓘(ℝ, ℝ).prod 𝓘(ℝ, E)) I 1
          (fun z : ℝ × E => (extChartAt I α).symm z.2)
          (univ ×ˢ (extChartAt I α).target) := by
      refine (contMDiffOn_extChartAt_symm (I := I) α).comp contMDiffOn_snd ?_
      exact fun _ hz => hz.2
    have hcomp := hψ.comp_contMDiffOn (hfst.prodMk hsnd)
    have hraw : ContDiffOn ℝ 1
        (fun z : ℝ × E => ψ (z.1, (extChartAt I α).symm z.2))
        (univ ×ˢ (extChartAt I α).target) := by
      rw [← contMDiffOn_iff_contDiffOn, modelWithCornersSelf_prod,
        ← chartedSpaceSelf_prod]
      exact hcomp
    intro z hz
    have hat : ContDiffAt ℝ 1
        (fun z : ℝ × E => ψ (z.1, (extChartAt I α).symm z.2)) z :=
      hraw.contDiffAt
        ((isOpen_univ.prod (isOpen_extChartAt_target (I := I) α)).mem_nhds
          ⟨mem_univ _, hz.2⟩)
    obtain ⟨K, V, hV, hK⟩ := hat.exists_lipschitzOnWith
    exact ⟨K, V, mem_nhdsWithin_of_mem_nhds hV, hK⟩
  have hscale (r : ℝ) : LocallyLipschitz (fun t : ℝ => r * t) :=
    (contDiff_const.mul contDiff_id : ContDiff ℝ 1 (fun t : ℝ => r * t)).locallyLipschitz
  refine ⟨?_, ?_, ?_⟩
  · intro α
    have hd : LocallyLipschitzOn (Ioo a c ×ˢ (extChartAt I α).target)
        (fun z : ℝ × E => d * φ₀ (z.1, (extChartAt I α).symm z.2)) :=
      (hscale d).locallyLipschitzOn.comp (hφ₀LL α) (mapsTo_univ _ _)
    have he : LocallyLipschitzOn (Ioo a c ×ˢ (extChartAt I α).target)
        (fun z : ℝ × E => e * ψ (z.1, (extChartAt I α).symm z.2)) :=
      (hscale e).locallyLipschitzOn.comp (hψLL α) (mapsTo_univ _ _)
    exact hd.add he
  · exact hdc.add hec
  · exact (tsupport_add (fun z => d * φ₀ z) (fun z => e * ψ z)).trans
      (union_subset hdsupp hesupp)

end DifferentialGeometry.Geometry.Riemannian


namespace DifferentialGeometry.Geometry.Operator

open MeasureTheory
open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Geometry.Riemannian
open scoped _root_.Manifold ContDiff

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [T2Space M] [SigmaCompactSpace M]

private local instance : MeasurableSpace M := borel M
private local instance : BorelSpace M := ⟨rfl⟩

private theorem radial_product_slice_differentiability
    [PreconnectedSpace M]
    (g : ℝ → SmoothRiemannianMetric I M) (qref : SmoothRiemannianMetric I M)
    (z : M) {r : ℝ} (hr : 0 < r) {η : ℝ → ℝ} (hη : ContDiff ℝ 1 η) :
    (∀ t x, DifferentiableAt ℝ (fun s => η s * radialDistanceCutoff qref z r x) t) ∧
      (∀ t, ∀ᵐ x ∂riemannianVolumeMeasure (I := I) (M := M) (g t),
        MDifferentiableAt I 𝓘(ℝ)
          (fun y => η t * radialDistanceCutoff qref z r y) x) := by
  refine ⟨fun t x => (hη.differentiable one_ne_zero t).mul_const _, ?_⟩
  intro t
  have hχ : ∀ᵐ x ∂riemannianVolumeMeasure (I := I) (M := M) (g t),
      MDifferentiableAt I 𝓘(ℝ) (radialDistanceCutoff qref z r) x :=
    ae_iff.mpr (DifferentialGeometry.Geometry.Measure.riemannianVolumeMeasure_nondiff_null
      (g t) (radialDistanceCutoff qref z r)
      (fun α => locallyLipschitzOn_radialDistanceCutoff_comp_extChartAt_symm qref z α hr))
  filter_upwards [hχ] with x hx
  exact hx.const_smul (η t)

end DifferentialGeometry.Geometry.Operator


namespace DifferentialGeometry.CheegerGromovCompactness

open Filter _root_.MeasureTheory Set
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

theorem integral_poleEndpoint_redDensity_limit_residual_eq_zero_of_radial_cutoff_limit
    [ConnectedSpace P.M]
    (Phi : PointedCGHMaps Y P phi)
    (R : SmoothRiemannianMetric I P.M) (hR : RiemannianMetricComplete R)
    (bf : BumpFamily Phi) (hsrc : SourceIsSigmaCompact Phi) (htgt : TargetIsSigmaCompact Phi)
    (co : HalfLineMetricConvergenceData Phi R bf hsrc htgt)
    (hcomplete : MetricComplete
      ({ P with metric := co.gInf 0 } : PointedRiemannianManifold I))
    (hboundary : BoundarylessManifold I P.M)
    (kappa : ℕ → ℝ) (hF : ∀ i, IsAncientKappaSolution (kappa i) ((U).term i))
    (p : F.M) {a c A : ℝ}
    (ha : 1 < a)
    (hbase : ∀ᶠ k in atTop, redLength ((U).term (phi (co.φ k))).S 0
      p (q (phi (co.φ k))) 1 ≤ A)
    (rho : ℕ → ℕ) (hrho : Tendsto rho atTop atTop)
    (ell : P.M × ℝ → ℝ)
    (hconv : ∀ y : P.M, ∀ t ∈ Icc a c,
      Tendsto (fun k => redLength ((U).term (phi (co.φ (rho k)))).S 0 p
        (Phi.map (co.φ (rho k)) y) t) atTop (𝓝 (ell (y, t))))
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
    (ψ : ℝ × P.M → ℝ)
    (hψ : ContMDiff ((𝓘(ℝ, ℝ)).prod I) 𝓘(ℝ, ℝ) 1 ψ)
    (hψc : HasCompactSupport ψ)
    (hψsupp : tsupport ψ ⊆ Ioo a' c' ×ˢ (univ : Set P.M))
    (η : ℝ → ℝ) (hη : ContDiff ℝ 1 η) (hηc : HasCompactSupport η)
    (hηsupp : tsupport η ⊆ Ioo a' c') (hηnonneg : ∀ t, 0 ≤ η t)
    (hηone : ∀ z ∈ tsupport ψ, η z.1 = 1)
    (qref : SmoothRiemannianMetric I P.M) (hqref : RiemannianMetricComplete qref)
    (zref : P.M) {ι : Type*} {l : Filter ι} [l.NeBot]
    {radii : ι → ℝ} (hradii : Tendsto radii l atTop)
    (hcutoff :
      let g := fun t : ℝ => co.gInf (1 - t)
      let density := fun z : ℝ × P.M => Real.exp (-ell (z.2, z.1) -
        (Module.finrank ℝ E : ℝ) / 2 * Real.log z.1 -
        (Module.finrank ℝ E : ℝ) / 2 * Real.log (4 * Real.pi))
      Tendsto (fun i => ∫ t in Ioc a' c', ∫ x,
        density (t, x) *
          (deriv (fun s => η s * radialDistanceCutoff qref zref (radii i) x) t +
            (g t).inner x (gradientFun (g t) (fun y => ell (y, t)) x)
              (gradientFun (g t)
                (fun y => η t * radialDistanceCutoff qref zref (radii i) y) x))
        ∂riemannianVolumeMeasure (I := I) (M := P.M) (g t)) l (𝓝 0)) :
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
  classical
  let _ : TopologicalSpace.MetrizableSpace P.M := Manifold.metrizableSpace I P.M
  let _ : T2Space (TangentBundle I P.M) := inferInstance
  let g := fun t : ℝ => co.gInf (1 - t)
  let density := fun z : ℝ × P.M => Real.exp (-ell (z.2, z.1) -
    (Module.finrank ℝ E : ℝ) / 2 * Real.log z.1 -
    (Module.finrank ℝ E : ℝ) / 2 * Real.log (4 * Real.pi))
  let X : (t : ℝ) → (x : P.M) → TangentSpace I x :=
    fun t x => gradientFun (g t) (fun y => ell (y, t)) x
  let μ : Measure ℝ := volume.restrict (Ioc a' c')
  let ν := fun t => riemannianVolumeMeasure (I := I) (M := P.M) (g t)
  let residual := fun (v : ℝ × P.M → ℝ) (t : ℝ) (x : P.M) => density (t, x) *
    (deriv (fun s => v (s, x)) t +
      (g t).inner x (X t x) (gradientFun (g t) (fun y => v (t, y)) x))
  let L := fun v : ℝ × P.M → ℝ => ∫ t, ∫ x, residual v t x ∂ν t ∂μ
  let χ := fun (i : ι) (z : ℝ × P.M) =>
    η z.1 * radialDistanceCutoff qref zref (radii i) z.2
  have hψint := co.integrable_poleEndpoint_redDensity_limit_residual_of_contMDiff
    F hcar hreg b hbmem tau q hsigma Phi R hR bf hsrc htgt
    kappa hF p ha hbase rho hrho ell hconv haa hcc ψ hψ hψc hψsupp
  change (∀ᵐ t ∂μ, Integrable (residual ψ t) (ν t)) ∧
    Integrable (fun t => ∫ x, residual ψ t x ∂ν t) μ at hψint
  refine ⟨hψint.1, hψint.2, ?_⟩
  change L ψ = 0
  have hψt : ∀ᵐ t ∂μ, ∀ᵐ x ∂ν t, DifferentiableAt ℝ (fun s => ψ (s, x)) t := by
    exact ae_of_all μ fun t => ae_of_all (ν t) fun x =>
      ((contMDiff_iff_contDiff.mp
        (hψ.comp (contMDiff_id.prodMk contMDiff_const))).differentiable
          one_ne_zero).differentiableAt
  have hψx : ∀ᵐ t ∂μ, ∀ᵐ x ∂ν t,
      MDifferentiableAt I 𝓘(ℝ) (fun y => ψ (t, y)) x := by
    exact ae_of_all μ fun t => ae_of_all (ν t) fun x =>
      (hψ.comp (contMDiff_const.prodMk contMDiff_id)).mdifferentiableAt one_ne_zero
  have hpos : ∀ᶠ i in l, 0 < radii i := hradii.eventually (eventually_gt_atTop 0)
  obtain ⟨C, _, hdom⟩ := exists_eventually_abs_le_mul_radialDistanceCutoff qref zref
    hψ.continuous hψc hηnonneg hηone hradii
  have hscaledLimit : Tendsto (fun i => C * L (χ i)) l (𝓝 0) := by
    simpa only [mul_zero] using hcutoff.const_mul C
  have hbounds : ∀ᶠ i in l, -(C * L (χ i)) ≤ L ψ ∧ L ψ ≤ C * L (χ i) := by
    filter_upwards [hpos, hdom] with i hi hdi
    have hχdata := radial_test_data qref hqref zref hi (a := a) (c := c) hη hηc hηsupp
    have hχint := co.integrable_poleEndpoint_redDensity_limit_residual
      F hcar hreg b hbmem tau q hsigma Phi R hR bf hsrc htgt
      kappa hF p ha hbase rho hrho ell hconv haa hcc (χ i)
      hχdata.1 hχdata.2.1 hχdata.2.2
    change (∀ᵐ t ∂μ, Integrable (residual (χ i) t) (ν t)) ∧
      Integrable (fun t => ∫ x, residual (χ i) t x ∂ν t) μ at hχint
    have hχt : ∀ᵐ t ∂μ, ∀ᵐ x ∂ν t,
        DifferentiableAt ℝ (fun s => χ i (s, x)) t :=
      ae_of_all μ fun t => ae_of_all (ν t) fun x => by
        change DifferentiableAt ℝ
          (fun s => η s * radialDistanceCutoff qref zref (radii i) x) t
        exact (hη.differentiable one_ne_zero t).mul_const _
    have hχx : ∀ᵐ t ∂μ, ∀ᵐ x ∂ν t,
        MDifferentiableAt I 𝓘(ℝ) (fun y => χ i (t, y)) x :=
      ae_of_all μ fun t => (radial_product_slice_differentiability g qref zref hi hη).2 t
    have hlinear (d e : ℝ) : L (d • χ i + e • ψ) = d * L (χ i) + e * L ψ := by
      have hd := integrable_and_integral_integral_parabolic_test_residual_const_mul
        μ ν g density X d hχint.1 hχint.2
      have he := integrable_and_integral_integral_parabolic_test_residual_const_mul
        μ ν g density X e hψint.1 hψint.2
      have hdt : ∀ᵐ t ∂μ, ∀ᵐ x ∂ν t,
          DifferentiableAt ℝ (fun s => (d • χ i) (s, x)) t := by
        filter_upwards [hχt] with t ht
        filter_upwards [ht] with x hx
        exact hx.const_mul d
      have het : ∀ᵐ t ∂μ, ∀ᵐ x ∂ν t,
          DifferentiableAt ℝ (fun s => (e • ψ) (s, x)) t := by
        filter_upwards [hψt] with t ht
        filter_upwards [ht] with x hx
        exact hx.const_mul e
      have hdx : ∀ᵐ t ∂μ, ∀ᵐ x ∂ν t,
          MDifferentiableAt I 𝓘(ℝ) (fun y => (d • χ i) (t, y)) x := by
        filter_upwards [hχx] with t ht
        filter_upwards [ht] with x hx
        exact hx.const_smul d
      have hex : ∀ᵐ t ∂μ, ∀ᵐ x ∂ν t,
          MDifferentiableAt I 𝓘(ℝ) (fun y => (e • ψ) (t, y)) x := by
        filter_upwards [hψx] with t ht
        filter_upwards [ht] with x hx
        exact hx.const_smul e
      have hadd := integrable_and_integral_integral_parabolic_test_residual_add
        μ ν g density X hdt het hdx hex hd.1 he.1 hd.2.1 he.2.1
      exact hadd.2.2.trans (congrArg₂ (fun x y : ℝ => x + y) hd.2.2 he.2.2)
    have hnonneg (e : ℝ) (he : ∀ q, 0 ≤ C * χ i q + e * ψ q) :
        0 ≤ C * L (χ i) + e * L ψ := by
      have hdata := signed_radial_test_data qref hqref zref hi C e (a := a) (c := c)
        hη hηc hηsupp hψ hψc hψsupp
      have hp :=
        co.integral_poleEndpoint_redDensity_limit_subsolution_of_chart_logarithmic_inequality
        F hcar hreg b hbmem tau q hsigma Phi R hR bf hsrc htgt
        hcomplete hboundary kappa hF p ha hbase rho hrho ell hconv hlog
        haa hac hcc (C • χ i + e • ψ) hdata.1 hdata.2.1 hdata.2.2 he
      have hpzero : 0 ≤ L (C • χ i + e • ψ) := hp.2.2
      rw [hlinear C e] at hpzero
      exact hpzero
    have hplus := hnonneg 1 (fun q => by
      have hb := (abs_le.mp (hdi q)).1
      dsimp only [χ]
      linarith)
    have hminus := hnonneg (-1) (fun q => by
      have hb := (abs_le.mp (hdi q)).2
      dsimp only [χ]
      linarith)
    constructor <;> linarith
  exact le_antisymm
    (ge_of_tendsto hscaledLimit (hbounds.mono fun _ hi => hi.2))
    (le_of_tendsto (by simpa only [neg_zero] using hscaledLimit.neg)
      (hbounds.mono fun _ hi => hi.1))

end HalfLineMetricConvergenceData

end DifferentialGeometry.CheegerGromovCompactness

end
