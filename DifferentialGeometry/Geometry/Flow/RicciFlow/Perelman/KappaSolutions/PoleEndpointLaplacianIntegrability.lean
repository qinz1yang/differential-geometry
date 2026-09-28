import DifferentialGeometry.Geometry.Flow.RicciFlow.Compactness.Fields.JointVolumeDensity
import DifferentialGeometry.Geometry.Flow.RicciFlow.Compactness.Fields.GradientCoefficients
import DifferentialGeometry.Geometry.Flow.RicciFlow.Compactness.Fields.SourceScalarContinuity
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.KappaSolutions.RegularPoleRescalings
import DifferentialGeometry.Analysis.Calculus.Derivative.LocallyLipschitz
import DifferentialGeometry.Analysis.Calculus.Derivative.WeakIdentification
import DifferentialGeometry.Geometry.Coordinates.Fields.ScalarDifferentiability
import DifferentialGeometry.Geometry.Operator.Gradient.NormSquared
import Mathlib.MeasureTheory.Function.LocallyIntegrable
import Mathlib.MeasureTheory.Group.Measure
import Mathlib.Analysis.Calculus.FDeriv.Measurable
import Mathlib.Analysis.Normed.Group.Bounded
import Mathlib.Analysis.Normed.Operator.BoundedLinearMaps
import Mathlib.MeasureTheory.Function.StronglyMeasurable.Lemmas
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.Topology.Algebra.MetricSpace.Lipschitz
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity

noncomputable section

open Filter MeasureTheory Set
open scoped Topology

namespace DifferentialGeometry.Analysis

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

private local instance covectorNormedAddCommGroup : NormedAddCommGroup (E →L[ℝ] ℝ) :=
  ContinuousLinearMap.toNormedAddCommGroup

private local instance covectorNormedSpace : NormedSpace ℝ (E →L[ℝ] ℝ) :=
  ContinuousLinearMap.toNormedSpace

private local instance covectorDualNormedAddCommGroup : NormedAddCommGroup ((E →L[ℝ] ℝ) →L[ℝ] ℝ) :=
  ContinuousLinearMap.toNormedAddCommGroup

private local instance covectorDualNormedSpace : NormedSpace ℝ ((E →L[ℝ] ℝ) →L[ℝ] ℝ) :=
  ContinuousLinearMap.toNormedSpace

private local instance covectorBilinNormedAddCommGroup :
    NormedAddCommGroup ((E →L[ℝ] ℝ) →L[ℝ] (E →L[ℝ] ℝ) →L[ℝ] ℝ) :=
  ContinuousLinearMap.toNormedAddCommGroup

private local instance covectorBilinNormedSpace :
    NormedSpace ℝ ((E →L[ℝ] ℝ) →L[ℝ] (E →L[ℝ] ℝ) →L[ℝ] ℝ) :=
  ContinuousLinearMap.toNormedSpace

private local instance timeCovectorNormedAddCommGroup : NormedAddCommGroup ((ℝ × E) →L[ℝ] ℝ) :=
  ContinuousLinearMap.toNormedAddCommGroup

private local instance timeCovectorNormedSpace : NormedSpace ℝ ((ℝ × E) →L[ℝ] ℝ) :=
  ContinuousLinearMap.toNormedSpace

private local instance projectionNormedAddCommGroup :
    NormedAddCommGroup (((ℝ × E) →L[ℝ] ℝ) →L[ℝ] (E →L[ℝ] ℝ)) :=
  ContinuousLinearMap.toNormedAddCommGroup

private local instance projectionNormedSpace :
    NormedSpace ℝ (((ℝ × E) →L[ℝ] ℝ) →L[ℝ] (E →L[ℝ] ℝ)) :=
  ContinuousLinearMap.toNormedSpace

private local instance timeDualNormedAddCommGroup :
    NormedAddCommGroup (((ℝ × E) →L[ℝ] ℝ) →L[ℝ] ℝ) :=
  ContinuousLinearMap.toNormedAddCommGroup

private local instance timeDualNormedSpace : NormedSpace ℝ (((ℝ × E) →L[ℝ] ℝ) →L[ℝ] ℝ) :=
  ContinuousLinearMap.toNormedSpace

private theorem weak_log_coefficients_measurable_bounded_on_compacts
    {Ω : Set (ℝ × E)} (hΩ : IsOpen Ω)
    {f : (ℝ × E) → ℝ} (hf : LocallyLipschitzOn Ω f)
    (rho R q : (ℝ × E) → ℝ)
    (B : (ℝ × E) → (E →L[ℝ] ℝ) →L[ℝ] (E →L[ℝ] ℝ) →L[ℝ] ℝ)
    (hrho : ContinuousOn rho Ω) (hR : ContinuousOn R Ω) (hq : ContinuousOn q Ω)
    (hB : ContinuousOn B Ω)
    (π : ((ℝ × E) →L[ℝ] ℝ) →L[ℝ] (E →L[ℝ] ℝ))
    (μ : Measure (ℝ × E)) :
    let d := fun z => π (fderiv ℝ f z)
    let b := fun z => rho z • ((B z (d z)).comp π)
    let c := fun z => rho z *
      ((1 / 2 : ℝ) * B z (d z) (d z) - (1 / 2 : ℝ) * R z + q z)
    (∀ v, AEStronglyMeasurable (fun z => b z v) (μ.restrict Ω)) ∧
      AEStronglyMeasurable c (μ.restrict Ω) ∧
      ∀ K : Set (ℝ × E), IsCompact K → K ⊆ Ω → ∃ M N : ℝ,
        (∀ᵐ z ∂μ.restrict K, ‖b z‖ ≤ M) ∧
        (∀ᵐ z ∂μ.restrict K, ‖c z‖ ≤ N) := by
  let d := fun z => π (fderiv ℝ f z)
  let b := fun z => rho z • ((B z (d z)).comp π)
  let c := fun z => rho z *
    ((1 / 2 : ℝ) * B z (d z) (d z) - (1 / 2 : ℝ) * R z + q z)
  change (∀ v, AEStronglyMeasurable (fun z => b z v) (μ.restrict Ω)) ∧
    AEStronglyMeasurable c (μ.restrict Ω) ∧
    ∀ K : Set (ℝ × E), IsCompact K → K ⊆ Ω → ∃ M N : ℝ,
      (∀ᵐ z ∂μ.restrict K, ‖b z‖ ≤ M) ∧
      (∀ᵐ z ∂μ.restrict K, ‖c z‖ ≤ N)
  have hdm : AEStronglyMeasurable d (μ.restrict Ω) :=
    π.continuous.comp_aestronglyMeasurable (measurable_fderiv ℝ f).aestronglyMeasurable
  have hrhom : AEStronglyMeasurable rho (μ.restrict Ω) :=
    hrho.aestronglyMeasurable hΩ.measurableSet
  have hRm : AEStronglyMeasurable R (μ.restrict Ω) :=
    hR.aestronglyMeasurable hΩ.measurableSet
  have hqm : AEStronglyMeasurable q (μ.restrict Ω) :=
    hq.aestronglyMeasurable hΩ.measurableSet
  have hBm : AEStronglyMeasurable B (μ.restrict Ω) :=
    hB.aestronglyMeasurable hΩ.measurableSet
  have hBdm : AEStronglyMeasurable (fun z => B z (d z)) (μ.restrict Ω) :=
    (isBoundedBilinearMap_apply (𝕜 := ℝ) (E := E →L[ℝ] ℝ)
      (F := (E →L[ℝ] ℝ) →L[ℝ] ℝ)).continuous.comp_aestronglyMeasurable
        (hBm.prodMk hdm)
  have hQm : AEStronglyMeasurable (fun z => B z (d z) (d z)) (μ.restrict Ω) :=
    (isBoundedBilinearMap_apply (𝕜 := ℝ) (E := E →L[ℝ] ℝ)
      (F := ℝ)).continuous.comp_aestronglyMeasurable (hBdm.prodMk hdm)
  refine ⟨?_, ?_, ?_⟩
  · intro v
    exact (hrhom.mul (hBdm.apply_continuousLinearMap (π v))).congr
      (Eventually.of_forall fun z => by
        simp only [b, smul_apply, ContinuousLinearMap.comp_apply, smul_eq_mul, Pi.mul_apply])
  · exact hrhom.mul (((hQm.const_mul (1 / 2 : ℝ)).sub (hRm.const_mul (1 / 2 : ℝ))).add hqm)
  · intro K hK hKΩ
    obtain ⟨L, hL, hKL, hLΩ⟩ := exists_compact_between hK hΩ hKΩ
    obtain ⟨C, hLip⟩ := (hf.mono hLΩ).exists_lipschitzOnWith_of_compact hL
    have hderiv (z : ℝ × E) (hz : z ∈ K) : ‖fderiv ℝ f z‖ ≤ (C : ℝ) :=
      norm_fderiv_le_of_lipschitzOn ℝ
        (mem_interior_iff_mem_nhds.mp (hKL hz)) hLip
    let D : ℝ := ‖π‖ * (C : ℝ)
    have hD : 0 ≤ D := mul_nonneg (norm_nonneg _) C.coe_nonneg
    have hd (z : ℝ × E) (hz : z ∈ K) : ‖d z‖ ≤ D :=
      π.le_opNorm_of_le (hderiv z hz)
    have hcoeff : ContinuousOn
        (fun z => ‖rho z‖ + ‖B z‖ + ‖R z‖ + ‖q z‖) K :=
      ((((hrho.mono hKΩ).norm.add (hB.mono hKΩ).norm).add
        (hR.mono hKΩ).norm).add (hq.mono hKΩ).norm)
    obtain ⟨A₀, hA₀⟩ := hK.exists_bound_of_continuousOn hcoeff
    let A : ℝ := max A₀ 0
    have hA : 0 ≤ A := le_max_right _ _
    have hbounds (z : ℝ × E) (hz : z ∈ K) :
        ‖rho z‖ ≤ A ∧ ‖B z‖ ≤ A ∧ ‖R z‖ ≤ A ∧ ‖q z‖ ≤ A := by
      have hsum : ‖‖rho z‖ + ‖B z‖ + ‖R z‖ + ‖q z‖‖ ≤ A :=
        (hA₀ z hz).trans (le_max_left A₀ 0)
      have hnonneg : 0 ≤ ‖rho z‖ + ‖B z‖ + ‖R z‖ + ‖q z‖ := by positivity
      rw [Real.norm_eq_abs, abs_of_nonneg hnonneg] at hsum
      refine ⟨?_, ?_, ?_, ?_⟩ <;>
        linarith only [hsum, norm_nonneg (rho z), norm_nonneg (B z),
          norm_nonneg (R z), norm_nonneg (q z)]
    have hBd (z : ℝ × E) (hz : z ∈ K) : ‖B z (d z)‖ ≤ A * D := by
      calc
        ‖B z (d z)‖ ≤ ‖B z‖ * ‖d z‖ := (B z).le_opNorm (d z)
        _ ≤ A * D := mul_le_mul (hbounds z hz).2.1 (hd z hz) (norm_nonneg _) hA
    have hQ (z : ℝ × E) (hz : z ∈ K) : ‖B z (d z) (d z)‖ ≤ A * D * D := by
      calc
        ‖B z (d z) (d z)‖ ≤ ‖B z (d z)‖ * ‖d z‖ :=
          (B z (d z)).le_opNorm (d z)
        _ ≤ A * D * D := mul_le_mul (hBd z hz) (hd z hz)
          (norm_nonneg _) (mul_nonneg hA hD)
    refine ⟨A * (A * D * ‖π‖), A * ((1 / 2 : ℝ) * (A * D * D) +
      (1 / 2 : ℝ) * A + A), ?_, ?_⟩
    · filter_upwards [ae_restrict_mem hK.measurableSet] with z hz
      have hcomp : ‖(B z (d z)).comp π‖ ≤ A * D * ‖π‖ :=
        ((B z (d z)).opNorm_comp_le π).trans
          (mul_le_mul_of_nonneg_right (hBd z hz) (norm_nonneg _))
      change ‖rho z • ((B z (d z)).comp π)‖ ≤ _
      rw [norm_smul]
      exact mul_le_mul (hbounds z hz).1 hcomp (norm_nonneg _) hA
    · filter_upwards [ae_restrict_mem hK.measurableSet] with z hz
      have hscalar :
          ‖(1 / 2 : ℝ) * B z (d z) (d z) - (1 / 2 : ℝ) * R z + q z‖ ≤
            (1 / 2 : ℝ) * (A * D * D) + (1 / 2 : ℝ) * A + A := by
        calc
          ‖(1 / 2 : ℝ) * B z (d z) (d z) - (1 / 2 : ℝ) * R z + q z‖ ≤
              ‖(1 / 2 : ℝ) * B z (d z) (d z) - (1 / 2 : ℝ) * R z‖ + ‖q z‖ :=
            norm_add_le _ _
          _ ≤ (‖(1 / 2 : ℝ) * B z (d z) (d z)‖ +
              ‖(1 / 2 : ℝ) * R z‖) + ‖q z‖ :=
            add_le_add (norm_sub_le _ _) le_rfl
          _ = (1 / 2 : ℝ) * ‖B z (d z) (d z)‖ +
              (1 / 2 : ℝ) * ‖R z‖ + ‖q z‖ := by norm_num [norm_mul]
          _ ≤ (1 / 2 : ℝ) * (A * D * D) + (1 / 2 : ℝ) * A + A :=
            add_le_add
              (add_le_add (mul_le_mul_of_nonneg_left (hQ z hz) (by norm_num))
                (mul_le_mul_of_nonneg_left (hbounds z hz).2.2.1 (by norm_num)))
              (hbounds z hz).2.2.2
      change ‖rho z * ((1 / 2 : ℝ) * B z (d z) (d z) -
        (1 / 2 : ℝ) * R z + q z)‖ ≤ _
      rw [norm_mul]
      exact mul_le_mul (hbounds z hz).1 hscalar (norm_nonneg _) hA

private theorem locallyIntegrableOn_weak_log_coefficient
    {Ω : Set (ℝ × E)} (hΩ : IsOpen Ω)
    {f : (ℝ × E) → ℝ} (hf : LocallyLipschitzOn Ω f)
    (rho R q : (ℝ × E) → ℝ)
    (B : (ℝ × E) → (E →L[ℝ] ℝ) →L[ℝ] (E →L[ℝ] ℝ) →L[ℝ] ℝ)
    (hrho : ContinuousOn rho Ω) (hR : ContinuousOn R Ω) (hq : ContinuousOn q Ω)
    (hB : ContinuousOn B Ω)
    (π : ((ℝ × E) →L[ℝ] ℝ) →L[ℝ] (E →L[ℝ] ℝ))
    (μ : Measure (ℝ × E)) [IsFiniteMeasureOnCompacts μ] :
    let d := fun z => π (fderiv ℝ f z)
    LocallyIntegrableOn
      (fun z => rho z * ((1 / 2 : ℝ) * B z (d z) (d z) - (1 / 2 : ℝ) * R z + q z))
      Ω μ := by
  let d := fun z => π (fderiv ℝ f z)
  let c := fun z => rho z *
    ((1 / 2 : ℝ) * B z (d z) (d z) - (1 / 2 : ℝ) * R z + q z)
  change LocallyIntegrableOn c Ω μ
  obtain ⟨_, hcm, hbound⟩ := weak_log_coefficients_measurable_bounded_on_compacts
    hΩ hf rho R q B hrho hR hq hB π μ
  apply (locallyIntegrableOn_iff hΩ.isLocallyClosed).mpr
  intro K hKΩ hK
  obtain ⟨_, N, _, hN⟩ := hbound K hK hKΩ
  exact IntegrableOn.of_bound hK.measure_lt_top
    (hcm.mono_measure (Measure.restrict_mono hKΩ le_rfl)) N hN

end DifferentialGeometry.Analysis

namespace DifferentialGeometry.CheegerGromovCompactness

open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Geometry.Operator
open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Tensor.Coordinates
open DifferentialGeometry.PDE.RicciFlow.Perelman
open DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions
open scoped ContDiff _root_.Manifold BigOperators

universe u uE uH

variable {E : Type uE} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]
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

private local instance covectorNormedAddCommGroup : NormedAddCommGroup (E →L[ℝ] ℝ) :=
  ContinuousLinearMap.toNormedAddCommGroup

private local instance covectorNormedSpace : NormedSpace ℝ (E →L[ℝ] ℝ) :=
  ContinuousLinearMap.toNormedSpace

private local instance covectorDualNormedAddCommGroup : NormedAddCommGroup ((E →L[ℝ] ℝ) →L[ℝ] ℝ) :=
  ContinuousLinearMap.toNormedAddCommGroup

private local instance covectorDualNormedSpace : NormedSpace ℝ ((E →L[ℝ] ℝ) →L[ℝ] ℝ) :=
  ContinuousLinearMap.toNormedSpace

private local instance covectorBilinNormedAddCommGroup :
    NormedAddCommGroup ((E →L[ℝ] ℝ) →L[ℝ] (E →L[ℝ] ℝ) →L[ℝ] ℝ) :=
  ContinuousLinearMap.toNormedAddCommGroup

private local instance covectorBilinNormedSpace :
    NormedSpace ℝ ((E →L[ℝ] ℝ) →L[ℝ] (E →L[ℝ] ℝ) →L[ℝ] ℝ) :=
  ContinuousLinearMap.toNormedSpace

private local instance timeCovectorNormedAddCommGroup : NormedAddCommGroup ((ℝ × E) →L[ℝ] ℝ) :=
  ContinuousLinearMap.toNormedAddCommGroup

private local instance timeCovectorNormedSpace : NormedSpace ℝ ((ℝ × E) →L[ℝ] ℝ) :=
  ContinuousLinearMap.toNormedSpace

private local instance projectionNormedAddCommGroup :
    NormedAddCommGroup (((ℝ × E) →L[ℝ] ℝ) →L[ℝ] (E →L[ℝ] ℝ)) :=
  ContinuousLinearMap.toNormedAddCommGroup

private local instance projectionNormedSpace :
    NormedSpace ℝ (((ℝ × E) →L[ℝ] ℝ) →L[ℝ] (E →L[ℝ] ℝ)) :=
  ContinuousLinearMap.toNormedSpace

private local instance timeDualNormedAddCommGroup :
    NormedAddCommGroup (((ℝ × E) →L[ℝ] ℝ) →L[ℝ] ℝ) :=
  ContinuousLinearMap.toNormedAddCommGroup

private local instance timeDualNormedSpace : NormedSpace ℝ (((ℝ × E) →L[ℝ] ℝ) →L[ℝ] ℝ) :=
  ContinuousLinearMap.toNormedSpace

omit [MeasurableSpace E] [BorelSpace E] [I.Boundaryless] in
private theorem continuousOn_chartInvGramOnE_of_chartGradientBilin
    (g : ℝ × E → SmoothRiemannianMetric I P.M) (a : P.M) {Ω : Set (ℝ × E)}
    (h : ContinuousOn (fun p => chartGradientBilin (g p) a ((extChartAt I a).symm p.2)) Ω)
    (i j : Fin (Module.finrank ℝ E)) :
    ContinuousOn (fun p => chartInvGramOnE (g p) a i j p.2) Ω := by
  classical
  let u : Fin (Module.finrank ℝ E) → E →L[ℝ] ℝ :=
    fun m => ((chartModelBasis E).coord m).toContinuousLinearMap
  have hu (m n : Fin (Module.finrank ℝ E)) :
      u m (chartModelBasis E n) = if n = m then 1 else 0 := by
    simp only [u, LinearMap.coe_toContinuousLinearMap', Module.Basis.coord_apply,
      Module.Basis.repr_self_apply]
  have hentry (p : ℝ × E) :
      chartGradientBilin (g p) a ((extChartAt I a).symm p.2) (u j) (u i) =
        chartInvGramOnE (g p) a i j p.2 := by
    rw [chartGradientBilin_apply]
    simp only [hu, mul_ite, mul_one, mul_zero, Finset.sum_ite_irrel,
      Finset.sum_const_zero, Finset.sum_ite_eq', Finset.mem_univ, ite_true,
      chartInvGramOnE_def]
  have hc := (h.clm_apply (g := fun _ => u j) continuousOn_const).clm_apply
    (g := fun _ => u i) continuousOn_const
  simpa only [hentry] using hc

omit [MeasurableSpace E] [BorelSpace E] in
private theorem continuousOn_poleEndpoint_chart_coefficients
    (Phi : PointedCGHMaps Y P phi) (R : SmoothRiemannianMetric I P.M)
    (bf : BumpFamily Phi) (hsrc : SourceIsSigmaCompact Phi) (htgt : TargetIsSigmaCompact Phi)
    (a : P.M)
    (k : ℕ) {J : Set ℝ} {V : Set E} (hJ : J ⊆ Ici 1)
    (hV : V ⊆ (extChartAt I a).target) :
    ContinuousOn
      (fun p : ℝ × E => chartDensityOnE (gSeqExt Phi R bf hsrc htgt k (1 - p.1)) a p.2)
      (J ×ˢ V) ∧
      ContinuousOn
        (fun p : ℝ × E =>
          chartGradientBilin (gSeqExt Phi R bf hsrc htgt k (1 - p.1)) a ((extChartAt I a).symm p.2))
        (J ×ˢ V) := by
  have hpair : ContinuousOn (fun p : ℝ × E => (1 - p.1, p.2)) (J ×ˢ V) :=
    (continuousOn_const.sub continuousOn_fst).prodMk continuousOn_snd
  have hpairMem : MapsTo (fun p : ℝ × E => (1 - p.1, p.2)) (J ×ˢ V)
      ((Y).D.carrier ×ˢ (extChartAt I a).target) := by
    intro p hp
    refine ⟨?_, hV hp.2⟩
    change 1 - p.1 ≤ 0
    exact sub_nonpos.mpr (mem_Ici.mp (hJ hp.1))
  constructor
  · have h := continuousOn_chartDensity_gSeqExt Phi R bf hsrc htgt k a
      (K := (extChartAt I a).target) Subset.rfl
    simpa only [chartDensityOnE, Function.comp_def] using h.comp hpair hpairMem
  · have h := continuousOn_smul_chartGradientBilin_gSeqExt Phi R bf hsrc htgt k a
      (K := (extChartAt I a).target) Subset.rfl (fun _ => (1 : ℝ)) continuousOn_const
    have hplain : ContinuousOn
        (fun p : ℝ × E => chartGradientBilin (gSeqExt Phi R bf hsrc htgt k p.1)
          a ((extChartAt I a).symm p.2))
        ((Y).D.carrier ×ˢ (extChartAt I a).target) := by
      simpa only [one_smul] using h
    simpa only [Function.comp_def] using hplain.comp hpair hpairMem

theorem eventually_locallyIntegrableOn_poleEndpoint_redLength_chart_laplacian_rhs
    (Phi : PointedCGHMaps Y P phi) (R : SmoothRiemannianMetric I P.M)
    (bf : BumpFamily Phi) (hsrc : SourceIsSigmaCompact Phi) (htgt : TargetIsSigmaCompact Phi)
    (p0 : F.M) (a : P.M) {K : Set P.M} (hK : IsCompact K)
    {μ : Measure E} [Measure.IsAddHaarMeasure μ] :
    ∀ᶠ k in atTop,
      let metric : ℝ → SmoothRiemannianMetric I P.M :=
        fun s => gSeqExt Phi R bf hsrc htgt k (1 - s)
      let ell : ℝ → P.M → ℝ :=
        fun s y => redLength ((U).term (phi k)).S 0 p0 (Phi.map k y) s
      let f : ℝ × E → ℝ := fun p => scalarOnE (I := I) a (ell p.1) p.2
      let RHS : ℝ × E → ℝ := fun p => chartDensityOnE (metric p.1) a p.2 *
        ((1 / 2 : ℝ) * normGradSqFun (metric p.1) (ell p.1) ((extChartAt I a).symm p.2) -
          (1 / 2 : ℝ) * ((U).term (phi k)).S.scalar (-p.1)
            (Phi.map k ((extChartAt I a).symm p.2)) +
          ((Module.finrank ℝ E : ℝ) - f p) / (2 * p.1))
      ∀ (J : Set ℝ) (V : Set E), IsOpen J → IsOpen V →
        J ⊆ Ioi 1 → V ⊆ (extChartAt I a).target →
        MapsTo (extChartAt I a).symm V K → LocallyLipschitzOn (J ×ˢ V) f →
        LocallyIntegrableOn RHS (J ×ˢ V) (volume.prod μ) := by
  have hscalar := Phi.eventually_continuousOn_scalar (fun k => k) tendsto_id
    (J := (Y).D.carrier) Subset.rfl hK
  filter_upwards [hscalar] with k hk
  intro metric ell f RHS J V hJ hV hJpos hVt hVK hlip
  let Ω := J ×ˢ V
  let rho : ℝ × E → ℝ := fun p => chartDensityOnE (metric p.1) a p.2
  let B : (ℝ × E) → (E →L[ℝ] ℝ) →L[ℝ] (E →L[ℝ] ℝ) →L[ℝ] ℝ :=
    fun p => chartGradientBilin (metric p.1) a ((extChartAt I a).symm p.2)
  let S : ℝ × E → ℝ := fun p =>
    ((U).term (phi k)).S.scalar (-p.1) (Phi.map k ((extChartAt I a).symm p.2))
  let qterm : ℝ × E → ℝ := fun p =>
    ((Module.finrank ℝ E : ℝ) - f p) / (2 * p.1)
  let π : ((ℝ × E) →L[ℝ] ℝ) →L[ℝ] (E →L[ℝ] ℝ) :=
    (ContinuousLinearMap.compL ℝ E (ℝ × E) ℝ).flip (ContinuousLinearMap.inr ℝ ℝ E)
  let dj : ℝ × E → E →L[ℝ] ℝ := fun p => π (fderiv ℝ f p)
  let c : ℝ × E → ℝ := fun p => rho p *
    ((1 / 2 : ℝ) * B p (dj p) (dj p) - (1 / 2 : ℝ) * S p + qterm p)
  have hΩ : IsOpen Ω := hJ.prod hV
  have htime {s : ℝ} (hs : s ∈ J) : 1 - s ∈ (Y).D.carrier := by
    change 1 - s ≤ 0
    exact sub_nonpos.mpr (le_of_lt (mem_Ioi.mp (hJpos hs)))
  obtain ⟨hrho, hB⟩ := continuousOn_poleEndpoint_chart_coefficients
    F hcar hreg b hbmem tau q hsigma Phi R bf hsrc htgt a k
    (fun _ hs => mem_Ici.mpr (le_of_lt (mem_Ioi.mp (hJpos hs)))) hVt
  have hS : ContinuousOn S Ω := by
    have hchart : ContinuousOn (fun p : ℝ × E => (extChartAt I a).symm p.2) Ω :=
      ((continuousOn_extChartAt_symm (I := I) a).mono hVt).comp
        continuousOn_snd (fun _ hp => hp.2)
    have hpull := hk.comp ((continuousOn_const.sub continuousOn_fst).prodMk hchart)
      (fun p hp => ⟨htime hp.1, hVK hp.2⟩)
    apply hpull.congr
    intro p _
    change metricScalarAt (((U).term (phi k)).S.base.metric (-p.1))
        (Phi.map k ((extChartAt I a).symm p.2)) =
      metricScalarAt (((Y).term (phi k)).S.base.metric (1 - p.1))
        (Phi.map k ((extChartAt I a).symm p.2))
    rw [poleEndpointRescaledFlowSeq_metric_eq_shift]
    have heq : 1 - p.1 - 1 = -p.1 := by ring
    rw [heq]
    rfl
  have hqterm : ContinuousOn qterm Ω := by
    apply (continuousOn_const.sub hlip.continuousOn).div
      (continuousOn_const.mul continuousOn_fst)
    intro p hp
    exact mul_ne_zero (by norm_num) (ne_of_gt (lt_trans zero_lt_one (mem_Ioi.mp (hJpos hp.1))))
  have hc : LocallyIntegrableOn c Ω (volume.prod μ) :=
    DifferentialGeometry.Analysis.locallyIntegrableOn_weak_log_coefficient
      hΩ hlip rho S qterm B hrho hS hqterm hB π (volume.prod μ)
  apply hc.congr
  filter_upwards [ae_restrict_of_ae (hlip.ae_differentiableAt_of_isOpen
    (μ := volume.prod μ) hΩ),
    ae_restrict_mem hΩ.measurableSet] with p hdiff hp
  have hjoint : DifferentiableAt ℝ f p := hdiff hp
  have hspatial : HasFDerivAt (fun z : E => f (p.1, z))
      ((fderiv ℝ f p).comp (ContinuousLinearMap.inr ℝ ℝ E)) p.2 :=
    HasFDerivAt.comp (𝕜 := ℝ) (g := f) (f := fun z : E => (p.1, z)) p.2
      hjoint.hasFDerivAt (hasFDerivAt_prodMk_right (𝕜 := ℝ) p.1 p.2)
  have hdf : DifferentiableAt ℝ (fun z => f (p.1, z)) p.2 :=
    hspatial.differentiableAt
  have hsource : (extChartAt I a).symm p.2 ∈ (chartAt H a).source := by
    simpa only [extChartAt_source] using (extChartAt I a).map_target (hVt hp.2)
  have hmd : MDifferentiableAt I 𝓘(ℝ, ℝ) (ell p.1)
      ((extChartAt I a).symm p.2) :=
    mdifferentiableAt_of_differentiableAt_scalarOnE (hVt hp.2) hdf
  have hds : fderiv ℝ (fun z => f (p.1, z)) p.2 = dj p := by
    simpa only [dj, π, ContinuousLinearMap.flip_apply, ContinuousLinearMap.compL_apply]
      using hspatial.fderiv
  have hgrad : normGradSqFun (metric p.1) (ell p.1)
      ((extChartAt I a).symm p.2) = B p (dj p) (dj p) := by
    rw [normGradSqFun_def,
      grad_norm_sq_eq_chartGradientBilin (metric p.1) a hmd hsource,
      (extChartAt I a).right_inv (hVt hp.2)]
    change B p (fderiv ℝ (fun z => f (p.1, z)) p.2)
      (fderiv ℝ (fun z => f (p.1, z)) p.2) = _
    rw [hds]
  change rho p * ((1 / 2 : ℝ) * B p (dj p) (dj p) - (1 / 2 : ℝ) * S p + qterm p) = _
  rw [← hgrad]

theorem locallyIntegrableOn_poleEndpoint_redLength_chart_laplacian_flux
    (Phi : PointedCGHMaps Y P phi) (R : SmoothRiemannianMetric I P.M)
    (bf : BumpFamily Phi) (hsrc : SourceIsSigmaCompact Phi) (htgt : TargetIsSigmaCompact Phi)
    (p0 : F.M) (a : P.M) (k : ℕ) {μ : Measure E} [Measure.IsAddHaarMeasure μ] :
    let metric : ℝ → SmoothRiemannianMetric I P.M :=
      fun s => gSeqExt Phi R bf hsrc htgt k (1 - s)
    let ell : ℝ → P.M → ℝ :=
      fun s y => redLength ((U).term (phi k)).S 0 p0 (Phi.map k y) s
    let f : ℝ × E → ℝ := fun p => scalarOnE (I := I) a (ell p.1) p.2
    ∀ {J : Set ℝ} {V : Set E}, IsOpen J → IsOpen V →
      J ⊆ Ici 1 → V ⊆ (extChartAt I a).target → LocallyLipschitzOn (J ×ˢ V) f →
      ∀ i j : Fin (Module.finrank ℝ E),
        LocallyIntegrableOn
          (fun p : ℝ × E =>
            (chartDensityOnE (metric p.1) a p.2 *
              chartInvGramOnE (metric p.1) a i j p.2) *
              fderiv ℝ (fun z => f (p.1, z)) p.2 (chartModelBasis E i))
          (J ×ˢ V) (volume.prod μ) := by
  intro metric ell f J V hJ hV hJpos hVt hlip i j
  classical
  let C : ℝ × E → ℝ := fun p => chartDensityOnE (metric p.1) a p.2 *
    chartInvGramOnE (metric p.1) a i j p.2
  obtain ⟨hrho, hB⟩ := continuousOn_poleEndpoint_chart_coefficients
    F hcar hreg b hbmem tau q hsigma Phi R bf hsrc htgt a k hJpos hVt
  have hC : ContinuousOn C (J ×ˢ V) :=
    hrho.mul (continuousOn_chartInvGramOnE_of_chartGradientBilin
      (fun p => metric p.1) a hB i j)
  have hd : LocallyIntegrableOn
      (fun p : ℝ × E => fderiv ℝ f p (0, chartModelBasis E i))
      (J ×ˢ V) (volume.prod μ) := by
    have h := (ContinuousLinearMap.apply ℝ ℝ (0, chartModelBasis E i)).locallyIntegrableOn_comp
      (hlip.locallyIntegrableOn_fderiv (μ := volume.prod μ) (hJ.prod hV))
    simpa only [Function.comp_def, ContinuousLinearMap.apply_apply] using h
  have hi : LocallyIntegrableOn
      (fun p : ℝ × E => C p * fderiv ℝ f p (0, chartModelBasis E i))
      (J ×ˢ V) (volume.prod μ) :=
    hd.continuousOn_mul hC (hJ.prod hV).isLocallyClosed
  apply hi.congr
  filter_upwards [ae_restrict_of_ae (hlip.ae_differentiableAt_of_isOpen
    (μ := volume.prod μ) (hJ.prod hV)), ae_restrict_mem (hJ.prod hV).measurableSet]
    with p hp hpJV
  have hjoint : DifferentiableAt ℝ f p := hp hpJV
  have hs : fderiv ℝ (fun z => f (p.1, z)) p.2 =
      (fderiv ℝ f p).comp (ContinuousLinearMap.inr ℝ ℝ E) :=
    (HasFDerivAt.comp (𝕜 := ℝ) (g := f) (f := fun z : E => (p.1, z)) p.2
      hjoint.hasFDerivAt (hasFDerivAt_prodMk_right (𝕜 := ℝ) p.1 p.2)).fderiv
  rw [hs]
  rfl

end DifferentialGeometry.CheegerGromovCompactness
