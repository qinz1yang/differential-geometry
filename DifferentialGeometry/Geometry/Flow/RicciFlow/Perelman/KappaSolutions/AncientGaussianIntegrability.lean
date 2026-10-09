import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.KappaSolutions.AncientReducedDensityGaussian
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.KappaSolutions.AncientVolumeComparison
import DifferentialGeometry.Analysis.Integration.Measure.Riemannian.GaussianTail

noncomputable section

open Set MeasureTheory
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.CheegerGromovCompactness
open DifferentialGeometry.Geometry.Riemannian.BonnetMyers
open DifferentialGeometry.Analysis.Measure
open DifferentialGeometry.Integral.Measure
open scoped ContDiff Manifold ENNReal

namespace DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions

open CanonicalNeighborhood

universe u uE uH

variable {E : Type uE} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [CompleteSpace E]
  {H : Type uH} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  (F : PointedFlowData.{u, uE, uH} (I := I) ancientTimeInterval)

local instance terminalFiniteTopology : TopologicalSpace F.M := F.topology
local instance terminalFiniteCharted : ChartedSpace H F.M := F.charted
local instance terminalFiniteSmooth : IsManifold I ∞ F.M := F.smooth
local instance terminalFiniteT2 : T2Space F.M := F.t2
local instance terminalFiniteSigma : SigmaCompactSpace F.M := F.sigmaCompact
private local instance : MeasurableSpace F.M := borel F.M
private local instance : BorelSpace F.M := ⟨rfl⟩

theorem ancient_lintegral_terminal_gaussian_ne_top
    {kappa : ℝ} (hF : IsAncientKappaSolution kappa F) (p : F.M)
    {s decay A : ℝ} (hs : s ≤ 0) (hdecay : 0 < decay) (hA : 0 ≤ A) :
    (∫⁻ q, ENNReal.ofReal (A * Real.exp
      (-decay * (riemannianEDistOf (I := I) (F.S.base.metric 0) p q).toReal ^ 2))
      ∂riemannianVolumeMeasure (I := I) (M := F.M) (F.S.base.metric s)) ≠ (⊤ : ENNReal) := by
  let : ConnectedSpace F.M := hF.connected
  let : TopologicalSpace.MetrizableSpace F.M := Manifold.metrizableSpace I F.M
  let : PseudoMetricSpace F.M := TopologicalSpace.pseudoMetrizableSpacePseudoMetric F.M
  have hdim' : Module.finrank ℝ E ≠ 0 := by
    intro hzero
    obtain ⟨t, ht, x, hx⟩ := hF.notFlat
    have hb := ancientKappa_rmNormLeScalar_finrank F hF t ht x
    rw [hzero, Nat.cast_zero] at hb
    norm_num at hb
    have hn : 0 ≤ F.rmNormSq (I := I) t x := by
      simpa only [PointedFlowData.rmNormSq, SolutionOn.family] using
        DifferentialGeometry.Tensor0SBundle.normSq0S_nonneg
          (I := I) (F.S.base.metric t) x 4 (F.S.base.rm04 t x)
    have hz : Real.sqrt (F.rmNormSq (I := I) t x) = 0 :=
      le_antisymm hb (Real.sqrt_nonneg _)
    exact hx ((Real.sqrt_eq_zero hn).mp hz)
  let : NeZero (Module.finrank ℝ E) := ⟨hdim'⟩
  obtain ⟨K, hK, hvol⟩ := exists_ancientKappa_volumeMeasure_le_exp F hF
  have hmeasure := hvol s 0 hs le_rfl
  let f : F.M → ENNReal := fun q => ENNReal.ofReal (A * Real.exp
    (-decay * (riemannianEDistOf (I := I) (F.S.base.metric 0) p q).toReal ^ 2))
  have hmono := MeasureTheory.lintegral_mono' hmeasure (le_refl f)
  rw [MeasureTheory.lintegral_smul_measure] at hmono
  have hcomplete : RiemannianMetricComplete (I := I) (F.S.base.metric 0) :=
    ⟨hF.complete 0 (by simp [ancientTimeInterval_carrier])⟩
  have hRic : RicciBoundedBelow (I := I) (F.S.base.metric 0) 0 := by
    intro x v
    rw [zero_mul, ← metricRicciAt_apply_eq_ricciTensor]
    apply metricRicciAt_nonnegative_of_curvatureOperator_nonnegative
    apply (metricAlgebraicCurvatureTensorAt_mem_curvatureOperatorNonnegativeCone_iff
      (F.S.base.metric 0) x).mpr
    intro n c a b
    simpa only [SolutionFamily.rm04, metricRm04StandardAt_apply, metricRm04_apply] using
      hF.nonnegativeCurvatureOperator 0 (by simp [ancientTimeInterval_carrier]) x n c a b
  have hgauss := lintegral_gaussian_riemannianEDistOf_le
    (F.S.base.metric 0) hcomplete p hdecay hRic 0
  have hgauss' : (∫⁻ q, ENNReal.ofReal (Real.exp
      (-decay * (riemannianEDistOf (I := I) (F.S.base.metric 0) p q).toReal ^ 2))
      ∂riemannianVolumeMeasure (I := I) (M := F.M) (F.S.base.metric 0)) ≤
      (((volume : Measure (EuclideanSpace ℝ (Fin (Module.finrank ℝ E)))).toSphere univ *
        ENNReal.ofReal ((Module.finrank ℝ E : ℝ)⁻¹)) * gaussianTail
          (Module.finrank ℝ E) decay 0) := by
    have htailset : {q : F.M | (0 : ℝ) ≤
        (riemannianEDistOf (I := I) (F.S.base.metric 0) p q).toReal} = Set.univ := by
      ext q
      simp only [mem_ofPred_eq, mem_univ, iff_true]
      exact ENNReal.toReal_nonneg
    rw [← MeasureTheory.setLIntegral_univ, ← htailset]
    simpa only [Nat.cast_zero] using hgauss
  have hAint : (∫⁻ q, f q ∂riemannianVolumeMeasure (I := I) (M := F.M)
      (F.S.base.metric 0)) ≤ ENNReal.ofReal A *
      ((((volume : Measure (EuclideanSpace ℝ (Fin (Module.finrank ℝ E)))).toSphere univ *
        ENNReal.ofReal ((Module.finrank ℝ E : ℝ)⁻¹)) * gaussianTail
          (Module.finrank ℝ E) decay 0)) := by
    have hf : (fun q => f q) = (fun q => ENNReal.ofReal A * ENNReal.ofReal
        (Real.exp (-decay * (riemannianEDistOf (I := I) (F.S.base.metric 0) p q).toReal ^ 2))) := by
      funext q
      dsimp only [f]
      rw [ENNReal.ofReal_mul hA]
    rw [hf]
    rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    exact mul_le_mul_of_nonneg_left hgauss' (by positivity)
  have htail : gaussianTail (Module.finrank ℝ E) decay 0 ≠ (⊤ : ENNReal) := by
    dsimp [gaussianTail]
    exact (summable_gaussianShell (Module.finrank ℝ E) hdecay).tsum_ofReal_ne_top
  have hfinite : ENNReal.ofReal A *
      (((volume : Measure (EuclideanSpace ℝ (Fin (Module.finrank ℝ E)))).toSphere univ *
        ENNReal.ofReal ((Module.finrank ℝ E : ℝ)⁻¹)) * gaussianTail
          (Module.finrank ℝ E) decay 0 ) ≠ (⊤ : ENNReal) := by
    apply ENNReal.mul_ne_top ENNReal.ofReal_ne_top
    exact ENNReal.mul_ne_top
      (ENNReal.mul_ne_top (measure_ne_top (volume.toSphere) univ) ENNReal.ofReal_ne_top) htail
  have hc : ENNReal.ofReal (Real.sqrt (Real.exp (2 * K * (0 - s)) ^ Module.finrank ℝ E)) ≠ (⊤ : ENNReal) := ENNReal.ofReal_ne_top
  have hfinite' := ENNReal.mul_ne_top hc hfinite
  apply ne_top_of_le_ne_top hfinite'
  calc
    _ ≤ ENNReal.ofReal (Real.sqrt (Real.exp (2 * K * (0 - s)) ^ Module.finrank ℝ E)) •
        (∫⁻ q, f q ∂riemannianVolumeMeasure (I := I) (M := F.M) (F.S.base.metric 0)) := hmono
    _ ≤ ENNReal.ofReal (Real.sqrt (Real.exp (2 * K * (0 - s)) ^ Module.finrank ℝ E)) •
        (ENNReal.ofReal A *
          (((volume : Measure (EuclideanSpace ℝ (Fin (Module.finrank ℝ E)))).toSphere univ *
            ENNReal.ofReal ((Module.finrank ℝ E : ℝ)⁻¹)) * gaussianTail
              (Module.finrank ℝ E) decay 0)) := by
      exact smul_le_smul_left _ hAint
    _ = _ := by simp only [smul_eq_mul]


end DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions
