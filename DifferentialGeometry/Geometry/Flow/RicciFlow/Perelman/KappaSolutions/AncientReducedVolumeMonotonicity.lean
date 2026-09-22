import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.ModelWitness
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.KappaSolutions.ReducedVolumeNormalization
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.LGeometry.ReducedVolume.Monotonicity
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.StandardSolution.ReducedVolumeMonotonicity
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.KappaSolutions.NonnegativeCurvatureScalarNorm
import Mathlib.Analysis.SpecialFunctions.Gaussian.FourierTransform
import Mathlib.MeasureTheory.Group.Integral


set_option autoImplicit false
noncomputable section

namespace DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions

open Filter
open DifferentialGeometry.Geometry
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Tensor0SBundle
open DifferentialGeometry.CheegerGromovCompactness
open CanonicalNeighborhood
open scoped _root_.Manifold ContDiff _root_.Topology

universe u uE uH

section RegularBase

variable {E : Type uE} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [CompleteSpace E]
  {H : Type uH} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  (F : PointedFlowData.{u, uE, uH} (I := I) ancientTimeInterval)

local instance ancientReducedVolumeTopology : TopologicalSpace F.M := F.topology
local instance ancientReducedVolumeCharted : ChartedSpace H F.M := F.charted
local instance ancientReducedVolumeSmooth : IsManifold I ∞ F.M := F.smooth
local instance ancientReducedVolumeC1 : IsManifold I 1 F.M := IsManifold.of_le (n := ∞) (by decide)
local instance ancientReducedVolumeT2 : T2Space F.M := F.t2
local instance ancientReducedVolumeTangentT2 : T2Space (TangentBundle I F.M) := F.t2TangentBundle
local instance ancientReducedVolumeSigma : SigmaCompactSpace F.M := F.sigmaCompact


theorem not_Icc_subset_ancientTimeInterval_regular
    {T : ℝ} (hT : T ∉ ancientTimeInterval.regular) {tau : ℝ} (htau : 0 ≤ tau) :
    ¬ (Set.Icc (T - tau) T ⊆ ancientTimeInterval.regular) := by
  intro hsub
  exact hT (hsub ⟨by linarith, le_rfl⟩)


theorem not_ancientTimeInterval_zero_mem_regular :
    (0 : ℝ) ∉ ancientTimeInterval.regular := by
  simp only [ancientTimeInterval_regular, Set.mem_Iio, lt_self_iff_false, not_false_eq_true]


omit [I.Boundaryless] in
private theorem exists_rmNormSq_le_of_isAncientKappaSolution
    {kappa C : ℝ} (hF : IsAncientKappaSolution kappa F)
    (hC : PointedFlowScalarBounded (I := I) F C)
    {a b : ℝ} (hb : b ≤ 0) :
    ∃ K : ℝ, ∀ t ∈ Set.Icc a b, ∀ z : F.M,
      normSq0S (I := I) (F.S.base.metric t) z 4 (F.S.base.rm04 t z) ≤ K := by
  refine ⟨((Module.finrank ℝ E : ℝ) ^ 2 * C) ^ 2, ?_⟩
  intro t ht z
  have htc : t ∈ ancientTimeInterval.carrier := by
    rw [ancientTimeInterval_carrier]
    exact ht.2.trans hb
  have hnonnegC : 0 ≤ C := (hC t htc z).1.trans (hC t htc z).2
  have hop : metricAlgebraicCurvatureTensorAt (I := I) (M := F.M) (F.S.base.metric t) z ∈
      algebraicCurvatureOperatorNonnegativeCone (I := I) (M := F.M) := by
    apply (metricAlgebraicCurvatureTensorAt_mem_curvatureOperatorNonnegativeCone_iff
      (F.S.base.metric t) z).mpr
    intro n c a b
    simpa only [SolutionFamily.rm04, metricRm04StandardAt_apply, metricRm04_apply] using
      hF.nonnegativeCurvatureOperator t htc z n c a b
  have hsqrt := sqrt_metricRm_normSq_le_finrank_sq_mul_scalar (I := I) (F.S.base.metric t) z hop
  have hscalar : metricScalarAt (I := I) (F.S.base.metric t) z ≤ C := (hC t htc z).2
  have hn2 : 0 ≤ (Module.finrank ℝ E : ℝ) ^ 2 := sq_nonneg _
  have hs := hsqrt.trans (mul_le_mul_of_nonneg_left hscalar hn2)
  exact (Real.sqrt_le_left (mul_nonneg hn2 hnonnegC)).mp hs


theorem ancient_reducedVolume_antitone_of_regular_base
    [NeZero (Module.finrank ℝ E)]
    {kappa : ℝ} (hF : IsAncientKappaSolution kappa F) (p : F.M)
    {T : ℝ} (hT : T ∈ ancientTimeInterval.regular) :
    AntitoneOn (intrinsicReducedVolume F.S T p) (Set.Ioi 0) := by
  have hTneg : T < 0 := by simpa only [ancientTimeInterval_regular, Set.mem_Iio] using hT
  let _ : ConnectedSpace F.M := hF.connected
  have hcomplete : RiemannianMetricComplete (I := I) (F.S.base.metric T) :=
    ⟨hF.complete T (by rw [ancientTimeInterval_carrier]; exact hTneg.le)⟩
  obtain ⟨C, hC⟩ := hF.globalScalarBound
  intro (tau₁ : ℝ) (h₁ : tau₁ ∈ Set.Ioi 0) (tau₂ : ℝ) (h₂ : tau₂ ∈ Set.Ioi 0)
    (h₁₂ : tau₁ ≤ tau₂)
  have hslab : Set.Icc (T - tau₂) T ⊆ ancientTimeInterval.regular := by
    intro t ht
    simp only [ancientTimeInterval_regular, Set.mem_Iio]
    exact ht.2.trans_lt hTneg
  have h := DifferentialGeometry.PDE.RicciFlow.Perelman.redVolume_anti_of_rm
    (I := I) (M := F.M) (D := ancientTimeInterval)
    F.S F.isSolution T hcomplete p
    (fun sigma _ _ => exists_rmNormSq_le_of_isAncientKappaSolution F hF hC hTneg.le)
    h₁ h₁₂ hslab
  exact h

end RegularBase

section TerminalExtension

variable {E : Type uE} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [CompleteSpace E]
  {H : Type uH} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  (F : PointedFlowData.{u, uE, uH} (I := I) ancientTimeInterval)

attribute [local instance]
  ancientReducedVolumeTopology
  ancientReducedVolumeCharted
  ancientReducedVolumeSmooth
  ancientReducedVolumeC1
  ancientReducedVolumeT2
  ancientReducedVolumeTangentT2
  ancientReducedVolumeSigma


theorem ancient_reducedVolume_antitone_of_terminal_extension
    [NeZero (Module.finrank ℝ E)]
    {kappa : ℝ} (hF : IsAncientKappaSolution kappa F) (p : F.M)
    (D' : RealTimeInterval) (hcover : Set.Iic 0 ⊆ D'.regular)
    (S' : SolutionOn (I := I) (M := F.M) D')
    (hbase : S'.base = F.S.base) (hS' : IsSolutionOn (I := I) S') :
    AntitoneOn (intrinsicReducedVolume F.S 0 p) (Set.Ioi 0) := by
  let _ : ConnectedSpace F.M := hF.connected
  let : TopologicalSpace.MetrizableSpace F.M :=
    Manifold.metrizableSpace I F.M
  let : PseudoMetricSpace F.M :=
    TopologicalSpace.pseudoMetrizableSpacePseudoMetric F.M
  have h0 : (0 : ℝ) ∈ ancientTimeInterval.carrier := by
    change (0 : ℝ) ≤ 0
    exact le_rfl
  have hcomplete : RiemannianMetricComplete (I := I) (F.S.base.metric 0) :=
    ⟨hF.complete 0 h0⟩
  obtain ⟨C, hC⟩ := hF.globalScalarBound
  intro (tau₁ : ℝ) (h₁ : tau₁ ∈ Set.Ioi 0) (tau₂ : ℝ) (h₂ : tau₂ ∈ Set.Ioi 0)
    (h₁₂ : tau₁ ≤ tau₂)
  have hslab : Set.Icc (0 - tau₂) 0 ⊆ D'.regular := by
    intro t ht
    exact hcover ht.2
  have h := DifferentialGeometry.PDE.RicciFlow.Perelman.redVolume_anti_of_rm_Ico_of_base_eq
    (I := I) (M := F.M) (D := ancientTimeInterval) (D' := D')
    F.S S' hbase hS' 0 p hcomplete
    (fun sigma _ _ => exists_rmNormSq_le_of_isAncientKappaSolution F hF hC le_rfl)
    h₁ h₁₂ hslab
  exact h


theorem ancient_reducedVolume_antitone_of_exists_terminal_extension
    [NeZero (Module.finrank ℝ E)]
    {kappa : ℝ} (hF : IsAncientKappaSolution kappa F) (p : F.M)
    (hext : ∃ (D' : RealTimeInterval) (S' : SolutionOn (I := I) (M := F.M) D'),
      Set.Iic 0 ⊆ D'.regular ∧ S'.base = F.S.base ∧ IsSolutionOn (I := I) S') :
    AntitoneOn (intrinsicReducedVolume F.S 0 p) (Set.Ioi 0) := by
  obtain ⟨D', S', hcover, hbase, hS'⟩ := hext
  exact ancient_reducedVolume_antitone_of_terminal_extension F hF p D' hcover S' hbase hS'


theorem exists_interval_Iic_subset_regular :
    ∃ D' : RealTimeInterval, Set.Iic (0 : ℝ) ⊆ D'.regular :=
  ⟨RealTimeInterval.infiniteOpen 1 0 one_pos, fun t ht => by
    change t < 1
    exact lt_of_le_of_lt ht one_pos⟩


section GaussianDensity

theorem euclidean_gaussian_density_integral
    (n : ℕ) (tau : ℝ) (htau : 0 < tau) :
    ∫ x : EuclideanSpace ℝ (Fin n), Real.exp (-(‖x‖ ^ 2) / (4 * tau)) =
      (4 * Real.pi * tau) ^ ((n : ℝ) / 2) := by
  have hb : 0 < 1 / (4 * tau) := by positivity
  calc
    ∫ x : EuclideanSpace ℝ (Fin n), Real.exp (-(‖x‖ ^ 2) / (4 * tau)) =
        ∫ x : EuclideanSpace ℝ (Fin n),
          Real.exp (-(1 / (4 * tau)) * ‖x‖ ^ 2) := by
      refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
      ring_nf
    _ = (Real.pi / (1 / (4 * tau))) ^
        (Module.finrank ℝ (EuclideanSpace ℝ (Fin n)) / 2 : ℝ) :=
      GaussianFourier.integral_rexp_neg_mul_sq_norm hb
    _ = (4 * Real.pi * tau) ^ ((n : ℝ) / 2) := by
      simp
      field_simp

theorem euclidean_gaussian_reducedDensity_integral_eq_one
    (n : ℕ) (tau : ℝ) (htau : 0 < tau) (p : EuclideanSpace ℝ (Fin n)) :
    (4 * Real.pi * tau) ^ (-(n : ℝ) / 2) *
        ∫ x : EuclideanSpace ℝ (Fin n), Real.exp (-(‖x - p‖ ^ 2) / (4 * tau)) = 1 := by
  have htrans :
      ∫ x : EuclideanSpace ℝ (Fin n), Real.exp (-(‖x - p‖ ^ 2) / (4 * tau)) =
        ∫ x : EuclideanSpace ℝ (Fin n), Real.exp (-(‖x‖ ^ 2) / (4 * tau)) := by
    rw [← MeasureTheory.integral_add_left_eq_self
      (fun x : EuclideanSpace ℝ (Fin n) => Real.exp (-(‖x‖ ^ 2) / (4 * tau))) (-p)]
    refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
    simp only [neg_add_eq_sub]
  rw [htrans, euclidean_gaussian_density_integral n tau htau,
    ← Real.rpow_add (by positivity : (0 : ℝ) < 4 * Real.pi * tau)]
  rw [show -(n : ℝ) / 2 + (n : ℝ) / 2 = 0 by ring]
  exact Real.rpow_zero _

end GaussianDensity

end TerminalExtension


end DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions
