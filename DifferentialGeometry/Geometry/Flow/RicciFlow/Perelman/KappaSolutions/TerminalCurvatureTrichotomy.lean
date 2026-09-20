import DifferentialGeometry.Geometry.Flow.RicciFlow.DimensionThree.ClosedRankTrichotomy
import DifferentialGeometry.Geometry.Flow.RicciFlow.DimensionThree.ClosedKernel
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.KappaSolutions.TerminalSurfaceProductBasepoint
import DifferentialGeometry.Geometry.Curvature.DimensionThree.CurvatureOperatorEigenvalues
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.KappaSolutions.TerminalSurfaceProduct
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.KappaSolutions.HarnackLimit
import DifferentialGeometry.Geometry.Curvature.DimensionThree.CurvatureOperator.Positivity
import DifferentialGeometry.Geometry.Curvature.Riemann.SectionalCurvature


set_option autoImplicit false

noncomputable section

namespace DifferentialGeometry.PDE.RicciFlow
open DifferentialGeometry.Geometry.Curvature DifferentialGeometry.Geometry.Curvature.DimensionThree
open DifferentialGeometry.Topology.Morse Perelman.KappaSolutions
open scoped _root_.Manifold ContDiff

variable {H : Type*} [TopologicalSpace H]
  {I : ModelWithCorners ℝ (MorseModel 3) H} [I.Boundaryless]
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [T2Space M]
  [SigmaCompactSpace M] [ConnectedSpace M]

private theorem terminal_curvature_trichotomy_of_complete_metric
    {D : RealTimeInterval} (S : SolutionOn (I := I) (M := M) D) (hS : IsSolutionOn S)
    {a b : ℝ} (hab : a < b) (hslab : Set.Icc a b ⊆ D.carrier)
    (hreg : Set.Ioo a b ⊆ D.regular)
    (hR : ∀ t ∈ Set.Icc a b, ∀ x,
      metricAlgebraicCurvatureTensorAt (S.family.metric t) x ∈
        algebraicCurvatureOperatorNonnegativeCone (I := I) (M := M))
    (hg : RiemannianMetricComplete (S.family.metric b)) :
    (∀ x, metricRm04At (S.family.metric b) x = 0) ∨
      HasCurvatureSurfaceProductSplitting (S.family.metric b) ∨
        (∀ x, CurvatureOperatorPositiveAt (S.family.metric b) x) := by
  have hdim : Module.finrank ℝ (MorseModel 3) = 3 := by simp [MorseModel]
  have htri := curvatureOperatorImageAt_finrank_trichotomy_at_right_endpoint
    S hS hdim hab hslab hreg hR
  have hne (x : M) : Module.finrank ℝ (curvatureOperatorImageAt (S.family.metric b) x
      (metricAlgebraicCurvatureTensorAt (S.family.metric b) x)) ≠ 2 := by
    rcases htri with h | h | h <;> rw [h x] <;> norm_num
  have hnull (x : M) (v : TangentSpace I x [⋀^Fin 2]→L[ℝ] ℝ)
      (hv : curvatureOperatorEndomorphismAt (S.family.metric b) x
        (metricAlgebraicCurvatureTensorAt (S.family.metric b) x) v = 0) :
      curvatureOperatorReactionEndomorphism3
        (curvatureOperatorEndomorphismAt (S.family.metric b) x
          (metricAlgebraicCurvatureTensorAt (S.family.metric b) x)).toLinearMap v = 0 := by
    have htwo : Module.finrank ℝ (TangentSpace I x [⋀^Fin 2]→L[ℝ] ℝ) = 3 := by
      rw [ContinuousAlternatingMap.finrank_continuousAlternatingMap]
      change (Module.finrank ℝ (MorseModel 3)).choose 2 = 3
      rw [hdim]
      norm_num
    apply curvatureOperatorReactionEndomorphism3_eq_zero_of_mem_ker_of_finrank_range_ne_two
      htwo _ _ hv
    rw [← curvatureOperatorImageAt_eq_range]
    exact hne x
  have hp (x : M) := curvatureOperatorEndomorphismAt_inner_nonneg_of_mem_nonnegativeCone
    hdim (S.family.metric b) x (metricAlgebraicCurvatureTensorAt (S.family.metric b) x)
    (hR b ⟨hab.le, le_rfl⟩ x)
  have hconst := curvatureOperatorImageAt_finrank_eq_at_right_endpoint
    S hS hdim hab hslab hreg hR
  have hparallel := curvatureOperatorKernelAt_parallel_at_right_endpoint
    S hS hdim hab hslab hreg hR
  have h := curvatureOperator_time_slice_rank_trichotomy_of_complete_metric_nonnegative_reaction_constant_rank_parallel_kernel
    (S.family.metric b) hg hp hnull hconst hparallel
  rcases h with hflat | hsplit | hpos
  · exact Or.inl (fun x => metricRm04At_eq_zero_of_curvatureOperatorEndomorphismAt_eq_zero
      (S.family.metric b) x hdim (hflat.1 x))
  · exact Or.inr (Or.inl hsplit.2)
  · refine Or.inr (Or.inr (fun x => ?_))
    apply curvatureOperatorPositiveAt_of_leastCurvatureOperatorEigenvalueAt_pos
      (S.family.metric b) x hdim
    exact leastCurvatureOperatorEigenvalueAt_pos_of_image_finrank_eq_three
      (S.family.metric b) x hdim (metricAlgebraicCurvatureTensorAt (S.family.metric b) x)
      (hR b ⟨hab.le, le_rfl⟩ x) (hpos.1 x)

end DifferentialGeometry.PDE.RicciFlow

namespace DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions

open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Geometry.Riemannian
open DifferentialGeometry.Geometry.Riemannian.Topology
open DifferentialGeometry.CheegerGromovCompactness
open CanonicalNeighborhood
open scoped _root_.Manifold ContDiff

universe u uE uH

variable {E : Type uE} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [CompleteSpace E]
  {H : Type uH} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {D : RealTimeInterval} (F : PointedFlowData.{u, uE, uH} (I := I) D)

local instance terminalTrichotomyTopology : TopologicalSpace F.M := F.topology
local instance terminalTrichotomyCharted : ChartedSpace H F.M := F.charted
local instance terminalTrichotomySmooth : IsManifold I ∞ F.M := F.smooth
local instance terminalTrichotomyC1 : IsManifold I 1 F.M :=
  IsManifold.of_le (I := I) (M := F.M) (n := ∞) (by decide)
local instance terminalTrichotomyT2 : T2Space F.M := F.t2
local instance terminalTrichotomySigma : SigmaCompactSpace F.M := F.sigmaCompact


local instance terminalTrichotomyInhabited : Inhabited F.M := ⟨F.basepoint⟩


local instance terminalTrichotomyLocallyPathConnected :
    LocallyPathConnectedSpace F.M := by
  let _ : LocallyPathConnectedSpace H :=
    I.toHomeomorph.isOpenEmbedding.locallyPathConnectedSpace
  exact ChartedSpace.locallyPathConnectedSpace H F.M


local instance terminalTrichotomySemilocallySimplyConnected :
    SemilocallySimplyConnectedSpace F.M :=
  manifold_semilocallySimplyConnectedSpace (I := I) (M := F.M)


open DifferentialGeometry.Geometry.Curvature.DimensionThree
open DifferentialGeometry.Topology.Morse

attribute [-instance] DifferentialGeometry.Tensor0SBundle.tangentSpaceNormedAddCommGroup
  DifferentialGeometry.Tensor0SBundle.tangentSpaceNormedSpace in
theorem klim_terminal_curvature_trichotomy {kappa : ℝ} (hK : KLim (I := I) kappa F)
    (hdim : Module.finrank ℝ E = 3) :
    DifferentialGeometry.Geometry.HasPositiveSectionalCurvature (I := I) (F.S.base.metric 0) ∨
      (∀ x : F.M, F.rmNormSq (I := I) 0 x = 0) ∨
      Nonempty (TerminalSurfaceProduct (I := I) (F.S.base.metric 0)) := by
  let _ : ConnectedSpace F.M := hK.connected
  let e : E ≃L[ℝ] MorseModel 3 :=
    (Module.finBasisOfFinrankEq ℝ E hdim).equivFun.toContinuousLinearEquiv
  let J := I.transContinuousLinearEquiv e
  let Phi := ContinuousLinearEquiv.toTransContinuousLinearEquiv (n := ∞) I F.M e
  let U : SolutionOn (I := J) (M := F.M) D := F.S.pullback Phi.symm
  have hU : IsSolutionOn U := F.isSolution.pullback F.S Phi.symm
  let _ : IsManifold J 1 F.M := IsManifold.of_le (n := ∞) (by decide)
  have hslab : Set.Icc (-1 : ℝ) 0 ⊆ D.carrier := by
    rw [hK.carrier_eq]
    exact fun _ ht => ht.2
  have hreg : Set.Ioo (-1 : ℝ) 0 ⊆ D.regular := by
    rw [hK.regular_eq]
    exact fun _ ht => ht.2
  have hcone (t : ℝ) (ht : t ∈ Set.Icc (-1 : ℝ) 0) (x : F.M) :
      metricAlgebraicCurvatureTensorAt (F.S.base.metric t) x ∈
        algebraicCurvatureOperatorNonnegativeCone (I := I) (M := F.M) := by
    apply mem_algebraicCurvatureOperatorNonnegativeCone.mpr
    intro n c v w
    have h := hK.nonnegativeCurvatureOperator t (hslab ht) x n c v w
    simpa only [algebraicCurvatureOperatorQuadraticEval, metricAlgebraicCurvatureTensorAt,
      tensor04StandardAt, SolutionFamily.rm04, metricRm04_apply] using h
  have hconeU (t : ℝ) (ht : t ∈ Set.Icc (-1 : ℝ) 0) (x : F.M) :
      metricAlgebraicCurvatureTensorAt (U.base.metric t) x ∈
        algebraicCurvatureOperatorNonnegativeCone (I := J) (M := F.M) := by
    apply (metricAlgebraicCurvatureTensorAt_mem_curvatureOperatorNonnegativeCone_iff _ x).mpr
    intro n c v w
    change 0 ≤ ∑ i, ∑ j, c i * c j * metricRm04StandardAt
      (Diffeomorph.pullbackMetricCross (F.S.base.metric t) Phi.symm) x (v i) (w i) (w j) (v j)
    simp_rw [metricRm04Standard_pullbackCross]
    exact (metricAlgebraicCurvatureTensorAt_mem_curvatureOperatorNonnegativeCone_iff _ x).mp
      (hcone t ht x) n c _ _
  have hg : RiemannianMetricComplete (U.base.metric 0) :=
    RiemannianMetricComplete.pullbackCross (F.S.base.metric 0) Phi.symm
      ⟨hK.complete 0 (hslab (by norm_num))⟩
  have hcurv (x : F.M) (v w z u : TangentSpace I x) :
      metricRm04StandardAt (U.base.metric 0) x (e v) (e w) (e z) (e u) =
        metricRm04StandardAt (F.S.base.metric 0) x v w z u := by
    have h := metricRm04Standard_pullbackCross (F.S.base.metric 0) Phi.symm x
      (e v) (e w) (e z) (e u)
    change _ = metricRm04StandardAt (F.S.base.metric 0) x
      (mfderiv J I id x (e v)) (mfderiv J I id x (e w))
      (mfderiv J I id x (e z)) (mfderiv J I id x (e u)) at h
    rw [show J = I.transContinuousLinearEquiv e from rfl,
      DifferentialGeometry.Manifold.mfderiv_id_transContinuousLinearEquiv] at h
    change metricRm04StandardAt (U.base.metric 0) x (e v) (e w) (e z) (e u) =
      metricRm04StandardAt (F.S.base.metric 0) x (e.symm (e v)) (e.symm (e w))
        (e.symm (e z)) (e.symm (e u)) at h
    erw [e.symm_apply_apply, e.symm_apply_apply, e.symm_apply_apply, e.symm_apply_apply] at h
    exact h
  obtain hflat | hsplit | hpos := terminal_curvature_trichotomy_of_complete_metric U hU
    (by norm_num : (-1 : ℝ) < 0) hslab hreg hconeU hg
  · have hflat' : ∀ x, metricRm04At (U.base.metric 0) x = 0 := hflat
    refine Or.inr (Or.inl (fun x => ?_))
    apply (DifferentialGeometry.Tensor0SBundle.normSq0S_eq_zero_iff _ x 4 _).mpr
    apply ContinuousMultilinearMap.ext
    intro v
    change (metricRm04At (F.S.base.metric 0) x) v = 0
    have hz := hcurv x (v 0) (v 1) (v 2) (v 3)
    have hvec : vec4 (v 0) (v 1) (v 2) (v 3) = v := by
      funext i
      fin_cases i <;> rfl
    simpa only [metricRm04StandardAt, tensor04StandardAt, hflat' x,
      zero_apply, hvec, SolutionFamily.rm04, metricRm04_apply] using hz.symm
  · have hp := nonempty_terminalSurfaceProduct_of_morseModel_hasCurvatureSurfaceProductSplitting
      e (F.S.base.metric 0) hsplit
    exact Or.inr (Or.inr ((nonempty_terminalSurfaceProduct_iff_basepoint (F.S.base.metric 0)
      (Classical.choice (inferInstance : Nonempty F.M)) F.basepoint).mp hp))
  · refine Or.inl (fun x v w hvw => ?_)
    have hi (v w : E) : (U.base.metric 0).inner x (e v) (e w) =
        (F.S.base.metric 0).inner x v w := by
      exact ((F.S.base.metric 0).transContinuousLinearEquiv_inner e x (e v) (e w)).trans
        (congrArg₂ (fun (v w : E) => (F.S.base.metric 0).inner x v w) (e.symm_apply_apply v) (e.symm_apply_apply w))
    have hgram : 0 < (U.base.metric 0).inner x (e v) (e v) *
        (U.base.metric 0).inner x (e w) (e w) -
          ((U.base.metric 0).inner x (e v) (e w)) ^ 2 := by
      erw [hi, hi, hi]
      exact DifferentialGeometry.Geometry.gram_determinant_pos (F.S.base.metric 0) x v w hvw
    have hp := (curvatureOperatorPositiveAt_iff_sectional (U.base.metric 0) x
      (by simp [MorseModel])).mp (hpos x) (e v) (e w) hgram
    rwa [hcurv] at hp


section TerminalNullPlaneDichotomy

variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [T2Space M] [SigmaCompactSpace M]

omit [I.Boundaryless] [SigmaCompactSpace M] in
theorem hasPositiveSectionalCurvature_iff_forall_curvatureOperatorPositiveAt
    (g : SmoothRiemannianMetric I M) (hdim : Module.finrank ℝ E = 3) :
    DifferentialGeometry.Geometry.HasPositiveSectionalCurvature (I := I) g ↔
      ∀ x : M, CurvatureOperatorPositiveAt (I := I) (M := M) g x := by
  constructor
  · intro hsec x
    rw [curvatureOperatorPositiveAt_iff_sectional (I := I) (M := M) g x hdim]
    intro a b hgram
    exact hsec x a b
      (Geometry.Riemannian.linearIndependent_pair_of_sectionalCurvatureDenominator_pos
        (I := I) (M := M) g x a b (by
          simpa only [Geometry.Riemannian.sectionalCurvatureDenominator_def] using hgram))
  · intro hpos x a b hab
    have hgram : 0 < g.inner x a a * g.inner x b b - (g.inner x a b) ^ 2 := by
      simpa only [Geometry.Riemannian.sectionalCurvatureDenominator_def] using
        Geometry.Riemannian.sectionalCurvatureDenominator_pos_of_linearIndependent
          (I := I) (M := M) g x a b hab
    exact ((curvatureOperatorPositiveAt_iff_sectional (I := I) (M := M) g x hdim).mp
      (hpos x) a b hgram)

omit [I.Boundaryless] [SigmaCompactSpace M] in
theorem exists_nullPlane_of_not_forall_curvatureOperatorPositiveAt
    (g : SmoothRiemannianMetric I M) (hdim : Module.finrank ℝ E = 3)
    (hnonneg : ∀ x : M, metricAlgebraicCurvatureTensorAt (I := I) (M := M) g x ∈
      algebraicCurvatureOperatorNonnegativeCone (I := I) (M := M))
    (hnot : ¬ ∀ x : M, CurvatureOperatorPositiveAt (I := I) (M := M) g x) :
    ∃ x : M, ∃ a b : TangentSpace I x,
      0 < g.inner x a a * g.inner x b b - (g.inner x a b) ^ 2 ∧
      metricRm04StandardAt (I := I) (M := M) g x a b b a = 0 := by
  push Not at hnot
  obtain ⟨x, hx⟩ := hnot
  have hplanes := (not_congr
    (curvatureOperatorPositiveAt_iff_sectional (I := I) (M := M) g x hdim)).mp hx
  push Not at hplanes
  obtain ⟨a, b, hgram, hnonpos⟩ := hplanes
  refine ⟨x, a, b, ?_, ?_⟩
  · simpa only [Geometry.Riemannian.sectionalCurvatureDenominator_def] using hgram
  · have hnonneg' : 0 ≤ metricRm04StandardAt (I := I) (M := M) g x a b b a := by
      have h := mem_algebraicCurvatureOperatorNonnegativeCone.mp (hnonneg x)
        1 (fun _ : Fin 1 => 1) (fun _ : Fin 1 => a) (fun _ : Fin 1 => b)
      simpa only [algebraicCurvatureOperatorQuadraticEval, Fin.sum_univ_one, one_mul,
        metricAlgebraicCurvatureTensorAt_coe, metricRm04StandardAt] using h
    exact le_antisymm hnonpos hnonneg'

end TerminalNullPlaneDichotomy

def TerminalNullPlaneSplitting (F : PointedFlowData.{u, uE, uH} (I := I) D) : Prop :=
  ∀ x : F.M, ∀ a b : TangentSpace I x,
    0 < (F.S.base.metric 0).inner x a a * (F.S.base.metric 0).inner x b b -
        ((F.S.base.metric 0).inner x a b) ^ 2 →
      metricRm04StandardAt (I := I) (M := F.M) (F.S.base.metric 0) x a b b a = 0 →
        (∀ y : F.M, F.rmNormSq (I := I) 0 y = 0) ∨
          Nonempty (TerminalSurfaceProduct (I := I) (F.S.base.metric 0))

theorem klim_terminal_curvature_trichotomy_of_nullPlaneSplitting
    (hsplit : TerminalNullPlaneSplitting (I := I) F)
    {kappa : ℝ} (hK : KLim (I := I) kappa F) (hdim : Module.finrank ℝ E = 3) :
    DifferentialGeometry.Geometry.HasPositiveSectionalCurvature (I := I) (F.S.base.metric 0) ∨
      (∀ x : F.M, F.rmNormSq (I := I) 0 x = 0) ∨
      Nonempty (TerminalSurfaceProduct (I := I) (F.S.base.metric 0)) := by
  by_cases hpos : DifferentialGeometry.Geometry.HasPositiveSectionalCurvature (I := I)
    (F.S.base.metric 0)
  · exact Or.inl hpos
  · refine Or.inr ?_
    have hnot : ¬ ∀ x : F.M,
        CurvatureOperatorPositiveAt (I := I) (M := F.M) (F.S.base.metric 0) x :=
      fun h => hpos ((hasPositiveSectionalCurvature_iff_forall_curvatureOperatorPositiveAt
        (I := I) (M := F.M) (F.S.base.metric 0) hdim).mpr h)
    have hnonneg : ∀ x : F.M,
        metricAlgebraicCurvatureTensorAt (I := I) (M := F.M) (F.S.base.metric 0) x ∈
          algebraicCurvatureOperatorNonnegativeCone (I := I) (M := F.M) := by
      intro x
      apply mem_algebraicCurvatureOperatorNonnegativeCone.mpr
      intro n c v w
      have h0 : (0 : ℝ) ∈ D.carrier := by
        simpa only [hK.carrier_eq, Set.mem_Iic] using (le_rfl : (0 : ℝ) ≤ 0)
      have h := hK.nonnegativeCurvatureOperator 0 h0 x n c v w
      simpa only [algebraicCurvatureOperatorQuadraticEval, metricAlgebraicCurvatureTensorAt,
        tensor04StandardAt, SolutionFamily.rm04, metricRm04_apply] using h
    obtain ⟨x, a, b, hgram, hnull⟩ :=
      exists_nullPlane_of_not_forall_curvatureOperatorPositiveAt (I := I) (M := F.M)
        (F.S.base.metric 0) hdim hnonneg hnot
    exact hsplit x a b hgram hnull

end DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions

end
