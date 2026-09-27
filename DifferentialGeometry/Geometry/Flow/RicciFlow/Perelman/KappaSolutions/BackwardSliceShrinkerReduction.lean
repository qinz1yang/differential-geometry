import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.KappaSolutions.AsymptoticShrinkerBlowdown
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.KappaSolutions.AncientSplittingFrontier
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.KappaSolutions.ForwardFlatness
import DifferentialGeometry.Geometry.Flow.RicciFlow.DimensionThree.CurvatureRank
import DifferentialGeometry.Geometry.Curvature.DimensionThree.CurvatureOperatorVanishing

set_option autoImplicit false

noncomputable section

namespace DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions

open Bundle Filter Set
open DifferentialGeometry.Geometry
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.CheegerGromovCompactness
open DifferentialGeometry.Geometry.Riemannian.Topology
open CanonicalNeighborhood
open scoped _root_.Manifold ContDiff _root_.Topology

universe u uE uH

section BackwardSliceComponents

variable {E : Type uE} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)] [CompleteSpace E]
  {H : Type uH} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {D : RealTimeInterval} (F : PointedFlowData.{u, uE, uH} (I := I) D)

local instance backwardSliceShrinkerReductionTopology : TopologicalSpace F.M := F.topology
local instance backwardSliceShrinkerReductionCharted : ChartedSpace H F.M := F.charted
local instance backwardSliceShrinkerReductionSmooth : IsManifold I ∞ F.M := F.smooth
local instance backwardSliceShrinkerReductionT2 : T2Space F.M := F.t2
local instance backwardSliceShrinkerReductionSigma : SigmaCompactSpace F.M := F.sigmaCompact
local instance backwardSliceShrinkerReductionTangentT2 :
    T2Space (TangentBundle I F.M) := F.t2TangentBundle

theorem exists_backward_slice_asymptotic_shrinker_of_antitone_compactness_rigidity
    {kappa : ℝ} (hF : IsAncientKappaSolution kappa F)
    (_hdim : 2 ≤ Module.finrank ℝ E)
    (tau : ℕ → ℝ) (htau : ∀ i, 0 < tau i) (_hescape : Tendsto tau atTop atTop)
    (h : ∃ (q : ℕ → F.M) (p : F.M),
      AntitoneOn (intrinsicReducedVolume F.S 0 p) (Set.Ioi 0) ∧
      backwardSliceApproximateMetricCompactness F hF tau htau q ∧
      backwardSliceLimitGradientShrinker F tau htau q p) :
    ∃ (q : ℕ → F.M) (L : PointedRiemannianManifold.{u, uE, uH} (I := I)) (phi : ℕ → ℕ),
      StrictMono phi ∧
      ∃ (Phi : PointedRiemannianConvergenceMaps (I := I) (backwardSliceSequence F tau htau q) L phi)
        (C : MetricConvergenceData (I := I) Phi),
        (∀ k, C.domain k = CanonicalMetricCompactness.canonicalSourceData (I := I) Phi k) ∧
        (∀ k, (C.domain k).referenceMetric = (C.domain k).limitMetric) ∧
        MetricComplete (I := I) L ∧
        (let _ : TopologicalSpace L.M := L.topology
         let _ : ChartedSpace H L.M := L.charted
         let _ : IsManifold I ∞ L.M := L.smooth
         let _ : T2Space L.M := L.t2
         ConnectedSpace L.M ∧
         (∃ x : L.M, metricScalarAt (I := I) L.metric x ≠ 0) ∧
         ∃ f : C^∞⟮I, L.M; ℝ⟯, gradientRicciSoliton (I := I) L.metric f 1) := by
  obtain ⟨q, p, hmono, hcompact, hrigid⟩ := h
  exact ⟨q, exists_backward_slice_asymptotic_shrinker_of_blowdownInput F hF tau htau q p
    hmono hcompact hrigid⟩

end BackwardSliceComponents

section NullPlane

variable {E : Type uE} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [CompleteSpace E]
  {H : Type uH} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  (F : PointedFlowData.{u, uE, uH} (I := I) ancientTimeInterval)

local instance backwardSliceShrinkerAncientTopology : TopologicalSpace F.M := F.topology
local instance backwardSliceShrinkerAncientCharted : ChartedSpace H F.M := F.charted
local instance backwardSliceShrinkerAncientSmooth : IsManifold I ∞ F.M := F.smooth
local instance backwardSliceShrinkerAncientC1 : IsManifold I 1 F.M :=
  IsManifold.of_le (I := I) (M := F.M) (n := ∞) (by decide)
local instance backwardSliceShrinkerAncientC2 : IsManifold I ((∞ : WithTop ℕ∞) + 1) F.M := by
  change IsManifold I ∞ F.M
  infer_instance
local instance backwardSliceShrinkerAncientT2 : T2Space F.M := F.t2
local instance backwardSliceShrinkerAncientSigma : SigmaCompactSpace F.M := F.sigmaCompact
local instance backwardSliceShrinkerAncientTangentT2 :
    T2Space (TangentBundle I F.M) := F.t2TangentBundle
local instance backwardSliceShrinkerAncientInhabited : Inhabited F.M := ⟨F.basepoint⟩
local instance backwardSliceShrinkerAncientLocallyPathConnected :
    LocallyPathConnectedSpace F.M := by
  let _ : LocallyPathConnectedSpace H :=
    I.toHomeomorph.isOpenEmbedding.locallyPathConnectedSpace
  exact ChartedSpace.locallyPathConnectedSpace H F.M
local instance backwardSliceShrinkerAncientSemilocallySimplyConnected :
    SemilocallySimplyConnectedSpace F.M :=
  manifold_semilocallySimplyConnectedSpace (I := I) (M := F.M)

omit [I.Boundaryless] in
private theorem rmNormSq_eq_zero_of_curvatureOperatorImageAt_finrank_eq_zero
    (hdim : Module.finrank ℝ E = 3) (t : ℝ) (x : F.M)
    (hzero : Module.finrank ℝ (curvatureOperatorImageAt (I := I) (F.S.base.metric t) x
      ⟨metricRm04At (I := I) (F.S.base.metric t) x,
        metricRm04At_mem_algebraicCurvatureTensorSubmodule
          (I := I) (F.S.base.metric t) x⟩) = 0) :
    F.rmNormSq (I := I) t x = 0 := by
  have hbot : curvatureOperatorImageAt (I := I) (F.S.base.metric t) x
      ⟨metricRm04At (I := I) (F.S.base.metric t) x,
        metricRm04At_mem_algebraicCurvatureTensorSubmodule
          (I := I) (F.S.base.metric t) x⟩ = ⊥ :=
    Submodule.finrank_eq_zero.mp hzero
  have hop : curvatureOperatorEndomorphismAt (I := I) (F.S.base.metric t) x
      ⟨metricRm04At (I := I) (F.S.base.metric t) x,
        metricRm04At_mem_algebraicCurvatureTensorSubmodule
          (I := I) (F.S.base.metric t) x⟩ = 0 := by
    refine ContinuousLinearMap.ext fun a => ?_
    have ha : curvatureOperatorEndomorphismAt (I := I) (F.S.base.metric t) x
        ⟨metricRm04At (I := I) (F.S.base.metric t) x,
          metricRm04At_mem_algebraicCurvatureTensorSubmodule
            (I := I) (F.S.base.metric t) x⟩ a ∈
        (curvatureOperatorEndomorphismAt (I := I) (F.S.base.metric t) x
          ⟨metricRm04At (I := I) (F.S.base.metric t) x,
            metricRm04At_mem_algebraicCurvatureTensorSubmodule
              (I := I) (F.S.base.metric t) x⟩).range := ⟨a, rfl⟩
    rw [← curvatureOperatorImageAt_eq_range] at ha
    rw [hbot] at ha
    simpa using ha
  have hrm : metricRm04At (I := I) (F.S.base.metric t) x = 0 :=
    DimensionThree.metricRm04At_eq_zero_of_curvatureOperatorEndomorphismAt_eq_zero
      (I := I) (F.S.base.metric t) x hdim hop
  have hrm' : F.S.base.rm04 t x = 0 := by
    have h1 : F.S.base.rm04 t x =
        metricRm04 (I := I) (M := F.M) (F.S.base.metric t) x := rfl
    rw [h1, metricRm04_apply, hrm]
  rw [show F.rmNormSq (I := I) t x = Tensor0SBundle.normSq0S (I := I)
      (F.S.base.metric t) x 4 (F.S.base.rm04 t x) from by
    simp only [PointedFlowData.rmNormSq, SolutionOn.family_metric]]
  rw [hrm']
  simp only [Tensor0SBundle.normSq0S, Tensor0SBundle.inner0S,
    Tensor0SBundle.MetricFiberData.inner, map_zero]

theorem nullPlane_scalar_pos_and_rank_one_at_negative_time
    (hdim : Module.finrank ℝ E = 3)
    (hconnected : ConnectedSpace F.M)
    (hcomplete : ∀ t : ℝ, t ≤ 0 → MetricComplete (I := I) (F.atTime t))
    (hcurvature : ∀ t : ℝ, t ≤ 0 →
      PointedFlowNonnegativeCurvatureOperator (I := I) F t)
    (hbounded : ∀ a b : ℝ, a < b → b ≤ 0 →
      ∃ C : ℝ, 0 ≤ C ∧ ∀ t ∈ Set.Icc a b, ∀ x : F.M,
        F.rmNormSq (I := I) t x ≤ C)
    (hnotFlat : PointedFlowNotFlat (I := I) F)
    (t₀ : ℝ) (ht₀ : t₀ < 0) (x₀ : F.M) (v₀ w₀ : TangentSpace I x₀)
    (hplane : 0 <
      (F.S.family.metric t₀).inner x₀ v₀ v₀ *
        (F.S.family.metric t₀).inner x₀ w₀ w₀ -
          ((F.S.family.metric t₀).inner x₀ v₀ w₀) ^ 2)
    (hnull : F.S.base.rm04 t₀ x₀ (vec4 (I := I) v₀ w₀ w₀ v₀) = 0) :
    0 < metricScalarAt (I := I) (F.S.base.metric t₀) x₀ ∧
      ∀ x : F.M, Module.finrank ℝ
        (curvatureOperatorImageAt (I := I) (F.S.base.metric t₀) x
          ⟨metricRm04At (I := I) (F.S.base.metric t₀) x,
            metricRm04At_mem_algebraicCurvatureTensorSubmodule
              (I := I) (F.S.base.metric t₀) x⟩) = 1 := by
  let _ : ConnectedSpace F.M := hconnected
  rcases nullPlane_slice_dichotomy_at_t₀ F hconnected hdim hcurvature t₀ ht₀ x₀ v₀ w₀
    hplane hnull with ⟨_, hendo⟩ | hpositive
  · exfalso
    have hflat : ∀ x : F.M, F.rmNormSq (I := I) t₀ x = 0 := by
      intro x
      have hbot : curvatureOperatorImageAt (I := I) (F.S.base.metric t₀) x
          ⟨metricRm04At (I := I) (F.S.base.metric t₀) x,
            metricRm04At_mem_algebraicCurvatureTensorSubmodule
              (I := I) (F.S.base.metric t₀) x⟩ = ⊥ := by
        rw [curvatureOperatorImageAt_eq_range, hendo x]
        simp
      exact rmNormSq_eq_zero_of_curvatureOperatorImageAt_finrank_eq_zero F hdim t₀ x
        (Submodule.finrank_eq_zero.mpr hbot)
    obtain ⟨C, hC0, hC⟩ := hbounded (t₀ - 1) 0 (by linarith) le_rfl
    have hcurv : ∃ K : ℝ, ∀ t ∈ Set.Icc t₀ 0, ∀ x : F.M,
        F.rmNormSq (I := I) t x ≤ K :=
      ⟨C, fun t ht x => hC t ⟨by linarith [ht.1], ht.2⟩ x⟩
    have hflatAll : ∀ t ∈ Set.Icc t₀ 0, ∀ x : F.M, F.rmNormSq (I := I) t x = 0 :=
      complete_forward_flatness F ht₀
        (fun t ht => by simpa only [ancientTimeInterval_carrier, Set.mem_Iic] using ht.2)
        (fun t ht => by
          simpa only [ancientTimeInterval_regular, Set.mem_Iio] using ht.2)
        (fun t ht => hcomplete t ht.2) hcurv hflat
    obtain ⟨t₁, ht₁, x₁, hx₁⟩ := hnotFlat
    rcases lt_or_ge t₁ t₀ with hlt | hle
    · have hreg : Set.Icc t₁ t₀ ⊆ ancientTimeInterval.regular := by
        intro r hr
        simp only [ancientTimeInterval_regular, Set.mem_Iio]
        exact lt_of_le_of_lt hr.2 ht₀
      have hcone : ∀ r ∈ Set.Icc t₁ t₀, ∀ x : F.M,
          (⟨metricRm04At (I := I) (F.S.base.metric r) x,
            metricRm04At_mem_algebraicCurvatureTensorSubmodule
              (I := I) (F.S.base.metric r) x⟩ :
            algebraicCurvatureTensorSubmodule (I := I) (M := F.M) x) ∈
            algebraicCurvatureOperatorNonnegativeCone (I := I) (M := F.M) :=
        fun r hr => nullPlane_curvatureOperatorImageAt_finrank_cone_membership F hcurvature r
          (le_of_lt (lt_of_le_of_lt hr.2 ht₀))
      have hrank := curvatureOperatorImageAt_finrank_le_at_later_time (S := F.S)
        F.isSolution hdim hlt hreg hcone x₁ x₀
      have hzero : Module.finrank ℝ (curvatureOperatorImageAt (I := I)
          (F.S.base.metric t₁) x₁
          ⟨metricRm04At (I := I) (F.S.base.metric t₁) x₁,
            metricRm04At_mem_algebraicCurvatureTensorSubmodule
              (I := I) (F.S.base.metric t₁) x₁⟩) = 0 := by
        have hbot : curvatureOperatorImageAt (I := I) (F.S.base.metric t₀) x₀
            ⟨metricRm04At (I := I) (F.S.base.metric t₀) x₀,
              metricRm04At_mem_algebraicCurvatureTensorSubmodule
                (I := I) (F.S.base.metric t₀) x₀⟩ = ⊥ := by
          rw [curvatureOperatorImageAt_eq_range, hendo x₀]
          simp
        exact Nat.le_zero.mp (hrank.trans_eq (Submodule.finrank_eq_zero.mpr hbot))
      exact hx₁ (rmNormSq_eq_zero_of_curvatureOperatorImageAt_finrank_eq_zero F hdim t₁ x₁ hzero)
    · exact hx₁ (hflatAll t₁ ⟨hle, ht₁⟩ x₁)
  · exact hpositive

end NullPlane

end DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions

end
