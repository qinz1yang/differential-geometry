import DifferentialGeometry.Analysis.Sobolev.TensorHilbert.DeTurckLie.FirstOrderTerm.L2JetBound
import DifferentialGeometry.Analysis.Spectral.Tensor.CovGrad.CurvatureCoefficientDifferenceJetTower.PairTrace
import DifferentialGeometry.Analysis.Spectral.Tensor.CovGrad.Permutation.Jets
import DifferentialGeometry.Analysis.Spectral.Intrinsic.DeTurckCoefficients.LieCorrection.Zero.Splitting

noncomputable section


open Bundle Manifold DifferentialGeometry.Tensor0SBundle
open scoped Manifold Topology ContDiff BigOperators

namespace DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral

open DifferentialGeometry.Integral.L2
open DifferentialGeometry.Integral.Connection
open DifferentialGeometry.Analysis.Parabolic.TensorSpectral
open DifferentialGeometry.Analysis.Spectral.DeTurck
open DifferentialGeometry.Analysis.Spectral
open DifferentialGeometry.Analysis.Spectral.LieCorrectionZeroCore
open DifferentialGeometry.Analysis.Sobolev

variable
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
      [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
      [IsManifold I ∞ M] [CompactSpace M] [I.Boundaryless]
      [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M]

private local instance : CompleteSpace E := FiniteDimensional.complete ℝ E

def reindexedPureTrace (g₀ g₁ : SmoothRiemannianMetric I M) (p : ℕ)
    (σ : Equiv.Perm (Fin (p + 2))) : SmoothCcTensor g₀ (p + 2) p :=
  reindexCoefficientInputSlots (I := I) (M := M) g₀ (p + 2) p
    (pureTrace (I := I) (M := M) g₀ g₁ p) σ

omit [NeZero (Module.finrank ℝ E)] [BoundarylessManifold I M] [SigmaCompactSpace M] in
omit [I.Boundaryless] in
theorem reindexedPureTrace_toSection (g₀ g₁ : SmoothRiemannianMetric I M) (p : ℕ)
    (σ : Equiv.Perm (Fin (p + 2))) (x : M) :
    (show Tensor0SSpace (p + 2) I x →L[ℝ] Tensor0SSpace p I x from
      (reindexedPureTrace (I := I) (M := M) g₀ g₁ p σ).toSection x) =
      lieCorrectionZeroTraceStep (I := I) g₁ p σ x := by
  apply ContinuousLinearMap.ext
  intro D
  rw [show
      ((show Tensor0SSpace (p + 2) I x →L[ℝ] Tensor0SSpace p I x from
        (reindexedPureTrace (I := I) (M := M) g₀ g₁ p σ).toSection x) D) =
        reindexCoefficientInputSlotsFiber (I := I) (p + 2) p σ x
          (show Tensor0SSpace (p + 2) I x →L[ℝ] Tensor0SSpace p I x from
            (pureTrace (I := I) (M := M) g₀ g₁ p).toSection x) D from rfl]
  rw [reindexCoefficientInputSlotsFiber_apply (I := I) (p + 2) p σ x _ D,
    pureTrace_toSection (I := I) (M := M) g₀ g₁ p x,
    lieCorrectionZeroTraceStep, ContinuousLinearMap.comp_apply]
  congr 1

omit [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M] in
private lemma unitTensor_model (x : M) (m : Fin 0 → E) :
    Tensor0SSpace.toModel (unitTensor (I := I) (M := M) x) m = 1 := by
  rw [unitTensor, Tensor0SSpace.toModel_ofModel]
  rfl

omit [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M] in
private lemma curry_zero (x : M) (D : Tensor0SSpace 1 I x) (v₀ : E) :
    tensor0SCurry (I := I) (M := M) (𝕜 := ℝ) 0 x D
        ((tangentSpaceModelContinuousLinearEquiv (I := I) x).symm v₀) =
      (Tensor0SSpace.toModel D (fun _ : Fin 1 => v₀)) •
        unitTensor (I := I) (M := M) x := by
  apply Tensor0SSpace.toModel_injective
  apply ContinuousMultilinearMap.ext
  intro m
  beta_reduce
  have h₁ : Tensor0SSpace.toModel
      (tensor0SCurry (I := I) (M := M) (𝕜 := ℝ) 0 x D
        ((tangentSpaceModelContinuousLinearEquiv (I := I) x).symm v₀)) m =
      Tensor0SSpace.toModel D (Fin.cons v₀ m) :=
    TensorMultilinear.tensor0S_curry_toModel_apply (I := I) (M := M) (n := 0)
      (T := D) (v0 := v₀) (vs := m)
  rw [h₁, Tensor0SSpace.toModel_smul, smul_apply,
    unitTensor_model (I := I) (M := M) x m, smul_eq_mul, mul_one]
  congr 1
  funext k
  refine Fin.cases ?_ (fun j => j.elim0) k
  rfl

omit [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M] in
private lemma clm_unit_smul (x : M) (s : ℕ)
    (A : Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace s I x) (c : ℝ) :
    A (c • unitTensor (I := I) (M := M) x) =
      c • A (unitTensor (I := I) (M := M) x) := A.map_smul c _

omit [NeZero (Module.finrank ℝ E)] [I.Boundaryless] [BoundarylessManifold I M] [SigmaCompactSpace M] in
private lemma slotExtendIter_rank_two_by_rank_three_apply (g₀ : SmoothRiemannianMetric I M)
    (K : SmoothCcTensor g₀ 0 3) (x : M) (D : Tensor0SSpace 2 I x) :
    (show Tensor0SSpace 2 I x →L[ℝ] Tensor0SSpace 5 I x from
      (slotExtendIter (I := I) (M := M) g₀ 0 3 2 K).toSection x) D =
    tensor0SProdKappaFib (I := I) (p := 2) (q := 3) x
      ((show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace 3 I x from K.toSection x)
        (unitTensor (I := I) (M := M) x)) D := by
  apply Tensor0SSpace.toModel_injective
  apply ContinuousMultilinearMap.ext
  intro m
  beta_reduce
  set κ : Tensor0SSpace 3 I x :=
    (show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace 3 I x from K.toSection x)
      (unitTensor (I := I) (M := M) x) with hκ
  have hLHS : Tensor0SSpace.toModel
      ((show Tensor0SSpace 2 I x →L[ℝ] Tensor0SSpace 5 I x from
        (slotExtendIter (I := I) (M := M) g₀ 0 3 2 K).toSection x) D) m =
      Tensor0SSpace.toModel D ![m 0, m 1] *
        Tensor0SSpace.toModel κ (fun j : Fin 3 => m (Fin.natAdd 2 j)) := by
    rw [show
        ((show Tensor0SSpace 2 I x →L[ℝ] Tensor0SSpace 5 I x from
          (slotExtendIter (I := I) (M := M) g₀ 0 3 2 K).toSection x) D) =
          slotExtendFib (I := I) (M := M) 1 4 x
            (show Tensor0SSpace 1 I x →L[ℝ] Tensor0SSpace 4 I x from
              (slotExtendIter (I := I) (M := M) g₀ 0 3 1 K).toSection x) D
          from rfl]
    rw [show m = Fin.cons (m 0) (Fin.tail m) from (Fin.cons_self_tail m).symm]
    rw [DifferentialGeometry.Integral.Connection.slotExtendFib_apply_eval (I := I) (M := M) 1 4 x _ D
      (m 0) (Fin.tail m)]
    set D₁ : Tensor0SSpace 1 I x :=
      tensor0SCurry (I := I) (M := M) (𝕜 := ℝ) 1 x D
        ((tangentSpaceModelContinuousLinearEquiv (I := I) x).symm (m 0)) with hD₁
    rw [show
        ((show Tensor0SSpace 1 I x →L[ℝ] Tensor0SSpace 4 I x from
          (slotExtendIter (I := I) (M := M) g₀ 0 3 1 K).toSection x) D₁) =
          slotExtendFib (I := I) (M := M) 0 3 x
            (show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace 3 I x from K.toSection x) D₁
          from rfl]
    rw [show (Fin.tail m : Fin 4 → E) =
        Fin.cons (m 1) (fun j : Fin 3 => m (Fin.natAdd 2 j)) from by
      funext k
      fin_cases k <;> rfl]
    rw [DifferentialGeometry.Integral.Connection.slotExtendFib_apply_eval (I := I) (M := M) 0 3 x _ D₁
      (m 1) (fun j : Fin 3 => m (Fin.natAdd 2 j))]
    rw [curry_zero (I := I) (M := M) x D₁ (m 1)]
    rw [clm_unit_smul (I := I) (M := M) x 3 _ _]
    rw [← hκ, Tensor0SSpace.toModel_smul,
      smul_apply, smul_eq_mul]
    have hD₁val : Tensor0SSpace.toModel D₁ (fun _ : Fin 1 => m 1) =
        Tensor0SSpace.toModel D ![m 0, m 1] := by
      rw [hD₁, TensorMultilinear.tensor0S_curry_toModel_apply
        (I := I) (M := M) (n := 1) (T := D) (v0 := m 0)
        (vs := fun _ : Fin 1 => m 1)]
      congr 1
      funext k
      fin_cases k <;> rfl
    rw [hD₁val]
    first
      | rfl
      | (congr 1; first | rfl | (congr 1; funext k; fin_cases k <;> rfl))
  rw [hLHS, tensor0SProdKappaFib_apply (I := I) x κ D,
    Tensor0SSpace.toModel_ofModel,
    Bundle.continuousMultilinearMap.modelProduct_apply]
  congr 1
  all_goals
    first
      | rfl
      | (congr 1; funext k; fin_cases k <;> rfl)

omit [NeZero (Module.finrank ℝ E)] [I.Boundaryless] [BoundarylessManifold I M] [SigmaCompactSpace M] in
private lemma slotExtendIter_rank_three_by_rank_three_apply (g₀ : SmoothRiemannianMetric I M)
    (K : SmoothCcTensor g₀ 0 3) (x : M) (D : Tensor0SSpace 3 I x) :
    (show Tensor0SSpace 3 I x →L[ℝ] Tensor0SSpace 6 I x from
      (slotExtendIter (I := I) (M := M) g₀ 0 3 3 K).toSection x) D =
    tensor0SProdKappaFib (I := I) (p := 3) (q := 3) x
      ((show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace 3 I x from K.toSection x)
        (unitTensor (I := I) (M := M) x)) D := by
  apply Tensor0SSpace.toModel_injective
  apply ContinuousMultilinearMap.ext
  intro m
  beta_reduce
  set κ : Tensor0SSpace 3 I x :=
    (show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace 3 I x from K.toSection x)
      (unitTensor (I := I) (M := M) x) with hκ
  have hLHS : Tensor0SSpace.toModel
      ((show Tensor0SSpace 3 I x →L[ℝ] Tensor0SSpace 6 I x from
        (slotExtendIter (I := I) (M := M) g₀ 0 3 3 K).toSection x) D) m =
      Tensor0SSpace.toModel D ![m 0, m 1, m 2] *
        Tensor0SSpace.toModel κ (fun j : Fin 3 => m (Fin.natAdd 3 j)) := by
    rw [show
        ((show Tensor0SSpace 3 I x →L[ℝ] Tensor0SSpace 6 I x from
          (slotExtendIter (I := I) (M := M) g₀ 0 3 3 K).toSection x) D) =
          slotExtendFib (I := I) (M := M) 2 5 x
            (show Tensor0SSpace 2 I x →L[ℝ] Tensor0SSpace 5 I x from
              (slotExtendIter (I := I) (M := M) g₀ 0 3 2 K).toSection x) D
          from rfl]
    rw [show m = Fin.cons (m 0) (Fin.tail m) from (Fin.cons_self_tail m).symm]
    rw [DifferentialGeometry.Integral.Connection.slotExtendFib_apply_eval (I := I) (M := M) 2 5 x _ D
      (m 0) (Fin.tail m)]
    set D₂ : Tensor0SSpace 2 I x :=
      tensor0SCurry (I := I) (M := M) (𝕜 := ℝ) 2 x D
        ((tangentSpaceModelContinuousLinearEquiv (I := I) x).symm (m 0)) with hD₂
    rw [slotExtendIter_rank_two_by_rank_three_apply (I := I) (M := M) g₀ K x D₂, ← hκ,
      tensor0SProdKappaFib_apply (I := I) x κ D₂,
      Tensor0SSpace.toModel_ofModel,
      Bundle.continuousMultilinearMap.modelProduct_apply]
    have hD₂val : Tensor0SSpace.toModel D₂
        ((Fin.tail m : Fin 5 → E) ∘ Fin.castAdd 3) =
        Tensor0SSpace.toModel D ![m 0, m 1, m 2] := by
      rw [hD₂, TensorMultilinear.tensor0S_curry_toModel_apply
        (I := I) (M := M) (n := 2) (T := D) (v0 := m 0)
        (vs := (Fin.tail m : Fin 5 → E) ∘ Fin.castAdd 3)]
      congr 1
      funext k
      fin_cases k <;> rfl
    rw [hD₂val]
    first
      | rfl
      | (congr 2; funext j; fin_cases j <;> rfl)
  rw [hLHS, tensor0SProdKappaFib_apply (I := I) x κ D,
    Tensor0SSpace.toModel_ofModel,
    Bundle.continuousMultilinearMap.modelProduct_apply]
  congr 1
  all_goals
    first
      | rfl
      | (congr 1; funext k; fin_cases k <;> rfl)

omit [NeZero (Module.finrank ℝ E)] [I.Boundaryless] [SigmaCompactSpace M] in
private lemma metricConnectionDifferenceLoweredCoefficient_apply_unitTensor (g₀ g₁ gB : SmoothRiemannianMetric I M) (x : M) :
    (show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace 3 I x from
      (metricConnectionDifferenceLoweredCoefficient (I := I) (M := M) g₀ g₁ gB).toSection x)
        (unitTensor (I := I) (M := M) x) =
      metricConnectionDifferenceLoweredFib (I := I) g₁ g₁ gB x := by
  rw [show
      (show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace 3 I x from
        (metricConnectionDifferenceLoweredCoefficient (I := I) (M := M) g₀ g₁ gB).toSection x)
          (unitTensor (I := I) (M := M) x) =
        (MixedSection.eval₀ (F := E) (E := (TangentSpace I : M → Type _)) x).smulRight
          (metricConnectionDifferenceLoweredFib (I := I) g₁ g₁ gB x)
          (ContinuousMultilinearMap.constOfIsEmpty ℝ
            (fun _ : Fin 0 => TangentSpace I x) (1 : ℝ)) from rfl]
  rw [ContinuousLinearMap.smulRight_apply, MixedSection.eval₀_apply,
    ContinuousMultilinearMap.constOfIsEmpty_apply, one_smul]

def lieCorrectionZeroMixedConnectionHalfExpansion (g₀ g₁ gB : SmoothRiemannianMetric I M)
    (σlast : Equiv.Perm (Fin 4)) : SmoothCcTensor g₀ 2 2 :=
  ccOperatorFieldComp (I := I) (M := M) g₀ 2 4 2
    (reindexedPureTrace (I := I) (M := M) g₀ g₁ 2 σlast)
    (ccOperatorFieldComp (I := I) (M := M) g₀ 2 6 4
      (reindexedPureTrace (I := I) (M := M) g₀ g₁ 4 lieCorrectionZeroMixedConnectionPermutationCycleZeroTwoThreeOne)
      (ccOperatorFieldComp (I := I) (M := M) g₀ 2 3 6
        (slotExtendIter (I := I) (M := M) g₀ 0 3 3
          (metricConnectionDifferenceLoweredCoefficient (I := I) (M := M) g₀ g₁ gB))
        (ccOperatorFieldComp (I := I) (M := M) g₀ 2 5 3
          (reindexedPureTrace (I := I) (M := M) g₀ g₁ 3 lieCorrectionZeroMixedConnectionPermutationCycleZeroOneFour)
          (slotExtendIter (I := I) (M := M) g₀ 0 3 2
            (metricConnectionDifferenceLoweredCoefficient (I := I) (M := M) g₀ g₁ g₀)))))

def lieCorrectionZeroMixedConnectionTraceOutputSwapPermutation : Equiv.Perm (Fin 4) :=
  ⟨![0, 1, 3, 2], ![0, 1, 3, 2], by decide, by decide⟩

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M] in
private lemma lieCorrectionZeroMixedConnection_trace_output_swap (g₁ : SmoothRiemannianMetric I M)
    (σ : Equiv.Perm (Fin 4)) (x : M) (Z : Tensor0SSpace 4 I x) :
    domDomCongrFibRank (I := I) 2 (Equiv.swap (0 : Fin 2) 1) x
      (lieCorrectionZeroTraceStep (I := I) g₁ 2 σ x Z) =
    lieCorrectionZeroTraceStep (I := I) g₁ 2 (lieCorrectionZeroMixedConnectionTraceOutputSwapPermutation * σ) x Z := by
  apply Tensor0SSpace.toModel_injective
  apply ContinuousMultilinearMap.ext
  intro w
  beta_reduce
  rw [domDomCongrFibRank_apply (I := I) 2 (Equiv.swap (0 : Fin 2) 1) x,
    Tensor0SSpace.toModel_ofModel, ContinuousMultilinearMap.domDomCongr_apply]
  rw [show lieCorrectionZeroTraceStep (I := I) g₁ 2 σ x Z =
      cometricDoubleTraceFib (I := I) g₁ 2 x
        (domDomCongrFibRank (I := I) 4 σ x Z) from rfl]
  rw [show lieCorrectionZeroTraceStep (I := I) g₁ 2 (lieCorrectionZeroMixedConnectionTraceOutputSwapPermutation * σ) x Z =
      cometricDoubleTraceFib (I := I) g₁ 2 x
        (domDomCongrFibRank (I := I) 4 (lieCorrectionZeroMixedConnectionTraceOutputSwapPermutation * σ) x Z) from rfl]
  rw [cometricDoubleTraceFib_toModel (I := I) g₁ 2 x,
    cometricDoubleTraceFib_toModel (I := I) g₁ 2 x]
  rw [modelDoubleTrace_apply (E := E) 2 (cometricLmodel (I := I) g₁ x),
    modelDoubleTrace_apply (E := E) 2 (cometricLmodel (I := I) g₁ x)]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [domDomCongrFibRank_apply (I := I) 4 σ x Z,
    Tensor0SSpace.toModel_ofModel, ContinuousMultilinearMap.domDomCongr_apply]
  rw [domDomCongrFibRank_apply (I := I) 4 (lieCorrectionZeroMixedConnectionTraceOutputSwapPermutation * σ) x Z,
    Tensor0SSpace.toModel_ofModel, ContinuousMultilinearMap.domDomCongr_apply]
  congr 1
  funext i
  have hpt : ∀ t : Fin 4,
      (Fin.cons (cometricLmodel (I := I) g₁ x
          (Tensor0SBundle.modelCovectorOfCLM (𝕜 := ℝ) (E := E)
            ((Module.finBasis ℝ E).cDualBasis k)))
        (Fin.cons ((Module.finBasis ℝ E) k)
          (fun j : Fin 2 => w ((Equiv.swap (0 : Fin 2) 1) j))) : Fin 4 → E) t =
      (Fin.cons (cometricLmodel (I := I) g₁ x
          (Tensor0SBundle.modelCovectorOfCLM (𝕜 := ℝ) (E := E)
            ((Module.finBasis ℝ E).cDualBasis k)))
        (Fin.cons ((Module.finBasis ℝ E) k) w) : Fin 4 → E) (lieCorrectionZeroMixedConnectionTraceOutputSwapPermutation t) := by
    intro t
    fin_cases t <;> rfl
  rw [hpt (σ i)]
  rfl

def lieCorrectionZeroMixedConnectionExpansion (g₀ g₁ gB : SmoothRiemannianMetric I M) :
    SmoothCcTensor g₀ 2 2 :=
  (2 : ℝ) •
    (lieCorrectionZeroMixedConnectionHalfExpansion (I := I) (M := M) g₀ g₁ gB lieCorrectionZeroMixedConnectionPermutationCycleZeroTwoOne +
      lieCorrectionZeroMixedConnectionHalfExpansion (I := I) (M := M) g₀ g₁ gB
        (lieCorrectionZeroMixedConnectionTraceOutputSwapPermutation * lieCorrectionZeroMixedConnectionPermutationCycleZeroTwoOne))

omit [NeZero (Module.finrank ℝ E)] [SigmaCompactSpace M] in
omit [I.Boundaryless] in
private lemma lieCorrectionZeroMixedConnectionHalfExpansion_apply (g₀ g₁ gB : SmoothRiemannianMetric I M)
    (σlast : Equiv.Perm (Fin 4)) (x : M) (D : Tensor0SSpace 2 I x) :
    (show Tensor0SSpace 2 I x →L[ℝ] Tensor0SSpace 2 I x from
      (lieCorrectionZeroMixedConnectionHalfExpansion (I := I) (M := M) g₀ g₁ gB σlast).toSection x) D =
    lieCorrectionZeroTraceStep (I := I) g₁ 2 σlast x
      (lieCorrectionZeroTraceStep (I := I) g₁ 4 lieCorrectionZeroMixedConnectionPermutationCycleZeroTwoThreeOne x
        (tensor0SProdKappaFib (I := I) (p := 3) (q := 3) x
          (metricConnectionDifferenceLoweredFib (I := I) g₁ g₁ gB x)
          (lieCorrectionZeroTraceStep (I := I) g₁ 3 lieCorrectionZeroMixedConnectionPermutationCycleZeroOneFour x
            (tensor0SProdKappaFib (I := I) (p := 2) (q := 3) x
              (metricConnectionDifferenceLoweredFib (I := I) g₁ g₁ g₀ x) D)))) := by
  simp only [lieCorrectionZeroMixedConnectionHalfExpansion, operatorFieldComposition_toSection, ContinuousLinearMap.comp_apply]
  rw [slotExtendIter_rank_two_by_rank_three_apply (I := I) (M := M) g₀
    (metricConnectionDifferenceLoweredCoefficient (I := I) (M := M) g₀ g₁ g₀) x D]
  rw [metricConnectionDifferenceLoweredCoefficient_apply_unitTensor (I := I) (M := M) g₀ g₁ g₀ x]
  rw [show
      (show Tensor0SSpace 5 I x →L[ℝ] Tensor0SSpace 3 I x from
        (reindexedPureTrace (I := I) (M := M) g₀ g₁ 3 lieCorrectionZeroMixedConnectionPermutationCycleZeroOneFour).toSection x)
          (tensor0SProdKappaFib (I := I) (p := 2) (q := 3) x
            (metricConnectionDifferenceLoweredFib (I := I) g₁ g₁ g₀ x) D) =
      lieCorrectionZeroTraceStep (I := I) g₁ 3 lieCorrectionZeroMixedConnectionPermutationCycleZeroOneFour x
        (tensor0SProdKappaFib (I := I) (p := 2) (q := 3) x
          (metricConnectionDifferenceLoweredFib (I := I) g₁ g₁ g₀ x) D) from
    congrFun (congrArg DFunLike.coe
      (reindexedPureTrace_toSection (I := I) (M := M) g₀ g₁ 3 lieCorrectionZeroMixedConnectionPermutationCycleZeroOneFour x)) _]
  rw [slotExtendIter_rank_three_by_rank_three_apply (I := I) (M := M) g₀
    (metricConnectionDifferenceLoweredCoefficient (I := I) (M := M) g₀ g₁ gB) x _]
  rw [metricConnectionDifferenceLoweredCoefficient_apply_unitTensor (I := I) (M := M) g₀ g₁ gB x]
  rw [show
      (show Tensor0SSpace 6 I x →L[ℝ] Tensor0SSpace 4 I x from
        (reindexedPureTrace (I := I) (M := M) g₀ g₁ 4 lieCorrectionZeroMixedConnectionPermutationCycleZeroTwoThreeOne).toSection x)
          (tensor0SProdKappaFib (I := I) (p := 3) (q := 3) x
            (metricConnectionDifferenceLoweredFib (I := I) g₁ g₁ gB x)
            (lieCorrectionZeroTraceStep (I := I) g₁ 3 lieCorrectionZeroMixedConnectionPermutationCycleZeroOneFour x
              (tensor0SProdKappaFib (I := I) (p := 2) (q := 3) x
                (metricConnectionDifferenceLoweredFib (I := I) g₁ g₁ g₀ x) D))) =
      lieCorrectionZeroTraceStep (I := I) g₁ 4 lieCorrectionZeroMixedConnectionPermutationCycleZeroTwoThreeOne x
        (tensor0SProdKappaFib (I := I) (p := 3) (q := 3) x
          (metricConnectionDifferenceLoweredFib (I := I) g₁ g₁ gB x)
          (lieCorrectionZeroTraceStep (I := I) g₁ 3 lieCorrectionZeroMixedConnectionPermutationCycleZeroOneFour x
            (tensor0SProdKappaFib (I := I) (p := 2) (q := 3) x
              (metricConnectionDifferenceLoweredFib (I := I) g₁ g₁ g₀ x) D))) from
    congrFun (congrArg DFunLike.coe
      (reindexedPureTrace_toSection (I := I) (M := M) g₀ g₁ 4 lieCorrectionZeroMixedConnectionPermutationCycleZeroTwoThreeOne x)) _]
  exact congrFun (congrArg DFunLike.coe
    (reindexedPureTrace_toSection (I := I) (M := M) g₀ g₁ 2 σlast x)) _

omit [NeZero (Module.finrank ℝ E)] [SigmaCompactSpace M] in
omit [I.Boundaryless] in
private lemma lieCorrectionZeroMixedConnectionExpansion_apply (g₀ g₁ gB : SmoothRiemannianMetric I M) (x : M)
    (D : Tensor0SSpace 2 I x) :
    (show Tensor0SSpace 2 I x →L[ℝ] Tensor0SSpace 2 I x from
      (lieCorrectionZeroMixedConnectionExpansion (I := I) (M := M) g₀ g₁ gB).toSection x) D =
      lieCorrectionZeroMixedConnectionFib (I := I) g₀ g₁ gB x D := by
  have h₁ :
      (show Tensor0SSpace 2 I x →L[ℝ] Tensor0SSpace 2 I x from
        (lieCorrectionZeroMixedConnectionExpansion (I := I) (M := M) g₀ g₁ gB).toSection x) D =
      (2 : ℝ) •
        ((show Tensor0SSpace 2 I x →L[ℝ] Tensor0SSpace 2 I x from
          (lieCorrectionZeroMixedConnectionHalfExpansion (I := I) (M := M) g₀ g₁ gB
            lieCorrectionZeroMixedConnectionPermutationCycleZeroTwoOne).toSection x) D +
        (show Tensor0SSpace 2 I x →L[ℝ] Tensor0SSpace 2 I x from
          (lieCorrectionZeroMixedConnectionHalfExpansion (I := I) (M := M) g₀ g₁ gB
            (lieCorrectionZeroMixedConnectionTraceOutputSwapPermutation * lieCorrectionZeroMixedConnectionPermutationCycleZeroTwoOne)).toSection x) D) := rfl
  rw [h₁]
  rw [lieCorrectionZeroMixedConnectionHalfExpansion_apply (I := I) (M := M) g₀ g₁ gB lieCorrectionZeroMixedConnectionPermutationCycleZeroTwoOne x D]
  rw [lieCorrectionZeroMixedConnectionHalfExpansion_apply (I := I) (M := M) g₀ g₁ gB
    (lieCorrectionZeroMixedConnectionTraceOutputSwapPermutation * lieCorrectionZeroMixedConnectionPermutationCycleZeroTwoOne) x D]
  rw [← lieCorrectionZeroMixedConnection_trace_output_swap (I := I) (M := M) g₁ lieCorrectionZeroMixedConnectionPermutationCycleZeroTwoOne x _]
  rw [show lieCorrectionZeroMixedConnectionFib (I := I) g₀ g₁ gB x D =
      (2 : ℝ) • (lieCorrectionZeroMixedConnectionHalfFib (I := I) g₀ g₁ gB x D +
        domDomCongrFibRank (I := I) 2 (Equiv.swap 0 1) x
          (lieCorrectionZeroMixedConnectionHalfFib (I := I) g₀ g₁ gB x D)) from by
    rw [lieCorrectionZeroMixedConnectionFib, smul_apply,
      add_apply, ContinuousLinearMap.comp_apply]]
  apply congrArg (fun Z : Tensor0SSpace 2 I x ↦ (2 : ℝ) • Z)
  apply congrArg₂ (fun A B : Tensor0SSpace 2 I x ↦ A + B)
  · simp only [lieCorrectionZeroMixedConnectionHalfFib,
      ContinuousLinearMap.comp_apply]
  · apply congrArg
    simp only [lieCorrectionZeroMixedConnectionHalfFib,
      ContinuousLinearMap.comp_apply]

omit [NeZero (Module.finrank ℝ E)] [SigmaCompactSpace M] in
omit [I.Boundaryless] in
theorem lieCorrectionZeroMixedConnection_eq_expansion (g₀ g₁ gB : SmoothRiemannianMetric I M) :
    lieCorrectionZeroMixedConnection (I := I) (M := M) g₀ g₁ gB =
      lieCorrectionZeroMixedConnectionExpansion (I := I) (M := M) g₀ g₁ gB := by
  apply SmoothCcTensor.ext
  apply ContMDiffSection.ext
  intro x
  apply ContinuousLinearMap.ext
  intro D
  change lieCorrectionZeroMixedConnectionFib (I := I) g₀ g₁ gB x D = _
  exact (lieCorrectionZeroMixedConnectionExpansion_apply (I := I) (M := M) g₀ g₁ gB x D).symm

def lieCorrectionZeroMixedConnectionBackgroundDifferenceCoefficient (g₀ g₁ gB : SmoothRiemannianMetric I M) :
    SmoothCcTensor g₀ 0 3 :=
  metricConnectionDifferenceLoweredCoefficient (I := I) (M := M) g₀ g₁ gB -
    metricConnectionDifferenceLoweredCoefficient (I := I) (M := M) g₀ g₁ g₀

def lieCorrectionZeroMixedConnectionBackgroundDifferenceHalfExpansion (g₀ g₁ gB : SmoothRiemannianMetric I M)
    (σ : Equiv.Perm (Fin 4)) : SmoothCcTensor g₀ 2 2 :=
  ccOperatorFieldComp (I := I) (M := M) g₀ 2 4 2
    (reindexedPureTrace (I := I) (M := M) g₀ g₁ 2 σ)
    (ccOperatorFieldComp (I := I) (M := M) g₀ 2 6 4
      (reindexedPureTrace (I := I) (M := M) g₀ g₁ 4 lieCorrectionZeroMixedConnectionPermutationCycleZeroTwoThreeOne)
      (ccOperatorFieldComp (I := I) (M := M) g₀ 2 3 6
        (slotExtendIter (I := I) (M := M) g₀ 0 3 3
          (lieCorrectionZeroMixedConnectionBackgroundDifferenceCoefficient (I := I) (M := M) g₀ g₁ gB))
        (ccOperatorFieldComp (I := I) (M := M) g₀ 2 5 3
          (reindexedPureTrace (I := I) (M := M) g₀ g₁ 3 lieCorrectionZeroMixedConnectionPermutationCycleZeroOneFour)
          (slotExtendIter (I := I) (M := M) g₀ 0 3 2
            (metricConnectionDifferenceLoweredCoefficient (I := I) (M := M) g₀ g₁ g₀)))))

omit [NeZero (Module.finrank ℝ E)] in
omit [I.Boundaryless] in
omit [SigmaCompactSpace M] in
theorem lieCorrectionZeroMixedConnectionHalfExpansion_sub_eq_backgroundDifferenceHalfExpansion
    (g₀ g₁ gB : SmoothRiemannianMetric I M)
    (σ : Equiv.Perm (Fin 4)) :
    lieCorrectionZeroMixedConnectionHalfExpansion (I := I) (M := M) g₀ g₁ gB σ -
        lieCorrectionZeroMixedConnectionHalfExpansion (I := I) (M := M) g₀ g₁ g₀ σ =
      lieCorrectionZeroMixedConnectionBackgroundDifferenceHalfExpansion (I := I) (M := M) g₀ g₁ gB σ := by
  unfold lieCorrectionZeroMixedConnectionHalfExpansion lieCorrectionZeroMixedConnectionBackgroundDifferenceHalfExpansion lieCorrectionZeroMixedConnectionBackgroundDifferenceCoefficient
  rw [← operatorFieldComposition_sub_right, ← operatorFieldComposition_sub_right,
    ← operatorFieldComposition_sub_left,
    ← DifferentialGeometry.Analysis.Spectral.slotExtendIter_sub]

omit [NeZero (Module.finrank ℝ E)] in
omit [I.Boundaryless] in
omit [SigmaCompactSpace M] in
theorem lieCorrectionZeroMixedConnection_sub_reference_eq_backgroundDifferenceExpansion
    (g₀ g₁ gB : SmoothRiemannianMetric I M) :
    lieCorrectionZeroMixedConnection (I := I) (M := M) g₀ g₁ gB -
        lieCorrectionZeroMixedConnection (I := I) (M := M) g₀ g₁ g₀ =
      (2 : ℝ) •
        (lieCorrectionZeroMixedConnectionBackgroundDifferenceHalfExpansion (I := I) (M := M) g₀ g₁ gB lieCorrectionZeroMixedConnectionPermutationCycleZeroTwoOne +
          lieCorrectionZeroMixedConnectionBackgroundDifferenceHalfExpansion (I := I) (M := M) g₀ g₁ gB
            (lieCorrectionZeroMixedConnectionTraceOutputSwapPermutation * lieCorrectionZeroMixedConnectionPermutationCycleZeroTwoOne)) := by
  rw [lieCorrectionZeroMixedConnection_eq_expansion (I := I) (M := M) g₀ g₁ gB,
    lieCorrectionZeroMixedConnection_eq_expansion (I := I) (M := M) g₀ g₁ g₀]
  have h0 := lieCorrectionZeroMixedConnectionHalfExpansion_sub_eq_backgroundDifferenceHalfExpansion (I := I) (M := M) g₀ g₁ gB lieCorrectionZeroMixedConnectionPermutationCycleZeroTwoOne
  have h1 := lieCorrectionZeroMixedConnectionHalfExpansion_sub_eq_backgroundDifferenceHalfExpansion (I := I) (M := M) g₀ g₁ gB
    (lieCorrectionZeroMixedConnectionTraceOutputSwapPermutation * lieCorrectionZeroMixedConnectionPermutationCycleZeroTwoOne)
  simp only [lieCorrectionZeroMixedConnectionExpansion]
  rw [show
      (2 : ℝ) •
          (lieCorrectionZeroMixedConnectionHalfExpansion (I := I) (M := M) g₀ g₁ gB lieCorrectionZeroMixedConnectionPermutationCycleZeroTwoOne +
            lieCorrectionZeroMixedConnectionHalfExpansion (I := I) (M := M) g₀ g₁ gB
              (lieCorrectionZeroMixedConnectionTraceOutputSwapPermutation * lieCorrectionZeroMixedConnectionPermutationCycleZeroTwoOne)) -
        (2 : ℝ) •
          (lieCorrectionZeroMixedConnectionHalfExpansion (I := I) (M := M) g₀ g₁ g₀ lieCorrectionZeroMixedConnectionPermutationCycleZeroTwoOne +
            lieCorrectionZeroMixedConnectionHalfExpansion (I := I) (M := M) g₀ g₁ g₀
              (lieCorrectionZeroMixedConnectionTraceOutputSwapPermutation * lieCorrectionZeroMixedConnectionPermutationCycleZeroTwoOne)) =
        (2 : ℝ) •
          ((lieCorrectionZeroMixedConnectionHalfExpansion (I := I) (M := M) g₀ g₁ gB lieCorrectionZeroMixedConnectionPermutationCycleZeroTwoOne -
              lieCorrectionZeroMixedConnectionHalfExpansion (I := I) (M := M) g₀ g₁ g₀ lieCorrectionZeroMixedConnectionPermutationCycleZeroTwoOne) +
            (lieCorrectionZeroMixedConnectionHalfExpansion (I := I) (M := M) g₀ g₁ gB
                (lieCorrectionZeroMixedConnectionTraceOutputSwapPermutation * lieCorrectionZeroMixedConnectionPermutationCycleZeroTwoOne) -
              lieCorrectionZeroMixedConnectionHalfExpansion (I := I) (M := M) g₀ g₁ g₀
                (lieCorrectionZeroMixedConnectionTraceOutputSwapPermutation * lieCorrectionZeroMixedConnectionPermutationCycleZeroTwoOne))) by module,
    h0, h1]

end DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral
