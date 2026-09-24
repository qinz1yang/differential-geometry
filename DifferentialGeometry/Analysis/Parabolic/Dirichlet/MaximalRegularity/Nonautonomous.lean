import DifferentialGeometry.Analysis.Parabolic.Dirichlet.MaximalRegularity.SolutionFieldLink
import DifferentialGeometry.Analysis.Integration.Lp.Operator

noncomputable section

open Bundle Manifold MeasureTheory Set Filter
open scoped Manifold Topology ContDiff ENNReal BigOperators
  RealInnerProductSpace InnerProductSpace NNReal

namespace DifferentialGeometry
namespace Analysis
namespace Parabolic
namespace Dirichlet
namespace MaximalRegularity

variable {n : ℕ} [NeZero n]
variable {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanHalfSpace n) M]
  [IsManifold (modelWithCornersEuclideanHalfSpace n) ∞ M]
  [T2Space M] [CompactSpace M]

private abbrev I_half (n : ℕ) [NeZero n] :
    ModelWithCorners ℝ (EuclideanSpace ℝ (Fin n)) (EuclideanHalfSpace n) :=
  modelWithCornersEuclideanHalfSpace n

open DifferentialGeometry.Integral.L2
open DifferentialGeometry.Analysis.Parabolic.TimeSobolev
open DifferentialGeometry.Analysis.Sobolev.Hs

variable {g : SmoothRiemannianMetric (I_half n) M}
variable {a T : ℝ}

def nonautonomousMap (a : ℝ) {T : ℝ} (hT : 0 < T)
    (u₀ : DirichletHs g (a + 1))
    (A₂ : ℝ → DirichletHs g (a + 2) →L[ℝ] DirichletHs g a)
    (hA₂ : ∀ v, AEStronglyMeasurable (fun t => A₂ t v) (timeMeasure T))
    (C₂ : NNReal) (hC₂ : ∀ᵐ t ∂timeMeasure T, ‖A₂ t‖ ≤ (C₂ : ℝ))
    (A₁ : ℝ → DirichletHs g (a + 1) →L[ℝ] DirichletHs g a)
    (hA₁ : ∀ v, AEStronglyMeasurable (fun t => A₁ t v) (timeMeasure T))
    (C₁ : NNReal) (hC₁ : ∀ᵐ t ∂timeMeasure T, ‖A₁ t‖ ≤ (C₁ : ℝ)) :
    timeL2 (DirichletHs g a) T → timeL2 (DirichletHs g a) T :=
  fun f =>
    Lp.multiplicationOperator (p := 2) A₂ hA₂ C₂ hC₂
        (maximalRegularityDuhamelSolField a hT u₀ f) +
      Lp.multiplicationOperator (p := 2) A₁ hA₁ C₁ hC₁
        (maximalRegularityDuhamelSolFieldHa1 a hT u₀ f)

theorem nonautonomousMap_apply (hT : 0 < T)
    (u₀ : DirichletHs g (a + 1))
    (A₂ : ℝ → DirichletHs g (a + 2) →L[ℝ] DirichletHs g a)
    (hA₂ : ∀ v, AEStronglyMeasurable (fun t => A₂ t v) (timeMeasure T))
    (C₂ : NNReal) (hC₂ : ∀ᵐ t ∂timeMeasure T, ‖A₂ t‖ ≤ (C₂ : ℝ))
    (A₁ : ℝ → DirichletHs g (a + 1) →L[ℝ] DirichletHs g a)
    (hA₁ : ∀ v, AEStronglyMeasurable (fun t => A₁ t v) (timeMeasure T))
    (C₁ : NNReal) (hC₁ : ∀ᵐ t ∂timeMeasure T, ‖A₁ t‖ ≤ (C₁ : ℝ))
    (f : timeL2 (DirichletHs g a) T) :
    nonautonomousMap a hT u₀ A₂ hA₂ C₂ hC₂
        A₁ hA₁ C₁ hC₁ f =
      Lp.multiplicationOperator (p := 2) A₂ hA₂ C₂ hC₂
          (maximalRegularityDuhamelSolField a hT u₀ f) +
        Lp.multiplicationOperator (p := 2) A₁ hA₁ C₁ hC₁
          (maximalRegularityDuhamelSolFieldHa1 a hT u₀ f) :=
  rfl

theorem nonautonomousMap_dist_le
    (hT : 0 < T) (hT1 : T ≤ 1)
    (u₀ : DirichletHs g (a + 1))
    (A₂ : ℝ → DirichletHs g (a + 2) →L[ℝ] DirichletHs g a)
    (hA₂ : ∀ v, AEStronglyMeasurable (fun t => A₂ t v) (timeMeasure T))
    (C₂ : NNReal) (hC₂ : ∀ᵐ t ∂timeMeasure T, ‖A₂ t‖ ≤ (C₂ : ℝ))
    (A₁ : ℝ → DirichletHs g (a + 1) →L[ℝ] DirichletHs g a)
    (hA₁ : ∀ v, AEStronglyMeasurable (fun t => A₁ t v) (timeMeasure T))
    (C₁ : NNReal) (hC₁ : ∀ᵐ t ∂timeMeasure T, ‖A₁ t‖ ≤ (C₁ : ℝ))
    (f f' : timeL2 (DirichletHs g a) T) :
    dist (nonautonomousMap a hT u₀ A₂ hA₂ C₂ hC₂
        A₁ hA₁ C₁ hC₁ f)
      (nonautonomousMap a hT u₀ A₂ hA₂ C₂ hC₂
        A₁ hA₁ C₁ hC₁ f') ≤
      ((C₂ : ℝ) * (1 + T) + (C₁ : ℝ) * (2 * Real.sqrt T)) *
        dist f f' := by
  have hfield₂ := maximalRegularityDuhamelSolField_norm_sub_le
    (a := a) hT u₀ f f'
  have hfield₁ := maximalRegularityDuhamelSolFieldHa1_norm_sub_le
    (a := a) hT hT1 u₀ f f'
  have h₂ :
      ‖Lp.multiplicationOperator (p := 2) A₂ hA₂ C₂ hC₂
            (maximalRegularityDuhamelSolField a hT u₀ f) -
          Lp.multiplicationOperator (p := 2) A₂ hA₂ C₂ hC₂
            (maximalRegularityDuhamelSolField a hT u₀ f')‖ ≤
        (C₂ : ℝ) * (1 + T) * ‖f - f'‖ := by
    rw [← map_sub]
    calc
      ‖Lp.multiplicationOperator (p := 2) A₂ hA₂ C₂ hC₂
          (maximalRegularityDuhamelSolField a hT u₀ f -
            maximalRegularityDuhamelSolField a hT u₀ f')‖ ≤
          ‖Lp.multiplicationOperator (p := 2) A₂ hA₂ C₂ hC₂‖ *
            ‖maximalRegularityDuhamelSolField a hT u₀ f -
              maximalRegularityDuhamelSolField a hT u₀ f'‖ :=
        (Lp.multiplicationOperator (p := 2) A₂ hA₂ C₂ hC₂).le_opNorm _
      _ ≤ (C₂ : ℝ) *
            ‖maximalRegularityDuhamelSolField a hT u₀ f -
              maximalRegularityDuhamelSolField a hT u₀ f'‖ :=
        mul_le_mul_of_nonneg_right
          (Lp.multiplicationOperator_norm_le (p := 2) A₂ hA₂ C₂ hC₂) (norm_nonneg _)
      _ ≤ (C₂ : ℝ) * ((1 + T) * ‖f - f'‖) :=
        mul_le_mul_of_nonneg_left hfield₂ C₂.coe_nonneg
      _ = (C₂ : ℝ) * (1 + T) * ‖f - f'‖ := by ring
  have h₁ :
      ‖Lp.multiplicationOperator (p := 2) A₁ hA₁ C₁ hC₁
            (maximalRegularityDuhamelSolFieldHa1 a hT u₀ f) -
          Lp.multiplicationOperator (p := 2) A₁ hA₁ C₁ hC₁
            (maximalRegularityDuhamelSolFieldHa1 a hT u₀ f')‖ ≤
        (C₁ : ℝ) * (2 * Real.sqrt T) * ‖f - f'‖ := by
    rw [← map_sub]
    calc
      ‖Lp.multiplicationOperator (p := 2) A₁ hA₁ C₁ hC₁
          (maximalRegularityDuhamelSolFieldHa1 a hT u₀ f -
            maximalRegularityDuhamelSolFieldHa1 a hT u₀ f')‖ ≤
          ‖Lp.multiplicationOperator (p := 2) A₁ hA₁ C₁ hC₁‖ *
            ‖maximalRegularityDuhamelSolFieldHa1 a hT u₀ f -
              maximalRegularityDuhamelSolFieldHa1 a hT u₀ f'‖ :=
        (Lp.multiplicationOperator (p := 2) A₁ hA₁ C₁ hC₁).le_opNorm _
      _ ≤ (C₁ : ℝ) *
            ‖maximalRegularityDuhamelSolFieldHa1 a hT u₀ f -
              maximalRegularityDuhamelSolFieldHa1 a hT u₀ f'‖ :=
        mul_le_mul_of_nonneg_right
          (Lp.multiplicationOperator_norm_le (p := 2) A₁ hA₁ C₁ hC₁) (norm_nonneg _)
      _ ≤ (C₁ : ℝ) * ((2 * Real.sqrt T) * ‖f - f'‖) :=
        mul_le_mul_of_nonneg_left hfield₁ C₁.coe_nonneg
      _ = (C₁ : ℝ) * (2 * Real.sqrt T) * ‖f - f'‖ := by ring
  rw [dist_eq_norm, dist_eq_norm]
  unfold nonautonomousMap
  have hsplit :
      (Lp.multiplicationOperator (p := 2) A₂ hA₂ C₂ hC₂
            (maximalRegularityDuhamelSolField a hT u₀ f) +
          Lp.multiplicationOperator (p := 2) A₁ hA₁ C₁ hC₁
            (maximalRegularityDuhamelSolFieldHa1 a hT u₀ f)) -
        (Lp.multiplicationOperator (p := 2) A₂ hA₂ C₂ hC₂
            (maximalRegularityDuhamelSolField a hT u₀ f') +
          Lp.multiplicationOperator (p := 2) A₁ hA₁ C₁ hC₁
            (maximalRegularityDuhamelSolFieldHa1 a hT u₀ f')) =
      (Lp.multiplicationOperator (p := 2) A₂ hA₂ C₂ hC₂
            (maximalRegularityDuhamelSolField a hT u₀ f) -
          Lp.multiplicationOperator (p := 2) A₂ hA₂ C₂ hC₂
            (maximalRegularityDuhamelSolField a hT u₀ f')) +
        (Lp.multiplicationOperator (p := 2) A₁ hA₁ C₁ hC₁
            (maximalRegularityDuhamelSolFieldHa1 a hT u₀ f) -
          Lp.multiplicationOperator (p := 2) A₁ hA₁ C₁ hC₁
            (maximalRegularityDuhamelSolFieldHa1 a hT u₀ f')) := by
    abel
  rw [hsplit]
  calc
    ‖(Lp.multiplicationOperator (p := 2) A₂ hA₂ C₂ hC₂
          (maximalRegularityDuhamelSolField a hT u₀ f) -
        Lp.multiplicationOperator (p := 2) A₂ hA₂ C₂ hC₂
          (maximalRegularityDuhamelSolField a hT u₀ f')) +
      (Lp.multiplicationOperator (p := 2) A₁ hA₁ C₁ hC₁
          (maximalRegularityDuhamelSolFieldHa1 a hT u₀ f) -
        Lp.multiplicationOperator (p := 2) A₁ hA₁ C₁ hC₁
          (maximalRegularityDuhamelSolFieldHa1 a hT u₀ f'))‖ ≤
        ‖Lp.multiplicationOperator (p := 2) A₂ hA₂ C₂ hC₂
            (maximalRegularityDuhamelSolField a hT u₀ f) -
          Lp.multiplicationOperator (p := 2) A₂ hA₂ C₂ hC₂
            (maximalRegularityDuhamelSolField a hT u₀ f')‖ +
        ‖Lp.multiplicationOperator (p := 2) A₁ hA₁ C₁ hC₁
            (maximalRegularityDuhamelSolFieldHa1 a hT u₀ f) -
          Lp.multiplicationOperator (p := 2) A₁ hA₁ C₁ hC₁
            (maximalRegularityDuhamelSolFieldHa1 a hT u₀ f')‖ :=
      norm_add_le _ _
    _ ≤ (C₂ : ℝ) * (1 + T) * ‖f - f'‖ +
        (C₁ : ℝ) * (2 * Real.sqrt T) * ‖f - f'‖ :=
      add_le_add h₂ h₁
    _ = ((C₂ : ℝ) * (1 + T) +
          (C₁ : ℝ) * (2 * Real.sqrt T)) * ‖f - f'‖ := by ring

theorem nonautonomousMap_contractingWith
    (hT : 0 < T) (hT1 : T ≤ 1)
    (u₀ : DirichletHs g (a + 1))
    (A₂ : ℝ → DirichletHs g (a + 2) →L[ℝ] DirichletHs g a)
    (hA₂ : ∀ v, AEStronglyMeasurable (fun t => A₂ t v) (timeMeasure T))
    (C₂ : NNReal) (hC₂ : ∀ᵐ t ∂timeMeasure T, ‖A₂ t‖ ≤ (C₂ : ℝ))
    (A₁ : ℝ → DirichletHs g (a + 1) →L[ℝ] DirichletHs g a)
    (hA₁ : ∀ v, AEStronglyMeasurable (fun t => A₁ t v) (timeMeasure T))
    (C₁ : NNReal) (hC₁ : ∀ᵐ t ∂timeMeasure T, ‖A₁ t‖ ≤ (C₁ : ℝ))
    (hsmall :
      (C₂ : ℝ) * (1 + T) + (C₁ : ℝ) * (2 * Real.sqrt T) < 1) :
    ContractingWith
      (NNReal.mk
        ((C₂ : ℝ) * (1 + T) + (C₁ : ℝ) * (2 * Real.sqrt T))
        (add_nonneg
          (mul_nonneg C₂.coe_nonneg (by linarith [hT.le]))
          (mul_nonneg C₁.coe_nonneg (by positivity))))
      (nonautonomousMap a hT u₀ A₂ hA₂ C₂ hC₂
        A₁ hA₁ C₁ hC₁) := by
  refine ⟨?_, ?_⟩
  · rw [← NNReal.coe_lt_coe]
    simpa only [NNReal.coe_mk, NNReal.coe_one] using hsmall
  · refine LipschitzWith.of_dist_le_mul (fun f f' => ?_)
    simpa only [NNReal.coe_mk] using
      nonautonomousMap_dist_le hT hT1 u₀ A₂ hA₂ C₂ hC₂
        A₁ hA₁ C₁ hC₁ f f'

theorem nonautonomous_forced_timeH1_exists
    (hT : 0 < T) (hT1 : T ≤ 1)
    (u₀ : DirichletHs g (a + 1))
    (A₂ : ℝ → DirichletHs g (a + 2) →L[ℝ] DirichletHs g a)
    (hA₂ : ∀ v, AEStronglyMeasurable (fun t => A₂ t v) (timeMeasure T))
    (C₂ : NNReal) (hC₂ : ∀ᵐ t ∂timeMeasure T, ‖A₂ t‖ ≤ (C₂ : ℝ))
    (A₁ : ℝ → DirichletHs g (a + 1) →L[ℝ] DirichletHs g a)
    (hA₁ : ∀ v, AEStronglyMeasurable (fun t => A₁ t v) (timeMeasure T))
    (C₁ : NNReal) (hC₁ : ∀ᵐ t ∂timeMeasure T, ‖A₁ t‖ ≤ (C₁ : ℝ))
    (f₀ : timeL2 (DirichletHs g a) T)
    (hsmall :
      (C₂ : ℝ) * (1 + T) + (C₁ : ℝ) * (2 * Real.sqrt T) < 1) :
    ∃ (u : MaximalRegularitySolutionSpace (g := g) a T)
      (f : timeL2 (DirichletHs g a) T),
      u = maximalRegularityDuhamelMap a hT u₀ f ∧
      f = Lp.multiplicationOperator (p := 2) A₂ hA₂ C₂ hC₂
            (maximalRegularityDuhamelSolField a hT u₀ f) +
          Lp.multiplicationOperator (p := 2) A₁ hA₁ C₁ hC₁
            (maximalRegularityDuhamelSolFieldHa1 a hT u₀ f) + f₀ ∧
      TimeSobolev.timeH1.trace0 _ T u =
        dirichletHsInclusion (show a ≤ a + 1 by linarith) u₀ ∧
      TimeSobolev.timeH1.timeDeriv _ T u =
        timeDirichletHsLaplacian g a
            (maximalRegularityDuhamelSolField a hT u₀ f) +
          (Lp.multiplicationOperator (p := 2) A₂ hA₂ C₂ hC₂
              (maximalRegularityDuhamelSolField a hT u₀ f) +
            Lp.multiplicationOperator (p := 2) A₁ hA₁ C₁ hC₁
              (maximalRegularityDuhamelSolFieldHa1 a hT u₀ f) + f₀) ∧
      (fun t => dirichletHsInclusion (show a ≤ a + 2 by linarith)
          (maximalRegularityDuhamelSolField a hT u₀ f t))
        =ᵐ[timeMeasure T] u.toFun ∧
      (fun t => dirichletHsInclusion (show a ≤ a + 1 by linarith)
          (maximalRegularityDuhamelSolFieldHa1 a hT u₀ f t))
        =ᵐ[timeMeasure T] u.toFun := by
  let K : NNReal :=
    ⟨(C₂ : ℝ) * (1 + T) + (C₁ : ℝ) * (2 * Real.sqrt T),
      add_nonneg
        (mul_nonneg C₂.coe_nonneg (by linarith [hT.le]))
        (mul_nonneg C₁.coe_nonneg (by positivity))⟩
  let F : timeL2 (DirichletHs g a) T → timeL2 (DirichletHs g a) T :=
    fun f => nonautonomousMap a hT u₀ A₂ hA₂ C₂ hC₂
      A₁ hA₁ C₁ hC₁ f + f₀
  have hbase := nonautonomousMap_contractingWith
    (a := a) hT hT1 u₀ A₂ hA₂ C₂ hC₂
      A₁ hA₁ C₁ hC₁ hsmall
  have hcontr : ContractingWith K F := by
    refine ⟨hbase.1, ?_⟩
    refine LipschitzWith.of_dist_le_mul (fun f f' => ?_)
    change dist
      (nonautonomousMap a hT u₀ A₂ hA₂ C₂ hC₂
          A₁ hA₁ C₁ hC₁ f + f₀)
      (nonautonomousMap a hT u₀ A₂ hA₂ C₂ hC₂
          A₁ hA₁ C₁ hC₁ f' + f₀) ≤
        (K : ℝ) * dist f f'
    rw [dist_add_right]
    exact hbase.2.dist_le_mul f f'
  set fstar := ContractingWith.fixedPoint F hcontr with hfstar_def
  have hfix : F fstar = fstar :=
    ContractingWith.fixedPoint_isFixedPt hcontr
  have hfstar : fstar =
      Lp.multiplicationOperator (p := 2) A₂ hA₂ C₂ hC₂
          (maximalRegularityDuhamelSolField a hT u₀ fstar) +
        Lp.multiplicationOperator (p := 2) A₁ hA₁ C₁ hC₁
          (maximalRegularityDuhamelSolFieldHa1 a hT u₀ fstar) + f₀ := by
    simpa only [F, nonautonomousMap] using hfix.symm
  refine ⟨maximalRegularityDuhamelMap a hT u₀ fstar, fstar,
    rfl, hfstar, maximalRegularityDuhamelMap_trace0 hT u₀ fstar, ?_,
    maximalRegularityDuhamelSolField_toFun_ae hT u₀ fstar,
    maximalRegularityDuhamelSolFieldHa1_toFun_ae hT hT1 u₀ fstar⟩
  rw [maximalRegularityDuhamelMap_timeDeriv_eq hT u₀ fstar]
  exact congrArg₂ (fun x y => x + y) rfl hfstar

theorem nonautonomous_forcing_unique
    (hT : 0 < T) (hT1 : T ≤ 1)
    (u₀ : DirichletHs g (a + 1))
    (A₂ : ℝ → DirichletHs g (a + 2) →L[ℝ] DirichletHs g a)
    (hA₂ : ∀ v, AEStronglyMeasurable (fun t => A₂ t v) (timeMeasure T))
    (C₂ : NNReal) (hC₂ : ∀ᵐ t ∂timeMeasure T, ‖A₂ t‖ ≤ (C₂ : ℝ))
    (A₁ : ℝ → DirichletHs g (a + 1) →L[ℝ] DirichletHs g a)
    (hA₁ : ∀ v, AEStronglyMeasurable (fun t => A₁ t v) (timeMeasure T))
    (C₁ : NNReal) (hC₁ : ∀ᵐ t ∂timeMeasure T, ‖A₁ t‖ ≤ (C₁ : ℝ))
    (f₀ : timeL2 (DirichletHs g a) T)
    (hsmall :
      (C₂ : ℝ) * (1 + T) + (C₁ : ℝ) * (2 * Real.sqrt T) < 1)
    {f f' : timeL2 (DirichletHs g a) T}
    (hf : f = nonautonomousMap a hT u₀ A₂ hA₂ C₂ hC₂
      A₁ hA₁ C₁ hC₁ f + f₀)
    (hf' : f' = nonautonomousMap a hT u₀ A₂ hA₂ C₂ hC₂
      A₁ hA₁ C₁ hC₁ f' + f₀) :
    f = f' := by
  let K : NNReal :=
    ⟨(C₂ : ℝ) * (1 + T) + (C₁ : ℝ) * (2 * Real.sqrt T),
      add_nonneg
        (mul_nonneg C₂.coe_nonneg (by linarith [hT.le]))
        (mul_nonneg C₁.coe_nonneg (by positivity))⟩
  let F : timeL2 (DirichletHs g a) T → timeL2 (DirichletHs g a) T :=
    fun q => nonautonomousMap a hT u₀ A₂ hA₂ C₂ hC₂
      A₁ hA₁ C₁ hC₁ q + f₀
  have hbase := nonautonomousMap_contractingWith
    (a := a) hT hT1 u₀ A₂ hA₂ C₂ hC₂
      A₁ hA₁ C₁ hC₁ hsmall
  have hcontr : ContractingWith K F := by
    refine ⟨hbase.1, ?_⟩
    refine LipschitzWith.of_dist_le_mul (fun q q' => ?_)
    change dist
      (nonautonomousMap a hT u₀ A₂ hA₂ C₂ hC₂
          A₁ hA₁ C₁ hC₁ q + f₀)
      (nonautonomousMap a hT u₀ A₂ hA₂ C₂ hC₂
          A₁ hA₁ C₁ hC₁ q' + f₀) ≤
        (K : ℝ) * dist q q'
    rw [dist_add_right]
    exact hbase.2.dist_le_mul q q'
  have hfix : Function.IsFixedPt F f := by
    change F f = f
    simpa only [F] using hf.symm
  have hfix' : Function.IsFixedPt F f' := by
    change F f' = f'
    simpa only [F] using hf'.symm
  exact hcontr.fixedPoint_unique' hfix hfix'

theorem nonautonomous_timeH1_exists
    (hT : 0 < T) (hT1 : T ≤ 1)
    (u₀ : DirichletHs g (a + 1))
    (A₂ : ℝ → DirichletHs g (a + 2) →L[ℝ] DirichletHs g a)
    (hA₂ : ∀ v, AEStronglyMeasurable (fun t => A₂ t v) (timeMeasure T))
    (C₂ : NNReal) (hC₂ : ∀ᵐ t ∂timeMeasure T, ‖A₂ t‖ ≤ (C₂ : ℝ))
    (A₁ : ℝ → DirichletHs g (a + 1) →L[ℝ] DirichletHs g a)
    (hA₁ : ∀ v, AEStronglyMeasurable (fun t => A₁ t v) (timeMeasure T))
    (C₁ : NNReal) (hC₁ : ∀ᵐ t ∂timeMeasure T, ‖A₁ t‖ ≤ (C₁ : ℝ))
    (hsmall :
      (C₂ : ℝ) * (1 + T) + (C₁ : ℝ) * (2 * Real.sqrt T) < 1) :
    ∃ (u : MaximalRegularitySolutionSpace (g := g) a T)
      (f : timeL2 (DirichletHs g a) T),
      u = maximalRegularityDuhamelMap a hT u₀ f ∧
      f = Lp.multiplicationOperator (p := 2) A₂ hA₂ C₂ hC₂
            (maximalRegularityDuhamelSolField a hT u₀ f) +
          Lp.multiplicationOperator (p := 2) A₁ hA₁ C₁ hC₁
            (maximalRegularityDuhamelSolFieldHa1 a hT u₀ f) ∧
      TimeSobolev.timeH1.trace0 _ T u =
        dirichletHsInclusion (show a ≤ a + 1 by linarith) u₀ ∧
      TimeSobolev.timeH1.timeDeriv _ T u =
        timeDirichletHsLaplacian g a
            (maximalRegularityDuhamelSolField a hT u₀ f) +
          (Lp.multiplicationOperator (p := 2) A₂ hA₂ C₂ hC₂
              (maximalRegularityDuhamelSolField a hT u₀ f) +
            Lp.multiplicationOperator (p := 2) A₁ hA₁ C₁ hC₁
              (maximalRegularityDuhamelSolFieldHa1 a hT u₀ f)) ∧
      (fun t => dirichletHsInclusion (show a ≤ a + 2 by linarith)
          (maximalRegularityDuhamelSolField a hT u₀ f t))
        =ᵐ[timeMeasure T] u.toFun ∧
      (fun t => dirichletHsInclusion (show a ≤ a + 1 by linarith)
          (maximalRegularityDuhamelSolFieldHa1 a hT u₀ f t))
        =ᵐ[timeMeasure T] u.toFun := by
  obtain ⟨u, f, hu, hf, htrace, heq, hfield₂, hfield₁⟩ :=
    nonautonomous_forced_timeH1_exists
      (a := a) hT hT1 u₀ A₂ hA₂ C₂ hC₂
        A₁ hA₁ C₁ hC₁ 0 hsmall
  refine ⟨u, f, hu, ?_, htrace, ?_, hfield₂, hfield₁⟩
  · simpa using hf
  · simpa using heq

theorem exists_nonautonomous_solution
    (hT : 0 < T) (hT1 : T ≤ 1)
    (u₀ : DirichletHs g (a + 1))
    (A₂ : ℝ → DirichletHs g (a + 2) →L[ℝ] DirichletHs g a)
    (hA₂ : ∀ v, AEStronglyMeasurable (fun t => A₂ t v) (timeMeasure T))
    (C₂ : NNReal) (hC₂ : ∀ᵐ t ∂timeMeasure T, ‖A₂ t‖ ≤ (C₂ : ℝ))
    (A₁ : ℝ → DirichletHs g (a + 1) →L[ℝ] DirichletHs g a)
    (hA₁ : ∀ v, AEStronglyMeasurable (fun t => A₁ t v) (timeMeasure T))
    (C₁ : NNReal) (hC₁ : ∀ᵐ t ∂timeMeasure T, ‖A₁ t‖ ≤ (C₁ : ℝ))
    (f₀ : timeL2 (DirichletHs g a) T)
    (hsmall : (C₂ : ℝ) * (1 + T) + (C₁ : ℝ) * (2 * Real.sqrt T) < 1) :
    ∃ (u : timeH1 (DirichletHs g a) T)
      (U₂ : timeL2 (DirichletHs g (a + 2)) T)
      (U₁ : timeL2 (DirichletHs g (a + 1)) T),
      u.initial = dirichletHsInclusion (show a ≤ a + 1 by linarith) u₀ ∧
      (fun t => dirichletHsInclusion (show a ≤ a + 2 by linarith) (U₂ t))
        =ᵐ[timeMeasure T] u.toFun ∧
      (fun t => dirichletHsInclusion (show a ≤ a + 1 by linarith) (U₁ t))
        =ᵐ[timeMeasure T] u.toFun ∧
      u.deriv =ᵐ[timeMeasure T] fun t =>
        dirichletHsLaplacian g a (U₂ t) + A₂ t (U₂ t) + A₁ t (U₁ t) + f₀ t := by
  obtain ⟨u, f, hu, hf, htrace, heq, hfield₂, hfield₁⟩ :=
    nonautonomous_forced_timeH1_exists hT hT1 u₀ A₂ hA₂ C₂ hC₂
      A₁ hA₁ C₁ hC₁ f₀ hsmall
  let U₂ := maximalRegularityDuhamelSolField a hT u₀ f
  let U₁ := maximalRegularityDuhamelSolFieldHa1 a hT u₀ f
  let B₂ := Lp.multiplicationOperator (p := 2) A₂ hA₂ C₂ hC₂ U₂
  let B₁ := Lp.multiplicationOperator (p := 2) A₁ hA₁ C₁ hC₁ U₁
  refine ⟨u, U₂, U₁, htrace, hfield₂, hfield₁, ?_⟩
  change u.deriv = timeDirichletHsLaplacian g a U₂ + (B₂ + B₁ + f₀) at heq
  filter_upwards [Lp.coeFn_add (timeDirichletHsLaplacian g a U₂) (B₂ + B₁ + f₀),
    Lp.coeFn_add (B₂ + B₁) f₀, Lp.coeFn_add B₂ B₁,
    timeDirichletHsLaplacian_coeFn U₂,
    Lp.multiplicationOperator_apply_ae A₂ hA₂ C₂ hC₂ U₂,
    Lp.multiplicationOperator_apply_ae A₁ hA₁ C₁ hC₁ U₁] with t hsum hsum₀ hsum₁ hΔ h₂ h₁
  rw [heq, hsum, Pi.add_apply, hsum₀, Pi.add_apply, hsum₁, Pi.add_apply, hΔ]
  change _ + ((Lp.multiplicationOperator A₂ hA₂ C₂ hC₂ U₂ t +
    Lp.multiplicationOperator A₁ hA₁ C₁ hC₁ U₁ t) + _) = _
  rw [h₂, h₁]
  abel

theorem exists_local_nonautonomous_solution
    {T₀ : ℝ} (hT₀ : 0 < T₀)
    (A₂ : ℝ → DirichletHs g (a + 2) →L[ℝ] DirichletHs g a)
    (hA₂ : ∀ v, AEStronglyMeasurable (fun t => A₂ t v) (timeMeasure T₀))
    (C₂ : NNReal) (hC₂ : ∀ᵐ t ∂timeMeasure T₀, ‖A₂ t‖ ≤ (C₂ : ℝ))
    (hsmall : (C₂ : ℝ) < 1)
    (A₁ : ℝ → DirichletHs g (a + 1) →L[ℝ] DirichletHs g a)
    (hA₁ : ∀ v, AEStronglyMeasurable (fun t => A₁ t v) (timeMeasure T₀))
    (C₁ : NNReal) (hC₁ : ∀ᵐ t ∂timeMeasure T₀, ‖A₁ t‖ ≤ (C₁ : ℝ)) :
    ∃ T : ℝ, 0 < T ∧ T ≤ T₀ ∧
      ∀ (u₀ : DirichletHs g (a + 1)) (f₀ : timeL2 (DirichletHs g a) T),
        ∃ (u : timeH1 (DirichletHs g a) T)
          (U₂ : timeL2 (DirichletHs g (a + 2)) T)
          (U₁ : timeL2 (DirichletHs g (a + 1)) T),
          u.initial = dirichletHsInclusion (show a ≤ a + 1 by linarith) u₀ ∧
          (fun t => dirichletHsInclusion (show a ≤ a + 2 by linarith) (U₂ t))
            =ᵐ[timeMeasure T] u.toFun ∧
          (fun t => dirichletHsInclusion (show a ≤ a + 1 by linarith) (U₁ t))
            =ᵐ[timeMeasure T] u.toFun ∧
          u.deriv =ᵐ[timeMeasure T] fun t =>
            dirichletHsLaplacian g a (U₂ t) + A₂ t (U₂ t) + A₁ t (U₁ t) + f₀ t := by
  have hcont : ContinuousAt
      (fun t : ℝ => (C₂ : ℝ) * (1 + t) + (C₁ : ℝ) * (2 * Real.sqrt t)) 0 :=
    (continuousAt_const.mul (continuousAt_const.add continuousAt_id)).add
      (continuousAt_const.mul (continuousAt_const.mul Real.continuous_sqrt.continuousAt))
  have hevent : ∀ᶠ t : ℝ in 𝓝 0,
      (C₂ : ℝ) * (1 + t) + (C₁ : ℝ) * (2 * Real.sqrt t) < 1 :=
    hcont.eventually (gt_mem_nhds (by simpa only [add_zero, Real.sqrt_zero,
      mul_zero, mul_one] using hsmall))
  obtain ⟨ε, hε, he⟩ := Metric.eventually_nhds_iff.mp hevent
  let T := min T₀ (min 1 (ε / 2))
  have hT : 0 < T := lt_min hT₀ (lt_min zero_lt_one (half_pos hε))
  have hTT₀ : T ≤ T₀ := min_le_left _ _
  have hT1 : T ≤ 1 := (min_le_right _ _).trans (min_le_left _ _)
  have hTε : T < ε := ((min_le_right _ _).trans (min_le_right _ _)).trans_lt
    (half_lt_self hε)
  have hμ : timeMeasure T ≤ timeMeasure T₀ :=
    Measure.restrict_mono (Icc_subset_Icc le_rfl hTT₀) le_rfl
  refine ⟨T, hT, hTT₀, fun u₀ f₀ => ?_⟩
  exact exists_nonautonomous_solution hT hT1 u₀ A₂
    (fun v => (hA₂ v).mono_measure hμ) C₂ (ae_mono hμ hC₂) A₁
    (fun v => (hA₁ v).mono_measure hμ) C₁ (ae_mono hμ hC₁) f₀
    (he (by simpa only [Real.dist_eq, sub_zero, abs_of_pos hT] using hTε))

end MaximalRegularity
end Dirichlet
end Parabolic
end Analysis
end DifferentialGeometry
