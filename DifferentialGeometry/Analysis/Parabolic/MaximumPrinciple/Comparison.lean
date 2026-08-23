import DifferentialGeometry.Analysis.Parabolic.MaximumPrinciple.HeatPotentialStrong

set_option autoImplicit false

namespace DifferentialGeometry.Analysis.Parabolic

noncomputable section

open Bundle Set
open DifferentialGeometry.Geometry.Curvature
open scoped Manifold ContDiff

universe u uE uH

variable {E : Type uE} [NormedAddCommGroup E] [NormedSpace Real E]
variable [FiniteDimensional Real E] [CompleteSpace E]
variable {H : Type uH} [TopologicalSpace H]
variable {I : ModelWithCorners Real E H}
variable {M : Type u} [TopologicalSpace M] [ChartedSpace H M]
variable [IsManifold I ∞ M]

omit [CompleteSpace E] in
theorem heat_pot_comparison
    [I.Boundaryless] [SigmaCompactSpace M] [T2Space M] [CompactSpace M]
    [VectorBundle Real E (TangentSpace I : M → Type _)]
    (G : MetricConnectionFamily (I := I) (M := M) Real)
    {T : Real} (hT : 0 ≤ T) (V u v : Real → M → Real)
    (hu : IsHeatPotSubsolutionOn (RealTimeInterval.closed 0 T hT) G V u)
    (hv : IsHeatPotSupersolutionOn (RealTimeInterval.closed 0 T hT) G V v)
    (C : Real)
    (hV : ∀ t ∈ Set.Icc 0 T, ∀ x : M, V t x ≤ C)
    (hinit : ∀ x : M, u 0 x ≤ v 0 x) :
    ∀ t ∈ Set.Icc 0 T, ∀ x : M, u t x ≤ v t x := by
  have hdiff : IsHeatPotSupersolutionOn (RealTimeInterval.closed 0 T hT) G V
      (fun t x => v t x - u t x) :=
    hv.sub hu
  have hnonneg := heat_pot_supersolution_nonneg (I := I) G hT V
    (fun t x => v t x - u t x) hdiff C hV
    (fun x => sub_nonneg.mpr (hinit x))
  intro t ht x
  exact sub_nonneg.mp (hnonneg t ht x)

omit [CompleteSpace E] in
theorem heat_pot_eq_of_initial_eq
    [I.Boundaryless] [SigmaCompactSpace M] [T2Space M] [CompactSpace M]
    [VectorBundle Real E (TangentSpace I : M → Type _)]
    (G : MetricConnectionFamily (I := I) (M := M) Real)
    {T : Real} (hT : 0 ≤ T) (V u v : Real → M → Real)
    (hu : IsHeatPotOn (RealTimeInterval.closed 0 T hT) G V u)
    (hv : IsHeatPotOn (RealTimeInterval.closed 0 T hT) G V v)
    (C : Real)
    (hV : ∀ t ∈ Set.Icc 0 T, ∀ x : M, V t x ≤ C)
    (hinit : ∀ x : M, u 0 x = v 0 x) :
    ∀ t ∈ Set.Icc 0 T, ∀ x : M, u t x = v t x := by
  have huv := heat_pot_comparison (I := I) G hT V u v
    hu.toSubsolution hv.toSupersolution C hV
    (fun x => (hinit x).le)
  have hvu := heat_pot_comparison (I := I) G hT V v u
    hv.toSubsolution hu.toSupersolution C hV
    (fun x => (hinit x).symm.le)
  intro t ht x
  exact le_antisymm (huv t ht x) (hvu t ht x)

omit [CompleteSpace E] in
theorem heat_comparison
    [I.Boundaryless] [SigmaCompactSpace M] [T2Space M] [CompactSpace M]
    [VectorBundle Real E (TangentSpace I : M → Type _)]
    (G : MetricConnectionFamily (I := I) (M := M) Real)
    {T : Real} (hT : 0 ≤ T) (u v : Real → M → Real)
    (hu : IsHeatOn (RealTimeInterval.closed 0 T hT) G u)
    (hv : IsHeatOn (RealTimeInterval.closed 0 T hT) G v)
    (hinit : ∀ x : M, u 0 x ≤ v 0 x) :
    ∀ t ∈ Set.Icc 0 T, ∀ x : M, u t x ≤ v t x := by
  exact heat_pot_comparison (I := I) G hT (fun _ _ => 0) u v
    hu.toSubsolution hv.toSupersolution 0
    (by simp) hinit

omit [CompleteSpace E] in
theorem heat_subsolution_comparison
    [I.Boundaryless] [SigmaCompactSpace M] [T2Space M] [CompactSpace M]
    [VectorBundle Real E (TangentSpace I : M → Type _)]
    (G : MetricConnectionFamily (I := I) (M := M) Real)
    {T : Real} (hT : 0 ≤ T) (u v : Real → M → Real)
    (hu : IsHeatSubsolutionOn (RealTimeInterval.closed 0 T hT) G u)
    (hv : IsHeatSupersolutionOn (RealTimeInterval.closed 0 T hT) G v)
    (hinit : ∀ x : M, u 0 x ≤ v 0 x) :
    ∀ t ∈ Set.Icc 0 T, ∀ x : M, u t x ≤ v t x := by
  exact heat_pot_comparison (I := I) G hT (fun _ _ ↦ 0) u v hu hv 0
    (by simp) hinit

omit [CompleteSpace E] in
theorem heat_eq_of_initial_eq
    [I.Boundaryless] [SigmaCompactSpace M] [T2Space M] [CompactSpace M]
    [VectorBundle Real E (TangentSpace I : M → Type _)]
    (G : MetricConnectionFamily (I := I) (M := M) Real)
    {T : Real} (hT : 0 ≤ T) (u v : Real → M → Real)
    (hu : IsHeatOn (RealTimeInterval.closed 0 T hT) G u)
    (hv : IsHeatOn (RealTimeInterval.closed 0 T hT) G v)
    (hinit : ∀ x : M, u 0 x = v 0 x) :
    ∀ t ∈ Set.Icc 0 T, ∀ x : M, u t x = v t x := by
  exact heat_pot_eq_of_initial_eq (I := I) G hT (fun _ _ => 0) u v hu hv 0
    (by simp) hinit

end

end DifferentialGeometry.Analysis.Parabolic

namespace DifferentialGeometry.Analysis.Parabolic

noncomputable section

open Bundle Set
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Geometry.Operator
open scoped Manifold ContDiff Topology

universe u uE uH

variable {E : Type uE} [NormedAddCommGroup E] [NormedSpace Real E]
variable [FiniteDimensional Real E]
variable {H : Type uH} [TopologicalSpace H]
variable {I : ModelWithCorners Real E H}
variable {M : Type u} [TopologicalSpace M] [ChartedSpace H M]
variable [IsManifold I ∞ M]

theorem scalar_strong_comparison_time_dependent_metric_with_drift_and_potential
    [I.Boundaryless] [CompleteSpace E] [SigmaCompactSpace M]
    [T2Space M] [CompactSpace M] [ConnectedSpace M]
    [VectorBundle Real E (TangentSpace I : M → Type _)]
    (G : MetricConnectionFamily (I := I) (M := M) Real)
    {T : Real} (hT : 0 < T)
    (X : Real → (x : M) → TangentSpace I x)
    (hgrad_cont : ∀ (rho : M → Real),
      ContMDiff I 𝓘(Real, Real) ∞ rho →
      ContinuousOn (fun p : Real × M =>
        (G.metric p.1).inner p.2
          (gradientFun (I := I) (G.metric p.1) rho p.2)
          (gradientFun (I := I) (G.metric p.1) rho p.2))
        (spacetimeSlab (M := M) T))
    (hheat_cont : ∀ (rho : M → Real),
      ContMDiff I 𝓘(Real, Real) ∞ rho →
      ContinuousOn (fun p : Real × M =>
        heatOperatorWithDrift (I := I) G p.1 (X p.1) rho p.2)
        (spacetimeSlab (M := M) T))
    (V : Real → M → Real) (L : Real)
    (u v : Real → M → Real)
    (hu_cont : ContinuousOn (fun p : Real × M => u p.1 p.2)
      (spacetimeSlab (M := M) T))
    (hv_cont : ContinuousOn (fun p : Real × M => v p.1 p.2)
      (spacetimeSlab (M := M) T))
    (huv : ∀ t ∈ Set.Icc 0 T, ∀ x : M, u t x ≤ v t x)
    (hu_time : ∀ t ∈ Set.Icc 0 T, 0 < t → ∀ x : M,
      DifferentiableWithinAt Real (fun s => u s x) (Set.Icc 0 T) t)
    (hv_time : ∀ t ∈ Set.Icc 0 T, 0 < t → ∀ x : M,
      DifferentiableWithinAt Real (fun s => v s x) (Set.Icc 0 T) t)
    (hu_mdiff : ∀ t ∈ Set.Icc 0 T, 0 < t → ∀ x : M,
      MDifferentiableAt I 𝓘(Real, Real) (u t) x)
    (hv_mdiff : ∀ t ∈ Set.Icc 0 T, 0 < t → ∀ x : M,
      MDifferentiableAt I 𝓘(Real, Real) (v t) x)
    (hu_grad : ∀ t ∈ Set.Icc 0 T, 0 < t → ∀ x : M,
      MDiffAt (T% fun y : M =>
        gradientFun (I := I) (G.metric t) (u t) y) x)
    (hv_grad : ∀ t ∈ Set.Icc 0 T, 0 < t → ∀ x : M,
      MDiffAt (T% fun y : M =>
        gradientFun (I := I) (G.metric t) (v t) y) x)
    (hoperator : ∀ t ∈ Set.Icc 0 T, 0 < t → ∀ x : M,
      parabolicOperatorWithDrift (I := I) G T X u t x - V t x * u t x ≤
        parabolicOperatorWithDrift (I := I) G T X v t x - V t x * v t x)
    (hV : ∀ t ∈ Set.Icc 0 T, ∀ x : M, L ≤ V t x)
    {y : M} (hy : u T y = v T y) :
    ∀ t ∈ Set.Icc 0 T, ∀ x : M, u t x = v t x := by
  let w : Real → M → Real := fun t x => v t x - u t x
  have hw_cont : ContinuousOn (fun p : Real × M => w p.1 p.2)
      (spacetimeSlab (M := M) T) := by
    exact hv_cont.sub hu_cont
  have hw_nonneg : ∀ t ∈ Set.Icc 0 T, ∀ x : M, 0 ≤ w t x := by
    intro t ht x
    exact sub_nonneg.mpr (huv t ht x)
  have hw_time : ∀ t ∈ Set.Icc 0 T, 0 < t → ∀ x : M,
      DifferentiableWithinAt Real (fun s => w s x) (Set.Icc 0 T) t := by
    intro t ht htpos x
    exact (hv_time t ht htpos x).sub (hu_time t ht htpos x)
  have hw_mdiff : ∀ t ∈ Set.Icc 0 T, 0 < t → ∀ x : M,
      MDifferentiableAt I 𝓘(Real, Real) (w t) x := by
    intro t ht htpos x
    exact (hv_mdiff t ht htpos x).sub (hu_mdiff t ht htpos x)
  have hw_grad : ∀ t ∈ Set.Icc 0 T, 0 < t → ∀ x : M,
      MDiffAt (T% fun y : M =>
        gradientFun (I := I) (G.metric t) (w t) y) x := by
    intro t ht htpos x
    have heq :
        (T% fun y : M => gradientFun (I := I) (G.metric t) (w t) y) =
          (T% fun y : M =>
            gradientFun (I := I) (G.metric t) (v t) y -
              gradientFun (I := I) (G.metric t) (u t) y) := by
      funext y
      apply congrArg (fun q =>
        (⟨y, q⟩ : TotalSpace E (TangentSpace I : M → Type _)))
      exact gradientFun_sub (I := I) (G.metric t)
        (hv_mdiff t ht htpos y) (hu_mdiff t ht htpos y)
    rw [heq]
    exact mdifferentiableAt_sub_section
      (hv_grad t ht htpos x) (hu_grad t ht htpos x)
  have hw_super : ∀ t ∈ Set.Icc 0 T, 0 < t → ∀ x : M,
      0 ≤ parabolicOperatorWithDrift (I := I) G T X w t x -
        V t x * w t x := by
    intro t ht htpos x
    have hsub := parabolic_sub (I := I) G T X v u t x
      (hv_time t ht htpos x) (hu_time t ht htpos x)
      (hv_mdiff t ht htpos) (hu_mdiff t ht htpos)
      (hv_grad t ht htpos x) (hu_grad t ht htpos x)
    change parabolicOperatorWithDrift (I := I) G T X w t x = _ at hsub
    rw [hsub]
    dsimp only [w]
    linarith [hoperator t ht htpos x]
  have hwy : w T y = 0 := by
    dsimp only [w]
    linarith
  have hwzero :=
    scalar_strong_maximum_principle_time_dependent_metric_with_drift_and_potential
      (I := I) G hT X hgrad_cont hheat_cont V L w hw_cont hw_nonneg
        hw_time hw_mdiff hw_grad hw_super hV hwy
  intro t ht x
  have hzero := hwzero t ht x
  dsimp only [w] at hzero
  linarith

theorem scalar_strong_minimum_principle_time_dependent_metric_with_drift_and_potential
    [I.Boundaryless] [CompleteSpace E] [SigmaCompactSpace M]
    [T2Space M] [CompactSpace M] [ConnectedSpace M]
    [VectorBundle Real E (TangentSpace I : M → Type _)]
    (G : MetricConnectionFamily (I := I) (M := M) Real)
    {T : Real} (hT : 0 < T)
    (X : Real → (x : M) → TangentSpace I x)
    (hgrad_cont : ∀ (rho : M → Real),
      ContMDiff I 𝓘(Real, Real) ∞ rho →
      ContinuousOn (fun p : Real × M =>
        (G.metric p.1).inner p.2
          (gradientFun (I := I) (G.metric p.1) rho p.2)
          (gradientFun (I := I) (G.metric p.1) rho p.2))
        (spacetimeSlab (M := M) T))
    (hheat_cont : ∀ (rho : M → Real),
      ContMDiff I 𝓘(Real, Real) ∞ rho →
      ContinuousOn (fun p : Real × M =>
        heatOperatorWithDrift (I := I) G p.1 (X p.1) rho p.2)
        (spacetimeSlab (M := M) T))
    (V : Real → M → Real) (L : Real)
    (u : Real → M → Real)
    (hu_cont : ContinuousOn (fun p : Real × M => u p.1 p.2)
      (spacetimeSlab (M := M) T))
    (hu_nonpos : ∀ t ∈ Set.Icc 0 T, ∀ x : M, u t x ≤ 0)
    (hu_time : ∀ t ∈ Set.Icc 0 T, 0 < t → ∀ x : M,
      DifferentiableWithinAt Real (fun s => u s x) (Set.Icc 0 T) t)
    (hu_mdiff : ∀ t ∈ Set.Icc 0 T, 0 < t → ∀ x : M,
      MDifferentiableAt I 𝓘(Real, Real) (u t) x)
    (hu_grad : ∀ t ∈ Set.Icc 0 T, 0 < t → ∀ x : M,
      MDiffAt (T% fun y : M =>
        gradientFun (I := I) (G.metric t) (u t) y) x)
    (hu_sub : ∀ t ∈ Set.Icc 0 T, 0 < t → ∀ x : M,
      parabolicOperatorWithDrift (I := I) G T X u t x -
        V t x * u t x ≤ 0)
    (hV : ∀ t ∈ Set.Icc 0 T, ∀ x : M, L ≤ V t x)
    {y : M} (hy : u T y = 0) :
    ∀ t ∈ Set.Icc 0 T, ∀ x : M, u t x = 0 := by
  let w : Real → M → Real := fun t x => -u t x
  have hw_cont : ContinuousOn (fun p : Real × M => w p.1 p.2)
      (spacetimeSlab (M := M) T) := by
    exact hu_cont.neg
  have hw_nonneg : ∀ t ∈ Set.Icc 0 T, ∀ x : M, 0 ≤ w t x := by
    intro t ht x
    exact neg_nonneg.mpr (hu_nonpos t ht x)
  have hw_time : ∀ t ∈ Set.Icc 0 T, 0 < t → ∀ x : M,
      DifferentiableWithinAt Real (fun s => w s x) (Set.Icc 0 T) t := by
    intro t ht htpos x
    exact (hu_time t ht htpos x).neg
  have hw_mdiff : ∀ t ∈ Set.Icc 0 T, 0 < t → ∀ x : M,
      MDifferentiableAt I 𝓘(Real, Real) (w t) x := by
    intro t ht htpos x
    exact (hu_mdiff t ht htpos x).neg
  have hw_grad : ∀ t ∈ Set.Icc 0 T, 0 < t → ∀ x : M,
      MDiffAt (T% fun y : M =>
        gradientFun (I := I) (G.metric t) (w t) y) x := by
    intro t ht htpos x
    have heq :
        (T% fun y : M => gradientFun (I := I) (G.metric t) (w t) y) =
          (T% fun y : M => -gradientFun (I := I) (G.metric t) (u t) y) := by
      funext y
      apply congrArg (fun q =>
        (⟨y, q⟩ : TotalSpace E (TangentSpace I : M → Type _)))
      exact gradientFun_neg (I := I) (G.metric t)
        (hu_mdiff t ht htpos y)
    rw [heq]
    exact mdifferentiableAt_neg_section (hu_grad t ht htpos x)
  have hw_super : ∀ t ∈ Set.Icc 0 T, 0 < t → ∀ x : M,
      0 ≤ parabolicOperatorWithDrift (I := I) G T X w t x -
        V t x * w t x := by
    intro t ht htpos x
    have hneg := parabolic_neg (I := I) G T X u t x
      (hu_time t ht htpos x) (hu_mdiff t ht htpos)
      (hu_grad t ht htpos x)
    change parabolicOperatorWithDrift (I := I) G T X w t x = _ at hneg
    rw [hneg]
    dsimp only [w]
    linarith [hu_sub t ht htpos x]
  have hwy : w T y = 0 := by simp [w, hy]
  have hwzero :=
    scalar_strong_maximum_principle_time_dependent_metric_with_drift_and_potential
      (I := I) G hT X hgrad_cont hheat_cont V L w hw_cont hw_nonneg
        hw_time hw_mdiff hw_grad hw_super hV hwy
  intro t ht x
  have hzero := hwzero t ht x
  dsimp only [w] at hzero
  linarith

theorem scalar_strong_minimum_principle_time_dependent_metric_with_drift_and_potential_negative
    [I.Boundaryless] [CompleteSpace E] [SigmaCompactSpace M]
    [T2Space M] [CompactSpace M] [ConnectedSpace M]
    [VectorBundle Real E (TangentSpace I : M → Type _)]
    (G : MetricConnectionFamily (I := I) (M := M) Real)
    {T : Real} (hT : 0 < T)
    (X : Real → (x : M) → TangentSpace I x)
    (hgrad_cont : ∀ (rho : M → Real),
      ContMDiff I 𝓘(Real, Real) ∞ rho →
      ContinuousOn (fun p : Real × M =>
        (G.metric p.1).inner p.2
          (gradientFun (I := I) (G.metric p.1) rho p.2)
          (gradientFun (I := I) (G.metric p.1) rho p.2))
        (spacetimeSlab (M := M) T))
    (hheat_cont : ∀ (rho : M → Real),
      ContMDiff I 𝓘(Real, Real) ∞ rho →
      ContinuousOn (fun p : Real × M =>
        heatOperatorWithDrift (I := I) G p.1 (X p.1) rho p.2)
        (spacetimeSlab (M := M) T))
    (V : Real → M → Real) (L : Real)
    (u : Real → M → Real)
    (hu_cont : ContinuousOn (fun p : Real × M => u p.1 p.2)
      (spacetimeSlab (M := M) T))
    (hu_nonpos : ∀ t ∈ Set.Icc 0 T, ∀ x : M, u t x ≤ 0)
    (hu_time : ∀ t ∈ Set.Icc 0 T, 0 < t → ∀ x : M,
      DifferentiableWithinAt Real (fun s => u s x) (Set.Icc 0 T) t)
    (hu_mdiff : ∀ t ∈ Set.Icc 0 T, 0 < t → ∀ x : M,
      MDifferentiableAt I 𝓘(Real, Real) (u t) x)
    (hu_grad : ∀ t ∈ Set.Icc 0 T, 0 < t → ∀ x : M,
      MDiffAt (T% fun y : M =>
        gradientFun (I := I) (G.metric t) (u t) y) x)
    (hu_sub : ∀ t ∈ Set.Icc 0 T, 0 < t → ∀ x : M,
      parabolicOperatorWithDrift (I := I) G T X u t x -
        V t x * u t x ≤ 0)
    (hV : ∀ t ∈ Set.Icc 0 T, ∀ x : M, L ≤ V t x)
    {t : Real} (ht : t ∈ Set.Icc 0 T) {x : M} (hx : u t x < 0)
    (y : M) :
    u T y < 0 := by
  by_contra hy
  have hy0 : u T y = 0 := le_antisymm (hu_nonpos T ⟨hT.le, le_rfl⟩ y)
    (le_of_not_gt hy)
  have hpast :=
    scalar_strong_minimum_principle_time_dependent_metric_with_drift_and_potential
      (I := I) G hT X hgrad_cont hheat_cont V L u hu_cont hu_nonpos
        hu_time hu_mdiff hu_grad hu_sub hV hy0 t ht x
  linarith

end

end DifferentialGeometry.Analysis.Parabolic

namespace DifferentialGeometry.Analysis.Parabolic

noncomputable section

open Bundle Set
open DifferentialGeometry.Geometry.Connection
open DifferentialGeometry.Geometry.Curvature
open scoped Manifold ContDiff

universe u uE uH

variable {E : Type uE} [NormedAddCommGroup E] [NormedSpace Real E]
variable [FiniteDimensional Real E] [CompleteSpace E]
variable {H : Type uH} [TopologicalSpace H]
variable {I : ModelWithCorners Real E H}
variable {M : Type u} [TopologicalSpace M] [ChartedSpace H M]
variable [IsManifold I ∞ M]

theorem heat_pot_strict_comparison_of_initial_lt_of_metricFamilySmoothOn
    [I.Boundaryless] [SigmaCompactSpace M] [T2Space M] [CompactSpace M]
    [ConnectedSpace M]
    [VectorBundle Real E (TangentSpace I : M → Type _)]
    (G : MetricConnectionFamily (I := I) (M := M) Real)
    {T : Real} (hT : 0 ≤ T) (V u v : Real → M → Real)
    (hu : IsHeatPotOn (RealTimeInterval.closed 0 T hT) G V u)
    (hv : IsHeatPotOn (RealTimeInterval.closed 0 T hT) G V v)
    (C : Real)
    (hV_upper : ∀ t ∈ Set.Icc 0 T, ∀ x : M, V t x ≤ C)
    (hinit : ∀ x : M, u 0 x ≤ v 0 x)
    {c : M} (hc : u 0 c < v 0 c)
    {tau : Real} (htau : tau ∈ Set.Ioo 0 T)
    {D : RealTimeInterval}
    (hG : MetricFamilySmoothOn (I := I) (M := M) D G.metric)
    (hslab : Set.Icc 0 tau ⊆ D.regular)
    (hconn : ∀ t ∈ Set.Icc 0 tau,
      G.connection t = LeviCivita (I := I) (G.metric t))
    (L : Real) (hV_lower : ∀ t ∈ Set.Icc 0 tau, ∀ x : M, L ≤ V t x)
    (y : M) :
    u tau y < v tau y := by
  let w : Real → M → Real := fun t x => v t x - u t x
  have hw : IsHeatPotOn
      (RealTimeInterval.closed 0 T hT) G V w := by
    exact hv.sub hu
  have hwinit : ∀ x : M, 0 ≤ w 0 x := by
    intro x
    exact sub_nonneg.mpr (hinit x)
  have hwc : 0 < w 0 c := by
    exact sub_pos.mpr hc
  have hwpos := heat_pot_pos_of_initial_pos_of_metricFamilySmoothOn
    (I := I) G hT V w hw C hV_upper hwinit hwc htau
      hG hslab hconn L hV_lower y
  dsimp only [w] at hwpos
  linarith

theorem heat_strict_comparison_of_initial_lt_of_metricFamilySmoothOn
    [I.Boundaryless] [SigmaCompactSpace M] [T2Space M] [CompactSpace M]
    [ConnectedSpace M]
    [VectorBundle Real E (TangentSpace I : M → Type _)]
    (G : MetricConnectionFamily (I := I) (M := M) Real)
    {T : Real} (hT : 0 ≤ T) (u v : Real → M → Real)
    (hu : IsHeatOn (RealTimeInterval.closed 0 T hT) G u)
    (hv : IsHeatOn (RealTimeInterval.closed 0 T hT) G v)
    (hinit : ∀ x : M, u 0 x ≤ v 0 x)
    {c : M} (hc : u 0 c < v 0 c)
    {tau : Real} (htau : tau ∈ Set.Ioo 0 T)
    {D : RealTimeInterval}
    (hG : MetricFamilySmoothOn (I := I) (M := M) D G.metric)
    (hslab : Set.Icc 0 tau ⊆ D.regular)
    (hconn : ∀ t ∈ Set.Icc 0 tau,
      G.connection t = LeviCivita (I := I) (G.metric t))
    (y : M) :
    u tau y < v tau y := by
  exact heat_pot_strict_comparison_of_initial_lt_of_metricFamilySmoothOn
    (I := I) G hT (fun _ _ => 0) u v hu hv 0 (by simp) hinit hc htau
      hG hslab hconn 0 (by simp) y

end

end DifferentialGeometry.Analysis.Parabolic
