import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.KappaSolutions.TimePolynomialField
import DifferentialGeometry.Geometry.Flow.RicciFlow.Evolution.Curvature.TimeJetFields
import DifferentialGeometry.Geometry.Flow.RicciFlow.Evolution.Metric.ClosedIntervalDerivative
import DifferentialGeometry.Geometry.Flow.RicciFlow.Compactness.Solutions.Pullback
import DifferentialGeometry.Geometry.Metric.ModelChange
import DifferentialGeometry.Geometry.Metric.Convergence.Naturality.TensorTimeJets


set_option autoImplicit false
noncomputable section

namespace DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions

open Bundle _root_.Manifold Filter Set
open DifferentialGeometry.Tensor0SBundle DifferentialGeometry.Geometry.Curvature
open scoped _root_.Manifold ContDiff _root_.Topology BigOperators


def ordinaryMetricJetPolynomial {n : ℕ} (q : ℕ) (slots : Fin 2 → Fin n) :
    MvPolynomial (CurvatureTimePolynomialVariable n) ℝ :=
  (MvPolynomial.mkDerivation ℝ (curvatureTimeEvolution n))^[q]
    (-2 * curvatureTimeRicciPolynomial (slots 0) (slots 1))

section Coefficients

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

private theorem tensor_time_jets_of_polynomial_evolution {n r : ℕ} {x : M} {σ : Type*}
    (basis : Module.Basis (Fin n) ℝ (TangentSpace I x))
    (evolve : σ → MvPolynomial σ ℝ) (v : ℝ → σ → ℝ)
    (f : ℝ → Tensor0SSpace r I x) (P : (Fin r → Fin n) → MvPolynomial σ ℝ)
    {J : Set ℝ} (hJ : UniqueDiffOn ℝ J)
    (hv : ∀ t ∈ J, ∀ i, HasDerivWithinAt (fun s => v s i)
      (MvPolynomial.eval (v t) (evolve i)) J t)
    (hf : ∀ t ∈ J, ∀ slots, HasDerivWithinAt (fun s => component0S (I := I) basis (f s) slots)
      (MvPolynomial.eval (v t) (P slots)) J t) :
    ∀ q, ∀ t ∈ J,
      (∀ slots, component0S (I := I) basis (iteratedDerivWithin (q + 1) f J t) slots =
        MvPolynomial.eval (v t) ((MvPolynomial.mkDerivation ℝ evolve)^[q] (P slots))) ∧
      HasDerivWithinAt (iteratedDerivWithin q f J) (iteratedDerivWithin (q + 1) f J t) J t := by
  intro q
  induction q with
  | zero =>
    intro t ht
    have hd : HasDerivWithinAt f (tensorOfPolynomialComponents basis P (v t)) J t := by
      apply tensor0S_hasDerivWithinAt_of_components basis
      intro slots
      simpa only [component0S_tensorOfPolynomialComponents] using hf t ht slots
    have heq : iteratedDerivWithin 1 f J t = tensorOfPolynomialComponents basis P (v t) := by
      rw [iteratedDerivWithin_one]
      exact hd.derivWithin (hJ t ht)
    refine ⟨fun slots => ?_, ?_⟩
    · rw [heq, component0S_tensorOfPolynomialComponents]
      rfl
    · exact hd.congr_deriv heq.symm
  | succ q ih =>
    intro t ht
    let Q : (Fin r → Fin n) → MvPolynomial σ ℝ :=
      fun slots => (MvPolynomial.mkDerivation ℝ evolve)^[q + 1] (P slots)
    have hd : HasDerivWithinAt (iteratedDerivWithin (q + 1) f J)
        (tensorOfPolynomialComponents basis Q (v t)) J t := by
      apply tensor0S_hasDerivWithinAt_of_components basis
      intro slots
      have hp := DifferentialGeometry.Analysis.polynomial_hasDerivWithinAt evolve v (hv t ht)
        ((MvPolynomial.mkDerivation ℝ evolve)^[q] (P slots))
      have hp' := hp.congr_of_eventuallyEq
        (Filter.eventuallyEq_of_mem self_mem_nhdsWithin fun s hs => (ih s hs).1 slots)
        ((ih t ht).1 slots)
      simpa only [component0S_tensorOfPolynomialComponents, Q, Function.iterate_succ_apply'] using hp'
    have heq : iteratedDerivWithin (q + 1 + 1) f J t = tensorOfPolynomialComponents basis Q (v t) := by
      rw [iteratedDerivWithin_succ]
      exact hd.derivWithin (hJ t ht)
    refine ⟨fun slots => ?_, hd.congr_deriv heq.symm⟩
    rw [heq, component0S_tensorOfPolynomialComponents]

end Coefficients

section Ancient

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [CompleteSpace E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [T2Space M] [SigmaCompactSpace M]

private local instance ordinaryClosedMetricC1 : IsManifold I 1 M :=
  IsManifold.of_le (I := I) (M := M) (n := ∞) (by decide)


omit [SigmaCompactSpace M] in
private theorem ordinary_metric_time_jets_of_mixed_fields
    {D : RealTimeInterval} (S : SolutionOn (I := I) (M := M) D)
    {J : Set ℝ} (hJ : UniqueDiffOn ℝ J)
    (A : ℕ → ℝ → Tensor0SField (I := I) (M := M) (n := ∞) 4)
    (hA : ∀ q t, t ∈ J → ∀ x : M,
      A q t x = mixedCurvatureTensor S 0 q t x ∧
      HasDerivWithinAt (fun s => A q s x)
        (A (q + 1) t x - covariantEndomorphismAction0S (A q t x)
          (ricciSharp (S.base.metric t) x)) J t)
    (hmetric : ∀ t ∈ J, ∀ x : M, ∀ v w : TangentSpace I x,
      HasDerivWithinAt (fun s => (S.base.metric s).inner x v w)
        (-2 * S.ricciAt t x (vec2 v w)) J t) :
    (∃ B : ℕ → ℝ → Tensor0SField (I := I) (M := M) (n := ∞) 2,
      (∀ t, B 0 t = metricTensorField (S.base.metric t)) ∧
      ∀ q t, t ∈ J → ∀ x,
        B q t x = iteratedDerivWithin q (fun s => metricTensorField (S.base.metric s) x) J t ∧
        HasDerivWithinAt (fun s => B q s x) (B (q + 1) t x) J t) ∧
    ∀ q t, t ∈ J → ∀ (x : M) {n : ℕ},
      ∀ basis : Module.Basis (Fin n) ℝ (TangentSpace I x), ∀ slots : Fin 2 → Fin n,
        component0S (I := I) basis
          (iteratedDerivWithin (q + 1) (fun s => metricTensorField (S.base.metric s) x) J t) slots =
        MvPolynomial.eval (curvatureTimePolynomialValues S.base.metric
          (fun r s => mixedCurvatureTensor S 0 r s x) basis t)
          (ordinaryMetricJetPolynomial q slots) := by
  classical
  have hzero (t : ℝ) (ht : t ∈ J) (x : M) : A 0 t x = metricRm04At (S.base.metric t) x := by
    calc
      A 0 t x = mixedCurvatureTensor S 0 0 t x := (hA 0 t ht x).1
      _ = metricRm04 (S.base.metric t) x := rfl
      _ = metricRm04At (S.base.metric t) x := metricRm04_apply (S.base.metric t) x
  have hdata (x : M) {n : ℕ} (basis : Module.Basis (Fin n) ℝ (TangentSpace I x)) :
      ∀ q, ∀ t, t ∈ J →
        (∀ slots, component0S (I := I) basis
          (iteratedDerivWithin (q + 1) (fun s => metricTensorField (S.base.metric s) x) J t) slots =
          MvPolynomial.eval (curvatureTimePolynomialValues S.base.metric (fun q s => A q s x) basis t)
            (ordinaryMetricJetPolynomial q slots)) ∧
        HasDerivWithinAt (iteratedDerivWithin q (fun s => metricTensorField (S.base.metric s) x) J)
          (iteratedDerivWithin (q + 1) (fun s => metricTensorField (S.base.metric s) x) J t)
          J t := by
    apply tensor_time_jets_of_polynomial_evolution basis (curvatureTimeEvolution n)
      (curvatureTimePolynomialValues S.base.metric (fun q s => A q s x) basis)
      (fun s => metricTensorField (S.base.metric s) x)
      (fun slots => -2 * curvatureTimeRicciPolynomial (slots 0) (slots 1)) hJ
    · intro t ht v
      exact curvatureTimePolynomialValues_hasDerivWithinAt S.base.metric (fun q s => A q s x) basis
        (hzero t ht x) (fun i j => hmetric t ht x
          (basis i) (basis j)) (fun q => (hA q t ht x).2) v
    · intro t ht slots
      simpa only [component0S_apply, metricTensorField_apply, map_mul, map_neg, map_ofNat,
        SolutionOn.ricciAt, SolutionFamily.ricciAt,
        eval_curvatureTimeRicciPolynomial S.base.metric (fun q s => A q s x) basis (hzero t ht x)]
        using hmetric t ht x (basis (slots 0)) (basis (slots 1))
  have hformula : ∀ q t, t ∈ J → ∀ (x : M) {n : ℕ},
      ∀ basis : Module.Basis (Fin n) ℝ (TangentSpace I x), ∀ slots : Fin 2 → Fin n,
        component0S (I := I) basis
          (iteratedDerivWithin (q + 1) (fun s => metricTensorField (S.base.metric s) x) J t) slots =
        MvPolynomial.eval (curvatureTimePolynomialValues S.base.metric
          (fun r s => mixedCurvatureTensor S 0 r s x) basis t)
          (ordinaryMetricJetPolynomial q slots) := by
    intro q t ht x n basis slots
    have hh := (hdata x basis q t ht).1 slots
    have heq : curvatureTimePolynomialValues S.base.metric (fun r s => A r s x) basis t =
        curvatureTimePolynomialValues S.base.metric
          (fun r s => mixedCurvatureTensor S 0 r s x) basis t := by
      funext v
      cases v with
      | inl ij => rfl
      | inr rs =>
        simp only [curvatureTimePolynomialValues]
        rw [(hA rs.1 t ht x).1]
    exact hh.trans (congrArg
      (fun v => MvPolynomial.eval v (ordinaryMetricJetPolynomial q slots)) heq)
  refine ⟨?_, hformula⟩
  have hfields (q : ℕ) (t : {s : ℝ // s ∈ J}) :
      ∃ C : Tensor0SField (I := I) (M := M) (n := ∞) 2,
        ∀ x, C x = iteratedDerivWithin (q + 1) (fun s => metricTensorField (S.base.metric s) x) J t.val :=
    exists_time_polynomial_field S.base.metric A t.val 2 (ordinaryMetricJetPolynomial q)
      (fun x => iteratedDerivWithin (q + 1) (fun s => metricTensorField (S.base.metric s) x) J t.val)
      (fun x basis slots => (hdata x basis q t.val t.property).1 slots)
  choose C hC using hfields
  let B : ℕ → ℝ → Tensor0SField (I := I) (M := M) (n := ∞) 2 := fun q t =>
    match q with
    | 0 => metricTensorField (S.base.metric t)
    | q + 1 => if ht : t ∈ J then C q ⟨t, ht⟩ else 0
  have hB (q : ℕ) (t : ℝ) (ht : t ∈ J) (x : M) :
      B q t x = iteratedDerivWithin q (fun s => metricTensorField (S.base.metric s) x) J t := by
    cases q with
    | zero => rfl
    | succ q =>
      simp only [B, dite_eq_left ht]
      exact hC q ⟨t, ht⟩ x
  refine ⟨B, fun _ => rfl, fun q t ht x => ⟨hB q t ht x, ?_⟩⟩
  have hd := (hdata x (Module.finBasis ℝ (TangentSpace I x)) q t ht).2
  have hd' := hd.congr_deriv (hB (q + 1) t ht x).symm
  exact hd'.congr_of_eventuallyEq
    (Filter.eventuallyEq_of_mem self_mem_nhdsWithin fun s hs => hB q s hs x) (hB q t ht x)

theorem exists_ancient_ordinary_metric_time_jets
    {D : RealTimeInterval} (S : SolutionOn (I := I) (M := M) D) (hS : IsSolutionOn S)
    {b : ℝ} (hcarrier : D.carrier = Iic b) (hregular : D.regular = Iio b) :
    ∃ B : ℕ → ℝ → Tensor0SField (I := I) (M := M) (n := ∞) 2,
      (∀ t, B 0 t = metricTensorField (S.base.metric t)) ∧
      ∀ q, ∀ t, t ≤ b → ∀ x,
        B q t x = iteratedDerivWithin q (fun s => metricTensorField (S.base.metric s) x) (Iic b) t ∧
        HasDerivWithinAt (fun s => B q s x) (B (q + 1) t x) (Iic b) t := by
  classical
  obtain ⟨A, hA⟩ := exists_ancient_mixed_curvature_fields S hS hcarrier hregular 0
  exact (ordinary_metric_time_jets_of_mixed_fields S (uniqueDiffOn_Iic b) A hA
    (fun t ht x v w => ancient_metric_hasDerivWithinAt S hS hcarrier hregular ht x v w)).1

theorem ordinary_metric_time_jet_component_eq_polynomial
    {D : RealTimeInterval} (S : SolutionOn (I := I) (M := M) D) (hS : IsSolutionOn S)
    {b t : ℝ} (hcarrier : D.carrier = Iic b) (hregular : D.regular = Iio b)
    (ht : t ≤ b) (x : M) {n : ℕ}
    (basis : Module.Basis (Fin n) ℝ (TangentSpace I x)) (q : ℕ) (slots : Fin 2 → Fin n) :
    component0S (I := I) basis
      (iteratedDerivWithin (q + 1) (fun s => metricTensorField (S.base.metric s) x) (Iic b) t) slots =
    MvPolynomial.eval
      (curvatureTimePolynomialValues S.base.metric
        (fun r s => mixedCurvatureTensor S 0 r s x) basis t)
      (ordinaryMetricJetPolynomial q slots) := by
  obtain ⟨A, hA⟩ := exists_ancient_mixed_curvature_fields S hS hcarrier hregular 0
  exact (ordinary_metric_time_jets_of_mixed_fields S (uniqueDiffOn_Iic b) A hA
    (fun t ht x v w => ancient_metric_hasDerivWithinAt S hS hcarrier hregular ht x v w)).2
      q t ht x basis slots

private theorem exists_ordinary_metric_time_jets_on_closed_interval_of_inner_product_space
    {D : RealTimeInterval} (S : SolutionOn (I := I) (M := M) D) (hS : IsSolutionOn S)
    {a c b : ℝ} (hac : a < c) (hcb : c < b)
    (hcarrier : D.carrier = Icc a b) (hregular : Ioo a b ⊆ D.regular) :
    ∃ B : ℕ → ℝ → Tensor0SField (I := I) (M := M) (n := ∞) 2,
      (∀ t, B 0 t = metricTensorField (S.base.metric t)) ∧
      ∀ q t, t ∈ Icc c b → ∀ x,
        B q t x = iteratedDerivWithin q (fun s => metricTensorField (S.base.metric s) x) (Icc c b) t ∧
        HasDerivWithinAt (fun s => B q s x) (B (q + 1) t x) (Icc c b) t := by
  obtain ⟨A, hA⟩ := exists_mixed_curvature_fields_on_closed_interval S hS hac hcb hcarrier hregular 0
  exact (ordinary_metric_time_jets_of_mixed_fields S (uniqueDiffOn_Icc hcb) A hA
    (fun t ht x v w => metric_inner_hasDerivWithinAt_on_closed_interval S hS hcb
      (by rw [hcarrier]; exact Icc_subset_Icc_left hac.le)
      ((Ioo_subset_Ioo_left hac.le).trans hregular) ht x v w)).1

theorem ordinary_metric_time_jet_component_eq_polynomial_on_closed_interval
    {D : RealTimeInterval} (S : SolutionOn (I := I) (M := M) D) (hS : IsSolutionOn S)
    {a c b t : ℝ} (hac : a < c) (hcb : c < b)
    (hcarrier : D.carrier = Icc a b) (hregular : Ioo a b ⊆ D.regular)
    (ht : t ∈ Icc c b) (x : M) {n : ℕ}
    (basis : Module.Basis (Fin n) ℝ (TangentSpace I x)) (q : ℕ) (slots : Fin 2 → Fin n) :
    component0S (I := I) basis
      (iteratedDerivWithin (q + 1) (fun s => metricTensorField (S.base.metric s) x) (Icc c b) t) slots =
    MvPolynomial.eval
      (curvatureTimePolynomialValues S.base.metric
        (fun r s => mixedCurvatureTensor S 0 r s x) basis t)
      (ordinaryMetricJetPolynomial q slots) := by
  obtain ⟨A, hA⟩ := exists_mixed_curvature_fields_on_closed_interval S hS hac hcb hcarrier hregular 0
  exact (ordinary_metric_time_jets_of_mixed_fields S (uniqueDiffOn_Icc hcb) A hA
    (fun t ht x v w => metric_inner_hasDerivWithinAt_on_closed_interval S hS hcb
      (by rw [hcarrier]; exact Icc_subset_Icc_left hac.le)
      ((Ioo_subset_Ioo_left hac.le).trans hregular) ht x v w)).2 q t ht x basis slots

end Ancient

open DifferentialGeometry.CheegerGromovCompactness

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [T2Space M] [SigmaCompactSpace M]

theorem exists_ordinary_metric_time_jets_on_closed_interval
    {D : RealTimeInterval} (S : SolutionOn (I := I) (M := M) D) (hS : IsSolutionOn S)
    {a c b : ℝ} (hac : a < c) (hcb : c < b)
    (hcarrier : D.carrier = Icc a b) (hregular : Ioo a b ⊆ D.regular) :
    ∃ B : ℕ → ℝ → Tensor0SField (I := I) (M := M) (n := ∞) 2,
      (∀ t, B 0 t = metricTensorField (S.base.metric t)) ∧
      ∀ q t, t ∈ Icc c b → ∀ x,
        B q t x = iteratedDerivWithin q (fun s => metricTensorField (S.base.metric s) x) (Icc c b) t ∧
        HasDerivWithinAt (fun s => B q s x) (B (q + 1) t x) (Icc c b) t := by
  let _ : CompleteSpace E := FiniteDimensional.complete ℝ E
  let e : E ≃L[ℝ] EuclideanSpace ℝ (Fin (Module.finrank ℝ E)) :=
    (Module.finBasis ℝ E).equivFun.toContinuousLinearEquiv.trans
      (EuclideanSpace.equiv (Fin (Module.finrank ℝ E)) ℝ).symm
  let J := I.transContinuousLinearEquiv e
  let Φ := ContinuousLinearEquiv.toTransContinuousLinearEquiv (n := ∞) I M e
  let U : SolutionOn (I := J) (M := M) D := S.pullback Φ.symm
  have hU : IsSolutionOn U := hS.pullback S Φ.symm
  obtain ⟨A, hAzero, hA⟩ :=
    exists_ordinary_metric_time_jets_on_closed_interval_of_inner_product_space
      U hU hac hcb hcarrier hregular
  have hmetric (t : ℝ) : pullbackTensor02FieldCross Φ (metricTensorField (U.base.metric t)) =
      metricTensorField (S.base.metric t) := by
    have hp : pullbackTensor02FieldCross Φ (metricTensorField (U.base.metric t)) =
        metricTensorField (Diffeomorph.pullbackMetricCross (U.base.metric t) Φ) := by
      ext x v
      rw [pullbackTensor02FieldCross_apply, metricTensorField_apply, metricTensorField_apply,
        Diffeomorph.pullbackMetricCross_inner]
    rw [hp]
    congr 1
    exact SmoothRiemannianMetric.pullback_transContinuousLinearEquiv (S.base.metric t) e
  refine ⟨fun q t => pullbackTensor02FieldCross Φ (A q t), ?_, ?_⟩
  · intro t
    change pullbackTensor02FieldCross Φ (A 0 t) = _
    rw [hAzero, hmetric]
  · intro q t ht x
    refine ⟨?_, hasDerivWithinAt_pullbackTensor02FieldCross Φ (A q) (A (q + 1) t) x
      (hA q t ht (Φ x)).2⟩
    have hjet := pullbackTensor02FieldCross_eq_iteratedDerivWithin Φ
      (fun s => metricTensorField (U.base.metric s)) (A q t) q (uniqueDiffOn_Icc hcb) ht
      (fun y => (hA q t ht y).1) x
    simpa only [hmetric] using hjet


end DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions
