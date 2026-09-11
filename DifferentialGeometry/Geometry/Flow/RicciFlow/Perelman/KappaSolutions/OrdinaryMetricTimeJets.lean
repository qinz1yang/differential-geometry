import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.KappaSolutions.TimePolynomialField
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.KappaSolutions.MixedCurvatureFields


set_option autoImplicit false
noncomputable section

namespace DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions

open Bundle Manifold Filter Set
open DifferentialGeometry.Tensor0SBundle DifferentialGeometry.Geometry.Curvature
open scoped Manifold ContDiff _root_.Topology BigOperators


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
      have hp := polynomial_hasDerivWithinAt evolve v (hv t ht)
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
  [FiniteDimensional ℝ E] [CompleteSpace E] [NeZero (Module.finrank ℝ E)]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [T2Space M] [SigmaCompactSpace M]

private local instance ordinaryMetricC1 : IsManifold I 1 M :=
  IsManifold.of_le (I := I) (M := M) (n := ∞) (by decide)


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
  have hzero (t : ℝ) (ht : t ≤ b) (x : M) : A 0 t x = metricRm04At (S.base.metric t) x := by
    calc
      A 0 t x = mixedCurvatureTensor S 0 0 t x := (hA 0 t ht x).1
      _ = metricRm04 (S.base.metric t) x := rfl
      _ = metricRm04At (S.base.metric t) x := metricRm04_apply (S.base.metric t) x
  have hdata (x : M) {n : ℕ} (basis : Module.Basis (Fin n) ℝ (TangentSpace I x)) :
      ∀ q, ∀ t, t ≤ b →
        (∀ slots, component0S (I := I) basis
          (iteratedDerivWithin (q + 1) (fun s => metricTensorField (S.base.metric s) x) (Iic b) t) slots =
          MvPolynomial.eval (curvatureTimePolynomialValues S.base.metric (fun q s => A q s x) basis t)
            (ordinaryMetricJetPolynomial q slots)) ∧
        HasDerivWithinAt (iteratedDerivWithin q (fun s => metricTensorField (S.base.metric s) x) (Iic b))
          (iteratedDerivWithin (q + 1) (fun s => metricTensorField (S.base.metric s) x) (Iic b) t)
          (Iic b) t := by
    apply tensor_time_jets_of_polynomial_evolution basis (curvatureTimeEvolution n)
      (curvatureTimePolynomialValues S.base.metric (fun q s => A q s x) basis)
      (fun s => metricTensorField (S.base.metric s) x)
      (fun slots => -2 * curvatureTimeRicciPolynomial (slots 0) (slots 1)) (uniqueDiffOn_Iic b)
    · intro t ht v
      exact curvatureTimePolynomialValues_hasDerivWithinAt S.base.metric (fun q s => A q s x) basis
        (hzero t ht x) (fun i j => ancient_metric_hasDerivWithinAt S hS hcarrier hregular ht x
          (basis i) (basis j)) (fun q => (hA q t ht x).2) v
    · intro t ht slots
      simpa only [component0S_apply, metricTensorField_apply, map_mul, map_neg, map_ofNat,
        SolutionOn.ricciAt, SolutionFamily.ricciAt,
        eval_curvatureTimeRicciPolynomial S.base.metric (fun q s => A q s x) basis (hzero t ht x)]
        using ancient_metric_hasDerivWithinAt S hS hcarrier hregular ht x (basis (slots 0)) (basis (slots 1))
  have hfields (q : ℕ) (t : {s : ℝ // s ≤ b}) :
      ∃ C : Tensor0SField (I := I) (M := M) (n := ∞) 2,
        ∀ x, C x = iteratedDerivWithin (q + 1) (fun s => metricTensorField (S.base.metric s) x) (Iic b) t.val :=
    exists_time_polynomial_field S.base.metric A t.val 2 (ordinaryMetricJetPolynomial q)
      (fun x => iteratedDerivWithin (q + 1) (fun s => metricTensorField (S.base.metric s) x) (Iic b) t.val)
      (fun x basis slots => (hdata x basis q t.val t.property).1 slots)
  choose C hC using hfields
  let B : ℕ → ℝ → Tensor0SField (I := I) (M := M) (n := ∞) 2 := fun q t =>
    match q with
    | 0 => metricTensorField (S.base.metric t)
    | q + 1 => if ht : t ≤ b then C q ⟨t, ht⟩ else 0
  have hB (q : ℕ) (t : ℝ) (ht : t ≤ b) (x : M) :
      B q t x = iteratedDerivWithin q (fun s => metricTensorField (S.base.metric s) x) (Iic b) t := by
    cases q with
    | zero => rfl
    | succ q =>
      simp only [B, dif_pos ht]
      exact hC q ⟨t, ht⟩ x
  refine ⟨B, fun _ => rfl, fun q t ht x => ⟨hB q t ht x, ?_⟩⟩
  have hd := (hdata x (Module.finBasis ℝ (TangentSpace I x)) q t ht).2
  have hd' := hd.congr_deriv (hB (q + 1) t ht x).symm
  exact hd'.congr_of_eventuallyEq
    (Filter.eventuallyEq_of_mem self_mem_nhdsWithin fun s hs => hB q s hs x) (hB q t ht x)

end Ancient

end DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions
