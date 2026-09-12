import DifferentialGeometry.Geometry.Flow.RicciFlow.Evolution.Metric.CoefficientEvolution
import DifferentialGeometry.Analysis.Calculus.TimeJet.PolynomialEvolution
import DifferentialGeometry.Geometry.Curvature.Metric.LeviCivita


set_option autoImplicit false
noncomputable section

namespace DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions

open Bundle Manifold Filter Set
open DifferentialGeometry.Geometry.Curvature DifferentialGeometry.Tensor0SBundle
open scoped Manifold ContDiff _root_.Topology BigOperators


abbrev CurvatureTimePolynomialVariable (n : ℕ) :=
  (Fin n × Fin n) ⊕ (ℕ × (Fin 4 → Fin n))


def curvatureTimeRicciPolynomial {n : ℕ} (i j : Fin n) :
    MvPolynomial (CurvatureTimePolynomialVariable n) ℝ :=
  ∑ a : Fin n, ∑ c : Fin n,
    MvPolynomial.X (Sum.inl (a, c)) *
      MvPolynomial.X (Sum.inr (0, slots4 a i j c))


def curvatureTimeSharpPolynomial {n : ℕ} (i j : Fin n) :
    MvPolynomial (CurvatureTimePolynomialVariable n) ℝ :=
  ∑ k : Fin n, MvPolynomial.X (Sum.inl (j, k)) * curvatureTimeRicciPolynomial i k


def curvatureTimeEvolution (n : ℕ) :
    CurvatureTimePolynomialVariable n → MvPolynomial (CurvatureTimePolynomialVariable n) ℝ
  | Sum.inl ij => 2 * ∑ a : Fin n, ∑ c : Fin n,
      MvPolynomial.X (Sum.inl (ij.1, a)) * MvPolynomial.X (Sum.inl (ij.2, c)) *
        curvatureTimeRicciPolynomial a c
  | Sum.inr qs => MvPolynomial.X (Sum.inr (qs.1 + 1, qs.2)) -
      ∑ k : Fin 4, ∑ e : Fin n, curvatureTimeSharpPolynomial (qs.2 k) e *
        MvPolynomial.X (Sum.inr (qs.1, Function.update qs.2 k e))

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [CompleteSpace E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M] [T2Space M] [BoundarylessManifold I M]

private local instance timePolynomialC1 : IsManifold I 1 M :=
  IsManifold.of_le (I := I) (M := M) (n := ∞) (by decide)

omit [CompleteSpace E] [T2Space M] [BoundarylessManifold I M] in
def curvatureTimePolynomialValues {n : ℕ} {x : M}
    (g : ℝ → SmoothRiemannianMetric I M) (A : ℕ → ℝ → Tensor0SSpace 4 I x)
    (basis : Module.Basis (Fin n) ℝ (TangentSpace I x)) (t : ℝ) :
    CurvatureTimePolynomialVariable n → ℝ
  | Sum.inl ij => basisInvMetric (I := I) (g t) x basis ij.1 ij.2
  | Sum.inr qs => component0S (I := I) basis (A qs.1 t) qs.2

omit [BoundarylessManifold I M] in
theorem eval_curvatureTimeRicciPolynomial {n : ℕ} {x : M}
    (g : ℝ → SmoothRiemannianMetric I M) (A : ℕ → ℝ → Tensor0SSpace 4 I x)
    (basis : Module.Basis (Fin n) ℝ (TangentSpace I x)) {t : ℝ}
    (hA : A 0 t = metricRm04At (g t) x) (i j : Fin n) :
    MvPolynomial.eval (curvatureTimePolynomialValues g A basis t)
      (curvatureTimeRicciPolynomial i j) =
        metricRicciAt (g t) x (vec2 (basis i) (basis j)) := by
  classical
  let K := metricCurvatureSections (I := I) (M := M) (g t)
  have hLower := rm04LowersRm13At_of_realizes (I := I) (g t) (metricCov (g t))
    (metricRm13 (g t)) (metricRm04 (g t)) K.rm13Realizes K.rm04Realizes x
  have hTrace := ricciFirstTraceAt_of_rm13_section (I := I) (g t) basis
    (basisInvMetric (I := I) (g t) x basis) (basisInvMetric_isInverse (I := I) (g t) x basis)
    (metricRicci (g t)) (metricRm13 (g t)) (metricRm04 (g t)) K.ricciRealizes hLower i j
  simpa only [curvatureTimeRicciPolynomial, map_sum, map_mul, MvPolynomial.eval_X,
    curvatureTimePolynomialValues, hA, ← rm04CompAt_apply, rm04CompAt,
    metricRicci_apply, metricRm04_apply] using hTrace.symm


theorem eval_curvatureTimeSharpPolynomial {n : ℕ} {x : M}
    (g : ℝ → SmoothRiemannianMetric I M) (A : ℕ → ℝ → Tensor0SSpace 4 I x)
    (basis : Module.Basis (Fin n) ℝ (TangentSpace I x)) {t : ℝ}
    (hA : A 0 t = metricRm04At (g t) x) (i j : Fin n) :
    MvPolynomial.eval (curvatureTimePolynomialValues g A basis t)
      (curvatureTimeSharpPolynomial i j) =
        basis.repr (ricciSharp (g t) x (basis i)) j := by
  simp only [curvatureTimeSharpPolynomial, map_sum, map_mul, MvPolynomial.eval_X,
    curvatureTimePolynomialValues, eval_curvatureTimeRicciPolynomial g A basis hA]
  symm
  simpa only [inner_ricciSharp, metricRicciAt_apply_eq_ricciTensor] using
    (basis_repr_eq_sum_inv_inner (I := I) (g t) x basis
      (basisInvMetric (I := I) (g t) x basis) (basisInvMetric_isInverse (I := I) (g t) x basis)
      (ricciSharp (g t) x (basis i)) j)


theorem curvatureTimePolynomialValues_hasDerivWithinAt {n : ℕ} {x : M}
    (g : ℝ → SmoothRiemannianMetric I M) (A : ℕ → ℝ → Tensor0SSpace 4 I x)
    (basis : Module.Basis (Fin n) ℝ (TangentSpace I x)) {J : Set ℝ} {t : ℝ}
    (hzero : A 0 t = metricRm04At (g t) x)
    (hg : ∀ i j, HasDerivWithinAt
      (fun s => (g s).inner x (basis i) (basis j))
      (-2 * metricRicciAt (g t) x (vec2 (basis i) (basis j))) J t)
    (hA : ∀ q, HasDerivWithinAt (A q)
      (A (q + 1) t - covariantEndomorphismAction0S (A q t) (ricciSharp (g t) x)) J t)
    (v : CurvatureTimePolynomialVariable n) :
    HasDerivWithinAt (fun s => curvatureTimePolynomialValues g A basis s v)
      (MvPolynomial.eval (curvatureTimePolynomialValues g A basis t)
        (curvatureTimeEvolution n v)) J t := by
  classical
  cases v with
  | inl ij =>
    have hd := basisInvMetric_hasDerivWithinAt_of_pairings g basis
      (fun a c => metricRicciAt (g t) x (vec2 (basis a) (basis c))) hg ij.1 ij.2
    simpa only [curvatureTimeEvolution, map_mul, map_ofNat, map_sum, MvPolynomial.eval_X,
      curvatureTimePolynomialValues, eval_curvatureTimeRicciPolynomial g A basis hzero]
      using hd
  | inr qs =>
    have hd := (tensor0SEvalCLM (I := I) (fun k => basis (qs.2 k))).hasFDerivAt.comp_hasDerivWithinAt
      t (hA qs.1)
    apply hd.congr_deriv
    change component0S (I := I) basis
      (A (qs.1 + 1) t - covariantEndomorphismAction0S (A qs.1 t) (ricciSharp (g t) x)) qs.2 = _
    have haction : component0S (I := I) basis
        (covariantEndomorphismAction0S (A qs.1 t) (ricciSharp (g t) x)) qs.2 =
        ∑ k : Fin 4, ∑ e : Fin n,
          basis.repr (ricciSharp (g t) x (basis (qs.2 k))) e *
            component0S (I := I) basis (A qs.1 t) (Function.update qs.2 k e) :=
      tensor0SComponent_covariantEndomorphismAction0S basis (A qs.1 t)
        (ricciSharp (g t) x) qs.2
    rw [component0S_sub_field, haction]
    simp only [curvatureTimeEvolution, map_sub, map_sum, map_mul, MvPolynomial.eval_X,
      curvatureTimePolynomialValues, eval_curvatureTimeSharpPolynomial g A basis hzero]

end DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions
