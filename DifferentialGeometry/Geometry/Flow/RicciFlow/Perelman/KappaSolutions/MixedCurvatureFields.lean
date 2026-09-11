import DifferentialGeometry.Geometry.Flow.RicciFlow.Evolution.Curvature.PolynomialField
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.KappaSolutions.MixedCurvatureTerminal
import DifferentialGeometry.Geometry.Flow.RicciFlow.Evolution.Curvature.MixedJetPolynomials


set_option autoImplicit false

noncomputable section

namespace DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions

open Bundle Manifold Filter Set
open DifferentialGeometry.Tensor0SBundle DifferentialGeometry.Geometry.Curvature
open scoped Manifold ContDiff _root_.Topology

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [CompleteSpace E] [NeZero (Module.finrank ℝ E)]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [T2Space M] [SigmaCompactSpace M]

private local instance mixedFieldC1 : IsManifold I 1 M :=
  IsManifold.of_le (I := I) (M := M) (n := ∞) (by decide)
private local instance mixedFieldC2 : IsManifold I 2 M :=
  IsManifold.of_le (I := I) (M := M) (n := ∞) (by decide)


theorem exists_ancient_mixed_curvature_fields
    {D : RealTimeInterval} (S : SolutionOn (I := I) (M := M) D) (hS : IsSolutionOn S)
    {b : ℝ} (hcarrier : D.carrier = Iic b) (hregular : D.regular = Iio b) (p : ℕ) :
    ∃ A : ℕ → ℝ → Tensor0SField (I := I) (M := M) (n := ∞) (4 + p),
      ∀ q : ℕ, ∀ t : ℝ, t ≤ b → ∀ x : M,
        A q t x = mixedCurvatureTensor S p q t x ∧
        HasDerivWithinAt (fun s => A q s x)
          (A (q + 1) t x - covariantEndomorphismAction0S (A q t x)
            (ricciSharp (S.base.metric t) x)) (Iic b) t := by
  classical
  choose P hP using fun q : ℕ =>
    exists_mixed_curvature_jet_polynomials (Module.finrank ℝ E) p q
  have hactual (q : ℕ) (t : ℝ) (ht : t ≤ b) (x : M)
      (basis : Module.Basis (Fin (Module.finrank ℝ E)) ℝ (TangentSpace I x)) :
      DifferentiableWithinAt ℝ (fun s => mixedCurvatureTensor S p q s x) (Iic b) t ∧
      ∀ slots, component0S (I := I) basis (mixedCurvatureTensor S p q t x) slots =
        MvPolynomial.eval (curvatureJetPolynomialValues S (p + 2 * q) t basis)
          (P q slots) := by
    rcases ht.lt_or_eq with htneg | htb
    · have htr : t ∈ D.regular := by rwa [hregular]
      obtain ⟨hd, hcomp⟩ := hP q S hS t htr x basis
      exact ⟨hd.differentiableWithinAt, hcomp⟩
    · subst t
      have hreg : Ioo (b - 1) b ⊆ D.regular := by
        intro t ht
        rw [hregular]
        exact ht.2
      exact mixedCurvature_polynomial_terminal_of_regular S hS p
        (by linarith : b - 1 < b) hcarrier hreg P x basis
        (fun q t ht => hP q S hS t (hreg ht) x basis) q
  have hfields (q : ℕ) (t : {s : ℝ // s ≤ b}) :
      ∃ B : Tensor0SField (I := I) (M := M) (n := ∞) (4 + p),
        ∀ x : M, B x = mixedCurvatureTensor S p q t.val x :=
    exists_curvature_polynomial_field S (p + 2 * q) (4 + p) t.val (P q)
      (fun x => mixedCurvatureTensor S p q t.val x)
      (fun x basis slots => (hactual q t.val t.property x basis).2 slots)
  choose B hB using hfields
  let A : ℕ → ℝ → Tensor0SField (I := I) (M := M) (n := ∞) (4 + p) :=
    fun q t => if ht : t ≤ b then B q ⟨t, ht⟩ else 0
  have hA (q : ℕ) (t : ℝ) (ht : t ≤ b) (x : M) :
      A q t x = mixedCurvatureTensor S p q t x := by
    simp only [A, dif_pos ht]
    exact hB q ⟨t, ht⟩ x
  refine ⟨A, fun q t ht x => ⟨hA q t ht x, ?_⟩⟩
  have hd := (hactual q t ht x (Module.finBasis ℝ (TangentSpace I x))).1.hasDerivWithinAt
  have hrec : mixedCurvatureTensor S p (q + 1) t x =
      derivWithin (fun s => mixedCurvatureTensor S p q s x) (Iic b) t +
        covariantEndomorphismAction0S (mixedCurvatureTensor S p q t x)
          (ricciSharp (S.base.metric t) x) := by
    simp only [mixedCurvatureTensor, iteratedMetricTimeDerivWithin_succ,
      metricTimeDerivWithin, hcarrier]
  have hvalue : derivWithin (fun s => mixedCurvatureTensor S p q s x) (Iic b) t =
      mixedCurvatureTensor S p (q + 1) t x -
        covariantEndomorphismAction0S (mixedCurvatureTensor S p q t x)
          (ricciSharp (S.base.metric t) x) := by
    rw [hrec]
    exact (add_sub_cancel_right _ _).symm
  have hd' : HasDerivWithinAt (fun s => mixedCurvatureTensor S p q s x)
      (A (q + 1) t x - covariantEndomorphismAction0S (A q t x)
        (ricciSharp (S.base.metric t) x)) (Iic b) t := by
    apply hd.congr_deriv
    exact hvalue.trans (by rw [hA (q + 1) t ht x, hA q t ht x])
  exact hd'.congr_of_eventuallyEq
    (Filter.eventuallyEq_of_mem self_mem_nhdsWithin fun s hs => hA q s hs x)
    (hA q t ht x)

end DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions
