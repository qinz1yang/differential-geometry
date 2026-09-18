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


theorem mixed_curvature_polynomial_on_Ioc
    {D : RealTimeInterval} (S : SolutionOn (I := I) (M := M) D) (hS : IsSolutionOn S)
    {a b t : ℝ} (hcarrier : D.carrier = Icc a b) (hregular : Ioo a b ⊆ D.regular)
    (ht : t ∈ Ioc a b) (p q : ℕ) (x : M) {n : ℕ}
    (basis : Module.Basis (Fin n) ℝ (TangentSpace I x)) :
    DifferentiableWithinAt ℝ (fun s => mixedCurvatureTensor S p q s x) D.carrier t ∧
      ∀ slots, component0S (I := I) basis (mixedCurvatureTensor S p q t x) slots =
        MvPolynomial.eval (curvatureJetPolynomialValues S (p + 2 * q) t basis)
          (mixedJetPolynomial n p q slots) := by
  have hP (q : ℕ) (s : ℝ) (hs : s ∈ Ioo a b) :=
    mixedJetPolynomial_hasDerivWithinAt n p S hS q s (hregular hs) x basis
  rcases ht.2.lt_or_eq with htb | rfl
  · exact ⟨(hP q t ⟨ht.1, htb⟩).1.differentiableWithinAt, (hP q t ⟨ht.1, htb⟩).2⟩
  · simpa only [hcarrier] using
      mixedCurvature_polynomial_terminal_of_regular_Icc S hS p
        le_rfl ht.1 hcarrier hregular (mixedJetPolynomial n p) x basis
        (fun q t ht => ⟨((hP q t ht).1.hasDerivAt
          (D.regular_mem_nhds (hregular ht))).differentiableAt, (hP q t ht).2⟩) q

omit [NeZero (Module.finrank ℝ E)] [SigmaCompactSpace M] in
private theorem exists_mixed_curvature_fields_of_polynomial
    {D : RealTimeInterval} (S : SolutionOn (I := I) (M := M) D)
    (p : ℕ) {J : Set ℝ} (hJ : J ⊆ D.carrier)
    (P : (q : ℕ) → (Fin (4 + p) → Fin (Module.finrank ℝ E)) →
      MvPolynomial (CurvatureJetPolynomialVariable (Module.finrank ℝ E) (p + 2 * q)) ℝ)
    (hactual : ∀ q t, t ∈ J → ∀ x : M,
      ∀ basis : Module.Basis (Fin (Module.finrank ℝ E)) ℝ (TangentSpace I x),
        DifferentiableWithinAt ℝ (fun s => mixedCurvatureTensor S p q s x) D.carrier t ∧
        ∀ slots, component0S (I := I) basis (mixedCurvatureTensor S p q t x) slots =
          MvPolynomial.eval (curvatureJetPolynomialValues S (p + 2 * q) t basis) (P q slots)) :
    ∃ A : ℕ → ℝ → Tensor0SField (I := I) (M := M) (n := ∞) (4 + p),
      ∀ q t, t ∈ J → ∀ x : M,
        A q t x = mixedCurvatureTensor S p q t x ∧
        HasDerivWithinAt (fun s => A q s x)
          (A (q + 1) t x - covariantEndomorphismAction0S (A q t x)
            (ricciSharp (S.base.metric t) x)) J t := by
  classical
  have hfields (q : ℕ) (t : {s : ℝ // s ∈ J}) :
      ∃ B : Tensor0SField (I := I) (M := M) (n := ∞) (4 + p),
        ∀ x : M, B x = mixedCurvatureTensor S p q t.val x :=
    exists_curvature_polynomial_field S (p + 2 * q) (4 + p) t.val (P q)
      (fun x => mixedCurvatureTensor S p q t.val x)
      (fun x basis slots => (hactual q t.val t.property x basis).2 slots)
  choose B hB using hfields
  let A : ℕ → ℝ → Tensor0SField (I := I) (M := M) (n := ∞) (4 + p) :=
    fun q t => if ht : t ∈ J then B q ⟨t, ht⟩ else 0
  have hA (q : ℕ) (t : ℝ) (ht : t ∈ J) (x : M) :
      A q t x = mixedCurvatureTensor S p q t x := by
    simp only [A, dif_pos ht]
    exact hB q ⟨t, ht⟩ x
  refine ⟨A, fun q t ht x => ⟨hA q t ht x, ?_⟩⟩
  have hd := (hactual q t ht x (Module.finBasis ℝ (TangentSpace I x))).1.hasDerivWithinAt
  have hrec : mixedCurvatureTensor S p (q + 1) t x =
      derivWithin (fun s => mixedCurvatureTensor S p q s x) D.carrier t +
        covariantEndomorphismAction0S (mixedCurvatureTensor S p q t x)
          (ricciSharp (S.base.metric t) x) := by
    simp only [mixedCurvatureTensor, iteratedMetricTimeDerivWithin_succ,
      metricTimeDerivWithin]
  have hvalue : derivWithin (fun s => mixedCurvatureTensor S p q s x) D.carrier t =
      mixedCurvatureTensor S p (q + 1) t x -
        covariantEndomorphismAction0S (mixedCurvatureTensor S p q t x)
          (ricciSharp (S.base.metric t) x) := by
    rw [hrec]
    exact (add_sub_cancel_right _ _).symm
  have hd' : HasDerivWithinAt (fun s => mixedCurvatureTensor S p q s x)
      (A (q + 1) t x - covariantEndomorphismAction0S (A q t x)
        (ricciSharp (S.base.metric t) x)) D.carrier t := by
    apply hd.congr_deriv
    exact hvalue.trans (by rw [hA (q + 1) t ht x, hA q t ht x])
  exact (hd'.mono hJ).congr_of_eventuallyEq
    (Filter.eventuallyEq_of_mem self_mem_nhdsWithin fun s hs => hA q s hs x)
    (hA q t ht x)

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
  apply exists_mixed_curvature_fields_of_polynomial (J := Iic b) S p
    (by rw [hcarrier]) P
  intro q t ht x basis
  simpa only [hcarrier] using hactual q t ht x basis

theorem exists_mixed_curvature_fields_on_closed_interval
    {D : RealTimeInterval} (S : SolutionOn (I := I) (M := M) D) (hS : IsSolutionOn S)
    {a c b : ℝ} (hac : a < c) (hcb : c < b)
    (hcarrier : D.carrier = Icc a b) (hregular : Ioo a b ⊆ D.regular) (p : ℕ) :
    ∃ A : ℕ → ℝ → Tensor0SField (I := I) (M := M) (n := ∞) (4 + p),
      ∀ q t, t ∈ Icc c b → ∀ x : M,
        A q t x = mixedCurvatureTensor S p q t x ∧
        HasDerivWithinAt (fun s => A q s x)
          (A (q + 1) t x - covariantEndomorphismAction0S (A q t x)
            (ricciSharp (S.base.metric t) x)) (Icc c b) t := by
  classical
  choose P hP using fun q : ℕ =>
    exists_mixed_curvature_jet_polynomials (Module.finrank ℝ E) p q
  apply exists_mixed_curvature_fields_of_polynomial S p
    (by rw [hcarrier]; exact Icc_subset_Icc_left hac.le) P
  intro q t ht x basis
  rcases ht.2.lt_or_eq with htb | rfl
  · exact ⟨(hP q S hS t (hregular ⟨hac.trans_le ht.1, htb⟩) x basis).1.differentiableWithinAt,
      (hP q S hS t (hregular ⟨hac.trans_le ht.1, htb⟩) x basis).2⟩
  · simpa only [hcarrier] using
      mixedCurvature_polynomial_terminal_of_regular_Icc S hS p
        hac.le hcb hcarrier (Ioo_subset_Ioo_left hac.le |>.trans hregular)
        P x basis (fun q t ht => hP q S hS t (hregular ⟨hac.trans ht.1, ht.2⟩) x basis) q

end DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions
