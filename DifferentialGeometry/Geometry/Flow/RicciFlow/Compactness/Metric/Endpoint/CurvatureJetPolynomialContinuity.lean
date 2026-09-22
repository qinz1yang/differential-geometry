import DifferentialGeometry.Geometry.Flow.RicciFlow.Evolution.Metric.TimeCoefficientContinuity
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.TerminalCurvatureJets
import DifferentialGeometry.Geometry.Curvature.Metric.LeviCivita

set_option autoImplicit false

noncomputable section

namespace DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions

open Bundle _root_.Manifold Filter DifferentialGeometry.Tensor0SBundle
open DifferentialGeometry.Geometry.Curvature
open CanonicalNeighborhood.FiniteHorn
open scoped _root_.Manifold ContDiff _root_.Topology

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [CompleteSpace E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [T2Space M] [SigmaCompactSpace M]

private local instance flowPolynomialC1 : IsManifold I 1 M :=
  IsManifold.of_le (I := I) (M := M) (n := ∞) (by decide)
private local instance flowPolynomialC2 : IsManifold I 2 M :=
  IsManifold.of_le (I := I) (M := M) (n := ∞) (by decide)

omit [I.Boundaryless] [SigmaCompactSpace M] in theorem solution_metricPair_continuousWithinAt_terminal
    {D : RealTimeInterval} (S : SolutionOn (I := I) (M := M) D) (hS : IsSolutionOn S)
    {a b : ℝ} (hab : a < b) (hslab : Set.Icc a b ⊆ D.carrier)
    (x : M) (v w : TangentSpace I x) :
    ContinuousWithinAt (fun t => (S.base.metric t).inner x v w) (Set.Iio b) b := by
  have hnear : D.carrier ∈ 𝓝[<] b :=
    Filter.mem_of_superset (Ioo_mem_nhdsLT hab) (Set.Ioo_subset_Icc_self.trans hslab)
  exact ((hS.smoothMetric.coeff_cont x v w) b (hslab ⟨hab.le, le_rfl⟩)).mono_of_mem_nhdsWithin hnear

omit [SigmaCompactSpace M] in theorem solution_ricciTensorPair_continuousWithinAt_terminal
    {D : RealTimeInterval} (S : SolutionOn (I := I) (M := M) D) (hS : IsSolutionOn S)
    {a b : ℝ} (hab : a < b) (hslab : Set.Icc a b ⊆ D.carrier)
    (x : M) (v w : TangentSpace I x) :
    ContinuousWithinAt (fun t => ricciTensor (I := I) (S.base.metric t) x v w)
      (Set.Iio b) b := by
  have hnear : D.carrier ∈ 𝓝[<] b :=
    Filter.mem_of_superset (Ioo_mem_nhdsLT hab) (Set.Ioo_subset_Icc_self.trans hslab)
  have hc : ContinuousOn (fun t => S.ricci t x (vec2 v w)) D.carrier := by
    rw [continuousOn_iff_continuous_domRestrict]
    exact hS.ricciCont.eval_continuous (P := {t : ℝ // t ∈ D.carrier})
      (τ := Subtype.val) (b := fun _ => x) continuous_subtype_val
      (fun t => t.2) continuous_const
      (v := fun k _ => vec2 v w k) (fun _ => continuous_const)
  have heq (t : ℝ) : S.ricci t x (vec2 v w) =
      ricciTensor (I := I) (S.base.metric t) x v w := by
    change metricRicciAt (I := I) (S.base.metric t) x (vec2 v w) = _
    exact metricRicciAt_apply_eq_ricciTensor (I := I) (S.base.metric t) x v w
  simpa only [heq] using
    (hc b (hslab ⟨hab.le, le_rfl⟩)).mono_of_mem_nhdsWithin hnear

theorem solution_curvatureJetPolynomialValues_continuousWithinAt_terminal
    {D : RealTimeInterval} (S : SolutionOn (I := I) (M := M) D) (hS : IsSolutionOn S)
    {a b : ℝ} (hab : a < b) (hslab : Set.Icc a b ⊆ D.carrier)
    (hreg : Set.Ioo a b ⊆ D.regular) (N : ℕ) {n : ℕ} {x : M}
    (basis : Module.Basis (Fin n) ℝ (TangentSpace I x))
    (i : CurvatureJetPolynomialVariable n N) :
    ContinuousWithinAt (fun t => curvatureJetPolynomialValues S N t basis i) (Set.Iio b) b := by
  cases i with
  | inl ij =>
    exact basisInvMetric_continuousWithinAt S.base.metric basis
      (fun j k => solution_metricPair_continuousWithinAt_terminal S hS hab hslab x
        (basis j) (basis k)) ij.1 ij.2
  | inr js =>
    have hn : n ≠ 0 := by
      intro hn
      subst n
      exact Fin.elim0 (js.2 0)
    have hdim : Module.finrank ℝ E = n := by
      calc
        Module.finrank ℝ E = Module.finrank ℝ (TangentSpace I x) :=
          (tangentSpaceModelContinuousLinearEquiv (I := I) x).toLinearEquiv.finrank_eq.symm
        _ = n := by
          simpa only [Fintype.card_fin] using Module.finrank_eq_card_basis basis
    let _ : NeZero (Module.finrank ℝ E) := ⟨by rw [hdim]; exact hn⟩
    exact (solution_nablaKRm04_eval_continuousWithinAt_terminal S hS hab hslab hreg js.1.val x
      (fun k => basis (js.2 k))).mono Set.Iio_subset_Iic_self

theorem solution_curvatureJetPolynomialTensor_continuousWithinAt_terminal
    {D : RealTimeInterval} (S : SolutionOn (I := I) (M := M) D) (hS : IsSolutionOn S)
    {a b : ℝ} (hab : a < b) (hslab : Set.Icc a b ⊆ D.carrier)
    (hreg : Set.Ioo a b ⊆ D.regular) (N : ℕ) {n r : ℕ} {x : M}
    (basis : Module.Basis (Fin n) ℝ (TangentSpace I x))
    (P : (Fin r → Fin n) → MvPolynomial (CurvatureJetPolynomialVariable n N) ℝ) :
    ContinuousWithinAt (fun t => tensorOfPolynomialComponents basis P
      (curvatureJetPolynomialValues S N t basis)) (Set.Iio b) b :=
  tensorOfPolynomialComponents_continuousWithinAt basis P
    (solution_curvatureJetPolynomialValues_continuousWithinAt_terminal S hS hab hslab hreg N basis)

omit [SigmaCompactSpace M] in theorem solution_metricTimeCorrection_continuousWithinAt_terminal
    {D : RealTimeInterval} (S : SolutionOn (I := I) (M := M) D) (hS : IsSolutionOn S)
    {a b : ℝ} (hab : a < b) (hslab : Set.Icc a b ⊆ D.carrier)
    {n r : ℕ} {x : M} (basis : Module.Basis (Fin n) ℝ (TangentSpace I x))
    {A : ℝ → Tensor0SSpace r I x} (hA : ContinuousWithinAt A (Set.Iio b) b) :
    ContinuousWithinAt
      (fun t => covariantEndomorphismAction0S (A t) (ricciSharp (S.base.metric t) x))
      (Set.Iio b) b :=
  metricTimeCorrection_continuousWithinAt S.base.metric basis hA
    (fun i j => solution_metricPair_continuousWithinAt_terminal S hS hab hslab x (basis i) (basis j))
    (fun i j => solution_ricciTensorPair_continuousWithinAt_terminal S hS hab hslab x (basis i) (basis j))

end DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions

end
