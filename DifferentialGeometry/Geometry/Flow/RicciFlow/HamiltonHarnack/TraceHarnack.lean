import DifferentialGeometry.Geometry.Flow.RicciFlow.HamiltonHarnack.MatrixHarnack
import DifferentialGeometry.Geometry.Flow.RicciFlow.HamiltonHarnack.TraceHarnackAlgebra
import DifferentialGeometry.Geometry.Flow.RicciFlow.HamiltonHarnack.MIdentities
import DifferentialGeometry.Tensor.RSTensor.CotangentRiemannian

set_option autoImplicit false

noncomputable section

namespace DifferentialGeometry.PDE.RicciFlow

open Bundle DifferentialGeometry.Tensor0SBundle
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Geometry.Operator
open DifferentialGeometry.Analysis.Spectral
open scoped Manifold ContDiff BigOperators

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace Real E]
variable [FiniteDimensional Real E]
variable {H : Type*} [TopologicalSpace H]
variable {I : ModelWithCorners Real E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
variable [IsManifold I ∞ M] [IsManifold I 1 M]
variable [CompleteSpace E] [SigmaCompactSpace M] [T2Space M]

theorem hamilton_trace_harnack
    [I.Boundaryless] [NeZero (Module.finrank Real E)]
    {D : RealTimeInterval}
    (S : SolutionOn (I := I) (M := M) D)
    (hS : IsSolutionOn (I := I) S)
    (hcomplete : ∀ t ∈ D.regular,
      RiemannianMetricComplete (I := I) (S.base.metric t))
    (hcurv : ∀ a b : Real, Set.Icc a b ⊆ D.regular →
      ∃ C : Real, ∀ t ∈ Set.Icc a b, ∀ x : M,
        normSq0S (I := I) (S.base.metric t) x 4 (S.base.rm04 t x) ≤ C)
    (hR : ∀ t ∈ D.regular, ∀ x : M,
      metricAlgebraicCurvatureTensorAt
        (I := I) (M := M) (S.base.metric t) x ∈
          algebraicCurvatureOperatorNonnegativeCone (I := I) (M := M))
    (clock : HarnackClock)
    (hclock : Set.Icc clock.origin clock.time ⊆ D.regular)
    (x : M) (V : TangentSpace I x) :
    0 ≤ deriv (fun s : Real => S.scalar s x) clock.time +
        S.scalar clock.time x / clock.elapsed +
      2 * (S.base.metric clock.time).inner x
        (gradientAt (I := I) (flowG (I := I) S) clock.time
          (S.scalar clock.time) x) V +
      2 * metricRicci (I := I) (M := M) (S.base.metric clock.time) x
        (vec2 V V) := by
  classical
  let g := S.base.metric clock.time
  obtain ⟨basis, hON⟩ := exists_gOrthonormalBasis (I := I) g x
  have hinv : MetricInverseInBasisGen (I := I) (M := M) g x basis
      (identityInvMetric (Idx := Fin (Module.finrank Real (TangentSpace I x)))) :=
    metricInverseInBasis_of_orthonormal (I := I) g basis hON
  let v : Fin (Module.finrank Real (TangentSpace I x)) → Real :=
    fun a => basis.repr V a
  have hrepr : ∀ a, v a = g.inner x V (basis a) := by
    intro a
    change basis.repr V a = g.inner x V (basis a)
    rw [basis_repr_eq_sum_inv_inner (I := I) g x basis _ hinv V a]
    simp [identityInvMetric, diagonalInvMetric]
  have hcoord : ∀ a b, basis.coord a (basis b) = if b = a then 1 else 0 := by
    intro a b
    simp [Module.Basis.coord_apply, Finsupp.single_apply]
  let scalarFun : M → Real := fun y => metricScalarAt (I := I) (M := M) g y
  have hscalarFun : scalarFun = S.scalar clock.time := by
    funext y
    simp [scalarFun, g, metricScalarAt, SolutionOn.scalar_eq_metricTrace,
      SolutionOn.ricciAt, SolutionFamily.ricciAt]
  let dR : Fin (Module.finrank Real (TangentSpace I x)) → Real := fun a =>
    differential1FormFun (I := I) scalarFun x (fun _ : Fin 1 => basis a)
  let R : Fin (Module.finrank Real (TangentSpace I x)) →
      Fin (Module.finrank Real (TangentSpace I x)) →
      Fin (Module.finrank Real (TangentSpace I x)) →
      Fin (Module.finrank Real (TangentSpace I x)) → Real := fun a b c d =>
    tensor04StdAt (I := I) (M := M) (S.base.rm04 clock.time x)
      (basis a) (basis b) (basis c) (basis d)
  let P : Fin (Module.finrank Real (TangentSpace I x)) →
      Fin (Module.finrank Real (TangentSpace I x)) →
      Fin (Module.finrank Real (TangentSpace I x)) → Real := fun a b c =>
    hamiltonPAt (I := I) g x ![basis a, basis b, basis c]
  let Mc : Fin (Module.finrank Real (TangentSpace I x)) →
      Fin (Module.finrank Real (TangentSpace I x)) → Real := fun a b =>
    hamiltonMAt (I := I) clock g x ![basis a, basis b]
  have hBlock : ∀ r, 0 ≤ hamiltonBlockPolarized
      (fun a b c d => R a b d c) P Mc
      (fun a b => hamiltonTraceWedge v r a b)
      (fun a b => hamiltonTraceWedge v r a b)
      (hamiltonTraceWeight r) (hamiltonTraceWeight r) := by
    intro r
    let er : StrongDual Real (TangentSpace I x) :=
      (basis.coord r).toContinuousLinearMap
    let U : HamiltonHarnackTwoForm (TangentSpace I x) :=
      normalizedWedge (g.inner x V) er
    let W : Tensor0SSpace 1 I x := dualToCotangentGen (I := I) (basis.coord r)
    have hU : ∀ a b, U ![basis a, basis b] = hamiltonTraceWedge v r a b := by
      intro a b
      rw [normalizedWedge_apply]
      simp only [Matrix.cons_val_zero, Matrix.cons_val_one, er]
      rw [← hrepr a, ← hrepr b]
      simp only [LinearMap.coe_toContinuousLinearMap']
      rw [hcoord r a, hcoord r b]
      rfl
    have hW : ∀ a, W ![basis a] = hamiltonTraceWeight r a := by
      intro a
      change basis.coord r (basis a) = hamiltonTraceWeight r a
      rw [hcoord r a]
      rfl
    have hmatrix := hamilton_matrix_harnack (I := I) S hS hcomplete hcurv hR
      clock hclock x U W
    rw [hamiltonHarnackQuadraticAt_eq_hamiltonBlockQuadratic
      (I := I) S clock x U W basis hinv,
      hamiltonBlockQuadratic_eq_hamiltonQuadraticForm] at hmatrix
    rw [hamiltonBlockPolarized_diag]
    simpa only [R, P, Mc, g, hU, hW] using hmatrix
  have hPFirst : ∀ a, (∑ c, P c a c) = -(1 / 2 : Real) * dR a := by
    intro a
    have h := hamiltonPAt_first_trace (I := I) g basis
      (identityInvMetric (Idx := Fin (Module.finrank Real (TangentSpace I x))))
      hinv (basis a)
    simp only [dR]
    calc
      (∑ c, P c a c) = ∑ c, hamiltonPAt (I := I) g x
          (vec3 (basis c) (basis a) (basis c)) := by
        apply Finset.sum_congr rfl
        intro c _
        simp only [P]
        congr 1
        funext q
        fin_cases q <;> rfl
      _ = -(1 / 2 : Real) * differential1FormFun (I := I) scalarFun x
          (fun _ : Fin 1 => basis a) := by
        simpa [scalarFun, identityInvMetric, diagonalInvMetric] using h
  have hPSecond : ∀ a, (∑ c, P a c c) = (1 / 2 : Real) * dR a := by
    intro a
    have h := hamiltonPAt_second_trace (I := I) g basis
      (identityInvMetric (Idx := Fin (Module.finrank Real (TangentSpace I x))))
      hinv (basis a)
    simp only [dR]
    calc
      (∑ c, P a c c) = ∑ c, hamiltonPAt (I := I) g x
          (vec3 (basis a) (basis c) (basis c)) := by
        apply Finset.sum_congr rfl
        intro c _
        simp only [P]
        congr 1
        funext q
        fin_cases q <;> rfl
      _ = (1 / 2 : Real) * differential1FormFun (I := I) scalarFun x
          (fun _ : Fin 1 => basis a) := by
        simpa [scalarFun, identityInvMetric, diagonalInvMetric] using h
  have hForm : IsAlgCurvForm (fun X Y Z W : TangentSpace I x =>
      tensor04StdAt (I := I) (M := M) (S.base.rm04 clock.time x) X Y Z W) :=
    mem_algebraicCurvatureTensorSubmodule.mp
      (metricRm04At_mem_algebraicCurvatureTensorSubmodule
        (I := I) (S.base.metric clock.time) x)
  have hRFirst : ∀ a b c d, R a b c d = -R b a c d := by
    intro a b c d
    exact hForm.anti_first _ _ _ _
  have hRLast : ∀ a b c d, R a b c d = -R a b d c := by
    intro a b c d
    exact hForm.anti_last _ _ _ _
  have hRPair : ∀ a b c d, R a b c d = R c d a b := by
    intro a b c d
    exact hForm.pair_swap _ _ _ _
  have hAlgebra : 0 ≤ (∑ a, Mc a a) + ∑ a, dR a * v a +
      ∑ a, ∑ b, hamiltonRicciContraction R a b * v a * v b :=
    hamilton_trace_from_block_nonneg R P Mc v dR hBlock hPFirst hPSecond
      hRFirst hRLast hRPair
  have ht : clock.time ∈ D.regular :=
    hclock ⟨clock.origin_lt_time.le, le_rfl⟩
  have hMsum :
      (∑ a, Mc a a) =
        (1 / 2 : Real) *
          (deriv (fun s : Real => S.scalar s x) clock.time +
            S.scalar clock.time x / clock.elapsed) := by
    calc
      (∑ a, Mc a a) = metricTracePair0SAt (I := I) g
          (hamiltonMAt (I := I) clock g x) := by
        rw [metricTracePair0SAt_eq_sum_basis (I := I) g basis
          (identityInvMetric (Idx := Fin (Module.finrank Real (TangentSpace I x))))
          hinv]
        simp only [Mc, identityInvMetric, diagonalInvMetric, ite_mul, one_mul, zero_mul,
          Finset.sum_ite_eq, Finset.mem_univ, ↓reduceIte]
        apply Finset.sum_congr rfl
        intro a _
        congr 1
        funext q
        fin_cases q <;> rfl
      _ = (1 / 2 : Real) *
          (deriv (fun s : Real => S.scalar s x) clock.time +
            S.scalar clock.time x / clock.elapsed) := by
        simpa [g] using hamiltonMAt_metricTrace_eq (I := I) S hS clock ht x
  let dScalar := differential1FormFun (I := I) scalarFun x
  have hdExpand := tensor0S_apply_eq_sum (I := I) basis dScalar (fun _ : Fin 1 => V)
  rw [sum_fin_one_fun] at hdExpand
  have hdSum :
      (∑ a, dR a * v a) =
        g.inner x (gradientAt (I := I) (flowG (I := I) S) clock.time
          (S.scalar clock.time) x) V := by
    calc
      (∑ a, dR a * v a) = dScalar (fun _ : Fin 1 => V) := by
        rw [hdExpand]
        apply Finset.sum_congr rfl
        intro a _
        simp [dR, v, dScalar, component0S_apply, Module.Basis.coord_apply]
      _ = g.inner x (gradientFun (I := I) g scalarFun x) V :=
        differential1FormFun_apply_eq_inner_gradientFun (I := I) g scalarFun x V
      _ = g.inner x (gradientAt (I := I) (flowG (I := I) S) clock.time
          (S.scalar clock.time) x) V := by
        simp [gradientAt, flowG, g, hscalarFun]
  let Ric := metricRicci (I := I) (M := M) g x
  let K := metricCurvData (I := I) (M := M) g
  have hLower : Rm04LowersRm13At (I := I) g x
      (metricRm13 (I := I) (M := M) g x)
      (metricRm04 (I := I) (M := M) g x) :=
    rm04LowersRm13At_of_realizes (I := I) g (metricCov (I := I) (M := M) g)
      (metricRm13 (I := I) (M := M) g)
      (metricRm04 (I := I) (M := M) g) K.rm13Realizes K.rm04Realizes x
  have hRicTrace : RicciRealizesRm04FirstTraceAt (I := I) Ric
      (metricRm04 (I := I) (M := M) g x)
      (identityInvMetric (Idx := Fin (Module.finrank Real (TangentSpace I x))))
      basis := by
    exact ricciFirstTraceAt_of_rm13_section (I := I) g basis
      (identityInvMetric (Idx := Fin (Module.finrank Real (TangentSpace I x))))
      hinv (metricRicci (I := I) (M := M) g)
      (metricRm13 (I := I) (M := M) g)
      (metricRm04 (I := I) (M := M) g) K.ricciRealizes hLower
  have hRicCoord : ∀ a b, hamiltonRicciContraction R a b =
      Ric (vec2 (basis a) (basis b)) := by
    intro a b
    have h := hRicTrace a b
    simpa [hamiltonRicciContraction, R, Ric, g, identityInvMetric,
      diagonalInvMetric, SolutionFamily.rm04, SolutionFamily.rm04At] using h.symm
  have hRicExpand := tensor0S_apply_eq_sum (I := I) basis Ric (vec2 V V)
  rw [sum_fin_two_fun] at hRicExpand
  have hRicSum :
      (∑ a, ∑ b, hamiltonRicciContraction R a b * v a * v b) =
        Ric (vec2 V V) := by
    rw [hRicExpand]
    apply Finset.sum_congr rfl
    intro a _
    apply Finset.sum_congr rfl
    intro b _
    rw [hRicCoord]
    simp only [Fin.isValue, component0S_apply, Module.Basis.coord_apply,
      Fin.prod_univ_two, ↓reduceIte, one_ne_zero]
    have hslots : (fun q : Fin 2 => basis (if q = 0 then a else b)) =
        vec2 (basis a) (basis b) := by
      funext q
      fin_cases q <;> rfl
    rw [hslots]
    simp only [v, vec2, ↓reduceIte, one_ne_zero]
    rw [mul_assoc]
  rw [hMsum, hdSum, hRicSum] at hAlgebra
  dsimp only [g, Ric] at hAlgebra
  linarith

end DifferentialGeometry.PDE.RicciFlow
