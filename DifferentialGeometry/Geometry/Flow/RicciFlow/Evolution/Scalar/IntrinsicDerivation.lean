import DifferentialGeometry.Geometry.Flow.RicciFlow.Evolution.Ricci.CoordinateRegularity
import DifferentialGeometry.Geometry.Flow.RicciFlow.Evolution.Scalar
import DifferentialGeometry.Geometry.Flow.RicciFlow.Evolution.Scalar.TraceAlgebra
import DifferentialGeometry.Tensor.RSTensor.MetricTrace.Higher
import DifferentialGeometry.Geometry.Operator.HessianTraceRealization

set_option autoImplicit false
set_option linter.style.longLine false
set_option linter.unusedSectionVars false

/-!
# Scalar-curvature diffusion bridge

This file proves the realization-level identity

`scalarLaplacianTraceInFrame (coordInv S x₀) (coordRoughRic S x₀ (coordNab2Ric S x₀)) t x₀
  = laplacianAt (flowG S) t (S.scalar t) x₀`

i.e. the scalar-curvature heat term `g^{ab} (∇_a ∇_b Ric)_{ij} g^{ij}` realizes
`ΔR`.  The metric trace commutes with the Laplacian because `∇g = 0`.
-/

noncomputable section

namespace DifferentialGeometry.PDE.RicciFlow

open Bundle Tensor0SBundle
open DifferentialGeometry.Tensor.Coordinates
open DifferentialGeometry.Integral.Connection
open scoped Manifold ContDiff BigOperators

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace Real E]
variable [FiniteDimensional Real E]
variable {H : Type*} [TopologicalSpace H]
variable {I : ModelWithCorners Real E H} [I.Boundaryless]
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
variable [IsManifold I 1 M]
variable [CompleteSpace E] [SigmaCompactSpace M] [T2Space M]

/-- Swap the two traced index pairs in a four-fold finite sum. -/
private theorem sum_swap_four_local
    {Idx : Type*} [Fintype Idx] {R : Type*} [AddCommMonoid R]
    (F : Idx -> Idx -> Idx -> Idx -> R) :
    (∑ i : Idx, ∑ j : Idx, ∑ a : Idx, ∑ b : Idx, F i j a b) =
      ∑ a : Idx, ∑ b : Idx, ∑ i : Idx, ∑ j : Idx, F i j a b := by
  calc
    (∑ i : Idx, ∑ j : Idx, ∑ a : Idx, ∑ b : Idx, F i j a b) =
        ∑ i : Idx, ∑ a : Idx, ∑ j : Idx, ∑ b : Idx, F i j a b := by
          refine Finset.sum_congr rfl fun i _ => ?_
          rw [Finset.sum_comm]
    _ = ∑ a : Idx, ∑ i : Idx, ∑ j : Idx, ∑ b : Idx, F i j a b := by
          rw [Finset.sum_comm]
    _ = ∑ a : Idx, ∑ b : Idx, ∑ i : Idx, ∑ j : Idx, F i j a b := by
          refine Finset.sum_congr rfl fun a _ => ?_
          calc
            (∑ i : Idx, ∑ j : Idx, ∑ b : Idx, F i j a b) =
                ∑ i : Idx, ∑ b : Idx, ∑ j : Idx, F i j a b := by
                  refine Finset.sum_congr rfl fun i _ => ?_
                  rw [Finset.sum_comm]
            _ = ∑ b : Idx, ∑ i : Idx, ∑ j : Idx, F i j a b := by
                  rw [Finset.sum_comm]

/-- The connection of a solution at time `t` is `∞`-smooth (Levi-Civita). -/
private theorem connSmoothInf
    {D : DifferentialGeometry.Integral.Connection.RealTimeInterval}
    (S : SolutionOn (I := I) (M := M) D) (t : Real) :
    CovariantDerivative.ContMDiffCovariantDerivativeLocally
      (S.family.connection t) (∞ : WithTop ℕ∞) := by
  simpa [SolutionFamily.connection, metricCov] using
    metricCov_smooth (I := I) (M := M) (S.base.metric t)

/-- Metric compatibility for a solution at time `t`. -/
private theorem isMetricCompatibleSol
    {D : DifferentialGeometry.Integral.Connection.RealTimeInterval}
    (S : SolutionOn (I := I) (M := M) D) (t : Real) :
    DifferentialGeometry.Integral.Connection.IsMetricCompatible_gen (I := I)
      (S.family.connection t) (S.family.metric t) := by
  simpa [SolutionFamily.connection, SolutionOn.family_metric] using
    DifferentialGeometry.Integral.Connection.leviCivitaConnectionOfMetric_isMetricCompatible
      (I := I) (S.base.metric t)

/-- The canonical first covariant-derivative tensor field of Ricci. -/
private def nablaRicField
    {D : DifferentialGeometry.Integral.Connection.RealTimeInterval}
    (S : SolutionOn (I := I) (M := M) D) (t : Real) :
    Tensor0SField (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      (n := (∞ : WithTop ℕ∞)) 3 :=
  totalNabla0S (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
    2 (S.family.connection t) (S.ricci t)
    (totalNabla0S_reg (E := E) (H := H) (I := I) (M := M)
      2 (S.family.connection t) (connSmoothInf (I := I) S t) (S.ricci t))

/-- The canonical second covariant-derivative tensor field of Ricci. -/
private def nabla2RicField
    {D : DifferentialGeometry.Integral.Connection.RealTimeInterval}
    (S : SolutionOn (I := I) (M := M) D) (t : Real)
    (x : M) :
    Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) 4 x :=
  totalNabla0SFun (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
    3 (S.family.connection t) (nablaRicField (I := I) S t) x

/-- The CRUX: the explicit christoffel-formula second covariant derivative of
Ricci in the coordinate frame realizes the abstract second covariant derivative
tensor at the coordinate center. -/
theorem coordNab2Ric_eq_nabla2RicField
    {D : DifferentialGeometry.Integral.Connection.RealTimeInterval}
    (S : SolutionOn (I := I) (M := M) D)
    (x₀ : M) (t : Real)
    (d a i j : CoordinateIdx (𝕜 := Real) E) :
    coordNab2Ric (I := I) S x₀ t x₀ d a i j =
      nabla2RicField (I := I) S t x₀
        (DifferentialGeometry.Integral.Connection.vec4 (I := I)
          (coordinateFrameAt (I := I) x₀ d x₀)
          (coordinateFrameAt (I := I) x₀ a x₀)
          (coordinateFrameAt (I := I) x₀ i x₀)
          (coordinateFrameAt (I := I) x₀ j x₀)) := by
  classical
  set cov := S.family.connection t with hcov_def
  set frame := coordinateFrameAt (I := I) x₀ with hframe_def
  set nablaA := nablaRicField (I := I) S t with hnablaA_def
  -- realize the leading derivative direction by a smooth section
  obtain ⟨Dsec, hDsec⟩ :=
    ContMDiffSection.exists_eq_at_gen
      (I := I) (F := E) (V := TangentSpace I) (n := (⊤ : ℕ∞)) x₀ (frame d x₀)
  -- the three moving frame slots
  let slot : Fin 3 -> CoordinateIdx (𝕜 := Real) E :=
    fun q => if q = 0 then a else if q = 1 then i else j
  let V : Fin 3 -> (p : M) -> TangentSpace I p :=
    fun q p => frame (slot q) p
  have hVq : ∀ q : Fin 3, V q = frame (slot q) := fun q => rfl
  have hVslots :
      (fun q : Fin 3 => V q x₀) =
        DifferentialGeometry.Integral.Connection.vec3 (I := I)
          (frame a x₀) (frame i x₀) (frame j x₀) := by
    funext q
    fin_cases q <;> simp [V, slot, DifferentialGeometry.Integral.Connection.vec3]
  -- smoothness of each frame slot
  have hV_at : ∀ q : Fin 3,
      ContMDiffAt I (I.prod 𝓘(Real, E)) (∞ : WithTop ℕ∞)
        (fun p : M => (⟨p, V q p⟩ : TotalSpace E (TangentSpace I : M -> Type _))) x₀ := by
    intro q
    have hgen : ∀ k : CoordinateIdx (𝕜 := Real) E,
        ContMDiffAt I (I.prod 𝓘(Real, E)) (∞ : WithTop ℕ∞)
          (fun p : M => (⟨p, frame k p⟩ : TotalSpace E (TangentSpace I : M -> Type _))) x₀ := by
      intro k
      exact (coordinateFrameAt_isLocalFrame (I := I) x₀).contMDiffAt
        (coordinateFrameSet_open (I := I) x₀) (coordinateFrameAt_mem (I := I) x₀) k
    fin_cases q <;> simpa [V] using hgen _
  have hV : ∀ q : Fin 3, MDiffAt (T% (V q)) x₀ :=
    fun q => (hV_at q).mdifferentiableAt (by simp)
  have hVmodel : ∀ q : Fin 3,
      DifferentiableWithinAt Real
        (TensorLieDeriv.tangentFieldModelInChart (𝕜 := Real) (I := I) x₀ (V q))
        (Set.range I) (extChartAt I x₀ x₀) :=
    fun q =>
      Tensor0SBundle.tangentFieldModelInChart_differentiableWithinAt_center_of_contMDiffAt
        (I := I) (V q) x₀ (hV_at q)
  have hcoord : ∀ q : Fin 3, ∀ k : Fin (Module.finrank Real E),
      MDifferentiableAt I 𝓘(Real, Real)
        (fun p : M =>
          (Module.finBasis Real E).coord k
            (TensorLieDeriv.tangentFieldModelInChart (𝕜 := Real) (I := I) x₀ (V q)
              (extChartAt I x₀ p))) x₀ :=
    fun q k =>
      Tensor0SBundle.tangentFieldModelInChart_coord_mdiffAt_center_of_contMDiffAt
        (I := I) (V q) x₀ (hV_at q) k
  -- the pairing function equals the nablaRicComp component
  have hnablaA_eval : ∀ p : M,
      nablaA p
          (DifferentialGeometry.Integral.Connection.vec3 (I := I)
            (frame a p) (frame i p) (frame j p)) =
        nablaRicComp (I := I) S frame t p a i j := by
    intro p
    rfl
  have hpair : MDifferentiableAt I 𝓘(Real, Real)
      (fun p : M => nablaA p (fun q : Fin 3 => V q p)) x₀ := by
    have heq :
        (fun p : M => nablaA p (fun q : Fin 3 => V q p)) =
          fun p : M => nablaRicComp (I := I) S frame t p a i j := by
      funext p
      have : (fun q : Fin 3 => V q p) =
          DifferentialGeometry.Integral.Connection.vec3 (I := I)
            (frame a p) (frame i p) (frame j p) := by
        funext q
        fin_cases q <;> simp [V, slot, DifferentialGeometry.Integral.Connection.vec3]
      rw [this, hnablaA_eval p]
    rw [heq]
    exact coordNablaReg (I := I) S x₀ t a i j
  -- the raw moving-frame formula
  have hraw := Tensor0SBundle.nabla0SFun_eval_coordFrame_moving_raw
    (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
    (s := 3) cov Dsec V nablaA x₀ hpair hV hVmodel hcoord
  -- Step 1: rewrite the LHS via totalNabla0SFun_apply_section
  have hLHS :
      nabla2RicField (I := I) S t x₀
          (DifferentialGeometry.Integral.Connection.vec4 (I := I)
            (frame d x₀) (frame a x₀) (frame i x₀) (frame j x₀)) =
        nabla0SFun (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
          3 cov Dsec nablaA x₀ (fun q : Fin 3 => V q x₀) := by
    rw [hVslots]
    have hcons :
        DifferentialGeometry.Integral.Connection.vec4 (I := I)
            (frame d x₀) (frame a x₀) (frame i x₀) (frame j x₀) =
          Fin.cons (Dsec x₀)
            (DifferentialGeometry.Integral.Connection.vec3 (I := I)
              (frame a x₀) (frame i x₀) (frame j x₀)) := by
      rw [hDsec]
      rw [DifferentialGeometry.Integral.Connection.metricTrace_finCons_vec3_eq_vec4]
    rw [nabla2RicField, ← hnablaA_def, hcons]
    exact totalNabla0SFun_apply_section
      (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      3 cov Dsec nablaA x₀
      (DifferentialGeometry.Integral.Connection.vec3 (I := I)
        (frame a x₀) (frame i x₀) (frame j x₀))
  -- Step 2: rewrite coordNab2Ric as ricciSecondCovDerivCompInFrame
  rw [coordNab2At (I := I) S x₀ t d a i j]
  rw [hLHS, hraw]
  -- the extDeriv terms agree
  have hpair_fun :
      (fun p : M => nablaA p (fun q : Fin 3 => V q p)) =
        fun p : M => nablaRicComp (I := I) S frame t p a i j := by
    funext p
    have hVp : (fun q : Fin 3 => V q p) =
        DifferentialGeometry.Integral.Connection.vec3 (I := I)
          (frame a p) (frame i p) (frame j p) := by
      funext q
      fin_cases q <;> simp [V, slot, DifferentialGeometry.Integral.Connection.vec3]
    rw [hVp, hnablaA_eval p]
  -- the correction sum equals the three christoffel terms
  have hcorr :
      (∑ q : Fin 3,
          nablaA x₀
            (Function.update (fun r : Fin 3 => V r x₀) q
              ((cov (V q) x₀) (Dsec x₀)))) =
        (∑ p : CoordinateIdx (𝕜 := Real) E,
          christoffelSymbolInFrame cov frame
              (coordinateFrameAt_isLocalFrame_one (I := I) x₀) x₀ d a p *
            nablaRicComp (I := I) S frame t x₀ p i j) +
        (∑ p : CoordinateIdx (𝕜 := Real) E,
          christoffelSymbolInFrame cov frame
              (coordinateFrameAt_isLocalFrame_one (I := I) x₀) x₀ d i p *
            nablaRicComp (I := I) S frame t x₀ a p j) +
        (∑ p : CoordinateIdx (𝕜 := Real) E,
          christoffelSymbolInFrame cov frame
              (coordinateFrameAt_isLocalFrame_one (I := I) x₀) x₀ d j p *
            nablaRicComp (I := I) S frame t x₀ a i p) := by
    let hcf := coordinateFrameAt_isLocalFrame_one (I := I) x₀
    -- single-slot update lemma: plugging frame p into slot q gives a nablaRicComp
    have hupd : ∀ (q : Fin 3) (p : CoordinateIdx (𝕜 := Real) E),
        nablaA x₀
            (Function.update (fun r : Fin 3 => V r x₀) q (frame p x₀)) =
          nablaRicComp (I := I) S frame t x₀
            (if q = 0 then p else a)
            (if q = 1 then p else i)
            (if q = 2 then p else j) := by
      intro q p
      have hupd_vec :
          Function.update (fun r : Fin 3 => V r x₀) q (frame p x₀) =
            DifferentialGeometry.Integral.Connection.vec3 (I := I)
              (frame (if q = 0 then p else a) x₀)
              (frame (if q = 1 then p else i) x₀)
              (frame (if q = 2 then p else j) x₀) := by
        funext r
        fin_cases q <;> fin_cases r <;>
          simp [V, slot, Function.update, DifferentialGeometry.Integral.Connection.vec3]
      rw [hupd_vec]
      rfl
    -- expand each covariant derivative via Christoffel symbols
    have hchris : ∀ q : Fin 3,
        (cov (V q) x₀) (Dsec x₀) =
          ∑ p : CoordinateIdx (𝕜 := Real) E,
            christoffelSymbolInFrame cov frame hcf x₀ d (slot q) p •
              frame p x₀ := by
      intro q
      rw [hVq q, hDsec]
      exact covariantDerivative_eq_sum_christoffel
        (I := I) cov frame hcf (coordinateFrameAt_mem (I := I) x₀) d (slot q)
    have hterm : ∀ q : Fin 3,
        nablaA x₀
            (Function.update (fun r : Fin 3 => V r x₀) q
              ((cov (V q) x₀) (Dsec x₀))) =
          ∑ p : CoordinateIdx (𝕜 := Real) E,
            christoffelSymbolInFrame cov frame hcf x₀ d (slot q) p *
              nablaRicComp (I := I) S frame t x₀
                (if q = 0 then p else a)
                (if q = 1 then p else i)
                (if q = 2 then p else j) := by
      intro q
      rw [hchris q]
      rw [show
        (nablaA x₀)
            (Function.update (fun r : Fin 3 => V r x₀) q
              (∑ p : CoordinateIdx (𝕜 := Real) E,
                christoffelSymbolInFrame cov frame hcf x₀ d (slot q) p • frame p x₀)) =
          (nablaA x₀).toMultilinearMap
            (Function.update (fun r : Fin 3 => V r x₀) q
              (∑ p : CoordinateIdx (𝕜 := Real) E,
                christoffelSymbolInFrame cov frame hcf x₀ d (slot q) p • frame p x₀)) from rfl]
      rw [MultilinearMap.map_update_sum]
      refine Finset.sum_congr rfl fun p _ => ?_
      rw [MultilinearMap.map_update_smul]
      rw [show
        (nablaA x₀).toMultilinearMap
            (Function.update (fun r : Fin 3 => V r x₀) q (frame p x₀)) =
          (nablaA x₀)
            (Function.update (fun r : Fin 3 => V r x₀) q (frame p x₀)) from rfl]
      rw [hupd q p]
      rfl
    rw [Fin.sum_univ_three]
    rw [hterm 0, hterm 1, hterm 2]
    simp only [slot, Fin.isValue, if_true, reduceIte,
      show ((0 : Fin 3) = 1) = False by simp,
      show ((0 : Fin 3) = 2) = False by simp,
      show ((1 : Fin 3) = 0) = False by simp,
      show ((1 : Fin 3) = 2) = False by simp,
      show ((2 : Fin 3) = 0) = False by simp,
      show ((2 : Fin 3) = 1) = False by simp]
  rw [hpair_fun, hcorr, hDsec]
  -- now match the explicit ricciSecondCovDerivCompInFrame formula
  unfold DifferentialGeometry.PDE.RicciFlow.ricciSecondCovDerivCompInFrame
  ring

/-- The scalar-curvature diffusion bridge: the canonical coordinate rough
Laplacian of Ricci, contracted with the inverse metric, realizes `Δ R` at the
coordinate center. -/
theorem scalarLaplacianTraceInFrame_coord_eq_laplacianAt
    {D : DifferentialGeometry.Integral.Connection.RealTimeInterval}
    (S : SolutionOn (I := I) (M := M) D)
    (hS : IsSolutionOn (I := I) S)
    (x₀ : M)
    (t : DifferentialGeometry.Integral.Connection.RealTimeInterval.RegularTime D) :
    scalarLaplacianTraceInFrame (M := M) (coordInv (I := I) S x₀)
        (coordRoughRic (I := I) S x₀ (coordNab2Ric (I := I) S x₀)) (t : Real) x₀ =
      DifferentialGeometry.Integral.Connection.laplacianAt (I := I) (flowG (I := I) S)
        (t : Real) (S.scalar (t : Real)) x₀ := by
  classical
  set cov := S.family.connection (t : Real) with hcov_def
  set g := S.family.metric (t : Real) with hg_def
  set frame := coordinateFrameAt (I := I) x₀ with hframe_def
  set basis := coordinateFrameAt_toBasis (I := I) x₀ with hbasis_def
  set gInv : CoordinateIdx (𝕜 := Real) E -> CoordinateIdx (𝕜 := Real) E -> Real :=
    fun a b => coordInv (I := I) S x₀ (t : Real) x₀ a b with hgInv_def
  have hcov : CovariantDerivative.ContMDiffCovariantDerivativeLocally cov (∞ : WithTop ℕ∞) :=
    connSmoothInf (I := I) S (t : Real)
  have hcov1 : CovariantDerivative.ContMDiffCovariantDerivativeLocally cov (1 : WithTop ℕ∞) :=
    connSmoothOfSol (I := I) S hS (t : Real) (D.regular_subset t.2)
  have hmc : DifferentialGeometry.Integral.Connection.IsMetricCompatible_gen (I := I) cov g :=
    isMetricCompatibleSol (I := I) S (t : Real)
  have hinv :
      Tensor0SBundle.MetricInverseInBasis_gen (I := I) (M := M) g x₀ basis gInv := by
    simpa [hg_def, hbasis_def, hgInv_def] using coordInvReal (I := I) S x₀ (t : Real)
  -- the scalar curvature is the metric trace of the bundled Ricci tensor
  have hscalar_eq :
      S.scalar (t : Real) = fun y => metricTracePair0SAt (I := I) g (S.ricci (t : Real) y) := by
    funext y
    rw [SolutionOn.scalar_eq_metricTrace, hg_def]
    congr 1
  -- smoothness of the scalar
  have hf : ContMDiff I 𝓘(Real, Real) (∞ : WithTop ℕ∞) (S.scalar (t : Real)) := by
    rw [hscalar_eq]
    exact trace02_smooth (I := I) g (S.ricci (t : Real))
  -- canonical first/second covariant derivatives of Ricci
  set nablaA := nablaRicField (I := I) S (t : Real) with hnablaA_def
  -- the laplacian is the metric trace of the canonical Hessian of the scalar
  have hLapTrace :
      DifferentialGeometry.Integral.Connection.laplacianAt (I := I) (flowG (I := I) S)
          (t : Real) (S.scalar (t : Real)) x₀ =
        scalarLapTraceAt (I := I) g (hessianSec (I := I) cov hcov (S.scalar (t : Real)) hf x₀) := by
    have hreal := scalarLap_smooth (I := I) cov hcov g hmc (S.scalar (t : Real)) hf
      (x := x₀)
    have := DifferentialGeometry.Integral.Connection.ScalarLaplacianRealizesTraceAt.eq_trace
      (I := I) cov g (S.scalar (t : Real))
      (hessianSec (I := I) cov hcov (S.scalar (t : Real)) hf x₀) hreal
    simpa [DifferentialGeometry.Integral.Connection.laplacianAt, flowG, hcov_def, hg_def]
      using this
  -- the canonical Hessian of the scalar equals the canonical Hessian of the
  -- trace of Ricci (same function, proof-irrelevant)
  have hHess :
      hessianSec (I := I) cov hcov (S.scalar (t : Real)) hf =
        hessianSec (I := I) cov hcov
          (fun y => metricTracePair0SAt (I := I) g (S.ricci (t : Real) y))
          (trace02_smooth (I := I) g (S.ricci (t : Real))) := by
    congr 1
  -- abbreviation for the abstract second covariant derivative tensor
  have hnab2 := nabla2Trace02 (I := I) (M := M) cov hcov hcov1 g hmc
    (S.ricci (t : Real)) (Idx := CoordinateIdx (𝕜 := Real) E) (x := x₀)
    basis gInv hinv
  -- Step A: rewrite RHS = ∑ᵢⱼ gⁱʲ (Hess scalar)(vec2 eᵢ eⱼ)
  rw [hLapTrace, hHess, scalarLapTraceAt]
  rw [metricTracePair0SAt_eq_sum_basis (I := I) g basis gInv hinv]
  -- Step B: rewrite each Hessian component via nabla2Trace02
  have hRHS_comp : ∀ p q : CoordinateIdx (𝕜 := Real) E,
      hessianSec (I := I) cov hcov
          (fun y => metricTracePair0SAt (I := I) g (S.ricci (t : Real) y))
          (trace02_smooth (I := I) g (S.ricci (t : Real))) x₀
            (DifferentialGeometry.Integral.Connection.vec2 (I := I)
              (basis p) (basis q)) =
        ∑ a : CoordinateIdx (𝕜 := Real) E, ∑ b : CoordinateIdx (𝕜 := Real) E,
          gInv a b *
            nabla2RicField (I := I) S (t : Real) x₀
              (DifferentialGeometry.Integral.Connection.vec4 (I := I)
                (basis p) (basis q) (basis a) (basis b)) := by
    intro p q
    exact hnab2 (basis p) (basis q)
  -- Step C: rewrite LHS as a double sum over coordNab2Ric via coordNab2Can / crux
  have hLHS_expand :
      scalarLaplacianTraceInFrame (M := M) (coordInv (I := I) S x₀)
          (coordRoughRic (I := I) S x₀ (coordNab2Ric (I := I) S x₀)) (t : Real) x₀ =
        ∑ i : CoordinateIdx (𝕜 := Real) E, ∑ j : CoordinateIdx (𝕜 := Real) E,
          gInv i j *
            ∑ a : CoordinateIdx (𝕜 := Real) E, ∑ b : CoordinateIdx (𝕜 := Real) E,
              gInv a b *
                nabla2RicField (I := I) S (t : Real) x₀
                  (DifferentialGeometry.Integral.Connection.vec4 (I := I)
                    (frame a x₀) (frame b x₀) (frame i x₀) (frame j x₀)) := by
    rw [scalarLaplacianTraceInFrame]
    refine Finset.sum_congr rfl fun i _ => ?_
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [coordRoughRic]
    -- goal: coordInv i j * (∑ₐ∑ᵦ coordInv a b * coordNab2Ric a b i j)
    --     = gInv i j * (∑ₐ∑ᵦ gInv a b * nabla2RicField(...))
    congr 1
    refine Finset.sum_congr rfl fun a _ => ?_
    refine Finset.sum_congr rfl fun b _ => ?_
    rw [coordNab2Ric_eq_nabla2RicField (I := I) S x₀ (t : Real) a b i j]
  rw [hLHS_expand]
  -- Step D: rewrite RHS double sum and match via the double-trace sum swap
  have hRHS_expand :
      (∑ i : CoordinateIdx (𝕜 := Real) E, ∑ j : CoordinateIdx (𝕜 := Real) E,
        gInv i j *
          hessianSec (I := I) cov hcov
            (fun y => metricTracePair0SAt (I := I) g (S.ricci (t : Real) y))
            (trace02_smooth (I := I) g (S.ricci (t : Real))) x₀
              (DifferentialGeometry.Integral.Connection.vec2 (I := I)
                (basis i) (basis j))) =
        ∑ i : CoordinateIdx (𝕜 := Real) E, ∑ j : CoordinateIdx (𝕜 := Real) E,
          gInv i j *
            ∑ a : CoordinateIdx (𝕜 := Real) E, ∑ b : CoordinateIdx (𝕜 := Real) E,
              gInv a b *
                nabla2RicField (I := I) S (t : Real) x₀
                  (DifferentialGeometry.Integral.Connection.vec4 (I := I)
                    (basis i) (basis j) (basis a) (basis b)) := by
    refine Finset.sum_congr rfl fun i _ => ?_
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [hRHS_comp i j]
  rw [hRHS_expand]
  -- both sides equal a common 4-fold sum after relabeling (i,j) <-> (a,b)
  simp only [hbasis_def, coordinateFrameAt_toBasis_apply]
  -- Abbreviate the abstract second-derivative component.
  set N : CoordinateIdx (𝕜 := Real) E -> CoordinateIdx (𝕜 := Real) E ->
      CoordinateIdx (𝕜 := Real) E -> CoordinateIdx (𝕜 := Real) E -> Real :=
    fun p q r s =>
      nabla2RicField (I := I) S (t : Real) x₀
        (DifferentialGeometry.Integral.Connection.vec4 (I := I)
          (frame p x₀) (frame q x₀) (frame r x₀) (frame s x₀)) with hN_def
  -- Fully distribute both sides into 4-fold sums.
  have hLHS4 :
      (∑ i, ∑ j, gInv i j * ∑ a, ∑ b, gInv a b * N a b i j) =
        ∑ i, ∑ j, ∑ a, ∑ b, gInv i j * (gInv a b * N a b i j) := by
    refine Finset.sum_congr rfl fun i _ => ?_
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [Finset.mul_sum]
  have hRHS4 :
      (∑ i, ∑ j, gInv i j * ∑ a, ∑ b, gInv a b * N i j a b) =
        ∑ i, ∑ j, ∑ a, ∑ b, gInv i j * (gInv a b * N i j a b) := by
    refine Finset.sum_congr rfl fun i _ => ?_
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [Finset.mul_sum]
  rw [hLHS4, hRHS4]
  -- swap the (i,j) and (a,b) index pairs on the LHS
  rw [sum_swap_four_local (Idx := CoordinateIdx (𝕜 := Real) E)
    (fun i j a b => gInv i j * (gInv a b * N a b i j))]
  -- positional relabeling: outer (a,b) ↔ (i,j), commute the metric factors
  refine Finset.sum_congr rfl fun a _ => ?_
  refine Finset.sum_congr rfl fun b _ => ?_
  refine Finset.sum_congr rfl fun i _ => ?_
  refine Finset.sum_congr rfl fun j _ => ?_
  ring

/-- The curvature-trace cancellation `g^{ij} R_ikjl Ric^{kl} = -|Ric|²` at the
center of the coordinate frame, produced pointwise from the canonical `Rm04`
first-trace, output-skew, and first-Bianchi symmetries. -/
private theorem coordScalarRmTrace_center
    {D : DifferentialGeometry.Integral.Connection.RealTimeInterval}
    (S : SolutionOn (I := I) (M := M) D)
    (hS : IsSolutionOn (I := I) S)
    (x₀ : M)
    (t : DifferentialGeometry.Integral.Connection.RealTimeInterval.RegularTime D) :
    (∑ i : CoordinateIdx (𝕜 := Real) E, ∑ j : CoordinateIdx (𝕜 := Real) E,
        coordInv (I := I) S x₀ (t : Real) x₀ i j *
          rmRicciContractionCompInFrame (I := I) S S.base.rm04
            (coordInv (I := I) S x₀) (coordinateFrameAt (I := I) x₀)
            (t : Real) x₀ i j) =
      -ricciNormSqInFrame (I := I) S (coordInv (I := I) S x₀)
        (coordinateFrameAt (I := I) x₀) (t : Real) x₀ := by
  classical
  set basis := coordinateFrameAt_toBasis (I := I) x₀ with hbasis_def
  set gInv : CoordinateIdx (𝕜 := Real) E -> CoordinateIdx (𝕜 := Real) E -> Real :=
    fun a b => coordInv (I := I) S x₀ (t : Real) x₀ a b with hgInv_def
  have hinvAt :
      Tensor0SBundle.MetricInverseInBasis_gen (I := I) (M := M)
        (S.family.metric (t : Real)) x₀ basis gInv := by
    simpa [hbasis_def, hgInv_def] using coordInvReal (I := I) S x₀ (t : Real)
  -- the pointwise curvature symmetry producers, specialized at the center
  have hRm13 :
      ∀ τ : DifferentialGeometry.Integral.Connection.RealTimeInterval.RegularTime D,
        DifferentialGeometry.Integral.Connection.Rm13RealizesConnection (I := I)
          (S.family.connection (τ : Real)) (S.base.rm13 (τ : Real)) := by
    intro τ
    exact rm13OfSol (I := I) S (τ : Real) (D.regular_subset τ.2)
  have hLower :
      ∀ (τ : DifferentialGeometry.Integral.Connection.RealTimeInterval.RegularTime D) (y : M),
        DifferentialGeometry.Integral.Connection.Rm04LowersRm13At (I := I)
          (S.family.metric (τ : Real)) y
          (S.base.rm13 (τ : Real) y) (S.base.rm04 (τ : Real) y) := by
    intro τ y
    have h :=
      DifferentialGeometry.Integral.Connection.rm04LowersRm13At_of_realizes
        (I := I) (S.base.metric (τ : Real)) (S.base.connection (τ : Real))
        (S.base.rm13 (τ : Real)) (S.base.rm04 (τ : Real))
        (metricCurvData (I := I) (M := M) (S.base.metric (τ : Real))).h_rm13
        (metricCurvData (I := I) (M := M) (S.base.metric (τ : Real))).h_rm04
        y
    simpa [SolutionOn.family, SolutionFamily.connection, SolutionFamily.rm13,
      SolutionFamily.rm04, metricCov] using h
  have hTrace :
      DifferentialGeometry.Integral.Connection.RicciRealizesRm04FirstTraceAt (I := I)
        (S.ricci (t : Real) x₀) (S.base.rm04 (t : Real) x₀) gInv basis :=
    DifferentialGeometry.Integral.Connection.ricciFirstTraceAt_of_rm13_section
      (I := I) (S.family.metric (t : Real)) basis gInv hinvAt
      (S.ricci (t : Real)) (S.base.rm13 (t : Real)) (S.base.rm04 (t : Real))
      (ricciTraceOfSol (I := I) S (t : Real) (D.regular_subset t.2))
      (hLower t x₀)
      (Tensor0SBundle.invMetric_symm (I := I) (M := M) (S.family.metric (t : Real))
        x₀ basis gInv hinvAt)
  have hOutput :
      DifferentialGeometry.Integral.Connection.Rm04OutputSkewAt (I := I)
        (S.base.rm04 (t : Real) x₀) :=
    rm04OutputSkew_regular (I := I) S hS S.base.rm13 S.base.rm04 hRm13 hLower t x₀
  have hFirst :
      DifferentialGeometry.Integral.Connection.FirstBianchiAt (I := I)
        (S.base.rm04 (t : Real) x₀) :=
    rm04FirstBianchi_regular (I := I) S hS S.base.rm13 S.base.rm04 hRm13 hLower t x₀
  have hRicAt : ∀ i j : CoordinateIdx (𝕜 := Real) E,
      (S.ricci (t : Real) x₀)
          (DifferentialGeometry.Integral.Connection.vec2 (basis i) (basis j)) =
        (S.ricci (t : Real) x₀)
          (DifferentialGeometry.Integral.Connection.vec2 (basis j) (basis i)) := by
    intro i j
    have hsym :=
      DifferentialGeometry.Integral.Connection.metricRicciSymm (I := I) (M := M)
        (S.family.metric (t : Real)) basis gInv hinvAt i j
    simpa [SolutionOn.ricciAt, SolutionFamily.ricciAt] using hsym
  have hInvSym : ∀ i j : CoordinateIdx (𝕜 := Real) E, gInv i j = gInv j i :=
    Tensor0SBundle.invMetric_symm (I := I) (M := M) (S.family.metric (t : Real))
      x₀ basis gInv hinvAt
  have hmain :=
    DifferentialGeometry.Integral.Connection.metricTrace_rm04RicciContractionAt_eq_neg_inner
      (I := I) basis (S.base.rm04 (t : Real) x₀) gInv (S.ricci (t : Real) x₀)
      hTrace hOutput hFirst hRicAt hInvSym
  simpa [basis, hbasis_def, hgInv_def, coordinateFrameAt_toBasis_apply,
    DifferentialGeometry.Integral.Connection.rm04RicciContractionAt,
    DifferentialGeometry.Integral.Connection.raised02CompAt,
    rmRicciContractionCompInFrame, raisedRicciCompInFrame,
    DifferentialGeometry.Integral.Connection.raisedRicciComponentsInFrame,
    ricciNormSqInFrame, DifferentialGeometry.Integral.Connection.rm04Comp,
    ricciCompInFrame, ricciTwoTensorField,
    SolutionOn.ricciAt, SolutionFamily.ricciAt] using hmain

/-- The product-rule derivative RHS of the coordinate scalar trace identifies
with `Δ R + 2 |Ric|²` at the center of the coordinate frame. -/
private theorem coordScalarTraceDerivRHS_center
    {D : DifferentialGeometry.Integral.Connection.RealTimeInterval}
    (S : SolutionOn (I := I) (M := M) D)
    (hS : IsSolutionOn (I := I) S)
    (x₀ : M)
    (t : DifferentialGeometry.Integral.Connection.RealTimeInterval.RegularTime D) :
    scalarTraceDerivRHSInFrame (I := I) S S.base.rm04 (coordInv (I := I) S x₀)
        (coordinateFrameAt (I := I) x₀)
        (coordRoughRic (I := I) S x₀ (coordNab2Ric (I := I) S x₀)) (t : Real) x₀ =
      scalarLaplacianTraceInFrame (M := M) (coordInv (I := I) S x₀)
          (coordRoughRic (I := I) S x₀ (coordNab2Ric (I := I) S x₀)) (t : Real) x₀ +
        2 * ricciNormSqInFrame (I := I) S (coordInv (I := I) S x₀)
          (coordinateFrameAt (I := I) x₀) (t : Real) x₀ := by
  classical
  set frame := coordinateFrameAt (I := I) x₀ with hframe_def
  set gInv := coordInv (I := I) S x₀ with hgInv_def
  set roughLapRic := coordRoughRic (I := I) S x₀ (coordNab2Ric (I := I) S x₀)
    with hrough_def
  have hbasis : coordinateFrameAt_toBasis (I := I) x₀ =
      (coordinateFrameAt_isLocalFrame_one (I := I) x₀).toBasisAt
        (coordinateFrameAt_mem (I := I) x₀) := by
    ext k
    rw [IsLocalFrameOn.toBasisAt_coe, coordinateFrameAt_toBasis_apply]
  have hinvAt :
      Tensor0SBundle.MetricInverseInBasis_gen (I := I) (M := M)
        (S.family.metric (t : Real)) x₀ (coordinateFrameAt_toBasis (I := I) x₀)
        (fun a b => gInv (t : Real) x₀ a b) := by
    simpa [hgInv_def] using coordInvReal (I := I) S x₀ (t : Real)
  have hInvSym : ∀ i j : CoordinateIdx (𝕜 := Real) E,
      gInv (t : Real) x₀ i j = gInv (t : Real) x₀ j i :=
    Tensor0SBundle.invMetric_symm (I := I) (M := M) (S.family.metric (t : Real))
      x₀ (coordinateFrameAt_toBasis (I := I) x₀)
      (fun a b => gInv (t : Real) x₀ a b) hinvAt
  have hRicSym : ∀ i j : CoordinateIdx (𝕜 := Real) E,
      ricciCompInFrame (I := I) S frame (t : Real) x₀ i j =
        ricciCompInFrame (I := I) S frame (t : Real) x₀ j i := by
    intro i j
    have hsym :=
      DifferentialGeometry.Integral.Connection.metricRicciSymm (I := I) (M := M)
        (S.family.metric (t : Real)) (coordinateFrameAt_toBasis (I := I) x₀)
        (fun a b => gInv (t : Real) x₀ a b) hinvAt i j
    simpa [ricciCompInFrame, SolutionOn.ricciAt, SolutionFamily.ricciAt, frame,
      coordinateFrameAt_toBasis_apply] using hsym
  have hdt :=
    scalarTrace_inverseMetricEvolutionTerm_eq_two_ricciNormSq
      (I := I) S gInv frame (t : Real) x₀
  have hrm := coordScalarRmTrace_center (I := I) S hS x₀ t
  have hquad :=
    scalarTrace_ricciQuadraticTerm_eq_ricciNormSq_at
      (I := I) S gInv frame (t : Real) x₀ hInvSym hRicSym
  unfold scalarTraceDerivRHSInFrame
  rw [show scalarLaplacianTraceInFrame (M := M) gInv roughLapRic (t : Real) x₀ =
        ∑ i : CoordinateIdx (𝕜 := Real) E, ∑ j : CoordinateIdx (𝕜 := Real) E,
          gInv (t : Real) x₀ i j * roughLapRic (t : Real) x₀ i j from rfl]
  have hsplit :
      (∑ i : CoordinateIdx (𝕜 := Real) E, ∑ j : CoordinateIdx (𝕜 := Real) E,
        (inverseMetricEvolutionRHSInFrame (I := I) S gInv frame (t : Real) x₀ i j *
            ricciCompInFrame (I := I) S frame (t : Real) x₀ i j +
          gInv (t : Real) x₀ i j *
            ricciEvolutionRHSInFrame (I := I) S S.base.rm04 gInv frame roughLapRic
              (t : Real) x₀ i j)) =
        (∑ i : CoordinateIdx (𝕜 := Real) E, ∑ j : CoordinateIdx (𝕜 := Real) E,
          inverseMetricEvolutionRHSInFrame (I := I) S gInv frame (t : Real) x₀ i j *
            ricciCompInFrame (I := I) S frame (t : Real) x₀ i j) +
        (∑ i : CoordinateIdx (𝕜 := Real) E, ∑ j : CoordinateIdx (𝕜 := Real) E,
          gInv (t : Real) x₀ i j * roughLapRic (t : Real) x₀ i j) -
        2 * (∑ i : CoordinateIdx (𝕜 := Real) E, ∑ j : CoordinateIdx (𝕜 := Real) E,
          gInv (t : Real) x₀ i j *
            rmRicciContractionCompInFrame (I := I) S S.base.rm04 gInv frame
              (t : Real) x₀ i j) -
        2 * (∑ i : CoordinateIdx (𝕜 := Real) E, ∑ j : CoordinateIdx (𝕜 := Real) E,
          gInv (t : Real) x₀ i j *
            ricciQuadraticCompInFrame (I := I) S gInv frame (t : Real) x₀ i j) := by
    simp [ricciEvolutionRHSInFrame, sub_eq_add_neg, mul_add,
      Finset.sum_add_distrib, Finset.sum_neg_distrib, Finset.mul_sum,
      Finset.sum_mul]
    ring_nf
  rw [hsplit, hdt, hrm, hquad]
  ring

/-- The product-rule time derivative of the coordinate scalar trace at the
center of the coordinate frame, with the RHS already identified as
`Δ R + 2 |Ric|²`. -/
private theorem coordScalarTrace_hasDerivWithinAt_center
    {D : DifferentialGeometry.Integral.Connection.RealTimeInterval}
    (S : SolutionOn (I := I) (M := M) D)
    (hS : IsSolutionOn (I := I) S)
    (x₀ : M)
    (t : DifferentialGeometry.Integral.Connection.RealTimeInterval.RegularTime D) :
    HasDerivWithinAt
      (fun s : Real =>
        scalarTraceInFrame (I := I) S (coordInv (I := I) S x₀)
          (coordinateFrameAt (I := I) x₀) s x₀)
      (scalarLaplacianTraceInFrame (M := M) (coordInv (I := I) S x₀)
          (coordRoughRic (I := I) S x₀ (coordNab2Ric (I := I) S x₀)) (t : Real) x₀ +
        2 * ricciNormSqInFrame (I := I) S (coordInv (I := I) S x₀)
          (coordinateFrameAt (I := I) x₀) (t : Real) x₀)
      D.carrier
      (t : Real) := by
  classical
  set frame := coordinateFrameAt (I := I) x₀ with hframe_def
  set gInv := coordInv (I := I) S x₀ with hgInv_def
  have hInvEvol :=
    coordInvEvol (I := I) S hS x₀
  have hRicEvol :=
    fun (τ : DifferentialGeometry.Integral.Connection.RealTimeInterval.RegularTime D)
        (i j : CoordinateIdx (𝕜 := Real) E) =>
      coordRicciEvol (I := I) S hS x₀ τ i j
  -- product rule on the double sum, at the fixed center x₀
  have hbase :
      HasDerivWithinAt
        (fun s : Real =>
          scalarTraceInFrame (I := I) S gInv frame s x₀)
        (scalarTraceDerivRHSInFrame (I := I) S S.base.rm04 gInv frame
          (coordRoughRic (I := I) S x₀ (coordNab2Ric (I := I) S x₀)) (t : Real) x₀)
        D.carrier
        (t : Real) := by
    simpa [scalarTraceInFrame, scalarTraceDerivRHSInFrame, Finset.sum_apply] using
      (HasDerivWithinAt.fun_sum
        (u := (Finset.univ : Finset (CoordinateIdx (𝕜 := Real) E)))
        (A := fun i s =>
          ∑ j : CoordinateIdx (𝕜 := Real) E,
            gInv s x₀ i j * ricciCompInFrame (I := I) S frame s x₀ i j)
        (A' := fun i =>
          ∑ j : CoordinateIdx (𝕜 := Real) E,
            (inverseMetricEvolutionRHSInFrame (I := I) S gInv frame
                  (t : Real) x₀ i j *
                ricciCompInFrame (I := I) S frame (t : Real) x₀ i j +
              gInv (t : Real) x₀ i j *
                ricciEvolutionRHSInFrame
                  (I := I) S S.base.rm04 gInv frame
                  (coordRoughRic (I := I) S x₀ (coordNab2Ric (I := I) S x₀))
                  (t : Real) x₀ i j))
        (s := D.carrier) (x := (t : Real))
        (fun i _hi =>
          by
            simpa [Finset.sum_apply] using
              (HasDerivWithinAt.fun_sum
                (u := (Finset.univ : Finset (CoordinateIdx (𝕜 := Real) E)))
                (A := fun j s =>
                  gInv s x₀ i j * ricciCompInFrame (I := I) S frame s x₀ i j)
                (A' := fun j =>
                  (inverseMetricEvolutionRHSInFrame (I := I) S gInv frame
                        (t : Real) x₀ i j *
                      ricciCompInFrame (I := I) S frame (t : Real) x₀ i j +
                    gInv (t : Real) x₀ i j *
                      ricciEvolutionRHSInFrame
                        (I := I) S S.base.rm04 gInv frame
                        (coordRoughRic (I := I) S x₀ (coordNab2Ric (I := I) S x₀))
                        (t : Real) x₀ i j))
                (s := D.carrier) (x := (t : Real))
                (fun j _hj =>
                  by
                    have hInv :=
                      hInvEvol t x₀ (coordinateFrameAt_mem (I := I) x₀) i j
                    have hRic := hRicEvol t i j
                    exact hInv.mul hRic))))
  refine hbase.congr_deriv ?_
  exact coordScalarTraceDerivRHS_center (I := I) S hS x₀ t

/-- The scalar-curvature evolution `∂_t R = Δ R + 2 |Ric|²`, in the exact field
form of `IsSolutionOn.scalarEvolution`, derived from `hS` (rather than read off
the structure field) by combining the canonical coordinate Ricci/inverse-metric
evolutions, the curvature-trace cancellation, and the scalar-curvature diffusion
bridge `scalarLaplacianTraceInFrame_coord_eq_laplacianAt`. -/
theorem scalarEvolution_of_isSolution
    {D : DifferentialGeometry.Integral.Connection.RealTimeInterval}
    (S : SolutionOn (I := I) (M := M) D)
    (hS : IsSolutionOn (I := I) S) :
    ∀ (G : DifferentialGeometry.Integral.Connection.RealizedMetricFamily (I := I) (M := M) Real),
      (∀ t : DifferentialGeometry.Integral.Connection.RealTimeInterval.RegularTime D,
        G.metric (t : Real) = S.family.metric (t : Real)) ->
      (∀ t : DifferentialGeometry.Integral.Connection.RealTimeInterval.RegularTime D,
        G.connection (t : Real) = S.family.connection (t : Real)) ->
      ∀ (t : DifferentialGeometry.Integral.Connection.RealTimeInterval.RegularTime D) (x : M),
        HasDerivWithinAt
          (fun s : Real => S.scalar s x)
          (DifferentialGeometry.Integral.Connection.laplacianAt (I := I) G (t : Real)
              (S.scalar (t : Real)) x +
            2 * normSq0S (I := I) (S.family.metric (t : Real)) x 2
              (S.ricci (t : Real) x))
          D.carrier
          (t : Real) := by
  classical
  intro G hGm hGc t x
  -- work in the coordinate frame centered at x
  set frame := coordinateFrameAt (I := I) x with hframe_def
  set gInv := coordInv (I := I) S x with hgInv_def
  -- the at-center scalar-trace time derivative, RHS = diffusion + reaction
  have hderiv := coordScalarTrace_hasDerivWithinAt_center (I := I) S hS x t
  -- FUNCTION bridge: scalarTraceInFrame ... s x = S.scalar s x for all s
  have hscalar_eq : ∀ s : Real,
      scalarTraceInFrame (I := I) S gInv frame s x = S.scalar s x := by
    intro s
    rw [scalarTraceInFrame_eq_metricTracePair (I := I) S gInv frame
      (coordinateFrameAt_isLocalFrame_one (I := I) x) (coordInvLocal (I := I) S x) s
      (coordinateFrameAt_mem (I := I) x)]
    rw [SolutionOn.scalar_eq_metricTrace]
    rfl
  -- DIFFUSION bridge: the coordinate rough Laplacian trace realizes Δ R
  have hdiff :=
    scalarLaplacianTraceInFrame_coord_eq_laplacianAt (I := I) S hS x t
  -- REACTION bridge: the coordinate Ricci norm is |Ric|²
  have hreact :=
    ricciNormSqInFrame_eq_normSq0S (I := I) S gInv frame
      (coordinateFrameAt_isLocalFrame_one (I := I) x) (coordInvLocal (I := I) S x)
      (t : Real) (coordinateFrameAt_mem (I := I) x)
  -- G-congruence: laplacianAt G = laplacianAt (flowG S) at regular time t
  have hGcong :
      DifferentialGeometry.Integral.Connection.laplacianAt (I := I) G (t : Real)
          (S.scalar (t : Real)) x =
        DifferentialGeometry.Integral.Connection.laplacianAt (I := I) (flowG (I := I) S)
          (t : Real) (S.scalar (t : Real)) x := by
    simp only [DifferentialGeometry.Integral.Connection.laplacianAt, hGm t, hGc t,
      flowG, SolutionOn.family_metric, SolutionOn.family_connection]
  -- rewrite the derivand function and the RHS into the target form
  have hfun :
      (fun s : Real => scalarTraceInFrame (I := I) S gInv frame s x) =
        fun s : Real => S.scalar s x := by
    funext s
    exact hscalar_eq s
  rw [hfun, hdiff, hreact] at hderiv
  rw [hGcong]
  exact hderiv

end DifferentialGeometry.PDE.RicciFlow
