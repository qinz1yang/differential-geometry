import DifferentialGeometry.Tensor.RSTensor.FiberMetric.Tensor0SMetricDeriv
import DifferentialGeometry.Geometry.Operator.RoughLaplacian

set_option autoImplicit false
set_option linter.style.longLine false
set_option linter.unusedSectionVars false
set_option linter.unusedFintypeInType false
set_option linter.unusedDecidableInType false

/-!
# The general Bochner Laplacian split of a covariant-tensor norm

This file proves the **rank-uniform, intrinsic** Bochner Laplacian split of the
squared fibre norm `normSq0S g x s T` of a `(0,s)` tensor — the spatial twin of
the general moving-metric time derivative
`Tensor0SBundle.hasDerivWithinAt_normSq0S`
(`Tensor/RSTensor/FiberMetric/Tensor0SMetricDeriv.lean`).  Together the two retire
the two standing inputs of the Bernstein–Bando–Shi norm-square machinery: the time
derivative half is `hasDerivWithinAt_compNormSqMulti`
(`Evolution/MultiNormHeat.lean`), and the Laplacian half is
`MultiNormLaplacianSplit` (`Evolution/MultiNormHeat.lean:137`), currently always a
hypothesis.

## The split

In coordinates, the squared norm equals the `gInv`-raised contraction
`coordContract gInv (comps T) (comps T)` (`normSq0S_eq_coord`).  The classical
Bochner computation `Δ⟨T,T⟩ = g^{ab}∇_a∇_b⟨T,T⟩` proceeds by the covariant
inner-product Leibniz `∇_b⟨T,T⟩ = 2⟨∇_b T, T⟩` (metric compatibility), then a
second covariant differentiation `∇_a(2⟨∇_b T,T⟩) = 2⟨∇_a∇_b T,T⟩ + 2⟨∇_b T,∇_a T⟩`,
then tracing `g^{ab}`:

`Δ|T|² = 2⟨ΔT,T⟩ + 2|∇T|²`,

where `Δ = g^{ab}∇_a∇_b` is the connection/rough Laplacian and `∇T` is the total
covariant derivative (rank `s+1`).

The *geometric* content — that `∇_b⟨T,T⟩ = 2⟨∇_b T,T⟩` and that the second
covariant derivative obeys the product rule — is the **pointwise Hessian product
rule of the norm**, supplied here as a hypothesis at exactly the same status as
`MultiNormLaplacianSplit` itself (and exactly as the `(0,2)` producer
`du_norm02`/`freeze02_deriv` supply it for `s = 2` in
`Geometry/Curvature/Bochner/BochnerTensor.lean`).  What this file proves is the
**rank-uniform trace algebra** turning that pointwise rule, contracted with the
inverse metric, into the intrinsic split with the rough Laplacian `roughLap0SAt`
and the norm `normSq0S (s+1)` of `∇T`.

Everything below is intrinsic and rank-uniform: the contraction algebra carries no
curvature or flow content beyond the metric inverse and the supplied product rule.
`#print axioms` for every public theorem is `[propext, Classical.choice, Quot.sound]`.

## Why a hypothesis and not `nabla_metric_zero`

A fully self-contained derivation would prove the pointwise Hessian product rule
from `nabla_metric_zero` and the general-rank covariant inner-product Leibniz
`∇⟨T,S⟩ = ⟨∇T,S⟩ + ⟨T,∇S⟩`.  The latter is grep-confirmed **absent** at general
rank (only the `(0,2)` `inner0S_two_nabla` /
`inner0S_two_metricCompatible_extDerivFun` exist, in
`Tensor/RSTensor/Tensor0SRiemannian/Smooth.lean`), and building it intrinsically
runs into the bundled inverse-metric parallelism `∇gInv = 0` wall documented in
`Geometry/Flow/RicciFlow/Evolution/IteratedNablaRmTower.md` (the inverse metric is
a component function, not a bundled `(2,0)` tensor).  So the pointwise rule is the
honest input frontier; the `(0,2)` producer discharges it for `s = 2`.
-/

namespace Tensor0SBundle

noncomputable section

open scoped Manifold ContDiff BigOperators

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace Real E]
  [FiniteDimensional Real E]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners Real E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

/-! ## Pure coordinate trace algebra of component arrays

We work first at the assumption-free level of real component arrays
`(Fin s → Idx) → Real`, so the whole trace calculation carries no geometric
content.  `coordContract gInv cA cB` (from `Tensor0SMetricDeriv.lean`) is the
`gInv`-raised contraction `Σ_{I0,J0} (∏_a gInv (I0 a)(J0 a)) · cA I0 · cB J0`.  The
two facts proved here are the rank-uniform generalisations of the `(0,2)`
`sum_trace_tensor02_rough` / `sum_trace_tensor02_nabla` of `BochnerTensor.lean`. -/

section Coord

variable {Idx : Type*} [Fintype Idx]

/-- Freeze the first two slots of a rank-`s+2` component array against `(i, j)`,
leaving a rank-`s` component array. -/
def freezeFirst2Comp {s : Nat}
    (H2 : (Fin (s + 2) -> Idx) -> Real) (i j : Idx) :
    (Fin s -> Idx) -> Real :=
  fun J0 => H2 (Fin.cons i (Fin.cons j J0))

/-- Freeze the first slot of a rank-`s+1` component array against `i`, leaving a
rank-`s` component array. -/
def freezeFirst1Comp {s : Nat}
    (H1 : (Fin (s + 1) -> Idx) -> Real) (i : Idx) :
    (Fin s -> Idx) -> Real :=
  fun J0 => H1 (Fin.cons i J0)

/-- The metric trace of the first two slots of a rank-`s+2` component array,
`(tr_g H2) J0 = Σ_{i,j} gInv i j · H2 (i :: j :: J0)`.  This is the component form
of the rough Laplacian `Δ = g^{ab}∇_a∇_b` applied to a second covariant
derivative. -/
def traceFirst2Comp {s : Nat}
    (gInv : Idx -> Idx -> Real)
    (H2 : (Fin (s + 2) -> Idx) -> Real) :
    (Fin s -> Idx) -> Real :=
  fun J0 => ∑ i : Idx, ∑ j : Idx, gInv i j * H2 (Fin.cons i (Fin.cons j J0))

/-- Splitting a finite sum over rank-`s+1` index tuples on the leading slot:
`Σ_{K : Fin (s+1) → Idx} F K = Σ_i Σ_{K' : Fin s → Idx} F (i :: K')`. -/
theorem sum_fin_cons {s : Nat} {A : Type*} [AddCommMonoid A]
    (F : (Fin (s + 1) -> Idx) -> A) :
    (∑ K : Fin (s + 1) -> Idx, F K) =
      ∑ i : Idx, ∑ K' : Fin s -> Idx, F (Fin.cons i K') := by
  classical
  rw [Fintype.sum_equiv (Fin.consEquiv (fun _ : Fin (s + 1) => Idx)).symm
      F (fun p : Idx × (Fin s -> Idx) => F (Fin.cons p.1 p.2))]
  · rw [Fintype.sum_prod_type]
  · intro K
    congr 1
    exact (Fin.cons_self_tail K).symm

/-- Swap the two leading `Idx` sums past the two trailing tuple sums in a 4-fold
finite sum:
`Σ_i Σ_j Σ_p Σ_q F = Σ_p Σ_q Σ_i Σ_j F`. -/
theorem sum_comm_blocks {s : Nat} {A : Type*} [AddCommMonoid A]
    (F : Idx -> Idx -> (Fin s -> Idx) -> (Fin s -> Idx) -> A) :
    (∑ i : Idx, ∑ j : Idx, ∑ p : Fin s -> Idx, ∑ q : Fin s -> Idx, F i j p q) =
      ∑ p : Fin s -> Idx, ∑ q : Fin s -> Idx, ∑ i : Idx, ∑ j : Idx, F i j p q := by
  classical
  rw [show
      (∑ i : Idx, ∑ j : Idx, ∑ p : Fin s -> Idx, ∑ q : Fin s -> Idx, F i j p q) =
        ∑ ij : Idx × Idx, ∑ pq : (Fin s -> Idx) × (Fin s -> Idx),
          F ij.1 ij.2 pq.1 pq.2 from by
    rw [Fintype.sum_prod_type]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    rw [Fintype.sum_prod_type]]
  rw [Finset.sum_comm]
  rw [Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun p _ => Finset.sum_congr rfl fun q _ => ?_
  rw [Fintype.sum_prod_type]

/-- Splitting a double finite sum over rank-`s+1` index tuples on both leading
slots:
`Σ_K Σ_L F K L = Σ_i Σ_{K'} Σ_j Σ_{L'} F (i :: K') (j :: L')`. -/
theorem sum_fin_cons2 {s : Nat} {A : Type*} [AddCommMonoid A]
    (F : (Fin (s + 1) -> Idx) -> (Fin (s + 1) -> Idx) -> A) :
    (∑ K : Fin (s + 1) -> Idx, ∑ L : Fin (s + 1) -> Idx, F K L) =
      ∑ i : Idx, ∑ K' : Fin s -> Idx, ∑ j : Idx, ∑ L' : Fin s -> Idx,
        F (Fin.cons i K') (Fin.cons j L') := by
  rw [sum_fin_cons (fun K : Fin (s + 1) -> Idx =>
    ∑ L : Fin (s + 1) -> Idx, F K L)]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun K' _ => ?_
  rw [sum_fin_cons (fun L : Fin (s + 1) -> Idx => F (Fin.cons i K') L)]

/-- **The rough trace identity.**  Tracing `g^{ij}` over the contraction of the
`(i,j)`-frozen second derivative with `T` rebuilds the contraction of the metric
trace (the rough Laplacian) with `T`:

`Σ_{i,j} gInv i j · coordContract gInv (freezeFirst2Comp H2 i j) cT
  = coordContract gInv (traceFirst2Comp gInv H2) cT`.

Pure finite-sum algebra; rank-uniform. -/
theorem sum_trace_coordContract_rough {s : Nat}
    (gInv : Idx -> Idx -> Real)
    (H2 : (Fin (s + 2) -> Idx) -> Real)
    (cT : (Fin s -> Idx) -> Real) :
    (∑ i : Idx, ∑ j : Idx,
        gInv i j *
          coordContract (s := s) gInv (freezeFirst2Comp H2 i j) cT) =
      coordContract (s := s) gInv (traceFirst2Comp gInv H2) cT := by
  classical
  unfold coordContract traceFirst2Comp freezeFirst2Comp
  -- Common normal form: `Σ_i Σ_j Σ_{I0} Σ_{J0} gInv i j · (∏gInv) · H2(i::j::I0) · cT J0`.
  trans (∑ i : Idx, ∑ j : Idx, ∑ I0 : Fin s -> Idx, ∑ J0 : Fin s -> Idx,
      gInv i j *
        ((∏ a : Fin s, gInv (I0 a) (J0 a)) *
            H2 (Fin.cons i (Fin.cons j I0)) * cT J0))
  · -- LHS: pull `gInv i j` into the `(I0, J0)` double sum.
    simp_rw [Finset.mul_sum]
  · -- RHS: reorder to `Σ_{I0} Σ_{J0} Σ_i Σ_j`, then distribute.
    rw [sum_comm_blocks (fun i j I0 J0 =>
      gInv i j *
        ((∏ a : Fin s, gInv (I0 a) (J0 a)) *
            H2 (Fin.cons i (Fin.cons j I0)) * cT J0))]
    refine Finset.sum_congr rfl fun I0 _ => Finset.sum_congr rfl fun J0 _ => ?_
    simp_rw [Finset.mul_sum, Finset.sum_mul]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    ring

/-- **The covariant-derivative norm trace identity.**  Tracing `g^{ij}` over the
contraction of the `i`-frozen and `j`-frozen first derivative rebuilds the
rank-`s+1` contraction `coordContract gInv H1 H1 = |∇T|²`:

`Σ_{i,j} gInv i j · coordContract gInv (freezeFirst1Comp H1 i) (freezeFirst1Comp H1 j)
  = coordContract gInv H1 H1`.

Pure finite-sum algebra; the rank-`s+1` contraction is split on its leading slot.
Rank-uniform. -/
theorem sum_trace_coordContract_nabla {s : Nat}
    (gInv : Idx -> Idx -> Real)
    (H1 : (Fin (s + 1) -> Idx) -> Real) :
    (∑ i : Idx, ∑ j : Idx,
        gInv i j *
          coordContract (s := s) gInv
            (freezeFirst1Comp H1 i) (freezeFirst1Comp H1 j)) =
      coordContract (s := s + 1) gInv H1 H1 := by
  classical
  -- Work from the RHS: split both leading slots of the rank-`s+1` double sum,
  -- peel the `gInv i j` factor, then reorder to match the LHS.
  symm
  unfold coordContract freezeFirst1Comp
  rw [sum_fin_cons2 (fun K L : Fin (s + 1) -> Idx =>
    (∏ a : Fin (s + 1), gInv (K a) (L a)) * H1 K * H1 L)]
  -- Peel the leading `gInv i j` from each `(s+1)`-fold product.
  simp_rw [Fin.prod_univ_succ, Fin.cons_zero, Fin.cons_succ]
  -- Reorder `Σ_i Σ_{K'} Σ_j Σ_{L'} → Σ_i Σ_j Σ_{K'} Σ_{L'}` and pull `gInv i j` out.
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun K' _ => ?_
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun L' _ => ?_
  ring

end Coord

/-! ## The intrinsic rank-uniform Bochner split

We restate the trace algebra through the intrinsic fibre objects: `inner0S`,
`normSq0S`, and the basis rough Laplacian `roughLap0SAt`.  Working at a fixed
point `x` in a tangent basis with `gInv` a genuine inverse (`MetricInverseInBasis`),
the contractions are the intrinsic inner products by `inner0S_eq_coord`. -/

section Intrinsic

variable {Idx : Type*} [Fintype Idx] [DecidableEq Idx]

open DifferentialGeometry.Integral.Connection

/-- The basis-frozen first covariant derivative as a `(0,s)` tensor, evaluated on a
basis tuple, has components `freezeFirst1Comp` of the components of `∇T`. -/
private theorem tensor0S_curry_comp {s : Nat} {x : M}
    (nablaT : Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      (s + 1) x)
    (basis : Module.Basis Idx Real (TangentSpace I x))
    (i : Idx) (J0 : Fin s -> Idx) :
    tensor0SComponent (I := I)
        (tensor0S_curry (I := I) (𝕜 := Real) (M := M) s x nablaT (basis i))
        (fun k => basis k) J0 =
      freezeFirst1Comp (s := s)
        (fun K0 => tensor0SComponent (I := I) nablaT (fun k => basis k) K0) i J0 := by
  unfold tensor0SComponent freezeFirst1Comp
  rw [tensor0S_curry_apply_cons (I := I) s nablaT (basis i) (fun a => basis (J0 a))]
  congr 1
  funext a
  refine Fin.cases ?_ (fun b => ?_) a
  · rfl
  · rfl

/-- The basis-frozen second covariant derivative as a `(0,s)` tensor (freezing the
two derivative slots against `(i,j)`), evaluated on a basis tuple, has components
`freezeFirst2Comp` of the components of `∇²T`. -/
private theorem freezeFirstTwoArgs0S_comp {s : Nat} {x : M}
    (nabla2T : Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      (s + 2) x)
    (basis : Module.Basis Idx Real (TangentSpace I x))
    (i j : Idx) (J0 : Fin s -> Idx) :
    tensor0SComponent (I := I)
        (freezeFirstTwoArgs0S (I := I) nabla2T (basis i) (basis j))
        (fun k => basis k) J0 =
      freezeFirst2Comp (s := s)
        (fun K0 => tensor0SComponent (I := I) nabla2T (fun k => basis k) K0)
        i j J0 := by
  unfold tensor0SComponent freezeFirst2Comp
  rw [freezeFirstTwoArgs0S_apply (I := I) nabla2T (basis i) (basis j)
    (fun a => basis (J0 a))]
  congr 1
  funext a
  refine Fin.cases ?_ (fun b => ?_) a
  · rfl
  · refine Fin.cases ?_ (fun c => ?_) b
    · rfl
    · rfl

/-- The tensor-valued basis rough Laplacian `(0,s)` tensor of `∇²T`, evaluated on a
basis tuple, has components `traceFirst2Comp` of the components of `∇²T`. -/
private theorem metricTrace0S2TensorInBasis_comp {s : Nat} {x : M}
    (basis : Module.Basis Idx Real (TangentSpace I x))
    (gInv : Idx -> Idx -> Real)
    (nabla2T : Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      (s + 2) x)
    (J0 : Fin s -> Idx) :
    tensor0SComponent (I := I)
        (metricTrace0S2TensorInBasis (I := I) basis gInv nabla2T)
        (fun k => basis k) J0 =
      traceFirst2Comp (s := s) gInv
        (fun K0 => tensor0SComponent (I := I) nabla2T (fun k => basis k) K0) J0 := by
  unfold tensor0SComponent traceFirst2Comp
  rw [metricTrace0S2TensorInBasis_apply (I := I) basis gInv nabla2T
    (fun k => basis (J0 k))]
  unfold metricTrace0S2InBasis
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  congr 1
  beta_reduce
  congr 1
  funext a
  refine Fin.cases ?_ (fun b => ?_) a
  · rfl
  · refine Fin.cases ?_ (fun c => ?_) b
    · rfl
    · rfl

/-- **The pointwise Hessian product rule of a covariant-tensor norm**, in basis
component form.  This is the genuine geometric input of the Bochner split: the
`(0,2)` Hessian of `|T|²` evaluated on `(basis i, basis j)` is

`Hess|T|²(i,j) = 2·(⟨(∇²T)(eᵢ,eⱼ,·), T⟩ + ⟨(∇T)(eᵢ,·), (∇T)(eⱼ,·)⟩)`,

with the contractions written as the coordinate inner product `coordInner0S`.  It
is the rank-uniform analogue of `BochnerTensor.Tensor02NormHessianProductInBasis`,
and is discharged for `s = 2` from metric compatibility by `BochnerTensor.hess_norm02`. -/
def TensorNormHessianProductInBasis {s : Nat} {x : M}
    (basis : Module.Basis Idx Real (TangentSpace I x))
    (gInv : Idx -> Idx -> Real)
    (T : Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) s x)
    (nablaT : Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      (s + 1) x)
    (nabla2T : Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      (s + 2) x)
    (normSecond : Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      2 x) : Prop :=
  ∀ i j : Idx,
    normSecond (vec2 (I := I) (basis i) (basis j)) =
      (2 : Real) *
        (coordInner0S (I := I) (x := x) s gInv
            (freezeFirstTwoArgs0S (I := I) nabla2T (basis i) (basis j)) T basis +
          coordInner0S (I := I) (x := x) s gInv
            (tensor0S_curry (I := I) (𝕜 := Real) (M := M) s x nablaT (basis i))
            (tensor0S_curry (I := I) (𝕜 := Real) (M := M) s x nablaT (basis j))
            basis)

/-- **The general Bochner Laplacian split of a covariant-tensor norm (coordinate
form).**

Let `x : M`, let `basis` be a tangent basis at `x`, let `gInv` be component data
used for the metric trace, and let `T : (0,s)`, `nablaT : (0,s+1)`,
`nabla2T : (0,s+2)`, `normSecond : (0,2)` be tensors at `x`.  Suppose the pointwise
Hessian product rule of the norm holds (`hprod`).  Then the metric trace
`tr_g normSecond` (the scalar rough Laplacian of `|T|²`) splits as

`tr_g normSecond = 2 · coordInner0S s gInv (roughLap0SAt-tensor of ∇²T) T
                     + 2 · coordInner0S (s+1) gInv (∇T) (∇T)`,

i.e. `Δ|T|² = 2⟨ΔT,T⟩ + 2|∇T|²` in coordinates.  Pure trace algebra over the
supplied pointwise rule; rank-uniform and valid for **any** `gInv` (no inverse
hypothesis — the metric inverse enters only in the intrinsic restatement below). -/
theorem tensorNormBochnerSplit_coord {s : Nat} {x : M}
    (basis : Module.Basis Idx Real (TangentSpace I x))
    (gInv : Idx -> Idx -> Real)
    (T : Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) s x)
    (nablaT : Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      (s + 1) x)
    (nabla2T : Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      (s + 2) x)
    (normSecond : Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      2 x)
    (hprod : TensorNormHessianProductInBasis (I := I) basis gInv T nablaT nabla2T
      normSecond) :
    metricTrace0S2InBasis (I := I) basis gInv normSecond Fin.elim0 =
      2 * coordInner0S (I := I) (x := x) s gInv
            (metricTrace0S2TensorInBasis (I := I) basis gInv nabla2T) T basis +
        2 * coordInner0S (I := I) (x := x) (s + 1) gInv nablaT nablaT basis := by
  classical
  -- Component arrays of the three tensors in the basis.
  set cT : (Fin s -> Idx) -> Real :=
    fun J0 => tensor0SComponent (I := I) T (fun k => basis k) J0 with hcT
  set cH1 : (Fin (s + 1) -> Idx) -> Real :=
    fun J0 => tensor0SComponent (I := I) nablaT (fun k => basis k) J0 with hcH1
  set cH2 : (Fin (s + 2) -> Idx) -> Real :=
    fun J0 => tensor0SComponent (I := I) nabla2T (fun k => basis k) J0 with hcH2
  -- Step 1: expand the metric trace of `normSecond` via the pointwise product rule.
  have hexpand :
      metricTrace0S2InBasis (I := I) basis gInv normSecond Fin.elim0 =
        ∑ i : Idx, ∑ j : Idx,
          gInv i j *
            ((2 : Real) *
              (coordContract (s := s) gInv (freezeFirst2Comp cH2 i j) cT +
                coordContract (s := s) gInv
                  (freezeFirst1Comp cH1 i)
                  (freezeFirst1Comp cH1 j))) := by
    unfold metricTrace0S2InBasis
    refine Finset.sum_congr rfl fun i _ => ?_
    refine Finset.sum_congr rfl fun j _ => ?_
    congr 1
    -- `normSecond (metricTraceInput (basis i)(basis j) elim0) = normSecond (vec2 …)`.
    have hinput :
        normSecond (metricTraceInput (I := I) (basis i) (basis j) Fin.elim0) =
          normSecond (vec2 (I := I) (basis i) (basis j)) := by
      congr 1
      funext a
      fin_cases a
      · simp [metricTraceInput, vec2,
          DifferentialGeometry.Integral.Connection.vec2]
      · rfl
    rw [hinput, hprod i j]
    -- Identify the two `coordInner0S` with `coordContract` on component arrays.
    have hRough :
        coordInner0S (I := I) (x := x) s gInv
            (freezeFirstTwoArgs0S (I := I) nabla2T (basis i) (basis j)) T basis =
          coordContract (s := s) gInv (freezeFirst2Comp cH2 i j) cT := by
      rw [← coordContract_eq_coordInner0S (I := I) gInv
        (freezeFirstTwoArgs0S (I := I) nabla2T (basis i) (basis j)) T basis]
      refine congrArg (fun f => coordContract (s := s) gInv f cT) ?_
      funext K0
      rw [freezeFirstTwoArgs0S_comp (I := I) nabla2T basis i j K0]
    have hNab :
        coordInner0S (I := I) (x := x) s gInv
            (tensor0S_curry (I := I) (𝕜 := Real) (M := M) s x nablaT (basis i))
            (tensor0S_curry (I := I) (𝕜 := Real) (M := M) s x nablaT (basis j))
            basis =
          coordContract (s := s) gInv
            (freezeFirst1Comp cH1 i) (freezeFirst1Comp cH1 j) := by
      rw [← coordContract_eq_coordInner0S (I := I) gInv
        (tensor0S_curry (I := I) (𝕜 := Real) (M := M) s x nablaT (basis i))
        (tensor0S_curry (I := I) (𝕜 := Real) (M := M) s x nablaT (basis j)) basis]
      refine congrArg₂ (fun f g => coordContract (s := s) gInv f g) ?_ ?_
      · funext K0; rw [tensor0S_curry_comp (I := I) nablaT basis i K0]
      · funext K0; rw [tensor0S_curry_comp (I := I) nablaT basis j K0]
    rw [hRough, hNab]
  -- Step 2: split the trace into the two summed groups and apply the trace lemmas.
  rw [hexpand]
  have hsplit :
      (∑ i : Idx, ∑ j : Idx,
          gInv i j *
            ((2 : Real) *
              (coordContract (s := s) gInv (freezeFirst2Comp cH2 i j) cT +
                coordContract (s := s) gInv
                  (freezeFirst1Comp cH1 i)
                  (freezeFirst1Comp cH1 j)))) =
        2 *
            (∑ i : Idx, ∑ j : Idx,
              gInv i j *
                coordContract (s := s) gInv (freezeFirst2Comp cH2 i j) cT) +
          2 *
            (∑ i : Idx, ∑ j : Idx,
              gInv i j *
                coordContract (s := s) gInv
                  (freezeFirst1Comp cH1 i)
                  (freezeFirst1Comp cH1 j)) := by
    rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun j _ => ?_
    ring
  rw [hsplit]
  -- Step 3: rewrite both traced groups intrinsically.
  rw [sum_trace_coordContract_rough gInv cH2 cT]
  rw [sum_trace_coordContract_nabla gInv cH1]
  -- The rough term: `coordContract gInv (traceFirst2Comp gInv cH2) cT
  --   = coordInner0S s gInv (metricTrace0S2TensorInBasis …) T`.
  have hRL :
      coordContract (s := s) gInv (traceFirst2Comp gInv cH2) cT =
        coordInner0S (I := I) (x := x) s gInv
          (metricTrace0S2TensorInBasis (I := I) basis gInv nabla2T) T basis := by
    rw [← coordContract_eq_coordInner0S (I := I) gInv
      (metricTrace0S2TensorInBasis (I := I) basis gInv nabla2T) T basis]
    refine congrArg (fun f => coordContract (s := s) gInv f cT) ?_
    funext J0
    rw [metricTrace0S2TensorInBasis_comp (I := I) basis gInv nabla2T J0]
  -- The nabla term: `coordContract gInv cH1 cH1 = coordInner0S (s+1) gInv ∇T ∇T`.
  have hNN :
      coordContract (s := s + 1) gInv cH1 cH1 =
        coordInner0S (I := I) (x := x) (s + 1) gInv nablaT nablaT basis := by
    rw [hcH1]
    exact coordContract_eq_coordInner0S (I := I) gInv nablaT nablaT basis
  rw [hRL, hNN]

/-- **The general Bochner Laplacian split of a covariant-tensor norm (intrinsic
form).**

Let `g : SmoothMetric I M`, `x : M`, `basis` a tangent basis at `x` with `gInv` a
genuine inverse (`hinv : MetricInverseInBasis g x basis gInv`), and `T : (0,s)`,
`nablaT : (0,s+1)` (`= ∇T`), `nabla2T : (0,s+2)` (`= ∇²T`), `normSecond : (0,2)`
(`= Hess|T|²`) tensors at `x`.  Suppose the pointwise Hessian product rule of the
norm holds (`hprod`).  Then the metric trace of `normSecond` — the scalar Laplacian
`Δ|T|²` — splits intrinsically as

`Δ|T|² = 2 · ⟨ΔT, T⟩ + 2 · |∇T|²`,

i.e.

`metricTrace0S2InBasis basis gInv normSecond Fin.elim0
  = 2 · inner0S g x s (metricTrace0S2TensorInBasis basis gInv nabla2T) T
    + 2 · normSq0S g x (s+1) nablaT`,

where `metricTrace0S2TensorInBasis basis gInv nabla2T` is the rough Laplacian
`ΔT = g^{ab}∇_a∇_b T`.  This is the rank-uniform intrinsic Bochner split; it
discharges the `MultiNormLaplacianSplit` half of the BBS norm-square machinery from
the pointwise product rule (the `(0,2)` case is `BochnerTensor.second_norm02_mc`). -/
theorem tensorNormBochnerSplit {s : Nat} {x : M}
    (g : SmoothMetric I M)
    (basis : Module.Basis Idx Real (TangentSpace I x))
    (gInv : Idx -> Idx -> Real)
    (hinv : MetricInverseInBasis (I := I) g x basis gInv)
    (T : Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) s x)
    (nablaT : Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      (s + 1) x)
    (nabla2T : Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      (s + 2) x)
    (normSecond : Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      2 x)
    (hprod : TensorNormHessianProductInBasis (I := I) basis gInv T nablaT nabla2T
      normSecond) :
    metricTrace0S2InBasis (I := I) basis gInv normSecond Fin.elim0 =
      2 * inner0S (I := I) g x s
            (metricTrace0S2TensorInBasis (I := I) basis gInv nabla2T) T +
        2 * normSq0S (I := I) g x (s + 1) nablaT := by
  rw [tensorNormBochnerSplit_coord (I := I) basis gInv T nablaT nabla2T normSecond
    hprod]
  rw [← inner0S_eq_coord (I := I) g x s basis gInv hinv
      (metricTrace0S2TensorInBasis (I := I) basis gInv nabla2T) T,
    ← normSq0S_eq_coord (I := I) g x (s + 1) basis gInv hinv nablaT]

end Intrinsic

end

end Tensor0SBundle
