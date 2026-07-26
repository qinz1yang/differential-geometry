import DifferentialGeometry.Geometry.Flow.RicciFlow.Evolution.NablaRiemannCommutator
import DifferentialGeometry.Geometry.Flow.RicciFlow.Evolution.NablaRiemannHeat
import Mathlib.Analysis.InnerProductSpace.PiL2

set_option autoImplicit false
set_option linter.style.longLine false
set_option linter.unusedSectionVars false
set_option linter.unusedFintypeInType false
set_option linter.unusedDecidableInType false

/-!
# The coordinate→orthonormal frame-change adapter for the `k = 1` spatial commutator

`Evolution/NablaRiemannCommutator.lean` proves the spatial Laplacian–covariant
commutator `[Δ, ∇_c] Rm = Rm ∗ ∇Rm` **hardwired to the chart coordinate frame**
`coordinateFrameAt x₀`.  Its orthonormal-trace form `nablaLapComm_orthonormalTrace`
carries a hypothesis `horth : gInv = δ`, but `coordinateFrameAt x₀` is the *chart*
coordinate frame, which is **never** `g`-orthonormal at its centre
(`Geometry/Coordinates/CoordinateFrame.lean`: it does not make Christoffel symbols
vanish, and its `InverseMetricOrthonormalAt` is never discharged).  Consequently
the trace `roughLapNablaRmComp (coordinateFrameAt x₀) δ` is **not** the genuine
rough Laplacian `Δ(∇Rm) = gᵃᵇ ∇ₐ∇ᵦ ∇Rm` (which needs the *true* inverse metric of
the frame), so it cannot feed the producer
(`Evolution/NablaRiemannHeat.lean`, `nablaRm04NormHeatBoundOn_of_components`),
whose reaction `nablaRmReactionInFrame` is consumed in an **orthonormal** frame
(`InverseMetricOrthonormalAt gInv`, `gᵃᵇ = δ`).

This file is the **frame-change adapter** the bound footer (obstruction #4) and the
`IteratedNablaRmTower.md` follow-up (the `T₂` half's "Exact theorem needed next")
flagged.  It does **not** weaken the producer by assuming `coordinateFrameAt` is
orthonormal.  Instead it makes the spatial commutator available in a **genuinely
`g`-orthonormal frame**, where `gᵃᵇ = δ` is the *true* inverse metric (justified by
orthonormality), satisfying the producer's `InverseMetricOrthonormalAt` honestly.

## The mathematical observation that unblocks this

The spatial commutator lemmas of `NablaRiemannCommutator.lean` are derived purely
from the **frame-free** `(0, s)` Ricci identities `rm04_ricciIdentityAt` /
`nablaRm04_ricciIdentityAt` (`Evolution/RmRealizationBridge.lean`), which hold for
*arbitrary* tangent vectors at a point — they have **no** frame dependence.  The
only place `coordinateFrameAt x₀` enters is the *choice* of which tangent vectors
to feed the bundled `∇³Rm = nabla3Rm04Field`; the commutator evaluates the bundled
fields **only at the centre `x₀`** on tuples of vectors `frame · x₀`.  So the entire
commutator chain is frame-generic with **no** new mathematical content, and even
needs only a *basis at `x₀`* (no smoothness, no global frame).

We therefore:

1. re-state the commutator generically over an arbitrary index type `Idx` and
   frame `frame : Idx → (x : M) → TangentSpace I x` (Section `GenericFrame`), proving
   `nablaLapCommF_pointwise` / `_trace` / `_orthonormalTrace` from the frame-free
   Ricci identity exactly as in the coordinate-frame file; and
2. build a **pointwise `g`-orthonormal frame at `x₀`** from the *fibre* metric
   `g x₀ = S.family.metric t` (Section `OrthonormalFrame`), via the chart-locality-free
   `letI … ofCore` construction (the technique of
   `exists_orthonormal_frame_riemannianFiberNormSq` in
   `Analysis/Elliptic/…/RiemannianFiberNormSqRiemannOpVWFactorBound.lean`, replicated
   here directly to avoid that file's spurious `[InnerProductSpace ℝ E]` section
   variable).  No `[InnerProductSpace ℝ E]` on the *model* is needed; the fibre inner
   product comes from `g.toRiemannianMetric.toCore x₀` (`RiemannianMetric.toCore`,
   `Mathlib/Topology/VectorBundle/Riemannian.lean`, needs only a normed model fibre),
   and `stdOrthonormalBasis` supplies the basis.  The frame's inverse metric is
   genuinely `δ`, so `InverseMetricOrthonormalAt` holds **honestly**.

The assembled adapter `nablaLapComm_orthoFrame` (Section `Adapter`) then states the
spatial commutator `Δ(∇Rm) − ∇(ΔRm) = Σ_a reaction a a c m` in this orthonormal
frame, paired with the *genuine* `InverseMetricOrthonormalAt` witness, exactly the
form the producer's `nablaRm04NormHeatBoundOn_of_components` consumes.

## Honesty

* No axiomatized frame-change or orthonormality assumption: the orthonormality is a
  proved consequence of the fibre-metric Gram–Schmidt (`stdOrthonormalBasis` against
  `g.toRiemannianMetric.toCore`), and the commutator is the frame-free Ricci identity.
* The producer is untouched and not weakened; `coordinateFrameAt` is never asserted
  orthonormal.
* `#print axioms` for every public theorem is `[propext, Classical.choice, Quot.sound]`.

What this file does **not** do: it does not prove the quantitative reaction bound
`|reaction| ≤ C(dim)·|Rm|·|∇Rm|` (still gated by the `(1,3)` raising-parallelism of
the `T₁` summand — bound obstruction #1, a separate tensor-layer wall), nor does it
assemble the full `NablaRm04NormHeatEquationOn`.  It removes the *frame-mismatch*
obstruction (#4) so the spatial commutator is finally available in the producer's
orthonormal convention.
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
variable [IsManifold I 1 M] [IsManifold I 2 M]
variable [IsManifold I ((∞ : WithTop ℕ∞) + 1) M]
variable [CompleteSpace E] [SigmaCompactSpace M] [T2Space M]

/-! ## Section `GenericFrame` — the spatial commutator over an arbitrary frame

These mirror `nabla3InnerSlots`, `nabla3FrameTuple`, `nablaLapCommReactionTerm`,
`roughLapNablaRmComp`, `nablaRoughLapRmComp`, `nablaLapComm_pointwise`,
`nablaLapComm_trace`, `nablaLapComm_orthonormalTrace` from
`Evolution/NablaRiemannCommutator.lean`, but with the chart coordinate frame
`coordinateFrameAt x₀` replaced by an **arbitrary** index type `Idx` and frame
`frame : Idx → (x : M) → TangentSpace I x`.

The proofs are *identical* one-liners over the frame-free Ricci identity
`nablaRm04_ricciIdentityAt`; the frame only supplies tangent vectors at `x₀`. -/

section GenericFrame

variable {Idx : Type*} [Fintype Idx] [DecidableEq Idx]

/-- The `Fin 5` tensor-slot tuple for the `(0, 5)` Ricci identity on `∇Rm` in a
general frame: the inner derivative direction `d₂` followed by the four `Rm`
slots.  Generic-frame analogue of `nabla3InnerSlots`. -/
def nabla3InnerSlotsF
    (frame : Idx → (x : M) → TangentSpace I x) (x : M)
    (d₂ : Idx) (m : Fin 4 → Idx) :
    Fin 5 → TangentSpace I x :=
  Fin.cons (frame d₂ x) (frameTuple (I := I) frame x m)

/-- The `Fin 7` frame tuple feeding `nabla3Rm04Field` in a general frame:
derivative directions `d₀, d₁, d₂` then the four `Rm` slots.  Generic-frame
analogue of `nabla3FrameTuple`. -/
def nabla3FrameTupleF
    (frame : Idx → (x : M) → TangentSpace I x) (x : M)
    (d₀ d₁ d₂ : Idx) (m : Fin 4 → Idx) :
    Fin 7 → TangentSpace I x :=
  metricTraceInput (I := I) (frame d₀ x) (frame d₁ x)
    (nabla3InnerSlotsF (I := I) frame x d₂ m)

/-- The explicit `Rm ∗ ∇Rm` reaction array at `x₀` in a general frame, the sum of
the two curvature contributions of the operator identity
`∇_a∇_b∇_c − ∇_c∇_a∇_b = ∇_a([∇_b,∇_c]Rm) + [∇_a,∇_c](∇_b Rm)`.  Generic-frame
analogue of `nablaLapCommReactionTerm`. -/
def nablaLapCommReactionTermF
    {D : DifferentialGeometry.Integral.Connection.RealTimeInterval}
    (S : SolutionOn (I := I) (M := M) D) (t : Real) (x₀ : M)
    (frame : Idx → (x : M) → TangentSpace I x)
    (a b c : Idx) (m : Fin 4 → Idx) :
    Real :=
  (nabla3Rm04Field (I := I) S t x₀
        (nabla3FrameTupleF (I := I) frame x₀ a b c m) -
      nabla3Rm04Field (I := I) S t x₀
        (nabla3FrameTupleF (I := I) frame x₀ a c b m)) +
    curvatureAction0SAt (I := I) (S.base.rm13 t) (nablaRm04Field (I := I) S t x₀)
      (frame a x₀) (frame c x₀)
      (nabla3InnerSlotsF (I := I) frame x₀ b m)

/-- **The per-direction spatial commutator identity in a general frame.**
`(∇_a∇_b∇_c − ∇_c∇_a∇_b) Rm = nabla3(a,b,c) − nabla3(c,a,b) = reaction`, derived
from the Jacobi telescoping and the frame-free `(0, 5)` Ricci identity
`nablaRm04_ricciIdentityAt`.  Generic-frame analogue of `nablaLapComm_pointwise`. -/
theorem nablaLapCommF_pointwise
    {D : DifferentialGeometry.Integral.Connection.RealTimeInterval}
    (S : SolutionOn (I := I) (M := M) D)
    (hS : IsSolutionOn (I := I) S)
    (t : DifferentialGeometry.Integral.Connection.RealTimeInterval.RegularTime D)
    (x₀ : M)
    (frame : Idx → (x : M) → TangentSpace I x)
    (a b c : Idx) (m : Fin 4 → Idx) :
    nabla3Rm04Field (I := I) S (t : Real) x₀
        (nabla3FrameTupleF (I := I) frame x₀ a b c m) -
      nabla3Rm04Field (I := I) S (t : Real) x₀
        (nabla3FrameTupleF (I := I) frame x₀ c a b m) =
      nablaLapCommReactionTermF (I := I) S (t : Real) x₀ frame a b c m := by
  classical
  have hR2 :=
    nablaRm04_ricciIdentityAt (I := I) S hS t x₀
      (frame a x₀) (frame c x₀)
      (nabla3InnerSlotsF (I := I) frame x₀ b m)
  rw [nablaLapCommReactionTermF]
  simp only [nabla3FrameTupleF, nabla3InnerSlotsF] at hR2 ⊢
  linarith [hR2]

/-- The component-level rough Laplacian of `∇Rm` at `x₀` in a general frame: the
`gInv`-trace of the outer derivative pair of `∇³Rm`.  Generic-frame analogue of
`roughLapNablaRmComp`. -/
def roughLapNablaRmCompF
    {D : DifferentialGeometry.Integral.Connection.RealTimeInterval}
    (S : SolutionOn (I := I) (M := M) D) (t : Real) (x₀ : M)
    (frame : Idx → (x : M) → TangentSpace I x)
    (gInv : Idx → Idx → Real)
    (c : Idx) (m : Fin 4 → Idx) :
    Real :=
  ∑ a : Idx, ∑ b : Idx,
    gInv a b *
      nabla3Rm04Field (I := I) S t x₀
        (nabla3FrameTupleF (I := I) frame x₀ a b c m)

/-- The component-level covariant derivative of the rough Laplacian of `Rm` at `x₀`
in a general frame: the `gInv`-trace of the inner derivative pair of `∇³Rm`.
Generic-frame analogue of `nablaRoughLapRmComp`. -/
def nablaRoughLapRmCompF
    {D : DifferentialGeometry.Integral.Connection.RealTimeInterval}
    (S : SolutionOn (I := I) (M := M) D) (t : Real) (x₀ : M)
    (frame : Idx → (x : M) → TangentSpace I x)
    (gInv : Idx → Idx → Real)
    (c : Idx) (m : Fin 4 → Idx) :
    Real :=
  ∑ a : Idx, ∑ b : Idx,
    gInv a b *
      nabla3Rm04Field (I := I) S t x₀
        (nabla3FrameTupleF (I := I) frame x₀ c a b m)

/-- **The `gInv`-traced spatial commutator identity in a general frame.**
`Δ(∇Rm)(c) − ∇(ΔRm)(c) = Σ_{a,b} gInv a b · reaction a b c m`.  Generic-frame
analogue of `nablaLapComm_trace`; summed from `nablaLapCommF_pointwise`. -/
theorem nablaLapCommF_trace
    {D : DifferentialGeometry.Integral.Connection.RealTimeInterval}
    (S : SolutionOn (I := I) (M := M) D)
    (hS : IsSolutionOn (I := I) S)
    (t : DifferentialGeometry.Integral.Connection.RealTimeInterval.RegularTime D)
    (x₀ : M)
    (frame : Idx → (x : M) → TangentSpace I x)
    (gInv : Idx → Idx → Real)
    (c : Idx) (m : Fin 4 → Idx) :
    roughLapNablaRmCompF (I := I) S (t : Real) x₀ frame gInv c m -
        nablaRoughLapRmCompF (I := I) S (t : Real) x₀ frame gInv c m =
      ∑ a : Idx, ∑ b : Idx,
        gInv a b * nablaLapCommReactionTermF (I := I) S (t : Real) x₀ frame a b c m := by
  classical
  rw [roughLapNablaRmCompF, nablaRoughLapRmCompF]
  rw [← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun b _ => ?_
  rw [← mul_sub, nablaLapCommF_pointwise (I := I) S hS t x₀ frame a b c m]

/-- **The orthonormal-frame spatial commutator identity in a general frame.**
When `gInv = δ`, the double trace collapses to the diagonal sum
`Δ(∇Rm)(c) − ∇(ΔRm)(c) = Σ_a reaction a a c m`.  Generic-frame analogue of
`nablaLapComm_orthonormalTrace`.

Here, crucially, the hypothesis `horth : gInv = δ` is satisfied by the **genuine**
inverse metric of an orthonormal frame (Section `OrthonormalFrame`), so the
diagonal trace really is the rough Laplacian `Δ = gᵃᵇ ∇ₐ∇ᵦ`. -/
theorem nablaLapCommF_orthonormalTrace
    {D : DifferentialGeometry.Integral.Connection.RealTimeInterval}
    (S : SolutionOn (I := I) (M := M) D)
    (hS : IsSolutionOn (I := I) S)
    (t : DifferentialGeometry.Integral.Connection.RealTimeInterval.RegularTime D)
    (x₀ : M)
    (frame : Idx → (x : M) → TangentSpace I x)
    (gInv : Idx → Idx → Real)
    (horth : ∀ i j : Idx, gInv i j = if i = j then 1 else 0)
    (c : Idx) (m : Fin 4 → Idx) :
    roughLapNablaRmCompF (I := I) S (t : Real) x₀ frame gInv c m -
        nablaRoughLapRmCompF (I := I) S (t : Real) x₀ frame gInv c m =
      ∑ a : Idx,
        nablaLapCommReactionTermF (I := I) S (t : Real) x₀ frame a a c m := by
  classical
  rw [nablaLapCommF_trace (I := I) S hS t x₀ frame gInv c m]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [Finset.sum_eq_single a]
  · rw [horth a a, if_pos rfl, one_mul]
  · intro b _ hb
    rw [horth a b, if_neg (fun h => hb h.symm), zero_mul]
  · intro h; exact absurd (Finset.mem_univ a) h

end GenericFrame

/-! ## Section `OrthonormalFrame` — a pointwise `g`-orthonormal frame at `x₀`

We build a `g`-orthonormal frame of `T_{x₀}M` from the **fibre** metric
`g x₀ = S.family.metric t`, with **no** model `[InnerProductSpace ℝ E]`.  The
construction is the chart-locality-free `letI … ofCore` Gram–Schmidt of
`exists_orthonormal_frame_riemannianFiberNormSq` (it puts the fibre inner product
on `T_{x₀}M` via `g.toRiemannianMetric.toCore x₀` and takes
`stdOrthonormalBasis`). -/

section OrthonormalFrame

/-- A `g`-orthonormal frame of `T_{x₀}M` at the centre `x₀`, packaged as a frame
`Fin n → (x : M) → TangentSpace I x` (with `n` the tangent dimension).  Its values
**at `x₀`** are a `g x₀`-orthonormal basis; off `x₀` it is the same fibre vector
transported as a constant function (the commutator only ever reads it at `x₀`, so
the off-centre behaviour is irrelevant).

This exists for the fibre metric of a Ricci-flow solution at any time and point,
with **no** model inner-product assumption: the inner product on the fibre
`T_{x₀}M` is built from `g.toRiemannianMetric.toCore x₀` via the chart-locality-free
`letI … ofCore` Gram–Schmidt (the technique of
`exists_orthonormal_frame_riemannianFiberNormSq`), and `stdOrthonormalBasis`
supplies a `g x₀`-orthonormal basis.  `RiemannianMetric.toCore`/`.continuousAt`/
`.isVonNBounded` (`Mathlib/Topology/VectorBundle/Riemannian.lean`) require only a
`NormedAddCommGroup`/`NormedSpace` model fibre, never `[InnerProductSpace ℝ E]`. -/
theorem exists_orthoFrameAt
    {D : DifferentialGeometry.Integral.Connection.RealTimeInterval}
    (S : SolutionOn (I := I) (M := M) D) (t : Real) (x₀ : M) :
    ∃ (n : ℕ) (frame : Fin n → (x : M) → TangentSpace I x),
      (∀ i j : Fin n,
        (S.family.metric t).inner x₀ (frame i x₀) (frame j x₀) =
          if i = j then (1 : Real) else 0) := by
  classical
  -- The fibre inner product on `T_{x₀}M` from the Ricci-flow metric's fibre metric.
  set g := S.family.metric t with hg_def
  let cd : InnerProductSpace.Core Real (TangentSpace I x₀) := g.toRiemannianMetric.toCore x₀
  have hc : ContinuousAt (fun v : TangentSpace I x₀ => cd.inner v v) 0 :=
    g.toRiemannianMetric.continuousAt x₀
  have hbnd : Bornology.IsVonNBounded Real {v : TangentSpace I x₀ |
      RCLike.re (cd.inner v v) < 1} :=
    g.toRiemannianMetric.isVonNBounded x₀
  letI nag : NormedAddCommGroup (TangentSpace I x₀) :=
    cd.toNormedAddCommGroupOfTopology hc hbnd
  letI ips : InnerProductSpace Real (TangentSpace I x₀) :=
    InnerProductSpace.ofCoreOfTopology cd hc hbnd
  set n : ℕ := Module.finrank Real (TangentSpace I x₀) with hn_def
  set e : OrthonormalBasis (Fin n) Real (TangentSpace I x₀) :=
    stdOrthonormalBasis Real (TangentSpace I x₀) with he_def
  -- The `letI` inner product is, by construction, the fibre metric `g x₀`.
  have hinner_eq : ∀ u v : TangentSpace I x₀, (inner Real u v : Real) = g.inner x₀ u v :=
    fun u v => rfl
  -- Promote the fibre vectors `e i : T_{x₀}M` to constant-in-the-base frames.
  refine ⟨n, fun i _x => e i, ?_⟩
  intro i j
  have horth : Orthonormal Real (fun i : Fin n => e i) := e.orthonormal
  have hite := (orthonormal_iff_ite (𝕜 := Real) (E := TangentSpace I x₀)).mp horth i j
  rw [← hinner_eq (e i) (e j)]
  simpa using hite

end OrthonormalFrame

/-! ## Section `Adapter` — the spatial commutator in a genuine orthonormal frame

Combining the generic-frame commutator with the pointwise `g`-orthonormal frame:
the spatial commutator `[Δ, ∇_c] Rm` is available in a frame whose inverse metric
is **honestly** `δ` (`InverseMetricOrthonormalAt`), exactly the convention the
producer (`Evolution/NablaRiemannHeat.lean`) consumes.

The `gInv` here is the constant Kronecker delta, and the
`InverseMetricOrthonormalAt` witness is **not** an assumption about the chart
coordinate frame: it is the *true* inverse metric of the `g`-orthonormal frame
`orthoFrame`, because for a `g`-orthonormal basis `gᵃᵇ = δ`. -/

section Adapter

/-- The constant Kronecker-delta inverse metric, the genuine inverse metric of a
`g`-orthonormal frame. -/
def deltaInvMetric {Idx : Type*} [DecidableEq Idx] :
    Real → DifferentialGeometry.Integral.Connection.InverseMetricComponents M Idx :=
  fun _ _ i j => if i = j then 1 else 0

@[simp] theorem deltaInvMetric_apply {Idx : Type*} [DecidableEq Idx]
    (t : Real) (x : M) (i j : Idx) :
    deltaInvMetric (M := M) (Idx := Idx) t x i j = if i = j then 1 else 0 := rfl

/-- `deltaInvMetric` is orthonormal at every `(t, x)`: it is by definition the
Kronecker delta.  This is the **honest** `InverseMetricOrthonormalAt` witness for a
`g`-orthonormal frame, with no claim about `coordinateFrameAt`. -/
theorem deltaInvMetric_orthonormal {Idx : Type*} [Fintype Idx] [DecidableEq Idx]
    (t : Real) (x : M) :
    InverseMetricOrthonormalAt (M := M) (Idx := Idx) (deltaInvMetric (M := M)) t x := by
  intro i j; rfl

/-- **The frame-change adapter: the `k = 1` spatial commutator in a genuine
orthonormal frame.**

At the chart centre `x₀`, for a Ricci-flow solution at a regular time, there exist
a `g`-orthonormal frame `frame` of `T_{x₀}M` (from the *fibre* metric
`S.family.metric t`) and the Kronecker-delta inverse metric `deltaInvMetric`,
such that:

* `InverseMetricOrthonormalAt deltaInvMetric t x₀` holds **genuinely** — `gᵃᵇ = δ`
  is the *true* inverse metric of `frame`, since `frame` is `g x₀`-orthonormal
  (so `roughLapNablaRmCompF … frame δ` is the genuine rough Laplacian
  `Δ(∇Rm) = gᵃᵇ ∇ₐ∇ᵦ ∇Rm`); and
* the spatial commutator collapses to the diagonal trace
  `Δ(∇Rm)(c) − ∇(ΔRm)(c) = Σ_a reaction a a c m`,

which is exactly the orthonormal shape the producer
(`nablaRm04NormHeatBoundOn_of_components`, via the heat residual `(∂ₜ − Δ)∇Rm`)
consumes.

This is the honest replacement for `nablaLapComm_orthonormalTrace`, whose `δ`
hypothesis was *unsatisfiable* for the chart coordinate frame's true inverse
metric.  The producer is **not** weakened: `coordinateFrameAt` is never asserted
orthonormal; the orthonormality is the proved fibre-metric Gram–Schmidt
(`exists_orthoFrameAt`). -/
theorem nablaLapComm_orthoFrame
    {D : DifferentialGeometry.Integral.Connection.RealTimeInterval}
    (S : SolutionOn (I := I) (M := M) D)
    (hS : IsSolutionOn (I := I) S)
    (t : DifferentialGeometry.Integral.Connection.RealTimeInterval.RegularTime D)
    (x₀ : M) :
    ∃ (n : ℕ) (frame : Fin n → (x : M) → TangentSpace I x),
      (∀ i j : Fin n,
        (S.family.metric (t : Real)).inner x₀ (frame i x₀) (frame j x₀) =
          if i = j then (1 : Real) else 0) ∧
      InverseMetricOrthonormalAt (M := M) (Idx := Fin n)
        (deltaInvMetric (M := M)) (t : Real) x₀ ∧
      ∀ (c : Fin n) (m : Fin 4 → Fin n),
        roughLapNablaRmCompF (I := I) S (t : Real) x₀ frame
            (deltaInvMetric (M := M) (Idx := Fin n) (t : Real) x₀) c m -
          nablaRoughLapRmCompF (I := I) S (t : Real) x₀ frame
            (deltaInvMetric (M := M) (Idx := Fin n) (t : Real) x₀) c m =
          ∑ a : Fin n,
            nablaLapCommReactionTermF (I := I) S (t : Real) x₀ frame a a c m := by
  classical
  obtain ⟨n, frame, horthFrame⟩ := exists_orthoFrameAt (I := I) S (t : Real) x₀
  refine ⟨n, frame, horthFrame, deltaInvMetric_orthonormal (M := M) (t : Real) x₀, ?_⟩
  intro c m
  exact nablaLapCommF_orthonormalTrace (I := I) S hS t x₀ frame
    (deltaInvMetric (M := M) (Idx := Fin n) (t : Real) x₀)
    (fun i j => rfl) c m

end Adapter

/-! ## Produced shape and remaining wall

**Produced (sorry-free, no axiomatized frame-change/orthonormality).**

* `nablaLapCommF_pointwise` / `_trace` / `_orthonormalTrace` — the spatial
  commutator `[Δ, ∇_c] Rm = reaction` over an **arbitrary** index type and frame,
  the genuine reusable abstraction of the `coordinateFrameAt` lemmas of
  `Evolution/NablaRiemannCommutator.lean` (proved from the frame-free Ricci
  identity `nablaRm04_ricciIdentityAt`).
* `exists_orthoFrameAt` — a pointwise `g`-orthonormal frame of `T_{x₀}M` from the
  *fibre* metric `S.family.metric t`, with **no** model `[InnerProductSpace ℝ E]`
  (the chart-locality-free `letI … ofCore` Gram–Schmidt
  `g.toRiemannianMetric.toCore x₀` + `stdOrthonormalBasis`).
* `deltaInvMetric_orthonormal` — the **honest** `InverseMetricOrthonormalAt`
  witness, the genuine inverse metric of the orthonormal frame.
* `nablaLapComm_orthoFrame` — the assembled adapter: the `k = 1` spatial commutator
  in a genuine orthonormal frame, with the producer's `InverseMetricOrthonormalAt`
  satisfied **honestly** (not assumed about `coordinateFrameAt`).

**Cited lemmas:** `nablaRm04_ricciIdentityAt`, `rm04_ricciIdentityAt`
(`Evolution/RmRealizationBridge.lean`); `RiemannianMetric.toCore` /
`InnerProductSpace.ofCoreOfTopology` / `stdOrthonormalBasis`
(`Mathlib/Topology/VectorBundle/Riemannian.lean`, `Mathlib/Analysis/InnerProductSpace/PiL2.lean`);
`InverseMetricOrthonormalAt` (`Evolution/RiemannNormHeatProducer.lean`).  The
construction mirrors `exists_orthonormal_frame_riemannianFiberNormSq`
(`Analysis/Elliptic/…/RiemannianFiberNormSqRiemannOpVWFactorBound.lean`).

**This removes frame obstruction #4** (`IteratedNablaRmTower.md` / the
`NablaRiemannCommutatorBound.lean` footer): the `∇rm13`-free `T₂` half — and indeed
the *whole* spatial commutator — is now available in the orthonormal frame the
producer demands, with a genuine `gᵃᵇ = δ`.

**Remaining wall (the quantitative bound, unchanged and separate).**  The
quantitative reaction estimate `|reaction| ≤ C(dim)·|Rm|·|∇Rm|` is still not closed.
Its `T₁` summand `∇_a([∇_b,∇_c]Rm) = ∇_a(Rm ∗ Rm)` needs the **`(1,3)`
raising-parallelism** `∇(raise rm04) = raise(∇ rm04)` (bound obstruction #1, a
tensor-layer metric-compatibility lemma in
`Geometry/Connection/MetricCompatibility/TensorLoweringParallel.lean`), which is
*orthogonal* to the frame change resolved here.  This adapter is exactly the
frame-change bridge the footer named as "the exact theorem needed next" for `T₂`;
the `T₁` raising-parallelism remains the genuinely missing tensor API. -/

end DifferentialGeometry.PDE.RicciFlow
