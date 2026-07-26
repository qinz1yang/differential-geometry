import DifferentialGeometry.Geometry.Comparison.ExpBallDiffeo
import DifferentialGeometry.Geometry.Exponential.FramedNormalCoordinates
import DifferentialGeometry.Geometry.Flow.RicciFlow.HCGCompactness.PointedRiemannian
import DifferentialGeometry.Geometry.Flow.RicciFlow.HCGCompactness.C4.GoodCoveringSeq

set_option autoImplicit false
set_option linter.unusedSectionVars false

/-!
# MSM135 Chapter 4 `lbl383` item 3 — per-manifold exp-ball diffeomorphism (B5 bridge)

The layer bridge from the Step A net (over `PointedRiemannianManifold`s `X.obj k`) to the
exponential ball diffeomorphism `exists_expBall_diffeo_of_lt` (`ExpBallDiffeo.lean`,
item 3a, unconditional): for a bundled pointed Riemannian manifold `Y`, a center `c : Y.M`,
and a radius `ρ` below both the injectivity radius and the intrinsic framed
radius of `Y.metric` at `c`, the framed exponential map is a `C^1` partial
diffeomorphism on `Metric.ball 0 ρ`.

This is the per-center half of `lbl383` item 3; the net-level instantiation (the radius
discipline `λ^α ≤ expRadiusGp` — the book's "`D` large enough" choice — and the
universal clause over live centers) consumes this.
-/

noncomputable section

universe u uE uH

namespace DifferentialGeometry
namespace HCGCompactness

open scoped Manifold ContDiff
open DifferentialGeometry.Geometry.Riemannian
open DifferentialGeometry.Geometry.Riemannian.NormalCoordinates
open DifferentialGeometry.Geometry.Riemannian.Exponential

variable {E : Type uE} [NormedAddCommGroup E]
variable [InnerProductSpace Real E] [FiniteDimensional Real E]
variable [NeZero (Module.finrank Real E)] [CompleteSpace E]
variable {H : Type uH} [TopologicalSpace H]
variable {I : ModelWithCorners Real E H}
variable [I.Boundaryless]

/-- **`lbl383` item 3, per-manifold form.**  On a bundled pointed Riemannian manifold `Y`,
for a center `c` and radius `ρ ≤ expRadiusGp Y.metric c` with
`ofReal ρ < injRadius Y.metric c`, the framed exponential map restricts to a
`C^1` partial diffeomorphism with source `Metric.ball 0 ρ`.  The bundle's stored instances
(`Y.topology`, …, `Y.t2TangentBundle`) are installed locally; the nonsingularity input is
discharged inside `exists_expBall_diffeo_of_lt` from normal coordinates. -/
theorem PointedRiemannianManifold.exists_expBall_diffeo
    (Y : PointedRiemannianManifold.{u, uE, uH} (I := I)) (c : Y.M) {ρ : Real} :
    letI := Y.topology
    letI := Y.charted
    letI := Y.smooth
    letI := Y.sigmaCompact
    letI := Y.t2
    letI := Y.t2TangentBundle
    ENNReal.ofReal ρ < injRadius (I := I) Y.metric c →
    ρ ≤ expRadiusGp (I := I) Y.metric c →
      ∃ Φ : PartialDiffeomorph 𝓘(ℝ, E) I E Y.M 1,
        Φ.source = Metric.ball (0 : E) ρ ∧
        Φ.target = framedExpMap (I := I) Y.metric c '' Metric.ball (0 : E) ρ ∧
        Set.EqOn Φ (framedExpMap (I := I) Y.metric c)
          (Metric.ball (0 : E) ρ) := by
  letI := Y.topology
  letI := Y.charted
  letI := Y.smooth
  letI := Y.sigmaCompact
  letI := Y.t2
  letI := Y.t2TangentBundle
  intro hinj hC2
  exact exists_expBall_diffeo_of_lt (I := I) Y.metric c hinj hC2

variable {X : PointedRiemannianSeq.{u, uE, uH} (I := I)}

/-- The scalar multiplying `lamInf` in the book's item-3 exponential-ball
radius.  It is kept separate from the radius predicate so the divisor can be
chosen once before the packing bound is instantiated. -/
def item3RadiusFactor (hd : InjRadiusDecayInput (I := I) X) (D : Real) : Real :=
  205 * Real.exp (hd.C * (20 * hd.lambda D 0))

/-- The book's item-3 radius factor is positive. -/
theorem item3Factor_pos (hd : InjRadiusDecayInput (I := I) X) (D : Real) :
    0 < item3RadiusFactor hd D := by
  exact mul_pos (by norm_num) (Real.exp_pos _)

/-- **Honest-input (book "`D` large enough", `lbl391`/`lbl392`).**  At each live net center
`x_k^α`, the chosen item-3 ball radius `ρ k α` is below the intrinsic framed radius and the
injectivity radius of the realized metric `(X.obj k).metric`.  This is the §5 geometric
scale choice: the injectivity part follows from `InjRadiusDecayInput.decay` (for `D > 1`),
the `C²` part from the curvature-comparison `C²`-radius lower bound (the `lbl413`/§5
boundary).  `ProperMetricOn.realizes` identifies the net's `ms`-distance radii with the
Riemannian ones, so `ρ` is well-defined across the layer. -/
def Item3RadiusInput (hd : InjRadiusDecayInput (I := I) X) (D : Real)
    (P : ∀ k : Nat, ProperMetricOn (I := I) (X.obj k)) (ρ : Nat → Nat → Real) : Prop :=
  ∀ k α : Nat, ∀ c : (X.obj k).M, c ∈ seqCenter hd D P k α →
    letI := (X.obj k).topology
    letI := (X.obj k).charted
    letI := (X.obj k).smooth
    letI := (X.obj k).sigmaCompact
    letI := (X.obj k).t2
    letI := (X.obj k).t2TangentBundle
    ENNReal.ofReal (ρ k α) < injRadius (I := I) (X.obj k).metric c ∧
      ρ k α ≤ expRadiusGp (I := I) (X.obj k).metric c

/-- The item-3 radius discipline at one sequence index and on the finite
packing family, for radii `a * lamInf γ`. -/
def Item3RadiusAt (hd : InjRadiusDecayInput (I := I) X) (D : Real)
    (P : ∀ k : Nat, ProperMetricOn (I := I) (X.obj k))
    (L : NetLimitData (I := I) hd D P) (pb : hd.PackingBound D) (r a : Real)
    (n : Nat) : Prop :=
  ∀ γ : Fin (pb.A r), ∀ c : (X.obj (L.φ n)).M,
    seqCenter hd D P (L.φ n) (γ : Nat) = some c →
      letI := (X.obj (L.φ n)).topology
      letI := (X.obj (L.φ n)).charted
      letI := (X.obj (L.φ n)).smooth
      letI := (X.obj (L.φ n)).sigmaCompact
      letI := (X.obj (L.φ n)).t2
      letI := (X.obj (L.φ n)).t2TangentBundle
      ENNReal.ofReal (a * L.lamInf (γ : Nat)) <
          injRadius (I := I) (X.obj (L.φ n)).metric c ∧
        a * L.lamInf (γ : Nat) ≤
          expRadiusGp (I := I) (X.obj (L.φ n)).metric c

/-- The finite packing-local item-3 radius discipline eventually holds along
the chosen net-limit subsequence. -/
def Item3RadiusTail (hd : InjRadiusDecayInput (I := I) X) (D : Real)
    (P : ∀ k : Nat, ProperMetricOn (I := I) (X.obj k))
    (L : NetLimitData (I := I) hd D P) (pb : hd.PackingBound D) (r a : Real) : Prop :=
  ∀ᶠ n in Filter.atTop, Item3RadiusAt (I := I) hd D P L pb r a n

/-- Reindex a packing-local item-3 radius tail along a further subsequence. -/
theorem Item3RadiusTail.subseq (hd : InjRadiusDecayInput (I := I) X) (D : Real)
    (P : ∀ k : Nat, ProperMetricOn (I := I) (X.obj k))
    (L : NetLimitData (I := I) hd D P) (pb : hd.PackingBound D) (r a : Real)
    (hrad : Item3RadiusTail (I := I) hd D P L pb r a)
    {ψ : Nat → Nat} (hψ : StrictMono ψ) :
    Item3RadiusTail (I := I) hd D P (L.subseq hψ) pb r a := by
  filter_upwards [hψ.tendsto_atTop.eventually hrad] with n hn
  intro γ c hc
  exact hn γ c hc

namespace Item3RadiusInput

/-- Reindex item-3 radius discipline along a subsequence. -/
theorem subseq (hd : InjRadiusDecayInput (I := I) X) (D : Real)
    (P : ∀ k : Nat, ProperMetricOn (I := I) (X.obj k)) (ρ : Nat → Nat → Real)
    (hrad : Item3RadiusInput (I := I) hd D P ρ) (f : Nat -> Nat) :
    Item3RadiusInput (I := I) (hd.subseq f) D (fun k => P (f k))
      (fun k α => ρ (f k) α) := by
  intro k α c hc
  have hc' : c ∈ seqCenter hd D P (f k) α := by
    simpa [seqCenter, InjRadiusDecayInput.subseq, InjRadiusDecayInput.lambda,
      InjRadiusDecayInput.mu, PointedRiemannianSeq.subseq] using hc
  simpa [InjRadiusDecayInput.subseq, PointedRiemannianSeq.subseq] using
    hrad (f k) α c hc'

end Item3RadiusInput

/-- **`lbl383` item 3, net-level producer.**  Given the radius-discipline input, every live
net center `x_k^α` carries the item-3 exponential ball diffeomorphism on `Metric.ball 0
(ρ k α)` of the realized metric `(X.obj k).metric`.  Reduces, per center, to the
per-manifold bridge `PointedRiemannianManifold.exists_expBall_diffeo`. -/
theorem exists_seqItem3Diffeo
    (hd : InjRadiusDecayInput (I := I) X) (D : Real)
    (P : ∀ k : Nat, ProperMetricOn (I := I) (X.obj k)) (ρ : Nat → Nat → Real)
    (hrad : Item3RadiusInput (I := I) hd D P ρ)
    (k α : Nat) (c : (X.obj k).M) (hc : c ∈ seqCenter hd D P k α) :
    letI := (X.obj k).topology
    letI := (X.obj k).charted
    letI := (X.obj k).smooth
    letI := (X.obj k).sigmaCompact
    letI := (X.obj k).t2
    letI := (X.obj k).t2TangentBundle
      ∃ Φ : PartialDiffeomorph 𝓘(ℝ, E) I E (X.obj k).M 1,
        Φ.source = Metric.ball (0 : E) (ρ k α) ∧
        Φ.target = framedExpMap (I := I) (X.obj k).metric c ''
          Metric.ball (0 : E) (ρ k α) ∧
        Set.EqOn Φ (framedExpMap (I := I) (X.obj k).metric c)
          (Metric.ball (0 : E) (ρ k α)) :=
  (X.obj k).exists_expBall_diffeo c (hrad k α c hc).1 (hrad k α c hc).2

/-- The packing-local fixed-index item-3 radius fact gives the corresponding
exponential-ball diffeomorphism at each selected slot. -/
theorem exists_item3Diffeo
    (hd : InjRadiusDecayInput (I := I) X) {D a r : Real}
    (P : ∀ k : Nat, ProperMetricOn (I := I) (X.obj k))
    (L : NetLimitData (I := I) hd D P) (pb : hd.PackingBound D) (n : Nat)
    (hrad : Item3RadiusAt (I := I) hd D P L pb r a n)
    (γ : Fin (pb.A r)) (c : (X.obj (L.φ n)).M)
    (hc : seqCenter hd D P (L.φ n) (γ : Nat) = some c) :
    letI := (X.obj (L.φ n)).topology
    letI := (X.obj (L.φ n)).charted
    letI := (X.obj (L.φ n)).smooth
    letI := (X.obj (L.φ n)).sigmaCompact
    letI := (X.obj (L.φ n)).t2
    letI := (X.obj (L.φ n)).t2TangentBundle
      ∃ Φ : PartialDiffeomorph 𝓘(ℝ, E) I E (X.obj (L.φ n)).M 1,
        Φ.source = Metric.ball (0 : E) (a * L.lamInf (γ : Nat)) ∧
        Φ.target = framedExpMap (I := I) (X.obj (L.φ n)).metric c ''
          Metric.ball (0 : E) (a * L.lamInf (γ : Nat)) ∧
        Set.EqOn Φ (framedExpMap (I := I) (X.obj (L.φ n)).metric c)
          (Metric.ball (0 : E) (a * L.lamInf (γ : Nat))) :=
  (X.obj (L.φ n)).exists_expBall_diffeo c
    (hrad γ c hc).1 (hrad γ c hc).2

/-- Legacy all-index form of the `lbl383`/`lbl427` `g_p` scale separation.  It
requires every natural-numbered slot at every index and is therefore stronger
than the construction needs.  The canonical post-packing API below uses
`Item3GpScaleAt` and `Item3GpScaleTail`; the H6 relative-radius profile produces
that finite eventual form.  This declaration remains as a compatibility input
for older callers. -/
def Item3GpScaleInput (hd : InjRadiusDecayInput (I := I) X) (D : Real)
    (P : ∀ k : Nat, ProperMetricOn (I := I) (X.obj k))
    (L : NetLimitData (I := I) hd D P) : Prop :=
  ∀ n γ : Nat, ∀ c : (X.obj (L.φ n)).M,
    seqCenter hd D P (L.φ n) γ = some c →
      letI : TopologicalSpace (X.obj (L.φ n)).M := (X.obj (L.φ n)).topology
      letI : ChartedSpace H (X.obj (L.φ n)).M := (X.obj (L.φ n)).charted
      letI : IsManifold I ∞ (X.obj (L.φ n)).M := (X.obj (L.φ n)).smooth
      letI : T2Space (X.obj (L.φ n)).M := (X.obj (L.φ n)).t2
      letI : T2Space (TangentBundle I (X.obj (L.φ n)).M) :=
        (X.obj (L.φ n)).t2TangentBundle
      4 * L.lamInf γ < expRadiusGp (I := I) (X.obj (L.φ n)).metric c

/-- The `g_p` scale separation at one sequence index, on the finite family of
slots selected by one fixed packing bound and source radius. -/
def Item3GpScaleAt (hd : InjRadiusDecayInput (I := I) X) (D : Real)
    (P : ∀ k : Nat, ProperMetricOn (I := I) (X.obj k))
    (L : NetLimitData (I := I) hd D P) (pb : hd.PackingBound D) (r : Real)
    (n : Nat) : Prop :=
  ∀ γ : Fin (pb.A r), ∀ c : (X.obj (L.φ n)).M,
    seqCenter hd D P (L.φ n) (γ : Nat) = some c →
      letI : TopologicalSpace (X.obj (L.φ n)).M := (X.obj (L.φ n)).topology
      letI : ChartedSpace H (X.obj (L.φ n)).M := (X.obj (L.φ n)).charted
      letI : IsManifold I ∞ (X.obj (L.φ n)).M := (X.obj (L.φ n)).smooth
      letI : T2Space (X.obj (L.φ n)).M := (X.obj (L.φ n)).t2
      letI : T2Space (TangentBundle I (X.obj (L.φ n)).M) :=
        (X.obj (L.φ n)).t2TangentBundle
      4 * L.lamInf (γ : Nat) < expRadiusGp (I := I) (X.obj (L.φ n)).metric c

/-- The finite packing-local scale separation eventually holds along the chosen
net-limit subsequence.  This is the construction-facing asymptotic input. -/
def Item3GpScaleTail (hd : InjRadiusDecayInput (I := I) X) (D : Real)
    (P : ∀ k : Nat, ProperMetricOn (I := I) (X.obj k))
    (L : NetLimitData (I := I) hd D P) (pb : hd.PackingBound D) (r : Real) : Prop :=
  ∀ᶠ n in Filter.atTop, Item3GpScaleAt (I := I) hd D P L pb r n

/-- The older all-slot scale input restricts to the finite packing family at
any fixed sequence index. -/
theorem Item3GpScaleInput.at (hd : InjRadiusDecayInput (I := I) X) (D : Real)
    (P : ∀ k : Nat, ProperMetricOn (I := I) (X.obj k))
    (L : NetLimitData (I := I) hd D P)
    (hgp : Item3GpScaleInput (I := I) hd D P L)
    (pb : hd.PackingBound D) (r : Real) (n : Nat) :
    Item3GpScaleAt (I := I) hd D P L pb r n := by
  intro γ c hc
  exact hgp n (γ : Nat) c hc

/-- The older all-slot scale input implies the finite packing-local tail input. -/
theorem Item3GpScaleInput.to_tail (hd : InjRadiusDecayInput (I := I) X) (D : Real)
    (P : ∀ k : Nat, ProperMetricOn (I := I) (X.obj k))
    (L : NetLimitData (I := I) hd D P)
    (hgp : Item3GpScaleInput (I := I) hd D P L)
    (pb : hd.PackingBound D) (r : Real) :
    Item3GpScaleTail (I := I) hd D P L pb r :=
  Filter.Eventually.of_forall fun n => hgp.at hd D P L pb r n

/-- Reindex the `g_p`-scale input along a further subsequence: `L.subseq hψ` shares
`L`'s `lamInf` and reindexes `φ` by `ψ`, so the scale separation transports directly. -/
theorem Item3GpScaleInput.subseq (hd : InjRadiusDecayInput (I := I) X) (D : Real)
    (P : ∀ k : Nat, ProperMetricOn (I := I) (X.obj k))
    (L : NetLimitData (I := I) hd D P)
    (hgp : Item3GpScaleInput (I := I) hd D P L)
    {ψ : Nat → Nat} (hψ : StrictMono ψ) :
    Item3GpScaleInput (I := I) hd D P (L.subseq hψ) := by
  intro n γ c hc
  exact hgp (ψ n) γ c hc

/-- Reindex a packing-local scale tail along a further subsequence. -/
theorem Item3GpScaleTail.subseq (hd : InjRadiusDecayInput (I := I) X) (D : Real)
    (P : ∀ k : Nat, ProperMetricOn (I := I) (X.obj k))
    (L : NetLimitData (I := I) hd D P) (pb : hd.PackingBound D) (r : Real)
    (hgp : Item3GpScaleTail (I := I) hd D P L pb r)
    {ψ : Nat → Nat} (hψ : StrictMono ψ) :
    Item3GpScaleTail (I := I) hd D P (L.subseq hψ) pb r := by
  filter_upwards [hψ.tendsto_atTop.eventually hgp] with n hn
  intro γ c hc
  exact hn γ c hc

end HCGCompactness
end DifferentialGeometry
