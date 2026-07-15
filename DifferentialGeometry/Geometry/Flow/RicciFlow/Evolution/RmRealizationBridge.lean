import DifferentialGeometry.Geometry.Flow.RicciFlow.Evolution.IteratedNablaRmTower

set_option autoImplicit false
set_option linter.style.longLine false
set_option linter.unusedSectionVars false
set_option linter.unusedFintypeInType false
set_option linter.unusedDecidableInType false

/-!
# The rank-(0,4)/(0,5) `Rm` realization bridge

This file connects the **component-array producer** of the Bernstein–Bando–Shi
curvature-derivative tower to the **bundled `Tensor0SSection` curvature machinery**.

* The producer (`Evolution/IteratedNablaRmTower.lean`) builds `∇ᵏRm` as a
  rank-`(4+k)` component array `iteratedRmComp frame chr base k` through the
  pure-real `covDerivStepComp` recursion.
* The curvature/Ricci-identity machinery acts on bundled `Tensor0SSection`s with
  realization predicates (`Nabla0SSectionRealizes`, `Nabla20SRealizesAt`,
  `tensor0S_ricciIdentity_of_torsionFree`).

For a Ricci-flow `SolutionOn` we provide:

* `nablaRm04Field` / `nabla2Rm04Field` — the bundled `∇Rm` (rank 5) and `∇²Rm`
  (rank 6) of the lowered Riemann tensor `S.base.rm04`, the exact analogues of
  `nablaRicField` / `nabla2RicField` in `Evolution/Scalar/IntrinsicDerivation.lean`;
* `covDerivStepComp_frameComp_eq` — the rank-uniform **step bridge**: the explicit
  frame covariant-derivative array `covDerivStepComp` of the frame-component array
  of a bundled tensor equals the canonical `totalNabla0S` evaluated at the frame
  vectors (this is the rank-uniform generalization of `coordNab2Ric_eq_nabla2RicField`);
* `iteratedRmComp_one_eq_nablaRm04Field` — the **∇Rm bridge** (rank 5): the
  level-1 producer array, frame-evaluated, equals `nablaRm04Field` at the frame
  vectors, on the whole coordinate-frame neighbourhood;
* `iteratedRmComp_two_eq_nabla2Rm04Field` — the **∇²Rm bridge** (rank 6): the
  level-2 producer array, frame-evaluated at the centre, equals `nabla2Rm04Field`
  at the frame vectors;
* `rm04_nabla20SRealizesAt` / `nablaRm04_nabla20SRealizesAt` — the discharged
  `Nabla20SRealizesAt` packages making the `(0,s)` Ricci identity
  `tensor0S_ricciIdentity_of_torsionFree` applicable at `s = 4` and `s = 5`, and
  the resulting `Tensor0SRicciIdentityAt` instances `rm04_ricciIdentityAt` /
  `nablaRm04_ricciIdentityAt`.

Everything mirrors the bundled-vs-coordinate `(0,2)` template
(`coordNab2Ric_eq_nabla2RicField`, `coordCommAt`); no realization predicate is
assumed — the `Nabla*RealizesAt` witnesses are all discharged from the canonical
`CanonicalSpatialDerivs0S.of_smooth_connection` producer.
-/

noncomputable section

namespace DifferentialGeometry.PDE.RicciFlow

open Bundle Tensor0SBundle
open DifferentialGeometry.Tensor.Coordinates
open scoped Manifold ContDiff BigOperators

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace Real E]
variable [FiniteDimensional Real E]
variable {H : Type*} [TopologicalSpace H]
variable {I : ModelWithCorners Real E H} [I.Boundaryless]
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
variable [IsManifold I 1 M] [IsManifold I 2 M]
variable [IsManifold I ((∞ : WithTop ℕ∞) + 1) M]
variable [CompleteSpace E] [SigmaCompactSpace M] [T2Space M]

/-! ## Frame-vector helpers -/

section FrameTuple

variable {Idx : Type*} [Fintype Idx] [DecidableEq Idx]

/-- Turn a multi-index `m : Fin r → Idx` into the corresponding tuple of frame
vectors `q ↦ frame (m q) x`. -/
def frameTuple {r : ℕ}
    (frame : Idx → (x : M) → TangentSpace I x) (x : M) (m : Fin r → Idx) :
    Fin r → TangentSpace I x :=
  fun q => frame (m q) x

/-- The frame-component array of a bundled covariant `(0,r)` tensor field:
`A x` evaluated on the frame vectors selected by the multi-index. -/
def frameComp0S {r : ℕ}
    (A : Tensor0SField (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      (n := (∞ : WithTop ℕ∞)) r)
    (frame : Idx → (x : M) → TangentSpace I x) :
    M → (Fin r → Idx) → Real :=
  fun x m => A x (frameTuple (I := I) frame x m)

@[simp] theorem frameComp0S_apply {r : ℕ}
    (A : Tensor0SField (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      (n := (∞ : WithTop ℕ∞)) r)
    (frame : Idx → (x : M) → TangentSpace I x) (x : M) (m : Fin r → Idx) :
    frameComp0S (I := I) A frame x m = A x (fun q => frame (m q) x) := rfl

/-- A multi-index tuple of frame vectors decomposes as the leading slot followed
by the tail tuple. -/
theorem frameTuple_eq_cons {r : ℕ}
    (frame : Idx → (x : M) → TangentSpace I x) (x : M) (n : Fin (r + 1) → Idx) :
    frameTuple (I := I) frame x n =
      Fin.cons (frame (n 0) x) (frameTuple (I := I) frame x (Fin.tail n)) := by
  funext q
  refine Fin.cases ?_ ?_ q
  · simp [frameTuple]
  · intro q
    simp [frameTuple, Fin.tail]

end FrameTuple

/-! ## The rank-uniform step bridge

This is the heart of the file: the explicit frame covariant-derivative array
`covDerivStepComp`, fed the frame-component array of a bundled `(0,s)` tensor `A`
and its canonical Christoffel data, equals the canonical total covariant
derivative `totalNabla0S` of `A` evaluated on the frame vectors.

It is the rank-uniform generalization of the `(0,2)` identity
`coordNab2Ric_eq_nabla2RicField` (the second-Ricci-derivative coordinate
realization) and of `coordNab2Can`. -/

section StepBridge

variable {Idx : Type*} [Fintype Idx] [DecidableEq Idx] {u : Set M}

/-- **The rank-uniform step bridge.**  For a smooth covariant `(0,s)` tensor
field `A` whose canonical first total covariant derivative `nablaA` realizes the
total derivative (`TotalNabla0SRealizes`), the explicit `covDerivStepComp`
covariant-derivative array of the frame-component array of `A` — using the frame
directional derivative and the Christoffel data of the connection — equals
`nablaA` evaluated on the frame vectors.

This holds at every point of the local-frame domain `u`. -/
theorem covDerivStepComp_frameComp_eq {s : ℕ}
    (cov : CovariantDerivative I E (TangentSpace I : M → Type _))
    (A : Tensor0SField (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      (n := (∞ : WithTop ℕ∞)) s)
    (nablaA : Tensor0SField (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      (n := (∞ : WithTop ℕ∞)) (s + 1))
    (hreal : TotalNabla0SRealizes (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      s cov A nablaA)
    (frame : Idx → (x : M) → TangentSpace I x)
    (hframe : IsLocalFrameOn I E (1 : WithTop ℕ∞) frame u) (hu : IsOpen u)
    {x : M} (hx : x ∈ u) (n : Fin (s + 1) → Idx) :
    covDerivStepComp
        (frameExtData (I := I) frame (frameComp0S (I := I) A frame) x)
        (christoffelSymbolInFrame cov frame hframe x)
        (frameComp0S (I := I) A frame x) n =
      nablaA x (frameTuple (I := I) frame x n) := by
  classical
  -- The moving slots are the tail frame vectors; the derivative slot is `n 0`.
  set V : Fin s → (y : M) → TangentSpace I y :=
    fun q y => frame (Fin.tail n q) y with hV_def
  -- Realize the derivative direction by a smooth global section.
  obtain ⟨X, hX⟩ :=
    ContMDiffSection.exists_eq_at_gen
      (I := I) (F := E) (V := TangentSpace I) (n := (⊤ : ℕ∞)) x (frame (n 0) x)
  -- `C¹` smoothness of each moving frame slot at `x`.
  have hV_at : ∀ q : Fin s,
      ContMDiffAt I (I.prod 𝓘(Real, E)) (1 : WithTop ℕ∞)
        (fun y : M => (⟨y, V q y⟩ : TotalSpace E (TangentSpace I : M → Type _))) x := by
    intro q
    have htop :
        ContMDiffAt I (I.prod 𝓘(Real, E)) (1 : WithTop ℕ∞)
          (fun y : M =>
            (⟨y, frame (Fin.tail n q) y⟩ :
              TotalSpace E (TangentSpace I : M → Type _))) x :=
      (hframe.contMDiffAt hu hx (Fin.tail n q))
    simpa [hV_def] using htop
  -- The canonical derivation rule for the realized total derivative.
  have heval :=
    (hreal X x (fun q : Fin s => V q x)).trans
      (nabla0SFun_eval_C1_slots
        (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
        cov X V A x hV_at)
  -- Rewrite the leading derivative slot value `X x = frame (n 0) x`.
  -- LHS of `covDerivStepComp` unfolds to `frameExtData … − Σ Christoffel`.
  unfold covDerivStepComp
  rw [frameTuple_eq_cons (I := I) frame x n]
  -- Identify the bundled value with the realized derivation formula.
  rw [show
      nablaA x (Fin.cons (frame (n 0) x)
          (frameTuple (I := I) frame x (Fin.tail n))) =
        nablaA x (Fin.cons (X x) (fun q : Fin s => V q x)) by
        rw [hX]; rfl]
  rw [heval, hX]
  -- The exterior-derivative terms agree definitionally.
  have hext :
      extDerivFun (I := I)
          (fun p : M => A p (fun q : Fin s => V q p)) x (frame (n 0) x) =
        frameExtData (I := I) frame (frameComp0S (I := I) A frame) x
          (Fin.tail n) (n 0) := by
    rfl
  rw [hext]
  -- It remains to match the Christoffel-correction sum.
  congr 1
  -- Expand each `cov`-corrected slot into a sum over the Christoffel symbols.
  have hslot : ∀ q : Fin s,
      A x
          (Function.update (fun b : Fin s => V b x) q ((cov (V q) x) (frame (n 0) x))) =
        ∑ p : Idx,
          christoffelSymbolInFrame cov frame hframe x (n 0) (Fin.tail n q) p *
            frameComp0S (I := I) A frame x
              (Function.update (Fin.tail n) q p) := by
    intro q
    have hVq : V q = frame (Fin.tail n q) := by funext y; rfl
    have hcov :
        (cov (V q) x) (frame (n 0) x) =
          ∑ p : Idx,
            christoffelSymbolInFrame cov frame hframe x (n 0) (Fin.tail n q) p •
              frame p x := by
      rw [hVq]
      exact covariantDerivative_eq_sum_christoffel
        (𝕜 := Real) (I := I) (cov := cov) (frame := frame) (hframe := hframe) hx
        (n 0) (Fin.tail n q)
    rw [hcov]
    rw [show
        A x
            (Function.update (fun b : Fin s => V b x) q
              (∑ p : Idx,
                christoffelSymbolInFrame cov frame hframe x (n 0) (Fin.tail n q) p •
                  frame p x)) =
          (A x).toMultilinearMap
            (Function.update (fun b : Fin s => V b x) q
              (∑ p : Idx,
                christoffelSymbolInFrame cov frame hframe x (n 0) (Fin.tail n q) p •
                  frame p x)) from rfl]
    rw [MultilinearMap.map_update_sum]
    refine Finset.sum_congr rfl fun p _ => ?_
    rw [MultilinearMap.map_update_smul]
    -- Identify the updated slot tuple with a frame-component array entry.
    have hupd :
        Function.update (fun b : Fin s => V b x) q (frame p x) =
          frameTuple (I := I) frame x (Function.update (Fin.tail n) q p) := by
      funext r
      by_cases hr : r = q
      · subst hr; simp [frameTuple, Function.update_self]
      · simp [frameTuple, Function.update_of_ne hr, hV_def]
    rw [show
        (A x).toMultilinearMap (Function.update (fun b : Fin s => V b x) q (frame p x)) =
          A x (Function.update (fun b : Fin s => V b x) q (frame p x)) from rfl]
    rw [hupd]
    simp [frameComp0S, smul_eq_mul]
  -- Assemble: each producer correction term is the corresponding eval term.
  exact Finset.sum_congr rfl fun q _ => (hslot q).symm

end StepBridge

/-! ## Solution-side helpers -/

section Solution

/-- The connection of a solution at time `t` is `∞`-smooth (Levi-Civita), the
input required by `CanonicalSpatialDerivs0S.of_smooth_connection`. -/
theorem connSmoothInf
    {D : DifferentialGeometry.Integral.Connection.RealTimeInterval}
    (S : SolutionOn (I := I) (M := M) D) (t : Real) :
    CovariantDerivative.ContMDiffCovariantDerivativeLocally
      (S.family.connection t) (∞ : WithTop ℕ∞) := by
  simpa [SolutionFamily.connection, metricCov] using
    metricCov_smooth (I := I) (M := M) (S.base.metric t)

/-- The scalar exterior-derivative directional derivative respects eventual
equality of the differentiated function. -/
theorem extDerivFun_eventuallyEq_congr
    {f g : M → Real} {x : M} (V : TangentSpace I x)
    (h : f =ᶠ[nhds x] g) :
    extDerivFun (I := I) f x V = extDerivFun (I := I) g x V := by
  rw [extDerivFun_real_eq_mfderiv (I := I) f x V,
    extDerivFun_real_eq_mfderiv (I := I) g x V]
  rw [Filter.EventuallyEq.mfderiv_eq (I := I) (I' := 𝓘(Real, Real)) h]
  rfl

/-! ## Bundled `∇Rm`, `∇²Rm`, `∇³Rm`

The exact analogues of `nablaRicField` / `nabla2RicField` for the lowered
Riemann tensor, built explicitly through `totalNabla0S` so that each level's
realization witness is available with no cross-definition defeq juggling. -/

/-- The canonical first covariant-derivative tensor field `∇Rm` of the lowered
Riemann tensor (rank 5). -/
def nablaRm04Field
    {D : DifferentialGeometry.Integral.Connection.RealTimeInterval}
    (S : SolutionOn (I := I) (M := M) D) (t : Real) :
    Tensor0SField (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      (n := (∞ : WithTop ℕ∞)) 5 :=
  totalNabla0S (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
    4 (S.family.connection t) (S.base.rm04 t)
    (totalNabla0S_reg (E := E) (H := H) (I := I) (M := M)
      4 (S.family.connection t) (connSmoothInf (I := I) S t) (S.base.rm04 t))

/-- The canonical second covariant-derivative tensor field `∇²Rm` of the lowered
Riemann tensor (rank 6). -/
def nabla2Rm04Field
    {D : DifferentialGeometry.Integral.Connection.RealTimeInterval}
    (S : SolutionOn (I := I) (M := M) D) (t : Real) :
    Tensor0SField (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      (n := (∞ : WithTop ℕ∞)) 6 :=
  totalNabla0S (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
    5 (S.family.connection t) (nablaRm04Field (I := I) S t)
    (totalNabla0S_reg (E := E) (H := H) (I := I) (M := M)
      5 (S.family.connection t) (connSmoothInf (I := I) S t)
      (nablaRm04Field (I := I) S t))

/-- The canonical third covariant-derivative tensor field `∇³Rm` of the lowered
Riemann tensor (rank 7).  Needed only as the second-order realization witness for
the `(0,5)` Ricci identity applied to `∇Rm`. -/
def nabla3Rm04Field
    {D : DifferentialGeometry.Integral.Connection.RealTimeInterval}
    (S : SolutionOn (I := I) (M := M) D) (t : Real) :
    Tensor0SField (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      (n := (∞ : WithTop ℕ∞)) 7 :=
  totalNabla0S (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
    6 (S.family.connection t) (nabla2Rm04Field (I := I) S t)
    (totalNabla0S_reg (E := E) (H := H) (I := I) (M := M)
      6 (S.family.connection t) (connSmoothInf (I := I) S t)
      (nabla2Rm04Field (I := I) S t))

theorem nablaRm04Field_realizes
    {D : DifferentialGeometry.Integral.Connection.RealTimeInterval}
    (S : SolutionOn (I := I) (M := M) D) (t : Real) :
    TotalNabla0SRealizes (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      4 (S.family.connection t) (S.base.rm04 t) (nablaRm04Field (I := I) S t) :=
  totalNabla0S_realizes (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
    4 (S.family.connection t) (S.base.rm04 t)
    (totalNabla0S_reg (E := E) (H := H) (I := I) (M := M)
      4 (S.family.connection t) (connSmoothInf (I := I) S t) (S.base.rm04 t))

theorem nabla2Rm04Field_realizes
    {D : DifferentialGeometry.Integral.Connection.RealTimeInterval}
    (S : SolutionOn (I := I) (M := M) D) (t : Real) :
    TotalNabla0SRealizes (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      5 (S.family.connection t) (nablaRm04Field (I := I) S t)
      (nabla2Rm04Field (I := I) S t) :=
  totalNabla0S_realizes (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
    5 (S.family.connection t) (nablaRm04Field (I := I) S t)
    (totalNabla0S_reg (E := E) (H := H) (I := I) (M := M)
      5 (S.family.connection t) (connSmoothInf (I := I) S t)
      (nablaRm04Field (I := I) S t))

theorem nabla3Rm04Field_realizes
    {D : DifferentialGeometry.Integral.Connection.RealTimeInterval}
    (S : SolutionOn (I := I) (M := M) D) (t : Real) :
    TotalNabla0SRealizes (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      6 (S.family.connection t) (nabla2Rm04Field (I := I) S t)
      (nabla3Rm04Field (I := I) S t) :=
  totalNabla0S_realizes (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
    6 (S.family.connection t) (nabla2Rm04Field (I := I) S t)
    (totalNabla0S_reg (E := E) (H := H) (I := I) (M := M)
      6 (S.family.connection t) (connSmoothInf (I := I) S t)
      (nabla2Rm04Field (I := I) S t))

/-! ## The producer instantiation

The "realized" arguments to `iteratedRmComp` for a solution: the coordinate
frame, the realized Christoffel data, and the realized lowered Riemann component
array. -/

/-- The realized Christoffel data for a solution in the coordinate frame centred
at `x₀`. -/
def realizedChr
    {D : DifferentialGeometry.Integral.Connection.RealTimeInterval}
    (S : SolutionOn (I := I) (M := M) D) (x₀ : M) :
    Real → M → CoordinateIdx (𝕜 := Real) E → CoordinateIdx (𝕜 := Real) E →
      CoordinateIdx (𝕜 := Real) E → Real :=
  fun t x =>
    christoffelSymbolInFrame (S.family.connection t)
      (coordinateFrameAt (I := I) x₀)
      (coordinateFrameAt_isLocalFrame_one (I := I) x₀) x

/-- The realized lowered Riemann component array (level `0` of the tower) for a
solution in the coordinate frame centred at `x₀`. -/
def realizedRmBase
    {D : DifferentialGeometry.Integral.Connection.RealTimeInterval}
    (S : SolutionOn (I := I) (M := M) D) (x₀ : M) :
    Real → M → (Fin 4 → CoordinateIdx (𝕜 := Real) E) → Real :=
  fun t => frameComp0S (I := I) (S.base.rm04 t) (coordinateFrameAt (I := I) x₀)

@[simp] theorem realizedRmBase_apply
    {D : DifferentialGeometry.Integral.Connection.RealTimeInterval}
    (S : SolutionOn (I := I) (M := M) D) (x₀ : M)
    (t : Real) (x : M) (m : Fin 4 → CoordinateIdx (𝕜 := Real) E) :
    realizedRmBase (I := I) S x₀ t x m =
      S.base.rm04 t x (fun q => coordinateFrameAt (I := I) x₀ (m q) x) := rfl

/-! ## The `∇Rm` bridge (rank 5)

The level-1 producer array, frame-evaluated, equals the bundled `∇Rm` at the
frame vectors — on the whole coordinate-frame neighbourhood.  This is the genuine
rank-5 analogue of `coordNab2Ric_eq_nabla2RicField`. -/

/-- **The ∇Rm bridge (rank 5).**  At every point of the coordinate-frame
neighbourhood of `x₀`, the level-1 iterated-derivative component array
`iteratedRmComp (coordinateFrame) (realizedChr) (realizedRmBase) 1` equals the
canonical bundled `∇Rm` (`nablaRm04Field`) evaluated on the frame vectors. -/
theorem iteratedRmComp_one_eq_nablaRm04Field
    {D : DifferentialGeometry.Integral.Connection.RealTimeInterval}
    (S : SolutionOn (I := I) (M := M) D)
    (x₀ : M) (t : Real)
    {x : M} (hx : x ∈ coordinateFrameSet (I := I) x₀)
    (n : Fin 5 → CoordinateIdx (𝕜 := Real) E) :
    iteratedRmComp (I := I) (coordinateFrameAt (I := I) x₀)
        (realizedChr (I := I) S x₀) (realizedRmBase (I := I) S x₀) 1 t x n =
      nablaRm04Field (I := I) S t x
        (frameTuple (I := I) (coordinateFrameAt (I := I) x₀) x n) := by
  rw [iteratedRmComp_succ]
  simp only [iteratedRmComp_zero]
  exact covDerivStepComp_frameComp_eq
    (I := I) (S.family.connection t) (S.base.rm04 t) (nablaRm04Field (I := I) S t)
    (nablaRm04Field_realizes (I := I) S t)
    (coordinateFrameAt (I := I) x₀)
    (coordinateFrameAt_isLocalFrame_one (I := I) x₀)
    (coordinateFrameSet_open (I := I) x₀) hx n

/-! ## The `∇²Rm` bridge (rank 6)

The level-2 producer array, frame-evaluated at the centre, equals the bundled
`∇²Rm` at the frame vectors.  This uses the neighbourhood form of the ∇Rm bridge
to rewrite the inner level-1 array as the frame-component array of the bundled
`∇Rm`, then applies the step bridge once more. -/

/-- **The ∇²Rm bridge (rank 6).**  At the centre `x₀`, the level-2
iterated-derivative component array equals the canonical bundled `∇²Rm`
(`nabla2Rm04Field`) evaluated on the frame vectors. -/
theorem iteratedRmComp_two_eq_nabla2Rm04Field
    {D : DifferentialGeometry.Integral.Connection.RealTimeInterval}
    (S : SolutionOn (I := I) (M := M) D)
    (x₀ : M) (t : Real)
    (n : Fin 6 → CoordinateIdx (𝕜 := Real) E) :
    iteratedRmComp (I := I) (coordinateFrameAt (I := I) x₀)
        (realizedChr (I := I) S x₀) (realizedRmBase (I := I) S x₀) 2 t x₀ n =
      nabla2Rm04Field (I := I) S t x₀
        (frameTuple (I := I) (coordinateFrameAt (I := I) x₀) x₀ n) := by
  classical
  set frame := coordinateFrameAt (I := I) x₀ with hframe_def
  -- The inner level-1 array equals the frame-component array of the bundled `∇Rm`
  -- throughout the coordinate-frame neighbourhood.
  have hlevel1 :
      (fun y : M =>
          iteratedRmComp (I := I) frame
            (realizedChr (I := I) S x₀) (realizedRmBase (I := I) S x₀) 1 t y) =ᶠ[nhds x₀]
        fun y : M =>
          frameComp0S (I := I) (nablaRm04Field (I := I) S t) frame y := by
    refine Filter.eventually_of_mem
      ((coordinateFrameSet_open (I := I) x₀).mem_nhds (coordinateFrameAt_mem (I := I) x₀))
      ?_
    intro y hy
    funext m
    simpa [frameComp0S, hframe_def] using
      iteratedRmComp_one_eq_nablaRm04Field (I := I) S x₀ t hy m
  -- Expand the level-2 step.
  rw [iteratedRmComp_succ]
  -- Rewrite the `covDerivStepComp` inputs using the level-1 identity near `x₀`.
  have hext :
      frameExtData (I := I) frame
          (fun y : M =>
            iteratedRmComp (I := I) frame
              (realizedChr (I := I) S x₀) (realizedRmBase (I := I) S x₀) 1 t y) x₀ =
        frameExtData (I := I) frame
          (frameComp0S (I := I) (nablaRm04Field (I := I) S t) frame) x₀ := by
    funext m d
    simp only [frameExtData]
    refine extDerivFun_eventuallyEq_congr (I := I) _ ?_
    exact hlevel1.mono fun y hy => congrFun hy m
  have hbase :
      iteratedRmComp (I := I) frame
          (realizedChr (I := I) S x₀) (realizedRmBase (I := I) S x₀) 1 t x₀ =
        frameComp0S (I := I) (nablaRm04Field (I := I) S t) frame x₀ :=
    hlevel1.self_of_nhds
  rw [hext, hbase]
  -- Now apply the step bridge for the rank-5 field `∇Rm`.
  exact covDerivStepComp_frameComp_eq
    (I := I) (S.family.connection t) (nablaRm04Field (I := I) S t)
    (nabla2Rm04Field (I := I) S t)
    (nabla2Rm04Field_realizes (I := I) S t)
    frame
    (coordinateFrameAt_isLocalFrame_one (I := I) x₀)
    (coordinateFrameSet_open (I := I) x₀) (coordinateFrameAt_mem (I := I) x₀) n

end Solution

/-! ## Ricci-identity realization packages

The discharged `Nabla20SRealizesAt` packages making the `(0,s)` Ricci identity
`tensor0S_ricciIdentity_of_torsionFree` applicable at `s = 4` (for `Rm`) and at
`s = 5` (for `∇Rm`).  These are obtained, with no axiomatization, from the
canonical `CanonicalSpatialDerivs0S` realizations. -/

section RicciIdentity

/-- `Nabla0SSectionRealizes` for `Rm`: the bundled `∇Rm` realizes the covariant
derivative of `S.base.rm04` (the `s = 4` first-derivative realization). -/
theorem rm04_nabla0SSectionRealizes
    {D : DifferentialGeometry.Integral.Connection.RealTimeInterval}
    (S : SolutionOn (I := I) (M := M) D) (t : Real) :
    DifferentialGeometry.Integral.Connection.Nabla0SSectionRealizes (I := I) 4
      (S.family.connection t) (S.base.rm04 t) (nablaRm04Field (I := I) S t) := by
  intro y X slots
  exact nablaRm04Field_realizes (I := I) S t X y slots

/-- `Nabla0SSectionRealizes` for `∇Rm`: the bundled `∇²Rm` realizes the covariant
derivative of `∇Rm` (the `s = 5` first-derivative realization). -/
theorem nablaRm04_nabla0SSectionRealizes
    {D : DifferentialGeometry.Integral.Connection.RealTimeInterval}
    (S : SolutionOn (I := I) (M := M) D) (t : Real) :
    DifferentialGeometry.Integral.Connection.Nabla0SSectionRealizes (I := I) 5
      (S.family.connection t) (nablaRm04Field (I := I) S t)
      (nabla2Rm04Field (I := I) S t) := by
  intro y X slots
  exact nabla2Rm04Field_realizes (I := I) S t X y slots

/-- **`Nabla20SRealizesAt` for `Rm` (s = 4).**  The bundled `∇Rm`/`∇²Rm` realize
the true first and second covariant derivatives of `S.base.rm04` at every point,
discharging the hypothesis the `(0,4)` Ricci identity needs. -/
theorem rm04_nabla20SRealizesAt
    {D : DifferentialGeometry.Integral.Connection.RealTimeInterval}
    (S : SolutionOn (I := I) (M := M) D) (t : Real) (x : M) :
    DifferentialGeometry.Integral.Connection.Nabla20SRealizesAt (I := I) 4
      (S.family.connection t) (S.base.rm04 t) (nablaRm04Field (I := I) S t) x
      (nabla2Rm04Field (I := I) S t x) := by
  refine ⟨rm04_nabla0SSectionRealizes (I := I) S t, ?_⟩
  intro X slots
  exact nabla2Rm04Field_realizes (I := I) S t X x slots

/-- **`Nabla20SRealizesAt` for `∇Rm` (s = 5).**  The bundled `∇²Rm`/`∇³Rm` realize
the true first and second covariant derivatives of `∇Rm` at every point,
discharging the hypothesis the `(0,5)` Ricci identity needs. -/
theorem nablaRm04_nabla20SRealizesAt
    {D : DifferentialGeometry.Integral.Connection.RealTimeInterval}
    (S : SolutionOn (I := I) (M := M) D) (t : Real) (x : M) :
    DifferentialGeometry.Integral.Connection.Nabla20SRealizesAt (I := I) 5
      (S.family.connection t) (nablaRm04Field (I := I) S t)
      (nabla2Rm04Field (I := I) S t) x
      (nabla3Rm04Field (I := I) S t x) := by
  refine ⟨nablaRm04_nabla0SSectionRealizes (I := I) S t, ?_⟩
  intro X slots
  exact nabla3Rm04Field_realizes (I := I) S t X x slots

/-- **The `(0,4)` Ricci identity for `Rm`.**  The Ricci-identity commutator of
the bundled `∇²Rm` equals the slotwise curvature action on `Rm`, at every regular
time and point — produced from the discharged realization package above. -/
theorem rm04_ricciIdentityAt
    {D : DifferentialGeometry.Integral.Connection.RealTimeInterval}
    (S : SolutionOn (I := I) (M := M) D)
    (hS : IsSolutionOn (I := I) S)
    (t : DifferentialGeometry.Integral.Connection.RealTimeInterval.RegularTime D)
    (x : M) :
    DifferentialGeometry.Integral.Connection.Tensor0SRicciIdentityAt (I := I)
      (S.base.rm13 (t : Real)) (S.base.rm04 (t : Real) x)
      (nabla2Rm04Field (I := I) S (t : Real) x) := by
  have hcov :
      CovariantDerivative.ContMDiffCovariantDerivativeLocally
        (S.family.connection (t : Real)) (1 : WithTop ℕ∞) :=
    connSmoothOfSol (I := I) S hS (t : Real) (D.regular_subset t.2)
  have htor : (S.family.connection (t : Real)).torsion x = 0 := by
    have htf :=
      DifferentialGeometry.Integral.Connection.torsionFree_of_isLeviCivita
        (I := I) (lcAt_regular (I := I) S hS t)
    simpa [DifferentialGeometry.Integral.Connection.IsTorsionFreeAt] using htf x
  exact DifferentialGeometry.Integral.Connection.tensor0S_ricciIdentity_of_torsionFree
    (I := I) (S.family.connection (t : Real)) hcov (S.base.rm13 (t : Real))
    (S.base.rm04 (t : Real)) (nablaRm04Field (I := I) S (t : Real))
    (S.base.rm04 (t : Real) x) (nablaRm04Field (I := I) S (t : Real) x)
    (nabla2Rm04Field (I := I) S (t : Real) x)
    (rm13OfSol (I := I) S (t : Real) (D.regular_subset t.2)) rfl rfl
    (rm04_nabla20SRealizesAt (I := I) S (t : Real) x) htor

/-- **The `(0,5)` Ricci identity for `∇Rm`.**  The Ricci-identity commutator of
the bundled `∇³Rm` equals the slotwise curvature action on `∇Rm`, at every
regular time and point — produced from the discharged realization package. -/
theorem nablaRm04_ricciIdentityAt
    {D : DifferentialGeometry.Integral.Connection.RealTimeInterval}
    (S : SolutionOn (I := I) (M := M) D)
    (hS : IsSolutionOn (I := I) S)
    (t : DifferentialGeometry.Integral.Connection.RealTimeInterval.RegularTime D)
    (x : M) :
    DifferentialGeometry.Integral.Connection.Tensor0SRicciIdentityAt (I := I)
      (S.base.rm13 (t : Real)) (nablaRm04Field (I := I) S (t : Real) x)
      (nabla3Rm04Field (I := I) S (t : Real) x) := by
  have hcov :
      CovariantDerivative.ContMDiffCovariantDerivativeLocally
        (S.family.connection (t : Real)) (1 : WithTop ℕ∞) :=
    connSmoothOfSol (I := I) S hS (t : Real) (D.regular_subset t.2)
  have htor : (S.family.connection (t : Real)).torsion x = 0 := by
    have htf :=
      DifferentialGeometry.Integral.Connection.torsionFree_of_isLeviCivita
        (I := I) (lcAt_regular (I := I) S hS t)
    simpa [DifferentialGeometry.Integral.Connection.IsTorsionFreeAt] using htf x
  exact DifferentialGeometry.Integral.Connection.tensor0S_ricciIdentity_of_torsionFree
    (I := I) (S.family.connection (t : Real)) hcov (S.base.rm13 (t : Real))
    (nablaRm04Field (I := I) S (t : Real)) (nabla2Rm04Field (I := I) S (t : Real))
    (nablaRm04Field (I := I) S (t : Real) x)
    (nabla2Rm04Field (I := I) S (t : Real) x)
    (nabla3Rm04Field (I := I) S (t : Real) x)
    (rm13OfSol (I := I) S (t : Real) (D.regular_subset t.2)) rfl rfl
    (nablaRm04_nabla20SRealizesAt (I := I) S (t : Real) x) htor

end RicciIdentity

end DifferentialGeometry.PDE.RicciFlow
