import DifferentialGeometry.Geometry.Flow.RicciFlow.Evolution.NablaRiemannCommutator

set_option autoImplicit false
set_option linter.style.longLine false
set_option linter.unusedSectionVars false
set_option linter.unusedFintypeInType false
set_option linter.unusedDecidableInType false

/-!
# The slot-swap/∇ commutation for the `∇³Rm` antisymmetrization `T₁`

This file works on the **first reaction summand** of
`Evolution/NablaRiemannCommutator.lean`,

`T₁ := nabla3Rm04Field(a,b,c,m) − nabla3Rm04Field(a,c,b,m)`,

the `∇³Rm` antisymmetrization in its two *non-leading* derivative slots `b, c`
(the leading/derivative slot is `a`).  The second reaction summand is already a
single `curvatureAction0SAt`; the wall (recorded in the footer of
`NablaRiemannCommutator.lean`) was to turn this `∇³Rm`-difference into a genuine
`Rm ∗ ∇Rm` bound.

## What is derived here (sorry-free, from the concrete evaluation formula)

The **slot-swap/∇ commutation**, `nablaLapComm_T1_eq_covDeriv_curvatureAction`:
at the chart centre `x₀`, for a Ricci-flow solution at a regular time,

`T₁ = extDerivFun (y ↦ curvatureAction0SAt (rm13 y) (Rm04 y) b c m) x₀ (frame a)`
`     − Σ_{q : Fin 6} curvatureAction0SAt (rm13 x₀) (Rm04 x₀) (Wq 0) (Wq 1) (tail Wq)`,

where `Wq` is the `q`-corrected slot tuple
`Function.update (b :: c :: m) q ((∇ frame_q) a)` (the Christoffel correction in
the `q`-th slot of `∇²Rm`).  This is **exactly** the tensorial derivation rule
(Definition 14.5, `eval_C1_slots`) for the covariant derivative `∇_a K` of the
curvature-action `(0,5)` field `K(y) := curvatureAction0SAt (rm13 y) (Rm04 y)`,
the field whose value is `[∇_b, ∇_c] Rm`.

### How it is derived (the concrete route, no abstract `domDomCongr`)

* `nabla3Rm04Field = totalNabla0S nabla2Rm04Field` (`nabla3Rm04Field_realizes`),
  so each of the two `nabla3` values expands through the **explicit** evaluation
  formula `TotalNabla0SRealizes.eval_C1_slots`:
  `(∇α)(a :: slots) = extDerivFun (y ↦ α y slots) x₀ a − Σ_q α x₀ (slots[q ↦ ∇_a e_q])`.
* The two expansions differ only by swapping the *non-leading* slots `b, c`.  The
  difference of the `extDerivFun` parts is the `extDerivFun` of the *difference*
  field (`extDerivFun_sub_at`), and the difference field is, **pointwise in `y`**,
  the `(b,c)` antisymmetrization of `∇²Rm` — i.e. `curvatureAction0SAt` by the
  pointwise `(0,4)` Ricci identity `rm04_ricciIdentityAt` applied at every `y`.
* The two Christoffel-correction sums are reindexed by the transposition
  `σ = swap 0 1` (which sends the `(b,c)`-ordered tuple to the `(c,b)`-ordered
  one); each paired difference is again a slot-0,1 antisymmetrization of `∇²Rm`,
  hence a `curvatureAction0SAt` by `rm04_ricciIdentityAt` at `x₀`.

The genuine `domDomCongr`/∇-commutation that a field-level route needs is thereby
**replaced** by the elementary `Function.update`/`Equiv.swap` reindexing of the
concrete correction sum.

## The remaining wall (the bound), reported precisely in the footer

`T₁ = ∇_a K`, `K = Rm ∗ Rm` (the curvature action).  Bounding `|T₁| ≤ C|Rm||∇Rm|`
requires the covariant Leibniz rule `∇(Rm ∗ Rm) = ∇Rm ∗ Rm + Rm ∗ ∇Rm` for this
specific `rm13`-contraction, **and** identifying `∇(rm13)` with `∇(Rm04)` (a metric
raising commuting with `∇`).  Neither is available: see the file footer for the
exact obstruction (`coordinateFrameAt` is the chart frame, **not** orthonormal at
its centre, so the raising cannot be trivialized there).
-/

noncomputable section

namespace DifferentialGeometry.PDE.RicciFlow

open Bundle Tensor0SBundle
open DifferentialGeometry.Tensor.Coordinates
open DifferentialGeometry.Integral.Connection
open scoped Manifold ContDiff BigOperators

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace Real E]
variable [Module.Finite Real E] [FiniteDimensional Real E]
variable {H : Type*} [TopologicalSpace H]
variable {I : ModelWithCorners Real E H} [I.Boundaryless]
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
variable [IsManifold I 1 M] [IsManifold I 2 M]
variable [IsManifold I ((∞ : WithTop ℕ∞) + 1) M]
variable [CompleteSpace E] [SigmaCompactSpace M] [T2Space M]

-- File-local instances so typeclass resolution finds the normed structure on the
-- `(0,s)` tensor model fibre, as in `Geometry/Metric/TensorInner/Tensor0SRiemannian.lean`.
private instance tensor0SModelNormedSpace_local {s : ℕ} :
    NormedSpace Real (Tensor0SModel s Real E) :=
  Tensor0SBundle.tensor0SModel_normedSpace s

private instance tensor0SModelNormedAddCommGroup_local {s : ℕ} :
    NormedAddCommGroup (Tensor0SModel s Real E) := inferInstance

/-! ## The `Fin 6` slot fields of `∇²Rm` for the outer `∇_a` step

`nabla3Rm04Field = ∇(nabla2Rm04Field)`, so in `nabla3Rm04Field(a, d₁, d₂, m)` the
leading slot is the new derivative direction `a` and the remaining six slots are
the six `∇²Rm` slots: the two derivative directions `d₁, d₂` followed by the four
`Rm` slots `m`.  We package these six slots as **vector fields** so the concrete
evaluation formula `eval_C1_slots` (Definition 14.5) applies. -/

/-- The six moving slot fields fed to the outer `∇_a` step of `∇³Rm`: the two
inner derivative directions `d₁, d₂` and the four `Rm`-slot frame fields. -/
def nabla3SlotFields
    (frame : CoordinateIdx (𝕜 := Real) E → (x : M) → TangentSpace I x)
    (d₁ d₂ : CoordinateIdx (𝕜 := Real) E) (m : Fin 4 → CoordinateIdx (𝕜 := Real) E) :
    Fin 6 → (x : M) → TangentSpace I x :=
  Fin.cons (frame d₁) (Fin.cons (frame d₂) (fun q : Fin 4 => frame (m q)))

/-- Swapping the two inner derivative directions `d₁, d₂` of the slot fields is the
`σ = swap 0 1` precomposition: `nabla3SlotFields frame d₂ d₁ m = nabla3SlotFields
frame d₁ d₂ m ∘ σ` as **vector fields** (not just pointwise). -/
theorem nabla3SlotFields_swap
    (frame : CoordinateIdx (𝕜 := Real) E → (x : M) → TangentSpace I x)
    (d₁ d₂ : CoordinateIdx (𝕜 := Real) E) (m : Fin 4 → CoordinateIdx (𝕜 := Real) E) :
    nabla3SlotFields (I := I) frame d₂ d₁ m =
      fun q : Fin 6 => nabla3SlotFields (I := I) frame d₁ d₂ m (Equiv.swap (0 : Fin 6) 1 q) := by
  funext q
  refine Fin.cases ?_ (fun q => ?_) q
  · change nabla3SlotFields (I := I) frame d₂ d₁ m 0 =
      nabla3SlotFields (I := I) frame d₁ d₂ m (Equiv.swap (0 : Fin 6) 1 0)
    rw [Equiv.swap_apply_left]; rfl
  · refine Fin.cases ?_ (fun q => ?_) q
    · change nabla3SlotFields (I := I) frame d₂ d₁ m 1 =
        nabla3SlotFields (I := I) frame d₁ d₂ m (Equiv.swap (0 : Fin 6) 1 1)
      rw [Equiv.swap_apply_right]; rfl
    · have hne0 : Fin.succ (Fin.succ q) ≠ (0 : Fin 6) := Fin.succ_ne_zero _
      have hne1 : Fin.succ (Fin.succ q) ≠ (1 : Fin 6) := by
        rw [show (1 : Fin 6) = Fin.succ 0 from rfl]
        exact fun h => Fin.succ_ne_zero _ (Fin.succ_injective _ h)
      change nabla3SlotFields (I := I) frame d₂ d₁ m (Fin.succ (Fin.succ q)) =
        nabla3SlotFields (I := I) frame d₁ d₂ m (Equiv.swap (0 : Fin 6) 1 (Fin.succ (Fin.succ q)))
      rw [Equiv.swap_apply_of_ne_of_ne hne0 hne1]; rfl

/-- The `∇³Rm` frame tuple is the leading derivative direction `a` consed onto the
six `∇²Rm` slot fields evaluated at `x`. -/
theorem nabla3FrameTuple_eq_cons_slotFields
    (frame : CoordinateIdx (𝕜 := Real) E → (x : M) → TangentSpace I x) (x : M)
    (a d₁ d₂ : CoordinateIdx (𝕜 := Real) E) (m : Fin 4 → CoordinateIdx (𝕜 := Real) E) :
    nabla3FrameTuple (I := I) frame x a d₁ d₂ m =
      Fin.cons (frame a x)
        (fun q : Fin 6 => nabla3SlotFields (I := I) frame d₁ d₂ m q x) := by
  funext q
  refine Fin.cases ?_ (fun q => ?_) q
  · rfl
  · -- The six tail slots: unfold both sides through the `Fin.cons` layers.
    simp only [nabla3FrameTuple, nabla3InnerSlots, metricTraceInput, nabla3SlotFields,
      Fin.cons_succ]
    refine Fin.cases ?_ (fun q => ?_) q
    · rfl
    · refine Fin.cases ?_ (fun q => ?_) q
      · rfl
      · rfl

/-- The inner tensor-slot tuple `nabla3InnerSlots d₂ m` agrees with the tail of the
six slot fields at every point: it is `(frame d₂) :: (frame ∘ m)`. -/
theorem nabla3InnerSlots_eq_tail_slotFields
    (frame : CoordinateIdx (𝕜 := Real) E → (x : M) → TangentSpace I x) (x : M)
    (d₁ d₂ : CoordinateIdx (𝕜 := Real) E) (m : Fin 4 → CoordinateIdx (𝕜 := Real) E) :
    nabla3InnerSlots (I := I) frame x d₂ m =
      fun q : Fin 5 =>
        (Fin.tail (fun r : Fin 6 => nabla3SlotFields (I := I) frame d₁ d₂ m r x)) q := by
  funext q
  simp only [nabla3InnerSlots, nabla3SlotFields, Fin.tail]
  refine Fin.cases ?_ (fun q => ?_) q
  · rfl
  · rfl

/-! ## The concrete `eval_C1_slots` expansion of one `∇³Rm` value

Each `nabla3Rm04Field(a, d₁, d₂, m)` is `∇_a` applied to `∇²Rm` evaluated on the
six slot fields `(d₁, d₂, m)`.  The explicit tensorial derivation rule
(`TotalNabla0SRealizes.eval_C1_slots`, Definition 14.5) splits it into the
`extDerivFun` of the scalar evaluation plus the Christoffel corrections in each of
the six slots. -/

/-- **Concrete expansion of one `∇³Rm` value.**  At the chart centre,
`nabla3Rm04Field(a, d₁, d₂, m)` equals the directional derivative of the scalar
field `y ↦ ∇²Rm(y)(d₁, d₂, m)` along `frame a`, minus the Christoffel correction
in each of the six `∇²Rm` slots.  This is `eval_C1_slots` for the canonical total
derivative `nabla3Rm04Field = ∇(nabla2Rm04Field)`. -/
theorem nabla3Rm04Field_eval_expand
    {D : DifferentialGeometry.Integral.Connection.RealTimeInterval}
    (S : SolutionOn (I := I) (M := M) D) (t : Real) (x₀ : M)
    (a d₁ d₂ : CoordinateIdx (𝕜 := Real) E) (m : Fin 4 → CoordinateIdx (𝕜 := Real) E) :
    nabla3Rm04Field (I := I) S t x₀
        (nabla3FrameTuple (I := I) (coordinateFrameAt (I := I) x₀) x₀ a d₁ d₂ m) =
      extDerivFun (I := I)
          (fun p : M =>
            nabla2Rm04Field (I := I) S t p
              (fun q : Fin 6 => nabla3SlotFields (I := I) (coordinateFrameAt (I := I) x₀) d₁ d₂ m q p))
          x₀ (coordinateFrameAt (I := I) x₀ a x₀) -
        ∑ q : Fin 6,
          nabla2Rm04Field (I := I) S t x₀
            (Function.update
              (fun r : Fin 6 => nabla3SlotFields (I := I) (coordinateFrameAt (I := I) x₀) d₁ d₂ m r x₀) q
              ((S.family.connection t
                  (nabla3SlotFields (I := I) (coordinateFrameAt (I := I) x₀) d₁ d₂ m q) x₀)
                (coordinateFrameAt (I := I) x₀ a x₀))) := by
  classical
  set frame := coordinateFrameAt (I := I) x₀ with hframe_def
  set V : Fin 6 → (x : M) → TangentSpace I x :=
    nabla3SlotFields (I := I) frame d₁ d₂ m with hV_def
  -- A global smooth section realizing the derivative direction `frame a` at `x₀`.
  obtain ⟨X, hX⟩ :=
    ContMDiffSection.exists_eq_at_gen
      (I := I) (F := E) (V := TangentSpace I) (n := (⊤ : ℕ∞)) x₀ (frame a x₀)
  -- `C¹` smoothness of each of the six moving slot fields at `x₀`.
  have hV_at : ∀ q : Fin 6,
      ContMDiffAt I (I.prod 𝓘(Real, E)) (1 : WithTop ℕ∞)
        (fun y : M => (⟨y, V q y⟩ : TotalSpace E (TangentSpace I : M → Type _))) x₀ := by
    intro q
    -- Each slot field is a coordinate-frame field, hence `C¹` on the frame domain.
    have hbase : ∀ i : CoordinateIdx (𝕜 := Real) E,
        ContMDiffAt I (I.prod 𝓘(Real, E)) (1 : WithTop ℕ∞)
          (fun y : M => (⟨y, frame i y⟩ : TotalSpace E (TangentSpace I : M → Type _))) x₀ :=
      fun i =>
        (coordinateFrameAt_isLocalFrame_one (I := I) x₀).contMDiffAt
          (coordinateFrameSet_open (I := I) x₀) (coordinateFrameAt_mem (I := I) x₀) i
    -- Identify slot `q` with the right coordinate-frame field.
    refine Fin.cases ?_ (fun q => ?_) q
    · simpa [hV_def, nabla3SlotFields] using hbase d₁
    · refine Fin.cases ?_ (fun q => ?_) q
      · simpa [hV_def, nabla3SlotFields] using hbase d₂
      · simpa [hV_def, nabla3SlotFields] using hbase (m q)
  -- Apply the tensorial derivation rule (Definition 14.5) for `∇(nabla2Rm04Field)`.
  have heval :=
    (nabla3Rm04Field_realizes (I := I) S t).eval_C1_slots X V x₀ hV_at
  -- Rewrite the leading slot value `X x₀ = frame a x₀` and the cons-decomposition.
  rw [nabla3FrameTuple_eq_cons_slotFields (I := I) frame x₀ a d₁ d₂ m]
  rw [hX] at heval
  exact heval

/-! ## The curvature-action field `K = [∇_b, ∇_c] Rm`

The field whose value at `y` is the `(b,c)` curvature action on `Rm`.  By the
pointwise `(0,4)` Ricci identity `rm04_ricciIdentityAt`, it is exactly the `(b,c)`
antisymmetrization of `∇²Rm` — at **every** point `y`, which is what the
`extDerivFun` congruence needs. -/

/-- The slot-field tuple `nabla3SlotFields frame b c m`, evaluated at a point,
is the `metricTraceInput` consumed by the `(0,4)` Ricci identity on `∇²Rm`:
`(frame b) :: (frame c) :: (frame ∘ m)`. -/
theorem nabla3SlotFields_eq_metricTraceInput
    (frame : CoordinateIdx (𝕜 := Real) E → (x : M) → TangentSpace I x) (x : M)
    (b c : CoordinateIdx (𝕜 := Real) E) (m : Fin 4 → CoordinateIdx (𝕜 := Real) E) :
    (fun q : Fin 6 => nabla3SlotFields (I := I) frame b c m q x) =
      metricTraceInput (I := I) (frame b x) (frame c x)
        (frameTuple (I := I) frame x m) := by
  funext q
  simp only [nabla3SlotFields, metricTraceInput]
  refine Fin.cases ?_ (fun q => ?_) q
  · rfl
  · refine Fin.cases ?_ (fun q => ?_) q
    · rfl
    · rfl

/-- **The curvature-action field equals the `(b,c)`-antisymmetrized `∇²Rm` field,
pointwise.**  Using `rm04_ricciIdentityAt` at every point `y`, the difference of
`∇²Rm` on the `(b,c)`-ordered and `(c,b)`-ordered slot fields is the `(b,c)`
curvature action on `Rm`. -/
theorem nabla2Rm04Field_antisym_eq_curvatureAction_field
    {D : DifferentialGeometry.Integral.Connection.RealTimeInterval}
    (S : SolutionOn (I := I) (M := M) D)
    (hS : IsSolutionOn (I := I) S)
    (t : DifferentialGeometry.Integral.Connection.RealTimeInterval.RegularTime D)
    (x₀ : M)
    (b c : CoordinateIdx (𝕜 := Real) E) (m : Fin 4 → CoordinateIdx (𝕜 := Real) E) :
    (fun p : M =>
        nabla2Rm04Field (I := I) S (t : Real) p
            (fun q : Fin 6 =>
              nabla3SlotFields (I := I) (coordinateFrameAt (I := I) x₀) b c m q p) -
          nabla2Rm04Field (I := I) S (t : Real) p
            (fun q : Fin 6 =>
              nabla3SlotFields (I := I) (coordinateFrameAt (I := I) x₀) c b m q p)) =
      fun p : M =>
        curvatureAction0SAt (I := I) (S.base.rm13 (t : Real))
          (S.base.rm04 (t : Real) p)
          (coordinateFrameAt (I := I) x₀ b p) (coordinateFrameAt (I := I) x₀ c p)
          (frameTuple (I := I) (coordinateFrameAt (I := I) x₀) p m) := by
  funext p
  set frame := coordinateFrameAt (I := I) x₀ with hframe_def
  -- The `(0,4)` Ricci identity for `Rm` at the point `p`.
  have hR := rm04_ricciIdentityAt (I := I) S hS t p
    (frame b p) (frame c p) (frameTuple (I := I) frame p m)
  rw [nabla3SlotFields_eq_metricTraceInput (I := I) frame p b c m,
    nabla3SlotFields_eq_metricTraceInput (I := I) frame p c b m]
  exact hR

/-! ## The slot-0,1 antisymmetrization of a rank-6 tuple is a curvature action

For the Christoffel-correction sum we need, for **any** `Fin 6` tangent tuple `W`,
the slot-0,1 antisymmetrization of `∇²Rm`, which by `rm04_ricciIdentityAt` is the
curvature action with derivative directions `W 0, W 1` and `Rm`-slots the tail. -/

/-- A `Fin 6` tuple is its own `metricTraceInput` repackaging on slots `0, 1`. -/
theorem fin6_eq_metricTraceInput {x : M} (W : Fin 6 → TangentSpace I x) :
    W =
      metricTraceInput (I := I) (W 0) (W 1)
        (fun q : Fin 4 => W (Fin.succ (Fin.succ q))) := by
  funext j
  refine Fin.cases ?_ (fun j => ?_) j
  · rfl
  · refine Fin.cases ?_ (fun j => ?_) j
    · rfl
    · rfl

/-- Swapping slots `0, 1` of a `Fin 6` tuple is the `metricTraceInput` with `W 0`
and `W 1` exchanged. -/
theorem fin6_comp_swap_eq_metricTraceInput {x : M} (W : Fin 6 → TangentSpace I x) :
    W ∘ Equiv.swap (0 : Fin 6) 1 =
      metricTraceInput (I := I) (W 1) (W 0)
        (fun q : Fin 4 => W (Fin.succ (Fin.succ q))) := by
  funext j
  refine Fin.cases ?_ (fun j => ?_) j
  · change W (Equiv.swap (0 : Fin 6) 1 0) = _
    rw [Equiv.swap_apply_left]; rfl
  · refine Fin.cases ?_ (fun j => ?_) j
    · change W (Equiv.swap (0 : Fin 6) 1 1) = _
      rw [Equiv.swap_apply_right]; rfl
    · -- For `j ≥ 2` the swap is the identity.
      have hne0 : Fin.succ (Fin.succ j) ≠ (0 : Fin 6) := Fin.succ_ne_zero _
      have hne1 : Fin.succ (Fin.succ j) ≠ (1 : Fin 6) := by
        rw [show (1 : Fin 6) = Fin.succ 0 from rfl]
        exact fun h => Fin.succ_ne_zero _ (Fin.succ_injective _ h)
      change W (Equiv.swap (0 : Fin 6) 1 (Fin.succ (Fin.succ j))) = _
      rw [Equiv.swap_apply_of_ne_of_ne hne0 hne1]; rfl

/-- **The slot-0,1 antisymmetrization of `∇²Rm` on a rank-6 tuple is a curvature
action.**  This is `rm04_ricciIdentityAt` repackaged for an arbitrary `Fin 6`
tuple `W`: the difference of `∇²Rm` on `W` and on `W` with slots `0, 1` swapped is
the curvature action with derivative directions `W 0, W 1`. -/
theorem nabla2Rm04Field_slot01_antisym
    {D : DifferentialGeometry.Integral.Connection.RealTimeInterval}
    (S : SolutionOn (I := I) (M := M) D)
    (hS : IsSolutionOn (I := I) S)
    (t : DifferentialGeometry.Integral.Connection.RealTimeInterval.RegularTime D)
    (x₀ : M) (W : Fin 6 → TangentSpace I x₀) :
    nabla2Rm04Field (I := I) S (t : Real) x₀ W -
        nabla2Rm04Field (I := I) S (t : Real) x₀ (W ∘ Equiv.swap (0 : Fin 6) 1) =
      curvatureAction0SAt (I := I) (S.base.rm13 (t : Real)) (S.base.rm04 (t : Real) x₀)
        (W 0) (W 1) (fun q : Fin 4 => W (Fin.succ (Fin.succ q))) := by
  have hR := rm04_ricciIdentityAt (I := I) S hS t x₀
    (W 0) (W 1) (fun q : Fin 4 => W (Fin.succ (Fin.succ q)))
  rw [← fin6_eq_metricTraceInput (I := I) W,
    ← fin6_comp_swap_eq_metricTraceInput (I := I) W] at hR
  exact hR

/-! ## `C¹` differentiability of `∇²Rm` on the coordinate-frame slots

The `extDerivFun` part of the slot-swap commutation needs the scalar field
`y ↦ ∇²Rm(y)(frame slots)` to be `MDifferentiableAt x₀`.  The `∇²Rm` field is
`∞`-smooth and the coordinate-frame slots are `C¹` at `x₀`, so the evaluation is
`C¹` by `contMDiffAt_section_apply_one`. -/

/-- The scalar field `y ↦ ∇²Rm(y)` evaluated on the six coordinate-frame slot
fields is `MDifferentiableAt x₀`. -/
theorem nabla2Rm04Field_slotFields_mdifferentiableAt
    {D : DifferentialGeometry.Integral.Connection.RealTimeInterval}
    (S : SolutionOn (I := I) (M := M) D) (t : Real) (x₀ : M)
    (d₁ d₂ : CoordinateIdx (𝕜 := Real) E) (m : Fin 4 → CoordinateIdx (𝕜 := Real) E) :
    MDifferentiableAt I 𝓘(Real, Real)
      (fun p : M =>
        nabla2Rm04Field (I := I) S t p
          (fun q : Fin 6 => nabla3SlotFields (I := I) (coordinateFrameAt (I := I) x₀) d₁ d₂ m q p))
      x₀ := by
  classical
  set frame := coordinateFrameAt (I := I) x₀ with hframe_def
  set V : Fin 6 → (x : M) → TangentSpace I x :=
    nabla3SlotFields (I := I) frame d₁ d₂ m with hV_def
  -- `C¹` total-space smoothness of each coordinate-frame slot field.
  have hV_at : ∀ q : Fin 6,
      ContMDiffAt I (I.prod 𝓘(Real, E)) (1 : WithTop ℕ∞)
        (fun y : M =>
          (⟨y, V q y⟩ : TotalSpace E (TangentSpace I : M → Type _))) x₀ := by
    intro q
    have hbase : ∀ i : CoordinateIdx (𝕜 := Real) E,
        ContMDiffAt I (I.prod 𝓘(Real, E)) (1 : WithTop ℕ∞)
          (fun y : M =>
            (⟨y, frame i y⟩ : TotalSpace E (TangentSpace I : M → Type _))) x₀ :=
      fun i =>
        (coordinateFrameAt_isLocalFrame_one (I := I) x₀).contMDiffAt
          (coordinateFrameSet_open (I := I) x₀) (coordinateFrameAt_mem (I := I) x₀) i
    refine Fin.cases ?_ (fun q => ?_) q
    · simpa [hV_def, nabla3SlotFields] using hbase d₁
    · refine Fin.cases ?_ (fun q => ?_) q
      · simpa [hV_def, nabla3SlotFields] using hbase d₂
      · simpa [hV_def, nabla3SlotFields] using hbase (m q)
  -- `∇²Rm` is `∞`-smooth and the slots are `C¹`, so the evaluation is `C¹`.
  exact tensor0SField_eval_C1_slots_mdiffAt
    (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
    (nabla2Rm04Field (I := I) S t) V x₀ hV_at

/-! ## The Christoffel-correction-sum reindexing

The two `eval_C1_slots` correction sums (one for the `(b,c)` ordering, one for
`(c,b)`) are related by the transposition `σ = swap 0 1`.  The reindexing turns the
`(c,b)` correction sum into the `(b,c)` correction sum with each summand's slot
tuple post-composed with `σ`. -/

/-- **The Christoffel-correction-sum reindexing.**  For a rank-6 tensor value `α`,
slot data `S`, and derivative-correction values `D`, if the `(c,b)` slot/derivative
data is the `σ`-precomposition of the `(b,c)` data (`S' = S ∘ σ`, `D' = D ∘ σ`),
the `(c,b)` correction sum equals the `(b,c)` correction sum with each updated tuple
post-composed by `σ`.  Here `σ = swap 0 1`, and `S` updated at `q` to `D q`,
composed with `σ`, is the slot-swapped corrected tuple. -/
theorem correction_sum_swap_reindex {x₀ : M}
    (α : Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) 6 x₀)
    (S : Fin 6 → TangentSpace I x₀) (D : Fin 6 → TangentSpace I x₀) :
    (∑ q : Fin 6,
        α (Function.update (fun r : Fin 6 => S (Equiv.swap (0 : Fin 6) 1 r)) q
          (D (Equiv.swap (0 : Fin 6) 1 q)))) =
      ∑ q : Fin 6,
        α (Function.update S q (D q) ∘ Equiv.swap (0 : Fin 6) 1) := by
  classical
  set σ : Equiv.Perm (Fin 6) := Equiv.swap (0 : Fin 6) 1 with hσ
  -- Reindex the summation `q ↦ σ q`.
  rw [← Equiv.sum_comp σ
        (fun q : Fin 6 =>
          α (Function.update (fun r : Fin 6 => S (σ r)) q (D (σ q))))]
  refine Finset.sum_congr rfl fun q _ => ?_
  -- After reindexing the summand index is `σ q`; `σ` is involutive so `σ (σ q) = q`.
  have hσσ : σ (σ q) = q := by rw [hσ]; exact Equiv.swap_apply_self _ _ q
  rw [hσσ]
  -- `update (S ∘ σ) (σ q) (D q) = (update S q (D q)) ∘ σ` by injectivity of `σ`.
  congr 1
  have hinj : Function.Injective σ := σ.injective
  have hupd :
      Function.update S (σ (σ q)) (D q) ∘ σ =
        Function.update (S ∘ σ) (σ q) (D q) :=
    Function.update_comp_eq_of_injective S hinj (σ q) (D q)
  rw [hσσ] at hupd
  exact hupd.symm

/-! ## The slot-swap/∇ commutation for `T₁`

Assembling the pieces: applying the concrete expansion `nabla3Rm04Field_eval_expand`
to both `nabla3(a,b,c,m)` and `nabla3(a,c,b,m)`, the difference `T₁` is the
covariant derivative `∇_a` of the curvature-action field `K = [∇_b, ∇_c] Rm`, in
the concrete tensorial-derivation-rule form: the `extDerivFun` of the scalar
curvature-action field minus the Christoffel correction in each `∇²Rm` slot (each
correction itself a curvature action via `rm04_ricciIdentityAt`). -/

/-- The Christoffel-corrected slot tuple for the `q`-th term of the outer `∇_a`
step: the `(b,c)`-ordered slot tuple at `x₀` with slot `q` replaced by the
covariant derivative of the `q`-th slot field along `frame a`. -/
def nabla3CorrectedSlots
    {D : DifferentialGeometry.Integral.Connection.RealTimeInterval}
    (S : SolutionOn (I := I) (M := M) D) (t : Real) (x₀ : M)
    (a b c : CoordinateIdx (𝕜 := Real) E) (m : Fin 4 → CoordinateIdx (𝕜 := Real) E)
    (q : Fin 6) : Fin 6 → TangentSpace I x₀ :=
  Function.update
    (fun r : Fin 6 => nabla3SlotFields (I := I) (coordinateFrameAt (I := I) x₀) b c m r x₀) q
    ((S.family.connection t
        (nabla3SlotFields (I := I) (coordinateFrameAt (I := I) x₀) b c m q) x₀)
      (coordinateFrameAt (I := I) x₀ a x₀))

/-- **The slot-swap/∇ commutation for `T₁` (the concrete route).**

At the chart centre `x₀`, for a Ricci-flow solution at a regular time, the first
reaction summand `T₁ = ∇³Rm(a,b,c,m) − ∇³Rm(a,c,b,m)` of
`Evolution/NablaRiemannCommutator.lean` equals the covariant derivative `∇_a` of
the curvature-action field `K(y) := [∇_b, ∇_c] Rm = curvatureAction0SAt (rm13 y)
(Rm04 y) b c m`, expressed in the explicit tensorial-derivation-rule form: the
directional derivative of the scalar curvature-action field along `frame a`, minus
the curvature action on each of the six `∇²Rm`-slot Christoffel corrections.

Derived **purely from the concrete evaluation formula** `eval_C1_slots` together
with the pointwise `(0,4)` Ricci identity `rm04_ricciIdentityAt` and the
elementary `Equiv.swap`/`Function.update` reindexing of the correction sum — **no**
abstract `domDomCongr`/∇-commutation. -/
theorem nablaLapComm_T1_eq_covDeriv_curvatureAction
    {D : DifferentialGeometry.Integral.Connection.RealTimeInterval}
    (S : SolutionOn (I := I) (M := M) D)
    (hS : IsSolutionOn (I := I) S)
    (t : DifferentialGeometry.Integral.Connection.RealTimeInterval.RegularTime D)
    (x₀ : M)
    (a b c : CoordinateIdx (𝕜 := Real) E) (m : Fin 4 → CoordinateIdx (𝕜 := Real) E) :
    nabla3Rm04Field (I := I) S (t : Real) x₀
        (nabla3FrameTuple (I := I) (coordinateFrameAt (I := I) x₀) x₀ a b c m) -
      nabla3Rm04Field (I := I) S (t : Real) x₀
        (nabla3FrameTuple (I := I) (coordinateFrameAt (I := I) x₀) x₀ a c b m) =
      extDerivFun (I := I)
          (fun p : M =>
            curvatureAction0SAt (I := I) (S.base.rm13 (t : Real))
              (S.base.rm04 (t : Real) p)
              (coordinateFrameAt (I := I) x₀ b p) (coordinateFrameAt (I := I) x₀ c p)
              (frameTuple (I := I) (coordinateFrameAt (I := I) x₀) p m))
          x₀ (coordinateFrameAt (I := I) x₀ a x₀) -
        ∑ q : Fin 6,
          curvatureAction0SAt (I := I) (S.base.rm13 (t : Real)) (S.base.rm04 (t : Real) x₀)
            (nabla3CorrectedSlots (I := I) S (t : Real) x₀ a b c m q 0)
            (nabla3CorrectedSlots (I := I) S (t : Real) x₀ a b c m q 1)
            (fun r : Fin 4 =>
              nabla3CorrectedSlots (I := I) S (t : Real) x₀ a b c m q (Fin.succ (Fin.succ r))) := by
  classical
  set frame := coordinateFrameAt (I := I) x₀ with hframe_def
  -- Abbreviations for the two slot-field tuples at `x₀`.
  set Sbc : Fin 6 → TangentSpace I x₀ :=
    fun r : Fin 6 => nabla3SlotFields (I := I) frame b c m r x₀ with hSbc_def
  -- Expand both `∇³Rm` values through the concrete tensorial derivation rule.
  rw [nabla3Rm04Field_eval_expand (I := I) S (t : Real) x₀ a b c m,
    nabla3Rm04Field_eval_expand (I := I) S (t : Real) x₀ a c b m]
  -- Group as `(extDeriv b c − extDeriv c b) − (corr b c − corr c b)`.
  rw [show
    ∀ Ebc Ecb Cbc Ccb : Real, (Ebc - Cbc) - (Ecb - Ccb) = (Ebc - Ecb) - (Cbc - Ccb)
    from fun _ _ _ _ => by ring]
  congr 1
  · -- **Piece A: the `extDerivFun` difference is the `extDerivFun` of `K`.**
    rw [← extDerivFun_sub_at (I := I) (frame a x₀)
      (nabla2Rm04Field_slotFields_mdifferentiableAt (I := I) S (t : Real) x₀ b c m)
      (nabla2Rm04Field_slotFields_mdifferentiableAt (I := I) S (t : Real) x₀ c b m)]
    -- The inner field difference is the curvature-action field, pointwise.
    rw [nabla2Rm04Field_antisym_eq_curvatureAction_field (I := I) S hS t x₀ b c m]
  · -- **Piece B: the correction-sum difference is the curvature-action sum.**
    -- Rewrite the `(c,b)` correction sum via the slot-field swap and reindexing.
    -- Step 1: rewrite each `(c,b)` summand into the `correction_sum_swap_reindex` LHS shape,
    -- by replacing the `(c,b)` slot field with the `σ`-precomposed `(b,c)` slot field.
    have hStep1 :
        (∑ q : Fin 6,
            nabla2Rm04Field (I := I) S (t : Real) x₀
              (Function.update
                (fun r : Fin 6 => nabla3SlotFields (I := I) frame c b m r x₀) q
                ((S.family.connection (t : Real)
                    (nabla3SlotFields (I := I) frame c b m q) x₀) (frame a x₀)))) =
          ∑ q : Fin 6,
            nabla2Rm04Field (I := I) S (t : Real) x₀
              (Function.update (fun r : Fin 6 => Sbc (Equiv.swap (0 : Fin 6) 1 r)) q
                ((S.family.connection (t : Real)
                    (nabla3SlotFields (I := I) frame b c m (Equiv.swap (0 : Fin 6) 1 q)) x₀)
                  (frame a x₀))) := by
      simp only [nabla3SlotFields_swap (I := I) frame b c m, hSbc_def]
    -- Step 2: apply the reindexing lemma.
    rw [hStep1, correction_sum_swap_reindex (I := I)
      (nabla2Rm04Field (I := I) S (t : Real) x₀) Sbc
      (fun q : Fin 6 =>
        (S.family.connection (t : Real)
          (nabla3SlotFields (I := I) frame b c m q) x₀) (frame a x₀))]
    -- Now each paired difference is a slot-0,1 curvature action.
    rw [← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun q _ => ?_
    -- `corr_bc(q) − corr_cb(q) = nabla2(W_q) − nabla2(W_q ∘ σ) = curvatureAction(...)`.
    have hW := nabla2Rm04Field_slot01_antisym (I := I) S hS t x₀
      (nabla3CorrectedSlots (I := I) S (t : Real) x₀ a b c m q)
    simp only [nabla3CorrectedSlots, hframe_def, hSbc_def] at hW ⊢
    exact hW

/-! ## The full reaction term in separated curvature-action form

Combining the slot-swap/∇ commutation `nablaLapComm_T1_eq_covDeriv_curvatureAction`
(for the `T₁` summand) with the *definition* of `nablaLapCommReactionTerm` (whose
`T₂` summand is already a `curvatureAction0SAt` on `∇Rm`), the whole reaction term
is exhibited as the operator-identity sum

`nablaLapCommReactionTerm = ∇_a([∇_b,∇_c]Rm) + [∇_a,∇_c](∇_b Rm)`,

with `∇_a([∇_b,∇_c]Rm)` in the explicit `eval_C1_slots` form (an `extDerivFun` of
the scalar `(b,c)` curvature-action field minus the six `∇²Rm`-slot Christoffel
corrections, each itself a curvature action) and `[∇_a,∇_c](∇_b Rm)` the bare
`(0,5)` curvature action on `∇Rm`.  This is the single machine-checked statement
of the `Rm ∗ ∇Rm` reaction in its separated curvature-action form, and is the
exact object whose *quantitative* bound is recorded as the wall below. -/

/-- **The full reaction term as `∇(Rm ∗ Rm) + Rm ∗ ∇Rm`.**  At the chart centre
`x₀`, for a Ricci-flow solution at a regular time, the `k = 1` curvature reaction
`nablaLapCommReactionTerm a b c m` equals the sum of

* `∇_a([∇_b,∇_c]Rm)` — the covariant derivative of the `(b,c)` curvature
  commutator on `Rm`, in the explicit tensorial-derivation-rule form (the
  `extDerivFun` of the scalar curvature-action field along `frame a`, minus the
  curvature action on each of the six `∇²Rm`-slot Christoffel corrections), and
* `[∇_a,∇_c](∇_b Rm)` — the `(0,5)` curvature action on `∇Rm`.

This is `nablaLapComm_T1_eq_covDeriv_curvatureAction` (the `T₁` half) added to the
unchanged `T₂` half of the definition, so the whole reaction is exhibited as the
operator-identity sum `∇(Rm ∗ Rm) + Rm ∗ ∇Rm`.  Sorry-free, derived purely from
the concrete evaluation formula `eval_C1_slots` and the pointwise Ricci
identities. -/
theorem nablaLapCommReactionTerm_eq_covDeriv_curvatureAction_add_curvatureAction
    {D : DifferentialGeometry.Integral.Connection.RealTimeInterval}
    (S : SolutionOn (I := I) (M := M) D)
    (hS : IsSolutionOn (I := I) S)
    (t : DifferentialGeometry.Integral.Connection.RealTimeInterval.RegularTime D)
    (x₀ : M)
    (a b c : CoordinateIdx (𝕜 := Real) E) (m : Fin 4 → CoordinateIdx (𝕜 := Real) E) :
    nablaLapCommReactionTerm (I := I) S (t : Real) x₀ a b c m =
      (extDerivFun (I := I)
            (fun p : M =>
              curvatureAction0SAt (I := I) (S.base.rm13 (t : Real))
                (S.base.rm04 (t : Real) p)
                (coordinateFrameAt (I := I) x₀ b p) (coordinateFrameAt (I := I) x₀ c p)
                (frameTuple (I := I) (coordinateFrameAt (I := I) x₀) p m))
            x₀ (coordinateFrameAt (I := I) x₀ a x₀) -
          ∑ q : Fin 6,
            curvatureAction0SAt (I := I) (S.base.rm13 (t : Real)) (S.base.rm04 (t : Real) x₀)
              (nabla3CorrectedSlots (I := I) S (t : Real) x₀ a b c m q 0)
              (nabla3CorrectedSlots (I := I) S (t : Real) x₀ a b c m q 1)
              (fun r : Fin 4 =>
                nabla3CorrectedSlots (I := I) S (t : Real) x₀ a b c m q (Fin.succ (Fin.succ r)))) +
        curvatureAction0SAt (I := I) (S.base.rm13 (t : Real))
          (nablaRm04Field (I := I) S (t : Real) x₀)
          (coordinateFrameAt (I := I) x₀ a x₀) (coordinateFrameAt (I := I) x₀ c x₀)
          (nabla3InnerSlots (I := I) (coordinateFrameAt (I := I) x₀) x₀ b m) := by
  rw [nablaLapCommReactionTerm]
  rw [nablaLapComm_T1_eq_covDeriv_curvatureAction (I := I) S hS t x₀ a b c m]

/-! ## Produced shape and the exact bound obstruction

**Produced (sorry-free, from the concrete evaluation formula, no axiomatized
commutator or Leibniz).**  At the chart centre `x₀`, for a Ricci-flow solution at
a regular time:

* `nablaLapComm_T1_eq_covDeriv_curvatureAction` :
  `T₁ = ∇³Rm(a,b,c,m) − ∇³Rm(a,c,b,m) = ∇_a K`, the covariant derivative of the
  curvature-action field `K(y) = [∇_b, ∇_c] Rm = curvatureAction0SAt (rm13 y)
  (Rm04 y) b c m`, in the explicit `eval_C1_slots` form
  `extDerivFun (K) x₀ (frame a) − Σ_{q} curvatureAction0SAt (rm13 x₀)(Rm04 x₀)
  (Wq 0)(Wq 1)(tail Wq)`, `Wq = nabla3CorrectedSlots …`.

  This **is** the slot-swap/∇ commutation the original `NablaRiemannCommutator.lean`
  footer flagged as the wall and the prior agent declared blocked at the field
  level.  It is derived here entirely from the **concrete** evaluation formula:

  - `nabla3Rm04Field_eval_expand` — the `eval_C1_slots` (Definition 14.5) expansion
    of each `∇³Rm` value into `extDerivFun` minus Christoffel corrections;
  - `nabla2Rm04Field_antisym_eq_curvatureAction_field` — the `extDerivFun` part,
    via `extDerivFun_sub_at` and the **pointwise** `(0,4)` Ricci identity
    `rm04_ricciIdentityAt` (at every point of the field);
  - `correction_sum_swap_reindex` + `nabla2Rm04Field_slot01_antisym` — the
    Christoffel-correction part, via the elementary `Equiv.swap` / `Function.update`
    reindexing of the correction sum and `rm04_ricciIdentityAt` at `x₀`.

  The `MDifferentiableAt` needed by `extDerivFun_sub_at` is discharged by
  `nabla2Rm04Field_slotFields_mdifferentiableAt` (an `∞`-smooth tensor on `C¹`
  coordinate-frame slots is `C¹`, `tensor0SField_eval_C1_slots_mdiffAt`).

**The exact bound obstruction (the genuine decision point of the task).**  The
task's target was `|T₁| ≤ C(dim)·|Rm|·|∇Rm|`.  With `T₁ = ∇_a K` and `K = Rm ∗ Rm`
the curvature action, this is the true statement `|∇(Rm ∗ Rm)| ≤ C·|Rm|·|∇Rm|`.
Completing it in Lean is blocked, and **not** for the reason the task anticipated.

* The components of `∇_a K` produced above are `extDerivFun(curvatureAction)`
  (an **ordinary chart derivative** of the `rm13`-contraction) and curvature
  actions on Christoffel-corrected slots (`Wq` contains `(∇ frame_q) a`, an
  unbounded Christoffel symbol).  *Neither summand* is bounded by `|Rm|·|∇Rm|`;
  only their specific combination — the covariant derivative — is.

* To expose the `|Rm|·|∇Rm|` bound one needs the covariant Leibniz rule
  `∇(Rm ∗ Rm) = ∇Rm ∗ Rm + Rm ∗ ∇Rm` for **this** `rm13`-contraction
  (`curvatureAction0SAt (rm13 ·) (Rm04 ·)`).  Differentiating that contraction
  covariantly produces `∇(rm13) ∗ Rm04 + rm13 ∗ ∇(Rm04)`.  Here `∇(Rm04) =
  nablaRm04Field` is bounded by `|∇Rm|`, but `∇(rm13)` is the covariant derivative
  of the **(1,3)** tensor `rm13` (one index already raised by `g⁻¹`), a different
  object from `nablaRm04Field`.

* Identifying `∇(rm13)` with `∇(Rm04)` requires the metric raising `g⁻¹` to commute
  with `∇`, i.e. `∇ g⁻¹ = 0`.  The task proposed working at the chart centre where
  `g(x₀) = δ` makes the raising trivial — **but this is false for the frame in
  play**: `coordinateFrameAt x₀` is the *chart coordinate frame* (see
  `Geometry/Coordinates/CoordinateFrame.lean`, which states it is "weaker than
  normal coordinates … it does not assert Christoffel symbols vanish"), and the
  producer's orthonormality `InverseMetricOrthonormalAt` is **always** carried as a
  separate hypothesis and is *never* discharged for `coordinateFrameAt`.  So the
  raising cannot be trivialized at the centre.

* Even granting `∇ g⁻¹ = 0`, the tree has **no** infrastructure to state, let alone
  bound, `∇(rm13)`: there is no `totalNablaRS`/realization for `rm13` in the
  solution context and no `Tensor13` component-norm (searched: `CurvatureAction.lean`,
  `RmRealizationBridge.lean`, `NablaRiemannHeat.lean`, the `RicciIdentity`/
  `CovGradRoughLap` namespaces).  There is likewise no `∇(curvatureAction)` /
  `∇(Rm ∗ Rm)` Leibniz lemma anywhere.

**Conclusion.**  The slot-swap/∇ commutation (`T₁ = ∇_a (Rm ∗ Rm)`) is now proved
concretely and sorry-free.  The remaining bound reduces to the covariant Leibniz
`∇(Rm ∗ Rm) = ∇Rm ∗ Rm + Rm ∗ ∇Rm` for the `rm13`-contraction together with
`∇(rm13) ↔ ∇(Rm04)` (metric-raising/∇ commutation); both are genuinely absent from
the tree, and the proposed centre-orthonormality shortcut does not apply to the
chart coordinate frame.  This is the precise point at which the concrete route
reaches the bound, recorded per the task's stop condition.

## Third-attempt addendum: the `rm04`-contraction route, evaluated step by step

The third attempt was directed to the **`rm04`-contraction route**: build a
covariant contraction Leibniz `∇(contract(A,B)) = contract(∇A,B)+contract(A,∇B)`
from the concrete `eval_smooth_slots` formula, supported by (1) `∇g⁻¹ = 0` derived
from `∇g = 0`, and (2) `rm13 = raise(rm04)`, so that `∇rm13 = raise(∇rm04)` with no
`(1,3)` `totalNablaRS`.  Each named support was checked against the tree and is
**not assemblable here**, for reasons specific to this route:

1. **`∇g⁻¹ = 0` is not statable in the realization framework.**  `nabla_metric_zero`
   (`Tensor/RSTensor/MetricCompatibility.lean`) is `∇ = 0` for the metric *as a
   `(0,2)` tensor field* `metricTensorField`.  The inverse metric in this codebase
   is `InverseMetricComponents M Idx := M → Idx → Idx → ℝ` (`Curvature/Basic.lean`),
   a **frame-component function**, not a bundled `(2,0)` tensor field; and there is
   no `(2,0)`/`(r,0)` `totalNabla` realization in the solution context to express
   its covariant derivative.  So `∇g⁻¹ = 0` cannot even be *phrased* on the
   `totalNabla0S`/`SolutionOn` side, let alone derived by differentiating `g·g⁻¹=I`.

2. **`rm13 = raise(rm04)` is not available as a usable field-level lemma.**  In the
   solution context `S.base.rm13 = metricRm13 (g t) = rm13Section(cov)` and
   `S.base.rm04 = metricRm04 (g t) = rm04Section(g, cov)` are produced *independently*
   (`Curvature/Metric.lean`); their relationship is only the two *realization
   predicates* `Rm13RealizesConnection` / `Rm04RealizesConnection` (which separately
   say `rm13(ω)(X,Y,Z)=ω(R(X,Y)Z)` and `rm04(X,Y,Z,W)=g(W,R(X,Y)Z)`), not a tensor
   equation `rm13 = raise rm04`.  The genuine index-raising equivalence
   (`lowerAllUpperIndicesEquiv`, `Connection/MetricCompatibility/TensorLoweringParallel.lean`)
   and its ∇-parallelism live in a **different** covariant-derivative formalism
   (`tensorRSCovariantDerivative`/`tensor0SCovariantDerivative`), and the parallelism
   theorem `loweredCovDerivAt_eq_lower_tensorCovDerivAt` is proved only at
   `(r,s)=(0,2)`, never for the `(1,3)` rank of `rm13`.  Bridging that formalism to
   the `totalNabla0S` solution machinery is itself the `RmRealizationBridge`-style
   frontier, not a lemma to cite.

3. **The contraction Leibniz, even if built generically, would still need `∇rm13`.**
   `curvatureAction0SAt (rm13 ·) (Rm04 ·)` is a contraction of the `(1,3)` field
   `rm13` against the `(0,4)` field `Rm04`; differentiating it covariantly produces
   `∇rm13 ∗ Rm04 + rm13 ∗ ∇Rm04`.  As confirmed by search, there is **no**
   `nablaRm13Field` / `TotalNablaRSRealizes` for `S.base.rm13` anywhere in the tree
   (the only `totalNabla*` realizations for solution curvature are the lowered
   `nablaRm04Field`/`nabla2Rm04Field`/`nabla3Rm04Field` of `RmRealizationBridge.lean`).
   Without step 2 collapsing `∇rm13` to `raise(∇rm04)`, the `∇rm13` factor is a
   genuinely undefined object in this context.

4. **Frame mismatch makes the target inequality ill-posed as stated.**
   `nablaLapCommReactionTerm` is hardwired to the **chart coordinate frame**
   `coordinateFrameAt x₀`, which is *not* orthonormal at its centre.  The target
   norms `rm04NormSqInFrame` / `nablaRm04NormSqInFrame` (`RiemannNorm.lean`,
   `RiemannNormHeatProducer.lean`) are defined for a *general* frame carrying an
   `InverseMetricOrthonormalAt` hypothesis (`gᵃᵇ = δ`), which the coordinate frame
   never satisfies.  Consequently even the genuinely reachable, Leibniz-free
   **operator-norm** bound of the `T₂` half — `|curvatureAction0SAt rm13 (∇Rm) …| ≤
   ‖rm13 x₀‖ · ‖∇Rm x₀‖ · ∏‖frame‖` via `tensorRSSpace_norm_apply_le` +
   `ContinuousMultilinearMap.le_opNorm` — produces *fiber* norms `‖rm13 x₀‖`,
   `‖∇Rm x₀‖` and uncontrolled coordinate-frame-vector / musical-isomorphism factors,
   none of which is `C(dim)·√(rm04NormSqInFrame)·√(nablaRm04NormSqInFrame)`.  Matching
   the requested shape additionally requires a fiber-norm ↔ component-norm bridge in
   an orthonormal frame (`Curvature/FiberNormParseval/*`) *and* a coordinate→orthonormal
   frame change — neither of which is "bounding `nablaLapCommReactionTerm`."

**What was added on this attempt.**  The single machine-checked
`nablaLapCommReactionTerm_eq_covDeriv_curvatureAction_add_curvatureAction`, exhibiting
the whole reaction as the separated operator-identity sum
`∇_a([∇_b,∇_c]Rm) + [∇_a,∇_c](∇_b Rm)` (i.e. `∇(Rm ∗ Rm) + Rm ∗ ∇Rm`), with the
first summand in explicit `eval_C1_slots` form and the second the bare `(0,5)`
curvature action.  This pins the wall to one named object and is the cleanest true
statement reachable without the four missing subsystems above.  Per the task's stop
condition (after three attempts, a precise final wall is the deliverable), the
`rm04`-contraction route is reported as not assemblable in the current tree at the
four points itemised here. -/

end DifferentialGeometry.PDE.RicciFlow
