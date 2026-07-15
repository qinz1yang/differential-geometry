import DifferentialGeometry.Geometry.Flow.RicciFlow.Evolution.NablaRiemannReactionBound
import DifferentialGeometry.Geometry.Flow.RicciFlow.Evolution.NablaRiemannHeatSolution

set_option autoImplicit false
set_option linter.style.longLine false
set_option linter.unusedSectionVars false
set_option linter.unusedFintypeInType false
set_option linter.unusedDecidableInType false

/-!
# Frame invariance of the `k = 1` orthonormal component norms, and the
intrinsic-norm restatement of the spatial commutator bound

This file closes the **norm frame-invariance** half of WALL 2 (the frame
reconciliation) for the `k = 1` Bernstein–Bando–Shi producer, via Route (b) of
`Evolution/IteratedNablaRmTower.md`'s twelfth follow-up.

## The problem this addresses

The quantitative spatial reaction bound
`abs_spatialCommNablaRm_orthoFrame_le` (`Evolution/NablaRiemannReactionBound.lean`)
is stated in a **`g(t)`-orthonormal frame**, with the `Rm`/`∇Rm` factors carried
by the *frame-component* norms `rm04NormSqInFrame Rm04 δ frame` /
`nablaRm04NormSqInFrame … δ`.  These are the plain orthonormal-component squared
sums; *a priori* they look frame-dependent (they mention the chosen `frame`).

The `horth`-free scalar producer
(`nablaRm04NormHeatBoundOn_scalar`, `Evolution/NablaRiemannHeatSolution.lean`) on
the other hand consumes a **frame-independent scalar** reaction bound
`reaction ≤ cReact · √v · u` for *intrinsic* scalar fields `u = |∇Rm|²`,
`v = |Rm|²`.

The bridge between them is the observation that, in **any** `g`-orthonormal frame,
the plain component squared sum **equals the intrinsic metric fibre norm**
`normSq0S` (`Tensor/RSTensor/FiberMetric/Tensor0SMetric.lean`), which mentions no
frame at all.  This is exactly the Route (b) condition the twelfth follow-up named
("if `multiNormRaised gInv = (intrinsic)` holds frame-independently, the
orthonormal bound transfers directly"): here `multiNormRaised δ A = compNormSqMulti A`
(`multiNormInFrame_eq_compNormSqMulti`, `Evolution/IteratedNablaRmTower.lean`) and
`compNormSqMulti` of the orthonormal components `= normSq0S` (this file's
`compNormSqMulti_orthoBasis_eq_normSq0S`), so the orthonormal-component norm is the
intrinsic fibre norm, **independent of which orthonormal frame is used**.

## What this file produces

* `metricInverseInBasis_identity_of_orthonormal` — a `g`-orthonormal basis has the
  Kronecker-delta inverse metric in the `MetricInverseInBasis_gen` sense (the
  hypothesis `normSq0S_identity_eq_sum_sq` consumes).
* `compNormSqMulti_orthoBasis_eq_normSq0S` — **the norm frame-invariance bridge**:
  for a `g`-orthonormal basis, `compNormSqMulti (orthonormal components of A) =
  normSq0S g x s A`, the intrinsic fibre norm (rank-uniform, any `(0,s)` tensor).
* `rm04NormSqInFrame_orthoBasis_eq_normSq0S` /
  `nablaRm04NormSqInFrame_orthoBasis_eq_normSq0S` — the specialisations to the
  producer's `rm04NormSqInFrame`/`nablaRm04NormSqInFrame` (with the genuine
  Kronecker-delta inverse metric), equating them to the intrinsic
  `normSq0S g 4 Rm04` (`= |Rm|²`) and `normSq0S g 5 (∇Rm)` (`= |∇Rm|²`).
* `abs_spatialCommNablaRm_intrinsic_le` — **the frame-independent restatement of
  the proven spatial commutator bound**: the spatial commutator
  `Δ(∇Rm)(c) − ∇(ΔRm)(c)` is bounded by `13·card²·√(|Rm|²)·√(|∇Rm|²)` with the
  `Rm`/`∇Rm` factors carried by the **intrinsic** fibre norms `normSq0S g · Rm` /
  `normSq0S g · (∇Rm)`, i.e. genuinely frame-independent scalars — the exact shape
  the `horth`-free producer's reaction-bound input needs (modulo the remaining
  intrinsic-norm time-derivative half, recorded in the footer).

## Honesty

This is **only** the frame-invariance / norm-identification half of Route (b).  It
does **not** by itself close the full `k = 1` producer from a bare `SolutionOn`:
the remaining gap is the *intrinsic-norm time derivative* `∂ₜ|∇Rm|²` (the temporal
half of the heat residual `(∂ₜ − Δ)∇Rm`, which involves `∂ₜΓ ∗ Rm` and the
Uhlenbeck `∂ₜRm`, and the moving metric `g(t)` inside `normSq0S`).  See the file
footer for the precise remaining frontier.

`#print axioms` for every public theorem is `[propext, Classical.choice, Quot.sound]`.
-/

noncomputable section

namespace DifferentialGeometry.PDE.RicciFlow

open Bundle Tensor0SBundle
open DifferentialGeometry.Tensor.Coordinates
open DifferentialGeometry.Integral.Connection
open scoped Manifold ContDiff BigOperators

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace Real E]
variable [Module.Finite Real E] [FiniteDimensional Real E] [InnerProductSpace Real E]
variable {H : Type*} [TopologicalSpace H]
variable {I : ModelWithCorners Real E H} [I.Boundaryless]
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
variable [IsManifold I 1 M] [IsManifold I 2 M]
variable [IsManifold I ((∞ : WithTop ℕ∞) + 1) M]
variable [CompleteSpace E] [SigmaCompactSpace M] [T2Space M]

/-! ## The norm frame-invariance bridge

The plain orthonormal-component squared sum `compNormSqMulti` of a `(0,s)` tensor
equals the metric-induced fibre norm `normSq0S`, which mentions no frame.  The key
input is that a `g`-orthonormal basis carries the Kronecker-delta inverse metric in
the `MetricInverseInBasis_gen` sense. -/

section FrameInvariance

variable {Idx : Type*} [Fintype Idx] [DecidableEq Idx]

/-- A `g`-orthonormal basis has the **Kronecker-delta inverse metric** in the
`MetricInverseInBasis_gen` sense: with `gᵢⱼ = δᵢⱼ`, the identity components
`identityInvMetric` are a genuine two-sided inverse of the Gram matrix.  This is the
inline computation of `cotangentSharp_orthoBasis_expand'`
(`Evolution/NablaRiemannReactionBound.lean`), extracted as a reusable lemma. -/
theorem metricInverseInBasis_identity_of_orthonormal
    (g : SmoothMetric_gen I M) {x : M}
    (basis : Module.Basis Idx Real (TangentSpace I x))
    (horth : ∀ i j : Idx,
      g.inner x (basis i) (basis j) = if i = j then (1 : Real) else 0) :
    MetricInverseInBasis_gen (I := I) g x basis (identityInvMetric (Idx := Idx)) := by
  classical
  intro i j
  refine ⟨?_, ?_⟩
  · -- `∑ₖ δᵢₖ · g(eₖ, eⱼ) = g(eᵢ, eⱼ) = δᵢⱼ`.
    rw [Finset.sum_eq_single i]
    · rw [identityInvMetric_apply_self, one_mul]; exact horth i j
    · intro k _ hk
      rw [identityInvMetric, diagonalInvMetric_eq_zero_of_ne (fun h => hk h.symm), zero_mul]
    · intro h; exact absurd (Finset.mem_univ i) h
  · -- `∑ₖ g(eᵢ, eₖ) · δₖⱼ = g(eᵢ, eⱼ) = δᵢⱼ`.
    rw [Finset.sum_eq_single j]
    · rw [identityInvMetric_apply_self, mul_one]; exact horth i j
    · intro k _ hk
      rw [identityInvMetric, diagonalInvMetric_eq_zero_of_ne hk, mul_zero]
    · intro h; exact absurd (Finset.mem_univ j) h

/-- **The norm frame-invariance bridge.**  For a `g`-orthonormal basis, the plain
orthonormal-component squared sum `compNormSqMulti` of a `(0,s)` tensor `A` equals
the intrinsic metric fibre norm `normSq0S g x s A`:

`∑_{idx} (A (basis ∘ idx))² = normSq0S g x s A`.

The right-hand side mentions **no** frame, so the left-hand side is the same for
*every* `g`-orthonormal basis — the norm frame-invariance that lets the
orthonormal-frame reaction bound transfer to a frame-independent scalar bound
(Route (b) of `Evolution/IteratedNablaRmTower.md`'s twelfth follow-up).  Combined
with `multiNormInFrame_eq_compNormSqMulti` (`multiNormRaised δ A = compNormSqMulti A`)
this shows the `δ`-raised component norm is the intrinsic fibre norm. -/
theorem compNormSqMulti_orthoBasis_eq_normSq0S
    (g : SmoothMetric_gen I M) {x : M} {s : ℕ}
    (basis : Module.Basis Idx Real (TangentSpace I x))
    (horth : ∀ i j : Idx,
      g.inner x (basis i) (basis j) = if i = j then (1 : Real) else 0)
    (A : Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) s x) :
    compNormSqMulti (fun idx : Fin s → Idx => A (fun p => basis (idx p))) =
      normSq0S (I := I) g x s A := by
  classical
  rw [normSq0S_identity_eq_sum_sq (I := I) g x s basis
    (metricInverseInBasis_identity_of_orthonormal (I := I) g basis horth) A]
  unfold compNormSqMulti
  refine Finset.sum_congr rfl fun idx _ => ?_
  -- `component0S basis A idx = A (basis ∘ idx)`, definitionally.
  rfl

end FrameInvariance

/-! ## Specialisation to the producer's `Rm`/`∇Rm` frame norms

The reaction bound `abs_spatialCommNablaRm_orthoFrame_le` carries its `Rm`/`∇Rm`
factors through `rm04NormSqInFrame Rm04 δ frame` and `nablaRm04NormSqInFrame … δ`.
Via the orthonormal reductions `rm04NormSqInFrame_eq_compNormSq4` /
`nablaRm04NormSqInFrame_eq_compNormSq5` and the multi-index reindexings, these are
the `compNormSqMulti` of the frame components, hence (by the bridge above) the
intrinsic `normSq0S`. -/

section ProducerNorms

variable {n : ℕ}

/-- The producer's `Rm`-factor norm `rm04NormSqInFrame Rm04 δ frame` equals the
intrinsic fibre norm `normSq0S g 4 (Rm04 x₀)` in a `g`-orthonormal frame whose
centre values are `basis`.  (`Rm` factor of `abs_spatialCommNablaRm_orthoFrame_le`,
re-expressed frame-independently.) -/
theorem rm04NormSqInFrame_orthoBasis_eq_normSq0S
    {D : DifferentialGeometry.Integral.Connection.RealTimeInterval}
    (S : SolutionOn (I := I) (M := M) D)
    (t : DifferentialGeometry.Integral.Connection.RealTimeInterval.RegularTime D)
    (x₀ : M)
    (frame : Fin n → (x : M) → TangentSpace I x)
    (basis : Module.Basis (Fin n) Real (TangentSpace I x₀))
    (hframe : ∀ i : Fin n, frame i x₀ = basis i)
    (horth : ∀ i j : Fin n,
      (S.base.metric (t : Real)).inner x₀ (basis i) (basis j) =
        if i = j then (1 : Real) else 0) :
    rm04NormSqInFrame (I := I) (fun s => S.base.rm04 s)
        (deltaInvMetric (M := M)) frame (t : Real) x₀ =
      normSq0S (I := I) (S.base.metric (t : Real)) x₀ 4 (S.base.rm04 (t : Real) x₀) := by
  classical
  -- The δ-raised frame norm is `compNormSq4` of the frame components.
  rw [rm04NormSqInFrame_eq_compNormSq4 (I := I) (fun s => S.base.rm04 s)
    (deltaInvMetric (M := M)) frame (t : Real) x₀
    (deltaInvMetric_orthonormal (M := M) (t : Real) x₀)]
  -- `compNormSq4` of the frame components equals `compNormSqMulti` of the basis
  -- components (reindexing `Fin 4 → Fin n`), then the bridge gives `normSq0S`.
  rw [← compNormSqMulti_orthoBasis_eq_normSq0S (I := I) (S.base.metric (t : Real))
    basis horth (S.base.rm04 (t : Real) x₀)]
  rw [compNormSqMulti_eq_compNormSq4_basis (I := I) (S.base.rm04 (t : Real) x₀) basis]
  refine Finset.sum_congr rfl fun i _ => ?_
  refine Finset.sum_congr rfl fun j _ => ?_
  refine Finset.sum_congr rfl fun k _ => ?_
  refine Finset.sum_congr rfl fun l _ => ?_
  simp only [DifferentialGeometry.Integral.Connection.rm04Comp]
  rw [hframe i, hframe j, hframe k, hframe l]

/-- The producer's `∇Rm`-factor norm `nablaRm04NormSqInFrame … δ` equals the
intrinsic fibre norm `normSq0S g 5 (∇Rm)` in a `g`-orthonormal frame whose centre
values are `basis`.  (`∇Rm` factor of `abs_spatialCommNablaRm_orthoFrame_le`,
re-expressed frame-independently.) -/
theorem nablaRm04NormSqInFrame_orthoBasis_eq_normSq0S
    {D : DifferentialGeometry.Integral.Connection.RealTimeInterval}
    (S : SolutionOn (I := I) (M := M) D)
    (t : DifferentialGeometry.Integral.Connection.RealTimeInterval.RegularTime D)
    (x₀ : M)
    (frame : Fin n → (x : M) → TangentSpace I x)
    (basis : Module.Basis (Fin n) Real (TangentSpace I x₀))
    (hframe : ∀ i : Fin n, frame i x₀ = basis i)
    (horth : ∀ i j : Fin n,
      (S.base.metric (t : Real)).inner x₀ (basis i) (basis j) =
        if i = j then (1 : Real) else 0) :
    nablaRm04NormSqInFrame (M := M)
        (fun s y i j k l p =>
          nablaRm04Field (I := I) S s y (vec5 (I := I)
            (frame i y) (frame j y) (frame k y) (frame l y) (frame p y)))
        (deltaInvMetric (M := M)) (t : Real) x₀ =
      normSq0S (I := I) (S.base.metric (t : Real)) x₀ 5
        (nablaRm04Field (I := I) S (t : Real) x₀) := by
  classical
  -- The δ-raised frame norm is `compNormSq5` of the frame components.
  rw [nablaRm04NormSqInFrame_eq_compNormSq5 (M := M) _
    (deltaInvMetric (M := M)) (t : Real) x₀
    (deltaInvMetric_orthonormal (M := M) (t : Real) x₀)]
  -- Reindex `compNormSq5` to `compNormSqMulti` of the basis components, then bridge.
  rw [← compNormSqMulti_orthoBasis_eq_normSq0S (I := I) (S.base.metric (t : Real))
    basis horth (nablaRm04Field (I := I) S (t : Real) x₀)]
  rw [compNormSqMulti_eq_compNormSq5
    (fun idx : Fin 5 → Fin n =>
      nablaRm04Field (I := I) S (t : Real) x₀ (fun p => basis (idx p)))]
  refine Finset.sum_congr rfl fun mi _ => ?_
  refine Finset.sum_congr rfl fun a _ => ?_
  refine Finset.sum_congr rfl fun b _ => ?_
  refine Finset.sum_congr rfl fun c _ => ?_
  refine Finset.sum_congr rfl fun d _ => ?_
  dsimp only
  have htup : (fun p : Fin 5 => basis ((![mi, a, b, c, d] : Fin 5 → Fin n) p)) =
      vec5 (I := I) (frame mi x₀) (frame a x₀) (frame b x₀) (frame c x₀) (frame d x₀) := by
    funext p; fin_cases p <;> simp [vec5, hframe]
  rw [htup]

end ProducerNorms

/-! ## The frame-independent (intrinsic-norm) spatial commutator bound

Combining `abs_spatialCommNablaRm_orthoFrame_le` with the two norm-identifications
above yields the spatial commutator bound with the `Rm`/`∇Rm` factors carried by the
**intrinsic** fibre norms `normSq0S` — genuinely frame-independent scalars. -/

/-- **The frame-independent spatial commutator bound for `∇Rm`.**

At `x₀`, for a Ricci-flow solution at a regular time, there exist a `g`-orthonormal
frame `frame` (centre values a `Module.Basis`) and the Kronecker-delta inverse
metric with `InverseMetricOrthonormalAt` holding **genuinely**, such that the
spatial commutator `[Δ, ∇_c] Rm = Δ(∇Rm)(c) − ∇(ΔRm)(c)` is bounded by

`|Δ(∇Rm)(c) − ∇(ΔRm)(c)| ≤ 13·card²·√(|Rm|²)·√(|∇Rm|²)`,

with the `Rm`/`∇Rm` factors now carried by the **intrinsic metric fibre norms**
`normSq0S g · (Rm)` (`= |Rm|²`) and `normSq0S g · (∇Rm)` (`= |∇Rm|²`) — frame-free
scalars.  This is the `Rm ∗ ∇Rm`-bound the `horth`-free producer
(`nablaRm04NormHeatBoundOn_scalar`, `Evolution/NablaRiemannHeatSolution.lean`)
consumes as the *spatial* part of its frame-independent reaction bound `reaction ≤
cReact·√v·u` with `v = |Rm|²`, `u = |∇Rm|²` intrinsic.

This is `abs_spatialCommNablaRm_orthoFrame_le` with its `rm04NormSqInFrame δ` /
`nablaRm04NormSqInFrame δ` factors rewritten as the intrinsic `normSq0S` via the
norm frame-invariance bridge `compNormSqMulti_orthoBasis_eq_normSq0S`.  No
orthonormal frame is referenced in the bound's *right-hand side*; the frame is only
the existential witness in which the diagonal trace is the genuine rough Laplacian. -/
theorem abs_spatialCommNablaRm_intrinsic_le
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
        |roughLapNablaRmCompF (I := I) S (t : Real) x₀ frame
            (deltaInvMetric (M := M) (Idx := Fin n) (t : Real) x₀) c m -
          nablaRoughLapRmCompF (I := I) S (t : Real) x₀ frame
            (deltaInvMetric (M := M) (Idx := Fin n) (t : Real) x₀) c m| ≤
          (13 : Real) * (Fintype.card (Fin n) : Real) ^ 2 *
            (Real.sqrt (normSq0S (I := I) (S.base.metric (t : Real)) x₀ 4
                (S.base.rm04 (t : Real) x₀)) *
              Real.sqrt (normSq0S (I := I) (S.base.metric (t : Real)) x₀ 5
                (nablaRm04Field (I := I) S (t : Real) x₀))) := by
  classical
  -- Recover the orthonormal frame, the genuine δ inverse metric, and the
  -- frame-component spatial commutator bound.
  obtain ⟨n, frame, hortho, hinv, hbnd⟩ :=
    abs_spatialCommNablaRm_orthoFrame_le (I := I) S hS t x₀
  -- The frame's centre values form a `Module.Basis` (from the orthonormal-basis
  -- construction); recover it alongside the centre-value identity.
  obtain ⟨n', frame', basis, hframe', horth'⟩ :=
    exists_orthoBasisFrameAt (I := I) S (t : Real) x₀
  -- Use the `exists_orthoBasisFrameAt` frame directly (it satisfies both the
  -- orthonormality and the `Module.Basis` centre identity), re-running the
  -- frame-component bound on it.
  refine ⟨n', frame', ?_, deltaInvMetric_orthonormal (M := M) (t : Real) x₀, ?_⟩
  · intro i j; rw [hframe' i, hframe' j]; exact horth' i j
  intro c m
  -- The frame-component spatial commutator bound, specialised to `frame'`.
  have hbnd' :
      |roughLapNablaRmCompF (I := I) S (t : Real) x₀ frame'
            (deltaInvMetric (M := M) (Idx := Fin n') (t : Real) x₀) c m -
          nablaRoughLapRmCompF (I := I) S (t : Real) x₀ frame'
            (deltaInvMetric (M := M) (Idx := Fin n') (t : Real) x₀) c m| ≤
        (13 : Real) * (Fintype.card (Fin n') : Real) ^ 2 *
          (Real.sqrt (rm04NormSqInFrame (I := I) (fun s => S.base.rm04 s)
              (deltaInvMetric (M := M)) frame' (t : Real) x₀) *
            Real.sqrt (nablaRm04NormSqInFrame (M := M)
              (fun s y i j k l p =>
                nablaRm04Field (I := I) S s y (vec5 (I := I)
                  (frame' i y) (frame' j y) (frame' k y) (frame' l y) (frame' p y)))
              (deltaInvMetric (M := M)) (t : Real) x₀)) := by
    -- Re-run the commutator identity + reaction bound on `frame'` directly.
    rw [nablaLapCommF_orthonormalTrace (I := I) S hS t x₀ frame'
      (deltaInvMetric (M := M) (Idx := Fin n') (t : Real) x₀) (fun i j => rfl) c m]
    have hreact := abs_nablaLapCommReactionTerm_diag_orthoBasis_le (I := I) S hS t x₀
      frame' basis hframe' horth' c m
    have hRm :
        compNormSq4 (fun i j k l : Fin n' =>
            S.base.rm04 (t : Real) x₀ (vec4 (I := I) (basis i) (basis j) (basis k) (basis l))) =
          rm04NormSqInFrame (I := I) (fun s => S.base.rm04 s)
            (deltaInvMetric (M := M)) frame' (t : Real) x₀ := by
      rw [rm04NormSqInFrame_eq_compNormSq4 (I := I) (fun s => S.base.rm04 s)
        (deltaInvMetric (M := M)) frame' (t : Real) x₀
        (deltaInvMetric_orthonormal (M := M) (t : Real) x₀)]
      refine Finset.sum_congr rfl fun i _ => ?_
      refine Finset.sum_congr rfl fun j _ => ?_
      refine Finset.sum_congr rfl fun k _ => ?_
      refine Finset.sum_congr rfl fun l _ => ?_
      simp only [DifferentialGeometry.Integral.Connection.rm04Comp]
      rw [hframe' i, hframe' j, hframe' k, hframe' l]
    have hNab :
        compNormSqMulti (fun idx : Fin 5 → Fin n' =>
            nablaRm04Field (I := I) S (t : Real) x₀ (fun p => basis (idx p))) =
          nablaRm04NormSqInFrame (M := M)
            (fun s y i j k l p =>
              nablaRm04Field (I := I) S s y (vec5 (I := I)
                (frame' i y) (frame' j y) (frame' k y) (frame' l y) (frame' p y)))
            (deltaInvMetric (M := M)) (t : Real) x₀ := by
      rw [nablaRm04NormSqInFrame_eq_compNormSq5 (M := M) _
        (deltaInvMetric (M := M)) (t : Real) x₀
        (deltaInvMetric_orthonormal (M := M) (t : Real) x₀)]
      rw [compNormSqMulti_eq_compNormSq5
        (fun idx : Fin 5 → Fin n' =>
          nablaRm04Field (I := I) S (t : Real) x₀ (fun p => basis (idx p)))]
      refine Finset.sum_congr rfl fun mi _ => ?_
      refine Finset.sum_congr rfl fun a _ => ?_
      refine Finset.sum_congr rfl fun b _ => ?_
      refine Finset.sum_congr rfl fun c' _ => ?_
      refine Finset.sum_congr rfl fun d _ => ?_
      dsimp only
      have htup : (fun p : Fin 5 => basis ((![mi, a, b, c', d] : Fin 5 → Fin n') p)) =
          vec5 (I := I) (frame' mi x₀) (frame' a x₀) (frame' b x₀) (frame' c' x₀) (frame' d x₀) := by
        funext p; fin_cases p <;> simp [vec5, hframe']
      rw [htup]
    rw [hRm, hNab] at hreact
    exact hreact
  -- Rewrite the two frame norms as the intrinsic fibre norms.
  rw [rm04NormSqInFrame_orthoBasis_eq_normSq0S (I := I) S t x₀ frame' basis hframe' horth',
    nablaRm04NormSqInFrame_orthoBasis_eq_normSq0S (I := I) S t x₀ frame' basis hframe' horth']
    at hbnd'
  exact hbnd'

/-! ## Remaining frontier (the intrinsic-norm time derivative)

This file discharges the **norm frame-invariance** half of WALL 2 (Route (b)):
the proven spatial commutator bound is now stated against the *intrinsic*,
frame-independent fibre norms `normSq0S g (Rm)` / `normSq0S g (∇Rm)`
(`abs_spatialCommNablaRm_intrinsic_le`), the exact `Rm ∗ ∇Rm` shape the
`horth`-free scalar producer (`nablaRm04NormHeatBoundOn_scalar`) consumes as the
*spatial* part of its reaction bound.

What this file does **not** close — the genuinely remaining `k = 1` frontier:

1. **The intrinsic-norm time derivative `∂ₜ|∇Rm|²`** (the *temporal* half of the
   heat residual `(∂ₜ − Δ)∇Rm`).  The full scalar heat **equation**
   `NablaRm04NormHeatEquationOn u uLap nabla2 reaction` needs `∂ₜu` for the
   intrinsic `u = |∇Rm|² = normSq0S (g(t)) (∇Rm)`.  But:
   * `iteratedRmComp_one_hasDerivWithinAt` (`Evolution/NablaRiemannTimeDeriv.lean`)
     gives the *per-component* time derivative in the **time-independent
     `coordinateFrameAt`**, not `∂ₜ(normSq0S (g(t)) ·)`;
   * `normSq0S (g(t)) ·` carries the **moving metric `g(t)`**, so `∂ₜ` of it picks
     up a `∂ₜg`-contraction term (the analogue of the `k = 0`
     `raisedRm04DerivRHSInFrame` term in `rm04NormDerivRHSInFrame`,
     `Evolution/RiemannNorm.lean`).
   This is the **same status as the `k = 0` producer**: the `k = 0` heat equation
   (`rm04NormHeatEquationOn_of_solution`,
   `Evolution/RiemannNormHeatProducer.lean`) also takes its raw time-derivative
   identity (`Rm04NormRawDerivativeEquationOn`) as a *hypothesis*, and produces the
   heat equation in `rm04NormSqInFrame Rm04 gInv frame` for a **fixed frame and
   moving `gInv`** (Route (a)), never closing `∂ₜ|Rm|²` from a bare `SolutionOn`.
   So this gap is **not** specific to `k = 1`; the project's `k = 0` baseline has
   the identical hypothesis-status time-derivative input.

2. **The full residual reaction** `2⟨(∂ₜ − Δ)∇Rm, ∇Rm⟩`.  Beyond the spatial
   commutator bounded here, the residual also has the temporal pieces
   `∂ₜ(∇Rm) − ∇(∂ₜRm) = (∂ₜΓ) ∗ Rm` (with `∂ₜΓ = ∇Ric` under Ricci flow) and the
   Uhlenbeck `∂ₜRm − ΔRm = Rm ∗ Rm`, which are `Rm ∗ ∇Rm`/`Rm ∗ Rm`-controlled but
   not yet assembled into the contracted reaction scalar.

The deliverable here is the precise, verified reduction of Route (b)'s
*norm-identification* obstruction to a single reusable bridge
(`compNormSqMulti_orthoBasis_eq_normSq0S`), leaving the intrinsic-norm
time-derivative (item 1, the `k = 0`-status hypothesis input) and the temporal
residual assembly (item 2) as the remaining `k = 1` frontier. -/

end DifferentialGeometry.PDE.RicciFlow
