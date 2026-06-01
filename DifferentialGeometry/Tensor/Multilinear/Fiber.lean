/-
Authors: Jack McCarthy
-/
import DifferentialGeometry.Tensor.Multilinear.Bundle
import DifferentialGeometry.Tensor.Multilinear.Basis
/-!
# Fiber-level results for the continuous multilinear map bundle

This file establishes that the bundle topology on each fiber
`Bundle.continuousMultilinearMap 𝕜 s F E x` agrees with the norm topology on
`ContinuousMultilinearMap 𝕜 (fun _ : Fin s => E x) 𝕜`, and derives topological and
algebraic instances from this fact.

These results hold for any vector bundle `E` with normed fibers, not just the
tangent bundle. The key tool is a continuous linear equivalence from the bundle fiber
to the model fiber, constructed from the trivialization at each point.

## Main Definitions

* `Bundle.continuousMultilinearMap.continuousLinearEquivAt`: the CLE from the bundle fiber
  at `x` to the model fiber, built from the trivialization at `x`.

## Main Results

* `Bundle.continuousMultilinearMap.topology_eq`: the bundle and norm topologies agree.
* Derived instances: `NormedAddCommGroup`, `NormedSpace`, `T2Space`,
  `IsTopologicalAddGroup`, `ContinuousSMul`, `FiniteDimensional` on fibers.
* `Bundle.continuousMultilinearMap.finrank_eq`: dimension is `(finrank 𝕜 F) ^ s`.

## Tags

multilinear map, vector bundle, fiber topology, continuous linear equivalence
-/

noncomputable section

set_option backward.isDefEq.respectTransparency false

open Bundle Set

open scoped Manifold Topology Bundle ContDiff BigOperators

namespace Bundle.continuousMultilinearMap

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
variable {B : Type*} [TopologicalSpace B]
variable {F : Type*} [NormedAddCommGroup F] [NormedSpace 𝕜 F]
variable {E : B → Type*} [∀ x, NormedAddCommGroup (E x)] [∀ x, NormedSpace 𝕜 (E x)]
variable [TopologicalSpace (TotalSpace F E)]
variable [FiberBundle F E] [VectorBundle 𝕜 F E]
variable {s : ℕ}

/-- `Bundle.continuousMultilinearMap` fibers inherit the `FunLike` coercion from
`ContinuousMultilinearMap`, enabling direct function application. -/
instance instFunLike (s : ℕ) (x : B) :
    FunLike (Bundle.continuousMultilinearMap 𝕜 s F E x) (Fin s → E x) 𝕜 :=
  ContinuousMultilinearMap.funLike

/-!
## Topology equivalence

The bundle topology on `Bundle.continuousMultilinearMap 𝕜 s F E x` is defined as
`induced (pretriv ∘ mk') product_topology`. We show this equals the norm topology on
`ContinuousMultilinearMap 𝕜 (fun _ : Fin s => E x) 𝕜` by factoring through a
homeomorphism to the model fiber.
-/

set_option backward.isDefEq.respectTransparency false in
/-- The bundle and norm topologies on a `Bundle.continuousMultilinearMap` fiber agree.
The bundle topology is induced from the pretrivialization (a continuous linear equivalence
to the model fiber), and this coincides with the norm topology since the composition map
is a homeomorphism. -/
theorem topology_eq (s : ℕ) (x : B) :
    (inferInstance : TopologicalSpace (Bundle.continuousMultilinearMap 𝕜 s F E x)) =
    (inferInstanceAs (TopologicalSpace
      (ContinuousMultilinearMap 𝕜 (fun _ : Fin s => E x) 𝕜))) := by
  change instTopologicalSpaceContinuousMultilinearMap 𝕜 s F E x = _
  simp only [instTopologicalSpaceContinuousMultilinearMap]
  -- Step 1: Factor pretriv ∘ mk' = Prod.mk x ∘ g where g is the fiber map
  set e := trivializationAt F E x
  set g : ContinuousMultilinearMap 𝕜 (fun _ : Fin s => E x) 𝕜 →L[𝕜]
      ContinuousMultilinearMap 𝕜 (fun _ : Fin s => F) 𝕜 :=
    ContinuousMultilinearMap.compContinuousLinearMapL (fun _ => e.symmL 𝕜 x) with hg_def
  have hfactor : (↑(Pretrivialization.continuousMultilinearMap 𝕜 s e) ∘
      TotalSpace.mk' _ x) = Prod.mk x ∘ g := by funext; rfl
  -- Step 2: Decompose via induced_compose and isInducing_prodMkRight
  rw [hfactor, ← induced_compose, (isInducing_prodMkRight x).eq_induced.symm]
  -- Goal: induced g τ_norm = τ_norm
  -- Step 3: g is a homeomorphism (continuous with continuous inverse), hence inducing
  set g' := ContinuousMultilinearMap.compContinuousLinearMapL (F := 𝕜)
    (E₁ := fun _ : Fin s => F) (E := fun _ : Fin s => E x)
    (fun _ => e.continuousLinearMapAt 𝕜 x) with hg'_def
  have hx : x ∈ e.baseSet := mem_baseSet_trivializationAt F E x
  have hleft : Function.LeftInverse g' g := by
    intro L; ext v; dsimp [g, g']
    congr 1; funext i; exact e.symmₗ_linearMapAt hx (v i)
  have hright : Function.RightInverse g' g := by
    intro M; ext v; dsimp [g, g']
    congr 1; funext i; exact e.linearMapAt_symmₗ hx (v i)
  exact (Homeomorph.mk ⟨g, g', hleft, hright⟩
    g.continuous g'.continuous).isInducing.eq_induced.symm

/-!
## Normed instances
-/

/-- The fiber `Bundle.continuousMultilinearMap 𝕜 s F E x` is a normed additive commutative
group, using the norm topology which agrees with the bundle topology. -/
instance instNormedAddCommGroup (s : ℕ) (x : B) :
    NormedAddCommGroup (Bundle.continuousMultilinearMap 𝕜 s F E x) := by
  delta Bundle.continuousMultilinearMap; infer_instance

/-- The fiber `Bundle.continuousMultilinearMap 𝕜 s F E x` is a normed `𝕜`-module. -/
instance instNormedSpace (s : ℕ) (x : B) :
    NormedSpace 𝕜 (Bundle.continuousMultilinearMap 𝕜 s F E x) := by
  delta Bundle.continuousMultilinearMap; exact ContinuousMultilinearMap.normedSpace

/-!
## Topological instances derived from the topology equality
-/

instance instT2Space (s : ℕ) (x : B) :
    @T2Space (Bundle.continuousMultilinearMap 𝕜 s F E x) inferInstance :=
  (topology_eq (𝕜 := 𝕜) (F := F) (E := E) s x).symm ▸
    inferInstanceAs (@T2Space (ContinuousMultilinearMap 𝕜 (fun _ : Fin s => E x) 𝕜) _)

instance instIsTopologicalAddGroup (s : ℕ) (x : B) :
    @IsTopologicalAddGroup (Bundle.continuousMultilinearMap 𝕜 s F E x) inferInstance _ :=
  (topology_eq (𝕜 := 𝕜) (F := F) (E := E) s x).symm ▸
    inferInstanceAs (@IsTopologicalAddGroup
      (ContinuousMultilinearMap 𝕜 (fun _ : Fin s => E x) 𝕜) _ _)

instance instContinuousSMul (s : ℕ) (x : B) :
    @ContinuousSMul 𝕜 (Bundle.continuousMultilinearMap 𝕜 s F E x) _ _ inferInstance :=
  (topology_eq (𝕜 := 𝕜) (F := F) (E := E) s x).symm ▸
    inferInstanceAs (@ContinuousSMul 𝕜
      (ContinuousMultilinearMap 𝕜 (fun _ : Fin s => E x) 𝕜) _ _ _)

instance instContinuousAdd (s : ℕ) (x : B) :
    @ContinuousAdd (Bundle.continuousMultilinearMap 𝕜 s F E x) inferInstance _ :=
  @IsTopologicalAddGroup.toContinuousAdd _ inferInstance _ (instIsTopologicalAddGroup s x)

/-!
## Continuous linear equivalence to the model fiber
-/

/-- The continuous linear equivalence from the multilinear bundle fiber at `x` to the model
fiber `ContinuousMultilinearMap 𝕜 (fun _ : Fin s => F) 𝕜`, constructed from the
trivialization at `x`. The forward map precomposes with `e.symmL`, and the inverse
precomposes with `e.continuousLinearMapAt`. -/
def continuousLinearEquivAt (s : ℕ) (x : B) :
    Bundle.continuousMultilinearMap 𝕜 s F E x ≃L[𝕜]
    ContinuousMultilinearMap 𝕜 (fun _ : Fin s => F) 𝕜 where
  toFun := ContinuousMultilinearMap.compContinuousLinearMapL
    (fun _ => (trivializationAt F E x).symmL 𝕜 x)
  invFun := ContinuousMultilinearMap.compContinuousLinearMapL
    (fun _ => (trivializationAt F E x).continuousLinearMapAt 𝕜 x)
  left_inv L := ContinuousMultilinearMap.ext fun v => by
    dsimp [ContinuousMultilinearMap.compContinuousLinearMapL]
    congr 1; funext i
    exact (trivializationAt F E x).symmₗ_linearMapAt
      (mem_baseSet_trivializationAt F E x) (v i)
  right_inv M := ContinuousMultilinearMap.ext fun v => by
    dsimp [ContinuousMultilinearMap.compContinuousLinearMapL]
    congr 1; funext i
    exact (trivializationAt F E x).linearMapAt_symmₗ
      (mem_baseSet_trivializationAt F E x) (v i)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  continuous_toFun := by
    change @Continuous (Bundle.continuousMultilinearMap 𝕜 s F E x)
      (ContinuousMultilinearMap 𝕜 (fun _ : Fin s => F) 𝕜)
      (instTopologicalSpaceContinuousMultilinearMap 𝕜 s F E x)
      ContinuousMultilinearMap.instTopologicalSpace _
    rw [show instTopologicalSpaceContinuousMultilinearMap 𝕜 s F E x =
      ContinuousMultilinearMap.instTopologicalSpace from topology_eq s x]
    exact (ContinuousMultilinearMap.compContinuousLinearMapL
      (fun _ => (trivializationAt F E x).symmL 𝕜 x)).continuous
  continuous_invFun := by
    change @Continuous (ContinuousMultilinearMap 𝕜 (fun _ : Fin s => F) 𝕜)
      (Bundle.continuousMultilinearMap 𝕜 s F E x)
      ContinuousMultilinearMap.instTopologicalSpace
      (instTopologicalSpaceContinuousMultilinearMap 𝕜 s F E x) _
    rw [show instTopologicalSpaceContinuousMultilinearMap 𝕜 s F E x =
      ContinuousMultilinearMap.instTopologicalSpace from topology_eq s x]
    exact (ContinuousMultilinearMap.compContinuousLinearMapL
      (fun _ => (trivializationAt F E x).continuousLinearMapAt 𝕜 x)).continuous

/-!
## Extensionality
-/

omit [TopologicalSpace B] [NormedAddCommGroup F] [NormedSpace 𝕜 F]
  [TopologicalSpace (TotalSpace F E)] [FiberBundle F E] [VectorBundle 𝕜 F E] in
@[ext]
theorem ext {s : ℕ} {x : B}
    {T₁ T₂ : Bundle.continuousMultilinearMap 𝕜 s F E x}
    (h : ∀ m, T₁ m = T₂ m) : T₁ = T₂ :=
  ContinuousMultilinearMap.ext h

/-!
## Degeneracy of the `0`-multilinear bundle trivialization

For the `0`-multilinear bundle, the trivialization at any base point is degenerate:
because the trivialization precomposes with `symmL` per argument, and on `Fin 0` arguments
this composition is vacuous, the trivialized form of any fiber element evaluated at any
input reduces to the original element evaluated at the unique empty tuple.

This degeneracy is the technical content that makes the equivalence between mixed
`(0, s)`-sections and pure `s`-multilinear sections work smoothly.
-/

/-- The trivialization at `x₀` of a `0`-multilinear bundle fiber element `T` at point `x`,
when evaluated at any `Fin 0 → F` argument, equals `T Fin.elim0`. The trivialization is
defined by precomposing with `symmL` per argument, which on `Fin 0` arguments is vacuous. -/
theorem triv_zero_apply_eq (x₀ x : B)
    (T : Bundle.continuousMultilinearMap 𝕜 0 F E x)
    (w : Fin 0 → F) :
    (trivializationAt (ContinuousMultilinearMap 𝕜 (fun _ : Fin 0 => F) 𝕜)
      (Bundle.continuousMultilinearMap 𝕜 0 F E) x₀ ⟨x, T⟩).2 w = T Fin.elim0 := by
  change T (fun i : Fin 0 => (trivializationAt F E x₀).symmL 𝕜 x (w i)) = T Fin.elim0
  exact congrArg T (Subsingleton.elim _ _)

/-- Symmetric version: applying the inverse of the trivialization at `x₀` to a model-fiber
element `ω₀ : MLF 0` and then evaluating at `Fin.elim0` recovers `ω₀ 0`. Used to compute
the trivialized form of `eval₀`-style smooth sections. -/
theorem triv_zero_symmL_apply_elim0 (x₀ x : B)
    (hx : x ∈ (trivializationAt F E x₀).baseSet)
    (ω₀ : ContinuousMultilinearMap 𝕜 (fun _ : Fin 0 => F) 𝕜) :
    ((trivializationAt (ContinuousMultilinearMap 𝕜 (fun _ : Fin 0 => F) 𝕜)
        (Bundle.continuousMultilinearMap 𝕜 0 F E) x₀).symmL 𝕜 x ω₀ :
        Bundle.continuousMultilinearMap 𝕜 0 F E x) Fin.elim0 = ω₀ 0 := by
  set e := trivializationAt (ContinuousMultilinearMap 𝕜 (fun _ : Fin 0 => F) 𝕜)
    (Bundle.continuousMultilinearMap 𝕜 0 F E) x₀ with he_def
  have hbase : x ∈ e.baseSet := hx
  -- `e.symmL 𝕜 x ω₀` and `e.symm x ω₀` agree as fiber elements (definitional via simps).
  have hsymmL : (e.symmL 𝕜 x ω₀ : Bundle.continuousMultilinearMap 𝕜 0 F E x) =
      e.symm x ω₀ := by
    simp [Trivialization.symmL_apply]
  rw [hsymmL]
  -- Apply triv_zero_apply_eq to the fiber element T = e.symm x ω₀, with input 0.
  have h1 := triv_zero_apply_eq (F := F) (E := E) x₀ x (e.symm x ω₀) 0
  -- h1 : (e ⟨x, e.symm x ω₀⟩).2 0 = (e.symm x ω₀) Fin.elim0
  -- Use that e ⟨x, e.symm x ω₀⟩ = (x, ω₀) via apply_mk_symm.
  have h2 : (e ⟨x, e.symm x ω₀⟩ : B × _) = (x, ω₀) :=
    e.apply_mk_symm hbase ω₀
  rw [show (e ⟨x, e.symm x ω₀⟩ : B × _).2 = ω₀ from congrArg Prod.snd h2] at h1
  exact h1.symm

/-!
## Inverse trivialization formula for `s`-multilinear bundles

The inverse trivialization `e.symmL 𝕜 x T` of the multilinear bundle at `x₀` sends a
model-fiber element `T : MLF s` to a fiber element that, when applied to any
`v : Fin s → E x`, gives `T (fun i => (trivAt F E x₀).continuousLinearMapAt 𝕜 x (v i))`.

This is the analog of `triv_zero_apply_eq` for the inverse direction and for general `s`.
-/

/-- The inverse trivialization of the multilinear bundle at `x₀`, applied to a model-fiber
element `T : MLF s` at point `x ∈ baseSet`, when evaluated at `v : Fin s → E x`, equals
`T` applied to `(trivAt F E x₀).continuousLinearMapAt 𝕜 x` composed into each argument.

The proof uses the round-trip: apply the forward trivialization to `e.symm x T` and use
`e.apply_mk_symm` to recover `T`, then match via the forward trivialization formula. -/
theorem triv_symmL_eq_compContinuousLinearMap {s : ℕ} (x₀ x : B)
    (hx : x ∈ (trivializationAt F E x₀).baseSet)
    (T : ContinuousMultilinearMap 𝕜 (fun _ : Fin s => F) 𝕜) :
    ((trivializationAt (ContinuousMultilinearMap 𝕜 (fun _ : Fin s => F) 𝕜)
        (Bundle.continuousMultilinearMap 𝕜 s F E) x₀).symmL 𝕜 x T :
        Bundle.continuousMultilinearMap 𝕜 s F E x) =
      T.compContinuousLinearMap
        (fun _ : Fin s => (trivializationAt F E x₀).continuousLinearMapAt 𝕜 x) := by
  set e := trivializationAt (ContinuousMultilinearMap 𝕜 (fun _ : Fin s => F) 𝕜)
    (Bundle.continuousMultilinearMap 𝕜 s F E) x₀ with he_def
  have hbase : x ∈ e.baseSet := hx
  -- Convert `e.symmL` to `e.symm` (they agree as functions).
  have hsymmL : (e.symmL 𝕜 x T : Bundle.continuousMultilinearMap 𝕜 s F E x) =
      e.symm x T := by
    simp [Trivialization.symmL_apply]
  rw [hsymmL]
  -- Both sides are continuous multilinear maps on `E x`. Check equality on any input.
  apply Bundle.continuousMultilinearMap.ext
  intro v
  -- RHS at v: T (fun i => (trivAt F E x₀).continuousLinearMapAt 𝕜 x (v i))
  rw [ContinuousMultilinearMap.compContinuousLinearMap_apply]
  -- LHS at v: (e.symm x T) v
  -- Use the round-trip: `(e ⟨x, e.symm x T⟩).2 = T` (by `e.apply_mk_symm`).
  -- The forward trivialization formula gives:
  -- `(e ⟨x, M⟩).2 w = M (fun i => (trivAt F E x₀).symmL 𝕜 x (w i))` (definitionally).
  -- So `T w = (e.symm x T) (fun i => (trivAt F E x₀).symmL 𝕜 x (w i))`.
  -- Setting `w i = (trivAt F E x₀).continuousLinearMapAt 𝕜 x (v i)`:
  -- `T (fun i => e.cLMA x (v i)) = (e.symm x T) (fun i => e.symmL x (e.cLMA x (v i)))`
  -- `= (e.symm x T) (fun i => v i)` by `symmL_continuousLinearMapAt`.
  -- This is `(e.symm x T) v`. ✓
  have h_fwd : ∀ (M : Bundle.continuousMultilinearMap 𝕜 s F E x)
      (w : Fin s → F),
      (e ⟨x, M⟩).2 w = M (fun i => (trivializationAt F E x₀).symmL 𝕜 x (w i)) := by
    intro M w; rfl
  have h_rt : (e ⟨x, e.symm x T⟩ : B × _) = (x, T) :=
    e.apply_mk_symm hbase T
  -- From h_rt: `(e ⟨x, e.symm x T⟩).2 = T`.
  have h_snd : (e ⟨x, e.symm x T⟩ : B × _).2 = T := congrArg Prod.snd h_rt
  -- From h_fwd with M = e.symm x T, w i = (trivAt F E x₀).continuousLinearMapAt 𝕜 x (v i):
  have h_apply := h_fwd (e.symm x T)
    (fun i => (trivializationAt F E x₀).continuousLinearMapAt 𝕜 x (v i))
  -- h_apply: (e ⟨x, e.symm x T⟩).2 (fun i => e.cLMA x (v i))
  --        = (e.symm x T) (fun i => e.symmL x (e.cLMA x (v i)))
  rw [h_snd] at h_apply
  -- h_apply: T (fun i => e.cLMA x (v i)) = (e.symm x T) (fun i => e.symmL x (e.cLMA x (v i)))
  -- The RHS of h_apply simplifies: e.symmL x ∘ e.cLMA x = id (by symmL_continuousLinearMapAt).
  conv_rhs at h_apply =>
    arg 2; ext i
    rw [(trivializationAt F E x₀).symmL_continuousLinearMapAt hx (v i)]
  -- h_apply: T (fun i => e.cLMA x (v i)) = (e.symm x T) v
  exact h_apply.symm

/-!
## Coercion to model fiber

The continuous linear equivalence `continuousLinearEquivAt` identifies each fiber with
the model fiber. We package this as `toModel` (forward direction) and `ofModel`
(its inverse), together with linearity, continuity, and invertibility lemmas.
-/

/-- Coerce a multilinear bundle fiber element to the model fiber via the trivialization CLE. -/
def toModel {s : ℕ} {x : B}
    (T : Bundle.continuousMultilinearMap 𝕜 s F E x) :
    ContinuousMultilinearMap 𝕜 (fun _ : Fin s => F) 𝕜 :=
  continuousLinearEquivAt (F := F) (E := E) s x T

/-- `toModel` as a bundled `ContinuousLinearMap`. -/
def toModelL (s : ℕ) (x : B) :
    Bundle.continuousMultilinearMap 𝕜 s F E x →L[𝕜]
    ContinuousMultilinearMap 𝕜 (fun _ : Fin s => F) 𝕜 :=
  (continuousLinearEquivAt (F := F) (E := E) s x).toContinuousLinearMap

/-- Construct a multilinear bundle fiber element from a model fiber element. -/
def ofModel {s : ℕ} {x : B}
    (f : ContinuousMultilinearMap 𝕜 (fun _ : Fin s => F) 𝕜) :
    Bundle.continuousMultilinearMap 𝕜 s F E x :=
  (continuousLinearEquivAt (F := F) (E := E) s x).symm f

@[simp]
theorem toModelL_apply {s : ℕ} {x : B}
    (T : Bundle.continuousMultilinearMap 𝕜 s F E x) :
    toModelL (F := F) (E := E) s x T = toModel T := rfl

@[simp]
theorem toModel_add {s : ℕ} {x : B}
    (T₁ T₂ : Bundle.continuousMultilinearMap 𝕜 s F E x) :
    toModel (F := F) (E := E) (T₁ + T₂) =
      toModel T₁ + toModel T₂ :=
  map_add (continuousLinearEquivAt (F := F) (E := E) s x) T₁ T₂

@[simp]
theorem toModel_smul {s : ℕ} {x : B}
    (c : 𝕜) (T : Bundle.continuousMultilinearMap 𝕜 s F E x) :
    toModel (F := F) (E := E) (c • T) = c • toModel T :=
  map_smul (continuousLinearEquivAt (F := F) (E := E) s x) c T

@[simp]
theorem toModel_zero {s : ℕ} {x : B} :
    toModel (F := F) (E := E)
      (0 : Bundle.continuousMultilinearMap 𝕜 s F E x) = 0 :=
  map_zero (continuousLinearEquivAt (F := F) (E := E) s x)

@[simp]
theorem toModel_neg {s : ℕ} {x : B}
    (T : Bundle.continuousMultilinearMap 𝕜 s F E x) :
    toModel (F := F) (E := E) (-T) = -toModel T :=
  map_neg (continuousLinearEquivAt (F := F) (E := E) s x) T

@[simp]
theorem toModel_sub {s : ℕ} {x : B}
    (T₁ T₂ : Bundle.continuousMultilinearMap 𝕜 s F E x) :
    toModel (F := F) (E := E) (T₁ - T₂) =
      toModel T₁ - toModel T₂ :=
  map_sub (continuousLinearEquivAt (F := F) (E := E) s x) T₁ T₂

@[simp]
theorem ofModel_toModel {s : ℕ} {x : B}
    (T : Bundle.continuousMultilinearMap 𝕜 s F E x) :
    ofModel (F := F) (E := E) (toModel T) = T :=
  (continuousLinearEquivAt (F := F) (E := E) s x).symm_apply_apply T

@[simp]
theorem toModel_ofModel {s : ℕ} {x : B}
    (f : ContinuousMultilinearMap 𝕜 (fun _ : Fin s => F) 𝕜) :
    toModel (F := F) (E := E) (ofModel (x := x) f) = f :=
  (continuousLinearEquivAt (F := F) (E := E) s x).apply_symm_apply f

theorem toModel_continuous {s : ℕ} {x : B} :
    Continuous
      (fun T : Bundle.continuousMultilinearMap 𝕜 s F E x =>
        toModel (F := F) (E := E) T) :=
  (continuousLinearEquivAt (F := F) (E := E) s x).continuous_toFun

theorem toModel_injective {s : ℕ} {x : B} :
    Function.Injective
      (fun T : Bundle.continuousMultilinearMap 𝕜 s F E x =>
        toModel (F := F) (E := E) T) :=
  (continuousLinearEquivAt (F := F) (E := E) s x).injective

theorem toModel_surjective {s : ℕ} {x : B} :
    Function.Surjective
      (fun T : Bundle.continuousMultilinearMap 𝕜 s F E x =>
        toModel (F := F) (E := E) T) :=
  (continuousLinearEquivAt (F := F) (E := E) s x).surjective

theorem toModel_bijective {s : ℕ} {x : B} :
    Function.Bijective
      (fun T : Bundle.continuousMultilinearMap 𝕜 s F E x =>
        toModel (F := F) (E := E) T) :=
  (continuousLinearEquivAt (F := F) (E := E) s x).bijective

/-!
## Finite-dimensionality and rank
-/

variable [CompleteSpace 𝕜] [FiniteDimensional 𝕜 F]

noncomputable instance instFiniteDimensional (s : ℕ) (x : B) :
    FiniteDimensional 𝕜 (Bundle.continuousMultilinearMap 𝕜 s F E x) := by
  haveI : FiniteDimensional 𝕜 (ContinuousMultilinearMap 𝕜 (fun _ : Fin s => F) 𝕜) :=
    continuousMultilinearMap_finiteDimensional s
  exact (continuousLinearEquivAt (F := F) (E := E) s x).symm.toLinearEquiv.finiteDimensional

@[simp]
theorem finrank_eq (s : ℕ) (x : B) :
    Module.finrank 𝕜 (Bundle.continuousMultilinearMap 𝕜 s F E x) =
    (Module.finrank 𝕜 F) ^ s := by
  rw [(continuousLinearEquivAt (F := F) (E := E) s x).toLinearEquiv.finrank_eq,
      finrank_continuousMultilinearMap s]

end Bundle.continuousMultilinearMap

end
