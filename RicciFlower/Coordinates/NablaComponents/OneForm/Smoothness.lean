import RicciFlower.Coordinates.NablaComponents.OneForm.Moving

/-!
# Coordinate one-form covariant derivative components

This submodule is part of the split `OneForm` coordinate component API.
-/

set_option autoImplicit false
set_option linter.style.longLine false
set_option linter.unusedSectionVars false

noncomputable section

namespace RicciFlower
namespace Coordinates

open Bundle Set Tensor0SBundle TensorLieDeriv
open scoped BigOperators Manifold ContDiff Topology

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜] [CompleteSpace 𝕜]
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
variable [Module.Finite 𝕜 E] [FiniteDimensional 𝕜 E]
variable {H : Type*} [TopologicalSpace H]
variable {I : ModelWithCorners 𝕜 E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
variable [IsManifold I 1 M] [IsManifold I 2 M] [IsManifold I ∞ M]
variable [IsManifold I (∞ : WithTop ℕ∞) M]
variable [IsManifold I ((∞ : WithTop ℕ∞) + 1) M]


private theorem coordinateFrame_coeff_contMDiffAt
    (Z : ContMDiffSection I E (∞ : WithTop ℕ∞) (TangentSpace I : M -> Type _))
    (x₀ : M) (j : CoordinateIdx (𝕜 := 𝕜) E) :
    ContMDiffAt I 𝓘(𝕜, 𝕜) (∞ : WithTop ℕ∞)
      (fun y : M =>
        (coordinateFrameAt_isLocalFrame_one (I := I) x₀).coeff j y (Z y)) x₀ := by
  let e := coordinateTrivializationAt (I := I) x₀
  have hx : x₀ ∈ e.baseSet := by
    simp [e, coordinateTrivializationAt]
  have hcoeff :=
    contMDiffAt_localFrame_coeff
      (I := I) (V := TangentSpace I) (e := e)
      (b := Module.finBasis 𝕜 E) (s := fun y : M => Z y)
      (k := (∞ : WithTop ℕ∞)) hx Z.contMDiff.contMDiffAt j
  simpa [e, coordinateTrivializationAt, coordinateFrameAt_isLocalFrame_one,
    coordinateFrameAt] using hcoeff

private theorem coordinateFrame_coeff_contMDiffAt_of_contMDiffAt
    (Z : (x : M) -> TangentSpace I x) {x₀ : M}
    (hZ : ContMDiffAt I (I.prod 𝓘(𝕜, E)) (∞ : WithTop ℕ∞)
      (fun y : M => (⟨y, Z y⟩ : TotalSpace E (TangentSpace I : M -> Type _))) x₀)
    (j : CoordinateIdx (𝕜 := 𝕜) E) :
    ContMDiffAt I 𝓘(𝕜, 𝕜) (∞ : WithTop ℕ∞)
      (fun y : M =>
        (coordinateFrameAt_isLocalFrame_one (I := I) x₀).coeff j y (Z y)) x₀ := by
  let e := coordinateTrivializationAt (I := I) x₀
  have hx : x₀ ∈ e.baseSet := by
    simp [e, coordinateTrivializationAt]
  have hcoeff :=
    contMDiffAt_localFrame_coeff
      (I := I) (V := TangentSpace I) (e := e)
      (b := Module.finBasis 𝕜 E) (s := Z)
      (k := (∞ : WithTop ℕ∞)) hx hZ j
  simpa [e, coordinateTrivializationAt, coordinateFrameAt_isLocalFrame_one,
    coordinateFrameAt] using hcoeff

set_option backward.isDefEq.respectTransparency false in
theorem oneForm_eval_coordinateFrame_contMDiffAt
    (α : Tensor0SField (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M)
      (n := (∞ : WithTop ℕ∞)) 1)
    (x₀ : M) (j : CoordinateIdx (𝕜 := 𝕜) E) :
    ContMDiffAt I 𝓘(𝕜, 𝕜) (∞ : WithTop ℕ∞)
      (fun y : M => α y (fun _ : Fin 1 => coordinateFrameAt (I := I) x₀ j y)) x₀ := by
  have hα_top := α.contMDiff x₀
  have hα := hα_top.of_le
    (by simp : (∞ : WithTop ℕ∞) ≤ (∞ : WithTop ℕ∞))
  have hframe :
      ContMDiffAt I (I.prod 𝓘(𝕜, E)) (∞ : WithTop ℕ∞)
        (fun y : M =>
          (⟨y, coordinateFrameAt (I := I) x₀ j y⟩ :
            TotalSpace E (TangentSpace I : M -> Type _))) x₀ :=
    (coordinateFrameAt_isLocalFrame (I := I) x₀).contMDiffAt
      (coordinateFrameSet_open (I := I) x₀)
      (coordinateFrameAt_mem (I := I) x₀) j
  have hEval := TensorMultilinear.contMDiffAt_section_apply
    (I := I) (M := M) (n := 1) (x₀ := x₀)
    (T := fun y : M => α y) hα
    (v := fun _ : Fin 1 => coordinateFrameAt (I := I) x₀ j)
    (hv := fun _ : Fin 1 => hframe)
  simpa [Tensor0SSpace.toModel, tensor0SSpace_continuousLinearEquiv_apply] using hEval

/-- Intrinsic one-form covariant derivative formula for smooth moving slots. -/
theorem nabla0SFun_one_eval_smooth_slots
    (cov : CovariantDerivative I E (TangentSpace I : M -> Type _))
    (X Z : ContMDiffSection I E (∞ : WithTop ℕ∞) (TangentSpace I : M -> Type _))
    (α : Tensor0SField (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M)
      (n := (∞ : WithTop ℕ∞)) 1)
    (x₀ : M) :
    (nabla0SFun (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M)
      1 cov X α x₀) (fun _ : Fin 1 => Z x₀) =
      extDerivFun (I := I) (fun y : M => α y (fun _ : Fin 1 => Z y)) x₀ (X x₀) -
        α x₀ (fun _ : Fin 1 => (cov (fun y : M => Z y) x₀) (X x₀)) := by
  rw [nabla0SFun_one_eval_coordFrame_moving
    (I := I) cov X Z α x₀
    (modelDeriv_eq_coordDeriv0SAt (I := I) X x₀ α)
    (fun j =>
      (coordinateFrame_coeff_contMDiffAt (I := I) Z x₀ j).mdifferentiableAt
        (by simp))
      (fun j =>
        (oneForm_eval_coordinateFrame_contMDiffAt (I := I) α x₀ j).mdifferentiableAt
        (by simp))]

/-- If the scalar pairing `α(Z)` is locally constant, then the one-form
covariant derivative is just the correction term
`(∇_X α)(Z) = - α(∇_X Z)`.

This is the reusable derivation-on-contraction step behind the local coframe
identity `∇ θ^i = -Γ^i_j θ^j`. -/
theorem nabla0SFun_one_eval_of_pair_eventually_const
    (cov : CovariantDerivative I E (TangentSpace I : M -> Type _))
    (X Z : ContMDiffSection I E (∞ : WithTop ℕ∞) (TangentSpace I : M -> Type _))
    (α : Tensor0SField (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M)
      (n := (∞ : WithTop ℕ∞)) 1)
    (x₀ : M) (c : 𝕜)
    (hpair :
      (fun y : M => α y (fun _ : Fin 1 => Z y)) =ᶠ[𝓝 x₀]
        fun _ : M => c) :
    (nabla0SFun (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M)
      1 cov X α x₀) (fun _ : Fin 1 => Z x₀) =
      -α x₀ (fun _ : Fin 1 => (cov (fun y : M => Z y) x₀) (X x₀)) := by
  rw [nabla0SFun_one_eval_smooth_slots (I := I) cov X Z α x₀]
  have hderiv_zero :
      extDerivFun (I := I) (fun y : M => α y (fun _ : Fin 1 => Z y))
          x₀ (X x₀) = 0 := by
    have hmf := Filter.EventuallyEq.mfderiv_eq
      (I := I) (I' := 𝓘(𝕜, 𝕜)) hpair
    unfold extDerivFun
    rw [hmf, mfderiv_const]
    rfl
  simp [hderiv_zero]

/-- Local-frame form of `nabla0SFun_one_eval_of_pair_eventually_const`.

If `Z` agrees near `x₀` with a local-frame vector `e_j`, the pairing
`α(Z)` is locally constant, and `α_{x₀}` is the `i`-th dual coframe at `x₀`,
then `(∇_X α)(e_j) = -Γ^i_j(X)`. -/
theorem nabla0SFun_one_eval_localFrame_dual
    {Idx : Type*} {u : Set M}
    (cov : CovariantDerivative I E (TangentSpace I : M -> Type _))
    (X Z : ContMDiffSection I E (∞ : WithTop ℕ∞) (TangentSpace I : M -> Type _))
    (α : Tensor0SField (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M)
      (n := (∞ : WithTop ℕ∞)) 1)
    (frame : Idx -> (x : M) -> TangentSpace I x)
    (hframe : IsLocalFrameOn I E 1 frame u)
    (hu : IsOpen u) {x₀ : M} (hx₀ : x₀ ∈ u) (i j : Idx) (c : 𝕜)
    (hZ : (fun y : M => Z y) =ᶠ[𝓝 x₀] fun y : M => frame j y)
    (hpair :
      (fun y : M => α y (fun _ : Fin 1 => Z y)) =ᶠ[𝓝 x₀]
        fun _ : M => c)
    (hα_eval : ∀ W : TangentSpace I x₀,
      α x₀ (fun _ : Fin 1 => W) = hframe.coeff i x₀ W) :
    (nabla0SFun (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M)
      1 cov X α x₀) (fun _ : Fin 1 => Z x₀) =
      -christoffelAlongInFrame cov frame hframe x₀ (X x₀) j i := by
  rw [nabla0SFun_one_eval_of_pair_eventually_const
    (I := I) cov X Z α x₀ c hpair]
  have hZ_mdiff : MDiffAt (T% (fun y : M => Z y)) x₀ :=
    Z.contMDiff.contMDiffAt.mdifferentiableAt (by simp)
  have hframe_mdiff : MDiffAt (T% (frame j)) x₀ :=
    (hframe.contMDiffAt hu hx₀ j).mdifferentiableAt one_ne_zero
  have hcov :
      cov (fun y : M => Z y) x₀ = cov (frame j) x₀ :=
    cov.isCovariantDerivativeOnUniv.congr_of_eventuallyEq
      hZ_mdiff hframe_mdiff (by simp) hZ
  rw [hcov]
  simp [christoffelAlongInFrame, hα_eval]

set_option backward.isDefEq.respectTransparency false in
/-- Unbundled one-form version of
`nabla0SFun_one_eval_of_pair_eventually_const`.

This is the form consumed by the mixed-tensor moving-slot bridge, whose upper
input correction is written with `localCovariantDerivTensor0SAt`. -/
theorem localCovariantDerivTensor0SAt_one_eval_of_pair_eventually_const
    (cov : CovariantDerivative I E (TangentSpace I : M -> Type _))
    (X Z : ContMDiffSection I E (∞ : WithTop ℕ∞) (TangentSpace I : M -> Type _))
    (α : Tensor0SField (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M)
      (n := (∞ : WithTop ℕ∞)) 1)
    (x₀ : M) (c : 𝕜)
    (hpair :
      (fun y : M => α y (fun _ : Fin 1 => Z y)) =ᶠ[𝓝 x₀]
        fun _ : M => c) :
    (localCovariantDerivTensor0SAt
      (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M) 1 cov X
      (fun y : M => α y) x₀) (fun _ : Fin 1 => Z x₀) =
      -α x₀ (fun _ : Fin 1 => (cov (fun y : M => Z y) x₀) (X x₀)) := by
  let β : (y : M) -> Tensor0SSpace (𝕜 := 𝕜) (E := E) (H := H)
      (I := I) (M := M) 1 y := fun y => α y
  let V : Fin 1 -> (y : M) -> TangentSpace I y := fun _ y => Z y
  have hpair_mdiff : MDifferentiableAt I 𝓘(𝕜, 𝕜)
      (fun y : M => β y (fun a : Fin 1 => V a y)) x₀ := by
    have hpair' :
        (fun y : M => β y (fun a : Fin 1 => V a y)) =ᶠ[𝓝 x₀]
          fun _ : M => c := by
      simpa [β, V] using hpair
    exact hpair'.mdifferentiableAt_iff.mpr mdifferentiableAt_const
  have hβ_cont :
      ContMDiffAt I (I.prod 𝓘(𝕜, Tensor0SModel 1 𝕜 E))
        (∞ : WithTop ℕ∞)
        (fun y : M =>
          (⟨y, β y⟩ :
            TotalSpace (Tensor0SModel 1 𝕜 E)
              (fun y : M => Tensor0SSpace 1 I y))) x₀ := by
    simpa [β] using α.contMDiff x₀
  have hβmodel :
      DifferentiableWithinAt 𝕜
        (tensor0SModelInChart (𝕜 := 𝕜) (E := E) (H := H) (I := I)
          (M := M) 1 x₀ β)
        (Set.range I) (extChartAt I x₀ x₀) :=
    tensor0SModelInChart_differentiableWithinAt_center_of_contMDiffAt
      (I := I) β x₀ hβ_cont
  have hV_at : ∀ a : Fin 1,
      ContMDiffAt I (I.prod 𝓘(𝕜, E)) (∞ : WithTop ℕ∞)
        (fun y : M =>
          (⟨y, V a y⟩ : TotalSpace E (TangentSpace I : M -> Type _))) x₀ := by
    intro a
    simpa [V] using Z.contMDiff.contMDiffAt
  have hV : ∀ a : Fin 1, MDiffAt (T% (V a)) x₀ :=
    fun a => (hV_at a).mdifferentiableAt (by simp)
  have hVmodel : ∀ a : Fin 1,
      DifferentiableWithinAt 𝕜
        (tangentFieldModelInChart (𝕜 := 𝕜) (I := I) x₀ (V a))
        (Set.range I) (extChartAt I x₀ x₀) :=
    fun a =>
      tangentFieldModelInChart_differentiableWithinAt_center_of_contMDiffAt
        (I := I) (V a) x₀ (hV_at a)
  have hcoord : ∀ a : Fin 1, ∀ i : Fin (Module.finrank 𝕜 E),
      MDifferentiableAt I 𝓘(𝕜, 𝕜)
        (fun y : M =>
          (Module.finBasis 𝕜 E).coord i
            (tangentFieldModelInChart (𝕜 := 𝕜) (I := I) x₀ (V a)
              (extChartAt I x₀ y))) x₀ :=
    fun a i =>
      tangentFieldModelInChart_coord_mdiffAt_center_of_contMDiffAt
        (I := I) (V a) x₀ (hV_at a) i
  have hraw :=
    localCovariantDerivTensor0SAt_eval_moving_raw
      (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M)
      (r := 1) cov X β V x₀ hpair_mdiff hβmodel hV hVmodel hcoord
  have hderiv_zero :
      extDerivFun (I := I) (fun y : M => β y (fun a : Fin 1 => V a y))
          x₀ (X x₀) = 0 := by
    have hpair' :
        (fun y : M => β y (fun a : Fin 1 => V a y)) =ᶠ[𝓝 x₀]
          fun _ : M => c := by
      simpa [β, V] using hpair
    have hmf := Filter.EventuallyEq.mfderiv_eq
      (I := I) (I' := 𝓘(𝕜, 𝕜)) hpair'
    unfold extDerivFun
    rw [hmf, mfderiv_const]
    rfl
  have hupdate :
      Function.update (fun b : Fin 1 => Z x₀) 0
          ((cov (fun y : M => Z y) x₀) (X x₀)) =
        fun _ : Fin 1 => (cov (fun y : M => Z y) x₀) (X x₀) := by
    funext q
    fin_cases q
    simp
  calc
    (localCovariantDerivTensor0SAt
      (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M) 1 cov X
      (fun y : M => α y) x₀) (fun _ : Fin 1 => Z x₀)
        = extDerivFun (I := I) (fun y : M => β y (fun a : Fin 1 => V a y))
            x₀ (X x₀) -
          ∑ a : Fin 1,
            β x₀
              (Function.update (fun b : Fin 1 => V b x₀) a
                ((cov (V a) x₀) (X x₀))) := by
          simpa [β, V] using hraw
    _ = -α x₀ (fun _ : Fin 1 => (cov (fun y : M => Z y) x₀) (X x₀)) := by
          simp [β, V, hderiv_zero, hupdate]

/-- Unbundled local-frame coframe formula:
`(∇_X θ^i)(e_j) = -Γ^i_j(X)`.

This is the same statement as `nabla0SFun_one_eval_localFrame_dual`, but in
the `localCovariantDerivTensor0SAt` form used by the mixed-tensor moving-slot
component theorem. -/
theorem localCovariantDerivTensor0SAt_one_eval_localFrame_dual
    {Idx : Type*} {u : Set M}
    (cov : CovariantDerivative I E (TangentSpace I : M -> Type _))
    (X Z : ContMDiffSection I E (∞ : WithTop ℕ∞) (TangentSpace I : M -> Type _))
    (α : Tensor0SField (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M)
      (n := (∞ : WithTop ℕ∞)) 1)
    (frame : Idx -> (x : M) -> TangentSpace I x)
    (hframe : IsLocalFrameOn I E 1 frame u)
    (hu : IsOpen u) {x₀ : M} (hx₀ : x₀ ∈ u) (i j : Idx) (c : 𝕜)
    (hZ : (fun y : M => Z y) =ᶠ[𝓝 x₀] fun y : M => frame j y)
    (hpair :
      (fun y : M => α y (fun _ : Fin 1 => Z y)) =ᶠ[𝓝 x₀]
        fun _ : M => c)
    (hα_eval : ∀ W : TangentSpace I x₀,
      α x₀ (fun _ : Fin 1 => W) = hframe.coeff i x₀ W) :
    (localCovariantDerivTensor0SAt
      (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M) 1 cov X
      (fun y : M => α y) x₀) (fun _ : Fin 1 => Z x₀) =
      -christoffelAlongInFrame cov frame hframe x₀ (X x₀) j i := by
  rw [localCovariantDerivTensor0SAt_one_eval_of_pair_eventually_const
    (I := I) cov X Z α x₀ c hpair]
  have hZ_mdiff : MDiffAt (T% (fun y : M => Z y)) x₀ :=
    Z.contMDiff.contMDiffAt.mdifferentiableAt (by simp)
  have hframe_mdiff : MDiffAt (T% (frame j)) x₀ :=
    (hframe.contMDiffAt hu hx₀ j).mdifferentiableAt one_ne_zero
  have hcov :
      cov (fun y : M => Z y) x₀ = cov (frame j) x₀ :=
    cov.isCovariantDerivativeOnUniv.congr_of_eventuallyEq
      hZ_mdiff hframe_mdiff (by simp) hZ
  rw [hcov]
  simp [christoffelAlongInFrame, hα_eval]

/-- A one-form section which pairs with local frame extensions as the `i`-th
Kronecker delta is locally the `i`-th dual coframe.

The statement is total as a section-valued eventual equality; on the frame
domain it identifies `α y` with the tensor-basis covector supplied by
`hframe.toBasisAt`. -/
theorem oneForm_eventually_eq_localFrame_dual
    {Idx : Type*} [Fintype Idx] [DecidableEq Idx] {u : Set M}
    (Z : Idx -> ContMDiffSection I E (∞ : WithTop ℕ∞)
      (TangentSpace I : M -> Type _))
    (α : Tensor0SField (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M)
      (n := (∞ : WithTop ℕ∞)) 1)
    (frame : Idx -> (x : M) -> TangentSpace I x)
    (hframe : IsLocalFrameOn I E 1 frame u)
    {x₀ : M} (i : Idx)
    (hZ : ∀ j : Idx,
      (fun y : M => Z j y) =ᶠ[𝓝 x₀] fun y : M => frame j y)
    (hpair : ∀ j : Idx,
      (fun y : M => α y (fun _ : Fin 1 => Z j y)) =ᶠ[𝓝 x₀]
        fun _ : M => if j = i then (1 : 𝕜) else 0) :
    ∀ᶠ y in 𝓝 x₀, ∀ hy : y ∈ u,
      α y =
        basisTensor0S (I := I) (hframe.toBasisAt hy) (fun _ : Fin 1 => i) := by
  classical
  have hZall : ∀ᶠ y in 𝓝 x₀, ∀ j : Idx, Z j y = frame j y := by
    exact Filter.eventually_all.mpr hZ
  have hpairall : ∀ᶠ y in 𝓝 x₀, ∀ j : Idx,
      α y (fun _ : Fin 1 => Z j y) = if j = i then (1 : 𝕜) else 0 := by
    exact Filter.eventually_all.mpr hpair
  filter_upwards [hZall, hpairall] with y hZy hpairy
  intro hy
  apply ext0S_basis (I := I) (hframe.toBasisAt hy)
  intro slots
  let j := slots 0
  have hslots_frame :
      (fun a : Fin 1 => frame (slots a) y) =
        fun _ : Fin 1 => frame j y := by
    funext q
    fin_cases q
    rfl
  have hbasis_slots :
      (fun a : Fin 1 => hframe.toBasisAt hy (slots a)) =
        fun a : Fin 1 => frame (slots a) y := by
    funext q
    simp [IsLocalFrameOn.toBasisAt_coe]
  have hleft :
      component0S (I := I) (hframe.toBasisAt hy) (α y) slots =
        if j = i then (1 : 𝕜) else 0 := by
    rw [component0S_apply, hbasis_slots, hslots_frame]
    simpa [j, hZy j] using hpairy j
  have hdelta :
      (if j = i then (1 : 𝕜) else 0) =
        (if (fun _ : Fin 1 => i) = slots then (1 : 𝕜) else 0) := by
    by_cases hji : j = i
    · have hslots : (fun _ : Fin 1 => i) = slots := by
        funext q
        fin_cases q
        simpa [j] using hji.symm
      simp [hji, hslots]
    · have hslots : (fun _ : Fin 1 => i) ≠ slots := by
        intro h
        have hij : i = j := by
          simpa [j] using congrFun h 0
        exact hji hij.symm
      simp [hji, hslots]
  calc
    component0S (I := I) (hframe.toBasisAt hy) (α y) slots
        = if j = i then (1 : 𝕜) else 0 := hleft
    _ = if (fun _ : Fin 1 => i) = slots then (1 : 𝕜) else 0 := hdelta
    _ = component0S (I := I) (hframe.toBasisAt hy)
        (basisTensor0S (I := I) (hframe.toBasisAt hy)
          (fun _ : Fin 1 => i)) slots := by
          rw [basisTensor0S_component]

/-- Local-frame coframe derivative as a full one-form identity.

If `α` is the `i`-th dual coframe at `x₀` and the sections `Z j` locally
realize the frame vectors with the expected dual pairings, then
`∇_X α = -∑_p Γ^i_p(X) θ^p` at `x₀`.  This is the tensor-level form consumed by
mixed-tensor moving-slot arguments. -/
theorem localCovariantDerivTensor0SAt_one_localFrame_dual_eq
    {Idx : Type*} [Fintype Idx] [DecidableEq Idx] {u : Set M}
    (cov : CovariantDerivative I E (TangentSpace I : M -> Type _))
    (X : ContMDiffSection I E (∞ : WithTop ℕ∞) (TangentSpace I : M -> Type _))
    (Z : Idx -> ContMDiffSection I E (∞ : WithTop ℕ∞)
      (TangentSpace I : M -> Type _))
    (α : Tensor0SField (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M)
      (n := (∞ : WithTop ℕ∞)) 1)
    (frame : Idx -> (x : M) -> TangentSpace I x)
    (hframe : IsLocalFrameOn I E 1 frame u)
    (hu : IsOpen u) {x₀ : M} (hx₀ : x₀ ∈ u) (i : Idx)
    (hZ : ∀ j : Idx,
      (fun y : M => Z j y) =ᶠ[𝓝 x₀] fun y : M => frame j y)
    (hpair : ∀ j : Idx,
      (fun y : M => α y (fun _ : Fin 1 => Z j y)) =ᶠ[𝓝 x₀]
        fun _ : M => if j = i then (1 : 𝕜) else 0)
    (hα_eval : ∀ W : TangentSpace I x₀,
      α x₀ (fun _ : Fin 1 => W) = hframe.coeff i x₀ W) :
    localCovariantDerivTensor0SAt
        (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M) 1 cov X
        (fun y : M => α y) x₀ =
      -∑ p : Idx,
        christoffelAlongInFrame cov frame hframe x₀ (X x₀) p i •
          basisTensor0S (I := I) (hframe.toBasisAt hx₀)
            (fun _ : Fin 1 => p) := by
  classical
  let basis := hframe.toBasisAt hx₀
  apply ext0S_basis (I := I) basis
  intro slots
  let j := slots 0
  have hZx : Z j x₀ = frame j x₀ := by
    exact (hZ j).eq_of_nhds
  have hleft :=
    localCovariantDerivTensor0SAt_one_eval_localFrame_dual
      (I := I) cov X (Z j) α frame hframe hu hx₀ i j
      (if j = i then (1 : 𝕜) else 0) (hZ j) (hpair j) hα_eval
  have hslots_frame :
      (fun a : Fin 1 => frame (slots a) x₀) =
        fun _ : Fin 1 => frame j x₀ := by
    funext q
    fin_cases q
    rfl
  have hbasis_slots :
      (fun a : Fin 1 => basis (slots a)) =
        fun a : Fin 1 => frame (slots a) x₀ := by
    funext q
    simp [basis, IsLocalFrameOn.toBasisAt_coe]
  have hleft_comp :
      component0S (I := I) basis
          (localCovariantDerivTensor0SAt
            (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M) 1 cov X
            (fun y : M => α y) x₀) slots =
        -christoffelAlongInFrame cov frame hframe x₀ (X x₀) j i := by
    rw [component0S_apply, hbasis_slots, hslots_frame]
    simpa [basis, j, hZx] using hleft
  have hsum :
      (∑ p : Idx,
        christoffelAlongInFrame cov frame hframe x₀ (X x₀) p i *
          (if (fun _ : Fin 1 => p) = slots then (1 : 𝕜) else 0)) =
        christoffelAlongInFrame cov frame hframe x₀ (X x₀) j i := by
    rw [Finset.sum_eq_single j]
    · have heq : (fun _ : Fin 1 => j) = slots := by
        funext q
        fin_cases q
        rfl
      simp [heq]
    · intro p _ hp
      have hne : (fun _ : Fin 1 => p) ≠ slots := by
        intro h
        have hpj : p = j := by
          simpa [j] using congrFun h 0
        exact hp hpj
      simp [hne]
    · intro hnot
      exact False.elim (hnot (Finset.mem_univ j))
  have hsum_eval :
      (∑ p : Idx,
        christoffelAlongInFrame cov frame hframe x₀ (X x₀) p i *
          (basisTensor0S (I := I) basis (fun _ : Fin 1 => p))
            (fun a : Fin 1 => basis (slots a))) =
        christoffelAlongInFrame cov frame hframe x₀ (X x₀) j i := by
    rw [Finset.sum_eq_single j]
    · simp [basisTensor0S_apply, j]
    · intro p _ hp
      have hzero :
          (basisTensor0S (I := I) basis (fun _ : Fin 1 => p))
              (fun a : Fin 1 => basis (slots a)) = 0 := by
        simp [basisTensor0S_apply, j, hp]
      rw [hzero]
      simp
    · intro hnot
      exact False.elim (hnot (Finset.mem_univ j))
  have hright_apply :
      ((∑ p : Idx,
        christoffelAlongInFrame cov frame hframe x₀ (X x₀) p i •
          basisTensor0S (I := I) basis (fun _ : Fin 1 => p))
          (fun a : Fin 1 => basis (slots a))) =
        christoffelAlongInFrame cov frame hframe x₀ (X x₀) j i := by
    rw [tensor0S_sum_apply]
    simpa [ContinuousMultilinearMap.smul_apply] using hsum_eval
  calc
    component0S (I := I) basis
        (localCovariantDerivTensor0SAt
          (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M) 1 cov X
          (fun y : M => α y) x₀) slots
        = -christoffelAlongInFrame cov frame hframe x₀ (X x₀) j i := hleft_comp
    _ = component0S (I := I) basis
        (-∑ p : Idx,
          christoffelAlongInFrame cov frame hframe x₀ (X x₀) p i •
            basisTensor0S (I := I) basis (fun _ : Fin 1 => p)) slots := by
          rw [component0S_apply]
          simpa using (congrArg Neg.neg hright_apply).symm

private theorem coordinateFrame_covariantDeriv_apply_contMDiffAt
    (cov : CovariantDerivative I E (TangentSpace I : M -> Type _))
    (hcov : CovariantDerivative.ContMDiffCovariantDerivativeLocally cov
      (∞ : WithTop ℕ∞))
    (X : ContMDiffSection I E (∞ : WithTop ℕ∞) (TangentSpace I : M -> Type _))
    (x₀ : M) (j : CoordinateIdx (𝕜 := 𝕜) E) :
    ContMDiffAt I (I.prod 𝓘(𝕜, E)) (∞ : WithTop ℕ∞)
      (fun p : M =>
        (⟨p, (cov (coordinateFrameAt (I := I) x₀ j) p) (X p)⟩ :
          TotalSpace E (TangentSpace I : M -> Type _))) x₀ := by
  let u := coordinateFrameSet (I := I) x₀
  let frame := coordinateFrameAt (I := I) x₀
  have hu : IsOpen u := coordinateFrameSet_open (I := I) x₀
  have hx₀ : x₀ ∈ u := coordinateFrameAt_mem (I := I) x₀
  have hframe_smooth :
      CMDiff[u] ((∞ : WithTop ℕ∞) + 1) (T% (frame j)) := by
    exact ((coordinateFrameAt_isLocalFrame (I := I) x₀).contMDiffOn j).of_le
      (by simp)
  have hcov_frame :
      ContMDiffOn I (I.prod 𝓘(𝕜, E →L[𝕜] E)) (∞ : WithTop ℕ∞)
        (fun p : M =>
          (⟨p, cov (frame j) p⟩ :
            TotalSpace (E →L[𝕜] E)
              (fun p : M => TangentSpace I p →L[𝕜] TangentSpace I p)))
        u := by
    simpa [u, frame] using (hcov hu).contMDiff hframe_smooth
  have hX_on :
      CMDiff[u] (∞ : WithTop ℕ∞) (T% (fun p : M => X p)) :=
    (X.contMDiff.of_le (by simp :
      (∞ : WithTop ℕ∞) ≤ (∞ : WithTop ℕ∞))).contMDiffOn
  have hW_on :
      ContMDiffOn I (I.prod 𝓘(𝕜, E)) (∞ : WithTop ℕ∞)
        (fun p : M =>
          (⟨p, (cov (frame j) p) (X p)⟩ :
            TotalSpace E (TangentSpace I : M -> Type _)))
        u := by
    simpa [frame] using hcov_frame.clm_bundle_apply hX_on
  exact (hW_on x₀ hx₀).contMDiffAt (hu.mem_nhds hx₀)

set_option backward.isDefEq.respectTransparency false in
/-- Smoothness of the scalar function obtained by evaluating `nabla0SFun 1`
on a smooth vector field.

This is the intrinsic one-form smoothness input: use the moving-slot formula,
then prove smoothness of the exterior-derivative term and the correction term
separately. -/
theorem nabla0SFun_one_eval_contMDiff
    (cov : CovariantDerivative I E (TangentSpace I : M -> Type _))
    (hcov : CovariantDerivative.ContMDiffCovariantDerivative cov (∞ : WithTop ℕ∞))
    (X Z : ContMDiffSection I E (∞ : WithTop ℕ∞) (TangentSpace I : M -> Type _))
    (α : Tensor0SField (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M)
      (n := (∞ : WithTop ℕ∞)) 1) :
    ContMDiff I 𝓘(𝕜, 𝕜) (∞ : WithTop ℕ∞)
      (fun p : M =>
        (nabla0SFun (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M)
          1 cov X α p) (fun _ : Fin 1 => Z p)) := by
  let pair : M -> 𝕜 := fun y => α y (fun _ : Fin 1 => Z y)
  let Xinf : ContMDiffSection I E (∞ : WithTop ℕ∞) (TangentSpace I : M -> Type _) :=
    ⟨fun p : M => X p, X.contMDiff.of_le (by simp)⟩
  let Zinf : ContMDiffSection I E (∞ : WithTop ℕ∞) (TangentSpace I : M -> Type _) :=
    ⟨fun p : M => Z p, Z.contMDiff.of_le (by simp)⟩
  let αinf : Tensor0SField (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M)
      (n := (∞ : WithTop ℕ∞)) 1 :=
    ⟨fun p : M => α p, α.contMDiff.of_le (by simp)⟩
  have hpair : ContMDiff I 𝓘(𝕜, 𝕜) (∞ : WithTop ℕ∞) pair := by
    simpa [pair, αinf, Zinf] using
      (TensorMultilinear.contMDiff_tensor0SField_apply
        (E := E) (H := H) (I := I) (M := M) (n := 1)
        αinf (fun _ : Fin 1 => Zinf))
  have hderiv :
      ContMDiff I 𝓘(𝕜, 𝕜) (∞ : WithTop ℕ∞)
        (fun p : M => extDerivFun (I := I) pair p (X p)) :=
    extDerivFun_apply_contMDiff (I := I) pair hpair Xinf
  let W : (p : M) -> TangentSpace I p :=
    fun p : M => (cov (fun q : M => Z q) p) (X p)
  have hWtop :
      ContMDiff I (I.prod 𝓘(𝕜, E)) (∞ : WithTop ℕ∞)
        (fun p : M => (⟨p, W p⟩ :
          TotalSpace E (TangentSpace I : M -> Type _))) := by
    simpa [W] using
      (TensorLieDeriv.covariantDeriv_vectorField_contMDiff
        (𝕜 := 𝕜) (I := I) (M := M) cov hcov X Z)
  let Winf : ContMDiffSection I E (∞ : WithTop ℕ∞) (TangentSpace I : M -> Type _) :=
    ⟨W, hWtop.of_le (by simp)⟩
  have hcorr_raw :
      ContMDiff I 𝓘(𝕜, 𝕜) (∞ : WithTop ℕ∞)
        (fun p : M => αinf p (fun _ : Fin 1 => Winf p)) := by
    simpa using
      (TensorMultilinear.contMDiff_tensor0SField_apply
        (E := E) (H := H) (I := I) (M := M) (n := 1)
        αinf (fun _ : Fin 1 => Winf))
  have hcorr :
      ContMDiff I 𝓘(𝕜, 𝕜) (∞ : WithTop ℕ∞)
        (fun p : M => α p
          (fun _ : Fin 1 => (cov (fun q : M => Z q) p) (X p))) := by
    refine hcorr_raw.congr ?_
    intro p
    simp [αinf, Winf, W]
  have hmain :
      ContMDiff I 𝓘(𝕜, 𝕜) (∞ : WithTop ℕ∞)
        (fun p : M =>
          extDerivFun (I := I) pair p (X p) -
            α p (fun _ : Fin 1 => (cov (fun q : M => Z q) p) (X p))) :=
    hderiv.sub hcorr
  refine hmain.congr ?_
  intro p
  rw [nabla0SFun_one_eval_coordFrame_moving
    (I := I) cov X Z α p
    (modelDeriv_eq_coordDeriv0SAt (I := I) X p α)
    (fun j =>
      (coordinateFrame_coeff_contMDiffAt (I := I) Z p j).mdifferentiableAt
        (by simp))
    (fun j =>
        (oneForm_eval_coordinateFrame_contMDiffAt (I := I) α p j).mdifferentiableAt
        (by simp))]

set_option backward.isDefEq.respectTransparency false in
/-- Local coordinate-frame scalar smoothness for `nabla0SFun 1`.

This is the local-frame version of `nabla0SFun_one_eval_contMDiff`: the moving
slot is the chart-induced coordinate-frame field around `x₀`, which is only
known to be smooth locally. The proof uses
`ContMDiffCovariantDerivativeLocally`, not global smooth-section extension. -/
theorem nabla0SFun_one_eval_coordinateFrame_contMDiffAt
    (cov : CovariantDerivative I E (TangentSpace I : M -> Type _))
    (hcov : CovariantDerivative.ContMDiffCovariantDerivativeLocally cov
      (∞ : WithTop ℕ∞))
    (X : ContMDiffSection I E (∞ : WithTop ℕ∞) (TangentSpace I : M -> Type _))
    (α : Tensor0SField (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M)
      (n := (∞ : WithTop ℕ∞)) 1)
    (x₀ : M) (j : CoordinateIdx (𝕜 := 𝕜) E) :
    ContMDiffAt I 𝓘(𝕜, 𝕜) (∞ : WithTop ℕ∞)
      (fun p : M =>
        (nabla0SFun (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M)
          1 cov X α p)
          (fun _ : Fin 1 => coordinateFrameAt (I := I) x₀ j p)) x₀ := by
  let Z : (p : M) -> TangentSpace I p := coordinateFrameAt (I := I) x₀ j
  let pair : M -> 𝕜 := fun p => α p (fun _ : Fin 1 => Z p)
  let Xinf : ContMDiffSection I E (∞ : WithTop ℕ∞) (TangentSpace I : M -> Type _) :=
    ⟨fun p : M => X p, X.contMDiff.of_le (by simp)⟩
  let αinf : Tensor0SField (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M)
      (n := (∞ : WithTop ℕ∞)) 1 :=
    ⟨fun p : M => α p, α.contMDiff.of_le (by simp)⟩
  have hpair : ContMDiffAt I 𝓘(𝕜, 𝕜) (∞ : WithTop ℕ∞) pair x₀ := by
    simpa [pair, Z] using oneForm_eval_coordinateFrame_contMDiffAt
      (I := I) α x₀ j
  have hderiv :
      ContMDiffAt I 𝓘(𝕜, 𝕜) (∞ : WithTop ℕ∞)
        (fun p : M => extDerivFun (I := I) pair p (X p)) x₀ :=
    extDerivFun_apply_contMDiffAt (I := I) hpair Xinf
  let W : (p : M) -> TangentSpace I p :=
    fun p : M => (cov Z p) (X p)
  have hW :
      ContMDiffAt I (I.prod 𝓘(𝕜, E)) (∞ : WithTop ℕ∞)
        (fun p : M => (⟨p, W p⟩ : TotalSpace E (TangentSpace I : M -> Type _))) x₀ := by
    simpa [W, Z] using
      coordinateFrame_covariantDeriv_apply_contMDiffAt
        (I := I) cov hcov X x₀ j
  have hcorr_raw :
      ContMDiffAt I 𝓘(𝕜, 𝕜) (∞ : WithTop ℕ∞)
        (fun p : M => αinf p (fun _ : Fin 1 => W p)) x₀ := by
    simpa using
      (TensorMultilinear.contMDiffAt_section_apply
        (I := I) (M := M) (n := 1) (x₀ := x₀)
        (T := fun p : M => αinf p) αinf.contMDiff.contMDiffAt
        (v := fun _ : Fin 1 => W)
        (hv := fun _ : Fin 1 => hW))
  have hcorr :
      ContMDiffAt I 𝓘(𝕜, 𝕜) (∞ : WithTop ℕ∞)
        (fun p : M => α p (fun _ : Fin 1 => W p)) x₀ := by
    refine hcorr_raw.congr_of_eventuallyEq ?_
    filter_upwards with p
    simp [αinf]
  have hmain :
      ContMDiffAt I 𝓘(𝕜, 𝕜) (∞ : WithTop ℕ∞)
        (fun p : M =>
          extDerivFun (I := I) pair p (X p) -
            α p (fun _ : Fin 1 => W p)) x₀ :=
    hderiv.sub hcorr
  refine hmain.congr_of_eventuallyEq ?_
  filter_upwards [(coordinateFrameSet_open (I := I) x₀).mem_nhds
      (coordinateFrameAt_mem (I := I) x₀)] with p hp
  have hZ_at :
      ContMDiffAt I (I.prod 𝓘(𝕜, E)) (∞ : WithTop ℕ∞)
        (fun y : M => (⟨y, Z y⟩ : TotalSpace E (TangentSpace I : M -> Type _))) p := by
    simpa [Z] using
      (coordinateFrameAt_isLocalFrame (I := I) x₀).contMDiffAt
        (coordinateFrameSet_open (I := I) x₀) hp j
  rw [nabla0SFun_one_eval_coordFrame_moving_raw
    (I := I) cov X Z α p
    (modelDeriv_eq_coordDeriv0SAt (I := I) X p α)
    (fun k =>
      (coordinateFrame_coeff_contMDiffAt_of_contMDiffAt
        (I := I) Z hZ_at k).mdifferentiableAt (by simp))
    (fun k =>
      (oneForm_eval_coordinateFrame_contMDiffAt
        (I := I) α p k).mdifferentiableAt (by simp))
    (hZ_at.mdifferentiableAt (by simp))]

set_option backward.isDefEq.respectTransparency false in
/-- Local-frame proof that `nabla0SFun 1` is a smooth one-form section.

This avoids global extension of coordinate-frame fields. Smoothness is checked
in local tensor-bundle coordinates, whose basis coefficients are exactly the
scalar evaluations handled by
`nabla0SFun_one_eval_coordinateFrame_contMDiffAt`. -/
theorem nabla0SFun_one_contMDiff
    (cov : CovariantDerivative I E (TangentSpace I : M -> Type _))
    (hcov : CovariantDerivative.ContMDiffCovariantDerivativeLocally cov
      (∞ : WithTop ℕ∞))
    (X : ContMDiffSection I E (∞ : WithTop ℕ∞) (TangentSpace I : M -> Type _))
    (α : Tensor0SField (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M)
      (n := (∞ : WithTop ℕ∞)) 1) :
    letI := tensor0SBundle_topology (𝕜 := 𝕜) (E := E) (H := H) (I := I)
      (M := M) 1
    ContMDiff I (I.prod 𝓘(𝕜, Tensor0SModel 1 𝕜 E)) (∞ : WithTop ℕ∞)
      (fun p : M =>
        (⟨p, nabla0SFun (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M)
          1 cov X α p⟩ :
          TotalSpace (Tensor0SModel 1 𝕜 E) (fun p : M => Tensor0SSpace 1 I p))) := by
  letI := tensor0SBundle_topology (𝕜 := 𝕜) (E := E) (H := H) (I := I)
    (M := M) 1
  let F : (p : M) -> Tensor0SSpace (𝕜 := 𝕜) (E := E) (H := H) (I := I)
      (M := M) 1 p :=
    fun p : M =>
      nabla0SFun (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M)
        1 cov X α p
  let d := Module.finrank 𝕜 E
  let b : Module.Basis (Fin d) 𝕜 E := Module.finBasis 𝕜 E
  refine (contMDiff_multilinearSection_iff_coord (TangentSpace I)
    (∞ : WithTop ℕ∞) b F).mpr ?_
  intro σ x₀
  let j : CoordinateIdx (𝕜 := 𝕜) E := σ 0
  have hframe_eval :=
    nabla0SFun_one_eval_coordinateFrame_contMDiffAt
      (I := I) cov hcov X α x₀ j
  refine hframe_eval.congr_of_eventuallyEq ?_
  filter_upwards
    [(coordinateFrameSet_open (I := I) x₀).mem_nhds
      (coordinateFrameAt_mem (I := I) x₀)] with p hp
  have hslot :
      (fun a : Fin 1 =>
          (trivializationAt E (TangentSpace I : M -> Type _) x₀).symmL 𝕜 p
            (b (σ a))) =
        fun _ : Fin 1 => coordinateFrameAt (I := I) x₀ j p := by
    funext a
    fin_cases a
    have hp_src : p ∈ (chartAt H x₀).source := by
      simpa [coordinateFrameSet, coordinateTrivializationAt] using hp
    rw [coordinateFrameAt_apply_of_mem (I := I) (x₀ := x₀) (x := p) hp j]
    simpa [j, b] using
      congrArg
        (fun L : E →L[𝕜] TangentSpace I p => L (b j))
        (TangentBundle.symmL_trivializationAt (I := I) (𝕜 := 𝕜) hp_src)
  rw [continuousMultilinearMap_basis_repr]
  change ((trivializationAt (Tensor0SModel 1 𝕜 E)
      (Bundle.continuousMultilinearMap 𝕜 1 E (TangentSpace I : M -> Type _)) x₀
      ⟨p, F p⟩).2)
      (fun a : Fin 1 => b (σ a)) =
    (nabla0SFun (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M)
      1 cov X α p) (fun _ : Fin 1 => coordinateFrameAt (I := I) x₀ j p)
  change (F p).compContinuousLinearMap
      (fun _ : Fin 1 =>
        (trivializationAt E (TangentSpace I : M -> Type _) x₀).symmL 𝕜 p)
      (fun a : Fin 1 => b (σ a)) =
    F p (fun _ : Fin 1 => coordinateFrameAt (I := I) x₀ j p)
  rw [ContinuousMultilinearMap.compContinuousLinearMap_apply]
  rw [hslot]
end Coordinates
end RicciFlower
