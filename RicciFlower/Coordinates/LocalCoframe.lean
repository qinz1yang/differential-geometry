import RicciFlower.Coordinates.Tensor
import RicciFlower.VectorBundle.Frame
import RicciFlower.Tensor.RSTensor.LocalFrameRegularity

/-!
# Local coframes from tangent trivializations

This file records the small coordinate/tensor facts needed to turn a
trivialization-induced local frame into the corresponding smooth dual coframe.
It is kept below the HCG approximate-isometry layer.
-/

set_option autoImplicit false
set_option linter.style.longLine false
set_option linter.unusedSectionVars false

namespace RicciFlower
namespace Coordinates

noncomputable section

open Bundle
open scoped Manifold ContDiff Topology

variable
  {𝕜 : Type*} [NontriviallyNormedField 𝕜] [CompleteSpace 𝕜]
  {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
    [FiniteDimensional 𝕜 E]
  {H : Type*} [TopologicalSpace H]
  {I : ModelWithCorners 𝕜 E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

set_option backward.isDefEq.respectTransparency false in
/-- On the tangent-trivialization domain, a fixed tensor-bundle basis section
`Tensor0SSpace.constInChart` is the basis tensor of the local frame induced by
the same tangent trivialization and model basis. -/
theorem constInChart_eq_basis0S_trivFrame
    {Idx : Type*} [Fintype Idx] [DecidableEq Idx] {r : Nat}
    (x₀ : M) (b : Module.Basis Idx 𝕜 E)
    {x : M}
    (hx : x ∈ (trivializationAt E (TangentSpace I : M -> Type _) x₀).baseSet)
    (slots : Fin r -> Idx) :
    Tensor0SBundle.Tensor0SSpace.constInChart (𝕜 := 𝕜) (E := E) (H := H)
        (I := I) (M := M) r x₀
        ((Tensor0SBundle.continuousMultilinearMapBasis
          (𝕜 := 𝕜) (V := E) b r) slots) x =
      Tensor0SBundle.basisTensor0S (I := I)
        ((trivializationAt E (TangentSpace I : M -> Type _) x₀).basisAt b hx)
        slots := by
  classical
  let e := trivializationAt E (TangentSpace I : M -> Type _) x₀
  rw [Tensor0SBundle.Tensor0SSpace.constInChart]
  rw [Bundle.continuousMultilinearMap.triv_symmL_eq_compContinuousLinearMap
    (F := E) (E := TangentSpace I) x₀ x hx]
  ext v
  have hlin (w : TangentSpace I x) :
      (Trivialization.linearMapAt 𝕜 (trivializationAt E (TangentSpace I) x₀) x) w =
        (trivializationAt E (TangentSpace I) x₀ ⟨x, w⟩).2 := by
    change (trivializationAt E (TangentSpace I) x₀).linearMapAt 𝕜 x w = _
    rw [(trivializationAt E (TangentSpace I) x₀).coe_linearMapAt_of_mem (R := 𝕜) hx]
  simp [Tensor0SBundle.basisTensor0S, Tensor0SBundle.tensor0SBasis,
    Tensor0SBundle.continuousMultilinearMapBasis_apply,
    Tensor0SBundle.continuousMultilinearMapBasisElem,
    Tensor0SBundle.coframeOfBasis,
    ContinuousMultilinearMap.compContinuousLinearMap_apply,
    Bundle.Trivialization.continuousLinearMapAt_apply,
    Bundle.Trivialization.basisAt, hlin]

/-- A chart-constant covector from the tangent trivialization is dual to the
local frame induced by the same trivialization and model basis. -/
theorem constInChart_one_eval_trivFrame
    {Idx : Type*} [Fintype Idx] [DecidableEq Idx]
    (x₀ : M) (b : Module.Basis Idx 𝕜 E)
    {x : M}
    (hx : x ∈ (trivializationAt E (TangentSpace I : M -> Type _) x₀).baseSet)
    (i j : Idx) :
    Tensor0SBundle.Tensor0SSpace.constInChart (𝕜 := 𝕜) (E := E) (H := H)
        (I := I) (M := M) 1 x₀
        ((Tensor0SBundle.continuousMultilinearMapBasis
          (𝕜 := 𝕜) (V := E) b 1) (fun _ : Fin 1 => i)) x
        (fun _ : Fin 1 =>
          (trivializationAt E (TangentSpace I : M -> Type _) x₀).localFrame b j x)
      = if j = i then 1 else 0 := by
  classical
  let e := trivializationAt E (TangentSpace I : M -> Type _) x₀
  rw [constInChart_eq_basis0S_trivFrame (𝕜 := 𝕜) (I := I) (M := M)
    (Idx := Idx) (r := 1) x₀ b hx (fun _ : Fin 1 => i)]
  rw [Tensor0SBundle.basisTensor0S_apply]
  rw [e.localFrame_apply_of_mem_baseSet (b := b) (i := j) hx]
  have hround : (e ⟨x, e.symm x (b j)⟩ : M × E).2 = b j := by
    exact congrArg Prod.snd (e.apply_mk_symm hx (b j))
  simp [Bundle.Trivialization.basisAt, Finsupp.single_apply, hround, e]

/-- Eventual pairing form of `constInChart_one_eval_trivFrame`: if smooth
sections `Z j` realize the trivialization-induced local frame near `x₀`, then
the chart-constant dual covector pairs with them as the Kronecker delta. -/
theorem constInChart_one_pair_eventually_trivFrame
    {Idx : Type*} [Fintype Idx] [DecidableEq Idx]
    (x₀ : M) (b : Module.Basis Idx 𝕜 E)
    (Z : Idx -> ContMDiffSection I E (∞ : WithTop ℕ∞)
      (TangentSpace I : M -> Type _))
    (hZ : ∀ j : Idx,
      (fun y : M => Z j y) =ᶠ[𝓝 x₀]
        fun y : M =>
          (trivializationAt E (TangentSpace I : M -> Type _) x₀).localFrame b j y)
    (i j : Idx) :
    (fun y : M =>
        Tensor0SBundle.Tensor0SSpace.constInChart
          (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M) 1 x₀
          ((Tensor0SBundle.continuousMultilinearMapBasis
            (𝕜 := 𝕜) (V := E) b 1) (fun _ : Fin 1 => i)) y
          (fun _ : Fin 1 => Z j y)) =ᶠ[𝓝 x₀]
      fun _ : M => if j = i then (1 : 𝕜) else 0 := by
  let e := trivializationAt E (TangentSpace I : M -> Type _) x₀
  have hx₀ : x₀ ∈ e.baseSet := by
    exact mem_baseSet_trivializationAt E (TangentSpace I : M -> Type _) x₀
  filter_upwards [hZ j, e.open_baseSet.mem_nhds hx₀] with y hZy hy
  rw [hZy]
  exact constInChart_one_eval_trivFrame
    (𝕜 := 𝕜) (I := I) (M := M) x₀ b (by simpa [e] using hy) i j

section Real

variable
  {F : Type*} [NormedAddCommGroup F] [NormedSpace Real F]
    [FiniteDimensional Real F]
  {G : Type*} [TopologicalSpace G]
  {J : ModelWithCorners Real F G}
  {N : Type*} [TopologicalSpace N] [ChartedSpace G N] [IsManifold J ∞ N]
    [T2Space N]

/-- A realized `LocalChartAt` frame admits global smooth section extensions
which agree with it near the chart center.

This is the general local-chart frame producer.  The dual coframe producer below
is still only available for the default/tangent-trivialization chart until the
project has an induced smooth dual-coframe section API for arbitrary tangent
trivializations. -/
theorem existsChartFrameSec
    {x₀ : N} {C : LocalChartAt (I := J) x₀} (F₀ : C.Frame) :
    ∃ Z : CoordinateIdx (𝕜 := Real) F -> ContMDiffSection J F (∞ : WithTop ℕ∞)
        (TangentSpace J : N -> Type _),
      ∀ j : CoordinateIdx (𝕜 := Real) F,
        (fun y : N => Z j y) =ᶠ[𝓝 x₀]
          fun y : N => F₀.frame j y := by
  obtain ⟨Z, hZ⟩ :=
    F₀.hframe.exists_contMDiffSection_eqOn_nhd F₀.isOpen_domain F₀.mem_base
  refine ⟨Z, fun j => ?_⟩
  exact hZ.mono fun _ hy => hy j

/-- The full-source frame attached to a `LocalChartAt` admits smooth section
extensions near the chart center. -/
theorem existsChartToFrameSec
    {x₀ : N} (C : LocalChartAt (I := J) x₀) :
    ∃ Z : CoordinateIdx (𝕜 := Real) F -> ContMDiffSection J F (∞ : WithTop ℕ∞)
        (TangentSpace J : N -> Type _),
      ∀ j : CoordinateIdx (𝕜 := Real) F,
        (fun y : N => Z j y) =ᶠ[𝓝 x₀]
          fun y : N => (C.toFrame).frame j y :=
  existsChartFrameSec (J := J) C.toFrame

/-- The local frame induced by a tangent trivialization admits global smooth
section extensions which agree with it near the center. -/
theorem existsTrivFrameSec
    {Idx : Type*}
    (x₀ : N) (b : Module.Basis Idx Real F) :
    ∃ Z : Idx -> ContMDiffSection J F (∞ : WithTop ℕ∞)
        (TangentSpace J : N -> Type _),
      ∀ j : Idx,
        (fun y : N => Z j y) =ᶠ[𝓝 x₀]
          fun y : N =>
            (trivializationAt F (TangentSpace J : N -> Type _) x₀).localFrame b j y := by
  let e := trivializationAt F (TangentSpace J : N -> Type _) x₀
  have hx₀ : x₀ ∈ e.baseSet :=
    mem_baseSet_trivializationAt F (TangentSpace J : N -> Type _) x₀
  let hframe := e.isLocalFrameOn_localFrame_baseSet J (∞ : WithTop ℕ∞) b
  obtain ⟨Z, hZ⟩ := hframe.exists_contMDiffSection_eqOn_nhd e.open_baseSet hx₀
  refine ⟨Z, fun j => ?_⟩
  exact hZ.mono fun _ hy => hy j

/-- Combined local-frame section and dual-pairing producer for a tangent
trivialization.  The one-form here is still the supplied chart-constant
covector; a later wrapper may extend that covector to a global tensor field. -/
theorem existsTrivFramePair
    {Idx : Type*} [Fintype Idx] [DecidableEq Idx]
    (x₀ : N) (b : Module.Basis Idx Real F) :
    ∃ Z : Idx -> ContMDiffSection J F (∞ : WithTop ℕ∞)
        (TangentSpace J : N -> Type _),
      (∀ j : Idx,
        (fun y : N => Z j y) =ᶠ[𝓝 x₀]
          fun y : N =>
            (trivializationAt F (TangentSpace J : N -> Type _) x₀).localFrame b j y) ∧
      (∀ i j : Idx,
        (fun y : N =>
          Tensor0SBundle.Tensor0SSpace.constInChart
            (𝕜 := Real) (E := F) (H := G) (I := J) (M := N) 1 x₀
            ((Tensor0SBundle.continuousMultilinearMapBasis
              (𝕜 := Real) (V := F) b 1) (fun _ : Fin 1 => i)) y
            (fun _ : Fin 1 => Z j y)) =ᶠ[𝓝 x₀]
          fun _ : N => if j = i then (1 : Real) else 0) := by
  obtain ⟨Z, hZ⟩ := existsTrivFrameSec (J := J) x₀ b
  refine ⟨Z, hZ, fun i j => ?_⟩
  exact constInChart_one_pair_eventually_trivFrame
    (𝕜 := Real) (I := J) (M := N) x₀ b Z hZ i j

set_option backward.isDefEq.respectTransparency false in
/-- A chart-constant covariant tensor in the tensor-bundle trivialization has a
global smooth tensor-field section extension which agrees with it near the
chart center. -/
theorem existsConstTensor0S
    (r : Nat) (x₀ : N) (β : Tensor0SBundle.Tensor0SModel r Real F) :
    ∃ α : Tensor0SBundle.Tensor0SField
        (𝕜 := Real) (E := F) (H := G) (I := J) (M := N)
        (n := (∞ : WithTop ℕ∞)) r,
      (fun y : N =>
        (⟨y, α y⟩ :
          TotalSpace (Tensor0SBundle.Tensor0SModel r Real F)
            (fun p : N => Tensor0SBundle.Tensor0SSpace r J p))) =ᶠ[𝓝 x₀]
        fun y : N =>
          (⟨y,
            Tensor0SBundle.Tensor0SSpace.constInChart
              (𝕜 := Real) (E := F) (H := G) (I := J) (M := N) r x₀ β y⟩ :
            TotalSpace (Tensor0SBundle.Tensor0SModel r Real F)
              (fun p : N => Tensor0SBundle.Tensor0SSpace r J p)) := by
  classical
  haveI : IsManifold J ((∞ : WithTop ℕ∞) + 1) N := by
    simpa using (inferInstance : IsManifold J (∞ : WithTop ℕ∞) N)
  letI := Tensor0SBundle.tensor0SBundle_topology
    (𝕜 := Real) (E := F) (H := G) (I := J) (M := N) r
  letI := Tensor0SBundle.tensor0SBundle_fiber
    (𝕜 := Real) (E := F) (H := G) (I := J) (M := N) r
  letI := Tensor0SBundle.tensor0SBundle_vector
    (𝕜 := Real) (E := F) (H := G) (I := J) (M := N) r
  letI := Tensor0SBundle.tensor0SBundle_smooth
    (𝕜 := Real) (E := F) (H := G) (I := J) (M := N)
    (n := (∞ : WithTop ℕ∞)) r
  let V : N -> Type _ := fun p : N => Tensor0SBundle.Tensor0SSpace r J p
  let fiber : Type _ := Tensor0SBundle.Tensor0SModel r Real F
  let e := trivializationAt fiber V x₀
  let s : Unit -> (y : N) -> V y :=
    fun _ y =>
      Tensor0SBundle.Tensor0SSpace.constInChart
        (𝕜 := Real) (E := F) (H := G) (I := J) (M := N) r x₀ β y
  have hs : ∀ i : Unit,
      ContMDiffOn J
        (J.prod 𝓘(Real, fiber))
        (∞ : WithTop ℕ∞)
        (fun y : N =>
          (⟨y, s i y⟩ :
            TotalSpace fiber V))
        e.baseSet := by
    intro i
    simpa [s, e, fiber, V] using
      Tensor0SBundle.tensor0SConstInChart_contMDiffOn_baseSet
        (𝕜 := Real) (E := F) (H := G) (I := J) (M := N)
        (r := r) x₀ β
  have hx₀ : x₀ ∈ e.baseSet := by
    simpa [e, fiber, V] using
      (mem_baseSet_trivializationAt fiber V x₀)
  obtain ⟨αs, hαs⟩ :=
    exists_contMDiffSection_eqOn_nhd
      (E := F) (H := G) (I := J) (M := N)
      (F := fiber) (V := V)
      (n := (⊤ : ℕ∞))
      (s := s) hs e.open_baseSet hx₀
  refine ⟨αs (), ?_⟩
  filter_upwards [hαs] with y hy
  exact congrArg
    (fun z =>
      (⟨y, z⟩ :
        TotalSpace (Tensor0SBundle.Tensor0SModel r Real F)
          (fun p : N => Tensor0SBundle.Tensor0SSpace r J p)))
    (hy ())

/-- A chart-constant covector in the tensor-bundle trivialization has a
global smooth one-form section extension which agrees with it near the chart
center. -/
theorem existsConstCoframe
    (x₀ : N) (β : Tensor0SBundle.Tensor0SModel 1 Real F) :
    ∃ α : Tensor0SBundle.Tensor0SField
        (𝕜 := Real) (E := F) (H := G) (I := J) (M := N)
        (n := (∞ : WithTop ℕ∞)) 1,
      (fun y : N =>
        (⟨y, α y⟩ :
          TotalSpace (Tensor0SBundle.Tensor0SModel 1 Real F)
            (fun p : N => Tensor0SBundle.Tensor0SSpace 1 J p))) =ᶠ[𝓝 x₀]
        fun y : N =>
          (⟨y,
            Tensor0SBundle.Tensor0SSpace.constInChart
              (𝕜 := Real) (E := F) (H := G) (I := J) (M := N) 1 x₀ β y⟩ :
            TotalSpace (Tensor0SBundle.Tensor0SModel 1 Real F)
              (fun p : N => Tensor0SBundle.Tensor0SSpace 1 J p)) :=
  existsConstTensor0S (J := J) 1 x₀ β

/-- The basis tensors of a tangent-trivialization model basis have global
smooth covariant tensor-field section extensions agreeing with the
chart-constant tensors near the center. -/
theorem existsTrivTensor0SSec
    {Idx : Type*} [Fintype Idx] [DecidableEq Idx]
    (r : Nat) (x₀ : N) (b : Module.Basis Idx Real F) :
    ∃ θ : (Fin r -> Idx) -> Tensor0SBundle.Tensor0SField
        (𝕜 := Real) (E := F) (H := G) (I := J) (M := N)
        (n := (∞ : WithTop ℕ∞)) r,
      ∀ slots : Fin r -> Idx,
        (fun y : N =>
          (⟨y, θ slots y⟩ :
            TotalSpace (Tensor0SBundle.Tensor0SModel r Real F)
              (fun p : N => Tensor0SBundle.Tensor0SSpace r J p))) =ᶠ[𝓝 x₀]
          fun y : N =>
            (⟨y,
              Tensor0SBundle.Tensor0SSpace.constInChart
                (𝕜 := Real) (E := F) (H := G) (I := J) (M := N) r x₀
                ((Tensor0SBundle.continuousMultilinearMapBasis
                  (𝕜 := Real) (V := F) b r) slots) y⟩ :
              TotalSpace (Tensor0SBundle.Tensor0SModel r Real F)
                (fun p : N => Tensor0SBundle.Tensor0SSpace r J p)) := by
  classical
  choose θ hθ using fun slots : Fin r -> Idx =>
    existsConstTensor0S (J := J) r x₀
      ((Tensor0SBundle.continuousMultilinearMapBasis
        (𝕜 := Real) (V := F) b r) slots)
  exact ⟨θ, hθ⟩

/-- Default-coordinate version of `existsTrivTensor0SSec`, using
`LocalChartAt.default`/`coordinateFrameAt` indices. -/
theorem existsDefaultTensor0SSec
    (r : Nat) (x₀ : N) :
    ∃ θ : (Fin r -> CoordinateIdx (𝕜 := Real) F) ->
        Tensor0SBundle.Tensor0SField
          (𝕜 := Real) (E := F) (H := G) (I := J) (M := N)
          (n := (∞ : WithTop ℕ∞)) r,
      ∀ slots : Fin r -> CoordinateIdx (𝕜 := Real) F,
        (fun y : N =>
          (⟨y, θ slots y⟩ :
            TotalSpace (Tensor0SBundle.Tensor0SModel r Real F)
              (fun p : N => Tensor0SBundle.Tensor0SSpace r J p))) =ᶠ[𝓝 x₀]
          fun y : N =>
            (⟨y,
              Tensor0SBundle.Tensor0SSpace.constInChart
                (𝕜 := Real) (E := F) (H := G) (I := J) (M := N) r x₀
                ((Tensor0SBundle.continuousMultilinearMapBasis
                  (𝕜 := Real) (V := F) (Module.finBasis Real F) r)
                    slots) y⟩ :
              TotalSpace (Tensor0SBundle.Tensor0SModel r Real F)
                (fun p : N => Tensor0SBundle.Tensor0SSpace r J p)) :=
  existsTrivTensor0SSec (J := J) r x₀ (Module.finBasis Real F)

/-- The dual covectors of a tangent-trivialization model basis have global
smooth one-form section extensions agreeing with the chart-constant covectors
near the center. -/
theorem existsTrivCoframeSec
    {Idx : Type*} [Fintype Idx] [DecidableEq Idx]
    (x₀ : N) (b : Module.Basis Idx Real F) :
    ∃ θ : Idx -> Tensor0SBundle.Tensor0SField
        (𝕜 := Real) (E := F) (H := G) (I := J) (M := N)
        (n := (∞ : WithTop ℕ∞)) 1,
      ∀ i : Idx,
        (fun y : N =>
          (⟨y, θ i y⟩ :
            TotalSpace (Tensor0SBundle.Tensor0SModel 1 Real F)
              (fun p : N => Tensor0SBundle.Tensor0SSpace 1 J p))) =ᶠ[𝓝 x₀]
          fun y : N =>
            (⟨y,
              Tensor0SBundle.Tensor0SSpace.constInChart
                (𝕜 := Real) (E := F) (H := G) (I := J) (M := N) 1 x₀
                ((Tensor0SBundle.continuousMultilinearMapBasis
                  (𝕜 := Real) (V := F) b 1) (fun _ : Fin 1 => i)) y⟩ :
              TotalSpace (Tensor0SBundle.Tensor0SModel 1 Real F)
                (fun p : N => Tensor0SBundle.Tensor0SSpace 1 J p)) := by
  classical
  choose θ hθ using fun i : Idx =>
    existsConstCoframe (J := J) x₀
      ((Tensor0SBundle.continuousMultilinearMapBasis
        (𝕜 := Real) (V := F) b 1) (fun _ : Fin 1 => i))
  exact ⟨θ, hθ⟩

/-- Smooth tangent-frame and dual-coframe section extensions for a tangent
trivialization, with the Kronecker pairing near the center. -/
theorem existsTrivFrameCoframePair
    {Idx : Type*} [Fintype Idx] [DecidableEq Idx]
    (x₀ : N) (b : Module.Basis Idx Real F) :
    ∃ Z : Idx -> ContMDiffSection J F (∞ : WithTop ℕ∞)
        (TangentSpace J : N -> Type _),
    ∃ θ : Idx -> Tensor0SBundle.Tensor0SField
        (𝕜 := Real) (E := F) (H := G) (I := J) (M := N)
        (n := (∞ : WithTop ℕ∞)) 1,
      (∀ j : Idx,
        (fun y : N => Z j y) =ᶠ[𝓝 x₀]
          fun y : N =>
            (trivializationAt F (TangentSpace J : N -> Type _) x₀).localFrame b j y) ∧
      (∀ i : Idx,
        (fun y : N =>
          (⟨y, θ i y⟩ :
            TotalSpace (Tensor0SBundle.Tensor0SModel 1 Real F)
              (fun p : N => Tensor0SBundle.Tensor0SSpace 1 J p))) =ᶠ[𝓝 x₀]
          fun y : N =>
            (⟨y,
              Tensor0SBundle.Tensor0SSpace.constInChart
                (𝕜 := Real) (E := F) (H := G) (I := J) (M := N) 1 x₀
                ((Tensor0SBundle.continuousMultilinearMapBasis
                  (𝕜 := Real) (V := F) b 1) (fun _ : Fin 1 => i)) y⟩ :
              TotalSpace (Tensor0SBundle.Tensor0SModel 1 Real F)
                (fun p : N => Tensor0SBundle.Tensor0SSpace 1 J p))) ∧
      (∀ i j : Idx,
        (fun y : N => θ i y (fun _ : Fin 1 => Z j y)) =ᶠ[𝓝 x₀]
          fun _ : N => if j = i then (1 : Real) else 0) := by
  classical
  obtain ⟨Z, hZ, hraw⟩ := existsTrivFramePair (J := J) x₀ b
  obtain ⟨θ, hθ⟩ := existsTrivCoframeSec (J := J) x₀ b
  refine ⟨Z, θ, hZ, hθ, fun i j => ?_⟩
  filter_upwards [hθ i, hraw i j] with y hθy hpair
  have hθy_fiber :
      θ i y =
        Tensor0SBundle.Tensor0SSpace.constInChart
          (𝕜 := Real) (E := F) (H := G) (I := J) (M := N) 1 x₀
          ((Tensor0SBundle.continuousMultilinearMapBasis
            (𝕜 := Real) (V := F) b 1) (fun _ : Fin 1 => i)) y :=
    TotalSpace.mk_inj.mp hθy
  rw [hθy_fiber]
  exact hpair

/-- Smooth frame/coframe section extensions for the default `LocalChartAt`.

This is the chart-facing specialization of `existsTrivFrameCoframePair`.  It
uses the default tangent trivialization carried by `LocalChartAt.default`, so it
does not assert the still-missing arbitrary-trivialization coframe smoothness
bridge. -/
theorem existsDefaultCoframePair
    (x₀ : N) :
    ∃ Z : CoordinateIdx (𝕜 := Real) F -> ContMDiffSection J F (∞ : WithTop ℕ∞)
        (TangentSpace J : N -> Type _),
    ∃ θ : CoordinateIdx (𝕜 := Real) F -> Tensor0SBundle.Tensor0SField
        (𝕜 := Real) (E := F) (H := G) (I := J) (M := N)
        (n := (∞ : WithTop ℕ∞)) 1,
      (∀ j : CoordinateIdx (𝕜 := Real) F,
        (fun y : N => Z j y) =ᶠ[𝓝 x₀]
          fun y : N => (LocalChartAt.defaultFrame (I := J) x₀).frame j y) ∧
      (∀ i : CoordinateIdx (𝕜 := Real) F,
        (fun y : N =>
          (⟨y, θ i y⟩ :
            TotalSpace (Tensor0SBundle.Tensor0SModel 1 Real F)
              (fun p : N => Tensor0SBundle.Tensor0SSpace 1 J p))) =ᶠ[𝓝 x₀]
          fun y : N =>
            (⟨y,
              Tensor0SBundle.Tensor0SSpace.constInChart
                (𝕜 := Real) (E := F) (H := G) (I := J) (M := N) 1 x₀
                ((Tensor0SBundle.continuousMultilinearMapBasis
                  (𝕜 := Real) (V := F) (Module.finBasis Real F) 1)
                    (fun _ : Fin 1 => i)) y⟩ :
              TotalSpace (Tensor0SBundle.Tensor0SModel 1 Real F)
                (fun p : N => Tensor0SBundle.Tensor0SSpace 1 J p))) ∧
      (∀ i j : CoordinateIdx (𝕜 := Real) F,
        (fun y : N => θ i y (fun _ : Fin 1 => Z j y)) =ᶠ[𝓝 x₀]
          fun _ : N => if j = i then (1 : Real) else 0) := by
  classical
  obtain ⟨Z, θ, hZ, hθ, hpair⟩ :=
    existsTrivFrameCoframePair (J := J) (N := N) x₀ (Module.finBasis Real F)
  refine ⟨Z, θ, ?_, hθ, hpair⟩
  intro j
  simpa [LocalChartAt.defaultFrame_frame, coordinateFrameAt]
    using hZ j

end Real

end

end Coordinates
end RicciFlower
