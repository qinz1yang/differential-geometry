import DifferentialGeometry.Geometry.Connection.TensorNabla.TensorRSNabla
import DifferentialGeometry.Analysis.Spectral.Tensor.CovGrad.Defs

/-!
# The second-order Hom-bundle `Hom(T^{r,a}, T^{r,c})` and its covariant calculus

For a closed (compact, boundaryless) smooth Riemannian manifold `(M, g)` modelled on a real
inner-product space `E`, this file builds the **second-order Hom-bundle**
`Hom(TensorRSSpace r a, TensorRSSpace r c) = fun x => TensorRSSpace r a I x →L[ℝ] TensorRSSpace r c I x`
— the bundle of fibrewise continuous-linear endomorphism-type maps between *full* `(r, a)`- and
`(r, c)`-tensor fibres — together with its induced covariant derivative and the full Hom-bundle
operator-field action calculus.

Unlike the first-order Hom-bundle `Hom(Tensor0SSpace r, Tensor0SSpace s) = TensorRSSpace r s`
(the `(r, s)`-tensor bundle itself, `Tensor0SBundle`), whose source/target are the global
`Tensor0SSpace` bundles, the source/target here are themselves the *first-order* Hom-bundles
`TensorRSSpace r a` / `TensorRSSpace r c`.  Both already carry the full vector-bundle instance suite
(`Tensor0SBundle.tensorRSBundle_topology/fiber/vector/smooth`), so the second-order Hom-bundle is the
`Bundle.ContinuousLinearMap` bundle of two existing smooth vector bundles — exactly as the `(r, s)`-tensor
bundle is the `Bundle.ContinuousLinearMap` bundle of the `(0, r)`- and `(0, s)`-tensor bundles.  The
construction therefore *reuses* the entire `homBundleCovariantDerivativeGen` machinery
(`HomBundleNabla`), instantiated with `U = TensorRSSpace r a`, `V = TensorRSSpace r c`, exactly as
`tensorRSCovariantDerivative` instantiates it with `U = Tensor0SSpace r`, `V = Tensor0SSpace s`.

## Main declarations

* `HomTensorRSModel r a c 𝕜 E` / `HomTensorRSSpace r a c I x` — the model fiber and point-wise fiber of
  the second-order Hom-bundle (non-reducible `def`s carrying re-declared instance towers, mirroring the
  `Tensor0SBundle` discipline for `TensorRSSpace`);
* the bundle instance tower (`homTensorRSBundle_topology/fiber/vector/smooth`) — the
  `Bundle.ContinuousLinearMap` bundle of the source/target `(r, a)` / `(r, c)`-tensor bundles;
* `homTensorRSCovariantDerivative r a c cov` — the induced covariant derivative on the second-order
  Hom-bundle, via `homBundleCovariantDerivativeGen`, with its pointwise product-rule apply formula;
* `appFullRS` / `covGrad_appFullRS_eq` — the full Hom-bundle operator-field action and its covariant
  product rule `∇(Ψ·W) = (∇Ψ)·W + (slotExtend Ψ)·(∇W)` (built in the consumer files over this calculus).
-/

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option linter.style.setOption false
set_option synthInstance.maxHeartbeats 1600000
set_option maxHeartbeats 3200000

open Bundle Manifold Set IsManifold Tensor0SBundle
open scoped Manifold Topology ContDiff BigOperators

namespace DifferentialGeometry.Integral.Connection

/-! ## The second-order Hom-bundle model fiber and its instance tower

The model fiber is purely algebraic (no manifold context), so its instance tower is declared in a
`{𝕜} {E}`-only section, exactly mirroring `TensorRSModel`'s `Tensor0SBundle` discipline. -/

section ModelFiber

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E] [FiniteDimensional 𝕜 E]

/-- **The model fiber of the second-order Hom-bundle `Hom(T^{r,a}, T^{r,c})`**: continuous linear maps
from the `(r, a)`-tensor model fiber to the `(r, c)`-tensor model fiber.  Declared as a non-reducible
`def` so that typeclass synthesis treats it as an opaque type; the normed instances are re-declared on it
directly (mirroring `TensorRSModel`'s discipline) to avoid the `SeminormedAddCommGroup` diamond between
the `ContinuousLinearMap`-induced structure and an `inferInstanceAs`-transported one. -/
@[nolint unusedArguments]
def HomTensorRSModel (r a c : ℕ) (𝕜 : Type*) (E : Type*) [NontriviallyNormedField 𝕜]
    [NormedAddCommGroup E] [NormedSpace 𝕜 E] [Module.Finite 𝕜 E] [FiniteDimensional 𝕜 E] :=
  TensorRSModel r a 𝕜 E →L[𝕜] TensorRSModel r c 𝕜 E

/-- The `(0, s)`-model fiber `Tensor0SModel s 𝕜 E`'s `SMulCommClass`, at the
`ContinuousMultilinearMap` level (where it is canonical). -/
private instance tensor0SModel_smulCommClass (s : ℕ) :
    SMulCommClass 𝕜 𝕜 (Tensor0SModel s 𝕜 E) := by
  unfold Tensor0SModel; infer_instance

/-- The `(r, c)`-model fiber `TensorRSModel r c 𝕜 E`'s `SMulCommClass`, lifted from the codomain
`Tensor0SModel c`'s after pinning the codomain normed-module structure. -/
private instance tensorRSModel_smulCommClass (r c : ℕ) :
    SMulCommClass 𝕜 𝕜 (TensorRSModel r c 𝕜 E) := by
  letI nsr : NormedSpace 𝕜 (Tensor0SModel r 𝕜 E) := tensor0SModel_normedSpace r
  letI nsc : NormedSpace 𝕜 (Tensor0SModel c 𝕜 E) := tensor0SModel_normedSpace c
  unfold TensorRSModel
  infer_instance

/-- `HomTensorRSModel r a c 𝕜 E` is a normed additive commutative group.  Built by the same explicit
`@ContinuousLinearMap.toNormedAddCommGroup` application `tensorRSModel_normedAddCommGroup` uses, one Hom
level up, with the source/target `(r, a)` / `(r, c)`-model normed structures pinned. -/
instance homTensorRSModel_normedAddCommGroup (r a c : ℕ) :
    NormedAddCommGroup (HomTensorRSModel r a c 𝕜 E) := by
  unfold HomTensorRSModel
  letI nsU : NormedSpace 𝕜 (TensorRSModel r a 𝕜 E) := tensorRSModel_normedSpace r a
  letI nsV : NormedSpace 𝕜 (TensorRSModel r c 𝕜 E) := tensorRSModel_normedSpace r c
  exact @ContinuousLinearMap.toNormedAddCommGroup 𝕜 𝕜
    (TensorRSModel r a 𝕜 E) (TensorRSModel r c 𝕜 E) _ _ _ _ nsU nsV _ _

/-- `HomTensorRSModel r a c 𝕜 E` is a normed `𝕜`-module.  Built by the same explicit
`@ContinuousLinearMap.toNormedSpace` application as `tensorRSModel_normedSpace`, one Hom level up, with
the source/target normed structures and the target `SMulCommClass` (`tensorRSModel_smulCommClass`)
pinned to avoid the reducibility-driven instance search. -/
instance homTensorRSModel_normedSpace (r a c : ℕ) :
    NormedSpace 𝕜 (HomTensorRSModel r a c 𝕜 E) := by
  unfold HomTensorRSModel
  letI nsU : NormedSpace 𝕜 (TensorRSModel r a 𝕜 E) := tensorRSModel_normedSpace r a
  letI nsV : NormedSpace 𝕜 (TensorRSModel r c 𝕜 E) := tensorRSModel_normedSpace r c
  letI scc : SMulCommClass 𝕜 𝕜 (TensorRSModel r c 𝕜 E) := tensorRSModel_smulCommClass r c
  exact @ContinuousLinearMap.toNormedSpace 𝕜 𝕜
    (TensorRSModel r a 𝕜 E) (TensorRSModel r c 𝕜 E) _ _ _ _ _ _ _ _ 𝕜 _ nsV scc

/-- `HomTensorRSModel r a c 𝕜 E` is finite-dimensional over `𝕜`.  Proved through the injective
`ContinuousLinearMap.coeLM` into the purely-linear Hom `TensorRSModel r a →ₗ TensorRSModel r c` (a
finite-dimensional module, both factors finite-dimensional), avoiding the `ContinuousLinearMap`
topological-instance synthesis on the un-wrapped Hom-of-Hom. -/
noncomputable instance homTensorRSModel_finiteDimensional [CompleteSpace 𝕜] (r a c : ℕ) :
    FiniteDimensional 𝕜 (HomTensorRSModel r a c 𝕜 E) := by
  letI nsU : NormedSpace 𝕜 (TensorRSModel r a 𝕜 E) := tensorRSModel_normedSpace r a
  letI nsV : NormedSpace 𝕜 (TensorRSModel r c 𝕜 E) := tensorRSModel_normedSpace r c
  haveI iUf : FiniteDimensional 𝕜 (TensorRSModel r a 𝕜 E) := tensorRSModel_finiteDimensional r a
  haveI iVf : FiniteDimensional 𝕜 (TensorRSModel r c 𝕜 E) := tensorRSModel_finiteDimensional r c
  unfold HomTensorRSModel
  exact ContinuousLinearMap.finiteDimensional

end ModelFiber

/-! ## The second-order Hom-bundle point-wise fiber and its bundle instance tower

The point-wise fiber `HomTensorRSSpace r a c I x` lives over a smooth manifold; its bundle instance
tower is the `Bundle.ContinuousLinearMap` bundle of the source `(r, a)`- and target `(r, c)`-tensor
bundles (`Tensor0SBundle.tensorRSBundle_topology/fiber/vector/smooth`), exactly as the `(r, s)`-tensor
bundle is the `Bundle.ContinuousLinearMap` bundle of the `(0, r)`- and `(0, s)`-tensor bundles. -/

section SpaceFiber

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E] [FiniteDimensional 𝕜 E]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners 𝕜 E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 1 M]

/-- **The point-wise fiber of the second-order Hom-bundle `Hom(T^{r,a}, T^{r,c})` at `x ∈ M`**:
continuous linear maps from the `(r, a)`-tensor fiber to the `(r, c)`-tensor fiber.  Declared as a
non-reducible `def` (mirroring `TensorRSSpace`'s `Tensor0SBundle` discipline); the bundle instances are
re-declared on it directly to avoid diamonds with the source/target `(r, a)` / `(r, c)`-bundle
topologies. -/
@[nolint unusedArguments]
def HomTensorRSSpace (r a c : ℕ) (I : ModelWithCorners 𝕜 E H) [IsManifold I 1 M] (x : M) : Type _ :=
  TensorRSSpace r a I x →L[𝕜] TensorRSSpace r c I x

/-! ### Bedrock fiber instances for `HomTensorRSSpace` -/

instance homTensorRSSpace_topologicalSpace (r a c : ℕ) (x : M) :
    TopologicalSpace (HomTensorRSSpace r a c I x) :=
  inferInstanceAs (TopologicalSpace (TensorRSSpace r a I x →L[𝕜] TensorRSSpace r c I x))

instance homTensorRSSpace_addCommGroup (r a c : ℕ) (x : M) :
    AddCommGroup (HomTensorRSSpace r a c I x) :=
  inferInstanceAs (AddCommGroup (TensorRSSpace r a I x →L[𝕜] TensorRSSpace r c I x))

instance homTensorRSSpace_module (r a c : ℕ) (x : M) :
    Module 𝕜 (HomTensorRSSpace r a c I x) :=
  inferInstanceAs (Module 𝕜 (TensorRSSpace r a I x →L[𝕜] TensorRSSpace r c I x))

instance homTensorRSSpace_isTopologicalAddGroup (r a c : ℕ) (x : M) :
    IsTopologicalAddGroup (HomTensorRSSpace r a c I x) :=
  inferInstanceAs (IsTopologicalAddGroup (TensorRSSpace r a I x →L[𝕜] TensorRSSpace r c I x))

instance homTensorRSSpace_continuousAdd (r a c : ℕ) (x : M) :
    ContinuousAdd (HomTensorRSSpace r a c I x) :=
  inferInstanceAs (ContinuousAdd (TensorRSSpace r a I x →L[𝕜] TensorRSSpace r c I x))

instance homTensorRSSpace_continuousSMul (r a c : ℕ) (x : M) :
    ContinuousSMul 𝕜 (HomTensorRSSpace r a c I x) :=
  inferInstanceAs (ContinuousSMul 𝕜 (TensorRSSpace r a I x →L[𝕜] TensorRSSpace r c I x))

/-! ### The `Bundle.ContinuousLinearMap` total-space topology, fiber bundle, and vector bundle -/

/-- The total space of the second-order Hom-bundle carries the `Bundle.ContinuousLinearMap`
total-space topology of the `(r, a)`- and `(r, c)`-tensor bundles. -/
noncomputable instance homTensorRSBundle_topology (r a c : ℕ) :
    TopologicalSpace (TotalSpace (HomTensorRSModel r a c 𝕜 E)
      (fun x : M => HomTensorRSSpace r a c I x)) :=
  Bundle.ContinuousLinearMap.topologicalSpaceTotalSpace (RingHom.id 𝕜)
    (TensorRSModel r a 𝕜 E) (fun x : M => TensorRSSpace r a I x)
    (TensorRSModel r c 𝕜 E) (fun x : M => TensorRSSpace r c I x)

/-- The second-order Hom-bundle is a fiber bundle, as a Hom bundle between two fiber bundles. -/
noncomputable instance homTensorRSBundle_fiber (r a c : ℕ) :
    @FiberBundle M (HomTensorRSModel r a c 𝕜 E) _ (by infer_instance : TopologicalSpace _)
      (fun x : M => HomTensorRSSpace r a c I x)
      (homTensorRSBundle_topology r a c) _ :=
  Bundle.ContinuousLinearMap.fiberBundle (RingHom.id 𝕜)
    (TensorRSModel r a 𝕜 E) (fun x : M => TensorRSSpace r a I x)
    (TensorRSModel r c 𝕜 E) (fun x : M => TensorRSSpace r c I x)

/-- The second-order Hom-bundle is a vector bundle with model fiber `HomTensorRSModel r a c 𝕜 E`. -/
noncomputable instance homTensorRSBundle_vector (r a c : ℕ) :
    @VectorBundle 𝕜 M (HomTensorRSModel r a c 𝕜 E) (fun x : M => HomTensorRSSpace r a c I x) _
      (fun x => by infer_instance) (fun x => by infer_instance)
      (homTensorRSModel_normedAddCommGroup r a c) (homTensorRSModel_normedSpace r a c) _
      (homTensorRSBundle_topology r a c) _
      (homTensorRSBundle_fiber r a c) :=
  Bundle.ContinuousLinearMap.vectorBundle (RingHom.id 𝕜)
    (TensorRSModel r a 𝕜 E) (fun x : M => TensorRSSpace r a I x)
    (TensorRSModel r c 𝕜 E) (fun x : M => TensorRSSpace r c I x)

/-- The second-order Hom-bundle is a `C^n` vector bundle over `M`, as a `Bundle.ContinuousLinearMap`
of the `C^n` `(r, a)`- and `(r, c)`-tensor bundles. -/
noncomputable instance homTensorRSBundle_smooth [CompleteSpace 𝕜] (n : WithTop ℕ∞)
    [IsManifold I (n + 1) M] (r a c : ℕ) :
    @ContMDiffVectorBundle n 𝕜 M (HomTensorRSModel r a c 𝕜 E)
      (fun x : M => HomTensorRSSpace r a c I x)
      _ E _ _ H _ I _ _ _ _ _ _
      (homTensorRSBundle_topology r a c) _
      (homTensorRSBundle_fiber r a c)
      (homTensorRSBundle_vector r a c) :=
  ContMDiffVectorBundle.continuousLinearMap

end SpaceFiber

/-! ## The second-order Hom-bundle covariant derivative

Specializing the generic Hom-bundle covariant derivative `homBundleCovariantDerivativeGen` to source
`U = TensorRSSpace r a` and target `V = TensorRSSpace r c`, both of which carry the full smooth
vector-bundle instance suite, gives the induced covariant derivative on the second-order Hom-bundle
`Hom(T^{r,a}, T^{r,c})`.  This is the exact mirror of `tensorRSCovariantDerivative` (which specializes
the generic derivative to `U = Tensor0SSpace r`, `V = Tensor0SSpace s`), one Hom level up. -/

section CovDeriv

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
variable {H : Type*} [TopologicalSpace H] (I : ModelWithCorners ℝ E H)
variable (M : Type*) [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [SigmaCompactSpace M] [T2Space M]

open scoped ContDiff
open CovariantDerivative

/-- **The second-order Hom-bundle covariant derivative on `Hom(T^{r,a}, T^{r,c})`**, obtained by
specializing the generic Hom-bundle covariant derivative `homBundleCovariantDerivativeGen` to
`U = TensorRSSpace r a` (source) and `V = TensorRSSpace r c` (target), with their induced
`(r, a)` / `(r, c)`-tensor covariant derivatives `tensorRSCovariantDerivative`. -/
noncomputable def homTensorRSCovariantDerivative (r a c : ℕ)
    (cov : CovariantDerivative I E (TangentSpace I : M → Type _))
    [ContMDiffCovariantDerivative cov ∞] :
    CovariantDerivative I (HomTensorRSModel r a c ℝ E)
      (fun x : M => HomTensorRSSpace r a c I x) :=
  HomConnectionGen.homBundleCovariantDerivativeGen I M
    (TensorRSModel r a ℝ E) (fun x : M => TensorRSSpace r a I x)
    (TensorRSModel r c ℝ E) (fun x : M => TensorRSSpace r c I x)
    (TensorRSNabla.tensorRSCovariantDerivative I M r a cov)
    (TensorRSNabla.tensorRSCovariantDerivative I M r c cov)

/-- Smoothness of `homTensorRSCovariantDerivative`: inherited from the `C^∞` instances of the
underlying `(r, a)`- and `(r, c)`-tensor covariant derivatives via the generic Hom-bundle smoothness
instance. -/
noncomputable instance homTensorRSCovariantDerivative_contMDiff (r a c : ℕ)
    (cov : CovariantDerivative I E (TangentSpace I : M → Type _))
    [ContMDiffCovariantDerivative cov ∞] :
    ContMDiffCovariantDerivative (homTensorRSCovariantDerivative I M r a c cov) ∞ :=
  HomConnectionGen.homBundleCovariantDerivativeGen_contMDiff I M
    (TensorRSModel r a ℝ E) (fun x : M => TensorRSSpace r a I x)
    (TensorRSModel r c ℝ E) (fun x : M => TensorRSSpace r c I x)
    (TensorRSNabla.tensorRSCovariantDerivative I M r a cov)
    (TensorRSNabla.tensorRSCovariantDerivative I M r c cov)

/-- **Pointwise product-rule formula for `homTensorRSCovariantDerivative`.** For a smooth second-order
Hom-bundle section `Ψ` and a smooth `(r, a)`-tensor section `W`, the value of the covariant derivative
applied bilinearly to a tangent vector `v ∈ T_xM` and `W x` is the standard product-rule expression
`∇^{(r,c)}_v(Ψ·W) − Ψ(∇^{(r,a)}_v W)`, where `∇^{(r,a)}`, `∇^{(r,c)}` are the `tensorRSCovariantDerivative`
connections. -/
theorem homTensorRSCovariantDerivative_apply (r a c : ℕ)
    (cov : CovariantDerivative I E (TangentSpace I : M → Type _))
    [ContMDiffCovariantDerivative cov ∞]
    (Ψ : Cₛ^∞⟮I; HomTensorRSModel r a c ℝ E, (fun x : M => HomTensorRSSpace r a c I x)⟯)
    (W : Cₛ^∞⟮I; TensorRSModel r a ℝ E, (fun x : M => TensorRSSpace r a I x)⟯)
    (x : M) (v : TangentSpace I x) :
    (show TensorRSSpace r a I x →L[ℝ] TensorRSSpace r c I x from
        homTensorRSCovariantDerivative I M r a c cov Ψ x v) (W x) =
      TensorRSNabla.tensorRSCovariantDerivative I M r c cov
        (fun y =>
          (show TensorRSSpace r a I y →L[ℝ] TensorRSSpace r c I y from Ψ y) (W y)) x v -
      (show TensorRSSpace r a I x →L[ℝ] TensorRSSpace r c I x from Ψ x)
        (TensorRSNabla.tensorRSCovariantDerivative I M r a cov W x v) :=
  HomConnectionGen.homBundleCovariantDerivativeGen_apply I M
    (TensorRSModel r a ℝ E) (fun x : M => TensorRSSpace r a I x)
    (TensorRSModel r c ℝ E) (fun x : M => TensorRSSpace r c I x)
    (TensorRSNabla.tensorRSCovariantDerivative I M r a cov)
    (TensorRSNabla.tensorRSCovariantDerivative I M r c cov)
    Ψ W x v

/-- **Raw-section pointwise apply for `homTensorRSCovariantDerivative`.** With a raw second-order
Hom-bundle section `Ψ`, a raw `(r, a)`-tensor section `W`, and a tangent vector field `V_field`, all
manifold-differentiable at `x` in total-space form, the bundled second-order Hom-bundle covariant
derivative applied bilinearly at `x` decomposes as the standard product-rule formula
`∇^{(r,c)}_v(Ψ·W) − Ψ(∇^{(r,a)}_v W)`. -/
theorem homTensorRSCovariantDerivative_apply_of_mdifferentiableAt (r a c : ℕ)
    (cov : CovariantDerivative I E (TangentSpace I : M → Type _))
    [ContMDiffCovariantDerivative cov ∞]
    (Ψ : Π x : M, TensorRSSpace r a I x →L[ℝ] TensorRSSpace r c I x)
    (W : Π x : M, TensorRSSpace r a I x)
    (V_field : Π x : M, TangentSpace I x)
    {x : M}
    (hΨ : MDifferentiableAt I (I.prod 𝓘(ℝ, TensorRSModel r a ℝ E →L[ℝ] TensorRSModel r c ℝ E))
      (fun y : M => TotalSpace.mk' (TensorRSModel r a ℝ E →L[ℝ] TensorRSModel r c ℝ E)
        (E := fun z : M => TensorRSSpace r a I z →L[ℝ] TensorRSSpace r c I z) y (Ψ y)) x)
    (hW : MDifferentiableAt I (I.prod 𝓘(ℝ, TensorRSModel r a ℝ E))
      (fun y : M => TotalSpace.mk' (TensorRSModel r a ℝ E)
        (E := fun z : M => TensorRSSpace r a I z) y (W y)) x)
    (hV : MDifferentiableAt I (I.prod 𝓘(ℝ, E))
      (fun y : M => TotalSpace.mk' E
        (E := fun z : M => TangentSpace I z) y (V_field y)) x) :
    (show TensorRSSpace r a I x →L[ℝ] TensorRSSpace r c I x from
        homTensorRSCovariantDerivative I M r a c cov Ψ x (V_field x)) (W x) =
      TensorRSNabla.tensorRSCovariantDerivative I M r c cov
        (fun y =>
          (show TensorRSSpace r a I y →L[ℝ] TensorRSSpace r c I y from Ψ y) (W y))
          x (V_field x) -
      (show TensorRSSpace r a I x →L[ℝ] TensorRSSpace r c I x from Ψ x)
        (TensorRSNabla.tensorRSCovariantDerivative I M r a cov W x (V_field x)) :=
  HomConnectionGen.homBundleCovariantDerivativeGen_apply_of_mdifferentiableAt I M
    (TensorRSModel r a ℝ E) (fun y : M => TensorRSSpace r a I y)
    (TensorRSModel r c ℝ E) (fun y : M => TensorRSSpace r c I y)
    (TensorRSNabla.tensorRSCovariantDerivative I M r a cov)
    (TensorRSNabla.tensorRSCovariantDerivative I M r c cov)
    Ψ hΨ hV hW

end CovDeriv

end DifferentialGeometry.Integral.Connection

end
