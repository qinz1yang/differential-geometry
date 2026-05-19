import RicciFlower.Curvature.Tensor
import RicciFlower.Tensor.RSTensor.NablaOnTensors
import RicciFlower.VectorBundle.PartialMfderiv
import RicciFlower.VectorBundle.TangentConst
import Mathlib.Geometry.Manifold.VectorBundle.CovariantDerivative.Torsion

/-!
# Pointwise Riemann and Ricci tensors

This file starts a definition-first curvature layer.  The auxiliary curvature
operator is the usual vector-field formula, and the pointwise tensors are the
objects intended for downstream use.  The constructors use chart-constant
tangent-field representatives; arbitrary smooth-field tensoriality is a separate
extension theorem frontier, not part of these definitions.
-/

noncomputable section

set_option autoImplicit false
set_option linter.style.longLine false
set_option linter.unusedSectionVars false

open Bundle Tensor0SBundle RicciFlower.Curvature
open scoped BigOperators Manifold ContDiff Topology

namespace RicciFlower.Riemann

variable {E : Type _} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [CompleteSpace E]
variable {H : Type _} [TopologicalSpace H]
variable {I : ModelWithCorners ℝ E H}
variable {M : Type _} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

namespace CovariantDerivative

private noncomputable def tangentConstAt (x : M) (v : TangentSpace I x) (p : M) :
    TangentSpace I p :=
  TensorLieDeriv.tangentConstInChart (𝕜 := Real) (I := I) x v p

@[simp] private theorem tangentConstAt_self (x : M) (v : TangentSpace I x) :
    tangentConstAt (I := I) x v x = v := by
  unfold tangentConstAt
  rw [TensorLieDeriv.tangentConstInChart_apply]
  have hL :
      (trivializationAt E (TangentSpace I) x).symmL Real x =
        (1 : E →L[Real] E) := by
    rw [TangentBundle.symmL_trivializationAt_eq_core
      (𝕜 := Real) (I := I) (b₀ := x) (b := x) (mem_chart_source H x)]
    ext w
    exact (tangentBundleCore I M).coordChange_self (achart H x) x
      (by rw [tangentBundleCore_baseSet, coe_achart]; exact mem_chart_source H x) w
  rw [hL]
  rfl

private theorem mdifferentiableAt_tangentConstAt_self
    (x : M) (v : TangentSpace I x) :
    MDiffAt (T% (tangentConstAt (I := I) x v : (p : M) → TangentSpace I p)) x := by
  unfold tangentConstAt
  exact TensorLieDeriv.mdifferentiableAt_tangentConstInChart_of_mem
    (𝕜 := Real) (I := I) (x₀ := x) (p := x) v
    (mem_baseSet_trivializationAt E (TangentSpace I) x)

@[simp] private theorem tangentConstAt_add (x : M) (v w : TangentSpace I x) :
    (tangentConstAt (I := I) x (v + w) : (p : M) → TangentSpace I p) =
      (tangentConstAt (I := I) x v : (p : M) → TangentSpace I p) +
        tangentConstAt (I := I) x w := by
  unfold tangentConstAt
  exact TensorLieDeriv.tangentConstInChart_add (𝕜 := Real) (I := I) x v w

@[simp] private theorem tangentConstAt_smul (x : M) (a : Real) (v : TangentSpace I x) :
    (tangentConstAt (I := I) x (a • v) : (p : M) → TangentSpace I p) =
      a • (tangentConstAt (I := I) x v : (p : M) → TangentSpace I p) := by
  unfold tangentConstAt
  exact TensorLieDeriv.tangentConstInChart_smul (𝕜 := Real) (I := I) x a v

private theorem cov_tangentConst_apply_mdiffAt_self
    (cov : CovariantDerivative I E (TangentSpace I : M → Type _))
    (hcov : CovariantDerivative.ContMDiffCovariantDerivativeLocally cov ∞)
    (x : M) (v w : TangentSpace I x) :
    MDiffAt
      (T% (fun p : M => (cov (tangentConstAt (I := I) x v) p)
        (tangentConstAt (I := I) x w p))) x := by
  unfold tangentConstAt
  let e := trivializationAt E (TangentSpace I) x
  have hx : x ∈ e.baseSet := by
    simp [e]
  haveI : IsManifold I ((∞ : WithTop ℕ∞) + 1) M := by
    simpa using (inferInstance : IsManifold I ∞ M)
  haveI : IsManifold I (((∞ : WithTop ℕ∞) + 1) + 1) M := by
    simpa using (inferInstance : IsManifold I ∞ M)
  have h_on :
      CMDiff[e.baseSet] ∞
        (T% (fun p : M =>
          (cov (TensorLieDeriv.tangentConstInChart (𝕜 := Real) (I := I) x v) p)
            (TensorLieDeriv.tangentConstInChart (𝕜 := Real) (I := I) x w p))) := by
    have hσ :
        CMDiff[e.baseSet] (∞ + 1)
          (T% (TensorLieDeriv.tangentConstInChart (𝕜 := Real) (I := I) x v :
            (p : M) → TangentSpace I p)) := by
      simpa [e] using
        (TensorLieDeriv.tangentConstInChart_contMDiffOn_baseSet
          (𝕜 := Real) (I := I) (M := M) (n := (∞ : WithTop ℕ∞) + 1) x v)
    have hcovσ :
        ContMDiffOn I (I.prod 𝓘(Real, E →L[Real] E)) ∞
          (fun p : M =>
            (⟨p, cov
              (TensorLieDeriv.tangentConstInChart (𝕜 := Real) (I := I) x v) p⟩ :
              TotalSpace (E →L[Real] E)
                (fun p : M => TangentSpace I p →L[Real] TangentSpace I p)))
          e.baseSet := by
      exact (hcov e.open_baseSet).contMDiff hσ
    have hX :
        CMDiff[e.baseSet] ∞
          (T% (TensorLieDeriv.tangentConstInChart (𝕜 := Real) (I := I) x w :
            (p : M) → TangentSpace I p)) := by
      simpa [e] using
        (TensorLieDeriv.tangentConstInChart_contMDiffOn_baseSet
          (𝕜 := Real) (I := I) (M := M) (n := (∞ : WithTop ℕ∞)) x w)
    simpa [e] using hcovσ.clm_bundle_apply hX
  have h_at : CMDiffAt ∞
      (T% (fun p : M =>
        (cov (TensorLieDeriv.tangentConstInChart (𝕜 := Real) (I := I) x v) p)
          (TensorLieDeriv.tangentConstInChart (𝕜 := Real) (I := I) x w p))) x :=
    (h_on x hx).contMDiffAt (e.open_baseSet.mem_nhds hx)
  exact h_at.mdifferentiableAt (by simp)

private theorem cov_smooth_apply_mdiffAt
    (cov : CovariantDerivative I E (TangentSpace I : M → Type _))
    (hcov : CovariantDerivative.ContMDiffCovariantDerivativeLocally cov
      (∞ : WithTop ℕ∞))
    (X Y : ContMDiffSection I E (∞ : WithTop ℕ∞)
      (TangentSpace I : M → Type _))
    (x : M) :
    MDiffAt (T% (fun p : M => (cov (fun q : M => Y q) p) (X p))) x := by
  let e := trivializationAt E (TangentSpace I) x
  have hx : x ∈ e.baseSet := by
    simp [e]
  haveI : IsManifold I (((1 : WithTop ℕ∞) + 1) + 1) M := by
    exact IsManifold.of_le (I := I) (M := M) (n := ∞)
      (by
        exact WithTop.coe_le_coe.2 (le_top : (3 : ℕ∞) ≤ (⊤ : ℕ∞)))
  have h_on :
      CMDiff[e.baseSet] (∞ : WithTop ℕ∞)
        (T% (fun p : M => (cov (fun q : M => Y q) p) (X p))) := by
    have hY :
        CMDiff[e.baseSet] ((∞ : WithTop ℕ∞) + 1)
          (T% (fun q : M => Y q)) := by
      simpa using Y.contMDiff.contMDiffOn
    have hcovY :
        ContMDiffOn I (I.prod 𝓘(Real, E →L[Real] E)) (∞ : WithTop ℕ∞)
          (fun p : M =>
            (⟨p, cov (fun q : M => Y q) p⟩ :
              TotalSpace (E →L[Real] E)
                (fun p : M => TangentSpace I p →L[Real] TangentSpace I p)))
          e.baseSet := by
      exact (hcov e.open_baseSet).contMDiff hY
    have hX :
        CMDiff[e.baseSet] (∞ : WithTop ℕ∞)
          (T% (fun p : M => X p)) := by
      exact X.contMDiff.contMDiffOn
    simpa [e] using hcovY.clm_bundle_apply hX
  have h_at : CMDiffAt (∞ : WithTop ℕ∞)
      (T% (fun p : M => (cov (fun q : M => Y q) p) (X p))) x :=
    (h_on x hx).contMDiffAt (e.open_baseSet.mem_nhds hx)
  exact h_at.mdifferentiableAt (by simp)

private theorem cov_smooth_apply_contMDiffAt
    (cov : CovariantDerivative I E (TangentSpace I : M → Type _))
    (hcov : CovariantDerivative.ContMDiffCovariantDerivativeLocally cov
      (∞ : WithTop ℕ∞))
    (X Y : ContMDiffSection I E (∞ : WithTop ℕ∞)
      (TangentSpace I : M → Type _))
    (x : M) :
    ContMDiffAt I (I.prod 𝓘(Real, E)) (∞ : WithTop ℕ∞)
      (T% (fun p : M => (cov (fun q : M => Y q) p) (X p))) x := by
  let e := trivializationAt E (TangentSpace I) x
  have hx : x ∈ e.baseSet := by
    simp [e]
  haveI : IsManifold I ((∞ : WithTop ℕ∞) + 1) M := by
    simpa using (inferInstance : IsManifold I ∞ M)
  haveI : IsManifold I (((∞ : WithTop ℕ∞) + 1) + 1) M := by
    simpa using (inferInstance : IsManifold I ∞ M)
  have h_on :
      CMDiff[e.baseSet] (∞ : WithTop ℕ∞)
        (T% (fun p : M => (cov (fun q : M => Y q) p) (X p))) := by
    have hY :
        CMDiff[e.baseSet] ((∞ : WithTop ℕ∞) + 1)
          (T% (fun q : M => Y q)) := by
      simpa using Y.contMDiff.contMDiffOn
    have hcovY :
        ContMDiffOn I (I.prod 𝓘(Real, E →L[Real] E)) (∞ : WithTop ℕ∞)
          (fun p : M =>
            (⟨p, cov (fun q : M => Y q) p⟩ :
              TotalSpace (E →L[Real] E)
                (fun p : M => TangentSpace I p →L[Real] TangentSpace I p)))
          e.baseSet := by
      exact (hcov e.open_baseSet).contMDiff hY
    have hX :
        CMDiff[e.baseSet] (∞ : WithTop ℕ∞)
          (T% (fun p : M => X p)) := by
      exact X.contMDiff.contMDiffOn
    simpa [e] using hcovY.clm_bundle_apply hX
  exact (h_on x hx).contMDiffAt (e.open_baseSet.mem_nhds hx)

private theorem cov_smooth_apply_raw_mdiffAt
    (cov : CovariantDerivative I E (TangentSpace I : M → Type _))
    (hcov : CovariantDerivative.ContMDiffCovariantDerivativeLocally cov
      (∞ : WithTop ℕ∞))
    {X : (p : M) → TangentSpace I p}
    (Y : ContMDiffSection I E (∞ : WithTop ℕ∞)
      (TangentSpace I : M → Type _))
    {x : M}
    (hX : MDiffAt (T% X) x) :
    MDiffAt (T% (fun p : M => (cov (fun q : M => Y q) p) (X p))) x := by
  let e := trivializationAt E (TangentSpace I) x
  have hx : x ∈ e.baseSet := by
    simp [e]
  haveI : IsManifold I (((1 : WithTop ℕ∞) + 1) + 1) M := by
    exact IsManifold.of_le (I := I) (M := M) (n := ∞)
      (by
        exact WithTop.coe_le_coe.2 (le_top : (3 : ℕ∞) ≤ (⊤ : ℕ∞)))
  have hY :
      CMDiff[e.baseSet] ((∞ : WithTop ℕ∞) + 1)
        (T% (fun q : M => Y q)) := by
    simpa using Y.contMDiff.contMDiffOn
  have hcovY_on :
      ContMDiffOn I (I.prod 𝓘(Real, E →L[Real] E)) (∞ : WithTop ℕ∞)
        (fun p : M =>
          (⟨p, cov (fun q : M => Y q) p⟩ :
            TotalSpace (E →L[Real] E)
              (fun p : M => TangentSpace I p →L[Real] TangentSpace I p)))
        e.baseSet := by
    exact (hcov e.open_baseSet).contMDiff hY
  have hcovY_at :
      ContMDiffAt I (I.prod 𝓘(Real, E →L[Real] E)) (∞ : WithTop ℕ∞)
        (fun p : M =>
          (⟨p, cov (fun q : M => Y q) p⟩ :
            TotalSpace (E →L[Real] E)
              (fun p : M => TangentSpace I p →L[Real] TangentSpace I p)))
        x :=
    (hcovY_on x hx).contMDiffAt (e.open_baseSet.mem_nhds hx)
  exact (hcovY_at.mdifferentiableAt (by simp)).clm_bundle_apply hX

private theorem curvField_contMDiffAt
    (cov : CovariantDerivative I E (TangentSpace I : M → Type _))
    (hcov : CovariantDerivative.ContMDiffCovariantDerivativeLocally cov
      (∞ : WithTop ℕ∞))
    (X Y Z : ContMDiffSection I E (∞ : WithTop ℕ∞)
      (TangentSpace I : M → Type _))
    (x : M) :
    ContMDiffAt I (I.prod 𝓘(Real, E)) (∞ : WithTop ℕ∞)
      (T% (fun p : M =>
        connectionRiemannCurvatureField cov
          (fun q : M => X q) (fun q : M => Y q) (fun q : M => Z q) p)) x := by
  haveI : IsManifold I ((∞ : WithTop ℕ∞) + 1) M := by
    simpa using (inferInstance : IsManifold I ∞ M)
  haveI : IsManifold I (minSmoothness Real 2) M := by
    rw [minSmoothness_of_isRCLikeNormedField]
    exact IsManifold.of_le (I := I) (M := M) (n := ∞)
      (by exact WithTop.coe_le_coe.2 (le_top : (2 : ℕ∞) ≤ ⊤))
  let YZ : ContMDiffSection I E (∞ : WithTop ℕ∞)
      (TangentSpace I : M → Type _) :=
    ⟨fun p : M => (cov (fun q : M => Z q) p) (Y p), by
      intro p
      exact cov_smooth_apply_contMDiffAt (I := I) cov hcov Y Z p⟩
  let XZ : ContMDiffSection I E (∞ : WithTop ℕ∞)
      (TangentSpace I : M → Type _) :=
    ⟨fun p : M => (cov (fun q : M => Z q) p) (X p), by
      intro p
      exact cov_smooth_apply_contMDiffAt (I := I) cov hcov X Z p⟩
  let B : ContMDiffSection I E (∞ : WithTop ℕ∞)
      (TangentSpace I : M → Type _) :=
    ⟨fun p : M => VectorField.mlieBracket I (fun q : M => X q) (fun q : M => Y q) p, by
      intro p
      exact
        ContMDiffAt.mlieBracket_vectorField (I := I) (m := (⊤ : ℕ∞))
          (n := (⊤ : ℕ∞)) (X.contMDiff.contMDiffAt)
          (Y.contMDiff.contMDiffAt) (by
            simp [minSmoothness_of_isRCLikeNormedField])⟩
  have h1 :
      ContMDiffAt I (I.prod 𝓘(Real, E)) (∞ : WithTop ℕ∞)
        (T% (fun p : M => (cov (fun q : M => YZ q) p) (X p))) x :=
    cov_smooth_apply_contMDiffAt (I := I) cov hcov X YZ x
  have h2 :
      ContMDiffAt I (I.prod 𝓘(Real, E)) (∞ : WithTop ℕ∞)
        (T% (fun p : M => (cov (fun q : M => XZ q) p) (Y p))) x :=
    cov_smooth_apply_contMDiffAt (I := I) cov hcov Y XZ x
  have h3 :
      ContMDiffAt I (I.prod 𝓘(Real, E)) (∞ : WithTop ℕ∞)
        (T% (fun p : M => (cov (fun q : M => Z q) p) (B p))) x :=
    cov_smooth_apply_contMDiffAt (I := I) cov hcov B Z x
  simpa [RicciFlower.Curvature.connectionRiemannCurvatureField, YZ, XZ, B] using
    (h1.sub_section h2).sub_section h3

private theorem metric_inner_contMDiffAt
    (g : SmoothRiemannianMetric I M)
    {X Y : (p : M) → TangentSpace I p} {x : M} {n : WithTop ℕ∞}
    (hX : ContMDiffAt I (I.prod 𝓘(Real, E)) n (T% X) x)
    (hY : ContMDiffAt I (I.prod 𝓘(Real, E)) n (T% Y) x) :
    ContMDiffAt I 𝓘(Real, Real) n
      (fun y : M => g.inner y (X y) (Y y)) x := by
  have hg :
      ContMDiffAt I
        (I.prod 𝓘(Real, E →L[Real] E →L[Real] Real)) n
        (fun y : M =>
          TotalSpace.mk' (E →L[Real] E →L[Real] Real)
            (E := fun y : M =>
              TangentSpace I y →L[Real] TangentSpace I y →L[Real] Real)
            y (g.inner y)) x :=
    (g.contMDiff.contMDiffAt).of_le le_top
  have htotal :
      ContMDiffAt I (I.prod 𝓘(Real, Real)) n
        (fun y : M =>
          TotalSpace.mk' Real (E := Bundle.Trivial M Real) y
            (g.inner y (X y) (Y y))) x := by
    exact ContMDiffAt.clm_bundle_apply₂
      (F₁ := E) (F₂ := E) hg hX hY
  rw [contMDiffAt_totalSpace] at htotal
  exact htotal.2

private theorem cov_tangentConst_add_apply_eventuallyEq
    (cov : CovariantDerivative I E (TangentSpace I : M → Type _))
    (x : M) (v₁ v₂ w : TangentSpace I x) :
    (fun p : M => (cov (tangentConstAt (I := I) x (v₁ + v₂)) p)
        (tangentConstAt (I := I) x w p))
      =ᶠ[𝓝 x]
    (fun p : M =>
      (cov (tangentConstAt (I := I) x v₁) p) (tangentConstAt (I := I) x w p) +
        (cov (tangentConstAt (I := I) x v₂) p) (tangentConstAt (I := I) x w p)) := by
  let e := trivializationAt E (TangentSpace I) x
  have hx : x ∈ e.baseSet := by
    simp [e]
  filter_upwards [e.open_baseSet.mem_nhds hx] with p hp
  have hv₁ : MDiffAt (T% (tangentConstAt (I := I) x v₁ : (p : M) → TangentSpace I p)) p := by
    unfold tangentConstAt
    exact TensorLieDeriv.mdifferentiableAt_tangentConstInChart_of_mem
      (𝕜 := Real) (I := I) (x₀ := x) (p := p) v₁ (by simpa [e] using hp)
  have hv₂ : MDiffAt (T% (tangentConstAt (I := I) x v₂ : (p : M) → TangentSpace I p)) p := by
    unfold tangentConstAt
    exact TensorLieDeriv.mdifferentiableAt_tangentConstInChart_of_mem
      (𝕜 := Real) (I := I) (x₀ := x) (p := p) v₂ (by simpa [e] using hp)
  rw [tangentConstAt_add]
  rw [cov.isCovariantDerivativeOnUniv.add hv₁ hv₂]
  simp

private theorem cov_tangentConst_smul_apply_eventuallyEq
    (cov : CovariantDerivative I E (TangentSpace I : M → Type _))
    (x : M) (a : Real) (v w : TangentSpace I x) :
    (fun p : M => (cov (tangentConstAt (I := I) x (a • v)) p)
        (tangentConstAt (I := I) x w p))
      =ᶠ[𝓝 x]
    (fun p : M =>
      a • (cov (tangentConstAt (I := I) x v) p) (tangentConstAt (I := I) x w p)) := by
  let e := trivializationAt E (TangentSpace I) x
  have hx : x ∈ e.baseSet := by
    simp [e]
  filter_upwards [e.open_baseSet.mem_nhds hx] with p hp
  have hv : MDiffAt (T% (tangentConstAt (I := I) x v : (p : M) → TangentSpace I p)) p := by
    unfold tangentConstAt
    exact TensorLieDeriv.mdifferentiableAt_tangentConstInChart_of_mem
      (𝕜 := Real) (I := I) (x₀ := x) (p := p) v (by simpa [e] using hp)
  rw [tangentConstAt_smul]
  rw [cov.isCovariantDerivativeOnUniv.smul_const a hv]
  simp [Pi.smul_apply]

/-- The curvature operator of a covariant derivative, before tensorial descent.

The sign convention is
`∇_X ∇_Y Z - ∇_Y ∇_X Z - ∇_[X,Y] Z`.
-/
def riemannCurvatureAux
    (cov : CovariantDerivative I E (TangentSpace I : M → Type _))
    (X Y Z : (p : M) → TangentSpace I p) (x : M) : TangentSpace I x :=
  (cov (fun p => (cov Z p) (Y p)) x) (X x) -
    (cov (fun p => (cov Z p) (X p)) x) (Y x) -
      (cov Z x) (VectorField.mlieBracket I X Y x)

@[simp]
theorem riemannCurvatureAux_eq_connectionRiemannCurvatureField
    (cov : CovariantDerivative I E (TangentSpace I : M → Type _))
    (X Y Z : (p : M) → TangentSpace I p) (x : M) :
    riemannCurvatureAux cov X Y Z x =
      connectionRiemannCurvatureField cov X Y Z x := rfl

/-- Germ congruence for the connection curvature operator on smooth bundled
tangent sections. -/
theorem connectionRiemannCurvatureField_congr_of_eventuallyEq
    (cov : CovariantDerivative I E (TangentSpace I : M → Type _))
    (hcov : CovariantDerivative.ContMDiffCovariantDerivativeLocally cov
      (∞ : WithTop ℕ∞))
    (X X' Y Y' Z Z' :
      ContMDiffSection I E (∞ : WithTop ℕ∞) (TangentSpace I : M → Type _))
    {x : M}
    (hX : (fun p : M => X p) =ᶠ[𝓝 x] fun p : M => X' p)
    (hY : (fun p : M => Y p) =ᶠ[𝓝 x] fun p : M => Y' p)
    (hZ : (fun p : M => Z p) =ᶠ[𝓝 x] fun p : M => Z' p) :
    connectionRiemannCurvatureField cov
        (fun p : M => X p) (fun p : M => Y p) (fun p : M => Z p) x =
      connectionRiemannCurvatureField cov
        (fun p : M => X' p) (fun p : M => Y' p) (fun p : M => Z' p) x := by
  classical
  have hXx : X x = X' x := hX.self_of_nhds
  have hYx : Y x = Y' x := hY.self_of_nhds
  have hbr :
      VectorField.mlieBracket I (fun p : M => X p) (fun p : M => Y p) x =
        VectorField.mlieBracket I (fun p : M => X' p) (fun p : M => Y' p) x :=
    hX.mlieBracket_vectorField_eq (I := I) hY
  have hZ_at :
      cov (fun p : M => Z p) x = cov (fun p : M => Z' p) x := by
    exact cov.isCovariantDerivativeOnUniv.congr_of_eventuallyEq
      (Z.contMDiff.contMDiffAt.mdifferentiableAt (by simp))
      (Z'.contMDiff.contMDiffAt.mdifferentiableAt (by simp))
      (by simp) hZ
  have hinnerY :
      (fun p : M => (cov (fun q : M => Z q) p) (Y p)) =ᶠ[𝓝 x]
        (fun p : M => (cov (fun q : M => Z' q) p) (Y' p)) := by
    rcases mem_nhds_iff.mp (hZ : {p : M | Z p = Z' p} ∈ 𝓝 x) with
      ⟨U, hUsub, hUopen, hxU⟩
    filter_upwards [hUopen.mem_nhds hxU, hY] with p hpU hYp
    have hZp :
        (fun q : M => Z q) =ᶠ[𝓝 p] fun q : M => Z' q := by
      exact Filter.eventuallyEq_of_mem (hUopen.mem_nhds hpU) fun q hq => hUsub hq
    have hcovp :
        cov (fun q : M => Z q) p = cov (fun q : M => Z' q) p := by
      exact cov.isCovariantDerivativeOnUniv.congr_of_eventuallyEq
        (Z.contMDiff.contMDiffAt.mdifferentiableAt (by simp))
        (Z'.contMDiff.contMDiffAt.mdifferentiableAt (by simp))
        (by simp) hZp
    rw [hcovp, hYp]
  have hinnerX :
      (fun p : M => (cov (fun q : M => Z q) p) (X p)) =ᶠ[𝓝 x]
        (fun p : M => (cov (fun q : M => Z' q) p) (X' p)) := by
    rcases mem_nhds_iff.mp (hZ : {p : M | Z p = Z' p} ∈ 𝓝 x) with
      ⟨U, hUsub, hUopen, hxU⟩
    filter_upwards [hUopen.mem_nhds hxU, hX] with p hpU hXp
    have hZp :
        (fun q : M => Z q) =ᶠ[𝓝 p] fun q : M => Z' q := by
      exact Filter.eventuallyEq_of_mem (hUopen.mem_nhds hpU) fun q hq => hUsub hq
    have hcovp :
        cov (fun q : M => Z q) p = cov (fun q : M => Z' q) p := by
      exact cov.isCovariantDerivativeOnUniv.congr_of_eventuallyEq
        (Z.contMDiff.contMDiffAt.mdifferentiableAt (by simp))
        (Z'.contMDiff.contMDiffAt.mdifferentiableAt (by simp))
        (by simp) hZp
    rw [hcovp, hXp]
  have hcovZY :
      cov (fun p : M => (cov (fun q : M => Z q) p) (Y p)) x =
        cov (fun p : M => (cov (fun q : M => Z' q) p) (Y' p)) x := by
    exact cov.isCovariantDerivativeOnUniv.congr_of_eventuallyEq
      (cov_smooth_apply_mdiffAt (I := I) cov hcov Y Z x)
      (cov_smooth_apply_mdiffAt (I := I) cov hcov Y' Z' x)
      (by simp) hinnerY
  have hcovZX :
      cov (fun p : M => (cov (fun q : M => Z q) p) (X p)) x =
        cov (fun p : M => (cov (fun q : M => Z' q) p) (X' p)) x := by
    exact cov.isCovariantDerivativeOnUniv.congr_of_eventuallyEq
      (cov_smooth_apply_mdiffAt (I := I) cov hcov X Z x)
      (cov_smooth_apply_mdiffAt (I := I) cov hcov X' Z' x)
      (by simp) hinnerX
  simp [RicciFlower.Curvature.connectionRiemannCurvatureField, hcovZY, hcovZX,
    hZ_at, hXx, hYx, hbr]

private theorem connectionRiemannCurvatureField_tensorial_left
    (cov : CovariantDerivative I E (TangentSpace I : M → Type _))
    (hcov : CovariantDerivative.ContMDiffCovariantDerivativeLocally cov
      (∞ : WithTop ℕ∞))
    (Y Z : ContMDiffSection I E (∞ : WithTop ℕ∞)
      (TangentSpace I : M → Type _))
    (x : M) :
    TensorialAt I E
      (fun X : (p : M) → TangentSpace I p =>
        connectionRiemannCurvatureField cov X
          (fun p : M => Y p) (fun p : M => Z p) x) x where
  smul {f} {σ} hf hσ := by
    have hZY : MDiffAt
        (T% (fun p : M => (cov (fun q : M => Z q) p) (Y p))) x :=
      cov_smooth_apply_mdiffAt (I := I) cov hcov Y Z x
    have hZσ : MDiffAt
        (T% (fun p : M => (cov (fun q : M => Z q) p) (σ p))) x :=
      cov_smooth_apply_raw_mdiffAt (I := I) cov hcov Z hσ
    have hmid :
        (fun p : M => (cov (fun q : M => Z q) p) ((f • σ) p)) =
          f • (fun p : M => (cov (fun q : M => Z q) p) (σ p)) := by
      funext p
      simp [map_smul]
    simp only [RicciFlower.Curvature.connectionRiemannCurvatureField]
    rw [hmid]
    rw [cov.isCovariantDerivativeOnUniv.leibniz hZσ hf]
    rw [VectorField.mlieBracket_smul_left (I := I) hf hσ]
    simp [map_smul]
    module
  add {σ σ'} hσ hσ' := by
    have hZY : MDiffAt
        (T% (fun p : M => (cov (fun q : M => Z q) p) (Y p))) x :=
      cov_smooth_apply_mdiffAt (I := I) cov hcov Y Z x
    have hZσ : MDiffAt
        (T% (fun p : M => (cov (fun q : M => Z q) p) (σ p))) x :=
      cov_smooth_apply_raw_mdiffAt (I := I) cov hcov Z hσ
    have hZσ' : MDiffAt
        (T% (fun p : M => (cov (fun q : M => Z q) p) (σ' p))) x :=
      cov_smooth_apply_raw_mdiffAt (I := I) cov hcov Z hσ'
    have hmid :
        (fun p : M => (cov (fun q : M => Z q) p) ((σ + σ') p)) =
          (fun p : M => (cov (fun q : M => Z q) p) (σ p)) +
            (fun p : M => (cov (fun q : M => Z q) p) (σ' p)) := by
      funext p
      simp [map_add]
    simp only [RicciFlower.Curvature.connectionRiemannCurvatureField]
    rw [hmid]
    rw [cov.isCovariantDerivativeOnUniv.add hZσ hZσ']
    rw [VectorField.mlieBracket_add_left (I := I) hσ hσ']
    simp [map_add]
    module

private theorem connectionRiemannCurvatureField_tensorial_middle
    (cov : CovariantDerivative I E (TangentSpace I : M → Type _))
    (hcov : CovariantDerivative.ContMDiffCovariantDerivativeLocally cov
      (∞ : WithTop ℕ∞))
    (X Z : ContMDiffSection I E (∞ : WithTop ℕ∞)
      (TangentSpace I : M → Type _))
    (x : M) :
    TensorialAt I E
      (fun Y : (p : M) → TangentSpace I p =>
        connectionRiemannCurvatureField cov
          (fun p : M => X p) Y (fun p : M => Z p) x) x where
  smul {f} {σ} hf hσ := by
    have hleft :=
      (connectionRiemannCurvatureField_tensorial_left
        (I := I) cov hcov X Z x).smul (f := f) (σ := σ) hf hσ
    rw [RicciFlower.Curvature.connectionRiemannCurvatureField_swap
      (I := I) (cov := cov) (X := f • σ) (Y := fun p : M => X p)
      (Z := fun p : M => Z p) (x := x)]
    rw [RicciFlower.Curvature.connectionRiemannCurvatureField_swap
      (I := I) (cov := cov) (X := σ) (Y := fun p : M => X p)
      (Z := fun p : M => Z p) (x := x)]
    rw [hleft]
    module
  add {σ σ'} hσ hσ' := by
    have hleft :=
      (connectionRiemannCurvatureField_tensorial_left
        (I := I) cov hcov X Z x).add (σ := σ) (σ' := σ') hσ hσ'
    rw [RicciFlower.Curvature.connectionRiemannCurvatureField_swap
      (I := I) (cov := cov) (X := σ + σ') (Y := fun p : M => X p)
      (Z := fun p : M => Z p) (x := x)]
    rw [RicciFlower.Curvature.connectionRiemannCurvatureField_swap
      (I := I) (cov := cov) (X := σ) (Y := fun p : M => X p)
      (Z := fun p : M => Z p) (x := x)]
    rw [RicciFlower.Curvature.connectionRiemannCurvatureField_swap
      (I := I) (cov := cov) (X := σ') (Y := fun p : M => X p)
      (Z := fun p : M => Z p) (x := x)]
    rw [hleft]
    module

/-- Pointwise tensoriality in the two curvature-direction slots.  The third
slot is harder because its scalar rule contains the second-derivative bracket
commutator cancellation. -/
theorem connectionRiemannCurvatureField_congr_first_two_point
    (cov : CovariantDerivative I E (TangentSpace I : M → Type _))
    (hcov : CovariantDerivative.ContMDiffCovariantDerivativeLocally cov
      (∞ : WithTop ℕ∞))
    (X X' Y Y' Z :
      ContMDiffSection I E (∞ : WithTop ℕ∞) (TangentSpace I : M → Type _))
    {x : M}
    (hX : X x = X' x) (hY : Y x = Y' x) :
    connectionRiemannCurvatureField cov
        (fun p : M => X p) (fun p : M => Y p) (fun p : M => Z p) x =
      connectionRiemannCurvatureField cov
        (fun p : M => X' p) (fun p : M => Y' p) (fun p : M => Z p) x := by
  have hXmd : MDiffAt (T% (fun p : M => X p)) x :=
    X.contMDiff.contMDiffAt.mdifferentiableAt (by simp)
  have hX'md : MDiffAt (T% (fun p : M => X' p)) x :=
    X'.contMDiff.contMDiffAt.mdifferentiableAt (by simp)
  have hYmd : MDiffAt (T% (fun p : M => Y p)) x :=
    Y.contMDiff.contMDiffAt.mdifferentiableAt (by simp)
  have hY'md : MDiffAt (T% (fun p : M => Y' p)) x :=
    Y'.contMDiff.contMDiffAt.mdifferentiableAt (by simp)
  calc
    connectionRiemannCurvatureField cov
        (fun p : M => X p) (fun p : M => Y p) (fun p : M => Z p) x
        =
      connectionRiemannCurvatureField cov
        (fun p : M => X' p) (fun p : M => Y p) (fun p : M => Z p) x := by
        exact
          (connectionRiemannCurvatureField_tensorial_left
            (I := I) cov hcov Y Z x).pointwise hXmd hX'md hX
    _ =
      connectionRiemannCurvatureField cov
        (fun p : M => X' p) (fun p : M => Y' p) (fun p : M => Z p) x := by
        exact
          (connectionRiemannCurvatureField_tensorial_middle
            (I := I) cov hcov X' Z x).pointwise hYmd hY'md hY

/-- Smooth scalar linearity in the curvature-output slot.

This is the Leibniz-expansion cancellation:
the extra coefficient is
`X(Y f) - Y(X f) - [X,Y] f`, hence vanishes by the scalar Lie-bracket
commutator formula. -/
private theorem connectionRiemannCurvatureField_smul_right_smooth
    (cov : CovariantDerivative I E (TangentSpace I : M → Type _))
    (hcov : CovariantDerivative.ContMDiffCovariantDerivativeLocally cov
      (∞ : WithTop ℕ∞))
    (X Y Z :
      ContMDiffSection I E (∞ : WithTop ℕ∞) (TangentSpace I : M → Type _))
    {f : M → Real}
    (hf : ContMDiff I 𝓘(Real, Real) (∞ : WithTop ℕ∞) f)
    (x : M) :
    connectionRiemannCurvatureField cov
        (fun p : M => X p) (fun p : M => Y p)
        (fun p : M => f p • Z p) x =
      f x • connectionRiemannCurvatureField cov
        (fun p : M => X p) (fun p : M => Y p)
        (fun p : M => Z p) x := by
  let Xf : M → Real := fun p => extDerivFun (I := I) f p (X p)
  let Yf : M → Real := fun p => extDerivFun (I := I) f p (Y p)
  let YZ : (p : M) → TangentSpace I p :=
    fun p => (cov (fun q : M => Z q) p) (Y p)
  let XZ : (p : M) → TangentSpace I p :=
    fun p => (cov (fun q : M => Z q) p) (X p)
  have hfmd : MDiffAt f x :=
    hf.contMDiffAt.mdifferentiableAt (by simp)
  have hXmd : MDiffAt (T% (fun p : M => X p)) x :=
    X.contMDiff.contMDiffAt.mdifferentiableAt (by simp)
  have hYmd : MDiffAt (T% (fun p : M => Y p)) x :=
    Y.contMDiff.contMDiffAt.mdifferentiableAt (by simp)
  have hZmd : MDiffAt (T% (fun p : M => Z p)) x :=
    Z.contMDiff.contMDiffAt.mdifferentiableAt (by simp)
  have hYZmd : MDiffAt (T% YZ) x :=
    cov_smooth_apply_mdiffAt (I := I) cov hcov Y Z x
  have hXZmd : MDiffAt (T% XZ) x :=
    cov_smooth_apply_mdiffAt (I := I) cov hcov X Z x
  have hYfmd : MDiffAt Yf x :=
    (RicciFlower.extDerivFun_apply_contMDiffAt (I := I)
      hf.contMDiffAt Y).mdifferentiableAt (by simp)
  have hXfmd : MDiffAt Xf x :=
    (RicciFlower.extDerivFun_apply_contMDiffAt (I := I)
      hf.contMDiffAt X).mdifferentiableAt (by simp)
  have hinnerY :
      (fun p : M => (cov (fun q : M => f q • Z q) p) (Y p)) =
        f • YZ + Yf • (fun p : M => Z p) := by
    funext p
    have hleib :
        cov (fun q : M => f q • Z q) p =
          f p • cov (fun q : M => Z q) p +
            (extDerivFun (I := I) f p).smulRight (Z p) := by
      simpa using
        (cov.isCovariantDerivativeOnUniv.leibniz
          (σ := fun q : M => Z q) (g := f) (x := p)
          (Z.contMDiff.contMDiffAt.mdifferentiableAt (by simp))
          (hf.contMDiffAt.mdifferentiableAt (by simp)))
    simpa [YZ, Yf, Pi.add_apply, Pi.smul_apply] using
      congrArg (fun L : TangentSpace I p →L[Real] TangentSpace I p => L (Y p)) hleib
  have hinnerX :
      (fun p : M => (cov (fun q : M => f q • Z q) p) (X p)) =
        f • XZ + Xf • (fun p : M => Z p) := by
    funext p
    have hleib :
        cov (fun q : M => f q • Z q) p =
          f p • cov (fun q : M => Z q) p +
            (extDerivFun (I := I) f p).smulRight (Z p) := by
      simpa using
        (cov.isCovariantDerivativeOnUniv.leibniz
          (σ := fun q : M => Z q) (g := f) (x := p)
          (Z.contMDiff.contMDiffAt.mdifferentiableAt (by simp))
          (hf.contMDiffAt.mdifferentiableAt (by simp)))
    simpa [XZ, Xf, Pi.add_apply, Pi.smul_apply] using
      congrArg (fun L : TangentSpace I p →L[Real] TangentSpace I p => L (X p)) hleib
  have hX2 :
      ContMDiffAt I (I.prod 𝓘(Real, E)) (minSmoothness Real 2)
        (T% (fun p : M => X p)) x := by
    exact X.contMDiff.contMDiffAt.of_le (by
      rw [minSmoothness_of_isRCLikeNormedField]
      exact WithTop.coe_le_coe.2 (le_top : (2 : ℕ∞) ≤ (⊤ : ℕ∞)))
  have hY2 :
      ContMDiffAt I (I.prod 𝓘(Real, E)) (minSmoothness Real 2)
        (T% (fun p : M => Y p)) x := by
    exact Y.contMDiff.contMDiffAt.of_le (by
      rw [minSmoothness_of_isRCLikeNormedField]
      exact WithTop.coe_le_coe.2 (le_top : (2 : ℕ∞) ≤ (⊤ : ℕ∞)))
  have hf2 : ContMDiffAt I 𝓘(Real, Real) (minSmoothness Real 2) f x := by
    exact hf.contMDiffAt.of_le (by
      rw [minSmoothness_of_isRCLikeNormedField]
      exact WithTop.coe_le_coe.2 (le_top : (2 : ℕ∞) ≤ (⊤ : ℕ∞)))
  have hscalar :
      extDerivFun (I := I) f x
          (VectorField.mlieBracket I (fun p : M => X p) (fun p : M => Y p) x) =
        extDerivFun (I := I) Yf x (X x) -
          extDerivFun (I := I) Xf x (Y x) := by
    simpa [vderiv, Xf, Yf] using
      (RicciFlower.vderiv_mlieBracket
        (I := I) (fun p : M => X p) (fun p : M => Y p) f x hX2 hY2 hf2)
  simp only [RicciFlower.Curvature.connectionRiemannCurvatureField]
  rw [hinnerY, hinnerX]
  rw [cov.isCovariantDerivativeOnUniv.add
    ((hfmd.smul_section hYZmd)) (hYfmd.smul_section hZmd)]
  rw [cov.isCovariantDerivativeOnUniv.add
    ((hfmd.smul_section hXZmd)) (hXfmd.smul_section hZmd)]
  rw [cov.isCovariantDerivativeOnUniv.leibniz hYZmd hfmd]
  rw [cov.isCovariantDerivativeOnUniv.leibniz hZmd hYfmd]
  rw [cov.isCovariantDerivativeOnUniv.leibniz hXZmd hfmd]
  rw [cov.isCovariantDerivativeOnUniv.leibniz hZmd hXfmd]
  have hZsmul : (fun p : M => f p • Z p) = f • (fun p : M => Z p) := rfl
  rw [hZsmul]
  rw [cov.isCovariantDerivativeOnUniv.leibniz hZmd hfmd]
  simp [YZ, XZ, Xf, Yf, hscalar]
  module

/-- Smooth additivity in the curvature-output slot. -/
private theorem connectionRiemannCurvatureField_add_right_smooth
    (cov : CovariantDerivative I E (TangentSpace I : M → Type _))
    (hcov : CovariantDerivative.ContMDiffCovariantDerivativeLocally cov
      (∞ : WithTop ℕ∞))
    (X Y Z Z' :
      ContMDiffSection I E (∞ : WithTop ℕ∞) (TangentSpace I : M → Type _))
    (x : M) :
    connectionRiemannCurvatureField cov
        (fun p : M => X p) (fun p : M => Y p)
        (fun p : M => (Z + Z') p) x =
      connectionRiemannCurvatureField cov
          (fun p : M => X p) (fun p : M => Y p)
          (fun p : M => Z p) x +
        connectionRiemannCurvatureField cov
          (fun p : M => X p) (fun p : M => Y p)
          (fun p : M => Z' p) x := by
  let YZ : (p : M) → TangentSpace I p :=
    fun p => (cov (fun q : M => Z q) p) (Y p)
  let YZ' : (p : M) → TangentSpace I p :=
    fun p => (cov (fun q : M => Z' q) p) (Y p)
  let XZ : (p : M) → TangentSpace I p :=
    fun p => (cov (fun q : M => Z q) p) (X p)
  let XZ' : (p : M) → TangentSpace I p :=
    fun p => (cov (fun q : M => Z' q) p) (X p)
  have hZmd : MDiffAt (T% (fun p : M => Z p)) x :=
    Z.contMDiff.contMDiffAt.mdifferentiableAt (by simp)
  have hZ'md : MDiffAt (T% (fun p : M => Z' p)) x :=
    Z'.contMDiff.contMDiffAt.mdifferentiableAt (by simp)
  have hYZmd : MDiffAt (T% YZ) x :=
    cov_smooth_apply_mdiffAt (I := I) cov hcov Y Z x
  have hYZ'md : MDiffAt (T% YZ') x :=
    cov_smooth_apply_mdiffAt (I := I) cov hcov Y Z' x
  have hXZmd : MDiffAt (T% XZ) x :=
    cov_smooth_apply_mdiffAt (I := I) cov hcov X Z x
  have hXZ'md : MDiffAt (T% XZ') x :=
    cov_smooth_apply_mdiffAt (I := I) cov hcov X Z' x
  have hinnerY :
      (fun p : M => (cov (fun q : M => (Z + Z') q) p) (Y p)) = YZ + YZ' := by
    funext p
    have hleib :
        cov (fun q : M => (Z + Z') q) p =
          cov (fun q : M => Z q) p + cov (fun q : M => Z' q) p := by
      simpa using
        (cov.isCovariantDerivativeOnUniv.add
          (σ := fun q : M => Z q) (σ' := fun q : M => Z' q) (x := p)
          (Z.contMDiff.contMDiffAt.mdifferentiableAt (by simp))
          (Z'.contMDiff.contMDiffAt.mdifferentiableAt (by simp)))
    simpa [YZ, YZ', Pi.add_apply] using
      congrArg (fun L : TangentSpace I p →L[Real] TangentSpace I p => L (Y p)) hleib
  have hinnerX :
      (fun p : M => (cov (fun q : M => (Z + Z') q) p) (X p)) = XZ + XZ' := by
    funext p
    have hleib :
        cov (fun q : M => (Z + Z') q) p =
          cov (fun q : M => Z q) p + cov (fun q : M => Z' q) p := by
      simpa using
        (cov.isCovariantDerivativeOnUniv.add
          (σ := fun q : M => Z q) (σ' := fun q : M => Z' q) (x := p)
          (Z.contMDiff.contMDiffAt.mdifferentiableAt (by simp))
          (Z'.contMDiff.contMDiffAt.mdifferentiableAt (by simp)))
    simpa [XZ, XZ', Pi.add_apply] using
      congrArg (fun L : TangentSpace I p →L[Real] TangentSpace I p => L (X p)) hleib
  simp only [RicciFlower.Curvature.connectionRiemannCurvatureField]
  rw [hinnerY, hinnerX]
  rw [cov.isCovariantDerivativeOnUniv.add hYZmd hYZ'md]
  rw [cov.isCovariantDerivativeOnUniv.add hXZmd hXZ'md]
  have hZadd :
      (fun p : M => (Z + Z') p) =
        (fun p : M => Z p) + (fun p : M => Z' p) := rfl
  rw [hZadd]
  rw [cov.isCovariantDerivativeOnUniv.add hZmd hZ'md]
  simp [YZ, YZ', XZ, XZ']
  module

private theorem smooth_linear_tangentSection_pointwise
    [T2Space M]
    {x : M}
    (Φ :
      ContMDiffSection I E (∞ : WithTop ℕ∞) (TangentSpace I : M → Type _) →
        TangentSpace I x)
    (hadd : ∀ σ τ, Φ (σ + τ) = Φ σ + Φ τ)
    (hsmul : ∀ (f : C^∞⟮I, M; Real⟯) σ, Φ (f • σ) = f x • Φ σ)
    {σ τ : ContMDiffSection I E (∞ : WithTop ℕ∞) (TangentSpace I : M → Type _)}
    (hστ : σ x = τ x) :
    Φ σ = Φ τ := by
  classical
  have hzero : Φ 0 = 0 := by
    let z : C^∞⟮I, M; Real⟯ := ⟨fun _ => (0 : Real), contMDiff_const⟩
    have h := hsmul z (0 :
      ContMDiffSection I E (∞ : WithTop ℕ∞) (TangentSpace I : M → Type _))
    simpa [z] using h
  have hneg : ∀ σ, Φ (-σ) = -Φ σ := by
    intro σ
    let m : C^∞⟮I, M; Real⟯ := ⟨fun _ => (-1 : Real), contMDiff_const⟩
    have h := hsmul m σ
    have hm : m • σ = -σ := by
      ext y
      simp [m, ContMDiffSection.coe_smulContMDiffMap]
    rw [hm] at h
    simpa [m] using h
  have hsub : ∀ σ τ, Φ (σ - τ) = Φ σ - Φ τ := by
    intro σ τ
    calc
      Φ (σ - τ) = Φ (σ + -τ) := by rw [sub_eq_add_neg]
      _ = Φ σ + Φ (-τ) := hadd σ (-τ)
      _ = Φ σ - Φ τ := by rw [hneg τ, sub_eq_add_neg]
  have hsum :
      ∀ (s : Finset (Fin (Module.finrank Real E)))
        (u : Fin (Module.finrank Real E) →
          ContMDiffSection I E (∞ : WithTop ℕ∞) (TangentSpace I : M → Type _)),
        Φ (∑ i ∈ s, u i) = ∑ i ∈ s, Φ (u i) := by
    intro s
    induction s using Finset.induction_on with
    | empty =>
        intro u
        simp [hzero]
    | insert a s ha ih =>
        intro u
        simp [Finset.sum_insert ha, hadd, ih]
  have hlocal :
      ∀ (δ : ContMDiffSection I E (∞ : WithTop ℕ∞) (TangentSpace I : M → Type _))
        {U : Set M}, IsOpen U → x ∈ U → (∀ y ∈ U, δ y = 0) → Φ δ = 0 := by
    intro δ U hU hxU hδU
    obtain ⟨ψ, -, hψsupp⟩ :=
      (SmoothBumpFunction.nhds_basis_tsupport (I := I) x).mem_iff.mp
        (hU.mem_nhds hxU)
    let ψ' : C^∞⟮I, M; Real⟯ :=
      ⟨ψ, ψ.contMDiff⟩
    have hψδ : ψ' • δ = 0 := by
      ext y
      simp only [ContMDiffSection.coe_smulContMDiffMap,
        ContMDiffSection.coe_zero, Pi.zero_apply]
      by_cases hy : y ∈ Function.support (ψ : M → Real)
      · exact smul_eq_zero_of_right _ (hδU y (hψsupp (subset_closure hy)))
      · simp only [Function.mem_support, not_not] at hy
        exact smul_eq_zero_of_left hy _
    have h := hsmul ψ' δ
    rw [hψδ, hzero] at h
    simpa [ψ', ψ.eq_one] using h.symm
  suffices hvanish :
      ∀ δ : ContMDiffSection I E (∞ : WithTop ℕ∞) (TangentSpace I : M → Type _),
        δ x = 0 → Φ δ = 0 by
    have hδ := hvanish (σ - τ) (by
      simp only [ContMDiffSection.coe_sub, Pi.sub_apply, sub_eq_zero]
      exact hστ)
    rw [hsub σ τ] at hδ
    exact sub_eq_zero.mp hδ
  intro δ hδx
  let e := trivializationAt E (TangentSpace I) x
  let b := Module.finBasis Real E
  have he : x ∈ e.baseSet := mem_baseSet_trivializationAt E (TangentSpace I) x
  have hframe := e.isLocalFrameOn_localFrame_baseSet I (∞ : WithTop ℕ∞) b
  obtain ⟨s', hs'⟩ := hframe.exists_contMDiffSection_eqOn_nhd e.open_baseSet he
  obtain ⟨χ, -, hχsupp⟩ :=
    (SmoothBumpFunction.nhds_basis_tsupport (I := I) x).mem_iff.mp
      (e.open_baseSet.mem_nhds he)
  have hcoeff_smooth : ∀ i, ContMDiff I 𝓘(Real) (∞ : WithTop ℕ∞)
      (fun y : M => χ y • hframe.coeff i y (δ y)) := by
    intro i y
    by_cases hy : y ∈ tsupport (χ : M → Real)
    · have hcoeff :
          ContMDiffAt I 𝓘(Real) (∞ : WithTop ℕ∞)
            (fun y : M => e.localFrame_coeff I b i y (δ y)) y :=
        contMDiffAt_localFrame_coeff b (hχsupp hy) δ.contMDiff.contMDiffAt i
      have hχy : ContMDiffAt I 𝓘(Real) (∞ : WithTop ℕ∞) (χ : M → Real) y :=
        χ.contMDiff.contMDiffAt
      refine (hχy.smul hcoeff).congr_of_eventuallyEq ?_
      filter_upwards [((e.open_baseSet).mem_nhds (hχsupp hy))] with z hz
      have hbasis : e.basisAt b hz = hframe.toBasisAt hz := by
        ext j
        simp [IsLocalFrameOn.toBasisAt, Trivialization.localFrame,
          Trivialization.basisAt, hz]
      simp only [hframe.coeff_apply_of_mem hz,
        e.localFrame_coeff_apply_of_mem_baseSet b hz, hbasis]
    · have hχ_zero : ∀ᶠ z in 𝓝 y, (χ : M → Real) z = 0 := by
        apply Filter.Eventually.mono
          ((isClosed_tsupport (χ : M → Real)).isOpen_compl.mem_nhds hy)
        intro z hz
        exact (notMem_tsupport_iff_eventuallyEq.mp hz).self_of_nhds
      exact (contMDiffAt_const (c := (0 : Real))).congr_of_eventuallyEq
        (hχ_zero.mono fun z hz => by simp [hz])
  let u' : Fin (Module.finrank Real E) → C^∞⟮I, M; Real⟯ := fun i =>
    ⟨fun y : M => χ y • hframe.coeff i y (δ y), hcoeff_smooth i⟩
  have hu'_zero : ∀ i, (u' i) x = 0 := by
    intro i
    change χ x • hframe.coeff i x (δ x) = 0
    rw [χ.eq_one, one_smul, hδx, map_zero]
  have hδ_eq_near : ∀ᶠ y in 𝓝 x,
      δ y = ∑ i, (u' i) y • (s' i) y := by
    filter_upwards [hs', χ.eventuallyEq_one, e.open_baseSet.mem_nhds he] with
      y hs'y hχy hy
    change δ y = ∑ i, (χ y • hframe.coeff i y (δ y)) • (s' i) y
    simp only [show χ y = (1 : M → Real) y from hχy, Pi.one_apply, one_smul]
    conv_lhs => rw [hframe.coeff_sum_eq (⇑δ) hy]
    congr 1
    ext i
    rw [hs'y i]
  obtain ⟨U, hU_open, hxU, hU_vanish⟩ : ∃ U : Set M, IsOpen U ∧ x ∈ U ∧
      ∀ y ∈ U, (δ - ∑ i, u' i • s' i) y = 0 := by
    obtain ⟨U, hU_nhds, hU⟩ := Filter.Eventually.exists_mem hδ_eq_near
    obtain ⟨U', hU'U, hU'_open, hxU'⟩ := mem_nhds_iff.mp hU_nhds
    refine ⟨U', hU'_open, hxU', ?_⟩
    intro y hy
    simp only [ContMDiffSection.coe_sub, Pi.sub_apply, sub_eq_zero,
      ContMDiffSection.finset_sum_apply, ContMDiffSection.coe_smulContMDiffMap]
    exact hU y (hU'U hy)
  have hloc := hlocal (δ - ∑ i, u' i • s' i) hU_open hxU hU_vanish
  rw [hsub δ (∑ i, u' i • s' i)] at hloc
  have hsum_eval :
      Φ (∑ i, u' i • s' i) = ∑ i, Φ (u' i • s' i) :=
    hsum Finset.univ (fun i => u' i • s' i)
  rw [hsum_eval] at hloc
  simp_rw [hsmul] at hloc
  have hsum_zero : (∑ i, (u' i) x • Φ (s' i)) = 0 := by
    exact Finset.sum_eq_zero fun i _ => by rw [hu'_zero i, zero_smul]
  rw [hsum_zero, sub_zero] at hloc
  exact hloc

/-- Pointwise tensoriality of the connection curvature operator on smooth
bundled tangent sections.

This is the central curvature tensoriality frontier.  Mathlib's covariant
derivative congruence gives germ dependence of one derivative; this stronger
statement needs the usual `C∞(M)`-linearity cancellation in all three curvature
slots. -/
theorem connectionRiemannCurvatureField_congr_point
    (cov : CovariantDerivative I E (TangentSpace I : M → Type _))
    (hcov : CovariantDerivative.ContMDiffCovariantDerivativeLocally cov
      (∞ : WithTop ℕ∞))
    [T2Space M]
    (X X' Y Y' Z Z' :
      ContMDiffSection I E (∞ : WithTop ℕ∞) (TangentSpace I : M → Type _))
    {x : M}
    (hX : X x = X' x) (hY : Y x = Y' x) (hZ : Z x = Z' x) :
    connectionRiemannCurvatureField cov
        (fun p : M => X p) (fun p : M => Y p) (fun p : M => Z p) x =
      connectionRiemannCurvatureField cov
        (fun p : M => X' p) (fun p : M => Y' p) (fun p : M => Z' p) x := by
  calc
    connectionRiemannCurvatureField cov
        (fun p : M => X p) (fun p : M => Y p) (fun p : M => Z p) x
        =
      connectionRiemannCurvatureField cov
        (fun p : M => X' p) (fun p : M => Y' p) (fun p : M => Z p) x := by
        exact connectionRiemannCurvatureField_congr_first_two_point
          (I := I) cov hcov X X' Y Y' Z hX hY
    _ =
      connectionRiemannCurvatureField cov
        (fun p : M => X' p) (fun p : M => Y' p) (fun p : M => Z' p) x := by
        exact smooth_linear_tangentSection_pointwise
          (I := I) (x := x)
          (Φ := fun Zsec =>
            connectionRiemannCurvatureField cov
              (fun p : M => X' p) (fun p : M => Y' p)
              (fun p : M => Zsec p) x)
          (fun σ τ =>
            connectionRiemannCurvatureField_add_right_smooth
              (I := I) cov hcov X' Y' σ τ x)
          (fun f σ =>
            connectionRiemannCurvatureField_smul_right_smooth
              (I := I) cov hcov X' Y' σ (f := fun p : M => f p)
              f.contMDiff x)
          hZ

private theorem riemannCurvatureAux_tangentConst_add_first
    (cov : CovariantDerivative I E (TangentSpace I : M → Type _))
    (hcov : CovariantDerivative.ContMDiffCovariantDerivativeLocally cov ∞)
    (x : M) (X₁ X₂ Y Z : TangentSpace I x) :
    riemannCurvatureAux cov
        (tangentConstAt (I := I) x (X₁ + X₂))
        (tangentConstAt (I := I) x Y)
        (tangentConstAt (I := I) x Z) x =
      riemannCurvatureAux cov
          (tangentConstAt (I := I) x X₁)
          (tangentConstAt (I := I) x Y)
          (tangentConstAt (I := I) x Z) x +
        riemannCurvatureAux cov
          (tangentConstAt (I := I) x X₂)
          (tangentConstAt (I := I) x Y)
          (tangentConstAt (I := I) x Z) x := by
  let X₁c : (p : M) → TangentSpace I p := tangentConstAt (I := I) x X₁
  let X₂c : (p : M) → TangentSpace I p := tangentConstAt (I := I) x X₂
  let Yc : (p : M) → TangentSpace I p := tangentConstAt (I := I) x Y
  let Zc : (p : M) → TangentSpace I p := tangentConstAt (I := I) x Z
  have hX₁ : MDiffAt (T% X₁c) x := mdifferentiableAt_tangentConstAt_self (I := I) x X₁
  have hX₂ : MDiffAt (T% X₂c) x := mdifferentiableAt_tangentConstAt_self (I := I) x X₂
  have hZX₁ : MDiffAt (T% (fun p : M => (cov Zc p) (X₁c p))) x := by
    simpa [X₁c, Zc] using cov_tangentConst_apply_mdiffAt_self (I := I) cov hcov x Z X₁
  have hZX₂ : MDiffAt (T% (fun p : M => (cov Zc p) (X₂c p))) x := by
    simpa [X₂c, Zc] using cov_tangentConst_apply_mdiffAt_self (I := I) cov hcov x Z X₂
  have hmid :
      (fun p : M => (cov Zc p) ((X₁c + X₂c) p)) =
        (fun p : M => (cov Zc p) (X₁c p)) +
          (fun p : M => (cov Zc p) (X₂c p)) := by
    funext p
    simp [Pi.add_apply, map_add]
  rw [tangentConstAt_add]
  change
    riemannCurvatureAux cov (X₁c + X₂c) Yc Zc x =
      riemannCurvatureAux cov X₁c Yc Zc x +
        riemannCurvatureAux cov X₂c Yc Zc x
  unfold riemannCurvatureAux
  rw [hmid]
  rw [cov.isCovariantDerivativeOnUniv.add hZX₁ hZX₂]
  rw [VectorField.mlieBracket_add_left (I := I) hX₁ hX₂]
  simp [Pi.add_apply, map_add]
  module

private theorem riemannCurvatureAux_tangentConst_smul_first
    (cov : CovariantDerivative I E (TangentSpace I : M → Type _))
    (hcov : CovariantDerivative.ContMDiffCovariantDerivativeLocally cov ∞)
    (x : M) (a : Real) (X Y Z : TangentSpace I x) :
    riemannCurvatureAux cov
        (tangentConstAt (I := I) x (a • X))
        (tangentConstAt (I := I) x Y)
        (tangentConstAt (I := I) x Z) x =
      a • riemannCurvatureAux cov
          (tangentConstAt (I := I) x X)
          (tangentConstAt (I := I) x Y)
          (tangentConstAt (I := I) x Z) x := by
  let Xc : (p : M) → TangentSpace I p := tangentConstAt (I := I) x X
  let Yc : (p : M) → TangentSpace I p := tangentConstAt (I := I) x Y
  let Zc : (p : M) → TangentSpace I p := tangentConstAt (I := I) x Z
  have hX : MDiffAt (T% Xc) x := mdifferentiableAt_tangentConstAt_self (I := I) x X
  have hZX : MDiffAt (T% (fun p : M => (cov Zc p) (Xc p))) x := by
    simpa [Xc, Zc] using cov_tangentConst_apply_mdiffAt_self (I := I) cov hcov x Z X
  have hmid :
      (fun p : M => (cov Zc p) ((a • Xc) p)) =
        a • (fun p : M => (cov Zc p) (Xc p)) := by
    funext p
    simp [Pi.smul_apply, map_smul]
  rw [tangentConstAt_smul]
  change
    riemannCurvatureAux cov (a • Xc) Yc Zc x =
      a • riemannCurvatureAux cov Xc Yc Zc x
  unfold riemannCurvatureAux
  rw [hmid]
  rw [cov.isCovariantDerivativeOnUniv.smul_const a hZX]
  rw [VectorField.mlieBracket_const_smul_left (I := I) (c := a) hX]
  simp [Pi.smul_apply, map_smul]
  module

private theorem riemannCurvatureAux_tangentConst_add_second
    (cov : CovariantDerivative I E (TangentSpace I : M → Type _))
    (hcov : CovariantDerivative.ContMDiffCovariantDerivativeLocally cov ∞)
    (x : M) (X Y₁ Y₂ Z : TangentSpace I x) :
    riemannCurvatureAux cov
        (tangentConstAt (I := I) x X)
        (tangentConstAt (I := I) x (Y₁ + Y₂))
        (tangentConstAt (I := I) x Z) x =
      riemannCurvatureAux cov
          (tangentConstAt (I := I) x X)
          (tangentConstAt (I := I) x Y₁)
          (tangentConstAt (I := I) x Z) x +
        riemannCurvatureAux cov
          (tangentConstAt (I := I) x X)
          (tangentConstAt (I := I) x Y₂)
          (tangentConstAt (I := I) x Z) x := by
  let Xc : (p : M) → TangentSpace I p := tangentConstAt (I := I) x X
  let Y₁c : (p : M) → TangentSpace I p := tangentConstAt (I := I) x Y₁
  let Y₂c : (p : M) → TangentSpace I p := tangentConstAt (I := I) x Y₂
  let Zc : (p : M) → TangentSpace I p := tangentConstAt (I := I) x Z
  have hY₁ : MDiffAt (T% Y₁c) x := mdifferentiableAt_tangentConstAt_self (I := I) x Y₁
  have hY₂ : MDiffAt (T% Y₂c) x := mdifferentiableAt_tangentConstAt_self (I := I) x Y₂
  have hZY₁ : MDiffAt (T% (fun p : M => (cov Zc p) (Y₁c p))) x := by
    simpa [Y₁c, Zc] using cov_tangentConst_apply_mdiffAt_self (I := I) cov hcov x Z Y₁
  have hZY₂ : MDiffAt (T% (fun p : M => (cov Zc p) (Y₂c p))) x := by
    simpa [Y₂c, Zc] using cov_tangentConst_apply_mdiffAt_self (I := I) cov hcov x Z Y₂
  have hmid :
      (fun p : M => (cov Zc p) ((Y₁c + Y₂c) p)) =
        (fun p : M => (cov Zc p) (Y₁c p)) +
          (fun p : M => (cov Zc p) (Y₂c p)) := by
    funext p
    simp [Pi.add_apply, map_add]
  rw [tangentConstAt_add]
  change
    riemannCurvatureAux cov Xc (Y₁c + Y₂c) Zc x =
      riemannCurvatureAux cov Xc Y₁c Zc x +
        riemannCurvatureAux cov Xc Y₂c Zc x
  unfold riemannCurvatureAux
  rw [hmid]
  rw [cov.isCovariantDerivativeOnUniv.add hZY₁ hZY₂]
  rw [VectorField.mlieBracket_add_right (I := I) hY₁ hY₂]
  simp [Pi.add_apply, map_add]
  module

private theorem riemannCurvatureAux_tangentConst_smul_second
    (cov : CovariantDerivative I E (TangentSpace I : M → Type _))
    (hcov : CovariantDerivative.ContMDiffCovariantDerivativeLocally cov ∞)
    (x : M) (a : Real) (X Y Z : TangentSpace I x) :
    riemannCurvatureAux cov
        (tangentConstAt (I := I) x X)
        (tangentConstAt (I := I) x (a • Y))
        (tangentConstAt (I := I) x Z) x =
      a • riemannCurvatureAux cov
          (tangentConstAt (I := I) x X)
          (tangentConstAt (I := I) x Y)
          (tangentConstAt (I := I) x Z) x := by
  let Xc : (p : M) → TangentSpace I p := tangentConstAt (I := I) x X
  let Yc : (p : M) → TangentSpace I p := tangentConstAt (I := I) x Y
  let Zc : (p : M) → TangentSpace I p := tangentConstAt (I := I) x Z
  have hY : MDiffAt (T% Yc) x := mdifferentiableAt_tangentConstAt_self (I := I) x Y
  have hZY : MDiffAt (T% (fun p : M => (cov Zc p) (Yc p))) x := by
    simpa [Yc, Zc] using cov_tangentConst_apply_mdiffAt_self (I := I) cov hcov x Z Y
  have hmid :
      (fun p : M => (cov Zc p) ((a • Yc) p)) =
        a • (fun p : M => (cov Zc p) (Yc p)) := by
    funext p
    simp [Pi.smul_apply, map_smul]
  rw [tangentConstAt_smul]
  change
    riemannCurvatureAux cov Xc (a • Yc) Zc x =
      a • riemannCurvatureAux cov Xc Yc Zc x
  unfold riemannCurvatureAux
  rw [hmid]
  rw [cov.isCovariantDerivativeOnUniv.smul_const a hZY]
  rw [VectorField.mlieBracket_const_smul_right (I := I) (c := a) hY]
  simp [Pi.smul_apply, map_smul]
  module

private theorem riemannCurvatureAux_tangentConst_add_third
    (cov : CovariantDerivative I E (TangentSpace I : M → Type _))
    (hcov : CovariantDerivative.ContMDiffCovariantDerivativeLocally cov ∞)
    (x : M) (X Y Z₁ Z₂ : TangentSpace I x) :
    riemannCurvatureAux cov
        (tangentConstAt (I := I) x X)
        (tangentConstAt (I := I) x Y)
        (tangentConstAt (I := I) x (Z₁ + Z₂)) x =
      riemannCurvatureAux cov
          (tangentConstAt (I := I) x X)
          (tangentConstAt (I := I) x Y)
          (tangentConstAt (I := I) x Z₁) x +
        riemannCurvatureAux cov
          (tangentConstAt (I := I) x X)
          (tangentConstAt (I := I) x Y)
          (tangentConstAt (I := I) x Z₂) x := by
  let Xc : (p : M) → TangentSpace I p := tangentConstAt (I := I) x X
  let Yc : (p : M) → TangentSpace I p := tangentConstAt (I := I) x Y
  let Z₁c : (p : M) → TangentSpace I p := tangentConstAt (I := I) x Z₁
  let Z₂c : (p : M) → TangentSpace I p := tangentConstAt (I := I) x Z₂
  let Z₁₂c : (p : M) → TangentSpace I p := tangentConstAt (I := I) x (Z₁ + Z₂)
  have hZ₁ : MDiffAt (T% Z₁c) x := mdifferentiableAt_tangentConstAt_self (I := I) x Z₁
  have hZ₂ : MDiffAt (T% Z₂c) x := mdifferentiableAt_tangentConstAt_self (I := I) x Z₂
  have hZ₁₂Y : MDiffAt (T% (fun p : M => (cov Z₁₂c p) (Yc p))) x := by
    simpa [Z₁₂c, Yc] using
      cov_tangentConst_apply_mdiffAt_self (I := I) cov hcov x (Z₁ + Z₂) Y
  have hZ₁Y : MDiffAt (T% (fun p : M => (cov Z₁c p) (Yc p))) x := by
    simpa [Z₁c, Yc] using cov_tangentConst_apply_mdiffAt_self (I := I) cov hcov x Z₁ Y
  have hZ₂Y : MDiffAt (T% (fun p : M => (cov Z₂c p) (Yc p))) x := by
    simpa [Z₂c, Yc] using cov_tangentConst_apply_mdiffAt_self (I := I) cov hcov x Z₂ Y
  have hZ₁₂X : MDiffAt (T% (fun p : M => (cov Z₁₂c p) (Xc p))) x := by
    simpa [Z₁₂c, Xc] using
      cov_tangentConst_apply_mdiffAt_self (I := I) cov hcov x (Z₁ + Z₂) X
  have hZ₁X : MDiffAt (T% (fun p : M => (cov Z₁c p) (Xc p))) x := by
    simpa [Z₁c, Xc] using cov_tangentConst_apply_mdiffAt_self (I := I) cov hcov x Z₁ X
  have hZ₂X : MDiffAt (T% (fun p : M => (cov Z₂c p) (Xc p))) x := by
    simpa [Z₂c, Xc] using cov_tangentConst_apply_mdiffAt_self (I := I) cov hcov x Z₂ X
  have hsumY :
      MDiffAt
        (T% ((fun p : M => (cov Z₁c p) (Yc p)) +
          fun p : M => (cov Z₂c p) (Yc p))) x :=
    mdifferentiableAt_add_section hZ₁Y hZ₂Y
  have hsumX :
      MDiffAt
        (T% ((fun p : M => (cov Z₁c p) (Xc p)) +
          fun p : M => (cov Z₂c p) (Xc p))) x :=
    mdifferentiableAt_add_section hZ₁X hZ₂X
  have hcongrY :
      cov (fun p : M => (cov Z₁₂c p) (Yc p)) x =
        cov ((fun p : M => (cov Z₁c p) (Yc p)) +
          fun p : M => (cov Z₂c p) (Yc p)) x := by
    exact cov.isCovariantDerivativeOnUniv.congr_of_eventuallyEq hZ₁₂Y hsumY
      (by simp)
      (by simpa [Z₁₂c, Z₁c, Z₂c, Yc] using
        cov_tangentConst_add_apply_eventuallyEq (I := I) cov x Z₁ Z₂ Y)
  have hcongrX :
      cov (fun p : M => (cov Z₁₂c p) (Xc p)) x =
        cov ((fun p : M => (cov Z₁c p) (Xc p)) +
          fun p : M => (cov Z₂c p) (Xc p)) x := by
    exact cov.isCovariantDerivativeOnUniv.congr_of_eventuallyEq hZ₁₂X hsumX
      (by simp)
      (by simpa [Z₁₂c, Z₁c, Z₂c, Xc] using
        cov_tangentConst_add_apply_eventuallyEq (I := I) cov x Z₁ Z₂ X)
  change
    riemannCurvatureAux cov Xc Yc Z₁₂c x =
      riemannCurvatureAux cov Xc Yc Z₁c x +
        riemannCurvatureAux cov Xc Yc Z₂c x
  unfold riemannCurvatureAux
  rw [hcongrY, hcongrX]
  rw [show Z₁₂c = Z₁c + Z₂c by
    simp [Z₁₂c, Z₁c, Z₂c]]
  rw [cov.isCovariantDerivativeOnUniv.add hZ₁Y hZ₂Y]
  rw [cov.isCovariantDerivativeOnUniv.add hZ₁X hZ₂X]
  rw [cov.isCovariantDerivativeOnUniv.add hZ₁ hZ₂]
  simp
  module

private theorem riemannCurvatureAux_tangentConst_smul_third
    (cov : CovariantDerivative I E (TangentSpace I : M → Type _))
    (hcov : CovariantDerivative.ContMDiffCovariantDerivativeLocally cov ∞)
    (x : M) (a : Real) (X Y Z : TangentSpace I x) :
    riemannCurvatureAux cov
        (tangentConstAt (I := I) x X)
        (tangentConstAt (I := I) x Y)
        (tangentConstAt (I := I) x (a • Z)) x =
      a • riemannCurvatureAux cov
          (tangentConstAt (I := I) x X)
          (tangentConstAt (I := I) x Y)
          (tangentConstAt (I := I) x Z) x := by
  let Xc : (p : M) → TangentSpace I p := tangentConstAt (I := I) x X
  let Yc : (p : M) → TangentSpace I p := tangentConstAt (I := I) x Y
  let Zc : (p : M) → TangentSpace I p := tangentConstAt (I := I) x Z
  let Za : (p : M) → TangentSpace I p := tangentConstAt (I := I) x (a • Z)
  have hZ : MDiffAt (T% Zc) x := mdifferentiableAt_tangentConstAt_self (I := I) x Z
  have hZaY : MDiffAt (T% (fun p : M => (cov Za p) (Yc p))) x := by
    simpa [Za, Yc] using
      cov_tangentConst_apply_mdiffAt_self (I := I) cov hcov x (a • Z) Y
  have hZY : MDiffAt (T% (fun p : M => (cov Zc p) (Yc p))) x := by
    simpa [Zc, Yc] using cov_tangentConst_apply_mdiffAt_self (I := I) cov hcov x Z Y
  have hZaX : MDiffAt (T% (fun p : M => (cov Za p) (Xc p))) x := by
    simpa [Za, Xc] using
      cov_tangentConst_apply_mdiffAt_self (I := I) cov hcov x (a • Z) X
  have hZX : MDiffAt (T% (fun p : M => (cov Zc p) (Xc p))) x := by
    simpa [Zc, Xc] using cov_tangentConst_apply_mdiffAt_self (I := I) cov hcov x Z X
  have hsmulY :
      MDiffAt (T% (a • fun p : M => (cov Zc p) (Yc p))) x :=
    mdifferentiableAt_const.smul_section hZY
  have hsmulX :
      MDiffAt (T% (a • fun p : M => (cov Zc p) (Xc p))) x :=
    mdifferentiableAt_const.smul_section hZX
  have hcongrY :
      cov (fun p : M => (cov Za p) (Yc p)) x =
        cov (a • fun p : M => (cov Zc p) (Yc p)) x := by
    exact cov.isCovariantDerivativeOnUniv.congr_of_eventuallyEq hZaY hsmulY
      (by simp)
      (by simpa [Za, Zc, Yc] using
        cov_tangentConst_smul_apply_eventuallyEq (I := I) cov x a Z Y)
  have hcongrX :
      cov (fun p : M => (cov Za p) (Xc p)) x =
        cov (a • fun p : M => (cov Zc p) (Xc p)) x := by
    exact cov.isCovariantDerivativeOnUniv.congr_of_eventuallyEq hZaX hsmulX
      (by simp)
      (by simpa [Za, Zc, Xc] using
        cov_tangentConst_smul_apply_eventuallyEq (I := I) cov x a Z X)
  change
    riemannCurvatureAux cov Xc Yc Za x =
      a • riemannCurvatureAux cov Xc Yc Zc x
  unfold riemannCurvatureAux
  rw [hcongrY, hcongrX]
  rw [show Za = a • Zc by
    simp [Za, Zc]]
  rw [cov.isCovariantDerivativeOnUniv.smul_const a hZY]
  rw [cov.isCovariantDerivativeOnUniv.smul_const a hZX]
  rw [cov.isCovariantDerivativeOnUniv.smul_const a hZ]
  simp [Pi.smul_apply]
  module

private noncomputable def riemannCurvatureZCLM
    (cov : CovariantDerivative I E (TangentSpace I : M → Type _))
    (hcov : CovariantDerivative.ContMDiffCovariantDerivativeLocally cov ∞) (x : M)
    (α : Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) 1 x)
    (X Y : TangentSpace I x) :
    TangentSpace I x →L[Real] Real :=
  LinearMap.toContinuousLinearMap
    { toFun := fun Z =>
        cotangentToDual α
          (riemannCurvatureAux cov
            (tangentConstAt (I := I) x X) (tangentConstAt (I := I) x Y)
            (tangentConstAt (I := I) x Z) x)
      map_add' := by
        intro Z₁ Z₂
        change
          cotangentToDual α
              (riemannCurvatureAux cov
                (tangentConstAt (I := I) x X) (tangentConstAt (I := I) x Y)
                (tangentConstAt (I := I) x (Z₁ + Z₂)) x) =
            cotangentToDual α
                (riemannCurvatureAux cov
                  (tangentConstAt (I := I) x X) (tangentConstAt (I := I) x Y)
                  (tangentConstAt (I := I) x Z₁) x) +
              cotangentToDual α
                (riemannCurvatureAux cov
                  (tangentConstAt (I := I) x X) (tangentConstAt (I := I) x Y)
                  (tangentConstAt (I := I) x Z₂) x)
        rw [riemannCurvatureAux_tangentConst_add_third cov hcov x X Y Z₁ Z₂]
        exact map_add (cotangentToDual α) _ _
      map_smul' := by
        intro a Z
        change
          cotangentToDual α
              (riemannCurvatureAux cov
                (tangentConstAt (I := I) x X) (tangentConstAt (I := I) x Y)
                (tangentConstAt (I := I) x (a • Z)) x) =
            a • cotangentToDual α
              (riemannCurvatureAux cov
                (tangentConstAt (I := I) x X) (tangentConstAt (I := I) x Y)
                (tangentConstAt (I := I) x Z) x)
        rw [riemannCurvatureAux_tangentConst_smul_third cov hcov x a X Y Z]
        exact map_smul (cotangentToDual α) a _ }

@[simp] private theorem riemannCurvatureZCLM_apply
    (cov : CovariantDerivative I E (TangentSpace I : M → Type _))
    (hcov : CovariantDerivative.ContMDiffCovariantDerivativeLocally cov ∞) (x : M)
    (α : Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) 1 x)
    (X Y Z : TangentSpace I x) :
    riemannCurvatureZCLM cov hcov x α X Y Z =
      cotangentToDual α
        (riemannCurvatureAux cov
          (tangentConstAt (I := I) x X) (tangentConstAt (I := I) x Y)
          (tangentConstAt (I := I) x Z) x) := rfl

private noncomputable def riemannCurvatureYZModel
    (cov : CovariantDerivative I E (TangentSpace I : M → Type _))
    (hcov : CovariantDerivative.ContMDiffCovariantDerivativeLocally cov ∞) (x : M)
    (α : Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) 1 x)
    (X : TangentSpace I x) :
    ContinuousMultilinearMap ℝ (fun _ : Fin 2 => TangentSpace I x) ℝ :=
  ContinuousLinearMap.uncurryLeft
    (𝕜 := Real) (n := 1) (Ei := fun _ : Fin 2 => TangentSpace I x) (G := Real)
    (LinearMap.toContinuousLinearMap
      { toFun := fun Y =>
          (continuousMultilinearCurryFin1 Real (TangentSpace I x) Real).symm
            (riemannCurvatureZCLM cov hcov x α X Y)
        map_add' := by
          intro Y₁ Y₂
          apply (continuousMultilinearCurryFin1 Real (TangentSpace I x) Real).injective
          ext Z
          change
            cotangentToDual α
                (riemannCurvatureAux cov
                  (tangentConstAt (I := I) x X) (tangentConstAt (I := I) x (Y₁ + Y₂))
                  (tangentConstAt (I := I) x Z) x) =
              cotangentToDual α
                  (riemannCurvatureAux cov
                    (tangentConstAt (I := I) x X) (tangentConstAt (I := I) x Y₁)
                    (tangentConstAt (I := I) x Z) x) +
                cotangentToDual α
                  (riemannCurvatureAux cov
                    (tangentConstAt (I := I) x X) (tangentConstAt (I := I) x Y₂)
                    (tangentConstAt (I := I) x Z) x)
          rw [riemannCurvatureAux_tangentConst_add_second cov hcov x X Y₁ Y₂ Z]
          exact map_add (cotangentToDual α) _ _
        map_smul' := by
          intro a Y
          apply (continuousMultilinearCurryFin1 Real (TangentSpace I x) Real).injective
          ext Z
          change
            cotangentToDual α
                (riemannCurvatureAux cov
                  (tangentConstAt (I := I) x X) (tangentConstAt (I := I) x (a • Y))
                  (tangentConstAt (I := I) x Z) x) =
              a • cotangentToDual α
                (riemannCurvatureAux cov
                  (tangentConstAt (I := I) x X) (tangentConstAt (I := I) x Y)
                  (tangentConstAt (I := I) x Z) x)
          rw [riemannCurvatureAux_tangentConst_smul_second cov hcov x a X Y Z]
          exact map_smul (cotangentToDual α) a _ })

@[simp] private theorem riemannCurvatureYZModel_apply_vec2
    (cov : CovariantDerivative I E (TangentSpace I : M → Type _))
    (hcov : CovariantDerivative.ContMDiffCovariantDerivativeLocally cov ∞) (x : M)
    (α : Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) 1 x)
    (X Y Z : TangentSpace I x) :
  riemannCurvatureYZModel cov hcov x α X (vec2 Y Z) =
      cotangentToDual α
        (riemannCurvatureAux cov
          (tangentConstAt (I := I) x X) (tangentConstAt (I := I) x Y)
          (tangentConstAt (I := I) x Z) x) := by
  unfold riemannCurvatureYZModel
  rw [ContinuousLinearMap.uncurryLeft_apply]
  change
    ((continuousMultilinearCurryFin1 Real (TangentSpace I x) Real).symm
      (riemannCurvatureZCLM cov hcov x α X Y))
      (fun i : Fin 1 => vec2 Y Z i.succ) =
    cotangentToDual α
      (riemannCurvatureAux cov
        (tangentConstAt (I := I) x X) (tangentConstAt (I := I) x Y)
        (tangentConstAt (I := I) x Z) x)
  rw [show (fun i : Fin 1 => vec2 Y Z i.succ) = fun _ : Fin 1 => Z by
    funext i
    fin_cases i
    simp [vec2]]
  rfl

private noncomputable def riemannCurvatureModel
    (cov : CovariantDerivative I E (TangentSpace I : M → Type _))
    (hcov : CovariantDerivative.ContMDiffCovariantDerivativeLocally cov ∞) (x : M)
    (α : Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) 1 x) :
    ContinuousMultilinearMap ℝ (fun _ : Fin 3 => TangentSpace I x) ℝ :=
  ContinuousLinearMap.uncurryLeft
    (𝕜 := Real) (n := 2) (Ei := fun _ : Fin 3 => TangentSpace I x) (G := Real)
    (LinearMap.toContinuousLinearMap
      { toFun := fun X => riemannCurvatureYZModel cov hcov x α X
        map_add' := by
          intro X₁ X₂
          apply ContinuousMultilinearMap.ext
          intro v
          have hv : v = vec2 (v 0) (v 1) := by
            funext i
            fin_cases i <;> simp [vec2]
          rw [hv]
          simp only [riemannCurvatureYZModel_apply_vec2]
          rw [riemannCurvatureAux_tangentConst_add_first cov hcov x X₁ X₂ (v 0) (v 1)]
          exact map_add (cotangentToDual α) _ _
        map_smul' := by
          intro a X
          apply ContinuousMultilinearMap.ext
          intro v
          have hv : v = vec2 (v 0) (v 1) := by
            funext i
            fin_cases i <;> simp [vec2]
          rw [hv]
          simp only [riemannCurvatureYZModel_apply_vec2]
          rw [riemannCurvatureAux_tangentConst_smul_first cov hcov x a X (v 0) (v 1)]
          exact map_smul (cotangentToDual α) a _ })

/-- The pointwise `(1,3)` Riemann curvature tensor of a covariant derivative. -/
noncomputable def riemannCurvatureAt
    (cov : CovariantDerivative I E (TangentSpace I : M → Type _))
    (hcov : CovariantDerivative.ContMDiffCovariantDerivativeLocally cov ∞) (x : M) :
    Tensor13At (I := I) (M := M) x :=
  TensorRSSpace.ofModel (I := I) (x := x)
    (LinearMap.toContinuousLinearMap
    { toFun := fun α =>
        riemannCurvatureModel cov hcov x
          (Tensor0SSpace.ofModel (𝕜 := Real) (I := I) (x := x) α)
      map_add' := by
        intro α β
        apply ContinuousMultilinearMap.ext
        intro v
        let R := riemannCurvatureAux cov
          (tangentConstAt (I := I) x (v 0)) (tangentConstAt (I := I) x (v 1))
          (tangentConstAt (I := I) x (v 2)) x
        change cotangentToDual (I := I)
            (Tensor0SSpace.ofModel (𝕜 := Real) (I := I) (x := x) (α + β)) R =
          cotangentToDual (I := I)
              (Tensor0SSpace.ofModel (𝕜 := Real) (I := I) (x := x) α) R +
            cotangentToDual (I := I)
              (Tensor0SSpace.ofModel (𝕜 := Real) (I := I) (x := x) β) R
        have hαβ :
            Tensor0SSpace.ofModel (𝕜 := Real) (I := I) (x := x) (α + β) =
              Tensor0SSpace.ofModel (𝕜 := Real) (I := I) (x := x) α +
                Tensor0SSpace.ofModel (𝕜 := Real) (I := I) (x := x) β := by
          exact map_add
            (tensor0SSpace_continuousLinearEquiv (𝕜 := Real) (E := E) (H := H)
              (I := I) (M := M) 1 x).symm α β
        rw [hαβ]
        rfl
      map_smul' := by
        intro c α
        apply ContinuousMultilinearMap.ext
        intro v
        let R := riemannCurvatureAux cov
          (tangentConstAt (I := I) x (v 0)) (tangentConstAt (I := I) x (v 1))
          (tangentConstAt (I := I) x (v 2)) x
        change cotangentToDual (I := I)
            (Tensor0SSpace.ofModel (𝕜 := Real) (I := I) (x := x) (c • α)) R =
          c • cotangentToDual (I := I)
            (Tensor0SSpace.ofModel (𝕜 := Real) (I := I) (x := x) α) R
        have hα :
            Tensor0SSpace.ofModel (𝕜 := Real) (I := I) (x := x) (c • α) =
              c • Tensor0SSpace.ofModel (𝕜 := Real) (I := I) (x := x) α := by
          exact map_smul
            (tensor0SSpace_continuousLinearEquiv (𝕜 := Real) (E := E) (H := H)
              (I := I) (M := M) 1 x).symm c α
        rw [hα]
        rfl })

@[simp]
theorem riemannCurvatureAt_apply_const
    (cov : CovariantDerivative I E (TangentSpace I : M → Type _))
    (hcov : CovariantDerivative.ContMDiffCovariantDerivativeLocally cov ∞) {x : M}
    (α : Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) 1 x)
    (X Y Z : TangentSpace I x) :
    riemannCurvatureAt cov hcov x α (vec3 X Y Z) =
      cotangentToDual α
        (riemannCurvatureAux cov
          (tangentConstAt (I := I) x X) (tangentConstAt (I := I) x Y)
          (tangentConstAt (I := I) x Z) x) := by
  change (riemannCurvatureModel cov hcov x α) (vec3 X Y Z) =
    cotangentToDual α
      (riemannCurvatureAux cov
        (tangentConstAt (I := I) x X) (tangentConstAt (I := I) x Y)
        (tangentConstAt (I := I) x Z) x)
  rfl

private noncomputable def tangentFlatCotangentModelCLM
    (g : SmoothRiemannianMetric I M) (x : M) :
    E →L[Real] ContinuousMultilinearMap Real (fun _ : Fin 1 => E) Real :=
  LinearMap.toContinuousLinearMap
    { toFun := fun W =>
        (continuousMultilinearCurryFin1 Real E Real).symm
          (LinearMap.toContinuousLinearMap ((tangentFlatLinear (I := I) g x) W))
      map_add' := by
        intro W W'
        apply (continuousMultilinearCurryFin1 Real E Real).injective
        ext V
        change
          ((tangentFlatLinear (I := I) g x) (W + W')) V =
            (((tangentFlatLinear (I := I) g x) W) +
              ((tangentFlatLinear (I := I) g x) W')) V
        exact congrArg (fun L : Module.Dual Real (TangentSpace I x) => L V)
          ((tangentFlatLinear (I := I) g x).map_add W W')
      map_smul' := by
        intro c W
        apply (continuousMultilinearCurryFin1 Real E Real).injective
        ext V
        change
          ((tangentFlatLinear (I := I) g x) (c • W)) V =
            (c • ((tangentFlatLinear (I := I) g x) W)) V
        exact congrArg (fun L : Module.Dual Real (TangentSpace I x) => L V)
          ((tangentFlatLinear (I := I) g x).map_smul c W) }

@[simp] private theorem tangentFlatCotangentModelCLM_apply
    (g : SmoothRiemannianMetric I M) (x : M) (W : TangentSpace I x) :
    tangentFlatCotangentModelCLM (I := I) g x W =
      (continuousMultilinearCurryFin1 Real E Real).symm
        (LinearMap.toContinuousLinearMap ((tangentFlatLinear (I := I) g x) W)) := by
  simp [tangentFlatCotangentModelCLM]

/-- The lowered pointwise `(0,4)` Riemann curvature tensor. -/
noncomputable def riemannCurvature04At
    (g : SmoothRiemannianMetric I M)
    (cov : CovariantDerivative I E (TangentSpace I : M → Type _))
    (hcov : CovariantDerivative.ContMDiffCovariantDerivativeLocally cov ∞) (x : M) :
    Tensor04At (I := I) (M := M) x :=
  Tensor0SSpace.ofModel (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
    (ContinuousLinearMap.uncurryLeft
      (𝕜 := Real) (n := 3) (Ei := fun _ : Fin 4 => E) (G := Real)
      (((TensorRSSpace.toModel (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
          (riemannCurvatureAt cov hcov x)).comp
        (tangentFlatCotangentModelCLM (I := I) g x)) :
        E →L[Real] ContinuousMultilinearMap Real (fun _ : Fin 3 => E) Real))

@[simp]
theorem riemannCurvature04At_apply_const
    (g : SmoothRiemannianMetric I M)
    (cov : CovariantDerivative I E (TangentSpace I : M → Type _))
    (hcov : CovariantDerivative.ContMDiffCovariantDerivativeLocally cov ∞) {x : M}
    (W X Y Z : TangentSpace I x) :
    riemannCurvature04At g cov hcov x (vec4 W X Y Z) =
      g.inner x W
        (riemannCurvatureAux cov
          (tangentConstAt (I := I) x X) (tangentConstAt (I := I) x Y)
          (tangentConstAt (I := I) x Z) x) := by
  change
    (ContinuousLinearMap.uncurryLeft
        (𝕜 := Real) (n := 3) (Ei := fun _ : Fin 4 => E) (G := Real)
        (((TensorRSSpace.toModel (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
            (riemannCurvatureAt cov hcov x)).comp
          (tangentFlatCotangentModelCLM (I := I) g x)) :
          E →L[Real] ContinuousMultilinearMap Real (fun _ : Fin 3 => E) Real))
        (vec4 W X Y Z) =
      g.inner x W
        (riemannCurvatureAux cov
          (tangentConstAt (I := I) x X) (tangentConstAt (I := I) x Y)
          (tangentConstAt (I := I) x Z) x)
  rw [ContinuousLinearMap.uncurryLeft_apply]
  change
    riemannCurvatureAt cov hcov x
        (Tensor0SSpace.ofModel (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
          (tangentFlatCotangentModelCLM (I := I) g x W))
        (fun i : Fin 3 => vec4 W X Y Z i.succ) =
      g.inner x W
        (riemannCurvatureAux cov
          (tangentConstAt (I := I) x X) (tangentConstAt (I := I) x Y)
          (tangentConstAt (I := I) x Z) x)
  rw [show (fun i : Fin 3 => vec4 W X Y Z i.succ) = vec3 X Y Z by
    funext i
    fin_cases i <;> simp [vec3, vec4]]
  rw [riemannCurvatureAt_apply_const]
  rw [cotangentToDual_apply]
  change
    (tangentFlatCotangentModelCLM (I := I) g x W)
        (fun _ : Fin 1 =>
          riemannCurvatureAux cov
            (tangentConstAt (I := I) x X) (tangentConstAt (I := I) x Y)
            (tangentConstAt (I := I) x Z) x) =
      g.inner x W
        (riemannCurvatureAux cov
          (tangentConstAt (I := I) x X) (tangentConstAt (I := I) x Y)
          (tangentConstAt (I := I) x Z) x)
  rw [tangentFlatCotangentModelCLM_apply]
  rfl

/-- The pointwise Ricci tensor, obtained by tracing the `(1,3)` tensor. -/
noncomputable def ricciCurvatureAt
    (cov : CovariantDerivative I E (TangentSpace I : M → Type _))
    (hcov : CovariantDerivative.ContMDiffCovariantDerivativeLocally cov ∞) (x : M) :
    Tensor02At (I := I) (M := M) x :=
  ricciFromRm13At (riemannCurvatureAt cov hcov x)

@[simp]
theorem ricciCurvatureAt_eq_trace
    (cov : CovariantDerivative I E (TangentSpace I : M → Type _))
    (hcov : CovariantDerivative.ContMDiffCovariantDerivativeLocally cov ∞) (x : M) :
    ricciCurvatureAt cov hcov x = ricciFromRm13At (riemannCurvatureAt cov hcov x) := rfl

/-- The lowered `(0,4)` tensor is evaluation of the metric on the `(1,3)` tensor. -/
theorem riemannCurvature04At_eq_lower_riemannCurvatureAt
    (g : SmoothRiemannianMetric I M)
    (cov : CovariantDerivative I E (TangentSpace I : M → Type _))
    (hcov : CovariantDerivative.ContMDiffCovariantDerivativeLocally cov ∞) {x : M}
    (W X Y Z : TangentSpace I x) :
    riemannCurvature04At g cov hcov x (vec4 W X Y Z) =
      riemannCurvatureAt cov hcov x (dualToCotangent ((tangentFlatLinear g x) W))
        (vec3 X Y Z) := by
  rw [riemannCurvature04At_apply_const, riemannCurvatureAt_apply_const]
  simp [tangentFlatLinear_apply]

private theorem exists_contMDiffSection_eventuallyEq_tangentConstAt
    [T2Space M] (x : M) (v : TangentSpace I x) :
    ∃ V : ContMDiffSection I E (∞ : WithTop ℕ∞) (TangentSpace I : M → Type _),
      (fun p : M => V p) =ᶠ[𝓝 x] tangentConstAt (I := I) x v ∧ V x = v := by
  classical
  let e := trivializationAt E (TangentSpace I) x
  let b := Module.finBasis Real E
  have he : x ∈ e.baseSet := by
    simp [e]
  have hframe := e.isLocalFrameOn_localFrame_baseSet I (∞ : WithTop ℕ∞) b
  obtain ⟨s', hs'⟩ := hframe.exists_contMDiffSection_eqOn_nhd e.open_baseSet he
  let V : ContMDiffSection I E (∞ : WithTop ℕ∞) (TangentSpace I : M → Type _) :=
    ∑ i, (b.repr v i) • s' i
  have hV : (fun p : M => V p) =ᶠ[𝓝 x] tangentConstAt (I := I) x v := by
    filter_upwards [hs', e.open_baseSet.mem_nhds he] with p hs'p hp
    have hbasis :
        (∑ i, (b.repr v i) • e.localFrame b i p) =
          tangentConstAt (I := I) x v p := by
      have hx_src : p ∈ (chartAt H x).source := by
        simpa [e, TangentBundle.trivializationAt_baseSet] using hp
      have hframe_apply (i) :
          e.localFrame b i p = e.symmL Real p (b i) := by
        rw [Bundle.Trivialization.localFrame_apply_of_mem_baseSet (e := e) (b := b) (i := i) hp]
        simp [e, Bundle.Trivialization.basisAt, Trivialization.symmL_apply]
      calc
        (∑ i, (b.repr v i) • e.localFrame b i p)
            = ∑ i, (b.repr v i) • e.symmL Real p (b i) := by
              exact Finset.sum_congr rfl (fun i _ => by rw [hframe_apply i])
        _ = e.symmL Real p (∑ i, (b.repr v i) • b i) := by
              rw [map_sum]
              simp
        _ = tangentConstAt (I := I) x v p := by
              rw [b.sum_repr]
              rfl
    calc
      V p = ∑ i, (b.repr v i) • s' i p := by
        simp [V, ContMDiffSection.finset_sum_apply]
      _ = ∑ i, (b.repr v i) • e.localFrame b i p := by
        apply Finset.sum_congr rfl
        intro i hi
        rw [hs'p i]
      _ = tangentConstAt (I := I) x v p := hbasis
  refine ⟨V, hV, ?_⟩
  exact hV.self_of_nhds.trans (tangentConstAt_self (I := I) x v)

private theorem connectionRiemannCurvatureField_eq_smooth_of_eventuallyEq_tangentConst
    (cov : CovariantDerivative I E (TangentSpace I : M → Type _))
    (hcov : CovariantDerivative.ContMDiffCovariantDerivativeLocally cov ∞)
    {x : M} (X Y Z : TangentSpace I x)
    (Xs Ys Zs :
      ContMDiffSection I E (∞ : WithTop ℕ∞) (TangentSpace I : M → Type _))
    (hX : (fun p : M => Xs p) =ᶠ[𝓝 x] tangentConstAt (I := I) x X)
    (hY : (fun p : M => Ys p) =ᶠ[𝓝 x] tangentConstAt (I := I) x Y)
    (hZ : (fun p : M => Zs p) =ᶠ[𝓝 x] tangentConstAt (I := I) x Z) :
    connectionRiemannCurvatureField cov
        (tangentConstAt (I := I) x X) (tangentConstAt (I := I) x Y)
        (tangentConstAt (I := I) x Z) x =
      connectionRiemannCurvatureField cov
        (fun p : M => Xs p) (fun p : M => Ys p) (fun p : M => Zs p) x := by
  classical
  let Xc : (p : M) → TangentSpace I p := tangentConstAt (I := I) x X
  let Yc : (p : M) → TangentSpace I p := tangentConstAt (I := I) x Y
  let Zc : (p : M) → TangentSpace I p := tangentConstAt (I := I) x Z
  have hX' : Xc =ᶠ[𝓝 x] fun p : M => Xs p := by
    simpa [Xc] using hX.symm
  have hY' : Yc =ᶠ[𝓝 x] fun p : M => Ys p := by
    simpa [Yc] using hY.symm
  have hZ' : Zc =ᶠ[𝓝 x] fun p : M => Zs p := by
    simpa [Zc] using hZ.symm
  have hXx : Xc x = Xs x := hX'.self_of_nhds
  have hYx : Yc x = Ys x := hY'.self_of_nhds
  have hbr :
      VectorField.mlieBracket I Xc Yc x =
        VectorField.mlieBracket I (fun p : M => Xs p) (fun p : M => Ys p) x := by
    exact hX'.mlieBracket_vectorField_eq (I := I) hY'
  have hZ_at :
      cov Zc x = cov (fun p : M => Zs p) x := by
    exact cov.isCovariantDerivativeOnUniv.congr_of_eventuallyEq
      (by simpa [Zc] using mdifferentiableAt_tangentConstAt_self (I := I) x Z)
      (Zs.contMDiff.contMDiffAt.mdifferentiableAt (by simp))
      (by simp) hZ'
  let e := trivializationAt E (TangentSpace I) x
  have he : x ∈ e.baseSet := by
    simp [e]
  have hinnerY :
      (fun p : M => (cov Zc p) (Yc p)) =ᶠ[𝓝 x]
        (fun p : M => (cov (fun q : M => Zs q) p) (Ys p)) := by
    rcases mem_nhds_iff.mp (hZ' : {p : M | Zc p = Zs p} ∈ 𝓝 x) with
      ⟨U, hUsub, hUopen, hxU⟩
    filter_upwards [hUopen.mem_nhds hxU, hY', e.open_baseSet.mem_nhds he] with
      p hpU hYp hpE
    have hZp : Zc =ᶠ[𝓝 p] fun q : M => Zs q :=
      Filter.eventuallyEq_of_mem (hUopen.mem_nhds hpU) fun q hq => hUsub hq
    have hZc_md : MDiffAt (T% Zc) p := by
      unfold Zc tangentConstAt
      exact TensorLieDeriv.mdifferentiableAt_tangentConstInChart_of_mem
        (𝕜 := Real) (I := I) (x₀ := x) (p := p) Z (by simpa [e] using hpE)
    have hcovp :
        cov Zc p = cov (fun q : M => Zs q) p := by
      exact cov.isCovariantDerivativeOnUniv.congr_of_eventuallyEq
        hZc_md (Zs.contMDiff.contMDiffAt.mdifferentiableAt (by simp))
        (by simp) hZp
    rw [hcovp, hYp]
  have hinnerX :
      (fun p : M => (cov Zc p) (Xc p)) =ᶠ[𝓝 x]
        (fun p : M => (cov (fun q : M => Zs q) p) (Xs p)) := by
    rcases mem_nhds_iff.mp (hZ' : {p : M | Zc p = Zs p} ∈ 𝓝 x) with
      ⟨U, hUsub, hUopen, hxU⟩
    filter_upwards [hUopen.mem_nhds hxU, hX', e.open_baseSet.mem_nhds he] with
      p hpU hXp hpE
    have hZp : Zc =ᶠ[𝓝 p] fun q : M => Zs q :=
      Filter.eventuallyEq_of_mem (hUopen.mem_nhds hpU) fun q hq => hUsub hq
    have hZc_md : MDiffAt (T% Zc) p := by
      unfold Zc tangentConstAt
      exact TensorLieDeriv.mdifferentiableAt_tangentConstInChart_of_mem
        (𝕜 := Real) (I := I) (x₀ := x) (p := p) Z (by simpa [e] using hpE)
    have hcovp :
        cov Zc p = cov (fun q : M => Zs q) p := by
      exact cov.isCovariantDerivativeOnUniv.congr_of_eventuallyEq
        hZc_md (Zs.contMDiff.contMDiffAt.mdifferentiableAt (by simp))
        (by simp) hZp
    rw [hcovp, hXp]
  have hcovZY :
      cov (fun p : M => (cov Zc p) (Yc p)) x =
        cov (fun p : M => (cov (fun q : M => Zs q) p) (Ys p)) x := by
    exact cov.isCovariantDerivativeOnUniv.congr_of_eventuallyEq
      (by
        simpa [Zc, Yc] using
          cov_tangentConst_apply_mdiffAt_self (I := I) cov hcov x Z Y)
      (cov_smooth_apply_mdiffAt (I := I) cov hcov Ys Zs x)
      (by simp) hinnerY
  have hcovZX :
      cov (fun p : M => (cov Zc p) (Xc p)) x =
        cov (fun p : M => (cov (fun q : M => Zs q) p) (Xs p)) x := by
    exact cov.isCovariantDerivativeOnUniv.congr_of_eventuallyEq
      (by
        simpa [Zc, Xc] using
          cov_tangentConst_apply_mdiffAt_self (I := I) cov hcov x Z X)
      (cov_smooth_apply_mdiffAt (I := I) cov hcov Xs Zs x)
      (by simp) hinnerX
  have hXval : tangentConstAt (I := I) x X x = Xs x := by
    simpa [Xc] using hXx
  have hYval : tangentConstAt (I := I) x Y x = Ys x := by
    simpa [Yc] using hYx
  simp only [RicciFlower.Curvature.connectionRiemannCurvatureField]
  rw [hcovZY, hcovZX, hZ_at, hbr]
  rw [hXval, hYval]

/-- The pointwise `(1,3)` Riemann tensor evaluates on smooth tangent sections
as the connection curvature operator.

The pointwise constructor `riemannCurvatureAt` is defined using chart-constant
representatives.  This theorem is the raw tensoriality bridge needed before
bundling the tensor as a smooth section. -/
theorem riemannCurvatureAt_apply_smooth
    (cov : CovariantDerivative I E (TangentSpace I : M → Type _))
    (hcov : CovariantDerivative.ContMDiffCovariantDerivativeLocally cov ∞)
    [T2Space M]
    (X Y Z : ContMDiffSection I E (∞ : WithTop ℕ∞)
      (TangentSpace I : M → Type _))
    {x : M}
    (α : Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) 1 x) :
    riemannCurvatureAt cov hcov x α (vec3 (X x) (Y x) (Z x)) =
      cotangentToDual α
        (connectionRiemannCurvatureField cov
          (fun p : M => X p) (fun p : M => Y p) (fun p : M => Z p) x) := by
  obtain ⟨Xc, hXc, hXcx⟩ :=
    exists_contMDiffSection_eventuallyEq_tangentConstAt (I := I) x (X x)
  obtain ⟨Yc, hYc, hYcx⟩ :=
    exists_contMDiffSection_eventuallyEq_tangentConstAt (I := I) x (Y x)
  obtain ⟨Zc, hZc, hZcx⟩ :=
    exists_contMDiffSection_eventuallyEq_tangentConstAt (I := I) x (Z x)
  have hraw :
      connectionRiemannCurvatureField cov
          (tangentConstAt (I := I) x (X x)) (tangentConstAt (I := I) x (Y x))
          (tangentConstAt (I := I) x (Z x)) x =
        connectionRiemannCurvatureField cov
          (fun p : M => Xc p) (fun p : M => Yc p) (fun p : M => Zc p) x :=
    connectionRiemannCurvatureField_eq_smooth_of_eventuallyEq_tangentConst
      (I := I) cov hcov (X x) (Y x) (Z x) Xc Yc Zc hXc hYc hZc
  have hsmooth :
      connectionRiemannCurvatureField cov
          (fun p : M => Xc p) (fun p : M => Yc p) (fun p : M => Zc p) x =
        connectionRiemannCurvatureField cov
          (fun p : M => X p) (fun p : M => Y p) (fun p : M => Z p) x :=
    connectionRiemannCurvatureField_congr_point
      (I := I) cov hcov Xc X Yc Y Zc Z hXcx hYcx hZcx
  rw [riemannCurvatureAt_apply_const]
  simpa [riemannCurvatureAux_eq_connectionRiemannCurvatureField] using
    congrArg (cotangentToDual α) (hraw.trans hsmooth)

/-- The lowered pointwise `(0,4)` Riemann tensor evaluates on smooth tangent
sections as the metric pairing with the connection curvature operator. -/
theorem riemannCurvature04At_apply_smooth
    (g : SmoothRiemannianMetric I M)
    (cov : CovariantDerivative I E (TangentSpace I : M → Type _))
    (hcov : CovariantDerivative.ContMDiffCovariantDerivativeLocally cov ∞)
    [T2Space M]
    (W X Y Z : ContMDiffSection I E (∞ : WithTop ℕ∞)
      (TangentSpace I : M → Type _))
    (x : M) :
    riemannCurvature04At g cov hcov x (vec4 (W x) (X x) (Y x) (Z x)) =
      g.inner x (W x)
        (connectionRiemannCurvatureField cov
          (fun p : M => X p) (fun p : M => Y p) (fun p : M => Z p) x) := by
  have h13 :=
    riemannCurvatureAt_apply_smooth (I := I) cov hcov X Y Z
      (dualToCotangent (I := I) ((tangentFlatLinear (I := I) g x) (W x)))
  rw [riemannCurvature04At_eq_lower_riemannCurvatureAt]
  simpa [tangentFlatLinear_apply] using h13

set_option backward.isDefEq.respectTransparency false in
private theorem riemannCurvatureAt_contMDiff
    (cov : CovariantDerivative I E (TangentSpace I : M → Type _))
    (hcov : CovariantDerivative.ContMDiffCovariantDerivativeLocally cov ∞)
    [T2Space M] [IsManifold I ((∞ : WithTop ℕ∞) + 1) M] :
    letI := tensorRSBundle_topology (𝕜 := Real) (E := E) (H := H) (I := I)
      (M := M) 1 3
    letI := tensorRSBundle_fiber (𝕜 := Real) (E := E) (H := H) (I := I)
      (M := M) 1 3
    letI := tensorRSBundle_vector (𝕜 := Real) (E := E) (H := H) (I := I)
      (M := M) 1 3
    letI := tensorRSBundle_smooth (𝕜 := Real) (E := E) (H := H) (I := I)
      (M := M) (n := (∞ : WithTop ℕ∞)) 1 3
    ContMDiff I (I.prod 𝓘(Real, TensorRSModel 1 3 Real E)) (∞ : WithTop ℕ∞)
      (fun x : M =>
        (⟨x, riemannCurvatureAt (I := I) cov hcov x⟩ :
          TotalSpace (TensorRSModel 1 3 Real E)
            (fun x : M =>
              TensorRSSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) 1 3 x))) := by
  classical
  haveI : IsManifold I ((∞ : WithTop ℕ∞) + 1) M := by
    simpa using (inferInstance : IsManifold I ∞ M)
  letI := tensorRSBundle_topology (𝕜 := Real) (E := E) (H := H) (I := I)
    (M := M) 1 3
  letI := tensorRSBundle_fiber (𝕜 := Real) (E := E) (H := H) (I := I)
    (M := M) 1 3
  letI := tensorRSBundle_vector (𝕜 := Real) (E := E) (H := H) (I := I)
    (M := M) 1 3
  letI := tensorRSBundle_smooth (𝕜 := Real) (E := E) (H := H) (I := I)
    (M := M) (n := (∞ : WithTop ℕ∞)) 1 3
  letI : FiniteDimensional Real (TensorRSModel 1 3 Real E) := inferInstance
  intro x₀
  rw [contMDiffAt_section]
  let e := trivializationAt (TensorRSModel 1 3 Real E)
    (fun p : M => TensorRSSpace 1 3 I p) x₀
  have hx₀ : x₀ ∈ e.baseSet := by
    simpa [e] using
      (mem_baseSet_trivializationAt
        (TensorRSModel 1 3 Real E) (fun p : M => TensorRSSpace 1 3 I p) x₀)
  let G : M → TensorRSModel 1 3 Real E := fun p =>
    (e ⟨p, riemannCurvatureAt (I := I) cov hcov p⟩).2
  let d := Module.finrank Real E
  let bE : Module.Basis (Fin d) Real E := Module.finBasis Real E
  have hG : ContMDiffAt I 𝓘(Real, TensorRSModel 1 3 Real E)
      (∞ : WithTop ℕ∞) G x₀ := by
    refine contMDiffAt_tensorRSModel_of_apply_basis_eval_basis
      (I := I) (bE := bE) (G := G) (x₀ := x₀)
      (n := (∞ : WithTop ℕ∞)) ?_
    intro ρ σ
    let eTan := trivializationAt E (TangentSpace I : M → Type _) x₀
    let βρ : Tensor0SModel 1 Real E :=
      (continuousMultilinearMap_basis (𝕜 := Real) (F := E) bE 1) ρ
    let βsec : (p : M) → Tensor0SSpace (𝕜 := Real) (E := E) (H := H)
        (I := I) (M := M) 1 p :=
      fun p : M => Tensor0SSpace.constInChart
        (𝕜 := Real) (I := I) (M := M) 1 x₀ βρ p
    let vσ : Fin 3 → E := fun a => bE (σ a)
    have hx₀Tan : x₀ ∈ eTan.baseSet := by
      dsimp [eTan]
      exact mem_baseSet_trivializationAt E (TangentSpace I : M → Type _) x₀
    have hframe := eTan.isLocalFrameOn_localFrame_baseSet I (∞ : WithTop ℕ∞) bE
    obtain ⟨s', hs'⟩ := hframe.exists_contMDiffSection_eqOn_nhd eTan.open_baseSet hx₀Tan
    let Xs : ContMDiffSection I E (∞ : WithTop ℕ∞)
        (TangentSpace I : M → Type _) := s' (σ 0)
    let Ys : ContMDiffSection I E (∞ : WithTop ℕ∞)
        (TangentSpace I : M → Type _) := s' (σ 1)
    let Zs : ContMDiffSection I E (∞ : WithTop ℕ∞)
        (TangentSpace I : M → Type _) := s' (σ 2)
    let Rsec : (p : M) → TangentSpace I p := fun p : M =>
      connectionRiemannCurvatureField cov
        (fun q : M => Xs q) (fun q : M => Ys q) (fun q : M => Zs q) p
    have hβ : ContMDiffAt I (I.prod 𝓘(Real, Tensor0SModel 1 Real E))
        (∞ : WithTop ℕ∞)
        (fun p : M =>
          (⟨p, βsec p⟩ :
            TotalSpace (Tensor0SModel 1 Real E)
              (fun p : M => Tensor0SSpace 1 I p))) x₀ := by
      simpa [βsec] using
        tensor0SConstInChart_contMDiffAt
          (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) x₀ βρ
    have hR : ContMDiffAt I (I.prod 𝓘(Real, E)) (∞ : WithTop ℕ∞)
        (fun p : M =>
          (⟨p, Rsec p⟩ : TotalSpace E (TangentSpace I : M → Type _))) x₀ := by
      simpa [Rsec] using
        curvField_contMDiffAt (I := I) cov hcov Xs Ys Zs x₀
    have hscalar : ContMDiffAt I 𝓘(Real, Real) (∞ : WithTop ℕ∞)
        (fun p : M => cotangentToDual (I := I) (βsec p) (Rsec p)) x₀ := by
      have hEval := TensorMultilinear.contMDiffAt_section_apply
        (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
        (n := 1) (x₀ := x₀) (T := βsec) hβ
        (v := fun _ : Fin 1 => Rsec) (fun _ => hR)
      simpa [cotangentToDual_apply] using hEval
    refine hscalar.congr_of_eventuallyEq ?_
    filter_upwards [eTan.open_baseSet.mem_nhds hx₀Tan, hs'] with p hpTan hs'p
    have hbasis : ∀ i : Fin d,
        eTan.symmL Real p (bE i) = eTan.basisAt bE hpTan i := by
      intro i
      simp [Bundle.Trivialization.basisAt, Trivialization.symmL_apply]
    have hslots :
        (fun a : Fin 3 => eTan.symmL Real p (vσ a)) =
          vec3 (I := I) (Xs p) (Ys p) (Zs p) := by
      funext a
      fin_cases a <;>
        simp [vec3, Xs, Ys, Zs, vσ, eTan,
          hs'p (σ 0), hs'p (σ 1), hs'p (σ 2),
          hbasis,
          Bundle.Trivialization.localFrame_apply_of_mem_baseSet
            (e := eTan) (b := bE) (i := σ 0) hpTan,
          Bundle.Trivialization.localFrame_apply_of_mem_baseSet
            (e := eTan) (b := bE) (i := σ 1) hpTan,
          Bundle.Trivialization.localFrame_apply_of_mem_baseSet
            (e := eTan) (b := bE) (i := σ 2) hpTan]
    have hcoord := TensorRSSpace.trivializationAt_basis_coord
      (𝕜 := Real) (I := I) (x₀ := x₀) (x := p)
      (bE := bE) (r := 1) (s := 3) hpTan
      (riemannCurvatureAt (I := I) cov hcov p) ρ σ
    have hsmooth :=
      riemannCurvatureAt_apply_smooth (I := I) cov hcov Xs Ys Zs
        (βsec p)
    calc
      G p ((continuousMultilinearMap_basis (𝕜 := Real) (F := E) bE 1) ρ)
          (fun a : Fin 3 => bE (σ a))
          =
        (riemannCurvatureAt (I := I) cov hcov p (βsec p))
          (fun a : Fin 3 => eTan.symmL Real p (vσ a)) := by
          simpa [G, e, eTan, βρ, βsec, vσ] using hcoord
      _ = riemannCurvatureAt (I := I) cov hcov p (βsec p)
          (vec3 (I := I) (Xs p) (Ys p) (Zs p)) := by
          rw [hslots]
      _ = cotangentToDual (I := I) (βsec p) (Rsec p) := by
          simpa [Rsec] using hsmooth
  simpa [G, e] using hG

set_option backward.isDefEq.respectTransparency false in
/-- The bundled `(1,3)` Riemann tensor section of a locally smooth connection.

The value is the intrinsic curvature tensor `R(X,Y)Z` packaged pointwise.  The
smooth-section proof is the single section-assembly frontier: it should be
proved from smoothness and tensoriality of `connectionRiemannCurvatureField`,
not by a coordinate definition. -/
noncomputable def rm13Section
    (cov : CovariantDerivative I E (TangentSpace I : M → Type _))
    (hcov : CovariantDerivative.ContMDiffCovariantDerivativeLocally cov ∞)
    [T2Space M] :
    Tensor13Section (I := I) (M := M) :=
  by
    haveI : IsManifold I ((∞ : WithTop ℕ∞) + 1) M := by
      simpa using (inferInstance : IsManifold I ∞ M)
    exact
      ⟨fun x => riemannCurvatureAt cov hcov x,
        riemannCurvatureAt_contMDiff (I := I) cov hcov⟩

@[simp]
theorem rm13Section_apply
    (cov : CovariantDerivative I E (TangentSpace I : M → Type _))
    (hcov : CovariantDerivative.ContMDiffCovariantDerivativeLocally cov ∞)
    [T2Space M]
    (x : M) :
    rm13Section (I := I) (M := M) cov hcov x =
      riemannCurvatureAt cov hcov x := by
  rfl

@[simp]
theorem rm13Section_apply_const
    (cov : CovariantDerivative I E (TangentSpace I : M → Type _))
    (hcov : CovariantDerivative.ContMDiffCovariantDerivativeLocally cov ∞)
    [T2Space M]
    {x : M}
    (α : Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) 1 x)
    (X Y Z : TangentSpace I x) :
    rm13Section (I := I) (M := M) cov hcov x α (vec3 X Y Z) =
      cotangentToDual α
        (connectionRiemannCurvatureField cov
          (tangentConstAt (I := I) x X) (tangentConstAt (I := I) x Y)
          (tangentConstAt (I := I) x Z) x) := by
  rw [rm13Section_apply, riemannCurvatureAt_apply_const]
  rfl

/-- The canonical bundled `(1,3)` Riemann section evaluates on smooth tangent
sections as the connection curvature operator.

This is the smooth-slot tensoriality theorem for curvature.  The pointwise
constructor `riemannCurvatureAt` is defined using chart-constant
representatives; this theorem is the bridge from that constructor to arbitrary
smooth vector-field representatives. -/
theorem rm13Section_apply_smooth
    (cov : CovariantDerivative I E (TangentSpace I : M → Type _))
    (hcov : CovariantDerivative.ContMDiffCovariantDerivativeLocally cov ∞)
    [T2Space M]
    (X Y Z : ContMDiffSection I E (∞ : WithTop ℕ∞)
      (TangentSpace I : M → Type _))
    {x : M}
    (α : Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) 1 x) :
    rm13Section (I := I) (M := M) cov hcov x α (vec3 (X x) (Y x) (Z x)) =
      cotangentToDual α
        (connectionRiemannCurvatureField cov
          (fun p : M => X p) (fun p : M => Y p) (fun p : M => Z p) x) := by
  rw [rm13Section_apply]
  exact riemannCurvatureAt_apply_smooth (I := I) cov hcov X Y Z α

set_option backward.isDefEq.respectTransparency false in
private theorem riemannCurvature04At_contMDiff
    (g : SmoothRiemannianMetric I M)
    (cov : CovariantDerivative I E (TangentSpace I : M → Type _))
    (hcov : CovariantDerivative.ContMDiffCovariantDerivativeLocally cov ∞)
    [T2Space M] :
    letI := tensor0SBundle_topology (𝕜 := Real) (E := E) (H := H) (I := I)
      (M := M) 4
    ContMDiff I (I.prod 𝓘(Real, Tensor0SModel 4 Real E)) (∞ : WithTop ℕ∞)
      (fun x : M =>
        (⟨x, riemannCurvature04At (I := I) g cov hcov x⟩ :
          TotalSpace (Tensor0SModel 4 Real E)
            (fun x : M =>
          Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) 4 x))) := by
  classical
  haveI : IsManifold I ((∞ : WithTop ℕ∞) + 1) M := by
    simpa using (inferInstance : IsManifold I ∞ M)
  letI := tensor0SBundle_topology (𝕜 := Real) (E := E) (H := H) (I := I)
    (M := M) 4
  letI := TangentBundle.contMDiffVectorBundle (I := I) (M := M)
    (n := (∞ : WithTop ℕ∞))
  let d := Module.finrank Real E
  let b : Module.Basis (Fin d) Real E := Module.finBasis Real E
  let F : (p : M) →
      Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) 4 p :=
    fun p : M => riemannCurvature04At (I := I) g cov hcov p
  refine (contMDiff_multilinearSection_iff_coord (TangentSpace I)
    (∞ : WithTop ℕ∞) b F).mpr ?_
  intro σ x₀
  let eTan := trivializationAt E (TangentSpace I : M → Type _) x₀
  have hx₀Tan : x₀ ∈ eTan.baseSet := by
    dsimp [eTan]
    exact mem_baseSet_trivializationAt E (TangentSpace I : M → Type _) x₀
  have hframe := eTan.isLocalFrameOn_localFrame_baseSet I (∞ : WithTop ℕ∞) b
  obtain ⟨s', hs'⟩ := hframe.exists_contMDiffSection_eqOn_nhd eTan.open_baseSet hx₀Tan
  let Ws : ContMDiffSection I E (∞ : WithTop ℕ∞)
      (TangentSpace I : M → Type _) := s' (σ 0)
  let Xs : ContMDiffSection I E (∞ : WithTop ℕ∞)
      (TangentSpace I : M → Type _) := s' (σ 1)
  let Ys : ContMDiffSection I E (∞ : WithTop ℕ∞)
      (TangentSpace I : M → Type _) := s' (σ 2)
  let Zs : ContMDiffSection I E (∞ : WithTop ℕ∞)
      (TangentSpace I : M → Type _) := s' (σ 3)
  let Rsec : (p : M) → TangentSpace I p := fun p : M =>
    connectionRiemannCurvatureField cov
      (fun q : M => Xs q) (fun q : M => Ys q) (fun q : M => Zs q) p
  have hW : ContMDiffAt I (I.prod 𝓘(Real, E)) (∞ : WithTop ℕ∞)
      (fun p : M => (⟨p, Ws p⟩ : TotalSpace E (TangentSpace I : M → Type _))) x₀ :=
    Ws.contMDiff.contMDiffAt
  have hR : ContMDiffAt I (I.prod 𝓘(Real, E)) (∞ : WithTop ℕ∞)
      (fun p : M => (⟨p, Rsec p⟩ : TotalSpace E (TangentSpace I : M → Type _))) x₀ := by
    simpa [Rsec] using
      curvField_contMDiffAt (I := I) cov hcov Xs Ys Zs x₀
  have hscalar : ContMDiffAt I 𝓘(Real, Real) (∞ : WithTop ℕ∞)
      (fun p : M => g.inner p (Ws p) (Rsec p)) x₀ :=
    metric_inner_contMDiffAt (I := I) g hW hR
  refine hscalar.congr_of_eventuallyEq ?_
  filter_upwards [eTan.open_baseSet.mem_nhds hx₀Tan, hs'] with p hpTan hs'p
  have hbasis : ∀ i : Fin d,
      eTan.symmL Real p (b i) = eTan.basisAt b hpTan i := by
    intro i
    simp [Bundle.Trivialization.basisAt, Trivialization.symmL_apply]
  have hslots :
      (fun a : Fin 4 => eTan.symmL Real p (b (σ a))) =
        vec4 (I := I) (Ws p) (Xs p) (Ys p) (Zs p) := by
    funext a
    fin_cases a <;>
      simp [vec4, Ws, Xs, Ys, Zs,
        hs'p (σ 0), hs'p (σ 1), hs'p (σ 2), hs'p (σ 3), hbasis,
        Bundle.Trivialization.localFrame_apply_of_mem_baseSet
          (e := eTan) (b := b) (i := σ 0) hpTan,
        Bundle.Trivialization.localFrame_apply_of_mem_baseSet
          (e := eTan) (b := b) (i := σ 1) hpTan,
        Bundle.Trivialization.localFrame_apply_of_mem_baseSet
          (e := eTan) (b := b) (i := σ 2) hpTan,
        Bundle.Trivialization.localFrame_apply_of_mem_baseSet
          (e := eTan) (b := b) (i := σ 3) hpTan]
  rw [continuousMultilinearMap_basis_repr]
  change ((trivializationAt (Tensor0SModel 4 Real E)
      (Bundle.continuousMultilinearMap Real 4 E (TangentSpace I : M → Type _)) x₀
      ⟨p, F p⟩).2)
      (fun a : Fin 4 => b (σ a)) =
    g.inner p (Ws p) (Rsec p)
  change (F p).compContinuousLinearMap
      (fun _ : Fin 4 =>
        (trivializationAt E (TangentSpace I : M → Type _) x₀).symmL Real p)
      (fun a : Fin 4 => b (σ a)) =
    g.inner p (Ws p) (Rsec p)
  rw [ContinuousMultilinearMap.compContinuousLinearMap_apply, hslots]
  simpa [F, Rsec] using
    riemannCurvature04At_apply_smooth (I := I) g cov hcov Ws Xs Ys Zs p

set_option backward.isDefEq.respectTransparency false in
/-- The bundled lowered `(0,4)` Riemann tensor section of a locally smooth
connection and a metric. -/
noncomputable def rm04Section
    (g : SmoothRiemannianMetric I M)
    (cov : CovariantDerivative I E (TangentSpace I : M → Type _))
    (hcov : CovariantDerivative.ContMDiffCovariantDerivativeLocally cov ∞)
    [T2Space M] :
    Tensor04Section (I := I) (M := M) :=
  ⟨fun x => riemannCurvature04At g cov hcov x,
    riemannCurvature04At_contMDiff (I := I) g cov hcov⟩

@[simp]
theorem rm04Section_apply
    (g : SmoothRiemannianMetric I M)
    (cov : CovariantDerivative I E (TangentSpace I : M → Type _))
    (hcov : CovariantDerivative.ContMDiffCovariantDerivativeLocally cov ∞)
    [T2Space M]
    (x : M) :
    rm04Section (I := I) (M := M) g cov hcov x =
      riemannCurvature04At g cov hcov x := by
  rfl

@[simp]
theorem rm04Section_apply_const
    (g : SmoothRiemannianMetric I M)
    (cov : CovariantDerivative I E (TangentSpace I : M → Type _))
    (hcov : CovariantDerivative.ContMDiffCovariantDerivativeLocally cov ∞)
    [T2Space M]
    {x : M}
    (W X Y Z : TangentSpace I x) :
    rm04Section (I := I) (M := M) g cov hcov x (vec4 W X Y Z) =
      g.inner x W
        (connectionRiemannCurvatureField cov
          (tangentConstAt (I := I) x X) (tangentConstAt (I := I) x Y)
          (tangentConstAt (I := I) x Z) x) := by
  rw [rm04Section_apply, riemannCurvature04At_apply_const]
  rfl

/-- Smooth-slot evaluation form of the canonical lowered Riemann section. -/
theorem rm04Section_apply_smooth
    (g : SmoothRiemannianMetric I M)
    (cov : CovariantDerivative I E (TangentSpace I : M → Type _))
    (hcov : CovariantDerivative.ContMDiffCovariantDerivativeLocally cov ∞)
    [T2Space M]
    (W X Y Z : ContMDiffSection I E (∞ : WithTop ℕ∞)
      (TangentSpace I : M → Type _))
    (x : M) :
    rm04Section (I := I) (M := M) g cov hcov x
        (vec4 (W x) (X x) (Y x) (Z x)) =
      g.inner x (W x)
        (connectionRiemannCurvatureField cov
          (fun p : M => X p) (fun p : M => Y p) (fun p : M => Z p) x) := by
  rw [rm04Section_apply]
  exact riemannCurvature04At_apply_smooth (I := I) g cov hcov W X Y Z x

set_option backward.isDefEq.respectTransparency false in
/-- The bundled Ricci tensor section of a locally smooth connection. -/
noncomputable def ricciSection
    (cov : CovariantDerivative I E (TangentSpace I : M → Type _))
    (hcov : CovariantDerivative.ContMDiffCovariantDerivativeLocally cov ∞)
    [T2Space M] :
    Tensor02Section (I := I) (M := M) :=
  by
    haveI : IsManifold I ((∞ : WithTop ℕ∞) + 1) M := by
      simpa using (inferInstance : IsManifold I ∞ M)
    exact tensorRSField_applyInput (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) ∞
      (contract_TensorRSField (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
        (n := ∞) 0 2 (rm13Section (I := I) (M := M) cov hcov))
      (Tensor0SField.one0 (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) ∞)

@[simp]
theorem ricciSection_apply
    (cov : CovariantDerivative I E (TangentSpace I : M → Type _))
    (hcov : CovariantDerivative.ContMDiffCovariantDerivativeLocally cov ∞)
    [T2Space M]
    (x : M) :
    ricciSection (I := I) (M := M) cov hcov x =
      ricciCurvatureAt cov hcov x := by
  haveI : IsManifold I ((∞ : WithTop ℕ∞) + 1) M := by
    simpa using (inferInstance : IsManifold I ∞ M)
  have hone :
      Tensor0SField.one0 (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) ∞ x =
        scalarOne0S (I := I) x := by
    apply Tensor0SSpace.toModel_injective
    refine ContinuousMultilinearMap.ext fun v => ?_
    rw [Tensor0SField.one0_apply (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      (n := ∞) x v]
    change (1 : Real) =
      (ContinuousMultilinearMap.constOfIsEmpty Real (fun _ : Fin 0 => E) 1) v
    simp
  simp [ricciSection, ricciCurvatureAt, ricciFromRm13At, contract_TensorRSField,
    contract_TensorRSField_fun, hone]

@[simp]
theorem ricciSection_eq_trace
    (cov : CovariantDerivative I E (TangentSpace I : M → Type _))
    (hcov : CovariantDerivative.ContMDiffCovariantDerivativeLocally cov ∞)
    [T2Space M]
    (x : M) :
    ricciSection (I := I) (M := M) cov hcov x =
      ricciFromRm13At (I := I) (M := M)
        (rm13Section (I := I) (M := M) cov hcov x) := by
  rw [ricciSection_apply, rm13Section_apply, ricciCurvatureAt_eq_trace]

end CovariantDerivative

end RicciFlower.Riemann

