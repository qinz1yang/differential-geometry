import DifferentialGeometry.Geometry.Connection.TensorNabla.HomBundleNabla
import DifferentialGeometry.Geometry.Curvature.CurvatureOperator.CurvatureBundling

/-!
# Curvature–Leibniz step for the generic Hom-bundle covariant derivative

Let `U` and `V` be smooth vector bundles over `M` with covariant derivatives `cov_U` and
`cov_V`, and let `cov := homBundleCovariantDerivativeGen cov_U cov_V` be the induced covariant
derivative on the Hom-bundle `Hom(U, V) = fun x => U x →L[ℝ] V x`. The section-level Riemann
curvature operator `riemannSec` of the three connections obeys the **curvature–Leibniz rule**: at
every point `x`, for smooth tangent fields `X, W` and smooth global sections `τ` (of `Hom(U, V)`)
and `Y` (of `U`),

```
(riemannSec cov X W τ x) (Y x) =
  riemannSec cov_V X W (fun b => τ b (Y b)) x − τ x (riemannSec cov_U X W Y x).
```

In words, the Hom-bundle curvature applied to `τ` and then paired with `Y` equals the curvature
of the *paired* `V`-section `b ↦ τ b (Y b)` minus `τ` of the curvature of `Y`. This is the
exact curvature analogue of the first-order product rule
`cov_V (τ·Y) = (cov τ)·Y + τ·(cov_U Y)` (the defining `homBundleCovariantDerivativeGen` apply
formula), differentiated a second time so that the four mixed `(∇τ)(∇Y)` cross terms cancel
between the two derivative orderings. It is the single inductive ingredient from which the
slot-wise tensor curvature formula is assembled.

## Main result

* `riemannSec_homBundleGen_apply_eq` — the curvature–Leibniz identity displayed above.
-/

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option linter.style.setOption false
set_option linter.unusedSectionVars false
set_option synthInstance.maxHeartbeats 800000
set_option maxHeartbeats 1200000

open scoped Manifold ContDiff Topology
open Bundle CovariantDerivative
open DifferentialGeometry.Integral.Connection

namespace HomConnectionGen

variable
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
  {H : Type*} [TopologicalSpace H]
  (I : ModelWithCorners ℝ E H)
  (M : Type*) [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [SigmaCompactSpace M] [T2Space M] [BoundarylessManifold I M]
  (E_U : Type*) [NormedAddCommGroup E_U] [NormedSpace ℝ E_U]
  [FiniteDimensional ℝ E_U] [CompleteSpace E_U]
  (U : M → Type*) [∀ x, AddCommGroup (U x)] [∀ x, Module ℝ (U x)]
  [∀ x, TopologicalSpace (U x)]
  [TopologicalSpace (TotalSpace E_U U)] [FiberBundle E_U U] [VectorBundle ℝ E_U U]
  [∀ x, IsTopologicalAddGroup (U x)] [∀ x, ContinuousSMul ℝ (U x)]
  [ContMDiffVectorBundle ∞ E_U U I]
  (F : Type*) [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
  [CompleteSpace F]
  (V : M → Type*) [∀ x, AddCommGroup (V x)] [∀ x, Module ℝ (V x)]
  [∀ x, TopologicalSpace (V x)]
  [TopologicalSpace (TotalSpace F V)] [FiberBundle F V] [VectorBundle ℝ F V]
  [∀ x, IsTopologicalAddGroup (V x)] [∀ x, ContinuousSMul ℝ (V x)]
  [ContMDiffVectorBundle ∞ F V I]

/-- The `V`-valued pairing section `b ↦ τ b (Y b)` of a Hom-section `τ` with a `U`-section `Y`. -/
def pairedSection (τ : Π b : M, (U b →L[ℝ] V b)) (Y : Π b : M, U b) :
    Π b : M, V b :=
  fun b => τ b (Y b)

@[simp] lemma pairedSection_apply (τ : Π b : M, (U b →L[ℝ] V b)) (Y : Π b : M, U b) (b : M) :
    pairedSection (M := M) (U := U) (V := V) τ Y b = τ b (Y b) := rfl

/-- The abbreviation `cov := homBundleCovariantDerivativeGen cov_U cov_V`. -/
local notation "covHom" =>
  homBundleCovariantDerivativeGen I M E_U U F V

/-- **First-order product rule, section form.** For smooth tangent field `Z`, smooth Hom-section
`τ`, and smooth `U`-section `Y`, the directional covariant derivative along `Z` of the paired
`V`-section `b ↦ τ b (Y b)` satisfies, at every base point `b`,
```
cov_V (τ·Y) b (Z b) = (cov τ b (Z b)) (Y b) + τ b (cov_U Y b (Z b)),
```
i.e. as a `V`-section it splits as `pairedSection (covApply cov Z τ) Y + pairedSection τ
(covApply cov_U Z Y)`. This is exactly the `homBundleCovariantDerivativeGen` defining apply
formula rearranged. -/
lemma covApply_cov_V_pairedSection_eq
    (cov_U : CovariantDerivative I E_U U)
    (cov_V : CovariantDerivative I F V)
    (Z : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯)
    (τ : Cₛ^∞⟮I; E_U →L[ℝ] F, (fun x : M => U x →L[ℝ] V x)⟯)
    (Y : Cₛ^∞⟮I; E_U, U⟯) :
    covApply cov_V (fun b => Z b)
        (pairedSection (M := M) (U := U) (V := V) (fun b => τ b) (fun b => Y b)) =
      pairedSection (M := M) (U := U) (V := V)
          (covApply (covHom cov_U cov_V) (fun b => Z b) (fun b => τ b)) (fun b => Y b) +
        pairedSection (M := M) (U := U) (V := V) (fun b => τ b)
          (covApply cov_U (fun b => Z b) (fun b => Y b)) := by
  funext b
  have hZ : MDifferentiableAt I (I.prod 𝓘(ℝ, E))
      (fun y => TotalSpace.mk' E (E := TangentSpace I) y (Z y)) b :=
    Z.contMDiff.contMDiffAt.mdifferentiableAt (by simp)
  have hτ : MDifferentiableAt I (I.prod 𝓘(ℝ, E_U →L[ℝ] F))
      (fun y => TotalSpace.mk' (E_U →L[ℝ] F)
        (E := fun x : M => (U x →L[ℝ] V x)) y (τ y)) b :=
    τ.contMDiff.contMDiffAt.mdifferentiableAt (by simp)
  have hY : MDifferentiableAt I (I.prod 𝓘(ℝ, E_U))
      (fun y => TotalSpace.mk' E_U (E := U) y (Y y)) b :=
    Y.contMDiff.contMDiffAt.mdifferentiableAt (by simp)
  have hkey :=
    homBundleCovariantDerivativeGen_apply_of_mdifferentiableAt I M E_U U F V cov_U cov_V
      (fun y : M => τ y) hτ hZ hY
  simp only [Pi.add_apply, pairedSection, covApply_apply]

  rw [hkey]
  abel

/-- **First-order product rule, pointwise form at `x`.** For a Hom-section `σ` differentiable at
`x`, a `U`-section `Y` differentiable at `x`, and any tangent vector `v ∈ T_x M`,
```
cov_V (σ·Y) x v = (cov σ x v) (Y x) + σ x (cov_U Y x v).
```
This is the defining `homBundleCovariantDerivativeGen` apply formula at the single point `x`,
rearranged. -/
lemma cov_V_toFun_pairedSection_apply
    (cov_U : CovariantDerivative I E_U U)
    (cov_V : CovariantDerivative I F V)
    {σ : Π b : M, (U b →L[ℝ] V b)} {Y : Π b : M, U b} {x : M}
    (hσ : MDifferentiableAt I (I.prod 𝓘(ℝ, E_U →L[ℝ] F))
      (fun y : M => TotalSpace.mk' (E_U →L[ℝ] F)
        (E := fun z : M => (U z →L[ℝ] V z)) y (σ y)) x)
    (hY : MDifferentiableAt I (I.prod 𝓘(ℝ, E_U))
      (fun y : M => TotalSpace.mk' E_U (E := U) y (Y y)) x)
    (v : TangentSpace I x) :
    cov_V.toFun (pairedSection (M := M) (U := U) (V := V) σ Y) x v =
      (covHom cov_U cov_V σ x v) (Y x) + σ x (cov_U.toFun Y x v) := by
  classical
  set X : Π b : M, TangentSpace I b := fun b => smoothExtensionTangent (I := I) x v b with hX_def
  have hXx : X x = v := smoothExtensionTangent_eq (I := I) x v
  have hX_smooth : ContMDiff I (I.prod 𝓘(ℝ, E)) ∞ (T% X) :=
    smoothExtensionTangent_contMDiff (I := I) x v
  have hX_at : MDifferentiableAt I (I.prod 𝓘(ℝ, E))
      (fun y => TotalSpace.mk' E (E := TangentSpace I) y (X y)) x :=
    (hX_smooth x).mdifferentiableAt (by simp)
  have hkey :=
    homBundleCovariantDerivativeGen_apply_of_mdifferentiableAt I M E_U U F V cov_U cov_V
      σ hσ hX_at hY
  rw [hXx] at hkey

  rw [show cov_V.toFun (pairedSection (M := M) (U := U) (V := V) σ Y) x v =
      cov_V.toFun (fun y => σ y (Y y)) x v from rfl, hkey]
  abel

/-- **Second-order expansion of `cov_V` of the paired section.** For smooth tangent field `Z`,
smooth Hom-section `τ`, smooth `U`-section `Y`, and any tangent vector `v`,
`cov_V.toFun (covApply cov_V Z (τ·Y)) x v` expands into the four product terms obtained by the
first-order product rule applied at the inner derivative `covApply cov_V Z (τ·Y) =
(covApply cov Z τ)·Y + τ·(covApply cov_U Z Y)` and then at the outer `cov_V`. -/
lemma cov_V_toFun_covApply_pairedSection_apply
    (cov_U : CovariantDerivative I E_U U) [ContMDiffCovariantDerivative cov_U ∞]
    (cov_V : CovariantDerivative I F V) [ContMDiffCovariantDerivative cov_V ∞]
    (Z : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯)
    (τ : Cₛ^∞⟮I; E_U →L[ℝ] F, (fun x : M => U x →L[ℝ] V x)⟯)
    (Y : Cₛ^∞⟮I; E_U, U⟯) {x : M} (v : TangentSpace I x) :
    cov_V.toFun
        (covApply cov_V (fun b => Z b)
          (pairedSection (M := M) (U := U) (V := V) (fun b => τ b) (fun b => Y b))) x v =
      (covHom cov_U cov_V (covApply (covHom cov_U cov_V) (fun b => Z b) (fun b => τ b)) x v)
          (Y x) +
        (covApply (covHom cov_U cov_V) (fun b => Z b) (fun b => τ b) x) (cov_U.toFun (fun b => Y b) x v) +
        (covHom cov_U cov_V (fun b => τ b) x v)
          (covApply cov_U (fun b => Z b) (fun b => Y b) x) +
        (τ x) (cov_U.toFun (covApply cov_U (fun b => Z b) (fun b => Y b)) x v) := by
  classical

  have hZ := Z.contMDiff
  have hτ := τ.contMDiff
  have hY := Y.contMDiff
  have hτ1 : ContMDiff I (I.prod 𝓘(ℝ, E_U →L[ℝ] F)) ((∞ : WithTop ℕ∞) + 1)
      (fun y : M => TotalSpace.mk' (E_U →L[ℝ] F)
        (E := fun z : M => (U z →L[ℝ] V z)) y (τ y)) := by
    rw [show (∞ : WithTop ℕ∞) + 1 = ∞ from by simp]; exact τ.contMDiff
  have hY1 : ContMDiff I (I.prod 𝓘(ℝ, E_U)) ((∞ : WithTop ℕ∞) + 1)
      (fun y : M => TotalSpace.mk' E_U (E := U) y (Y y)) := by
    rw [show (∞ : WithTop ℕ∞) + 1 = ∞ from by simp]; exact Y.contMDiff

  have hcovZτ := covApply_mdifferentiableAt (cov := covHom cov_U cov_V) (x := x) hZ hτ1
  have hcovZY := covApply_mdifferentiableAt (cov := cov_U) (x := x) hZ hY1
  have hτ_at : MDifferentiableAt I (I.prod 𝓘(ℝ, E_U →L[ℝ] F))
      (fun y : M => TotalSpace.mk' (E_U →L[ℝ] F)
        (E := fun z : M => (U z →L[ℝ] V z)) y (τ y)) x :=
    (hτ x).mdifferentiableAt (by simp)
  have hY_at : MDifferentiableAt I (I.prod 𝓘(ℝ, E_U))
      (fun y : M => TotalSpace.mk' E_U (E := U) y (Y y)) x :=
    (hY x).mdifferentiableAt (by simp)

  have hsec := covApply_cov_V_pairedSection_eq I M E_U U F V cov_U cov_V Z τ Y
  rw [hsec]

  have hcovZτ_glob :=
    contMDiffOn_univ.mp (covApply_contMDiffOn (cov := covHom cov_U cov_V) hZ hτ1)
  have hcovZY_glob :=
    contMDiffOn_univ.mp (covApply_contMDiffOn (cov := cov_U) hZ hY1)
  have hadd1 : MDiffAt (T% (pairedSection (M := M) (U := U) (V := V)
      (covApply (covHom cov_U cov_V) (fun b => Z b) (fun b => τ b)) (fun b => Y b))) x :=
    ((ContMDiff.clm_bundle_apply (b := id) hcovZτ_glob hY) x).mdifferentiableAt (by simp)
  have hadd2 : MDiffAt (T% (pairedSection (M := M) (U := U) (V := V)
      (fun b => τ b) (covApply cov_U (fun b => Z b) (fun b => Y b)))) x :=
    ((ContMDiff.clm_bundle_apply (b := id) hτ hcovZY_glob) x).mdifferentiableAt (by simp)
  rw [cov_V.isCovariantDerivativeOnUniv.add hadd1 hadd2]
  simp only [ContinuousLinearMap.add_apply]

  rw [cov_V_toFun_pairedSection_apply I M E_U U F V cov_U cov_V hcovZτ hY_at v,
      cov_V_toFun_pairedSection_apply I M E_U U F V cov_U cov_V hτ_at hcovZY v]
  abel

/-- **Curvature–Leibniz rule for the generic Hom-bundle, additive form.** For smooth tangent
fields `X, W`, a smooth Hom-section `τ`, and a smooth `U`-section `Y`, the curvature of the
paired `V`-section equals the Hom-curvature paired with `Y` plus `τ` of the `U`-curvature:
```
riemannSec cov_V X W (τ·Y) x =
  (riemannSec cov X W τ x) (Y x) + τ x (riemannSec cov_U X W Y x).
```
The four mixed `(∇τ)(∇Y)` cross terms produced by expanding both sides cancel. -/
lemma riemannSec_cov_V_pairedSection_eq
    (cov_U : CovariantDerivative I E_U U) [ContMDiffCovariantDerivative cov_U ∞]
    (cov_V : CovariantDerivative I F V) [ContMDiffCovariantDerivative cov_V ∞]
    (X W : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯)
    (τ : Cₛ^∞⟮I; E_U →L[ℝ] F, (fun x : M => U x →L[ℝ] V x)⟯)
    (Y : Cₛ^∞⟮I; E_U, U⟯) (x : M) :
    riemannSec cov_V (fun b => X b) (fun b => W b)
        (pairedSection (M := M) (U := U) (V := V) (fun b => τ b) (fun b => Y b)) x =
      (riemannSec (covHom cov_U cov_V) (fun b => X b) (fun b => W b) (fun b => τ b) x) (Y x) +
        (τ x) (riemannSec cov_U (fun b => X b) (fun b => W b) (fun b => Y b) x) := by
  classical
  set cov := covHom cov_U cov_V with hcov

  have hτ_at : MDifferentiableAt I (I.prod 𝓘(ℝ, E_U →L[ℝ] F))
      (fun y : M => TotalSpace.mk' (E_U →L[ℝ] F)
        (E := fun z : M => (U z →L[ℝ] V z)) y (τ y)) x :=
    (τ.contMDiff x).mdifferentiableAt (by simp)
  have hY_at : MDifferentiableAt I (I.prod 𝓘(ℝ, E_U))
      (fun y : M => TotalSpace.mk' E_U (E := U) y (Y y)) x :=
    (Y.contMDiff x).mdifferentiableAt (by simp)

  rw [riemannSec_def]

  rw [cov_V_toFun_covApply_pairedSection_apply I M E_U U F V cov_U cov_V W τ Y (X x),
      cov_V_toFun_covApply_pairedSection_apply I M E_U U F V cov_U cov_V X τ Y (W x)]

  rw [cov_V_toFun_pairedSection_apply I M E_U U F V cov_U cov_V hτ_at hY_at
        (VectorField.mlieBracket I (fun b => X b) (fun b => W b) x)]

  rw [riemannSec_def, riemannSec_def]
  simp only [covApply_apply, ContinuousLinearMap.sub_apply, map_sub]
  abel

/-- **Curvature–Leibniz rule for the generic Hom-bundle (subtractive form).** For smooth tangent
fields `X, W`, a smooth Hom-section `τ`, and a smooth `U`-section `Y`, the Hom-bundle curvature
applied to `τ` and paired with `Y` equals the `V`-curvature of the paired section minus `τ` of
the `U`-curvature of `Y`:
```
(riemannSec cov X W τ x) (Y x) =
  riemannSec cov_V X W (fun b => τ b (Y b)) x − τ x (riemannSec cov_U X W Y x).
```
This is the single inductive ingredient from which the slot-wise tensor curvature formula is
assembled: it expresses the Hom-bundle curvature operator through the curvatures of the source
and target bundles. -/
theorem riemannSec_homBundleGen_apply_eq
    (cov_U : CovariantDerivative I E_U U) [ContMDiffCovariantDerivative cov_U ∞]
    (cov_V : CovariantDerivative I F V) [ContMDiffCovariantDerivative cov_V ∞]
    (X W : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯)
    (τ : Cₛ^∞⟮I; E_U →L[ℝ] F, (fun x : M => U x →L[ℝ] V x)⟯)
    (Y : Cₛ^∞⟮I; E_U, U⟯) (x : M) :
    (riemannSec (covHom cov_U cov_V) (fun b => X b) (fun b => W b) (fun b => τ b) x) (Y x) =
      riemannSec cov_V (fun b => X b) (fun b => W b)
          (pairedSection (M := M) (U := U) (V := V) (fun b => τ b) (fun b => Y b)) x -
        (τ x) (riemannSec cov_U (fun b => X b) (fun b => W b) (fun b => Y b) x) := by
  rw [riemannSec_cov_V_pairedSection_eq I M E_U U F V cov_U cov_V X W τ Y x]
  abel

end HomConnectionGen

end
