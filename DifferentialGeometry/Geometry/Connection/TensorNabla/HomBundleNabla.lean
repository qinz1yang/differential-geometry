import DifferentialGeometry.Bundle.Hom
import DifferentialGeometry.Geometry.Connection.Realization.TensorNabla
import DifferentialGeometry.Geometry.Connection.Realization.SmoothSections
import DifferentialGeometry.Geometry.Connection.Realization.Connection
import Mathlib.Geometry.Manifold.VectorBundle.CovariantDerivative.Metric
import Mathlib.Geometry.Manifold.VectorBundle.Tensoriality
open DifferentialGeometry.Geometry.Connection.Realization


noncomputable section


open scoped Manifold ContDiff Topology
open Bundle CovariantDerivative

namespace DifferentialGeometry
namespace HomConnectionGen

variable
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
  {H : Type*} [TopologicalSpace H]
  (I : ModelWithCorners ℝ E H)
  (M : Type*) [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [SigmaCompactSpace M] [T2Space M]
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

private abbrev MDiffAtHom
    (τ : Π x : M, (U x →L[ℝ] V x)) (x : M) : Prop :=
  MDifferentiableAt I (I.prod 𝓘(ℝ, E_U →L[ℝ] F))
    (fun y => TotalSpace.mk' (E_U →L[ℝ] F)
      (E := fun x : M => (U x →L[ℝ] V x)) y (τ y)) x

private abbrev MDiffAtU (Y : Π x : M, U x) (x : M) : Prop :=
  MDifferentiableAt I (I.prod 𝓘(ℝ, E_U))
    (fun y => TotalSpace.mk' E_U (E := U) y (Y y)) x

private abbrev MDiffAtV (σ : Π x : M, V x) (x : M) : Prop :=
  MDifferentiableAt I (I.prod 𝓘(ℝ, F))
    (fun y => TotalSpace.mk' F (E := V) y (σ y)) x

omit [FiniteDimensional ℝ E] [CompleteSpace E] [IsManifold I ∞ M] [SigmaCompactSpace M] [T2Space M]
    [FiniteDimensional ℝ E_U] [CompleteSpace E_U] [∀ (x : M), IsTopologicalAddGroup (U x)]
    [∀ (x : M), ContinuousSMul ℝ (U x)] [ContMDiffVectorBundle ∞ E_U U I] [FiniteDimensional ℝ F]
    [CompleteSpace F] [ContMDiffVectorBundle ∞ F V I] in
private theorem mdiffAt_apply
    {τ : Π x : M, (U x →L[ℝ] V x)}
    {Y : Π x : M, U x} {x : M}
    (hτ : MDiffAtHom I M E_U U F V τ x) (hY : MDiffAtU I M E_U U Y x) :
    MDiffAtV I M F V (fun y => τ y (Y y)) x := by
  exact MDifferentiableAt.clm_bundle_apply (b := id) hτ hY

private def Psi
    (cov_U : CovariantDerivative I E_U U)
    (cov_V : CovariantDerivative I F V)
    (τ : Π x : M, (U x →L[ℝ] V x))
    (V_field : Π x : M, TangentSpace I x)
    (Y : Π x : M, U x) (x : M) : V x :=
  cov_V (fun y => τ y (Y y)) x (V_field x) - τ x (cov_U Y x (V_field x))

omit [FiniteDimensional ℝ E] [CompleteSpace E] [IsManifold I ∞ M] [SigmaCompactSpace M] [T2Space M]
    [FiniteDimensional ℝ E_U] [CompleteSpace E_U] [VectorBundle ℝ E_U U]
    [ContMDiffVectorBundle ∞ E_U U I] [FiniteDimensional ℝ F] [CompleteSpace F] [VectorBundle ℝ F V]
    [ContMDiffVectorBundle ∞ F V I] in
private theorem Psi_add_left
    (cov_U : CovariantDerivative I E_U U)
    (cov_V : CovariantDerivative I F V)
    (τ : Π x : M, (U x →L[ℝ] V x))
    {V_field V_field' : Π x : M, TangentSpace I x}
    {Y : Π x : M, U x} {x : M} :
    Psi I M E_U U F V cov_U cov_V τ (V_field + V_field') Y x =
      Psi I M E_U U F V cov_U cov_V τ V_field Y x +
        Psi I M E_U U F V cov_U cov_V τ V_field' Y x := by
  have h_add : (V_field + V_field' : Π x : M, TangentSpace I x) x = V_field x + V_field' x := rfl
  simp only [Psi, h_add, ContinuousLinearMap.map_add]
  abel

omit [FiniteDimensional ℝ E] [CompleteSpace E] [IsManifold I ∞ M] [SigmaCompactSpace M] [T2Space M]
    [FiniteDimensional ℝ E_U] [CompleteSpace E_U] [VectorBundle ℝ E_U U]
    [ContMDiffVectorBundle ∞ E_U U I] [FiniteDimensional ℝ F] [CompleteSpace F] [VectorBundle ℝ F V]
    [ContMDiffVectorBundle ∞ F V I] in
private theorem Psi_smul_left
    (cov_U : CovariantDerivative I E_U U)
    (cov_V : CovariantDerivative I F V)
    (τ : Π x : M, (U x →L[ℝ] V x))
    {f : M → ℝ} {V_field : Π x : M, TangentSpace I x}
    {Y : Π x : M, U x} {x : M} :
    Psi I M E_U U F V cov_U cov_V τ (f • V_field) Y x =
      f x • Psi I M E_U U F V cov_U cov_V τ V_field Y x := by
  have h_smul : (f • V_field : Π x : M, TangentSpace I x) x = f x • V_field x := rfl
  simp only [Psi, h_smul, ContinuousLinearMap.map_smul]
  rw [smul_sub]

omit [FiniteDimensional ℝ E] [CompleteSpace E] [IsManifold I ∞ M] [SigmaCompactSpace M] [T2Space M]
    [FiniteDimensional ℝ E_U] [CompleteSpace E_U] [ContMDiffVectorBundle ∞ E_U U I]
    [FiniteDimensional ℝ F] [CompleteSpace F] [ContMDiffVectorBundle ∞ F V I] in
private theorem Psi_add_right
    (cov_U : CovariantDerivative I E_U U)
    (cov_V : CovariantDerivative I F V)
    (τ : Π x : M, (U x →L[ℝ] V x))
    {V_field : Π x : M, TangentSpace I x}
    {Y Y' : Π x : M, U x} {x : M}
    (hτ : MDiffAtHom I M E_U U F V τ x)
    (hY : MDiffAtU I M E_U U Y x) (hY' : MDiffAtU I M E_U U Y' x) :
    Psi I M E_U U F V cov_U cov_V τ V_field (Y + Y') x =
      Psi I M E_U U F V cov_U cov_V τ V_field Y x +
        Psi I M E_U U F V cov_U cov_V τ V_field Y' x := by
  have hτY : MDiffAtV I M F V (fun y => τ y (Y y)) x := mdiffAt_apply I M E_U U F V hτ hY
  have hτY' : MDiffAtV I M F V (fun y => τ y (Y' y)) x := mdiffAt_apply I M E_U U F V hτ hY'
  have h_add_fun : (fun y => τ y ((Y + Y') y)) =
      (fun y => τ y (Y y)) + (fun y => τ y (Y' y)) := by
    funext y
    simp [Pi.add_apply, ContinuousLinearMap.map_add]
  have hY_T : MDiffAt (T% fun y => Y y) x := hY
  have hY'_T : MDiffAt (T% fun y => Y' y) x := hY'
  simp only [Psi]
  rw [h_add_fun, cov_V.isCovariantDerivativeOn.add hτY hτY']
  rw [show (Y + Y' : Π x : M, U x) = (fun x => Y x) + (fun x => Y' x) from rfl,
      cov_U.isCovariantDerivativeOn.add hY_T hY'_T]
  simp only [add_apply, ContinuousLinearMap.map_add]
  abel

omit [FiniteDimensional ℝ E] [CompleteSpace E] [IsManifold I ∞ M] [SigmaCompactSpace M] [T2Space M]
    [FiniteDimensional ℝ E_U] [CompleteSpace E_U] [ContMDiffVectorBundle ∞ E_U U I]
    [FiniteDimensional ℝ F] [CompleteSpace F] [ContMDiffVectorBundle ∞ F V I] in
private theorem Psi_smul_right
    (cov_U : CovariantDerivative I E_U U)
    (cov_V : CovariantDerivative I F V)
    (τ : Π x : M, (U x →L[ℝ] V x))
    {V_field : Π x : M, TangentSpace I x}
    {Y : Π x : M, U x} {f : M → ℝ} {x : M}
    (hτ : MDiffAtHom I M E_U U F V τ x)
    (hf : MDifferentiableAt I 𝓘(ℝ, ℝ) f x)
    (hY : MDiffAtU I M E_U U Y x) :
    Psi I M E_U U F V cov_U cov_V τ V_field (f • Y) x =
      f x • Psi I M E_U U F V cov_U cov_V τ V_field Y x := by
  have hτY : MDiffAtV I M F V (fun y => τ y (Y y)) x := mdiffAt_apply I M E_U U F V hτ hY
  have h_fun : (fun y => τ y ((f • Y) y)) = f • (fun y => τ y (Y y)) := by
    funext y
    exact ContinuousLinearMap.map_smul (τ y) (f y) (Y y)
  have hY_T : MDiffAt (T% fun y => Y y) x := hY
  simp only [Psi]
  rw [h_fun]
  rw [cov_V.isCovariantDerivativeOn.leibniz hτY hf]
  rw [show (f • Y : Π x : M, U x) = f • (fun x => Y x) from rfl,
      cov_U.isCovariantDerivativeOn.leibniz hY_T hf]
  simp only [add_apply, smul_apply,
    ContinuousLinearMap.smulRight_apply, ContinuousLinearMap.map_add,
    ContinuousLinearMap.map_smul]
  rw [smul_sub]
  abel

omit [FiniteDimensional ℝ E] [CompleteSpace E] [SigmaCompactSpace M] [T2Space M]
    [FiniteDimensional ℝ E_U] [CompleteSpace E_U] [VectorBundle ℝ E_U U]
    [ContMDiffVectorBundle ∞ E_U U I] [FiniteDimensional ℝ F] [CompleteSpace F] [VectorBundle ℝ F V]
    [ContMDiffVectorBundle ∞ F V I] in
private theorem Psi_tensorialAt_left
    (cov_U : CovariantDerivative I E_U U)
    (cov_V : CovariantDerivative I F V)
    (τ : Π x : M, (U x →L[ℝ] V x))
    {x : M} (Y : Π x : M, U x) :
    TensorialAt I E (fun V_field => Psi I M E_U U F V cov_U cov_V τ V_field Y x) x where
  smul := fun _ _ => Psi_smul_left I M E_U U F V cov_U cov_V τ
  add := fun _ _ => Psi_add_left I M E_U U F V cov_U cov_V τ

omit [FiniteDimensional ℝ E] [CompleteSpace E] [IsManifold I ∞ M] [SigmaCompactSpace M] [T2Space M]
    [FiniteDimensional ℝ E_U] [CompleteSpace E_U] [ContMDiffVectorBundle ∞ E_U U I]
    [FiniteDimensional ℝ F] [CompleteSpace F] [ContMDiffVectorBundle ∞ F V I] in
private theorem Psi_tensorialAt_right
    (cov_U : CovariantDerivative I E_U U)
    (cov_V : CovariantDerivative I F V)
    (τ : Π x : M, (U x →L[ℝ] V x))
    {x : M} (hτ : MDiffAtHom I M E_U U F V τ x)
    (V_field : Π x : M, TangentSpace I x) :
    TensorialAt I E_U (fun Y => Psi I M E_U U F V cov_U cov_V τ V_field Y x) x where
  smul := fun hf hY => Psi_smul_right I M E_U U F V cov_U cov_V τ hτ hf hY
  add := fun hY hY' => Psi_add_right I M E_U U F V cov_U cov_V τ hτ hY hY'

omit [FiniteDimensional ℝ E] [CompleteSpace E] [IsManifold I ∞ M] [SigmaCompactSpace M] [T2Space M]
    [FiniteDimensional ℝ E_U] [CompleteSpace E_U] [∀ (x : M), IsTopologicalAddGroup (U x)]
    [∀ (x : M), ContinuousSMul ℝ (U x)] [ContMDiffVectorBundle ∞ E_U U I] [FiniteDimensional ℝ F]
    [CompleteSpace F] [ContMDiffVectorBundle ∞ F V I] in
private theorem hom_section_mdiff
    (τ : Cₛ^∞⟮I; E_U →L[ℝ] F, (fun x => U x →L[ℝ] V x)⟯)
    (x : M) : MDiffAtHom I M E_U U F V (τ : Π x : M, (U x →L[ℝ] V x)) x :=
  τ.contMDiff.contMDiffAt.mdifferentiableAt (by simp)

omit [FiniteDimensional ℝ E] [CompleteSpace E] [IsManifold I ∞ M] [SigmaCompactSpace M] [T2Space M]
    [FiniteDimensional ℝ E_U] [CompleteSpace E_U] [VectorBundle ℝ E_U U]
    [∀ (x : M), IsTopologicalAddGroup (U x)] [∀ (x : M), ContinuousSMul ℝ (U x)]
    [ContMDiffVectorBundle ∞ E_U U I] in
omit [(x : M) → Module ℝ (U x)] in
omit [(x : M) → AddCommGroup (U x)] in
private theorem u_section_mdiff
    (Y : Cₛ^∞⟮I; E_U, U⟯) (x : M) :
    MDiffAtU I M E_U U (Y : Π x : M, U x) x :=
  Y.contMDiff.contMDiffAt.mdifferentiableAt (by simp)

omit [FiniteDimensional ℝ E] [CompleteSpace E] [SigmaCompactSpace M] [T2Space M] in
private theorem vec_section_mdiff
    (Y : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) (x : M) :
    MDifferentiableAt I (I.prod 𝓘(ℝ, E))
      (fun y => TotalSpace.mk' E (E := TangentSpace I) y (Y y)) x :=
  Y.contMDiff.contMDiffAt.mdifferentiableAt (by simp)

noncomputable def homBundleCovariantDerivativeGenFun
    (cov_U : CovariantDerivative I E_U U)
    (cov_V : CovariantDerivative I F V)
    (τ : Π x : M, (U x →L[ℝ] V x))
    (x : M) :
    TangentSpace I x →L[ℝ] (U x →L[ℝ] V x) := by
  classical
  by_cases hτ : MDiffAtHom I M E_U U F V τ x
  · exact TensorialAt.mkHom₂ (F := E) (F' := E_U)
      (V := (TangentSpace I : M → Type _)) (V' := U)
      (A := V x)
      (fun V_field Y => Psi I M E_U U F V cov_U cov_V τ V_field Y x) x
      (fun Y _ => Psi_tensorialAt_left I M E_U U F V cov_U cov_V τ Y)
      (fun V_field _ => Psi_tensorialAt_right I M E_U U F V cov_U cov_V τ hτ V_field)
  · exact 0

omit [CompleteSpace E] [SigmaCompactSpace M] [T2Space M] [CompleteSpace E_U] [FiniteDimensional ℝ F]
    [CompleteSpace F] [ContMDiffVectorBundle ∞ F V I] in
private theorem homBundleCovariantDerivativeGenFun_apply
    (cov_U : CovariantDerivative I E_U U)
    (cov_V : CovariantDerivative I F V)
    (τ : Π x : M, (U x →L[ℝ] V x))
    {x : M} (hτ : MDiffAtHom I M E_U U F V τ x)
    {V_field : Π x : M, TangentSpace I x}
    {Y : Π x : M, U x}
    (hV : MDifferentiableAt I (I.prod 𝓘(ℝ, E))
      (fun y => TotalSpace.mk' E (E := TangentSpace I) y (V_field y)) x)
    (hY : MDiffAtU I M E_U U Y x) :
    homBundleCovariantDerivativeGenFun I M E_U U F V cov_U cov_V τ x (V_field x) (Y x) =
      Psi I M E_U U F V cov_U cov_V τ V_field Y x := by
  unfold homBundleCovariantDerivativeGenFun
  rw [dif_pos hτ]
  exact TensorialAt.mkHom₂_apply
    (Φ := fun V_field Y => Psi I M E_U U F V cov_U cov_V τ V_field Y x)
    (fun Y _ => Psi_tensorialAt_left I M E_U U F V cov_U cov_V τ Y)
    (fun V_field _ => Psi_tensorialAt_right I M E_U U F V cov_U cov_V τ hτ V_field) hV hY

omit [CompleteSpace E] [SigmaCompactSpace M] [T2Space M] [CompleteSpace E_U] [FiniteDimensional ℝ F]
    [CompleteSpace F] [ContMDiffVectorBundle ∞ F V I] in
private theorem homBundleCovariantDerivativeGenFun_of_not_mdiff
    (cov_U : CovariantDerivative I E_U U)
    (cov_V : CovariantDerivative I F V)
    (τ : Π x : M, (U x →L[ℝ] V x))
    {x : M} (hτ : ¬ MDiffAtHom I M E_U U F V τ x) :
    homBundleCovariantDerivativeGenFun I M E_U U F V cov_U cov_V τ x = 0 := by
  unfold homBundleCovariantDerivativeGenFun
  rw [dif_neg hτ]

omit [FiniteDimensional ℝ F] [CompleteSpace F] [ContMDiffVectorBundle ∞ F V I] in
omit [CompleteSpace E] [SigmaCompactSpace M] [CompleteSpace E_U] in
private theorem homBundleCovariantDerivativeGenFun_isCovOn
    (cov_U : CovariantDerivative I E_U U)
    (cov_V : CovariantDerivative I F V) :
    IsCovariantDerivativeOn (E_U →L[ℝ] F)
      (homBundleCovariantDerivativeGenFun I M E_U U F V cov_U cov_V) Set.univ where
  add := by
    intro τ₁ τ₂ x hτ₁ hτ₂ _hx
    have hτ₁' : MDiffAtHom I M E_U U F V τ₁ x := hτ₁
    have hτ₂' : MDiffAtHom I M E_U U F V τ₂ x := hτ₂
    have hτ_sum : MDiffAtHom I M E_U U F V (τ₁ + τ₂) x :=
      mdifferentiableAt_add_section (F := E_U →L[ℝ] F) hτ₁ hτ₂
    ext v w
    obtain ⟨V_field, hVx⟩ := ContMDiffSection.exists_eq_at (I := I) (F := E)
      (V := (TangentSpace I : M → Type _)) (n := (⊤ : ℕ∞)) x v
    obtain ⟨Y, hYx⟩ := ContMDiffSection.exists_eq_at (I := I) (F := E_U)
      (V := U) (n := (⊤ : ℕ∞)) x w
    have hV_diff := vec_section_mdiff I M V_field x
    have hY_diff := u_section_mdiff I M E_U U Y x
    rw [show (v : TangentSpace I x) = (V_field : Π x : M, TangentSpace I x) x from hVx.symm]
    rw [show (w : U x) = (Y : Π x : M, U x) x from hYx.symm]
    rw [add_apply, add_apply]
    rw [homBundleCovariantDerivativeGenFun_apply I M E_U U F V cov_U cov_V (τ₁ + τ₂)
      hτ_sum hV_diff hY_diff]
    rw [homBundleCovariantDerivativeGenFun_apply I M E_U U F V cov_U cov_V τ₁
      hτ₁' hV_diff hY_diff]
    rw [homBundleCovariantDerivativeGenFun_apply I M E_U U F V cov_U cov_V τ₂
      hτ₂' hV_diff hY_diff]
    have h_funeq : (fun y => (τ₁ + τ₂) y (Y y)) =
        (fun y => τ₁ y (Y y)) + (fun y => τ₂ y (Y y)) := by
      funext y
      simp [Pi.add_apply, add_apply]
    have hτ₁Y : MDiffAtV I M F V (fun y => τ₁ y (Y y)) x :=
      mdiffAt_apply I M E_U U F V hτ₁' hY_diff
    have hτ₂Y : MDiffAtV I M F V (fun y => τ₂ y (Y y)) x :=
      mdiffAt_apply I M E_U U F V hτ₂' hY_diff
    simp only [Psi]
    rw [h_funeq, cov_V.isCovariantDerivativeOn.add hτ₁Y hτ₂Y]
    simp only [add_apply, Pi.add_apply]
    abel
  leibniz := by
    intro τ g x hτ hg _hx
    have hτ' : MDiffAtHom I M E_U U F V τ x := hτ
    have hgτ : MDiffAtHom I M E_U U F V (g • τ) x :=
      hg.smul_section (F := E_U →L[ℝ] F) hτ
    ext v w
    obtain ⟨V_field, hVx⟩ := ContMDiffSection.exists_eq_at (I := I) (F := E)
      (V := (TangentSpace I : M → Type _)) (n := (⊤ : ℕ∞)) x v
    obtain ⟨Y, hYx⟩ := ContMDiffSection.exists_eq_at (I := I) (F := E_U)
      (V := U) (n := (⊤ : ℕ∞)) x w
    have hV_diff := vec_section_mdiff I M V_field x
    have hY_diff := u_section_mdiff I M E_U U Y x
    rw [show (v : TangentSpace I x) = (V_field : Π x : M, TangentSpace I x) x from hVx.symm]
    rw [show (w : U x) = (Y : Π x : M, U x) x from hYx.symm]
    rw [homBundleCovariantDerivativeGenFun_apply I M E_U U F V cov_U cov_V (g • τ)
      hgτ hV_diff hY_diff]
    simp only [add_apply, smul_apply,
      ContinuousLinearMap.smulRight_apply]
    rw [homBundleCovariantDerivativeGenFun_apply I M E_U U F V cov_U cov_V τ
      hτ' hV_diff hY_diff]
    have h_funeq : (fun y => (g • τ) y (Y y)) = g • (fun y => τ y (Y y)) := by
      funext y
      rfl
    have hτY : MDiffAtV I M F V (fun y => τ y (Y y)) x :=
      mdiffAt_apply I M E_U U F V hτ' hY_diff
    simp only [Psi]
    rw [h_funeq]
    rw [cov_V.isCovariantDerivativeOn.leibniz hτY hg]
    have hgτ_apply : (g • τ) x = g x • τ x := rfl
    rw [hgτ_apply]
    simp only [add_apply, smul_apply,
      ContinuousLinearMap.smulRight_apply]
    rw [smul_sub]
    abel

omit [SigmaCompactSpace M] in
noncomputable def homBundleCovariantDerivativeGen
    (cov_U : CovariantDerivative I E_U U)
    (cov_V : CovariantDerivative I F V) :
    CovariantDerivative I (E_U →L[ℝ] F)
      (fun x => U x →L[ℝ] V x) where
  toFun := homBundleCovariantDerivativeGenFun I M E_U U F V cov_U cov_V
  isCovariantDerivativeOnUniv :=
    homBundleCovariantDerivativeGenFun_isCovOn I M E_U U F V cov_U cov_V

omit [FiniteDimensional ℝ F] [CompleteSpace F] [ContMDiffVectorBundle ∞ F V I] in
omit [CompleteSpace E] [SigmaCompactSpace M] [CompleteSpace E_U] in
theorem homBundleCovariantDerivativeGen_apply_of_mdifferentiableAt
    (cov_U : CovariantDerivative I E_U U)
    (cov_V : CovariantDerivative I F V)
    (τ : Π x : M, (U x →L[ℝ] V x))
    {x : M}
    (hτ : MDifferentiableAt I (I.prod 𝓘(ℝ, E_U →L[ℝ] F))
      (fun y : M => TotalSpace.mk' (E_U →L[ℝ] F)
        (E := fun x : M => (U x →L[ℝ] V x)) y (τ y)) x)
    {V_field : Π x : M, TangentSpace I x}
    {Y : Π x : M, U x}
    (hV : MDifferentiableAt I (I.prod 𝓘(ℝ, E))
      (fun y => TotalSpace.mk' E (E := TangentSpace I) y (V_field y)) x)
    (hY : MDifferentiableAt I (I.prod 𝓘(ℝ, E_U))
      (fun y => TotalSpace.mk' E_U (E := U) y (Y y)) x) :
    (homBundleCovariantDerivativeGen I M E_U U F V cov_U cov_V τ x (V_field x)) (Y x) =
      cov_V (fun y => τ y (Y y)) x (V_field x) - τ x (cov_U Y x (V_field x)) := by
  change homBundleCovariantDerivativeGenFun I M E_U U F V cov_U cov_V τ x
      (V_field x) (Y x) = _
  exact homBundleCovariantDerivativeGenFun_apply I M E_U U F V cov_U cov_V τ
    hτ hV hY

omit [FiniteDimensional ℝ E] [CompleteSpace E] [IsManifold I ∞ M] [SigmaCompactSpace M] [T2Space M]
    [FiniteDimensional ℝ E_U] [CompleteSpace E_U] [∀ (x : M), IsTopologicalAddGroup (U x)]
    [∀ (x : M), ContinuousSMul ℝ (U x)] [ContMDiffVectorBundle ∞ E_U U I] [FiniteDimensional ℝ F]
    [CompleteSpace F] [ContMDiffVectorBundle ∞ F V I] in
private theorem contMDiff_hom_apply_section
    (τ : Cₛ^∞⟮I; E_U →L[ℝ] F, (fun x => U x →L[ℝ] V x)⟯)
    (Y : Cₛ^∞⟮I; E_U, U⟯) :
    ContMDiff I (I.prod 𝓘(ℝ, F)) ∞
      (fun y => TotalSpace.mk' F (E := V) y (τ y (Y y))) :=
  ContMDiff.clm_bundle_apply (b := id) τ.contMDiff Y.contMDiff

omit [FiniteDimensional ℝ E] [CompleteSpace E] [SigmaCompactSpace M] [T2Space M]
    [FiniteDimensional ℝ E_U] [CompleteSpace E_U] [ContMDiffVectorBundle ∞ E_U U I] in
private theorem contMDiff_cov_U_apply_section
    (cov_U : CovariantDerivative I E_U U)
    [ContMDiffCovariantDerivative cov_U ∞]
    (Y : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯)
    (Z : Cₛ^∞⟮I; E_U, U⟯) :
    ContMDiff I (I.prod 𝓘(ℝ, E_U)) ∞
      (fun x => TotalSpace.mk' E_U (E := U) x (cov_U Z x (Y x))) := by
  have hZ_plus : ContMDiff I (I.prod 𝓘(ℝ, E_U)) (∞ + 1) (T% fun x => Z x) := by
    rw [show (∞ : WithTop ℕ∞) + 1 = ∞ from by simp]
    exact Z.contMDiff
  have hcov_U_smooth :=
    (‹ContMDiffCovariantDerivative cov_U ∞›).contMDiff.contMDiff hZ_plus.contMDiffOn
  have hcov_U_global : ContMDiff I (I.prod 𝓘(ℝ, E →L[ℝ] E_U)) ∞
      (fun x => TotalSpace.mk' (E →L[ℝ] E_U)
        (E := fun x : M => TangentSpace I x →L[ℝ] U x) x (cov_U Z x)) := by
    rwa [← contMDiffOn_univ]
  exact ContMDiff.clm_bundle_apply (b := id) hcov_U_global Y.contMDiff

omit [CompleteSpace F] in
omit [CompleteSpace E] [SigmaCompactSpace M] [CompleteSpace E_U] in
omit [FiniteDimensional ℝ F] [ContMDiffVectorBundle ∞ F V I] in
private theorem homBundleCovGen_section_smooth
    (cov_U : CovariantDerivative I E_U U)
    [ContMDiffCovariantDerivative cov_U ∞]
    (cov_V : CovariantDerivative I F V)
    [ContMDiffCovariantDerivative cov_V ∞]
    (τ : Cₛ^∞⟮I; E_U →L[ℝ] F, (fun x => U x →L[ℝ] V x)⟯)
    (Y : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) :
    ContMDiff I (I.prod 𝓘(ℝ, E_U →L[ℝ] F)) ∞
      (fun x => TotalSpace.mk' (E_U →L[ℝ] F)
        (E := fun x : M => (U x →L[ℝ] V x))
        x ((homBundleCovariantDerivativeGenFun I M E_U U F V cov_U cov_V τ x) (Y x))) := by
  apply contMDiff_clm_section_of_pointwise (I := I) (M := M)
    (V₁ := U) (V₂ := V)
    (φ := fun x => (homBundleCovariantDerivativeGenFun I M E_U U F V cov_U cov_V τ x) (Y x))
  intro Z
  have hτZ_section : ContMDiff I (I.prod 𝓘(ℝ, F)) ∞
      (fun y => TotalSpace.mk' F (E := V) y (τ y (Z y))) :=
    contMDiff_hom_apply_section I M E_U U F V τ Z
  let τZ : Cₛ^∞⟮I; F, V⟯ := ⟨fun y => τ y (Z y), hτZ_section⟩
  have hcov_V_τZ : ContMDiff I (I.prod 𝓘(ℝ, E →L[ℝ] F)) ∞
      (fun x => TotalSpace.mk' (E →L[ℝ] F)
        (E := fun x : M => (TangentSpace I x →L[ℝ] V x)) x (cov_V τZ x)) := by
    have hτZ_plus : ContMDiff I (I.prod 𝓘(ℝ, F)) (∞ + 1) (T% fun x => τZ x) := by
      rw [show (∞ : WithTop ℕ∞) + 1 = ∞ from by simp]
      exact τZ.contMDiff
    have hcov_V_smooth :=
      (‹ContMDiffCovariantDerivative cov_V ∞›).contMDiff.contMDiff hτZ_plus.contMDiffOn
    rwa [← contMDiffOn_univ]
  have h_first : ContMDiff I (I.prod 𝓘(ℝ, F)) ∞
      (fun x => TotalSpace.mk' F (E := V) x (cov_V τZ x (Y x))) :=
    ContMDiff.clm_bundle_apply (b := id) hcov_V_τZ Y.contMDiff
  have h_covUZY : ContMDiff I (I.prod 𝓘(ℝ, E_U)) ∞
      (fun x => TotalSpace.mk' E_U (E := U) x (cov_U Z x (Y x))) :=
    contMDiff_cov_U_apply_section I M E_U U cov_U Y Z
  have h_second : ContMDiff I (I.prod 𝓘(ℝ, F)) ∞
      (fun x => TotalSpace.mk' F (E := V) x (τ x (cov_U Z x (Y x)))) :=
    ContMDiff.clm_bundle_apply (b := id) τ.contMDiff h_covUZY
  have h_eq : ∀ x,
      (homBundleCovariantDerivativeGenFun I M E_U U F V cov_U cov_V τ x) (Y x) (Z x) =
      cov_V τZ x (Y x) - τ x (cov_U Z x (Y x)) := by
    intro x
    have hτ_diff := hom_section_mdiff I M E_U U F V τ x
    have hY_diff := vec_section_mdiff I M Y x
    have hZ_diff := u_section_mdiff I M E_U U Z x
    rw [homBundleCovariantDerivativeGenFun_apply I M E_U U F V cov_U cov_V τ
      hτ_diff hY_diff hZ_diff]
    rfl
  have h_diff : ContMDiff I (I.prod 𝓘(ℝ, F)) ∞
      (fun x => TotalSpace.mk' F (E := V) x
        (cov_V τZ x (Y x) - τ x (cov_U Z x (Y x)))) := by
    let s₁ : Cₛ^∞⟮I; F, V⟯ := ⟨fun x => cov_V τZ x (Y x), h_first⟩
    let s₂ : Cₛ^∞⟮I; F, V⟯ := ⟨fun x => τ x (cov_U Z x (Y x)), h_second⟩
    have : ContMDiff I (I.prod 𝓘(ℝ, F)) ∞
        (fun x => TotalSpace.mk' F (E := V) x ((s₁ - s₂) x)) := (s₁ - s₂).contMDiff
    exact this.congr fun x => by
      change TotalSpace.mk' F (E := V) x
        (cov_V τZ x (Y x) - τ x (cov_U Z x (Y x))) =
          TotalSpace.mk' F (E := V) x (s₁ x - s₂ x)
      rfl
  intro x₀
  rw [contMDiffAt_section]
  have h_diff_at := h_diff x₀
  rw [contMDiffAt_section] at h_diff_at
  refine h_diff_at.congr_of_eventuallyEq ?_
  filter_upwards with x
  rw [h_eq]

noncomputable instance homBundleCovariantDerivativeGen_contMDiff
    (cov_U : CovariantDerivative I E_U U)
    [ContMDiffCovariantDerivative cov_U ∞]
    (cov_V : CovariantDerivative I F V)
    [ContMDiffCovariantDerivative cov_V ∞] :
    ContMDiffCovariantDerivative
      (homBundleCovariantDerivativeGen I M E_U U F V cov_U cov_V) ∞ where
  contMDiff := {
    contMDiff := by
      intro τ hτ
      have hτ_smooth : ContMDiff I (I.prod 𝓘(ℝ, E_U →L[ℝ] F)) ∞
          (fun x => TotalSpace.mk' (E_U →L[ℝ] F)
            (E := fun x : M => (U x →L[ℝ] V x)) x (τ x)) := by
        rw [show (∞ : WithTop ℕ∞) = ∞ + 1 from by simp] at hτ
        rwa [← contMDiffOn_univ]
      let τ_section : Cₛ^∞⟮I; E_U →L[ℝ] F, (fun x => U x →L[ℝ] V x)⟯ :=
        ⟨τ, hτ_smooth⟩
      rw [contMDiffOn_univ]
      apply contMDiff_clm_section_of_pointwise (I := I) (M := M)
        (V₁ := TangentSpace I)
        (V₂ := fun x => U x →L[ℝ] V x)
        (φ := fun x => homBundleCovariantDerivativeGenFun I M E_U U F V cov_U cov_V τ x)
      intro Y
      exact homBundleCovGen_section_smooth I M E_U U F V cov_U cov_V τ_section Y
  }

omit [FiniteDimensional ℝ F] [CompleteSpace F] [ContMDiffVectorBundle ∞ F V I] in
omit [CompleteSpace E] [SigmaCompactSpace M] [CompleteSpace E_U] in
theorem homBundleCovariantDerivativeGen_apply
    (cov_U : CovariantDerivative I E_U U)
    (cov_V : CovariantDerivative I F V)
    (τ : Cₛ^∞⟮I; E_U →L[ℝ] F, (fun x => U x →L[ℝ] V x)⟯)
    (Y : Cₛ^∞⟮I; E_U, U⟯) (x : M) (v : TangentSpace I x) :
    (homBundleCovariantDerivativeGen I M E_U U F V cov_U cov_V τ x v) (Y x) =
      cov_V (fun y => τ y (Y y)) x v - τ x (cov_U Y x v) := by
  change homBundleCovariantDerivativeGenFun I M E_U U F V cov_U cov_V τ x v (Y x) = _
  obtain ⟨V_field, hVx⟩ := ContMDiffSection.exists_eq_at (I := I) (F := E)
    (V := (TangentSpace I : M → Type _)) (n := (⊤ : ℕ∞)) x v
  have hτ_diff := hom_section_mdiff I M E_U U F V τ x
  have hV_diff := vec_section_mdiff I M V_field x
  have hY_diff := u_section_mdiff I M E_U U Y x
  rw [show v = (V_field : Π x : M, TangentSpace I x) x from hVx.symm]
  rw [homBundleCovariantDerivativeGenFun_apply I M E_U U F V cov_U cov_V τ
    hτ_diff hV_diff hY_diff]
  rfl

end HomConnectionGen

namespace HomConnectionGen

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M] [T2Space M]
variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
  [FiniteDimensional ℝ F]
variable {V : M → Type*} [TopologicalSpace (TotalSpace F V)]
  [∀ x, NormedAddCommGroup (V x)] [∀ x, InnerProductSpace ℝ (V x)]
  [FiberBundle F V] [VectorBundle ℝ F V]
  [ContMDiffVectorBundle ∞ F V I]
  [IsContMDiffRiemannianBundle I 1 F V]

omit [IsContMDiffRiemannianBundle I 1 F V] in
theorem homBundleCovariantDerivativeGen_apply_of_eventually_mem_ker
    (cov : CovariantDerivative I F V)
    (A : Cₛ^∞⟮I; F →L[ℝ] F, (fun x : M => V x →L[ℝ] V x)⟯)
    (w : Cₛ^∞⟮I; F, V⟯) {x : M} {U : Set M}
    (hU : IsOpen U) (hxU : x ∈ U) (hw : ∀ y ∈ U, A y (w y) = 0)
    (v : TangentSpace I x) :
    (homBundleCovariantDerivativeGen I M F V F V cov cov A x v) (w x) =
      -A x (cov w x v) := by
  let Aw : Cₛ^∞⟮I; F, V⟯ :=
    ⟨fun y => A y (w y),
      ContMDiff.clm_bundle_apply (b := id) A.contMDiff w.contMDiff⟩
  have hcovAw : cov (fun y => Aw y) x = 0 := by
    have hzeroDiff : MDiffAt (T% fun y : M => (0 : V y)) x :=
      mdifferentiableAt_zeroSection (𝕜 := ℝ) (F := F) (E := V) (IB := I)
    have hEq : ∀ᶠ y in 𝓝 x, Aw y = (0 : V y) :=
      Filter.eventually_of_mem (hU.mem_nhds hxU) hw
    have hcovEq := cov.isCovariantDerivativeOnUniv.congr_of_eventuallyEq
      Aw.mdifferentiableAt hzeroDiff Filter.univ_mem hEq
    rw [hcovEq]
    exact congrArg (fun phi => phi x) cov.zero
  have happly := homBundleCovariantDerivativeGen_apply
    I M F V F V cov cov A w x v
  change
    (homBundleCovariantDerivativeGen I M F V F V cov cov
        (fun y => A y) x v) (w x) =
      cov (fun y => Aw y) x v - A x (cov (fun y => w y) x v) at happly
  rw [hcovAw] at happly
  simpa using happly

omit [IsContMDiffRiemannianBundle I 1 F V] in
theorem inner_homBundleCovariantDerivativeGen_apply_of_eventually_mem_ker
    (cov : CovariantDerivative I F V)
    (A : Cₛ^∞⟮I; F →L[ℝ] F, (fun x : M => V x →L[ℝ] V x)⟯)
    (hA : ∀ y, (A y : V y →ₗ[ℝ] V y).IsSymmetric)
    (w : Cₛ^∞⟮I; F, V⟯) {x : M} {U : Set M}
    (hU : IsOpen U) (hxU : x ∈ U) (hw : ∀ y ∈ U, A y (w y) = 0)
    (v : TangentSpace I x) :
    inner ℝ
      ((homBundleCovariantDerivativeGen I M F V F V cov cov A x v) (w x))
      (w x) = 0 := by
  rw [homBundleCovariantDerivativeGen_apply_of_eventually_mem_ker
    cov A w hU hxU hw v, inner_neg_left]
  have hswap :
      inner ℝ (A x (cov w x v)) (w x) =
        inner ℝ (cov w x v) (A x (w x)) := hA x _ _
  rw [hswap]
  rw [hw x hxU, inner_zero_right, neg_zero]

theorem homBundleCovariantDerivativeGen_isSymmetric
    (cov : CovariantDerivative I F V) (hcov : cov.IsMetricCompatible)
    (A : Cₛ^∞⟮I; F →L[ℝ] F, (fun x : M => V x →L[ℝ] V x)⟯)
    (hA : ∀ y, (A y : V y →ₗ[ℝ] V y).IsSymmetric)
    (x : M) (v : TangentSpace I x) :
    ((homBundleCovariantDerivativeGen I M F V F V cov cov A x v :
      V x →L[ℝ] V x) : V x →ₗ[ℝ] V x).IsSymmetric := by
  intro a b
  obtain ⟨X, hXx⟩ := ContMDiffSection.exists_eq_at
    (I := I) (F := E) (V := TangentSpace I) (n := (⊤ : ℕ∞)) x v
  obtain ⟨Y, hYx⟩ := ContMDiffSection.exists_eq_at
    (I := I) (F := F) (V := V) (n := (⊤ : ℕ∞)) x a
  obtain ⟨Z, hZx⟩ := ContMDiffSection.exists_eq_at
    (I := I) (F := F) (V := V) (n := (⊤ : ℕ∞)) x b
  let AY : Cₛ^∞⟮I; F, V⟯ :=
    ⟨fun y => A y (Y y),
      ContMDiff.clm_bundle_apply (b := id) A.contMDiff Y.contMDiff⟩
  let AZ : Cₛ^∞⟮I; F, V⟯ :=
    ⟨fun y => A y (Z y),
      ContMDiff.clm_bundle_apply (b := id) A.contMDiff Z.contMDiff⟩
  have hfun :
      (fun y : M => inner ℝ (AY y) (Z y)) =
        (fun y : M => inner ℝ (Y y) (AZ y)) := by
    funext y
    exact hA y (Y y) (Z y)
  have hderiv :
      d% (fun y : M => inner ℝ (AY y) (Z y)) x (X x) =
        d% (fun y : M => inner ℝ (Y y) (AZ y)) x (X x) := by
    rw [hfun]
  have hleft := hcov.mvfderiv_inner_eq (x := x) (fun y => X y)
    AY.mdifferentiableAt Z.mdifferentiableAt
  have hright := hcov.mvfderiv_inner_eq (x := x) (fun y => X y)
    Y.mdifferentiableAt AZ.mdifferentiableAt
  rw [hleft, hright] at hderiv
  rw [← hXx, ← hYx, ← hZx]
  have hDY := homBundleCovariantDerivativeGen_apply
    I M F V F V cov cov A Y x (X x)
  have hDZ := homBundleCovariantDerivativeGen_apply
    I M F V F V cov cov A Z x (X x)
  have hcovY :
      inner ℝ (A x (cov Y x (X x))) (Z x) =
        inner ℝ (cov Y x (X x)) (A x (Z x)) :=
    hA x _ _
  have hcovZ :
      inner ℝ (A x (Y x)) (cov Z x (X x)) =
        inner ℝ (Y x) (A x (cov Z x (X x))) :=
    hA x _ _
  change
    inner ℝ (cov (fun y => A y (Y y)) x (X x)) (Z x) +
        inner ℝ (A x (Y x)) (cov Z x (X x)) =
      inner ℝ (cov Y x (X x)) (A x (Z x)) +
        inner ℝ (Y x) (cov (fun y => A y (Z y)) x (X x)) at hderiv
  rw [hcovZ, ← hcovY] at hderiv
  calc
    inner ℝ
        ((homBundleCovariantDerivativeGen I M F V F V cov cov A x (X x)) (Y x))
        (Z x) =
        inner ℝ
          (cov (fun y => A y (Y y)) x (X x) - A x (cov Y x (X x)))
          (Z x) := congrArg (fun q : V x => inner ℝ q (Z x)) hDY
    _ = inner ℝ (Y x)
        (cov (fun y => A y (Z y)) x (X x) - A x (cov Z x (X x))) := by
      simp only [inner_sub_left, inner_sub_right]
      linear_combination hderiv
    _ = inner ℝ (Y x)
        ((homBundleCovariantDerivativeGen I M F V F V cov cov A x (X x))
          (Z x)) := congrArg (fun q : V x => inner ℝ (Y x) q) hDZ.symm

end HomConnectionGen

end DifferentialGeometry
end

noncomputable section

open Bundle
open scoped Manifold ContDiff

namespace DifferentialGeometry.HomConnectionGen

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M] [T2Space M]
  {F₁ F₂ F₃ : Type*}
  [NormedAddCommGroup F₁] [NormedSpace ℝ F₁] [FiniteDimensional ℝ F₁]
  [NormedAddCommGroup F₂] [NormedSpace ℝ F₂] [FiniteDimensional ℝ F₂]
  [NormedAddCommGroup F₃] [NormedSpace ℝ F₃]
  {V₁ : M → Type*} [TopologicalSpace (TotalSpace F₁ V₁)]
  [∀ x, AddCommGroup (V₁ x)] [∀ x, Module ℝ (V₁ x)]
  [∀ x, TopologicalSpace (V₁ x)] [∀ x, IsTopologicalAddGroup (V₁ x)]
  [∀ x, ContinuousSMul ℝ (V₁ x)]
  [FiberBundle F₁ V₁] [VectorBundle ℝ F₁ V₁] [ContMDiffVectorBundle ∞ F₁ V₁ I]
  {V₂ : M → Type*} [TopologicalSpace (TotalSpace F₂ V₂)]
  [∀ x, AddCommGroup (V₂ x)] [∀ x, Module ℝ (V₂ x)]
  [∀ x, TopologicalSpace (V₂ x)] [∀ x, IsTopologicalAddGroup (V₂ x)]
  [∀ x, ContinuousSMul ℝ (V₂ x)]
  [FiberBundle F₂ V₂] [VectorBundle ℝ F₂ V₂] [ContMDiffVectorBundle ∞ F₂ V₂ I]
  {V₃ : M → Type*} [TopologicalSpace (TotalSpace F₃ V₃)]
  [∀ x, AddCommGroup (V₃ x)] [∀ x, Module ℝ (V₃ x)]
  [∀ x, TopologicalSpace (V₃ x)] [∀ x, IsTopologicalAddGroup (V₃ x)]
  [∀ x, ContinuousSMul ℝ (V₃ x)]
  [FiberBundle F₃ V₃] [VectorBundle ℝ F₃ V₃]

theorem homBundleCovariantDerivativeGen_comp
    (cov₁ : CovariantDerivative I F₁ V₁)
    (cov₂ : CovariantDerivative I F₂ V₂)
    (cov₃ : CovariantDerivative I F₃ V₃)
    {φ : ∀ x, V₁ x →L[ℝ] V₂ x} {ψ : ∀ x, V₂ x →L[ℝ] V₃ x} {x : M}
    (hφ : MDifferentiableAt I (I.prod 𝓘(ℝ, F₁ →L[ℝ] F₂))
      (fun y => (⟨y, φ y⟩ : TotalSpace (F₁ →L[ℝ] F₂)
        (fun y => V₁ y →L[ℝ] V₂ y))) x)
    (hψ : MDifferentiableAt I (I.prod 𝓘(ℝ, F₂ →L[ℝ] F₃))
      (fun y => (⟨y, ψ y⟩ : TotalSpace (F₂ →L[ℝ] F₃)
        (fun y => V₂ y →L[ℝ] V₃ y))) x)
    (v : TangentSpace I x) :
    homBundleCovariantDerivativeGen I M F₁ V₁ F₃ V₃ cov₁ cov₃
        (fun y => (ψ y).comp (φ y)) x v =
      (homBundleCovariantDerivativeGen I M F₂ V₂ F₃ V₃ cov₂ cov₃ ψ x v).comp (φ x) +
        (ψ x).comp (homBundleCovariantDerivativeGen I M F₁ V₁ F₂ V₂ cov₁ cov₂ φ x v) := by
  ext w
  obtain ⟨X, hX⟩ := ContMDiffSection.exists_eq_at (I := I) (F := E)
    (V := TangentSpace I) (n := (⊤ : ℕ∞)) x v
  obtain ⟨Y, hY⟩ := ContMDiffSection.exists_eq_at (I := I) (F := F₁)
    (V := V₁) (n := (⊤ : ℕ∞)) x w
  rw [← hX, ← hY]
  simp only [add_apply, ContinuousLinearMap.comp_apply]
  rw [homBundleCovariantDerivativeGen_apply_of_mdifferentiableAt I M F₁ V₁ F₃ V₃
    cov₁ cov₃ _ (hψ.clm_bundle_comp hφ) X.mdifferentiableAt Y.mdifferentiableAt]
  rw [homBundleCovariantDerivativeGen_apply_of_mdifferentiableAt I M F₂ V₂ F₃ V₃
    cov₂ cov₃ _ hψ X.mdifferentiableAt (hφ.clm_bundle_apply Y.mdifferentiableAt)]
  rw [homBundleCovariantDerivativeGen_apply_of_mdifferentiableAt I M F₁ V₁ F₂ V₂
    cov₁ cov₂ _ hφ X.mdifferentiableAt Y.mdifferentiableAt]
  simp only [ContinuousLinearMap.comp_apply, map_sub]
  abel

end DifferentialGeometry.HomConnectionGen
