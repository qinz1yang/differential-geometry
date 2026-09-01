import DifferentialGeometry.Bundle.Section
import DifferentialGeometry.Bundle.TangentSpace
import Mathlib.Geometry.Manifold.VectorBundle.CovariantDerivative.Basic

set_option autoImplicit false

noncomputable section

open Bundle Filter
open scoped Manifold ContDiff Topology BigOperators

namespace DifferentialGeometry.Geometry.Connection

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M] [T2Space M]
variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
  [FiniteDimensional ℝ F]
variable {V : M → Type*} [∀ x, AddCommGroup (V x)] [∀ x, Module ℝ (V x)]
  [∀ x, TopologicalSpace (V x)] [∀ x, IsTopologicalAddGroup (V x)]
  [∀ x, ContinuousSMul ℝ (V x)] [TopologicalSpace (TotalSpace F V)]
  [FiberBundle F V] [VectorBundle ℝ F V] [ContMDiffVectorBundle ∞ F V I]

omit [FiniteDimensional ℝ E] [IsManifold I ∞ M] [T2Space M]
  [FiniteDimensional ℝ F] [ContMDiffVectorBundle ∞ F V I] in
private theorem covariantDerivative_finset_sum
    {J : Type*} (cov : CovariantDerivative I F V) (s : Finset J)
    (A : J → (x : M) → V x) {x : M}
    (hA : ∀ j, MDiffAt (T% (A j)) x) :
    cov (fun y ↦ ∑ j ∈ s, A j y) x = ∑ j ∈ s, cov (A j) x := by
  classical
  induction s using Finset.induction_on with
  | empty =>
      change cov (0 : (y : M) → V y) x = 0
      exact cov.isCovariantDerivativeOnUniv.zero
  | @insert j s hj ih =>
      have hsum : MDiffAt (T% (fun y ↦ ∑ k ∈ s, A k y)) x :=
        MDifferentiableAt.sum_section fun k hk ↦ hA k
      have hfun :
          (fun y ↦ ∑ k ∈ insert j s, A k y) = A j + fun y ↦ ∑ k ∈ s, A k y := by
        funext y
        simp [Finset.sum_insert, hj]
      rw [hfun, cov.isCovariantDerivativeOnUniv.add (hA j) hsum, ih]
      simp [Finset.sum_insert, hj]

private theorem exists_section_with_value_zero_and_covariantDerivative
    (cov : CovariantDerivative I F V) (x : M)
    (L : TangentSpace I x →L[ℝ] V x) :
    ∃ σ : Cₛ^∞⟮I; F, V⟯, σ x = 0 ∧ cov σ x = L := by
  classical
  let e := trivializationAt F V x
  let b := Module.finBasis ℝ F
  have he : x ∈ e.baseSet := mem_baseSet_trivializationAt F V x
  let P : E →L[ℝ] F := (e.continuousLinearMapAt ℝ x).comp L
  let q : Fin (Module.finrank ℝ F) → E →L[ℝ] ℝ :=
    fun i ↦ (LinearMap.toContinuousLinearMap (b.coord i)).comp P
  let f : Fin (Module.finrank ℝ F) → M → ℝ :=
    fun i y ↦ q i (extChartAt I x y) - q i (extChartAt I x x)
  let χ : SmoothBumpFunction I x := Classical.arbitrary (SmoothBumpFunction I x)
  let ψ : Fin (Module.finrank ℝ F) → M → ℝ :=
    fun i y ↦ χ y * f i y
  have hf_smooth (i : Fin (Module.finrank ℝ F)) :
      ContMDiffOn I (modelWithCornersSelf ℝ ℝ) ∞ (f i) (chartAt H x).source := by
    have hcomp :
        ContMDiffOn I (modelWithCornersSelf ℝ ℝ) ∞
          (q i ∘ extChartAt I x) (chartAt H x).source :=
      (q i).contMDiff.comp_contMDiffOn contMDiffOn_extChartAt
    simpa only [f, Function.comp_apply] using
      ContMDiffOn.sub_const (q i (extChartAt I x x)) hcomp
  have hψ_smooth (i : Fin (Module.finrank ℝ F)) :
      ContMDiff I (modelWithCornersSelf ℝ ℝ) ∞ (ψ i) := by
    simpa only [ψ, smul_eq_mul] using χ.contMDiff_smul (hf_smooth i)
  have hψ_value (i : Fin (Module.finrank ℝ F)) : ψ i x = 0 := by
    simp [ψ, f]
  have hf_deriv_apply (i : Fin (Module.finrank ℝ F)) (u : TangentSpace I x) :
      mvfderiv I (f i) x u =
        q i (tangentSpaceModelContinuousLinearEquiv (I := I) x u) := by
    have hchart : MDiffAt (extChartAt I x) x :=
      mdifferentiableAt_extChartAt (I := I) (mem_chart_source H x)
    have hq : MDiffAt (q i) (extChartAt I x x) :=
      (q i).mdifferentiableAt
    have hcomp :
        mvfderiv I (q i ∘ extChartAt I x) x u =
          mvfderiv (modelWithCornersSelf ℝ E) (q i) (extChartAt I x x)
            (mfderiv I (modelWithCornersSelf ℝ E) (extChartAt I x) x u) :=
      mvfderiv_comp_apply x hq hchart u
    rw [show f i = (q i ∘ extChartAt I x) - fun _ ↦ q i (extChartAt I x x) from rfl,
      mvfderiv_sub (hq.comp x hchart) mdifferentiableAt_const,
      mvfderiv_const, sub_zero, hcomp,
      mvfderiv_model_apply_eq_fderiv]
    have hchart_deriv :
        tangentSpaceModelContinuousLinearEquiv
            (I := modelWithCornersSelf ℝ E) (extChartAt I x x)
            (mfderiv I (modelWithCornersSelf ℝ E) (extChartAt I x) x u) =
          tangentSpaceModelContinuousLinearEquiv (I := I) x u := by
      rw [mfderiv_extChartAt_self]
      rfl
    rw [hchart_deriv]
    rw [(q i).fderiv]
  have hψ_deriv_apply (i : Fin (Module.finrank ℝ F)) (u : TangentSpace I x) :
      mvfderiv I (ψ i) x u =
        q i (tangentSpaceModelContinuousLinearEquiv (I := I) x u) := by
    have hev : ψ i =ᶠ[nhds x] f i := by
      filter_upwards [χ.eventuallyEq_one] with y hy
      simp [ψ, hy]
    unfold mvfderiv
    rw [hev.mfderiv_eq, show ψ i x = f i x from hev.eq_of_nhds]
    exact hf_deriv_apply i u
  choose Y hY using fun i : Fin (Module.finrank ℝ F) ↦
    ContMDiffSection.exists_eq_at (I := I) (F := F) (V := V) (n := (⊤ : ℕ∞)) x
      (e.symmL ℝ x (b i))
  let C : (y : M) → V y := fun y ↦ ∑ i, ψ i y • Y i y
  have hC_smooth : ContMDiff I (I.prod (modelWithCornersSelf ℝ F)) ∞ (T% C) := by
    exact ContMDiff.sum_section fun i _ ↦ (hψ_smooth i).smul_section (Y i).contMDiff
  let σ : Cₛ^∞⟮I; F, V⟯ := ⟨C, hC_smooth⟩
  refine ⟨σ, ?_, ?_⟩
  · simp [σ, C, hψ_value]
  · apply ContinuousLinearMap.ext
    intro u
    have hterm (i : Fin (Module.finrank ℝ F)) :
        cov (fun y ↦ ψ i y • Y i y) x u =
          mvfderiv I (ψ i) x u • Y i x := by
      have hYdiff : MDiffAt (T% (fun y : M ↦ Y i y)) x :=
        (Y i).contMDiff.mdifferentiableAt (by simp)
      have hψdiff : MDifferentiableAt I (modelWithCornersSelf ℝ ℝ) (ψ i) x :=
        (hψ_smooth i).mdifferentiableAt (by simp)
      have hleibniz := cov.isCovariantDerivativeOnUniv.leibniz
        (σ := fun y : M ↦ Y i y) (g := ψ i) hYdiff hψdiff
      have happ := congrArg (fun D ↦ D u) hleibniz
      change (cov ((ψ i) • fun y : M ↦ Y i y) x) u = _
      simpa only [Pi.smul_apply, add_apply, ContinuousLinearMap.smulRight_apply,
        hψ_value, zero_smul, zero_add] using happ
    rw [show (cov σ x) u = cov C x u from rfl]
    rw [covariantDerivative_finset_sum cov Finset.univ
      (fun i y ↦ ψ i y • Y i y)
      (fun i ↦ (hψ_smooth i).mdifferentiableAt (by simp) |>.smul_section
        ((Y i).contMDiff.mdifferentiableAt (by simp)))]
    simp_rw [sum_apply, hterm, hY]
    simp_rw [hψ_deriv_apply]
    change
      (∑ i, (b.repr (P (tangentSpaceModelContinuousLinearEquiv (I := I) x u))) i •
        e.symmL ℝ x (b i)) = L u
    calc
      (∑ i, (b.repr (P (tangentSpaceModelContinuousLinearEquiv (I := I) x u))) i •
          e.symmL ℝ x (b i)) =
          ∑ i, e.symmL ℝ x
            ((b.repr (P (tangentSpaceModelContinuousLinearEquiv (I := I) x u))) i • b i) := by
        apply Finset.sum_congr rfl
        intro i hi
        rw [map_smul]
      _ = e.symmL ℝ x
          (∑ i, (b.repr (P (tangentSpaceModelContinuousLinearEquiv (I := I) x u))) i • b i) := by
        rw [map_sum]
      _ = e.symmL ℝ x
          (P (tangentSpaceModelContinuousLinearEquiv (I := I) x u)) := by
        rw [b.sum_repr]
      _ = L u := by
        change e.symmL ℝ x ((e.continuousLinearMapAt ℝ x) (L u)) = L u
        exact e.symmL_continuousLinearMapAt he (L u)

theorem exists_section_with_value_and_covariantDerivative
    (cov : CovariantDerivative I F V) (x : M) (v : V x)
    (L : TangentSpace I x →L[ℝ] V x) :
    ∃ σ : Cₛ^∞⟮I; F, V⟯, σ x = v ∧ cov σ x = L := by
  obtain ⟨σ₀, hσ₀⟩ :=
    ContMDiffSection.exists_eq_at (I := I) (F := F) (V := V) (n := (⊤ : ℕ∞)) x v
  obtain ⟨τ, hτ₀, hτcov⟩ :=
    exists_section_with_value_zero_and_covariantDerivative cov x (L - cov σ₀ x)
  refine ⟨σ₀ + τ, ?_, ?_⟩
  · simp [hσ₀, hτ₀]
  · change cov ((σ₀ : (y : M) → V y) + (τ : (y : M) → V y)) x = L
    have hσ₀diff : MDiffAt (T% (fun y : M ↦ σ₀ y)) x :=
      σ₀.contMDiff.mdifferentiableAt (by simp)
    have hτdiff : MDiffAt (T% (fun y : M ↦ τ y)) x :=
      τ.contMDiff.mdifferentiableAt (by simp)
    rw [cov.isCovariantDerivativeOnUniv.add hσ₀diff hτdiff]
    rw [hτcov, add_sub_cancel]

theorem exists_section_with_value_and_covariantDerivative_zero
    (cov : CovariantDerivative I F V) (x : M) (v : V x) :
    ∃ σ : Cₛ^∞⟮I; F, V⟯, σ x = v ∧ cov σ x = 0 :=
  exists_section_with_value_and_covariantDerivative cov x v 0

end DifferentialGeometry.Geometry.Connection
