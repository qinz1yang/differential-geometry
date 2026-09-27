import DifferentialGeometry.Bundle.Section
import DifferentialGeometry.Bundle.TangentSpace
import Mathlib.Geometry.Manifold.VectorBundle.CovariantDerivative.Basic
import Mathlib.Geometry.Manifold.VectorBundle.CovariantDerivative.Metric
import Mathlib.Analysis.SpecialFunctions.Sqrt

set_option autoImplicit false

noncomputable section

open Bundle Filter
open scoped Manifold ContDiff Topology BigOperators

namespace DifferentialGeometry.Geometry.Connection

open Set
open scoped InnerProductSpace

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

namespace DifferentialGeometry.Geometry.Connection

open Bundle Filter Set
open scoped Manifold ContDiff Topology InnerProductSpace BigOperators

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M] [T2Space M]
variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
  [FiniteDimensional ℝ F]
variable {V : M → Type*} [∀ x, NormedAddCommGroup (V x)]
  [∀ x, InnerProductSpace ℝ (V x)] [TopologicalSpace (TotalSpace F V)]
  [FiberBundle F V] [VectorBundle ℝ F V] [ContMDiffVectorBundle ∞ F V I]
  [IsContMDiffRiemannianBundle I ∞ F V]

private theorem exists_orthonormal_normal_section_snoc
    (cov : CovariantDerivative I F V) (hcov : cov.IsMetricCompatible)
    (x : M) {k : ℕ} (w : V x) (hwNorm : ‖w‖ = 1)
    (U : Set M) (hU : IsOpen U) (hxU : x ∈ U)
    (e : Fin k → Cₛ^∞⟮I; F, V⟯)
    (heOrth : ∀ y ∈ U, Orthonormal ℝ (fun i ↦ e i y))
    (hwOrth : ∀ i, ⟪w, e i x⟫_ℝ = 0)
    (heCov : ∀ i, cov (e i) x = 0) :
    ∃ W : Set M, IsOpen W ∧ x ∈ W ∧
      ∃ eNew : Cₛ^∞⟮I; F, V⟯,
        (∀ y ∈ W, Orthonormal ℝ (Fin.snoc (fun i ↦ e i y) (eNew y))) ∧
        eNew x = w ∧ cov eNew x = 0 := by
  obtain ⟨σ, hσx, hσcov⟩ :=
    exists_section_with_value_and_covariantDerivative_zero cov x w
  let a : Fin k → C^∞⟮I, M; ℝ⟯ := fun i ↦
    ⟨fun y ↦ ⟪σ y, e i y⟫_ℝ, σ.contMDiff.inner_bundle (e i).contMDiff⟩
  let raw : Cₛ^∞⟮I; F, V⟯ := σ - ∑ i, a i • e i
  have hrawApply (y : M) :
      raw y = σ y - ∑ i, ⟪σ y, e i y⟫_ℝ • e i y := by
    rw [show raw = σ - ∑ i, a i • e i from rfl]
    change σ y - (∑ i, a i • e i) y = _
    rw [ContMDiffSection.finset_sum_apply]
    congr 1
  have hrawx : raw x = w := by
    rw [hrawApply, hσx]
    simp [hwOrth]
  have haValue (i : Fin k) : a i x = 0 := by
    simp [a, hσx, hwOrth i]
  have haDeriv (i : Fin k) : mfderiv I 𝓘(ℝ) (a i) x = 0 := by
    apply ContinuousLinearMap.ext
    intro u
    let X : (y : M) → TangentSpace I y := FiberBundle.extend E u
    have hX : X x = u := by simp [X]
    have h := hcov.mvfderiv_inner_eq (x := x) X
      (σ.contMDiff.mdifferentiableAt (by simp))
      ((e i).contMDiff.mdifferentiableAt (by simp))
    change mvfderiv I (a i) x u = 0
    rw [← hX]
    simpa [a, hσcov, heCov i] using h
  have htermCov (i : Fin k) :
      cov (fun y ↦ a i y • e i y) x = 0 := by
    have hleibniz := cov.isCovariantDerivativeOnUniv.leibniz
      (σ := fun y ↦ e i y) (g := fun y ↦ a i y) (x := x)
      ((e i).contMDiff.mdifferentiableAt (by simp))
      ((a i).contMDiff.mdifferentiableAt (by simp))
    change cov (((fun y ↦ a i y) • fun y ↦ e i y)) x = 0
    rw [hleibniz]
    simp [haValue i, haDeriv i, heCov i, mvfderiv]
  have hsumCov :
      cov (fun y ↦ ∑ i, a i y • e i y) x = 0 := by
    rw [covariantDerivative_finset_sum cov Finset.univ (fun i y ↦ a i y • e i y)
      (fun i ↦ ((a i).contMDiff.mdifferentiableAt (by simp)).smul_section
        ((e i).contMDiff.mdifferentiableAt (by simp)))]
    simp [htermCov]
  have hrawCov : cov raw x = 0 := by
    have hσdiff : MDiffAt (T% (fun y : M ↦ σ y)) x :=
      σ.contMDiff.mdifferentiableAt (by simp)
    have hsumDiff : MDiffAt (T% (fun y : M ↦ ∑ i, a i y • e i y)) x :=
      MDifferentiableAt.sum_section fun i hi ↦
        ((a i).contMDiff.mdifferentiableAt (by simp)).smul_section
          ((e i).contMDiff.mdifferentiableAt (by simp))
    have hneg :
        cov ((-1 : ℝ) • (fun y ↦ ∑ i, a i y • e i y)) x = 0 := by
      rw [cov.isCovariantDerivativeOnUniv.smul_const (-1) hsumDiff, hsumCov]
      simp
    have hnegDiff :
        MDiffAt (T% ((-1 : ℝ) • (fun y ↦ ∑ i, a i y • e i y))) x :=
      mdifferentiableAt_const.smul_section hsumDiff
    have hadd := cov.isCovariantDerivativeOnUniv.add hσdiff hnegDiff
    have hrawFun :
        (fun y ↦ raw y) =
          (fun y ↦ σ y) + (-1 : ℝ) • (fun y ↦ ∑ i, a i y • e i y) := by
      funext y
      rw [hrawApply]
      simp [a, sub_eq_add_neg]
    change cov (fun y ↦ raw y) x = 0
    rw [hrawFun, hadd, hσcov, hneg, add_zero]
  let q : M → ℝ := fun y ↦ ⟪raw y, raw y⟫_ℝ
  have hqSmooth : ContMDiff I 𝓘(ℝ) ∞ q :=
    raw.contMDiff.inner_bundle raw.contMDiff
  have hqx : q x = 1 := by
    simp [q, hrawx, hwNorm]
  let U' : Set M := U ∩ q ⁻¹' Ioi 0
  have hU' : IsOpen U' := hU.inter (isOpen_Ioi.preimage hqSmooth.continuous)
  have hxU' : x ∈ U' := by simp [U', hxU, hqx]
  let normalized : (y : M) → V y := fun y ↦ (Real.sqrt (q y))⁻¹ • raw y
  have hnormalizedNorm {y : M} (hyPos : 0 < q y) : ‖normalized y‖ = 1 := by
    have hrawNe : raw y ≠ 0 := by
      intro hr
      simp [q, hr] at hyPos
    rw [show normalized y = (Real.sqrt (q y))⁻¹ • raw y from rfl, norm_smul]
    rw [Real.norm_eq_abs, abs_inv, abs_of_pos (Real.sqrt_pos.mpr hyPos)]
    have hsqrt : Real.sqrt (q y) = ‖raw y‖ := by
      change Real.sqrt ⟪raw y, raw y⟫_ℝ = ‖raw y‖
      rw [real_inner_self_eq_norm_sq, Real.sqrt_sq (norm_nonneg _)]
    rw [hsqrt, inv_mul_cancel₀ (norm_ne_zero_iff.mpr hrawNe)]
  have hnormalizedSmooth :
      ContMDiffOn I (I.prod 𝓘(ℝ, F)) ∞ (T% normalized) U' := by
    have hsqrt : ContMDiffOn I 𝓘(ℝ) ∞ (fun y ↦ Real.sqrt (q y)) U' := by
      intro y hy
      exact (Real.contDiffAt_sqrt (ne_of_gt hy.2)).contMDiffAt.comp_contMDiffWithinAt
        y (hqSmooth.contMDiffAt.contMDiffWithinAt)
    have hinv : ContMDiffOn I 𝓘(ℝ) ∞ (fun y ↦ (Real.sqrt (q y))⁻¹) U' := by
      intro y hy
      exact (hsqrt y hy).inv₀ (ne_of_gt (Real.sqrt_pos.mpr hy.2))
    exact hinv.smul_section raw.contMDiff.contMDiffOn
  obtain ⟨e', he'⟩ := exists_contMDiffSection_eqOn_nhd
    (ι := Unit) (s := fun _ ↦ normalized) (u := U')
    (fun _ ↦ hnormalizedSmooth) hU' hxU'
  let eNew := e' ()
  have heNew : ∀ᶠ y in 𝓝 x, eNew y = normalized y :=
    he'.mono fun y hy ↦ hy ()
  have htarget : U' ∩ {y | eNew y = normalized y} ∈ 𝓝 x :=
    inter_mem (hU'.mem_nhds hxU') heNew
  obtain ⟨W, hWsub, hW, hxW⟩ := mem_nhds_iff.mp htarget
  refine ⟨W, hW, hxW, eNew, ?_, ?_, ?_⟩
  · intro y hy
    have hyTarget := hWsub hy
    have hyU : y ∈ U := hyTarget.1.1
    have hyPos : 0 < q y := hyTarget.1.2
    have heq : eNew y = normalized y := hyTarget.2
    have hold := heOrth y hyU
    have hrawOrth (j : Fin k) : ⟪raw y, e j y⟫_ℝ = 0 := by
      rw [hrawApply, inner_sub_left]
      have hsum := hold.inner_left_fintype (fun i ↦ ⟪σ y, e i y⟫_ℝ) j
      simpa using sub_eq_zero.mpr hsum.symm
    have hnorm : ‖normalized y‖ = 1 := hnormalizedNorm hyPos
    rw [heq]
    rw [orthonormal_iff_ite]
    intro i j
    refine Fin.lastCases ?_ (fun i ↦ ?_) i
    · refine Fin.lastCases ?_ (fun j ↦ ?_) j
      · simp [Fin.snoc_last, inner_self_eq_norm_sq_to_K, hnorm]
      · rw [Fin.snoc_last, Fin.snoc_castSucc]
        change ⟪(Real.sqrt (q y))⁻¹ • raw y, e j y⟫_ℝ = _
        rw [inner_smul_left, hrawOrth j]
        simp only [map_inv₀, conj_trivial, mul_zero, right_eq_ite_iff,
          zero_ne_one, imp_false]
        exact (Fin.castSucc_ne_last j).symm
    · refine Fin.lastCases ?_ (fun j ↦ ?_) j
      · rw [Fin.snoc_castSucc, Fin.snoc_last, real_inner_comm]
        simp [normalized, inner_smul_left, hrawOrth i]
      · simpa only [Fin.snoc_castSucc, Fin.castSucc_inj] using
          (orthonormal_iff_ite.mp hold i j)
  · rw [show eNew x = normalized x from heNew.self_of_nhds]
    simp [normalized, hqx, hrawx]
  · have hrawDiff : MDiffAt (T% (fun y : M ↦ raw y)) x :=
      raw.contMDiff.mdifferentiableAt (by simp)
    have hnormalizedDiff : MDiffAt (T% normalized) x :=
      (hnormalizedSmooth.contMDiffAt (hU'.mem_nhds hxU')).mdifferentiableAt
        (by simp)
    have heNewDiff : MDiffAt (T% (fun y : M ↦ eNew y)) x :=
      eNew.contMDiff.mdifferentiableAt (by simp)
    rw [cov.isCovariantDerivativeOnUniv.congr_of_eventuallyEq
      heNewDiff hnormalizedDiff (by simp) heNew]
    apply ContinuousLinearMap.ext
    intro u
    let X : (y : M) → TangentSpace I y := FiberBundle.extend E u
    have hX : X x = u := by simp [X]
    have hinnerEq :
        (fun y ↦ ⟪normalized y, normalized y⟫_ℝ) =ᶠ[𝓝 x]
          (fun _ ↦ (1 : ℝ)) := by
      filter_upwards [hU'.mem_nhds hxU'] with y hy
      simp [hnormalizedNorm hy.2]
    have hinnerDeriv :
        mvfderiv I (fun y ↦ ⟪normalized y, normalized y⟫_ℝ) x (X x) = 0 := by
      unfold mvfderiv
      have hvalue : (fun y ↦ ⟪normalized y, normalized y⟫_ℝ) x = 1 := by
        simp [hnormalizedNorm hxU'.2]
      have hinnerEq' :
          (fun y ↦ ⟪normalized y, normalized y⟫_ℝ) =ᶠ[𝓝 x]
            (fun _ ↦ (fun y ↦ ⟪normalized y, normalized y⟫_ℝ) x) := by
        filter_upwards [hinnerEq] with y hy
        calc
          (fun y ↦ ⟪normalized y, normalized y⟫_ℝ) y = 1 := hy
          _ = (fun y ↦ ⟪normalized y, normalized y⟫_ℝ) x := hvalue.symm
      rw [hinnerEq'.mfderiv_eq, mfderiv_const]
      change (NormedSpace.fromTangentSpace ((fun y ↦ ⟪normalized y, normalized y⟫_ℝ) x))
          ((0 : TangentSpace I x →L[ℝ]
            TangentSpace 𝓘(ℝ, ℝ) ((fun y ↦ ⟪normalized y, normalized y⟫_ℝ) x)) (X x)) = 0
      simp
    have hmetric := hcov.mvfderiv_inner_eq (x := x) X
      hnormalizedDiff hnormalizedDiff
    rw [hinnerDeriv] at hmetric
    have hscalarDiff : MDifferentiableAt I 𝓘(ℝ)
        (fun y ↦ (Real.sqrt (q y))⁻¹) x := by
      exact ((Real.contDiffAt_sqrt (x := q x) (by simp [hqx])).comp_contMDiffAt
        hqSmooth.contMDiffAt).inv₀ (by simp [hqx]) |>.mdifferentiableAt
          (by simp)
    have hleibniz := cov.isCovariantDerivativeOnUniv.leibniz
      (σ := fun y ↦ raw y) (g := fun y ↦ (Real.sqrt (q y))⁻¹)
      (x := x) hrawDiff hscalarDiff
    have hnormalizedx : normalized x = w := by simp [normalized, hqx, hrawx]
    have hcovApply :
        cov normalized x u =
          mvfderiv I (fun y ↦ (Real.sqrt (q y))⁻¹) x u • w := by
      have happ := congrArg (fun D ↦ D u) hleibniz
      have hnormalizedFun :
          normalized = (fun y ↦ (Real.sqrt (q y))⁻¹) • fun y ↦ raw y := by
        funext y
        rfl
      rw [hnormalizedFun]
      simpa [hqx, hrawCov, hrawx, mvfderiv] using happ
    rw [hcovApply]
    have hzero :
        mvfderiv I (fun y ↦ (Real.sqrt (q y))⁻¹) x u = 0 := by
      change 0 =
        ⟪cov normalized x (X x), normalized x⟫_ℝ +
          ⟪normalized x, cov normalized x (X x)⟫_ℝ at hmetric
      rw [hX] at hmetric
      rw [hcovApply, hnormalizedx, inner_smul_left, inner_smul_right,
        real_inner_self_eq_norm_sq, hwNorm] at hmetric
      rw [conj_trivial] at hmetric
      norm_num at hmetric
      linarith
    simp [hzero]

theorem exists_orthonormal_normal_sections
    (cov : CovariantDerivative I F V) (hcov : cov.IsMetricCompatible)
    (x : M) {k : ℕ} (v : Fin k → V x) (hv : Orthonormal ℝ v) :
    ∃ U : Set M, IsOpen U ∧ x ∈ U ∧
      ∃ e : Fin k → Cₛ^∞⟮I; F, V⟯,
        (∀ y ∈ U, Orthonormal ℝ (fun i ↦ e i y)) ∧
        (∀ i, e i x = v i) ∧
        ∀ i, cov (e i) x = 0 := by
  induction k with
  | zero =>
      refine ⟨Set.univ, isOpen_univ, mem_univ x, (fun i ↦ Fin.elim0 i), ?_, ?_, ?_⟩
      · intro y hy
        rw [orthonormal_iff_ite]
        intro i j
        exact Fin.elim0 i
      · intro i
        exact Fin.elim0 i
      · intro i
        exact Fin.elim0 i
  | succ k ih =>
      have hvInit : Orthonormal ℝ (fun i : Fin k ↦ v i.castSucc) := by
        convert hv.comp Fin.castSucc (Fin.castSucc_injective k) using 1
        rfl
      obtain ⟨U, hU, hxU, e, heOrth, heValue, heCov⟩ :=
        ih (fun i : Fin k ↦ v i.castSucc) hvInit
      have hwNorm : ‖v (Fin.last k)‖ = 1 := hv.norm_eq_one (Fin.last k)
      have hwOrth : ∀ i : Fin k, ⟪v (Fin.last k), e i x⟫_ℝ = 0 := by
        intro i
        have h := orthonormal_iff_ite.mp hv (Fin.last k) i.castSucc
        calc
          ⟪v (Fin.last k), e i x⟫_ℝ = ⟪v (Fin.last k), v i.castSucc⟫_ℝ := by rw [heValue i]
          _ = if Fin.last k = i.castSucc then 1 else 0 := h
          _ = 0 := by rw [if_neg (Fin.castSucc_ne_last i).symm]
      obtain ⟨W, hW, hxW, eNew, heNewOrth, heNewValue, heNewCov⟩ :=
        exists_orthonormal_normal_section_snoc cov hcov x (v (Fin.last k)) hwNorm
          U hU hxU e heOrth hwOrth heCov
      let eOut : Fin (k + 1) → Cₛ^∞⟮I; F, V⟯ :=
        Fin.snoc (fun i : Fin k ↦ e i) eNew
      refine ⟨W, hW, hxW, eOut, ?_, ?_, ?_⟩
      · intro y hy
        have hs :
            (fun i ↦ (eOut i) y) =
              Fin.snoc (fun i : Fin k ↦ e i y) (eNew y) := by
          funext i
          refine Fin.lastCases ?_ (fun j ↦ ?_) i <;>
            simp only [eOut, Fin.snoc_last, Fin.snoc_castSucc]
        rw [hs]
        exact heNewOrth y hy
      · intro i
        refine Fin.lastCases ?_ (fun j ↦ ?_) i
        · simpa [eOut, Fin.snoc_last] using heNewValue
        · simpa [eOut, Fin.snoc_castSucc] using heValue j
      · intro i
        refine Fin.lastCases ?_ (fun j ↦ ?_) i
        · simpa [eOut, Fin.snoc_last] using heNewCov
        · simpa [eOut, Fin.snoc_castSucc] using heCov j

end DifferentialGeometry.Geometry.Connection
