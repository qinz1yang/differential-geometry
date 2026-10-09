import DifferentialGeometry.Geometry.Connection.ChartFrame.RicciIdentitySmoothFrame
import DifferentialGeometry.Geometry.Connection.Subbundle
import DifferentialGeometry.Geometry.Connection.Hessian
import DifferentialGeometry.Geometry.Connection.HomBundle.Basic
import DifferentialGeometry.Geometry.Curvature.CurvatureOperator.TensorAction.HomBundleLeibniz

set_option autoImplicit false

noncomputable section

open Bundle CovariantDerivative
open DifferentialGeometry.Geometry.Curvature
open scoped Manifold ContDiff BigOperators Topology InnerProductSpace

namespace DifferentialGeometry.Geometry.Connection

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M] [T2Space M]
variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
  [FiniteDimensional ℝ F]

section Raw

variable {V : M → Type*} [TopologicalSpace (TotalSpace F V)]
  [∀ x, AddCommGroup (V x)] [∀ x, Module ℝ (V x)]
  [∀ x, TopologicalSpace (V x)] [∀ x, IsTopologicalAddGroup (V x)]
  [∀ x, ContinuousSMul ℝ (V x)] [FiberBundle F V]

def rawBundleConnLap
    (g : SmoothRiemannianMetric I M) (cov : CovariantDerivative I F V)
    (s : (x : M) → V x) (x : M) : V x :=
  ∑ i : Fin (Module.finrank ℝ E),
    (cov (covApply cov (smoothOrthoFrame (I := I) g x i) s) x
        (smoothOrthoFrame (I := I) g x i x) -
      cov s x
        ((LeviCivita (I := I) g)
          (smoothOrthoFrame (I := I) g x i) x
          (smoothOrthoFrame (I := I) g x i x)))

omit [T2Space M] [FiniteDimensional ℝ F] in
@[simp] theorem rawBundleConnLap_def
    (g : SmoothRiemannianMetric I M) (cov : CovariantDerivative I F V)
    (s : (x : M) → V x) (x : M) :
    rawBundleConnLap (I := I) g cov s x =
      ∑ i : Fin (Module.finrank ℝ E),
        (cov (covApply cov (smoothOrthoFrame (I := I) g x i) s) x
            (smoothOrthoFrame (I := I) g x i x) -
          cov s x
            ((LeviCivita (I := I) g)
              (smoothOrthoFrame (I := I) g x i) x
              (smoothOrthoFrame (I := I) g x i x))) := rfl

end Raw

variable {V : M → Type*} [TopologicalSpace (TotalSpace F V)]
  [∀ x, NormedAddCommGroup (V x)] [∀ x, NormedSpace ℝ (V x)]
  [FiberBundle F V] [VectorBundle ℝ F V]
  [ContMDiffVectorBundle ∞ F V I]

omit [FiniteDimensional ℝ F] [ContMDiffVectorBundle ∞ F V I] in
theorem rawBundleConnLap_eq_sum_hessian
    (g : SmoothRiemannianMetric I M) (cov : CovariantDerivative I F V)
    {σ : ∀ x, V x} {x : M}
    (hDσ : MDifferentiableAt I (I.prod 𝓘(ℝ, E →L[ℝ] F))
      (fun y => (⟨y, cov σ y⟩ : TotalSpace (E →L[ℝ] F)
        (fun y => TangentSpace I y →L[ℝ] V y))) x) :
    rawBundleConnLap g cov σ x =
      ∑ i : Fin (Module.finrank ℝ E),
        cov.hessian (LeviCivita g) σ x
          (smoothOrthoFrame g x i x) (smoothOrthoFrame g x i x) := by
  rw [rawBundleConnLap_def]
  apply Finset.sum_congr rfl
  intro i _
  let _ : NeZero (Module.finrank ℝ E) :=
    ⟨Nat.ne_of_gt (lt_of_le_of_lt (Nat.zero_le i.val) i.isLt)⟩
  exact (cov.hessian_apply (LeviCivita g) hDσ
    ((smoothOrthoFrame_smooth g x i).mdifferentiableAt (by simp)) _).symm

theorem rawBundleConnLap_eq_sum_hessian_of_contMDiffAt
    (g : SmoothRiemannianMetric I M) (cov : CovariantDerivative I F V)
    (hcov : ContMDiffCovariantDerivative cov ∞)
    {σ : ∀ x, V x} {x : M}
    (hσ : ContMDiffAt I (I.prod 𝓘(ℝ, F)) 2 (T% σ) x) :
    rawBundleConnLap g cov σ x =
      ∑ i : Fin (Module.finrank ℝ E),
        cov.hessian (LeviCivita g) σ x
          (smoothOrthoFrame g x i x) (smoothOrthoFrame g x i x) := by
  exact rawBundleConnLap_eq_sum_hessian g cov
    ((hcov.contMDiffAt (m := 1) hσ (by norm_num)).mdifferentiableAt (by simp))

omit [FiniteDimensional ℝ F] [ContMDiffVectorBundle ∞ F V I] in
theorem rawBundleConnLap_eq_zero_of_eventually_zero
    (g : SmoothRiemannianMetric I M) (cov : CovariantDerivative I F V)
    [ContMDiffCovariantDerivative cov ∞]
    (s : Cₛ^∞⟮I; F, V⟯) {x : M} {U : Set M}
    (hU : IsOpen U) (hxU : x ∈ U) (hs : ∀ y ∈ U, s y = 0) :
    rawBundleConnLap (I := I) g cov (fun y => s y) x = 0 := by
  classical
  by_cases hdim : Module.finrank ℝ E = 0
  · let _ : IsEmpty (Fin (Module.finrank ℝ E)) := by
      simp [hdim]
    simp [rawBundleConnLap]
  let _ : NeZero (Module.finrank ℝ E) := ⟨hdim⟩
  have cov_eq_zero_of_eqOn
      (T : (y : M) → V y) (hT : ∀ y ∈ U, T y = 0)
      (y : M) (hyU : y ∈ U) (hTdiff : MDiffAt (T% T) y) :
      cov T y = 0 := by
    have hzeroDiff : MDiffAt (T% fun z : M => (0 : V z)) y :=
      mdifferentiableAt_zeroSection (𝕜 := ℝ) (F := F) (E := V) (IB := I)
    have hEq : ∀ᶠ z in 𝓝 y, T z = (0 : V z) :=
      Filter.eventually_of_mem (hU.mem_nhds hyU) hT
    have hcovEq := cov.isCovariantDerivativeOnUniv.congr_of_eventuallyEq
      hTdiff hzeroDiff Filter.univ_mem hEq
    rw [hcovEq]
    exact congrArg (fun phi => phi y) cov.zero
  rw [rawBundleConnLap_def]
  apply Finset.sum_eq_zero
  intro i _
  let X := smoothOrthoFrame (I := I) g x i
  have hX : ContMDiff I (I.prod 𝓘(ℝ, E)) ∞ (T% X) :=
    smoothOrthoFrame_smooth (I := I) g x i
  have hcovs : cov (fun y => s y) x = 0 :=
    cov_eq_zero_of_eqOn (fun y => s y) hs x hxU s.mdifferentiableAt
  have hcovApplyZero : ∀ y ∈ U,
      DifferentialGeometry.Geometry.Curvature.covApply cov X (fun z => s z) y = 0 := by
    intro y hyU
    change cov (fun z => s z) y (X y) = 0
    rw [cov_eq_zero_of_eqOn (fun z => s z) hs y hyU s.mdifferentiableAt]
    rfl
  have hsPlus : ContMDiff I (I.prod 𝓘(ℝ, F)) ((∞ : WithTop ℕ∞) + 1)
      (T% fun y => s y) := by
    simpa using s.contMDiff
  have hcovApplyDiff : MDiffAt
      (T% (DifferentialGeometry.Geometry.Curvature.covApply cov X (fun y => s y))) x :=
    DifferentialGeometry.Geometry.Curvature.covApply_mdifferentiableAt
      (cov := cov) hX hsPlus
  have hcovCovApply : cov
      (DifferentialGeometry.Geometry.Curvature.covApply cov X (fun y => s y)) x = 0 :=
    cov_eq_zero_of_eqOn
      (DifferentialGeometry.Geometry.Curvature.covApply cov X (fun y => s y)) hcovApplyZero
      x hxU hcovApplyDiff
  change
    cov (DifferentialGeometry.Geometry.Curvature.covApply cov X (fun y => s y)) x (X x) -
      cov (fun y => s y) x
        ((LeviCivita (I := I) g) X x (X x)) = 0
  rw [hcovCovApply, hcovs]
  simp

omit [FiniteDimensional ℝ F] [ContMDiffVectorBundle ∞ F V I] in
theorem rawBundleConnLap_mem_of_isCovariantlyInvariant
    (g : SmoothRiemannianMetric I M) (cov : CovariantDerivative I F V)
    [ContMDiffCovariantDerivative cov ∞]
    (S : ∀ x, Submodule ℝ (V x))
    (hS : IsCovariantlyInvariantSubmoduleFamily cov S)
    (s : Cₛ^∞⟮I; F, V⟯) {x : M} {U : Set M}
    (hU : IsOpen U) (hxU : x ∈ U) (hs : ∀ y ∈ U, s y ∈ S y) :
    rawBundleConnLap (I := I) g cov (fun y => s y) x ∈ S x := by
  classical
  by_cases hdim : Module.finrank ℝ E = 0
  · let _ : IsEmpty (Fin (Module.finrank ℝ E)) := by
      simp [hdim]
    simp [rawBundleConnLap]
  let _ : NeZero (Module.finrank ℝ E) := ⟨hdim⟩
  rw [rawBundleConnLap_def]
  apply Submodule.sum_mem
  intro i hi
  let X := smoothOrthoFrame (I := I) g x i
  let u : Cₛ^∞⟮I; F, V⟯ :=
    ⟨covApply cov X (fun y => s y),
      contMDiffOn_univ.mp (covApply_contMDiffOn (cov := cov)
        (smoothOrthoFrame_smooth (I := I) g x i)
        (by simpa using s.contMDiff))⟩
  have hu : ∀ y ∈ U, u y ∈ S y := by
    intro y hy
    exact hS.covariantDerivative_mem s hU hs hy (X y)
  apply Submodule.sub_mem
  · exact hS.covariantDerivative_mem u hU hu hxU (X x)
  · exact hS.covariantDerivative_mem s hU hs hxU
      ((LeviCivita (I := I) g) X x (X x))

def rawBundleEndomorphismConnLap
    (g : SmoothRiemannianMetric I M) (cov : CovariantDerivative I F V)
    (A : (x : M) → V x →L[ℝ] V x) (x : M) : V x →L[ℝ] V x :=
  rawBundleConnLap (I := I) g
    (HomConnectionGen.homBundleCovariantDerivativeGen
      I M F V F V cov cov) A x

@[simp] theorem rawBundleEndomorphismConnLap_def
    (g : SmoothRiemannianMetric I M) (cov : CovariantDerivative I F V)
    (A : (x : M) → V x →L[ℝ] V x) (x : M) :
    rawBundleEndomorphismConnLap (I := I) g cov A x =
      rawBundleConnLap (I := I) g
        (HomConnectionGen.homBundleCovariantDerivativeGen
          I M F V F V cov cov) A x := rfl

theorem rawBundleEndomorphismConnLap_apply
    (g : SmoothRiemannianMetric I M) (cov : CovariantDerivative I F V)
    [ContMDiffCovariantDerivative cov ∞]
    (A : Cₛ^∞⟮I; F →L[ℝ] F, (fun x : M => V x →L[ℝ] V x)⟯)
    (w : Cₛ^∞⟮I; F, V⟯) (x : M) :
    rawBundleEndomorphismConnLap (I := I) g cov (fun y => A y) x (w x) =
      rawBundleConnLap (I := I) g cov (fun y => A y (w y)) x -
        A x (rawBundleConnLap (I := I) g cov (fun y => w y) x) -
        (2 : ℝ) • ∑ i : Fin (Module.finrank ℝ E),
          (HomConnectionGen.homBundleCovariantDerivativeGen
              I M F V F V cov cov (fun y => A y) x
              (smoothOrthoFrame (I := I) g x i x))
            (cov (fun y => w y) x (smoothOrthoFrame (I := I) g x i x)) := by
  classical
  by_cases hdim : Module.finrank ℝ E = 0
  · let _ : IsEmpty (Fin (Module.finrank ℝ E)) := by
      simp [hdim]
    simp [rawBundleEndomorphismConnLap, rawBundleConnLap]
  let _ : NeZero (Module.finrank ℝ E) := ⟨hdim⟩
  let covHom := HomConnectionGen.homBundleCovariantDerivativeGen
    I M F V F V cov cov
  simp only [rawBundleEndomorphismConnLap_def, rawBundleConnLap_def]
  simp only [_root_.sum_apply, map_sub, map_sum]
  rw [Finset.smul_sum]
  conv_rhs =>
    rw [← Finset.sum_sub_distrib]
    rw [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro i _
  let Z : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯ :=
    ⟨smoothOrthoFrame (I := I) g x i,
      smoothOrthoFrame_smooth (I := I) g x i⟩
  have hsecond := HomConnection.cov_V_toFun_covApply_pairedSection_apply
    I M F V F V cov cov Z A w (x := x) (Z x)
  have hfirst := HomConnectionGen.homBundleCovariantDerivativeGen_apply
    I M F V F V cov cov A w x
      ((LeviCivita (I := I) g) (fun y => Z y) x (Z x))
  simp only [covApply_apply] at hsecond
  change
    cov (covApply cov (fun y => Z y) (fun y => A y (w y))) x (Z x) =
      (covHom (covApply covHom (fun y => Z y) (fun y => A y)) x (Z x)) (w x) +
          (covHom (fun y => A y) x (Z x))
            (cov (fun y => w y) x (Z x)) +
        (covHom (fun y => A y) x (Z x))
          (cov (fun y => w y) x (Z x)) +
      A x (cov (covApply cov (fun y => Z y) (fun y => w y)) x (Z x)) at hsecond
  change
    (covHom (fun y => A y) x
        ((LeviCivita (I := I) g) (fun y => Z y) x (Z x))) (w x) =
      cov (fun y => A y (w y)) x
          ((LeviCivita (I := I) g) (fun y => Z y) x (Z x)) -
        A x (cov (fun y => w y) x
          ((LeviCivita (I := I) g) (fun y => Z y) x (Z x))) at hfirst
  change
    ((covHom (covApply covHom (fun y => Z y) (fun y => A y)) x (Z x)) (w x) -
        (covHom (fun y => A y) x
          ((LeviCivita (I := I) g) (fun y => Z y) x (Z x))) (w x)) =
      (cov (covApply cov (fun y => Z y) (fun y => A y (w y))) x (Z x) -
          cov (fun y => A y (w y)) x
            ((LeviCivita (I := I) g) (fun y => Z y) x (Z x))) -
        (A x (cov (covApply cov (fun y => Z y) (fun y => w y)) x (Z x)) -
          A x (cov (fun y => w y) x
            ((LeviCivita (I := I) g) (fun y => Z y) x (Z x)))) -
        (2 : ℝ) • (covHom (fun y => A y) x (Z x))
          (cov (fun y => w y) x (Z x))
  rw [hsecond, hfirst, two_smul]
  abel

end DifferentialGeometry.Geometry.Connection

namespace DifferentialGeometry.Geometry.Connection

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

theorem rawBundleEndomorphismConnLap_isSymmetric_of_eventually
    (g : SmoothRiemannianMetric I M)
    (cov : CovariantDerivative I F V) [ContMDiffCovariantDerivative cov ∞]
    (hcov : cov.IsMetricCompatible)
    (A : Cₛ^∞⟮I; F →L[ℝ] F, (fun x : M => V x →L[ℝ] V x)⟯)
    {x : M} (hA : ∀ᶠ y in 𝓝 x, (A y : V y →ₗ[ℝ] V y).IsSymmetric) :
    ((rawBundleEndomorphismConnLap g cov A x :
      V x →L[ℝ] V x) : V x →ₗ[ℝ] V x).IsSymmetric := by
  let : ∀ y, FiniteDimensional ℝ (V y) :=
    fun y => VectorBundle.finiteDimensional ℝ F V y
  let : ∀ y, CompleteSpace (V y) := fun y => FiniteDimensional.complete ℝ (V y)
  obtain ⟨U, hU, hUopen, hxU⟩ := mem_nhds_iff.mp hA
  have h := rawBundleConnLap_mem_of_isCovariantlyInvariant g
    (HomConnectionGen.homBundleCovariantDerivativeGen I M F V F V cov cov)
    (fun y => selfAdjoint.submodule ℝ (V y →L[ℝ] V y))
    (HomConnectionGen.homBundleCovariantDerivativeGen_isCovariantlyInvariant_selfAdjoint
      cov hcov) A hUopen hxU
    (fun y hy => ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mpr (hU hy))
  exact ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mp h

omit [IsContMDiffRiemannianBundle I 1 F V] in
theorem rawBundleEndomorphismConnLap_apply_eq_zero_of_isCovariantlyInvariant
    (g : SmoothRiemannianMetric I M) (cov : CovariantDerivative I F V)
    [ContMDiffCovariantDerivative cov ∞]
    (A : Cₛ^∞⟮I; F →L[ℝ] F, (fun x : M => V x →L[ℝ] V x)⟯)
    (w : Cₛ^∞⟮I; F, V⟯) (S : ∀ x, Submodule ℝ (V x))
    (hS : IsCovariantlyInvariantSubmoduleFamily cov S)
    (hAk : ∀ y v, v ∈ S y → A y v = 0) {x : M} {U : Set M}
    (hU : IsOpen U) (hxU : x ∈ U) (hs : ∀ y ∈ U, w y ∈ S y) :
    rawBundleEndomorphismConnLap (I := I) g cov (fun y => A y) x (w x) = 0 := by
  classical
  have hAw : ∀ y ∈ U, A y (w y) = 0 := by
    intro y hy
    exact hAk y (w y) (hs y hy)
  by_cases hdim : Module.finrank ℝ E = 0
  · let _ : IsEmpty (Fin (Module.finrank ℝ E)) := by
      simp [hdim]
    simp [rawBundleEndomorphismConnLap, rawBundleConnLap]
  let _ : NeZero (Module.finrank ℝ E) := ⟨hdim⟩
  let Aw : Cₛ^∞⟮I; F, V⟯ :=
    ⟨fun y => A y (w y),
      ContMDiff.clm_bundle_apply (b := id) A.contMDiff w.contMDiff⟩
  have hLapAw : rawBundleConnLap (I := I) g cov (fun y => Aw y) x = 0 :=
    rawBundleConnLap_eq_zero_of_eventually_zero g cov Aw hU hxU hAw
  have hLapw : rawBundleConnLap (I := I) g cov (fun y => w y) x ∈ S x :=
    rawBundleConnLap_mem_of_isCovariantlyInvariant g cov S hS w hU hxU hs
  have hAlapw : A x (rawBundleConnLap (I := I) g cov (fun y => w y) x) = 0 :=
    hAk x _ hLapw
  have hcross (i : Fin (Module.finrank ℝ E)) :
      (HomConnectionGen.homBundleCovariantDerivativeGen
          I M F V F V cov cov (fun y => A y) x
          (smoothOrthoFrame (I := I) g x i x))
        (cov (fun y => w y) x (smoothOrthoFrame (I := I) g x i x)) = 0 := by
    let X := smoothOrthoFrame (I := I) g x i
    let u : Cₛ^∞⟮I; F, V⟯ :=
      ⟨covApply cov X (fun y => w y),
        contMDiffOn_univ.mp (covApply_contMDiffOn (cov := cov)
          (smoothOrthoFrame_smooth (I := I) g x i)
          (by simpa using w.contMDiff))⟩
    have huS : ∀ y ∈ U, u y ∈ S y := by
      intro y hy
      exact hS.covariantDerivative_mem w hU hs hy (X y)
    have huA : ∀ y ∈ U, A y (u y) = 0 := by
      intro y hy
      exact hAk y _ (huS y hy)
    have hDA := HomConnectionGen.homBundleCovariantDerivativeGen_apply_of_eventually_mem_ker
      (I := I) (M := M) (F := F) (V := V) cov A u hU hxU huA (X x)
    have hcovuS : cov (fun y => u y) x (X x) ∈ S x :=
      hS.covariantDerivative_mem u hU huS hxU (X x)
    have hcovuA : A x (cov (fun y => u y) x (X x)) = 0 :=
      hAk x _ hcovuS
    change
      (HomConnectionGen.homBundleCovariantDerivativeGen
          I M F V F V cov cov (fun y => A y) x (X x)) (u x) = 0
    rw [hDA, hcovuA, neg_zero]
  rw [rawBundleEndomorphismConnLap_apply g cov A w x]
  have hLapAw' : rawBundleConnLap (I := I) g cov (fun y => A y (w y)) x = 0 := by
    simpa [Aw] using hLapAw
  rw [hLapAw', hAlapw]
  simp only [zero_sub]
  have hsum :
      ∑ i : Fin (Module.finrank ℝ E),
        (HomConnectionGen.homBundleCovariantDerivativeGen
            I M F V F V cov cov (fun y => A y) x
            (smoothOrthoFrame (I := I) g x i x))
          (cov (fun y => w y) x (smoothOrthoFrame (I := I) g x i x)) = 0 :=
    Finset.sum_eq_zero (fun i _ => hcross i)
  rw [hsum]
  simp

theorem inner_rawBundleEndomorphismConnLap_apply_of_eventually_mem_ker
    (g : SmoothRiemannianMetric I M) (cov : CovariantDerivative I F V)
    [ContMDiffCovariantDerivative cov ∞] (hcov : cov.IsMetricCompatible)
    (A : Cₛ^∞⟮I; F →L[ℝ] F, (fun x : M => V x →L[ℝ] V x)⟯)
    (hA : ∀ y, (A y : V y →ₗ[ℝ] V y).IsSymmetric)
    (w : Cₛ^∞⟮I; F, V⟯) {x : M} {U : Set M}
    (hU : IsOpen U) (hxU : x ∈ U) (hw : ∀ y ∈ U, A y (w y) = 0) :
    inner ℝ
        (rawBundleEndomorphismConnLap (I := I) g cov (fun y => A y) x (w x))
        (w x) =
      2 * ∑ i : Fin (Module.finrank ℝ E),
        inner ℝ
          (A x (cov (fun y => w y) x
            (smoothOrthoFrame (I := I) g x i x)))
          (cov (fun y => w y) x
            (smoothOrthoFrame (I := I) g x i x)) := by
  classical
  let Aw : Cₛ^∞⟮I; F, V⟯ :=
    ⟨fun y => A y (w y),
      ContMDiff.clm_bundle_apply (b := id) A.contMDiff w.contMDiff⟩
  have hAwZero : ∀ y ∈ U, Aw y = 0 := hw
  have hLapAw : rawBundleConnLap (I := I) g cov (fun y => Aw y) x = 0 :=
    rawBundleConnLap_eq_zero_of_eventually_zero g cov Aw hU hxU hAwZero
  have hcovAw : cov (fun y => Aw y) x = 0 := by
    have hzeroDiff : MDiffAt (T% fun y : M => (0 : V y)) x :=
      mdifferentiableAt_zeroSection (𝕜 := ℝ) (F := F) (E := V) (IB := I)
    have hEq : ∀ᶠ y in 𝓝 x, Aw y = (0 : V y) :=
      Filter.eventually_of_mem (hU.mem_nhds hxU) hAwZero
    have hcovEq := cov.isCovariantDerivativeOnUniv.congr_of_eventuallyEq
      Aw.mdifferentiableAt hzeroDiff Filter.univ_mem hEq
    rw [hcovEq]
    exact congrArg (fun phi => phi x) cov.zero
  have hDAw (i : Fin (Module.finrank ℝ E)) :
      (HomConnectionGen.homBundleCovariantDerivativeGen
          I M F V F V cov cov (fun y => A y) x
          (smoothOrthoFrame (I := I) g x i x)) (w x) =
        -A x (cov (fun y => w y) x
          (smoothOrthoFrame (I := I) g x i x)) := by
    have happly := HomConnectionGen.homBundleCovariantDerivativeGen_apply
      I M F V F V cov cov A w x
        (smoothOrthoFrame (I := I) g x i x)
    change
      (HomConnectionGen.homBundleCovariantDerivativeGen
          I M F V F V cov cov (fun y => A y) x
          (smoothOrthoFrame (I := I) g x i x)) (w x) =
        cov (fun y => Aw y) x (smoothOrthoFrame (I := I) g x i x) -
          A x (cov (fun y => w y) x
            (smoothOrthoFrame (I := I) g x i x)) at happly
    rw [hcovAw] at happly
    simpa using happly
  have hDAself (i : Fin (Module.finrank ℝ E)) :
      ((HomConnectionGen.homBundleCovariantDerivativeGen
          I M F V F V cov cov (fun y => A y) x
          (smoothOrthoFrame (I := I) g x i x) : V x →L[ℝ] V x) :
        V x →ₗ[ℝ] V x).IsSymmetric :=
    HomConnectionGen.homBundleCovariantDerivativeGen_isSymmetric
      cov hcov A hA x (smoothOrthoFrame (I := I) g x i x)
  have hwx : A x (w x) = 0 := hw x hxU
  have hAlap :
      inner ℝ
        (A x (rawBundleConnLap (I := I) g cov (fun y => w y) x)) (w x) = 0 := by
    calc
      inner ℝ
          (A x (rawBundleConnLap (I := I) g cov (fun y => w y) x)) (w x) =
        inner ℝ (rawBundleConnLap (I := I) g cov (fun y => w y) x)
          (A x (w x)) := hA x _ _
      _ = 0 := by rw [hwx, inner_zero_right]
  have hcross (i : Fin (Module.finrank ℝ E)) :
      inner ℝ
          ((HomConnectionGen.homBundleCovariantDerivativeGen
              I M F V F V cov cov (fun y => A y) x
              (smoothOrthoFrame (I := I) g x i x))
            (cov (fun y => w y) x
              (smoothOrthoFrame (I := I) g x i x)))
          (w x) =
        -inner ℝ
          (A x (cov (fun y => w y) x
            (smoothOrthoFrame (I := I) g x i x)))
          (cov (fun y => w y) x
            (smoothOrthoFrame (I := I) g x i x)) := by
    calc
      _ = inner ℝ
          (cov (fun y => w y) x
            (smoothOrthoFrame (I := I) g x i x))
          ((HomConnectionGen.homBundleCovariantDerivativeGen
              I M F V F V cov cov (fun y => A y) x
              (smoothOrthoFrame (I := I) g x i x)) (w x)) :=
        hDAself i _ _
      _ = inner ℝ
          (cov (fun y => w y) x
            (smoothOrthoFrame (I := I) g x i x))
          (-A x (cov (fun y => w y) x
            (smoothOrthoFrame (I := I) g x i x))) := by rw [hDAw i]
      _ = -inner ℝ
          (A x (cov (fun y => w y) x
            (smoothOrthoFrame (I := I) g x i x)))
          (cov (fun y => w y) x
            (smoothOrthoFrame (I := I) g x i x)) := by
        rw [inner_neg_right, real_inner_comm]
  have hLeib := rawBundleEndomorphismConnLap_apply
    g cov A w x
  have hLapAw' :
      rawBundleConnLap (I := I) g cov (fun y => A y (w y)) x = 0 := by
    simpa [Aw] using hLapAw
  rw [hLapAw'] at hLeib
  have hInner := congrArg (fun q : V x => inner ℝ q (w x)) hLeib
  simp only [inner_sub_left, zero_sub, inner_neg_left,
    inner_smul_left, starRingEnd_apply, star_trivial, sum_inner] at hInner
  simp_rw [hcross] at hInner
  rw [Finset.sum_neg_distrib] at hInner
  rw [hAlap] at hInner
  simpa [smul_eq_mul] using hInner

end DifferentialGeometry.Geometry.Connection
