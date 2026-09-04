import DifferentialGeometry.Geometry.Curvature.Metric.Defs
import DifferentialGeometry.Geometry.Metric.Pullback.Basic
import DifferentialGeometry.Geometry.Curvature.Riemann.Basic.Sections
import Mathlib.Geometry.Manifold.VectorField.LieBracket


open DifferentialGeometry.Geometry.Curvature


set_option autoImplicit false

noncomputable section

namespace DifferentialGeometry.Geometry.Curvature

open scoped Manifold ContDiff
open DifferentialGeometry.Tensor0SBundle

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace Real E]
  [FiniteDimensional Real E] [CompleteSpace E] [NeZero (Module.finrank Real E)]
variable {H : Type*} [TopologicalSpace H]
variable {I : ModelWithCorners Real E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
variable {N : Type*} [TopologicalSpace N] [ChartedSpace H N] [IsManifold I ∞ N]

private lemma infty_ne_zero : (∞ : WithTop ℕ∞) ≠ 0 := by
  decide

omit [FiniteDimensional ℝ E] [CompleteSpace E] [NeZero (Module.finrank ℝ E)] [IsManifold I ∞ M]
    [IsManifold I ∞ N] in
private theorem mfderiv_eq_cle_apply
    (Phi : M ≃ₘ⟮I, I⟯ N) (x : M) (v : TangentSpace I x) :
    Diffeomorph.mfderivToContinuousLinearEquiv Phi infty_ne_zero x v =
      mfderiv I I Phi x v := by
  have h :=
    Diffeomorph.mfderivToContinuousLinearEquiv_coe (Φ := Phi) (x := x) infty_ne_zero
  exact congrArg (fun f : TangentSpace I x →L[Real] TangentSpace I (Phi x) => f v) h

omit [FiniteDimensional ℝ E] [CompleteSpace E] [NeZero (Module.finrank ℝ E)] [IsManifold I ∞ M]
    [IsManifold I ∞ N] in
theorem mpullback_symm_apply
    (Phi : M ≃ₘ⟮I, I⟯ N) (X : (p : M) -> TangentSpace I p) (x : M) :
    VectorField.mpullback I I (Phi.symm : N -> M) X (Phi x) =
      mfderiv I I (Phi : M -> N) x (X x) := by
  unfold VectorField.mpullback
  rw [Diffeomorph.symm_apply_apply Phi x]
  have hinv :
      (mfderiv I I (Phi.symm : N -> M) (Phi x)).inverse =
        mfderiv I I (Phi : M -> N) x := by
    apply ContinuousLinearMap.inverse_eq
    · have hPhi : MDifferentiableAt I I (Phi : M -> N) x :=
        Phi.mdifferentiable infty_ne_zero x
      have hPhiSymm : MDifferentiableAt I I (Phi.symm : N -> M) (Phi x) :=
        Phi.symm.mdifferentiable infty_ne_zero (Phi x)
      have hcomp : (Phi.symm : N -> M) ∘ (Phi : M -> N) = id := by
        funext y
        exact Phi.symm_apply_apply y
      have hchain := mfderiv_comp x hPhiSymm hPhi
      rw [hcomp, mfderiv_id] at hchain
      exact hchain.symm
    · have hPhiSymm : MDifferentiableAt I I (Phi.symm : N -> M) (Phi x) :=
        Phi.symm.mdifferentiable infty_ne_zero (Phi x)
      have hPhi : MDifferentiableAt I I (Phi : M -> N) (Phi.symm (Phi x)) := by
        rw [Phi.symm_apply_apply]
        exact Phi.mdifferentiable infty_ne_zero x
      have hcomp : (Phi : M -> N) ∘ (Phi.symm : N -> M) = id := by
        funext y
        exact Phi.apply_symm_apply y
      have hchain := mfderiv_comp (Phi x) hPhi hPhiSymm
      rw [hcomp, mfderiv_id] at hchain
      rw [Phi.symm_apply_apply] at hchain
      exact hchain.symm
  exact congrArg
    (fun f : TangentSpace I x →L[Real] TangentSpace I (Phi x) => f (X x)) hinv

private abbrev pushFwdField
    (Phi : M ≃ₘ⟮I, I⟯ N) (X : (p : M) -> TangentSpace I p) :
    (q : N) -> TangentSpace I q :=
  VectorField.mpullback I I (Phi.symm : N -> M) X

omit [FiniteDimensional ℝ E] [CompleteSpace E] [NeZero (Module.finrank ℝ E)] [IsManifold I ∞ M]
    [IsManifold I ∞ N] in
@[simp] private theorem pushFwdField_apply_at_image
    (Phi : M ≃ₘ⟮I, I⟯ N) (X : (p : M) -> TangentSpace I p) (x : M) :
    pushFwdField (I := I) Phi X (Phi x) =
      mfderiv I I (Phi : M -> N) x (X x) :=
  mpullback_symm_apply (I := I) Phi X x


noncomputable def pushFwdSection
    [IsManifold I 1 M] [IsManifold I 1 N]
    (Phi : M ≃ₘ⟮I, I⟯ N)
    (X : ContMDiffSection I E (∞ : WithTop ℕ∞)
      (TangentSpace I : M -> Type _)) :
    ContMDiffSection I E (∞ : WithTop ℕ∞) (TangentSpace I : N -> Type _) where
  toFun := pushFwdField (I := I) Phi (fun p : M => X p)
  contMDiff_toFun := by
    refine ContMDiff.mpullback_vectorField
      (I := I) (I' := I) (f := (Phi.symm : N -> M))
      (V := fun p : M => X p) (m := ∞) (n := ∞)
      X.contMDiff Phi.symm.contMDiff ?_ ?_
    · intro q
      rw [← Diffeomorph.mfderivToContinuousLinearEquiv_coe
        (Φ := Phi.symm) (x := q) infty_ne_zero]
      exact ContinuousLinearMap.isInvertible_equiv
    · simp

omit [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)] [IsManifold I ∞ M] [IsManifold I ∞ N] in
@[simp] theorem pushFwdSection_apply_at_image
    [IsManifold I 1 M] [IsManifold I 1 N]
    (Phi : M ≃ₘ⟮I, I⟯ N)
    (X : ContMDiffSection I E (∞ : WithTop ℕ∞)
      (TangentSpace I : M -> Type _)) (x : M) :
    pushFwdSection (I := I) Phi X (Phi x) =
      mfderiv I I (Phi : M -> N) x (X x) := by
  simp [pushFwdSection]

omit [NeZero (Module.finrank ℝ E)] in
theorem directionalDeriv_pullback
    [T2Space M]
    [IsManifold I 1 M] [IsManifold I 1 N]
    (g : SmoothRiemannianMetric I N) (Phi : M ≃ₘ⟮I, I⟯ N)
    (A P Q : ContMDiffSection I E (∞ : WithTop ℕ∞)
      (TangentSpace I : M -> Type _)) (x : M) :
    DifferentialGeometry.Geometry.Connection.directionalDerivAlong (I := I) (fun p : M => A p)
        (fun y : M =>
          (Diffeomorph.pullbackMetric (I := I) g Phi).inner y (P y) (Q y)) x =
      DifferentialGeometry.Geometry.Connection.directionalDerivAlong (I := I)
        (fun q : N => pushFwdSection (I := I) Phi A q)
        (fun q : N =>
          g.inner q (pushFwdSection (I := I) Phi P q)
            (pushFwdSection (I := I) Phi Q q)) (Phi x) := by
  have hfun :
      (fun y : M =>
          (Diffeomorph.pullbackMetric (I := I) g Phi).inner y (P y) (Q y)) =
        fun y : M =>
          (fun q : N =>
            g.inner q (pushFwdSection (I := I) Phi P q)
              (pushFwdSection (I := I) Phi Q q)) (Phi y) := by
    funext y
    rw [Diffeomorph.pullbackMetric_inner]
    simp only [pushFwdSection_apply_at_image]
  rw [hfun]
  unfold DifferentialGeometry.Geometry.Connection.directionalDerivAlong
  dsimp only
  rw [pushFwdSection_apply_at_image]
  rw [mvfderiv_real_eq_mfderiv, mvfderiv_real_eq_mfderiv]
  have hG_diff :
      MDifferentiableAt I 𝓘(Real, Real)
        (fun q : N =>
          g.inner q (pushFwdSection (I := I) Phi P q)
            (pushFwdSection (I := I) Phi Q q)) (Phi x) :=
    (DifferentialGeometry.Geometry.Curvature.CovariantDerivative.metric_inner_contMDiffAt (I := I)
      (M := N) g
      (pushFwdSection (I := I) Phi P).contMDiff.contMDiffAt
      (pushFwdSection (I := I) Phi Q).contMDiff.contMDiffAt
      (by simp)).mdifferentiableAt (by simp)
  have hPhi_diff : MDifferentiableAt I I (Phi : M -> N) x :=
    Phi.contMDiff.contMDiffAt.mdifferentiableAt (by simp)
  have hcomp :=
    mfderiv_comp_apply (I := I) (I' := I) (I'' := 𝓘(Real, Real))
      (g := fun q : N =>
        g.inner q (pushFwdSection (I := I) Phi P q)
          (pushFwdSection (I := I) Phi Q q))
      (f := (Phi : M -> N)) (x := x) hG_diff hPhi_diff (A x)
  simpa [Function.comp_def] using hcomp

omit [NeZero (Module.finrank ℝ E)] in
private theorem inner_bracket_pullback_pushFwd
    [T2Space M]
    [IsManifold I 1 M] [IsManifold I 1 N]
    (g : SmoothRiemannianMetric I N) (Phi : M ≃ₘ⟮I, I⟯ N)
    (A P Q : ContMDiffSection I E (∞ : WithTop ℕ∞)
      (TangentSpace I : M -> Type _)) (x : M) :
    (Diffeomorph.pullbackMetric (I := I) g Phi).inner x (A x)
        (VectorField.mlieBracket I (fun p : M => P p) (fun p : M => Q p) x) =
      g.inner (Phi x) (pushFwdSection (I := I) Phi A (Phi x))
        (VectorField.mlieBracket I
          (fun q : N => pushFwdSection (I := I) Phi P q)
          (fun q : N => pushFwdSection (I := I) Phi Q q) (Phi x)) := by
  have : IsManifold I (minSmoothness Real 2) M := by
    exact IsManifold.of_le (I := I) (M := M) (n := ∞)
      (by
        rw [minSmoothness_of_isRCLikeNormedField]
        exact WithTop.coe_le_coe.2 (le_top : (2 : ℕ∞) ≤ (⊤ : ℕ∞)))
  have : IsManifold I (minSmoothness Real 2) N := by
    exact IsManifold.of_le (I := I) (M := N) (n := ∞)
      (by
        rw [minSmoothness_of_isRCLikeNormedField]
        exact WithTop.coe_le_coe.2 (le_top : (2 : ℕ∞) ≤ (⊤ : ℕ∞)))
  have hbr :
      VectorField.mpullback I I (Phi.symm : N -> M)
          (VectorField.mlieBracket I (fun p : M => P p) (fun p : M => Q p))
          (Phi x) =
        VectorField.mlieBracket I
          (fun q : N => pushFwdSection (I := I) Phi P q)
          (fun q : N => pushFwdSection (I := I) Phi Q q) (Phi x) := by
    have hbr' :=
      VectorField.mpullback_mlieBracket
        (I := I) (I' := I) (f := (Phi.symm : N -> M))
        (V := fun p : M => P p) (W := fun p : M => Q p) (x₀ := Phi x)
        (by simpa using P.contMDiff.contMDiffAt.mdifferentiableAt (by simp))
        (by simpa using Q.contMDiff.contMDiffAt.mdifferentiableAt (by simp))
        Phi.symm.contMDiff.contMDiffAt
        (by
          rw [minSmoothness_of_isRCLikeNormedField]
          exact WithTop.coe_le_coe.2 (le_top : (2 : ℕ∞) ≤ (⊤ : ℕ∞)))
    simpa [pushFwdSection, pushFwdField] using hbr'
  rw [← hbr]
  rw [mpullback_symm_apply]
  rw [Diffeomorph.pullbackMetric_inner]
  rw [pushFwdSection_apply_at_image]


omit [NeZero (Module.finrank ℝ E)] in
private theorem koszulScalar_pullback_pushFwd
    [T2Space M]
    [IsManifold I 1 M] [IsManifold I 1 N]
    (g : SmoothRiemannianMetric I N) (Phi : M ≃ₘ⟮I, I⟯ N)
    (A B C : ContMDiffSection I E (∞ : WithTop ℕ∞)
      (TangentSpace I : M -> Type _)) (x : M) :
    DifferentialGeometry.Geometry.Connection.koszulScalar (I := I)
      (Diffeomorph.pullbackMetric (I := I) g Phi)
        (fun p : M => A p) (fun p : M => B p) (fun p : M => C p) x =
      DifferentialGeometry.Geometry.Connection.koszulScalar (I := I) g
        (fun q : N => pushFwdSection (I := I) Phi A q)
        (fun q : N => pushFwdSection (I := I) Phi B q)
        (fun q : N => pushFwdSection (I := I) Phi C q) (Phi x) := by
  unfold DifferentialGeometry.Geometry.Connection.koszulScalar
  dsimp only
  rw [directionalDeriv_pullback (I := I) g Phi A B C x,
    directionalDeriv_pullback (I := I) g Phi B C A x,
    directionalDeriv_pullback (I := I) g Phi C A B x,
    inner_bracket_pullback_pushFwd (I := I) g Phi A B C x,
    inner_bracket_pullback_pushFwd (I := I) g Phi B C A x,
    inner_bracket_pullback_pushFwd (I := I) g Phi C A B x]

omit [NeZero (Module.finrank ℝ E)] in
theorem metricCov_pullback
    [T2Space M]
    [IsManifold I 1 M] [IsManifold I 1 N] (g : SmoothRiemannianMetric I N) (Phi : M ≃ₘ⟮I, I⟯ N)
    (Y : ContMDiffSection I E (∞ : WithTop ℕ∞)
      (TangentSpace I : M -> Type _)) (x : M) (v : TangentSpace I x) :
    mfderiv I I (Phi : M -> N) x
        ((metricCov (I := I) (M := M) (Diffeomorph.pullbackMetric (I := I) g Phi)
          (fun p : M => Y p) x) v)
      =
      (metricCov (I := I) (M := N) g
        (fun q : N => pushFwdSection (I := I) Phi Y q) (Phi x))
        (mfderiv I I (Phi : M -> N) x v) := by
  apply tangentFlatLinear_injective_gen (I := I) g (Phi x)
  ext u
  simp only [tangentFlatLinear_apply_gen]
  set e := Diffeomorph.mfderivToContinuousLinearEquiv Phi infty_ne_zero x with he
  set w : TangentSpace I x := e.symm u with hw_def
  have hdw : mfderiv I I (Phi : M -> N) x w = u := by
    rw [← mfderiv_eq_cle_apply (I := I) Phi x w, hw_def]
    exact e.apply_symm_apply u
  obtain ⟨Xv, hXv⟩ :=
    ContMDiffSection.exists_eq_at (I := I) (F := E) (V := TangentSpace I)
      (n := (⊤ : ℕ∞)) x v
  obtain ⟨Zw, hZw⟩ :=
    ContMDiffSection.exists_eq_at (I := I) (F := E) (V := TangentSpace I)
      (n := (⊤ : ℕ∞)) x w
  have hu : pushFwdSection (I := I) Phi Zw (Phi x) = u := by
    rw [pushFwdSection_apply_at_image, hZw]; exact hdw
  have hv : pushFwdSection (I := I) Phi Xv (Phi x) = mfderiv I I (Phi : M -> N) x v := by
    rw [pushFwdSection_apply_at_image, hXv]
  have hkoszul_h :
      g.inner (Phi x)
          (mfderiv I I (Phi : M -> N) x
            (metricCov (I := I) (M := M) (Diffeomorph.pullbackMetric (I := I) g Phi)
              (fun p : M => Y p) x v)) u
        = (1 / 2 : Real) *
            DifferentialGeometry.Geometry.Connection.koszulScalar (I := I)
              (Diffeomorph.pullbackMetric (I := I) g Phi)
              (fun p : M => Xv p) (fun p : M => Y p) (fun p : M => Zw p) x := by
    rw [← hdw, ← Diffeomorph.pullbackMetric_inner, ← hXv, ← hZw]
    exact
      DifferentialGeometry.Geometry.Connection.leviCivitaConnectionOfMetric_inner_eq_koszulScalar
      (I := I) (Diffeomorph.pullbackMetric (I := I) g Phi)
      (fun p : M => Xv p) (fun p : M => Y p) (fun p : M => Zw p) x
      (Xv.contMDiff.contMDiffAt.mdifferentiableAt (by simp))
      (Y.contMDiff.contMDiffAt.mdifferentiableAt (by simp))
      (Zw.contMDiff.contMDiffAt.mdifferentiableAt (by simp))
  have hkoszul_g :
      g.inner (Phi x)
          (metricCov (I := I) (M := N) g
            (fun q : N => pushFwdSection (I := I) Phi Y q) (Phi x)
            (mfderiv I I (Phi : M -> N) x v)) u
        = (1 / 2 : Real) *
            DifferentialGeometry.Geometry.Connection.koszulScalar (I := I) g
              (fun q : N => pushFwdSection (I := I) Phi Xv q)
              (fun q : N => pushFwdSection (I := I) Phi Y q)
              (fun q : N => pushFwdSection (I := I) Phi Zw q) (Phi x) := by
    rw [← hu, ← hv]
    exact
      DifferentialGeometry.Geometry.Connection.leviCivitaConnectionOfMetric_inner_eq_koszulScalar
      (I := I) g
      (fun q : N => pushFwdSection (I := I) Phi Xv q)
      (fun q : N => pushFwdSection (I := I) Phi Y q)
      (fun q : N => pushFwdSection (I := I) Phi Zw q) (Phi x)
      ((pushFwdSection (I := I) Phi Xv).contMDiff.contMDiffAt.mdifferentiableAt (by simp))
      ((pushFwdSection (I := I) Phi Y).contMDiff.contMDiffAt.mdifferentiableAt (by simp))
      ((pushFwdSection (I := I) Phi Zw).contMDiff.contMDiffAt.mdifferentiableAt (by simp))
  rw [hkoszul_h, hkoszul_g, koszulScalar_pullback_pushFwd (I := I) g Phi Xv Y Zw x]

omit [NeZero (Module.finrank ℝ E)] in
private theorem connectionRiemannCurvatureField_pullback_pushFwd
    [T2Space M]
    [IsManifold I 1 M] [IsManifold I 1 N]
    (g : SmoothRiemannianMetric I N) (Phi : M ≃ₘ⟮I, I⟯ N)
    (X Y Z : ContMDiffSection I E (∞ : WithTop ℕ∞)
      (TangentSpace I : M -> Type _)) (x : M) :
    mfderiv I I (Phi : M -> N) x
        (DifferentialGeometry.Geometry.Curvature.connectionRiemannCurvatureField
          (I := I)
          (metricCov (I := I) (M := M) (Diffeomorph.pullbackMetric (I := I) g Phi))
          (fun p : M => X p) (fun p : M => Y p) (fun p : M => Z p) x)
      =
      DifferentialGeometry.Geometry.Curvature.connectionRiemannCurvatureField
        (I := I) (metricCov (I := I) (M := N) g)
        (fun q : N => pushFwdSection (I := I) Phi X q)
        (fun q : N => pushFwdSection (I := I) Phi Y q)
        (fun q : N => pushFwdSection (I := I) Phi Z q) (Phi x) := by
  let h : SmoothRiemannianMetric I M := Diffeomorph.pullbackMetric (I := I) g Phi
  let covh : CovariantDerivative I E (TangentSpace I : M -> Type _) :=
    metricCov (I := I) (M := M) h
  let covg : CovariantDerivative I E (TangentSpace I : N -> Type _) :=
    metricCov (I := I) (M := N) g
  let ZYh : ContMDiffSection I E (∞ : WithTop ℕ∞) (TangentSpace I : M -> Type _) :=
    ⟨fun p : M => (covh (fun q : M => Z q) p) (Y p),
      fun p
        => DifferentialGeometry.Geometry.Curvature.CovariantDerivative.cov_smooth_apply_contMDiffAt
        (I := I) covh (metricCov_smooth (I := I) (M := M) h) Y Z p⟩
  let ZXh : ContMDiffSection I E (∞ : WithTop ℕ∞) (TangentSpace I : M -> Type _) :=
    ⟨fun p : M => (covh (fun q : M => Z q) p) (X p),
      fun p
        => DifferentialGeometry.Geometry.Curvature.CovariantDerivative.cov_smooth_apply_contMDiffAt
        (I := I) covh (metricCov_smooth (I := I) (M := M) h) X Z p⟩
  have hZY :
      (fun q : N => pushFwdSection (I := I) Phi ZYh q) =
        (fun q : N => (covg (fun r : N => pushFwdSection (I := I) Phi Z r) q)
          (pushFwdSection (I := I) Phi Y q)) := by
    funext q
    obtain ⟨p, rfl⟩ := Phi.surjective q
    calc
      pushFwdSection (I := I) Phi ZYh (Phi p) =
          mfderiv I I (Phi : M -> N) p
            ((covh (fun q : M => Z q) p) (Y p)) := by
            rw [pushFwdSection_apply_at_image]
            rfl
      _ =
          (metricCov (I := I) (M := N) g
            (fun r : N => pushFwdSection (I := I) Phi Z r) (Phi p))
            (mfderiv I I (Phi : M -> N) p (Y p)) := by
            simpa [h, covh, covg, ZYh] using
              metricCov_pullback
                (I := I) g Phi Z p (Y p)
      _ =
          (metricCov (I := I) (M := N) g
            (fun r : N => pushFwdSection (I := I) Phi Z r) (Phi p))
            (pushFwdSection (I := I) Phi Y (Phi p)) := by
            rw [pushFwdSection_apply_at_image]
  have hZX :
      (fun q : N => pushFwdSection (I := I) Phi ZXh q) =
        (fun q : N => (covg (fun r : N => pushFwdSection (I := I) Phi Z r) q)
          (pushFwdSection (I := I) Phi X q)) := by
    funext q
    obtain ⟨p, rfl⟩ := Phi.surjective q
    calc
      pushFwdSection (I := I) Phi ZXh (Phi p) =
          mfderiv I I (Phi : M -> N) p
            ((covh (fun q : M => Z q) p) (X p)) := by
            rw [pushFwdSection_apply_at_image]
            rfl
      _ =
          (metricCov (I := I) (M := N) g
            (fun r : N => pushFwdSection (I := I) Phi Z r) (Phi p))
            (mfderiv I I (Phi : M -> N) p (X p)) := by
            simpa [h, covh, covg, ZXh] using
              metricCov_pullback
                (I := I) g Phi Z p (X p)
      _ =
          (metricCov (I := I) (M := N) g
            (fun r : N => pushFwdSection (I := I) Phi Z r) (Phi p))
            (pushFwdSection (I := I) Phi X (Phi p)) := by
            rw [pushFwdSection_apply_at_image]
  have hbr :
      mfderiv I I (Phi : M -> N) x
          (VectorField.mlieBracket I (fun p : M => X p) (fun p : M => Y p) x) =
        VectorField.mlieBracket I
          (fun q : N => pushFwdSection (I := I) Phi X q)
          (fun q : N => pushFwdSection (I := I) Phi Y q) (Phi x) := by
    have : IsManifold I (minSmoothness Real 2) M := by
      exact IsManifold.of_le (I := I) (M := M) (n := ∞)
        (by
          rw [minSmoothness_of_isRCLikeNormedField]
          exact WithTop.coe_le_coe.2 (le_top : (2 : ℕ∞) ≤ (⊤ : ℕ∞)))
    have : IsManifold I (minSmoothness Real 2) N := by
      exact IsManifold.of_le (I := I) (M := N) (n := ∞)
        (by
          rw [minSmoothness_of_isRCLikeNormedField]
          exact WithTop.coe_le_coe.2 (le_top : (2 : ℕ∞) ≤ (⊤ : ℕ∞)))
    have hbr' :=
      VectorField.mpullback_mlieBracket
        (I := I) (I' := I) (f := (Phi.symm : N -> M))
        (V := fun p : M => X p) (W := fun p : M => Y p)
        (x₀ := Phi x)
        (by
          simpa using
            X.contMDiff.contMDiffAt.mdifferentiableAt (by simp))
        (by
          simpa using
            Y.contMDiff.contMDiffAt.mdifferentiableAt (by simp))
        Phi.symm.contMDiff.contMDiffAt
        (by
          rw [minSmoothness_of_isRCLikeNormedField]
          exact WithTop.coe_le_coe.2 (le_top : (2 : ℕ∞) ≤ (⊤ : ℕ∞)))
    simpa [pushFwdSection, pushFwdField] using hbr'
  simp only [DifferentialGeometry.Geometry.Curvature.connectionRiemannCurvatureField]
  change
    mfderiv I I (Phi : M -> N) x
      ((covh (fun p : M => ZYh p) x) (X x) -
        (covh (fun p : M => ZXh p) x) (Y x) -
        (covh (fun p : M => Z p) x)
          (VectorField.mlieBracket I (fun p : M => X p) (fun p : M => Y p) x))
      =
      (covg (fun q : N =>
          (covg (fun r : N => pushFwdSection (I := I) Phi Z r) q)
            (pushFwdSection (I := I) Phi Y q)) (Phi x))
        (pushFwdSection (I := I) Phi X (Phi x)) -
        (covg (fun q : N =>
          (covg (fun r : N => pushFwdSection (I := I) Phi Z r) q)
            (pushFwdSection (I := I) Phi X q)) (Phi x))
          (pushFwdSection (I := I) Phi Y (Phi x)) -
        (covg (fun q : N => pushFwdSection (I := I) Phi Z q) (Phi x))
          (VectorField.mlieBracket I
            (fun q : N => pushFwdSection (I := I) Phi X q)
            (fun q : N => pushFwdSection (I := I) Phi Y q) (Phi x))
  rw [map_sub, map_sub]
  rw [metricCov_pullback (I := I) g Phi ZYh x (X x)]
  rw [metricCov_pullback (I := I) g Phi ZXh x (Y x)]
  rw [metricCov_pullback
    (I := I) g Phi Z x
    (VectorField.mlieBracket I (fun p : M => X p) (fun p : M => Y p) x)]
  rw [hZY, hZX, hbr]
  simp [covg]

omit [NeZero (Module.finrank ℝ E)] in
theorem metricRm04Std_pullback
    [T2Space M] [T2Space N]
    [IsManifold I 1 M] [IsManifold I 1 N]
    (g : SmoothRiemannianMetric I N) (Phi : M ≃ₘ⟮I, I⟯ N)
    (x : M) (X Y Z W : TangentSpace I x) :
    metricRm04StdAt (I := I) (M := M)
        (Diffeomorph.pullbackMetric (I := I) g Phi) x X Y Z W =
      metricRm04StdAt (I := I) (M := N) g (Phi x)
        (mfderiv I I (Phi : M -> N) x X)
        (mfderiv I I (Phi : M -> N) x Y)
        (mfderiv I I (Phi : M -> N) x Z)
        (mfderiv I I (Phi : M -> N) x W) := by
  obtain ⟨Xs, hXs⟩ :=
    ContMDiffSection.exists_eq_at
      (I := I) (F := E) (V := TangentSpace I) (n := (⊤ : ℕ∞)) x X
  obtain ⟨Ys, hYs⟩ :=
    ContMDiffSection.exists_eq_at
      (I := I) (F := E) (V := TangentSpace I) (n := (⊤ : ℕ∞)) x Y
  obtain ⟨Zs, hZs⟩ :=
    ContMDiffSection.exists_eq_at
      (I := I) (F := E) (V := TangentSpace I) (n := (⊤ : ℕ∞)) x Z
  obtain ⟨Ws, hWs⟩ :=
    ContMDiffSection.exists_eq_at
      (I := I) (F := E) (V := TangentSpace I) (n := (⊤ : ℕ∞)) x W
  rw [metricRm04StdAt_apply, metricRm04StdAt_apply]
  unfold metricRm04At
  have hleft :=
    DifferentialGeometry.Geometry.Curvature.CovariantDerivative.riemannCurvature04At_apply_smooth
      (I := I)
      (g := Diffeomorph.pullbackMetric (I := I) g Phi)
      (cov := metricCov (I := I) (M := M)
        (Diffeomorph.pullbackMetric (I := I) g Phi))
      (hcov := metricCov_smooth (I := I) (M := M)
        (Diffeomorph.pullbackMetric (I := I) g Phi))
      Xs Ys Zs Ws x
  have hright :=
    DifferentialGeometry.Geometry.Curvature.CovariantDerivative.riemannCurvature04At_apply_smooth
      (I := I)
      (g := g)
      (cov := metricCov (I := I) (M := N) g)
      (hcov := metricCov_smooth (I := I) (M := N) g)
      (pushFwdSection (I := I) Phi Xs)
      (pushFwdSection (I := I) Phi Ys)
      (pushFwdSection (I := I) Phi Zs)
      (pushFwdSection (I := I) Phi Ws) (Phi x)
  rw [show DifferentialGeometry.Geometry.Curvature.CovariantDerivative.riemannCurvature04At
        (Diffeomorph.pullbackMetric (I := I) g Phi)
        (metricCov (I := I) (M := M) (Diffeomorph.pullbackMetric (I := I) g Phi))
        (metricCov_smooth (I := I) (M := M)
          (Diffeomorph.pullbackMetric (I := I) g Phi))
        x (vec4 X Y Z W) =
      (Diffeomorph.pullbackMetric (I := I) g Phi).inner x W
        (DifferentialGeometry.Geometry.Curvature.connectionRiemannCurvatureField
          (I := I)
          (metricCov (I := I) (M := M) (Diffeomorph.pullbackMetric (I := I) g Phi))
          (fun p : M => Xs p) (fun p : M => Ys p) (fun p : M => Zs p) x) by
        simpa [hXs, hYs, hZs, hWs] using hleft]
  rw [show DifferentialGeometry.Geometry.Curvature.CovariantDerivative.riemannCurvature04At
        g (metricCov (I := I) (M := N) g)
        (metricCov_smooth (I := I) (M := N) g)
        (Phi x)
        (vec4 (mfderiv I I (Phi : M -> N) x X)
          (mfderiv I I (Phi : M -> N) x Y)
          (mfderiv I I (Phi : M -> N) x Z)
          (mfderiv I I (Phi : M -> N) x W)) =
      g.inner (Phi x) (mfderiv I I (Phi : M -> N) x W)
        (DifferentialGeometry.Geometry.Curvature.connectionRiemannCurvatureField
          (I := I) (metricCov (I := I) (M := N) g)
          (fun q : N => pushFwdSection (I := I) Phi Xs q)
          (fun q : N => pushFwdSection (I := I) Phi Ys q)
          (fun q : N => pushFwdSection (I := I) Phi Zs q) (Phi x)) by
        simpa [hXs, hYs, hZs, hWs] using hright]
  rw [Diffeomorph.pullbackMetric_inner]
  rw [connectionRiemannCurvatureField_pullback_pushFwd
    (I := I) g Phi Xs Ys Zs x]

end DifferentialGeometry.Geometry.Curvature
