import DifferentialGeometry.Geometry.Connection.LeviCivita.Defs
import DifferentialGeometry.Geometry.Connection.LeviCivita.Smooth.Connection
import DifferentialGeometry.Geometry.Operator.Laplacian
import DifferentialGeometry.Geometry.Operator.LaplacianBridge
import DifferentialGeometry.Geometry.Operator.HessianTraceRealization
import DifferentialGeometry.Geometry.Operator.RoughLaplacian
import DifferentialGeometry.Tensor.RSTensor.MetricCompatibility
import DifferentialGeometry.Tensor.RSTensor.NablaDomDomCongr
import DifferentialGeometry.Tensor.RSTensor.NablaOnTensors.Regularity.TotalNabla0S
import DifferentialGeometry.Tensor.RSTensor.ProductNablaLeibniz

set_option autoImplicit false

noncomputable section

open Bundle Manifold
open scoped Manifold ContDiff

namespace DifferentialGeometry.Geometry.Operator

open DifferentialGeometry.Tensor0SBundle
open DifferentialGeometry.Geometry.Connection

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace Real E]
  [FiniteDimensional Real E] [NeZero (Module.finrank Real E)]
variable {H : Type*} [TopologicalSpace H]
variable {I : ModelWithCorners Real E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
variable [SigmaCompactSpace M] [T2Space M] [I.Boundaryless]

def weightedLaplacian
    (g : SmoothRiemannianMetric I M) (f u : C^∞⟮I, M; Real⟯) : M → Real :=
  fun x => ΔG (I := I) g u x -
    g.inner x (gradFun (I := I) g f x) (gradFun (I := I) g u x)

omit [NeZero (Module.finrank Real E)] [SigmaCompactSpace M] [T2Space M] in
@[simp]
theorem weightedLaplacian_apply
    (g : SmoothRiemannianMetric I M) (f u : C^∞⟮I, M; Real⟯) (x : M) :
    weightedLaplacian (I := I) g f u x = ΔG (I := I) g u x -
      g.inner x (gradFun (I := I) g f x) (gradFun (I := I) g u x) := rfl

open DifferentialGeometry.Integral.DivergenceTheorem in
omit [NeZero (Module.finrank Real E)] [SigmaCompactSpace M] in
theorem weightedLaplacian_contMDiff
    (g : SmoothRiemannianMetric I M) (f u : C^∞⟮I, M; Real⟯) :
    ContMDiff I (modelWithCornersSelf Real Real) ∞
      (weightedLaplacian (I := I) g f u) := by
  let V : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯ := gradG (I := I) g u
  have hinner : ContMDiff I (modelWithCornersSelf Real Real) ∞
      (fun x : M =>
        g.inner x (gradFun (I := I) g f x) (gradFun (I := I) g u x)) := by
    have hact := tangentSectionAction_contMDiff (I := I) V f.contMDiff
    have heq : (fun x : M =>
        g.inner x (gradFun (I := I) g f x) (gradFun (I := I) g u x)) =
        tangentSectionAction (I := I) V f := by
      funext x
      rw [tangentSectionAction_eq_inner_grad_g (I := I) g f V x]
      simp only [V, grad_g_apply]
      exact g.symm x _ _
    rw [heq]
    exact hact
  exact (Δ_g_contMDiff (I := I) g u).sub hinner

omit [NeZero (Module.finrank Real E)] [SigmaCompactSpace M] [T2Space M] in
theorem weightedLaplacian_add
    (g : SmoothRiemannianMetric I M) (f u v : C^∞⟮I, M; Real⟯) (x : M) :
    weightedLaplacian (I := I) g f (u + v) x =
      weightedLaplacian (I := I) g f u x +
        weightedLaplacian (I := I) g f v x := by
  rw [weightedLaplacian_apply, weightedLaplacian_apply,
    weightedLaplacian_apply, Δ_g_add]
  have hgrad : gradFun (I := I) g (u + v) x =
      gradFun (I := I) g u x + gradFun (I := I) g v x := by
    simpa only [ContMDiffMap.coe_add] using
      Operator.gradFun_add (I := I) g
        ((u.contMDiff x).mdifferentiableAt (by simp))
        ((v.contMDiff x).mdifferentiableAt (by simp))
  simp only [ContMDiffMap.coe_add]
  rw [hgrad]
  simp only [map_add]
  ring

omit [NeZero (Module.finrank Real E)] [SigmaCompactSpace M] in
theorem weightedLaplacian_const_smul
    (g : SmoothRiemannianMetric I M) (f u : C^∞⟮I, M; Real⟯)
    (a : Real) (x : M) :
    weightedLaplacian (I := I) g f (a • u) x =
      a * weightedLaplacian (I := I) g f u x := by
  have hgrad : MDiffAt
      (T% fun y : M => gradientFun (I := I) g u y) x :=
    (gradientFun_contMDiffAt (I := I) g (u.contMDiff x)).mdifferentiableAt
      (by simp)
  have hlap := laplacian_const_smul (I := I) (LeviCivita (I := I) g) g a
    (fun y => (u.contMDiff y).mdifferentiableAt (by simp)) hgrad
  have hscaled :
      ΔG (I := I) g (a • u) x =
        laplacian (I := I) (LeviCivita (I := I) g) g (a • u : M → Real) x :=
    (laplacian_levi_eq (I := I) g (a • u).contMDiff x).symm
  have hraw :
      ΔG (I := I) g u x =
        laplacian (I := I) (LeviCivita (I := I) g) g (u : M → Real) x :=
    (laplacian_levi_eq (I := I) g u.contMDiff x).symm
  rw [weightedLaplacian_apply, weightedLaplacian_apply,
    hscaled, hraw, hlap]
  have hgradScaled : gradFun (I := I) g (a • u) x =
      a • gradFun (I := I) g u x := by
    simpa only [ContMDiffMap.coe_smul] using
      Operator.gradFun_const_smul (I := I) g a
        ((u.contMDiff x).mdifferentiableAt (by simp))
  simp only [ContMDiffMap.coe_smul]
  rw [hgradScaled]
  simp only [map_smul, smul_eq_mul]
  ring

omit [NeZero (Module.finrank Real E)] [SigmaCompactSpace M] [T2Space M] in
theorem weightedLaplacian_const
    (g : SmoothRiemannianMetric I M) (f : C^∞⟮I, M; Real⟯)
    (c : Real) (x : M) :
    weightedLaplacian (I := I) g f (ContMDiffMap.const c) x = 0 := by
  rw [weightedLaplacian_apply, Δ_g_const]
  change 0 - g.inner x (gradFun (I := I) g f x)
    (gradFun (I := I) g (fun _ : M => c) x) = 0
  rw [Operator.gradFun_const]
  simp

omit [NeZero (Module.finrank Real E)] [SigmaCompactSpace M] in
theorem weightedLaplacian_sub_const
    (g : SmoothRiemannianMetric I M) (f u : C^∞⟮I, M; Real⟯)
    (c : Real) (x : M) :
    weightedLaplacian (I := I) g f (u - ContMDiffMap.const c) x =
      weightedLaplacian (I := I) g f u x := by
  rw [sub_eq_add_neg, ← neg_one_smul Real (ContMDiffMap.const c),
    weightedLaplacian_add, weightedLaplacian_const_smul,
    weightedLaplacian_const]
  ring

omit [NeZero (Module.finrank Real E)] [SigmaCompactSpace M] in
theorem weightedLaplacian_mul
    (g : SmoothRiemannianMetric I M) (f u v : C^∞⟮I, M; Real⟯) (x : M) :
    weightedLaplacian (I := I) g f (u * v) x =
      u x * weightedLaplacian (I := I) g f v x +
        v x * weightedLaplacian (I := I) g f u x +
          2 * g.inner x (gradFun (I := I) g u x) (gradFun (I := I) g v x) := by
  have hu : ∀ᶠ y in nhds x,
      MDifferentiableAt I 𝓘(Real, Real) (u : M → Real) y :=
    Filter.Eventually.of_forall fun y => (u.contMDiff y).mdifferentiableAt (by simp)
  have hv : ∀ᶠ y in nhds x,
      MDifferentiableAt I 𝓘(Real, Real) (v : M → Real) y :=
    Filter.Eventually.of_forall fun y => (v.contMDiff y).mdifferentiableAt (by simp)
  have hgradu : MDiffAt (T% fun y : M => gradientFun (I := I) g u y) x :=
    (gradientFun_contMDiffAt (I := I) g (u.contMDiff x)).mdifferentiableAt (by simp)
  have hgradv : MDiffAt (T% fun y : M => gradientFun (I := I) g v y) x :=
    (gradientFun_contMDiffAt (I := I) g (v.contMDiff x)).mdifferentiableAt (by simp)
  have hlap := laplacian_mul_at (I := I) (LeviCivita (I := I) g) g
    hu hv hgradu hgradv
  let uv : C^∞⟮I, M; Real⟯ :=
    ⟨fun y : M => u y * v y, (u * v).contMDiff⟩
  have huv : uv = u * v := by
    ext y
    rfl
  have huvBridge :
      laplacian (I := I) (LeviCivita (I := I) g) g
          (fun y : M => u y * v y) x =
        ΔG (I := I) g (u * v) x := by
    calc
      _ = laplacian (I := I) (LeviCivita (I := I) g) g (uv : M → Real) x := rfl
      _ = ΔG (I := I) g uv x :=
        laplacian_levi_eq (I := I) g uv.contMDiff x
      _ = ΔG (I := I) g (u * v) x := by rw [huv]
  have huBridge :
      laplacian (I := I) (LeviCivita (I := I) g) g (u : M → Real) x =
        ΔG (I := I) g u x :=
    laplacian_levi_eq (I := I) g u.contMDiff x
  have hvBridge :
      laplacian (I := I) (LeviCivita (I := I) g) g (v : M → Real) x =
        ΔG (I := I) g v x :=
    laplacian_levi_eq (I := I) g v.contMDiff x
  have hlap' :
      ΔG (I := I) g (u * v) x =
        u x * ΔG (I := I) g v x + v x * ΔG (I := I) g u x +
          2 * g.inner x (gradFun (I := I) g u x)
            (gradFun (I := I) g v x) := by
    calc
      ΔG (I := I) g (u * v) x =
          laplacian (I := I) (LeviCivita (I := I) g) g
            (fun y : M => u y * v y) x := huvBridge.symm
      _ = u x * laplacian (I := I) (LeviCivita (I := I) g) g v x +
            v x * laplacian (I := I) (LeviCivita (I := I) g) g u x +
              2 * g.inner x (gradientFun (I := I) g u x)
                (gradientFun (I := I) g v x) := hlap
      _ = _ := by rw [huBridge, hvBridge, Connection.gradient_eq_gradFun,
        Connection.gradient_eq_gradFun]
  have hgradmul :
      gradFun (I := I) g ((u * v : C^∞⟮I, M; Real⟯) : M → Real) x =
        u x • gradFun (I := I) g v x + v x • gradFun (I := I) g u x := by
    rw [← huv]
    change gradFun (I := I) g (fun y : M => u y * v y) x = _
    have h := gradientFun_mul (I := I) g
      ((u.contMDiff x).mdifferentiableAt (by simp))
      ((v.contMDiff x).mdifferentiableAt (by simp))
    simpa only [Connection.gradient_eq_gradFun] using h
  rw [weightedLaplacian_apply, weightedLaplacian_apply,
    weightedLaplacian_apply, hlap', hgradmul]
  simp only [map_add, map_smul, smul_eq_mul]
  ring

omit [FiniteDimensional Real E] [NeZero (Module.finrank Real E)]
    [SigmaCompactSpace M] [T2Space M] [I.Boundaryless] [IsManifold I ∞ M] in
private theorem contMDiff_rpow_const_of_pos
    {u : C^∞⟮I, M; Real⟯} {p : Real} (hpos : ∀ y : M, 0 < u y) :
    ContMDiff I 𝓘(Real, Real) ∞ (fun y : M => u y ^ p) := by
  intro y
  exact (Real.contDiffAt_rpow_const_of_ne (p := p) (hpos y).ne').comp_contMDiffAt
    (u.contMDiff.contMDiffAt)

omit [NeZero (Module.finrank Real E)] [SigmaCompactSpace M] in
theorem weightedLaplacian_rpow
    (g : SmoothRiemannianMetric I M) (f u : C^∞⟮I, M; Real⟯)
    (p : Real) (hpos : ∀ y : M, 0 < u y) (x : M) :
    let up : C^∞⟮I, M; Real⟯ :=
      ⟨fun y : M => u y ^ p, contMDiff_rpow_const_of_pos (I := I) hpos⟩
    weightedLaplacian (I := I) g f up x =
      (p * u x ^ (p - 1)) * weightedLaplacian (I := I) g f u x +
        (p * (p - 1) * u x ^ (p - 2)) *
          g.inner x (gradFun (I := I) g u x) (gradFun (I := I) g u x) := by
  let up : C^∞⟮I, M; Real⟯ :=
    ⟨fun y : M => u y ^ p, contMDiff_rpow_const_of_pos (I := I) hpos⟩
  change weightedLaplacian (I := I) g f up x = _
  have hu : ∀ y : M,
      MDifferentiableAt I 𝓘(Real, Real) (u : M → Real) y :=
    fun y => (u.contMDiff y).mdifferentiableAt (by simp)
  have hgradu : MDiffAt (T% fun y : M => gradientFun (I := I) g u y) x :=
    (gradientFun_contMDiffAt (I := I) g (u.contMDiff x)).mdifferentiableAt (by simp)
  have hlap := laplacian_rpow (I := I) (LeviCivita (I := I) g) g p hu hpos hgradu
  have hupBridge :
      laplacian (I := I) (LeviCivita (I := I) g) g
          (fun y : M => u y ^ p) x =
        ΔG (I := I) g up x := by
    calc
      _ = laplacian (I := I) (LeviCivita (I := I) g) g (up : M → Real) x := rfl
      _ = ΔG (I := I) g up x :=
        laplacian_levi_eq (I := I) g up.contMDiff x
  have huBridge :
      laplacian (I := I) (LeviCivita (I := I) g) g (u : M → Real) x =
        ΔG (I := I) g u x :=
    laplacian_levi_eq (I := I) g u.contMDiff x
  have hlap' :
      ΔG (I := I) g up x =
        (p * u x ^ (p - 1)) * ΔG (I := I) g u x +
          (p * (p - 1) * u x ^ (p - 2)) *
            g.inner x (gradFun (I := I) g u x)
              (gradFun (I := I) g u x) := by
    calc
      ΔG (I := I) g up x =
          laplacian (I := I) (LeviCivita (I := I) g) g
            (fun y : M => u y ^ p) x := hupBridge.symm
      _ = (p * u x ^ (p - 1)) *
            laplacian (I := I) (LeviCivita (I := I) g) g u x +
          (p * (p - 1) * u x ^ (p - 2)) *
            g.inner x (gradientFun (I := I) g u x)
              (gradientFun (I := I) g u x) := hlap
      _ = _ := by rw [huBridge, Connection.gradient_eq_gradFun]
  have hgradpow :
      gradFun (I := I) g up x =
        (p * u x ^ (p - 1)) • gradFun (I := I) g u x := by
    change gradFun (I := I) g (fun y : M => u y ^ p) x = _
    have h := gradientFun_rpow (I := I) g p (hu x) (hpos x)
    simpa only [Connection.gradient_eq_gradFun] using h
  rw [weightedLaplacian_apply, weightedLaplacian_apply, hlap', hgradpow]
  simp only [map_smul, smul_eq_mul]
  ring

omit [NeZero (Module.finrank Real E)] [SigmaCompactSpace M] in
theorem weightedLaplacian_mul_rpow
    (g : SmoothRiemannianMetric I M) (f u v : C^∞⟮I, M; Real⟯)
    (p : Real) (hpos : ∀ y : M, 0 < v y) (x : M) :
    let vp : C^∞⟮I, M; Real⟯ :=
      ⟨fun y : M => v y ^ p, contMDiff_rpow_const_of_pos (I := I) hpos⟩
    weightedLaplacian (I := I) g f (u * vp) x =
      v x ^ p * weightedLaplacian (I := I) g f u x +
        p * u x * v x ^ (p - 1) * weightedLaplacian (I := I) g f v x +
        p * (p - 1) * u x * v x ^ (p - 2) *
          g.inner x (gradFun (I := I) g v x) (gradFun (I := I) g v x) +
        2 * p * v x ^ (p - 1) *
          g.inner x (gradFun (I := I) g u x) (gradFun (I := I) g v x) := by
  let vp : C^∞⟮I, M; Real⟯ :=
    ⟨fun y : M => v y ^ p, contMDiff_rpow_const_of_pos (I := I) hpos⟩
  change weightedLaplacian (I := I) g f (u * vp) x = _
  have hmul := weightedLaplacian_mul (I := I) g f u vp x
  have hpow := weightedLaplacian_rpow (I := I) g f v p hpos x
  have hv : MDifferentiableAt I 𝓘(Real, Real) (v : M → Real) x :=
    (v.contMDiff x).mdifferentiableAt (by simp)
  have hgrad :
      gradFun (I := I) g vp x =
        (p * v x ^ (p - 1)) • gradFun (I := I) g v x := by
    change gradFun (I := I) g (fun y : M => v y ^ p) x = _
    have h := gradientFun_rpow (I := I) g p hv (hpos x)
    simpa only [Connection.gradient_eq_gradFun] using h
  have hvp : vp x = v x ^ p := rfl
  rw [hmul, hpow, hgrad, hvp]
  simp only [map_smul, smul_eq_mul]
  ring_nf

omit [NeZero (Module.finrank Real E)] [SigmaCompactSpace M] in
theorem weightedLaplacian_mul_inv_sq
    (g : SmoothRiemannianMetric I M) (f u v : C^∞⟮I, M; Real⟯)
    (hpos : ∀ y : M, 0 < v y) (x : M) :
    let vInvSq : C^∞⟮I, M; Real⟯ :=
      ⟨fun y : M => v y ^ (-2 : Real),
        contMDiff_rpow_const_of_pos (I := I) hpos⟩
    weightedLaplacian (I := I) g f (u * vInvSq) x =
      v x ^ (-2 : Real) * weightedLaplacian (I := I) g f u x -
        2 * u x * v x ^ (-3 : Real) * weightedLaplacian (I := I) g f v x +
        6 * u x * v x ^ (-4 : Real) *
          g.inner x (gradFun (I := I) g v x) (gradFun (I := I) g v x) -
        4 * v x ^ (-3 : Real) *
          g.inner x (gradFun (I := I) g u x) (gradFun (I := I) g v x) := by
  let vInvSq : C^∞⟮I, M; Real⟯ :=
    ⟨fun y : M => v y ^ (-2 : Real),
      contMDiff_rpow_const_of_pos (I := I) hpos⟩
  change weightedLaplacian (I := I) g f (u * vInvSq) x = _
  have h := weightedLaplacian_mul_rpow (I := I) g f u v (-2 : Real) hpos x
  change weightedLaplacian (I := I) g f (u * vInvSq) x = _ at h
  convert h using 1
  all_goals ring_nf

def weightedRoughLaplacian0S
    (g : SmoothRiemannianMetric I M) (f : C^∞⟮I, M; Real⟯) {s : Nat}
    (A : Tensor0SField (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      (n := (∞ : WithTop ℕ∞)) s) (x : M) :
    Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) s x := by
  let cov := DifferentialGeometry.Geometry.Connection.LeviCivita (I := I) g
  let hcov : CovariantDerivative.ContMDiffCovariantDerivativeLocally cov
      (∞ : WithTop ℕ∞) := by
    simpa [cov, DifferentialGeometry.Geometry.Connection.LeviCivita] using
      (DifferentialGeometry.Geometry.Connection.leviCivitaConnectionOfMetric_contMDiffCovariantDerivativeLocally
        (I := I) g)
  let hA := totalNabla0S_reg (E := E) (H := H) (I := I) (M := M) s cov hcov A
  let nablaA := totalNabla0S (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
    s cov A hA
  let hnablaA := totalNabla0S_reg (E := E) (H := H) (I := I) (M := M)
    (s + 1) cov hcov nablaA
  exact roughLap0STensor (I := I) g
      (totalNabla0SFun (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
        (s + 1) cov nablaA x) -
    tensor0SCurry (I := I) (𝕜 := Real) (M := M) s x
      (totalNabla0SFun (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
        s cov A x)
      (gradFun (I := I) g f x)

omit [NeZero (Module.finrank Real E)] [SigmaCompactSpace M]
    [I.Boundaryless] in
theorem weightedRoughLaplacian0S_sub
    (g : SmoothRiemannianMetric I M) (f : C^∞⟮I, M; Real⟯) {s : Nat}
    (A B : Tensor0SField (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      (n := (∞ : WithTop ℕ∞)) s) (x : M) :
    weightedRoughLaplacian0S (I := I) g f (A - B) x =
      weightedRoughLaplacian0S (I := I) g f A x -
        weightedRoughLaplacian0S (I := I) g f B x := by
  let cov := LeviCivita (I := I) g
  let hcov : CovariantDerivative.ContMDiffCovariantDerivativeLocally cov ∞ := by
    simpa [cov, LeviCivita] using
      (leviCivitaConnectionOfMetric_contMDiffCovariantDerivativeLocally
        (I := I) (M := M) g)
  let C := A - B
  let nablaA := totalNabla0S (I := I) s cov A
    (totalNabla0S_reg (I := I) s cov hcov A)
  let nablaB := totalNabla0S (I := I) s cov B
    (totalNabla0S_reg (I := I) s cov hcov B)
  let nablaC := totalNabla0S (I := I) s cov C
    (totalNabla0S_reg (I := I) s cov hcov C)
  let nabla2A := totalNabla0S (I := I) (s + 1) cov nablaA
    (totalNabla0S_reg (I := I) (s + 1) cov hcov nablaA)
  let nabla2B := totalNabla0S (I := I) (s + 1) cov nablaB
    (totalNabla0S_reg (I := I) (s + 1) cov hcov nablaB)
  let nabla2C := totalNabla0S (I := I) (s + 1) cov nablaC
    (totalNabla0S_reg (I := I) (s + 1) cov hcov nablaC)
  have hAreal : TotalNabla0SRealizes (I := I) s cov A nablaA :=
    totalNabla0S_realizes (I := I) s cov A _
  have hBreal : TotalNabla0SRealizes (I := I) s cov B nablaB :=
    totalNabla0S_realizes (I := I) s cov B _
  have hCreal : TotalNabla0SRealizes (I := I) s cov C (nablaA - nablaB) := by
    have hsub := hAreal.add (hBreal.smul (-1))
    simpa [C, sub_eq_add_neg, neg_smul] using hsub
  have hCcan : TotalNabla0SRealizes (I := I) s cov C nablaC :=
    totalNabla0S_realizes (I := I) s cov C _
  have hnablaC : nablaC = nablaA - nablaB :=
    totalNabla0SRealizes_unique (I := I) hCcan hCreal
  have hA2real : TotalNabla0SRealizes (I := I) (s + 1) cov nablaA nabla2A :=
    totalNabla0S_realizes (I := I) (s + 1) cov nablaA _
  have hB2real : TotalNabla0SRealizes (I := I) (s + 1) cov nablaB nabla2B :=
    totalNabla0S_realizes (I := I) (s + 1) cov nablaB _
  have hC2real : TotalNabla0SRealizes (I := I) (s + 1) cov
      (nablaA - nablaB) (nabla2A - nabla2B) := by
    have hsub := hA2real.add (hB2real.smul (-1))
    simpa [sub_eq_add_neg, neg_smul] using hsub
  have hC2can : TotalNabla0SRealizes (I := I) (s + 1) cov nablaC nabla2C :=
    totalNabla0S_realizes (I := I) (s + 1) cov nablaC _
  have hC2can' : TotalNabla0SRealizes (I := I) (s + 1) cov
      (nablaA - nablaB) nabla2C := by
    simpa [hnablaC] using hC2can
  have hnabla2C : nabla2C = nabla2A - nabla2B :=
    totalNabla0SRealizes_unique (I := I) hC2can' hC2real
  apply tensor0SSpace_ext (I := I) s x
  intro tail
  rw [weightedRoughLaplacian0S, weightedRoughLaplacian0S,
    weightedRoughLaplacian0S]
  change (roughLap0STensor (I := I) g (nabla2C x) -
      tensor0SCurry (I := I) (s := s) x (nablaC x)
        (gradFun (I := I) g f x)) tail =
    ((roughLap0STensor (I := I) g (nabla2A x) -
        tensor0SCurry (I := I) (s := s) x (nablaA x)
          (gradFun (I := I) g f x)) -
      (roughLap0STensor (I := I) g (nabla2B x) -
        tensor0SCurry (I := I) (s := s) x (nablaB x)
          (gradFun (I := I) g f x))) tail
  rw [hnablaC, hnabla2C]
  simp only [Tensor0SSpace.sub_apply, roughLap0STensor_apply,
    tensor0S_curry_apply_cons]
  change metricTraceFirstTwo0SAt (I := I) g (nabla2A x - nabla2B x) tail -
      (nablaA x - nablaB x) (Fin.cons (gradFun (I := I) g f x) tail) = _
  rw [metricTraceFirstTwo0SAt_sub]
  rw [Tensor0SSpace.sub_apply]
  ring

omit [NeZero (Module.finrank Real E)] [SigmaCompactSpace M] in
theorem weightedRoughLaplacian0S_smul_metric
    (g : SmoothRiemannianMetric I M) (f u : C^∞⟮I, M; Real⟯) (x : M) :
    weightedRoughLaplacian0S (I := I) g f
        (tensor0SFieldSmulByFun (I := I) (n := (∞ : WithTop ℕ∞)) (s := 2)
          (u : M → Real) u.contMDiff (metricTensorField (I := I) g)) x =
      weightedLaplacian (I := I) g f u x • metricTensorField (I := I) g x := by
  classical
  let cov := LeviCivita (I := I) g
  let hcov : CovariantDerivative.ContMDiffCovariantDerivativeLocally cov ∞ := by
    simpa [cov, LeviCivita] using
      (leviCivitaConnectionOfMetric_contMDiffCovariantDerivativeLocally
        (I := I) (M := M) g)
  have hmc : IsMetricCompatibleGen (I := I) cov g := by
    simpa [cov, LeviCivita] using
      (leviCivitaConnectionOfMetric_isMetricCompatible (I := I) g)
  let metric := metricTensorField (I := I) g
  let U := tensor0SFieldSmulByFun (I := I) (n := (∞ : WithTop ℕ∞)) (s := 2)
    (u : M → Real) u.contMDiff metric
  let du := duSec (I := I) (u : M → Real) u.contMDiff
  let Hess := hessianSec (I := I) cov hcov (u : M → Real) u.contMDiff
  let nablaU := totalNabla0S (I := I) 2 cov U
    (totalNabla0S_reg (I := I) 2 cov hcov U)
  let nabla2U := totalNabla0S (I := I) 3 cov nablaU
    (totalNabla0S_reg (I := I) 3 cov hcov nablaU)
  have hUreal : TotalNabla0SRealizes (I := I) 2 cov U nablaU :=
    totalNabla0S_realizes (I := I) 2 cov U _
  have hUexplicit : TotalNabla0SRealizes (I := I) 2 cov U
      (tensor0SFieldProduct (∞ : WithTop ℕ∞) (s := 1) (q := 2) du metric) := by
    exact nabla_smul_metric (I := I) (M := M) cov g hmc
      (u : M → Real) u.contMDiff du (fun y v => by
        rw [duSec_apply]
        exact differential1FormFun_apply_eq_mvfderiv (I := I) (u : M → Real) y v)
  have hnablaU : nablaU =
      tensor0SFieldProduct (∞ : WithTop ℕ∞) (s := 1) (q := 2) du metric :=
    totalNabla0SRealizes_unique (I := I) hUreal hUexplicit
  have hduReal : TotalNabla0SRealizes (I := I) 1 cov du Hess := by
    exact totalNabla0S_realizes (I := I) 1 cov du _
  have hmetricReal : TotalNabla0SRealizes (I := I) 2 cov metric 0 := by
    simpa [metric] using zero_realizes_metric (I := I) cov g hmc
  have hsecondExplicit : TotalNabla0SRealizes (I := I) 3 cov
      (tensor0SFieldProduct (∞ : WithTop ℕ∞) (s := 1) (q := 2) du metric)
      (tensor0SFieldProduct (∞ : WithTop ℕ∞) (s := 2) (q := 2) Hess metric) := by
    have hprod := nabla0S_product_realizes (I := I) cov du metric Hess 0
      hduReal hmetricReal
    simpa [leibnizLeftEquiv] using hprod
  have hsecondCanonical : TotalNabla0SRealizes (I := I) 3 cov nablaU nabla2U :=
    totalNabla0S_realizes (I := I) 3 cov nablaU _
  have hsecondCanonical' : TotalNabla0SRealizes (I := I) 3 cov
      (tensor0SFieldProduct (∞ : WithTop ℕ∞) (s := 1) (q := 2) du metric) nabla2U := by
    simpa [hnablaU] using hsecondCanonical
  have hnabla2U : nabla2U =
      tensor0SFieldProduct (∞ : WithTop ℕ∞) (s := 2) (q := 2) Hess metric :=
    totalNabla0SRealizes_unique (I := I) hsecondCanonical' hsecondExplicit
  let D := (tangentMetricDataGen (I := I) g x).metric
  let : InnerProductSpace.Core Real (TangentSpace I x) := D.toCore
  let : NormedAddCommGroup (TangentSpace I x) :=
    @InnerProductSpace.Core.toNormedAddCommGroup Real (TangentSpace I x) _ _ _ D.toCore
  let : InnerProductSpace Real (TangentSpace I x) :=
    @InnerProductSpace.ofCore Real (TangentSpace I x) _ _ _ D.toCore.toCore
  let ob := stdOrthonormalBasis Real (TangentSpace I x)
  let basis : Module.Basis (Fin (Module.finrank Real (TangentSpace I x))) Real
      (TangentSpace I x) := ob.toBasis
  have horth : ∀ i j : Fin (Module.finrank Real (TangentSpace I x)),
      g.inner x (basis i) (basis j) = if i = j then 1 else 0 := by
    intro i j
    have hinner : Inner.inner Real (ob i) (ob j) = D.inner (ob i) (ob j) :=
      MetricFiberData.toCore_inner D (ob i) (ob j)
    change D.inner (ob i) (ob j) = if i = j then 1 else 0
    rw [← hinner]
    exact ob.inner_eq_ite i j
  have hinv : MetricInverseInBasisGen (I := I) g x basis
      (identityInvMetric (Idx := Fin (Module.finrank Real (TangentSpace I x)))) :=
    metricInverseInBasis_identity_of_orthonormal (I := I) g basis horth
  have hrough : ∀ tail : Fin 2 → TangentSpace I x,
      roughLap0STensor (I := I) g (nabla2U x) tail =
        metricTraceFirstTwo0SAt (I := I) g (Hess x) Fin.elim0 * metric x tail := by
    intro tail
    rw [hnabla2U]
    exact roughLap_smul_par (I := I) g basis
      (identityInvMetric (Idx := Fin (Module.finrank Real (TangentSpace I x)))) hinv
      (u x) (du x) (Hess x) (metric x) 0 0
      (tensor0SFieldProduct (∞ : WithTop ℕ∞) (s := 2) (q := 2) Hess metric x) tail
      (by intro X tail'; rfl)
      (by intro X Y tail'; rfl)
      (by
        intro X Y tail'
        rw [tensor0SField_product_apply]
        simp only [zero_apply, mul_zero, add_zero]
        have hleft : metricTraceInput (I := I) X Y tail' ∘ Fin.castAdd 2 =
            metricTraceInput (I := I) X Y Fin.elim0 := by
          funext a
          fin_cases a <;> rfl
        have hright : metricTraceInput (I := I) X Y tail' ∘ Fin.natAdd 2 = tail' := by
          funext a
          fin_cases a <;> rfl
        rw [hleft, hright])
  have hlap : laplacian (I := I) cov g (u : M → Real) x =
      metricTraceFirstTwo0SAt (I := I) g (Hess x) Fin.elim0 := by
    exact scalarLap_smooth (I := I) cov hcov g hmc (u : M → Real) u.contMDiff
  apply tensor0SSpace_ext (I := I) 2 x
  intro tail
  rw [weightedRoughLaplacian0S]
  change (roughLap0STensor (I := I) g (nabla2U x) -
      tensor0SCurry (I := I) (s := 2) x (nablaU x)
        (gradFun (I := I) g f x)) tail = _
  rw [Tensor0SSpace.sub_apply, hrough, hnablaU]
  rw [tensor0S_curry_apply_cons, tensor0SField_product_apply]
  rw [Tensor0SSpace.smul_apply]
  change
    metricTraceFirstTwo0SAt (I := I) g (Hess x) Fin.elim0 * metric x tail -
        du x (fun _ : Fin 1 => gradFun (I := I) g f x) * metric x tail =
      weightedLaplacian (I := I) g f u x * metric x tail
  rw [← hlap]
  rw [show du x (fun _ : Fin 1 => gradFun (I := I) g f x) =
      g.inner x (gradFun (I := I) g f x) (gradFun (I := I) g u x) by
    rw [duSec_apply, differential1FormFun_apply_eq_inner_gradientFun]
    exact g.symm x _ _]
  rw [weightedLaplacian_apply]
  have hlapLevi : laplacian (I := I) cov g (u : M → Real) x =
      ΔG (I := I) g u x := by
    let u' : C^∞⟮I, M; Real⟯ := ⟨(u : M → Real), u.contMDiff⟩
    have hu' : u' = u := by
      ext y
      rfl
    rw [← hu']
    simpa [cov, u'] using laplacian_levi_eq (I := I) g u.contMDiff x
  rw [hlapLevi]
  ring

omit [NeZero (Module.finrank Real E)] [SigmaCompactSpace M] [I.Boundaryless] in
theorem weightedRoughLaplacian0S_sub_const_smul_metric
    (g : SmoothRiemannianMetric I M) (f : C^∞⟮I, M; Real⟯)
    (A : Tensor0SField (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      (n := (∞ : WithTop ℕ∞)) 2)
    (c : Real) (x : M) :
    weightedRoughLaplacian0S (I := I) g f
        (A - c • metricTensorField (I := I) g) x =
      weightedRoughLaplacian0S (I := I) g f A x := by
  let cov := LeviCivita (I := I) g
  let hcov : CovariantDerivative.ContMDiffCovariantDerivativeLocally cov
      (∞ : WithTop ℕ∞) := by
    simpa [cov, LeviCivita] using
      (leviCivitaConnectionOfMetric_contMDiffCovariantDerivativeLocally
        (I := I) (M := M) g)
  let metric := metricTensorField (I := I) g
  let B := A - c • metric
  let nablaA := totalNabla0S (I := I) 2 cov A
    (totalNabla0S_reg (I := I) 2 cov hcov A)
  let nablaB := totalNabla0S (I := I) 2 cov B
    (totalNabla0S_reg (I := I) 2 cov hcov B)
  have hmc : IsMetricCompatibleGen (I := I) cov g := by
    simpa [cov, LeviCivita] using
      (leviCivitaConnectionOfMetric_isMetricCompatible (I := I) g)
  have hAreal : TotalNabla0SRealizes (I := I) 2 cov A nablaA :=
    totalNabla0S_realizes (I := I) 2 cov A _
  have hmetricReal : TotalNabla0SRealizes (I := I) 2 cov metric 0 := by
    simpa [metric] using zero_realizes_metric (I := I) cov g hmc
  have hBreal : TotalNabla0SRealizes (I := I) 2 cov B nablaA := by
    have hsum := hAreal.add (hmetricReal.smul (-c))
    simpa [B, sub_eq_add_neg, neg_smul] using hsum
  have hBcan : TotalNabla0SRealizes (I := I) 2 cov B nablaB :=
    totalNabla0S_realizes (I := I) 2 cov B _
  have hnabla : nablaB = nablaA :=
    totalNabla0SRealizes_unique (I := I) hBcan hBreal
  unfold weightedRoughLaplacian0S
  change roughLap0STensor (I := I) g
      (totalNabla0SFun (I := I) 3 cov nablaB x) -
        tensor0SCurry (I := I) (𝕜 := Real) (M := M) 2 x
          (totalNabla0SFun (I := I) 2 cov B x)
          (gradFun (I := I) g f x) =
    roughLap0STensor (I := I) g
      (totalNabla0SFun (I := I) 3 cov nablaA x) -
        tensor0SCurry (I := I) (𝕜 := Real) (M := M) 2 x
          (totalNabla0SFun (I := I) 2 cov A x)
          (gradFun (I := I) g f x)
  rw [hnabla]
  have hfirst : totalNabla0SFun (I := I) 2 cov B x =
      totalNabla0SFun (I := I) 2 cov A x := by
    have hpoint := congrArg (fun T => T x) hnabla
    simpa [nablaA, nablaB, B] using hpoint
  rw [hfirst]

end DifferentialGeometry.Geometry.Operator
