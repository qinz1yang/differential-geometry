import DifferentialGeometry.Geometry.Connection.ChartBridge.Hessian
import DifferentialGeometry.Geometry.Operator.LaplacianMinimum
import DifferentialGeometry.Geometry.Connection.Hessian.Scalar
import DifferentialGeometry.Geometry.Connection.Laplacian.VectorBundleTrace
import DifferentialGeometry.Topology.Manifold.Curve
import DifferentialGeometry.Analysis.Calculus.LocalExtrema

set_option autoImplicit false

noncomputable section

open Bundle Manifold
open scoped Manifold ContDiff

namespace DifferentialGeometry.Geometry.Operator

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace Real E]
  [FiniteDimensional Real E]
variable {H : Type*} [TopologicalSpace H]
variable {I : ModelWithCorners Real E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M] [T2Space M]

theorem hessFun_apply_self_nonneg_at_spatial_min
    [I.Boundaryless]
    (g : SmoothRiemannianMetric I M)
    {f : M -> Real} {x : M}
    (hmin : IsLocalMin f x)
    (hf : ContMDiff I 𝓘(Real, Real) ∞ f)
    (v : TangentSpace I x) :
    0 <= hessFun (I := I) g f x v v := by
  rw [Connection.hessFun_eq_cov_grad (I := I) g hf x v v]
  exact cov_gradientFun_inner_self_nonneg_at_spatial_min_of_isInteriorPoint
    (I := I) (Connection.LeviCivita (I := I) g) g
      (by
        simpa [Connection.LeviCivita] using
          (Connection.leviCivitaConnectionOfMetric_isMetricCompatible
            (I := I) g))
      hmin BoundarylessManifold.isInteriorPoint
      (hf.mdifferentiable (by simp) x)
      (Filter.Eventually.of_forall fun y => hf.mdifferentiable (by simp) y)
      (gradientFun_mdiffAt (I := I) g hf x) v

theorem hessFun_apply_self_nonpos_at_spatial_max
    [I.Boundaryless]
    (g : SmoothRiemannianMetric I M)
    {f : M -> Real} {x : M}
    (hmax : IsLocalMax f x)
    (hf : ContMDiff I 𝓘(Real, Real) ∞ f)
    (v : TangentSpace I x) :
    hessFun (I := I) g f x v v <= 0 := by
  have hnonneg := hessFun_apply_self_nonneg_at_spatial_min
    (I := I) g hmax.neg hf.neg v
  have hneg : hessFun (I := I) g (fun y : M => -f y) x v v =
      -hessFun (I := I) g f x v v := by
    rw [show (fun y : M => -f y) = (-1 : Real) • f by
      funext y
      simp]
    rw [hessFun_smul]
    simp
  rw [hneg] at hnonneg
  linarith

end DifferentialGeometry.Geometry.Operator

section

open Set Filter CovariantDerivative DifferentialGeometry
open DifferentialGeometry.Geometry.Connection
open scoped Topology

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M] [T2Space M]

theorem IsLocalMax.hessian_trivial_nonpos
    (base : CovariantDerivative I E (TangentSpace I : M → Type _))
    {f : M → ℝ} {x : M} (hf : ContMDiffAt I 𝓘(ℝ, ℝ) 2 f x)
    (hx : I.IsInteriorPoint x) (hmax : IsLocalMax f x) (v : TangentSpace I x) :
    (CovariantDerivative.trivial I M ℝ).hessian base f x v v ≤ 0 := by
  obtain ⟨ε, hε, γ, hγ, hbound, hlaunch⟩ :=
    exists_contMDiff_curve_with_velocity (n := ∞) (by simp) hx v hmax
  have hγ₀ : γ 0 = x := congrArg TotalSpace.proj hlaunch
  have hvelocity :
      (mfderiv 𝓘(ℝ, ℝ) I γ 0 ((NormedSpace.fromTangentSpace (0 : ℝ)).symm 1) : E) = v :=
    congrArg (fun z : TangentBundle I M => (z.2 : E)) hlaunch
  have hJ : Icc (-ε) ε ∈ 𝓝 (0 : ℝ) := Icc_mem_nhds (neg_neg_of_pos hε) hε
  have hγat : ContMDiffAt 𝓘(ℝ, ℝ) I 2 γ 0 :=
    (hγ.contMDiffAt hJ).of_le (show (2 : ℕ∞ω) ≤ ∞ from ENat.LEInfty.out)
  have hf₀ : ContMDiffAt I 𝓘(ℝ, ℝ) 2 f (γ 0) := by simpa only [hγ₀] using hf
  have hσ : ContMDiffAt I (I.prod 𝓘(ℝ, ℝ)) 2 (T% f) (γ 0) :=
    (contMDiffAt_section (F := ℝ) (E := Bundle.Trivial M ℝ) (γ 0)).mpr hf₀
  have hlocal : IsLocalMax (fun t => f (γ t)) 0 := by
    filter_upwards [hJ] with t ht
    simpa only [hγ₀] using (show f (γ t) ≤ f x from hbound ht)
  have hsecond := hlocal.deriv_deriv_nonpos (hf₀.continuousAt.comp hγat.continuousAt)
  have h := (CovariantDerivative.trivial I M ℝ).derivAlongWithin_derivAlongWithin_section
    inferInstance base (J := univ) Filter.univ_mem hγat hσ
  dsimp only at h
  have hmax₀ : IsLocalMax f (γ 0) := by simpa only [hγ₀] using hmax
  have hx₀ : I.IsInteriorPoint (γ 0) := by simpa only [hγ₀] using hx
  have hfirst := hmax₀.mvfderiv_eq_zero hx₀
  simp only [CovariantDerivative.derivAlongWithin_trivial, derivWithin_univ,
    mfderivWithin_univ, CovariantDerivative.trivial_apply,
    hfirst, zero_apply, add_zero] at h
  rw [hvelocity, hγ₀] at h
  exact h ▸ hsecond

theorem IsLocalMax.abstractHessian_nonpos
    (g : SmoothRiemannianMetric I M) {f : M → ℝ} {x : M}
    (hf : ContMDiffAt I 𝓘(ℝ, ℝ) 2 f x)
    (hx : I.IsInteriorPoint x) (hmax : IsLocalMax f x) (v : TangentSpace I x) :
    abstractHessian g f x v v ≤ 0 := by
  have h := hmax.hessian_trivial_nonpos (LeviCivita g) hf hx v
  rwa [CovariantDerivative.hessian_trivial_eq_cotangentCov _ hf] at h

theorem IsLocalMax.rawBundleConnLap_trivial_nonpos
    (g : SmoothRiemannianMetric I M) {f : M → ℝ} {x : M}
    (hf : ContMDiffAt I 𝓘(ℝ, ℝ) 2 f x)
    (hx : I.IsInteriorPoint x) (hmax : IsLocalMax f x) :
    rawBundleConnLap g (CovariantDerivative.trivial I M ℝ) f x ≤ 0 := by
  classical
  by_cases hdim : Module.finrank ℝ E = 0
  · let _ : IsEmpty (Fin (Module.finrank ℝ E)) := by
      simpa only [hdim] using (Fin.isEmpty : IsEmpty (Fin 0))
    simp [rawBundleConnLap]
  let _ : NeZero (Module.finrank ℝ E) := ⟨hdim⟩
  have hσ : ContMDiffAt I (I.prod 𝓘(ℝ, ℝ)) 2 (T% f) x :=
    (contMDiffAt_section (F := ℝ) (E := Bundle.Trivial M ℝ) x).mpr hf
  rw [rawBundleConnLap_eq_sum_hessian_of_orthonormal_of_contMDiffAt g
    (CovariantDerivative.trivial I M ℝ) inferInstance hσ
    (fun i => smoothOrthoFrame g x i x) (smoothOrthoFrame_orthonormal_at_center g x)]
  exact Finset.sum_nonpos fun i _ =>
    hmax.hessian_trivial_nonpos (LeviCivita g) hf hx (smoothOrthoFrame g x i x)

end
