import DifferentialGeometry.Analysis.Parabolic.MaximumPrinciple.Tensor.FirstNull.Basic
import DifferentialGeometry.Geometry.Operator.WeightedLaplacian
import DifferentialGeometry.Geometry.Metric.QuadraticBounds.Unit

set_option autoImplicit false

noncomputable section

open Bundle Manifold Set
open scoped Manifold ContDiff

namespace DifferentialGeometry

open DifferentialGeometry.Tensor0SBundle
open DifferentialGeometry.Geometry
open DifferentialGeometry.Geometry.Connection
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Geometry.Operator

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace Real E]
  [FiniteDimensional Real E]
variable {H : Type*} [TopologicalSpace H]
variable {I : ModelWithCorners Real E H} [I.Boundaryless]
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M] [T2Space M]

theorem weightedRoughLaplacian0S_quad_nonnegative_at_unit_global_min
    (g : SmoothRiemannianMetric I M) (f : C^∞⟮I, M; Real⟯)
    (A : Tensor0SField (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      (n := (∞ : WithTop ℕ∞)) 2)
    (x : M) (v : TangentSpace I x)
    (hvunit : g.inner x v v = 1)
    (hsym : ∀ y : M, ∀ u w : TangentSpace I y,
      A y (vec2 (I := I) u w) = A y (vec2 (I := I) w u))
    (hmin : ∀ y : M, ∀ w : TangentSpace I y,
      g.inner y w w = 1 →
        quad02 (I := I) (M := M) (A x) v ≤
          quad02 (I := I) (M := M) (A y) w) :
    0 ≤ quad02 (I := I) (M := M)
      (weightedRoughLaplacian0S (I := I) g f A x) v := by
  classical
  let κ : Real := quad02 (I := I) (M := M) (A x) v
  let metric := metricTensorField (I := I) g
  let B := A - κ • metric
  have hBpsd : ∀ y : M, ∀ w : TangentSpace I y,
      0 ≤ quad02 (I := I) (M := M) (B y) w := by
    intro y w
    by_cases hw : w = 0
    · subst hw
      have hzero : quad02 (I := I) (M := M) (B y) (0 : TangentSpace I y) = 0 := by
        with_unfolding_all exact (B y).map_coord_zero (0 : Fin 2) rfl
      rw [hzero]
    · have hrpos : 0 < g.inner y w w := g.pos y w hw
      let r : Real := Real.sqrt (g.inner y w w)
      have hrpos' : 0 < r := Real.sqrt_pos.mpr hrpos
      have hrne : r ≠ 0 := ne_of_gt hrpos'
      have hrr : r * r = g.inner y w w := by
        simpa [r, sq] using Real.sq_sqrt hrpos.le
      set u : TangentSpace I y := r⁻¹ • w with hu_def
      have huunit : g.inner y u u = 1 := by
        rw [hu_def, metric_smul2]
        field_simp [hrne]
        linarith [hrr]
      have hκu : κ ≤ quad02 (I := I) (M := M) (A y) u :=
        hmin y u huunit
      have hwu : r • u = w := by
        simp [hu_def, hrne]
      have hAw : quad02 (I := I) (M := M) (A y) w =
          r * r * quad02 (I := I) (M := M) (A y) u := by
        rw [← hwu, tensor02_smul2]
      have hmul := mul_le_mul_of_nonneg_right hκu
        (by positivity : (0 : Real) ≤ r * r)
      change 0 ≤
        quad02 (I := I) (M := M) (A y) w - κ * g.inner y w w
      rw [hAw, ← hrr]
      nlinarith
  have hBnull : quad02 (I := I) (M := M) (B x) v = 0 := by
    change quad02 (I := I) (M := M) (A x) v - κ * g.inner x v v = 0
    rw [hvunit]
    simp [κ]
  have hBsym : ∀ y : M, ∀ u w : TangentSpace I y,
      eval02 (I := I) (M := M) (B y) u w =
        eval02 (I := I) (M := M) (B y) w u := by
    intro y u w
    change A y (vec2 (I := I) u w) - κ * g.inner y u w =
      A y (vec2 (I := I) w u) - κ * g.inner y w u
    rw [hsym y u w, g.symm y u w]
  have hkerL : ∀ w : TangentSpace I x,
      B x (vec2 (I := I) v w) = 0 := by
    intro w
    change eval02 (I := I) (M := M) (B x) v w = 0
    exact psd_null_left (I := I) (M := M) (B x) (hBsym x)
      (hBpsd x) hBnull w
  have hkerR : ∀ w : TangentSpace I x,
      B x (vec2 (I := I) w v) = 0 := by
    intro w
    change eval02 (I := I) (M := M) (B x) w v = 0
    exact psd_null_right (I := I) (M := M) (B x) (hBsym x)
      (hBpsd x) hBnull w
  let cov := LeviCivita (I := I) g
  let hcov : CovariantDerivative.ContMDiffCovariantDerivativeLocally cov ∞ := by
    simpa [cov, LeviCivita] using
      (leviCivitaConnectionOfMetric_contMDiffCovariantDerivativeLocally
        (I := I) (M := M) g)
  have hmc : IsMetricCompatible (I := I) cov g := by
    simpa [cov, LeviCivita] using
      (leviCivitaConnectionOfMetric_isMetricCompatible (I := I) g)
  obtain ⟨V, hV, hcovV⟩ :=
    TensorLieDeriv.exists_cov_zero_at_apply (I := I) cov x v
  let phi : M → Real := fun y => B y (vec2 (I := I) (V y) (V y))
  have hphi : ContMDiff I 𝓘(Real, Real) ∞ phi := by
    let Slots : Fin 2 →
        ContMDiffSection I E ∞ (TangentSpace I : M → Type _) := fun _ => V
    have hraw := TensorMultilinear.contMDiff_tensor0SField_apply
      (I := I) (M := M) B Slots
    simpa [phi, Slots, PDE.RicciFlow.vec2_self_eq_const] using hraw
  have hphix : phi x = 0 := by
    simpa [phi, hV, quad02, PDE.RicciFlow.vec2_self_eq_const] using hBnull
  have hlocalmin : IsLocalMin phi x := by
    refine Filter.Eventually.of_forall ?_
    intro y
    rw [hphix]
    simpa [phi, quad02, PDE.RicciFlow.vec2_self_eq_const] using hBpsd y (V y)
  let du : Tensor0SField (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      (n := ∞) 1 := duSec (I := I) phi hphi
  let Hess : (y : M) →
      Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) 2 y :=
    fun y => hessianSec (I := I) cov hcov phi hphi y
  let nablaB := totalNabla0S (I := I) 2 cov B
    (totalNabla0S_regularity (I := I) 2 cov hcov B)
  let nabla2B := totalNabla0S (I := I) 3 cov nablaB
    (totalNabla0S_regularity (I := I) 3 cov hcov nablaB)
  have hreal1 : TotalNabla0SRealizes (I := I) 2 cov B nablaB :=
    totalNabla0S_realizes (I := I) 2 cov B _
  have hreal2 : TotalNabla0SRealizes (I := I) 3 cov nablaB nabla2B :=
    totalNabla0S_realizes (I := I) 3 cov nablaB _
  have hdu : DuFieldRealizes (I := I) phi du := by
    simpa [du] using duSec_realizes (I := I) phi hphi
  have hHess : HessianRealizesNablaDuAt (I := I) cov du Hess x := by
    simpa [du, Hess] using hessianSec_realizesAt (I := I) cov hcov phi hphi x
  have hlap : ScalarLaplacianRealizesTraceAt (I := I) cov g phi (Hess x) := by
    simpa [Hess] using scalarLap_smooth (I := I) cov hcov g hmc phi hphi
  have hAreg : ∀ Y : ContMDiffSection I E ∞ (TangentSpace I : M → Type _),
      ContMDiffAt I (I.prod 𝓘(Real, E)) 1
        (fun p : M =>
          (⟨p, ((cov (fun q : M => V q) p) (Y p))⟩ :
            TotalSpace E (TangentSpace I : M → Type _))) x := by
    intro Y
    simpa using CovariantDerivative.smoothSections_cov_contMDiffAt_one
      (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) cov
      (by
        simpa [cov, LeviCivita] using
          (leviCivitaConnectionOfMetric_contMDiffCovariantDerivativeLocally_one
            (I := I) (M := M) g)) Y V x
  have hslots : ∀ U W : TangentSpace I x,
      nabla2B x (metricTraceInput (I := I) U W (vec2 (I := I) v v)) =
        Hess x (vec2 (I := I) U W) :=
    PDE.RicciFlow.nabla2Eval_hess_slots (I := I) (M := M) hreal1 hreal2 V hV
      hcovV hkerL hkerR hdu hHess hAreg
  have hlap_nonneg : 0 ≤ laplacian (I := I) cov g phi x := by
    exact laplacian_nonneg_at_spatial_min_of_metricCompatible
      (I := I) cov g hmc hlocalmin
      (hphi.contMDiffAt.mdifferentiableAt (by simp))
      (Filter.Eventually.of_forall fun y =>
        hphi.contMDiffAt.mdifferentiableAt (by simp))
      (gradientFun_mdiffAt (I := I) g hphi x)
  have htrace : 0 ≤ metricTraceFirstTwo0SAt (I := I) g (nabla2B x)
      (vec2 (I := I) v v) := by
    rw [lapTrace_of_slots (I := I) cov g phi (nabla2B x)
      (vec2 (I := I) v v) (Hess x) hlap hslots]
    exact hlap_nonneg
  obtain ⟨X, hX⟩ := ContMDiffSection.exists_eq_at
    (I := I) (F := E) (V := TangentSpace I) (n := (⊤ : ℕ∞)) x
      (gradFun (I := I) g f x)
  have hphideriv : mvfderiv (I := I) phi x (X x) = 0 := by
    have hzero := mfderiv_eq_zero_at_spatial_min (I := I) hlocalmin
      (hphi.contMDiffAt.mdifferentiableAt (by simp))
    rw [DifferentialGeometry.mvfderiv_real_eq_mfderiv, hzero]
    rfl
  have hdrift : nablaB x
      (Fin.cons (gradFun (I := I) g f x) (vec2 (I := I) v v)) = 0 := by
    have hz := PDE.RicciFlow.nablaEval_zero (I := I) (M := M) hreal1 X
      (fun _ : Fin 2 => V) (fun _ => hV)
      (by simpa [phi, PDE.RicciFlow.vec2_self_eq_const] using hphideriv)
      (fun _ => hcovV X)
    simpa [hX, phi, PDE.RicciFlow.vec2_self_eq_const] using hz
  have hweightedB : 0 ≤ quad02 (I := I) (M := M)
      (weightedRoughLaplacian0S (I := I) g f B x) v := by
    rw [weightedRoughLaplacian0S]
    unfold quad02
    rw [Tensor0SSpace.sub_apply, roughLap0STensor_apply,
      tensor0S_curry_apply_cons]
    rw [show (fun _ : Fin 2 => v) = vec2 (I := I) v v by
      exact (PDE.RicciFlow.vec2_self_eq_const (I := I) (M := M) v).symm]
    change 0 ≤ metricTraceFirstTwo0SAt (I := I) g (nabla2B x)
        (vec2 (I := I) v v) -
      nablaB x (Fin.cons (gradFun (I := I) g f x) (vec2 (I := I) v v))
    rw [hdrift, sub_zero]
    exact htrace
  rw [weightedRoughLaplacian0S_sub_const_smul_metric
    (I := I) g f A κ x] at hweightedB
  exact hweightedB

end DifferentialGeometry
