import DifferentialGeometry.Geometry.Comparison.Volume.Bishop.Intrinsic
import DifferentialGeometry.Geometry.Comparison.Volume.Segment.Polar.Pole
import DifferentialGeometry.Geometry.Exponential.Variation.EndpointShape
import Mathlib.Analysis.Calculus.Deriv.Slope

open DifferentialGeometry.Geometry.Curvature

set_option autoImplicit false

noncomputable section

open Bundle Filter Function Manifold Set
open scoped ContDiff Manifold Matrix Topology

namespace DifferentialGeometry
namespace Geometry
namespace Riemannian
namespace VolumeComparison

open CovariantDerivativeAlong
open Exponential
open Geodesic
open Variation
open BonnetMyers

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace Real E]
  [FiniteDimensional Real E]
  [NeZero (Module.finrank Real E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners Real E H}
  [I.Boundaryless]
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M] [T2Space M] [SigmaCompactSpace M]
  [T2Space (TangentBundle I M)]

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace

variable [RiemannianBundle (fun x : M ↦ TangentSpace I x)]
variable [PseudoEMetricSpace M] [IsRiemannianManifold I M] [CompleteSpace M]
  [IsContinuousRiemannianBundle E (fun x : M ↦ TangentSpace I x)]

omit [T2Space (TangentBundle I M)] in
/-- Nonconjugacy preserves linear independence of radially scaled intrinsic
Jacobi fields away from the pole. -/
theorem intrJacobi_li
    {ι : Type*}
    (g : SmoothRiemannianMetric I M)
    (hEnorm : IsMetricNorm (I := I) (M := M) g)
    (p : M) (u : TangentSpace I p) (v : ι → TangentSpace I p)
    (hv : LinearIndependent Real v) {t : Real} (ht : t ≠ 0)
    (hno : ¬ IsConjVec (I := I) g hEnorm p (t • (u : E))) :
    LinearIndependent Real fun i ↦
      intrinsicJacobi (I := I) g hEnorm p u (v i) t := by
  let L : E →L[Real] E :=
    mfderiv 𝓘(Real, E) I
      (fun z : E ↦ expMapIntrinsic (I := I) g hEnorm p
        (show TangentSpace I p from z))
      (t • (u : E))
  have hLinj : Function.Injective L := by
    unfold IsConjVec at hno
    exact Classical.not_not.mp hno
  let a : Realˣ := Units.mk0 t ht
  let as : ι → Realˣ := fun _ ↦ a
  have hscaled : LinearIndependent Real fun i ↦ t • v i := by
    have has : as • v = fun i ↦ t • v i := by
      funext i
      rfl
    rw [← has]
    exact hv.units_smul as
  have hmapped : LinearIndependent Real fun i ↦ L (t • (v i : E)) :=
    hscaled.map' L.toLinearMap (LinearMap.ker_eq_bot.mpr hLinj)
  let φ : TangentSpace I
      (intrinsicGeodesic (I := I) g hEnorm p u t) →ₗ[Real] E :=
    { toFun := fun z => (show E from z)
      map_add' := by intro a b; rfl
      map_smul' := by intro c a; rfl }
  let coeTangent : ∀ q : M, TangentSpace I q → E :=
    fun _ z => show E from z
  have hfieldE :
      (fun i ↦ coeTangent _ (intrinsicJacobi (I := I) g hEnorm p u (v i) t)) =
        fun i ↦ L (t • (v i : E)) := by
    funext i
    have h := intrinsic_jacobi_at (I := I) g hEnorm p (u : E) (v i : E) t
    have hcoe := congrArg (fun z => coeTangent _ z) h
    convert hcoe using 1 <;>
      simp only [coeTangent, intrinsicJacobi, L] <;> rfl
  have hcomp :
      φ ∘ (fun i ↦ intrinsicJacobi (I := I) g hEnorm p u (v i) t) =
        fun i ↦ L (t • (v i : E)) := by
    funext i
    change coeTangent _ (intrinsicJacobi (I := I) g hEnorm p u (v i) t) =
      L (t • (v i : E))
    simpa only [φ, coeTangent] using congrFun hfieldE i
  have hcompLI : LinearIndependent Real
      (φ ∘ (fun i ↦ intrinsicJacobi (I := I) g hEnorm p u (v i) t)) := by
    rw [hcomp]
    exact hmapped
  exact LinearIndependent.of_comp φ hcompLI

/-- Along a nonconjugate intrinsic radial segment under nonnegative Ricci
curvature, the radial Jacobi density has derivative at most `(d / t)` times
the density, where `d` is the dimension of the normal frame. -/
theorem intrDen_deriv_le
    (g : SmoothRiemannianMetric I M)
    (hEnorm : IsMetricNorm (I := I) (M := M) g)
    (p : M) (u : TangentSpace I p) (b : Real)
    (hd : 0 < Module.finrank Real E - 1)
    (hu : 0 < g.inner p u u)
    (v : Fin (Module.finrank Real E - 1) → TangentSpace I p)
    (hON : ∀ i j, g.inner p (v i) (v j) = if i = j then 1 else 0)
    (hperp : ∀ i, g.inner p u (v i) = 0)
    (hno : ∀ t ∈ Ioo (0 : Real) b,
      ¬ IsConjVec (I := I) g hEnorm p
        ((t • u : TangentSpace I p) : E))
    (hRic : RicciBoundedBelow (I := I) g 0) :
    let γ := intrinsicGeodesic (I := I) g hEnorm p u
    let V := fun i ↦ intrinsicJacobi (I := I) g hEnorm p u (v i)
    ∀ t ∈ Ioo (0 : Real) b,
      HasDerivAt (curveDensity (I := I) g γ V)
          (curveMean (I := I) g γ V t *
            curveDensity (I := I) g γ V t) t ∧
        curveMean (I := I) g γ V t *
            curveDensity (I := I) g γ V t ≤
          ((Module.finrank Real E - 1 : Nat) : Real) / t *
            curveDensity (I := I) g γ V t := by
  classical
  let d : Nat := Module.finrank Real E - 1
  let γ : Real → M := intrinsicGeodesic (I := I) g hEnorm p u
  let V : Fin d → ∀ t, TangentSpace I (γ t) := fun i ↦
    intrinsicJacobi (I := I) g hEnorm p u (v i)
  dsimp only
  intro t ht
  have hv : LinearIndependent Real v := by
    simpa only using
      linIndep_of_ortho (I := I) g p (fun i ↦ (v i : E)) hON
  have hLI : LinearIndependent Real fun i ↦ V i t := by
    simpa only [γ, V] using
      intrJacobi_li (I := I) g hEnorm p u v hv ht.1.ne' (hno t ht)
  have hγInf : ContMDiff 𝓘(Real, Real) I
      ((⊤ : ℕ∞) : WithTop ℕ∞) γ := by
    exact intrinsicGeodesic_contMDiff (I := I) g hEnorm p u
  have hγ : ContMDiffAt 𝓘(Real, Real) I (2 : WithTop ℕ∞) γ t :=
    hγInf.contMDiffAt.of_le
      (WithTop.coe_le_coe.2 (le_top : (2 : ℕ∞) ≤ (⊤ : ℕ∞)))
  have hVdiff : ∀ i,
      DifferentiableAt Real (chartRepAt (I := I) γ (V i) t) t := by
    intro i
    simpa only [γ, V] using
      (intrinsicJacobi_diff (I := I) g hEnorm p u (v i) t).1
  have hW : ∀ i j, jacobiWronskian (I := I) g γ (V i) (V j) t = 0 := by
    intro i j
    exact wronskian_eq_zero (I := I) (n := (2 : WithTop ℕ∞)) (by norm_num)
      g γ (V i) (V j)
      (hγInf.of_le
        (WithTop.coe_le_coe.2 (le_top : (2 : ℕ∞) ≤ (⊤ : ℕ∞))))
      (fun s _ ↦ by simpa only [γ, V] using
        (intrinsicJacobi_diff (I := I) g hEnorm p u (v i) s).1)
      (fun s _ ↦ by simpa only [γ, V] using
        (intrinsicJacobi_diff (I := I) g hEnorm p u (v j) s).1)
      (fun s _ ↦ by simpa only [γ, V] using
        (intrinsicJacobi_diff (I := I) g hEnorm p u (v i) s).2)
      (fun s _ ↦ by simpa only [γ, V] using
        (intrinsicJacobi_diff (I := I) g hEnorm p u (v j) s).2)
      (fun s _ ↦ by
        convert intrinsic_jacobi (I := I) g hEnorm p (u : E) (v i : E) s using 1
        · funext r
          rfl)
      (fun s _ ↦ by
        convert intrinsic_jacobi (I := I) g hEnorm p (u : E) (v j : E) s using 1
        · funext r
          rfl)
      (by simp [V]) (by simp [V]) t ⟨ht.1.le, ht.2.le⟩
  let R : Real → Real := fun r ↦
    curveDensity (I := I) g γ V r / hyperbolicDensity 0 d r
  have hRic0 : RicciBoundedBelow (I := I) g
      (-(((d : Nat) : Real) * (0 : Real) ^ 2)) := by
    simpa [d] using hRic
  have hanti : AntitoneOn R (Ioo (0 : Real) b) := by
    simpa only [R, γ, V, d, zero_mul] using
      intrinsicRatioOfFrame (I := I) g hEnorm p u 0 b (by norm_num)
        hd hu v hON hperp hno hRic0
  have hRderiv : HasDerivAt R
      (R t * (curveMean (I := I) g γ V t - hyperbolicMeanCurv 0 d t)) t := by
    simpa only [R] using
      hasDerivAt_denRatio (I := I) (n := (2 : WithTop ℕ∞)) (by norm_num)
        g γ V 0 t d (by norm_num) ht.1 hγ hVdiff
        (curveGram_det_pos (I := I) g γ V t hLI) hW
  have hRnonpos :
      R t * (curveMean (I := I) g γ V t - hyperbolicMeanCurv 0 d t) ≤ 0 := by
    have hderiv := hanti.derivWithin_nonpos (x := t)
    rw [hRderiv.hasDerivWithinAt.derivWithin (uniqueDiffWithinAt_Ioo ht)] at hderiv
    exact hderiv
  have hRpos : 0 < R t := by
    exact div_pos (curveDensity_pos (I := I) g γ V t hLI)
      (hyperbolicDensity_pos (q := (0 : Real)) (d := d) (r := t) (by norm_num) ht.1)
  have hmeanModel :
      curveMean (I := I) g γ V t ≤ hyperbolicMeanCurv 0 d t := by
    nlinarith
  have hmodel : hyperbolicMeanCurv 0 d t ≤ (d : Real) / t := by
    simpa only [add_zero, mul_zero] using
      hyperbolicMeanCurv_le (q := (0 : Real)) (r := t) d (by norm_num) ht.1
  have hmean : curveMean (I := I) g γ V t ≤ (d : Real) / t :=
    hmeanModel.trans hmodel
  have hJderiv : HasDerivAt (curveDensity (I := I) g γ V)
      (curveMean (I := I) g γ V t *
        curveDensity (I := I) g γ V t) t := by
    refine (hasDerivAt_symmDen (I := I) (n := (2 : WithTop ℕ∞)) (by norm_num)
      g γ V t hγ hVdiff
      (curveGram_det_pos (I := I) g γ V t hLI) hW).congr_deriv ?_
    rw [curveMean, curveShape]
  have hmul := mul_le_mul_of_nonneg_right hmean
    (curveDensity_pos (I := I) g γ V t hLI).le
  simpa only [γ, V, d] using And.intro hJderiv hmul

end VolumeComparison
end Riemannian
end Geometry
end DifferentialGeometry

end
