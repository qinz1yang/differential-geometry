import DifferentialGeometry.Geometry.Connection.ParallelTransport.Naturality.Pullback
import DifferentialGeometry.Geometry.Connection.ParallelTransport.Construction.Existence
import DifferentialGeometry.Geometry.Geodesic.Chart.Regularity

noncomputable section

open Bundle Set
open scoped ContDiff Manifold

namespace DifferentialGeometry
namespace Geometry
namespace Riemannian
namespace Geodesic

open CovariantDerivativeAlong
open Connection
open Variation

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]
variable {H : Type*} [TopologicalSpace H]
variable {I : ModelWithCorners ℝ E H} [I.Boundaryless]
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M] [T2Space M]

theorem IsGeodesic.isMIntegralCurve_of_parallel
    {g : SmoothRiemannianMetric I M} {γ : ℝ → M}
    (hgamma : IsGeodesic g γ) (hcont : Continuous γ)
    (X : ContMDiffSection I E ∞ (TangentSpace I : M → Type _))
    (hX : ∀ y : M, (LeviCivita g).toFun (fun z : M => X z) y = 0)
    {t₀ : ℝ} (hinit : mfderiv 𝓘(ℝ, ℝ) I γ t₀ (1 : ℝ) = X (γ t₀)) :
    IsMIntegralCurve γ (fun y : M => X y) := by
  classical
  let V : ∀ t : ℝ, TangentSpace I (γ t) := fun t ↦ X (γ t)
  let W : ∀ t : ℝ, TangentSpace I (γ t) := fun t ↦
    (mfderiv 𝓘(ℝ, ℝ) I γ t : ℝ →L[ℝ] TangentSpace I (γ t)) 1
  have hγ_smooth : ContMDiff 𝓘(ℝ, ℝ) I ∞ γ :=
    contMDiffOn_univ.mp (isGeodesicOn_contMDiffOn_infty g isOpen_univ
      (hgamma.isGeodesicOn univ) hcont.continuousOn)
  have hγ_two : ContMDiff 𝓘(ℝ, ℝ) I (2 : ℕ∞) γ :=
    hγ_smooth.of_le
      (WithTop.coe_le_coe.mpr (le_top : (2 : ℕ∞) ≤ (⊤ : ℕ∞)))
  have hVdiff (t : ℝ) :
      DifferentiableAt ℝ (chartRepAt (I := I) γ V t) t := by
    have hbase : γ t ∈
        (trivializationAt E (TangentSpace I) (γ t)).baseSet :=
      FiberBundle.mem_baseSet_trivializationAt E (TangentSpace I) (γ t)
    have hXcoord : MDifferentiableAt I 𝓘(ℝ, E)
        (Connection.chartESectionRepr (I := I) (γ t) (fun y : M ↦ X y))
        (γ t) :=
      (Connection.mdifferentiableAt_section_iff_chartE I (γ t)
        (fun y : M ↦ X y) hbase).mp X.mdifferentiableAt
    have hcomp : MDifferentiableAt 𝓘(ℝ, ℝ) 𝓘(ℝ, E)
        (Connection.chartESectionRepr (I := I) (γ t) (fun y : M ↦ X y) ∘ γ) t :=
      hXcoord.comp t (hγ_smooth.mdifferentiableAt (by simp))
    rw [mdifferentiableAt_iff_differentiableAt] at hcomp
    simpa only [V, chartRepAt, Connection.chartESectionRepr,
      Function.comp_apply] using! hcomp
  have hWdiff (t : ℝ) :
      DifferentiableAt ℝ (chartRepAt (I := I) γ W t) t := by
    simpa only [W, chartRepAt] using!
      MFDerivAlongCurve.velocity_coord_diff (I := I) γ t
        hγ_two.contMDiffAt
  have hVpar (t : ℝ) : covDerivAlong (I := I) g γ V t = 0 := by
    rw [covAlong_sec (I := I) g γ X t
      (hγ_smooth.mdifferentiableAt (by simp))]
    change (LeviCivita (I := I) g).toFun (fun y : M ↦ X y) (γ t) _ = 0
    rw [hX (γ t)]
    rfl
  have hWpar (t : ℝ) : covDerivAlong (I := I) g γ W t = 0 := by
    exact covDerivAlong_velocity_eq_zero_of_hasGeodesicEquationAt_C2 g γ t
      hγ_two.contMDiffAt (hgamma t)
  have hVWinit : V t₀ = W t₀ := hinit.symm
  intro t
  have ht : t ∈ Set.Icc (min t₀ t) (max t₀ t) := right_mem_uIcc
  have ht₀ : t₀ ∈ Set.Icc (min t₀ t) (max t₀ t) := left_mem_uIcc
  have hVW : V t = W t :=
    parallel_transport_unique_of_eq_at_point (I := I) g γ le_rfl hγ_two V W
      (fun s _ ↦ hVdiff s) (fun s _ ↦ hWdiff s)
      (fun s _ ↦ hVpar s) (fun s _ ↦ hWpar s)
      (t₀ := t₀) ht₀ hVWinit t ht
  have hvel :
      (mfderiv 𝓘(ℝ, ℝ) I γ t : ℝ →L[ℝ] TangentSpace I (γ t)) 1 =
        X (γ t) := by
    simpa only [V, W] using hVW.symm
  have hmfderiv : mfderiv 𝓘(ℝ, ℝ) I γ t =
      (1 : ℝ →L[ℝ] ℝ).smulRight (X (γ t)) := by
    apply ContinuousLinearMap.ext
    intro (r : ℝ)
    calc
      (mfderiv 𝓘(ℝ, ℝ) I γ t) r =
          r • (mfderiv 𝓘(ℝ, ℝ) I γ t) 1 := by
        have hmap := (show ℝ →L[ℝ] E from mfderiv 𝓘(ℝ, ℝ) I γ t).map_smul r (1 : ℝ)
        rw [smul_eq_mul, mul_one] at hmap
        exact hmap
      _ = r • X (γ t) := by rw [hvel]
      _ = ((1 : ℝ →L[ℝ] ℝ).smulRight (X (γ t))) r := by simp
  have hγ_at : HasMFDerivAt 𝓘(ℝ, ℝ) I γ t
      (mfderiv 𝓘(ℝ, ℝ) I γ t) :=
    (hγ_smooth.mdifferentiableAt (by simp)).hasMFDerivAt
  exact hγ_at.congr_mfderiv hmfderiv

end Geodesic
end Riemannian
end Geometry
end DifferentialGeometry
