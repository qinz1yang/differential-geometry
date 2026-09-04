import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.LGeometry.AdaptedField.Defs
import DifferentialGeometry.Geometry.Curvature.Metric.LeviCivita
import Mathlib.Analysis.Calculus.MeanValue

set_option autoImplicit false

noncomputable section

namespace DifferentialGeometry.PDE.RicciFlow.Perelman

open Set
open scoped Manifold ContDiff

open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Geometry.Riemannian.CovariantDerivativeAlong

universe u uE uH

variable {E : Type uE} [NormedAddCommGroup E] [NormedSpace Real E]
  [FiniteDimensional Real E]
  [NeZero (Module.finrank Real E)]
variable {H : Type uH} [TopologicalSpace H]
variable {I : ModelWithCorners Real E H} [I.Boundaryless]
variable {M : Type u} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M] [T2Space M] [SigmaCompactSpace M]
variable {D : RealTimeInterval}

omit [NeZero (Module.finrank Real E)] [SigmaCompactSpace M] in
theorem hasDerivAt_inner_of_isLAdaptedAt
    (S : SolutionOn (I := I) (M := M) D) (hS : IsSolutionOn (I := I) S)
    (T : Real) (alpha : Real → M)
    (V W : ∀ s, TangentSpace I (alpha s)) (s : Real)
    (ht : T - s ^ 2 ∈ D.regular)
    (halpha : MDifferentiableAt 𝓘(Real, Real) I alpha s)
    (hV : DifferentiableAt Real (chartRepAt (I := I) alpha V s) s)
    (hW : DifferentiableAt Real (chartRepAt (I := I) alpha W s) s)
    (hDV : IsLAdaptedAt S T alpha V s)
    (hDW : IsLAdaptedAt S T alpha W s) :
    HasDerivAt
      (fun r : Real ↦
        (S.base.metric (T - r ^ 2)).inner (alpha r) (V r) (W r)) 0 s := by
  have h := lRegInner_deriv S hS T alpha V W s ht halpha hV hW
  apply h.congr_deriv
  rw [hDV, hDW]
  rw [map_smul, smul_apply]
  rw [((S.base.metric (T - s ^ 2)).inner (alpha s) (V s)).map_smul]
  simp only [smul_eq_mul]
  rw [inner_ricciSharp, inner_ricciSharp_right]
  change
    (-2 * s) * ricciTensor (I := I) (S.base.metric (T - s ^ 2)) (alpha s) (V s) (W s) +
        (-2 * s) * ricciTensor (I := I) (S.base.metric (T - s ^ 2)) (alpha s) (W s) (V s) +
      4 * s * metricRicciAt (I := I) (S.base.metric (T - s ^ 2)) (alpha s)
        (vec2 (V s) (W s)) = 0
  rw [metricRicciAt_apply_eq_ricciTensor, ricciTensor_symm]
  ring

omit [NeZero (Module.finrank Real E)] [SigmaCompactSpace M] in
theorem metric_inner_eq_of_isLAdapted
    (S : SolutionOn (I := I) (M := M) D) (hS : IsSolutionOn (I := I) S)
    (T : Real) (alpha : Real → M)
    (V W : ∀ s, TangentSpace I (alpha s)) {a b : Real} (hab : a ≤ b)
    (ht : ∀ s ∈ Set.Icc a b, T - s ^ 2 ∈ D.regular)
    (halpha : ∀ s ∈ Set.Icc a b,
      MDifferentiableAt 𝓘(Real, Real) I alpha s)
    (hV : ∀ s ∈ Set.Icc a b,
      DifferentiableAt Real (chartRepAt (I := I) alpha V s) s)
    (hW : ∀ s ∈ Set.Icc a b,
      DifferentiableAt Real (chartRepAt (I := I) alpha W s) s)
    (hDV : IsLAdapted S T alpha V (Set.Icc a b))
    (hDW : IsLAdapted S T alpha W (Set.Icc a b)) :
    (S.base.metric (T - a ^ 2)).inner (alpha a) (V a) (W a) =
      (S.base.metric (T - b ^ 2)).inner (alpha b) (V b) (W b) := by
  let f : Real → Real := fun s ↦
    (S.base.metric (T - s ^ 2)).inner (alpha s) (V s) (W s)
  have hd : ∀ s ∈ Set.Icc a b, HasDerivAt f 0 s := by
    intro s hs
    exact hasDerivAt_inner_of_isLAdaptedAt S hS T alpha V W s
      (ht s hs) (halpha s hs) (hV s hs) (hW s hs) (hDV s hs) (hDW s hs)
  have hbound : ‖f b - f a‖ ≤ (0 : Real) * ‖b - a‖ :=
    (convex_Icc a b).norm_image_sub_le_of_norm_deriv_le (f := f) (s := Set.Icc a b)
      (fun s hs ↦ (hd s hs).differentiableAt)
      (fun s hs ↦ by rw [(hd s hs).deriv, norm_zero])
      ⟨le_rfl, hab⟩ ⟨hab, le_rfl⟩
  have hnorm : ‖f b - f a‖ ≤ 0 := by simpa only [zero_mul] using hbound
  have hsub : f b - f a = 0 :=
    norm_eq_zero.mp (le_antisymm hnorm (norm_nonneg _))
  exact (sub_eq_zero.mp hsub).symm

end DifferentialGeometry.PDE.RicciFlow.Perelman
