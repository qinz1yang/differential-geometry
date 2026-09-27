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
  have h := lRegularizedInner_deriv S hS T alpha V W s ht halpha hV hW
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

omit [NeZero (Module.finrank ℝ E)] [SigmaCompactSpace M] in
theorem IsLAdapted.eqOn_of_eq_at
    (S : SolutionOn (I := I) (M := M) D) (hS : IsSolutionOn S)
    (T : ℝ) (α : ℝ → M) (P Q : ∀ s, TangentSpace I (α s))
    {K : Set ℝ} (hK : IsPreconnected K) {s₀ : ℝ} (hs₀ : s₀ ∈ K)
    (hreg : ∀ s ∈ K, T - s ^ 2 ∈ D.regular)
    (hα : ∀ s ∈ K, MDifferentiableAt 𝓘(ℝ, ℝ) I α s)
    (hP : ∀ s ∈ K, DifferentiableAt ℝ (chartRepAt (I := I) α P s) s)
    (hQ : ∀ s ∈ K, DifferentiableAt ℝ (chartRepAt (I := I) α Q s) s)
    (hDP : IsLAdapted S T α P K) (hDQ : IsLAdapted S T α Q K)
    (heq : P s₀ = Q s₀) :
    ∀ s ∈ K, P s = Q s := by
  let R : ∀ s, TangentSpace I (α s) := fun s => P s + (-1 : ℝ) • Q s
  have hR (s : ℝ) (hs : s ∈ K) : DifferentiableAt ℝ (chartRepAt (I := I) α R s) s := by
    change DifferentiableAt ℝ (chartRepAt (I := I) α (fun s => P s + (-1 : ℝ) • Q s) s) s
    rw [chartRepAt_add, chartRepAt_smul]
    exact (hP s hs).add ((hQ s hs).const_smul (-1))
  have hDR : IsLAdapted S T α R K := by
    intro s hs
    unfold IsLAdaptedAt
    dsimp only [R]
    rw [covDerivAlong_add _ _ _ _ s (hP s hs) (by
      rw [chartRepAt_smul]
      exact (hQ s hs).const_smul (-1)), covDerivAlong_smul,
      hDP s hs, hDQ s hs, map_add, map_smul, smul_add]
    module
  have hRzero : R s₀ = 0 := by simp only [R, heq, neg_one_smul, add_neg_cancel]
  have hnorm {a b : ℝ} (ha : a ∈ K) (hb : b ∈ K) (hab : a ≤ b) :
      (S.base.metric (T - a ^ 2)).inner (α a) (R a) (R a) =
        (S.base.metric (T - b ^ 2)).inner (α b) (R b) (R b) := by
    have hsub : Icc a b ⊆ K := hK.ordConnected.out ha hb
    exact metric_inner_eq_of_isLAdapted S hS T α R R hab
      (fun s hs => hreg s (hsub hs)) (fun s hs => hα s (hsub hs))
      (fun s hs => hR s (hsub hs)) (fun s hs => hR s (hsub hs))
      (fun s hs => hDR s (hsub hs)) (fun s hs => hDR s (hsub hs))
  intro s hs
  have hz : (S.base.metric (T - s ^ 2)).inner (α s) (R s) (R s) = 0 := by
    have hh : (S.base.metric (T - s ^ 2)).inner (α s) (R s) (R s) =
        (S.base.metric (T - s₀ ^ 2)).inner (α s₀) (R s₀) (R s₀) := by
      rcases le_total s s₀ with h | h
      · exact hnorm hs hs₀ h
      · exact (hnorm hs₀ hs h).symm
    rw [hRzero, map_zero] at hh
    exact hh
  have hRs : R s = 0 := by
    by_contra hne
    have hp := (S.base.metric (T - s ^ 2)).pos (α s) (R s) hne
    rw [hz] at hp
    exact (lt_irrefl _ hp)
  simpa only [R, neg_one_smul, ← sub_eq_add_neg, sub_eq_zero] using hRs

end DifferentialGeometry.PDE.RicciFlow.Perelman
