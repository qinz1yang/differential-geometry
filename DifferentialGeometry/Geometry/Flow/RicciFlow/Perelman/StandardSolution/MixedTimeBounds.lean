import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.StandardSolution.ExpressionBounds
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.StandardSolution.StandardTimeJets

set_option autoImplicit false
noncomputable section
open Set Bundle Manifold DifferentialGeometry DifferentialGeometry.Tensor0SBundle
open DifferentialGeometry.Geometry.Curvature DifferentialGeometry.PDE.RicciFlow
open DifferentialGeometry.PDE.RicciFlow
open scoped Manifold ContDiff ENNReal BigOperators
namespace DifferentialGeometry.PDE.RicciFlow
private abbrev E3 := EuclideanSpace ℝ (Fin 3)

theorem uniformStandardLifetime_mixed_curvature_bounds_positive (θ : ℝ) (hθ : 0 ≤ θ)
    (hlt : ENNReal.ofReal θ < uniformStandardLifetime) (N : ℕ) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ S : StandardSolution, ∀ a b : ℕ, a + 2 * b ≤ N →
      ∀ t ∈ Ioc 0 θ, ∀ x : E3,
      Real.sqrt (normSq0S (S.val.metric t) x (4 + a)
        (iteratedCovariantTimeDerivWithin S.val.metric
          (fun r => nablaKRm04Field S.val.toSolutionOn r a x) S.val.domain b t)) ≤ B := by
  obtain ⟨C, hC, hnorm⟩ := uniformStandardLifetime_curvature_derivative_bounds_closed θ hθ hlt N
  obtain ⟨hT, _⟩ := uniformStandardLifetime_slab θ hθ hlt
  let F := fun a b => ((CurvatureExpression.curvature a).timeIter b).normBound 3 C
  have hF (a b : ℕ) : 0 ≤ F a b := CurvatureExpression.normBound_nonneg 3 C hC _
  refine ⟨∑ a ∈ Finset.range (N + 1), ∑ b ∈ Finset.range (N + 1), F a b,
    Finset.sum_nonneg (fun a _ => Finset.sum_nonneg (fun b _ => hF a b)), ?_⟩
  intro S a b hab t ht x
  have hreg : t ∈ (lifetimeInterval S.val.lifetime S.val.lifetime_pos).regular :=
    (mem_lifetimeInterval_regular S.val.lifetime S.val.lifetime_pos t).mpr
      ⟨ht.1, (ENNReal.ofReal_le_ofReal ht.2).trans_lt (hT S)⟩
  have hb := curvature_mixed_time_bound S.val.toSolutionOn S.val.isSolutionOn a b ⟨t, hreg⟩ x C hC
    (fun k hk => hnorm S k (hk.trans hab) t ⟨ht.1.le, ht.2⟩ x)
  have hb' : Real.sqrt (normSq0S (S.val.metric t) x (4 + a)
      (iteratedCovariantTimeDerivWithin S.val.metric
        (fun r => nablaKRm04Field S.val.toSolutionOn r a x) S.val.domain b t)) ≤ F a b := by
    simp only [finrank_euclideanSpace, Fintype.card_fin] at hb
    exact hb
  have hinner : F a b ≤ ∑ j ∈ Finset.range (N + 1), F a j :=
    Finset.single_le_sum (fun j _ => hF a j) (Finset.mem_range.mpr (by omega))
  have houter : (∑ j ∈ Finset.range (N + 1), F a j) ≤
      ∑ i ∈ Finset.range (N + 1), ∑ j ∈ Finset.range (N + 1), F i j :=
    Finset.single_le_sum (fun i _ => Finset.sum_nonneg (fun j _ => hF i j))
      (Finset.mem_range.mpr (by omega))
  exact hb'.trans (hinner.trans houter)

theorem uniformStandardLifetime_mixed_curvature_bounds_closed (θ : ℝ) (hθ : 0 ≤ θ)
    (hlt : ENNReal.ofReal θ < uniformStandardLifetime) (N : ℕ) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ S : StandardSolution, ∀ a b : ℕ, a + 2 * b ≤ N →
      ∀ t ∈ Icc 0 θ, ∀ x : E3,
      Real.sqrt (normSq0S (S.val.metric t) x (4 + a)
        (iteratedCovariantTimeDerivWithin S.val.metric
          (fun r => nablaKRm04Field S.val.toSolutionOn r a x) S.val.domain b t)) ≤ B := by
  obtain ⟨η, hη, hθη, hηL⟩ := ENNReal.lt_iff_exists_real_btwn.mp hlt
  have hltη : θ < η := lt_of_not_ge (fun h =>
    (not_le_of_gt hθη) (ENNReal.ofReal_le_ofReal h))
  have hηpos : 0 < η := hθ.trans_lt hltη
  obtain ⟨B, hB, hbound⟩ := uniformStandardLifetime_mixed_curvature_bounds_positive η hη hηL N
  obtain ⟨hT, _⟩ := uniformStandardLifetime_slab η hη hηL
  refine ⟨B, hB, ?_⟩
  intro S a b hab t ht x
  let f := fun r => Real.sqrt (normSq0S (S.val.metric r) x (4 + a)
    (iteratedCovariantTimeDerivWithin S.val.metric
      (fun q => nablaKRm04Field S.val.toSolutionOn q a x) S.val.domain b r))
  have hcont : ContinuousOn f (Icc 0 η) := by
    have hh := (S.val.curvature_time_jet_regular a b x).2.continuousOn.sqrt
    have hsub : Icc 0 η ⊆ S.val.domain := fun r hr =>
      (mem_lifetimeInterval_carrier S.val.lifetime S.val.lifetime_pos r).mpr
        ⟨hr.1, (ENNReal.ofReal_le_ofReal hr.2).trans_lt (hT S)⟩
    exact hh.mono hsub
  have hcl : closure (Ioc 0 η) = Icc 0 η := closure_Ioc hηpos.ne
  have hc : ContinuousOn f (closure (Ioc 0 η)) := by rw [hcl]; exact hcont
  have htcl : t ∈ closure (Ioc 0 η) := by rw [hcl]; exact ⟨ht.1, ht.2.trans hltη.le⟩
  exact le_on_closure (fun r hr => hbound S a b hab r hr x) hc continuousOn_const htcl
end DifferentialGeometry.PDE.RicciFlow
