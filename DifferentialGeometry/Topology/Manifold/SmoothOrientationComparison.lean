import DifferentialGeometry.Topology.Manifold.SmoothOrientationLocal

set_option autoImplicit false
noncomputable section
open Set Function Manifold TopologicalSpace
open scoped Manifold ContDiff Topology
namespace DifferentialGeometry.Topology.Manifold
variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
variable [TopologicalSpace H] (I : ModelWithCorners ℝ E H)
variable [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

def negSmoothOrientation (o : SmoothOrientation I M) : SmoothOrientation I M := by
  refine ⟨fun x => -o.val x, ?_⟩
  intro p
  have h := (o.property p).comp (fun a => -a)
  simpa only [Orientation.map_neg, Function.comp_def] using h

theorem negSmoothOrientation_apply (o : SmoothOrientation I M) (x : M) :
    (negSmoothOrientation I o).val x = -o.val x := rfl

theorem smoothOrientation_agreement_locallyConstant (o₁ o₂ : SmoothOrientation I M) :
    IsLocallyConstant (fun x : M => o₁.val x = o₂.val x) := by
  apply isLocallyConstant_of_open_neighborhoods
  intro p
  let U : Opens M := ⟨(chartAt H p).source, (chartAt H p).open_source⟩
  have h := (o₁.property p).comp₂ (o₂.property p) (fun a b => a = b)
  refine ⟨U, mem_chart_source H p, ?_⟩
  have he : (fun x : U =>
      Orientation.map _ (preferredChartTangentEquiv I p x.val x.property).toLinearEquiv (o₁.val x.val) =
        Orientation.map _ (preferredChartTangentEquiv I p x.val x.property).toLinearEquiv (o₂.val x.val)) =
      (fun x : U => o₁.val x.val = o₂.val x.val) := by
    funext x
    exact propext (Orientation.map _
      (preferredChartTangentEquiv I p x.val x.property).toLinearEquiv).injective.eq_iff
  have h' : IsLocallyConstant (fun x : U =>
      Orientation.map _ (preferredChartTangentEquiv I p x.val x.property).toLinearEquiv (o₁.val x.val) =
        Orientation.map _ (preferredChartTangentEquiv I p x.val x.property).toLinearEquiv (o₂.val x.val)) := h
  rw [he] at h'
  exact h'

theorem smoothOrientation_eq_of_eq_at [PreconnectedSpace M]
    (o₁ o₂ : SmoothOrientation I M) (p : M) (hp : o₁.val p = o₂.val p) :
    ∀ x : M, o₁.val x = o₂.val x := by
  intro x
  have h := (smoothOrientation_agreement_locallyConstant I o₁ o₂).apply_eq_of_preconnectedSpace x p
  exact h.symm ▸ hp

theorem smoothOrientation_eq_or_eq_neg [PreconnectedSpace M]
    (o₁ o₂ : SmoothOrientation I M) (p : M) :
    (∀ x : M, o₁.val x = o₂.val x) ∨ (∀ x : M, o₁.val x = -o₂.val x) := by
  rcases Orientation.eq_or_eq_neg (o₁.val p) (o₂.val p) (by simp) with hp | hp
  · exact Or.inl (smoothOrientation_eq_of_eq_at I o₁ o₂ p hp)
  · exact Or.inr (smoothOrientation_eq_of_eq_at I o₁ (negSmoothOrientation I o₂) p hp)
end DifferentialGeometry.Topology.Manifold
