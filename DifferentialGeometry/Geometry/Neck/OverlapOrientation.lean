import DifferentialGeometry.Geometry.Neck.LeastRicciField
import Mathlib.Topology.Connected.Basic

noncomputable section

open Set Bundle
open scoped Manifold ContDiff
open DifferentialGeometry DifferentialGeometry.Geometry.Operator
open DifferentialGeometry.Geometry.Curvature

namespace DifferentialGeometry.Geometry.Neck

theorem cylindricalChart.exists_sign_axial_gradient_bound_on_preconnected
    {F H M : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
    [TopologicalSpace H] {J : ModelWithCorners ℝ F H}
    [TopologicalSpace M] [ChartedSpace H M] [IsManifold J ∞ M] [T2Space M]
    [BoundarylessManifold J M]
    (C₀ C₁ : cylindricalChart J (M := M)) (g : SmoothRiemannianMetric J M)
    {U₀ : Set C₀.domain} {U₁ : Set C₁.domain} (hU₀ : IsOpen U₀) (hU₁ : IsOpen U₁)
    (ε₀ ε₁ : ℝ) (hε₀ : ε₀ < 1 / 200000) (hε₁ : ε₁ < 1 / 200000)
    (hsmall₀ : C₀.metricCloseOn g ε₀ U₀) (hsmall₁ : C₁.metricCloseOn g ε₁ U₁)
    {S : Set M} (hS : IsPreconnected S)
    (hS₀ : S ⊆ C₀.region U₀) (hS₁ : S ⊆ C₁.region U₁) :
    ∃ σ : ℝ, (σ = 1 ∨ σ = -1) ∧ ∀ x ∈ S,
      Real.sqrt (g.inner x (gradFun g C₀.axial x - σ • gradFun g C₁.axial x)
        (gradFun g C₀.axial x - σ • gradFun g C₁.axial x)) ≤ 184712 * (ε₀ + ε₁) := by
  obtain ⟨ν₀, Y₀, _, _, hY₀, hp₀⟩ :=
    C₀.exists_least_ricci_field_close_to_gradient g hU₀ ε₀ hε₀ hsmall₀
  obtain ⟨ν₁, Y₁, _, _, hY₁, hp₁⟩ :=
    C₁.exists_least_ricci_field_close_to_gradient g hU₁ ε₁ hε₁ hsmall₁
  have hsign (x : M) (hx : x ∈ S) : Y₀ x = Y₁ x ∨ Y₀ x = -Y₁ x := by
    obtain ⟨hn₀, he₀, hm₀, _, _, _, _, _⟩ := hp₀ x (hS₀ hx)
    obtain ⟨hn₁, he₁, hm₁, _, hs₁, _, _, _⟩ := hp₁ x (hS₁ hx)
    exact (least_ricci_eigenpair_eq_or_eq_neg g x
      (ν₀ x) (ν₁ x) (Y₀ x) (Y₁ x) hn₀ hn₁ he₀ he₁ hm₀ hm₁ hs₁).2
  let f : M → ℝ := fun x => g.inner x (Y₀ x) (Y₁ x)
  have hf : ContinuousOn f S := by
    have ht : ContMDiffOn J (J.prod 𝓘(ℝ)) ∞
        (fun x => TotalSpace.mk' ℝ (E := fun _ : M => ℝ) x (f x)) S :=
      ContMDiffOn.clm_bundle_apply₂ (E₁ := TangentSpace J) (E₂ := TangentSpace J)
        (E₃ := fun _ : M => ℝ) (b := id) (ψ := fun x => g.inner x)
        (v := Y₀) (w := Y₁) g.contMDiff.contMDiffOn (hY₀.mono hS₀) (hY₁.mono hS₁)
    have hsmooth : ContMDiffOn J 𝓘(ℝ) ∞ f S := by
      intro x hx
      exact (contMDiffWithinAt_totalSpace.mp (ht x hx)).2
    exact hsmooth.continuousOn
  have hfval (x : M) (hx : x ∈ S) : f x = 1 ∨ f x = -1 := by
    have hn₁ := (hp₁ x (hS₁ hx)).1
    rcases hsign x hx with heq | heq
    · exact Or.inl (by dsimp only [f]; rw [heq, hn₁])
    · exact Or.inr (by dsimp only [f]; rw [heq]; simp only [map_neg, neg_apply, hn₁])
  have hfzero (x : M) (hx : x ∈ S) : f x ≠ 0 := by
    rcases hfval x hx with h | h <;> rw [h] <;> norm_num
  have horient : ∃ σ : ℝ, (σ = 1 ∨ σ = -1) ∧ ∀ x ∈ S, Y₀ x = σ • Y₁ x := by
    rcases hS.mapsTo_Ioi_or_Iio hf hfzero with hpos | hneg
    · refine ⟨1, Or.inl rfl, ?_⟩
      intro x hx
      rw [one_smul]
      rcases hsign x hx with heq | heq
      · exact heq
      · have hp : 0 < f x := hpos hx
        have hn₁ := (hp₁ x (hS₁ hx)).1
        have hn : f x = -1 := by
          dsimp only [f]
          rw [heq]
          simp only [map_neg, neg_apply, hn₁]
        linarith
    · refine ⟨-1, Or.inr rfl, ?_⟩
      intro x hx
      rw [neg_one_smul]
      rcases hsign x hx with heq | heq
      · have hn : f x < 0 := hneg hx
        have hn₁ := (hp₁ x (hS₁ hx)).1
        have hp : f x = 1 := by dsimp only [f]; rw [heq, hn₁]
        linarith
      · exact heq
  obtain ⟨σ, hσ, heq⟩ := horient
  refine ⟨σ, hσ, ?_⟩
  intro x hx
  have hg₀ := (hp₀ x (hS₀ hx)).2.2.2.2.2.2.2
  have hg₁ := (hp₁ x (hS₁ hx)).2.2.2.2.2.2.2
  let a := gradFun g C₀.axial x
  let b := gradFun g C₁.axial x
  have hdiff : a - σ • b = -(Y₀ x - a) + σ • (Y₁ x - b) := by
    rw [heq x hx, smul_sub]
    abel
  have hneg : Real.sqrt (g.inner x (-(Y₀ x - a)) (-(Y₀ x - a))) =
      Real.sqrt (g.inner x (Y₀ x - a) (Y₀ x - a)) := by
    simp only [map_neg, neg_apply, neg_neg]
  have hnorm : Real.sqrt (g.inner x (σ • (Y₁ x - b)) (σ • (Y₁ x - b))) =
      Real.sqrt (g.inner x (Y₁ x - b) (Y₁ x - b)) := by
    rcases hσ with rfl | rfl
    · rw [one_smul]
    · simp only [neg_one_smul, map_neg, neg_apply, neg_neg]
  have ht := DifferentialGeometry.Geometry.Riemannian.sqrt_inner_add_le
    g x (-(Y₀ x - a)) (σ • (Y₁ x - b))
  rw [← hdiff, hneg, hnorm] at ht
  exact ht.trans ((add_le_add hg₀ hg₁).trans_eq (by ring))

end DifferentialGeometry.Geometry.Neck
