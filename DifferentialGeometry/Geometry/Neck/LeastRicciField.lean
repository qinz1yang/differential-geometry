import DifferentialGeometry.Geometry.Neck.Chart
import DifferentialGeometry.Geometry.Curvature.LeastRicciOverlap
import DifferentialGeometry.Geometry.Gradient.SignedDifference
import DifferentialGeometry.Geometry.Metric.Coordinates.InnerExpansion

noncomputable section
open Set Bundle
open scoped Manifold ContDiff
open DifferentialGeometry DifferentialGeometry.Geometry.Operator
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Geometry.Gradient

namespace DifferentialGeometry.Geometry.Neck

theorem cylindricalChart.exists_sign_axial_gradient_bound
    {F H M : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
    [TopologicalSpace H] {J : ModelWithCorners ℝ F H}
    [TopologicalSpace M] [ChartedSpace H M] [IsManifold J ∞ M] [T2Space M]
    [BoundarylessManifold J M]
    (C₀ C₁ : cylindricalChart J (M := M)) (g : SmoothRiemannianMetric J M)
    {U₀ : Set C₀.domain} {U₁ : Set C₁.domain} (hU₀ : IsOpen U₀) (hU₁ : IsOpen U₁)
    (ε₀ ε₁ : ℝ) (hε₀ : ε₀ < 1 / 200000) (hε₁ : ε₁ < 1 / 200000)
    (hsmall₀ : C₀.metricCloseOn g ε₀ U₀) (hsmall₁ : C₁.metricCloseOn g ε₁ U₁)
    {x : M} (hx₀ : x ∈ C₀.region U₀) (hx₁ : x ∈ C₁.region U₁) :
    ∃ σ : ℝ, (σ = 1 ∨ σ = -1) ∧
      Real.sqrt (g.inner x (gradFun g C₀.axial x - σ • gradFun g C₁.axial x)
        (gradFun g C₀.axial x - σ • gradFun g C₁.axial x)) ≤ 184712 * (ε₀ + ε₁) := by
  obtain ⟨ν₀, Y₀, _, _, _, hp₀⟩ :=
    C₀.exists_least_ricci_field_close_to_gradient g hU₀ ε₀ hε₀ hsmall₀
  obtain ⟨ν₁, Y₁, _, _, _, hp₁⟩ :=
    C₁.exists_least_ricci_field_close_to_gradient g hU₁ ε₁ hε₁ hsmall₁
  obtain ⟨hn₀, he₀, hm₀, _, _, _, _, hg₀⟩ := hp₀ x hx₀
  obtain ⟨hn₁, he₁, hm₁, _, hs₁, _, _, hg₁⟩ := hp₁ x hx₁
  obtain ⟨_, hsign⟩ := least_ricci_eigenpair_eq_or_eq_neg g x
    (ν₀ x) (ν₁ x) (Y₀ x) (Y₁ x) hn₀ hn₁ he₀ he₁ hm₀ hm₁ hs₁
  have hσ : ∃ σ : ℝ, (σ = 1 ∨ σ = -1) ∧ Y₀ x = σ • Y₁ x := by
    rcases hsign with h | h
    · exact ⟨1, Or.inl rfl, by simpa only [one_smul] using h⟩
    · exact ⟨-1, Or.inr rfl, by simpa only [neg_one_smul] using h⟩
  obtain ⟨σ, hσ, heq⟩ := hσ
  refine ⟨σ, hσ, ?_⟩
  let a := gradFun g C₀.axial x
  let b := gradFun g C₁.axial x
  have hdiff : a - σ • b = -(Y₀ x - a) + σ • (Y₁ x - b) := by
    rw [heq, smul_sub]
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

theorem exists_compatible_least_ricci_fields
    {ι F H M : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
    [TopologicalSpace H] {J : ModelWithCorners ℝ F H}
    [TopologicalSpace M] [ChartedSpace H M] [IsManifold J ∞ M] [T2Space M]
    [BoundarylessManifold J M]
    (g : SmoothRiemannianMetric J M) (C : ι → cylindricalChart J (M := M))
    (U : ∀ i, Set (C i).domain) (hU : ∀ i, IsOpen (U i))
    (ε δ : ℝ) (hε : ε < 1 / 200000) (hδ : 92354 * ε + δ < 1)
    (hsmall : ∀ i, (C i).metricCloseOn g ε (U i))
    (σ : ι → ι → ℝ) (hσ : ∀ i j, σ i j = 1 ∨ σ i j = -1)
    (hoverlap : ∀ i j, ∀ x ∈ (C i).region (U i), x ∈ (C j).region (U j) →
      Real.sqrt (g.inner x (gradFun g (C i).axial x - σ i j • gradFun g (C j).axial x)
        (gradFun g (C i).axial x - σ i j • gradFun g (C j).axial x)) ≤ δ) :
    ∃ (ν : ι → M → ℝ) (Y : ι → ∀ x : M, TangentSpace J x),
      (∀ i, ContMDiffOn J 𝓘(ℝ) ∞ (C i).axial (C i).target ∧
        ContMDiffOn J 𝓘(ℝ) ∞ (ν i) ((C i).region (U i)) ∧
        ContMDiffOn J J.tangent ∞ (fun x ↦ (⟨x, Y i x⟩ : TangentBundle J M)) ((C i).region (U i)) ∧
        ∀ x ∈ (C i).region (U i), g.inner x (Y i x) (Y i x) = 1 ∧
          ricciSharp g x (Y i x) = ν i x • Y i x ∧
          (∀ z : TangentSpace J x, g.inner x z z = 1 → ν i x ≤ ricciTensor g x z z) ∧
          |ν i x| ≤ 5772 * (C i).scale * ε ∧
          Module.End.eigenspace (ricciSharp g x).toLinearMap (ν i x) = Submodule.span ℝ {Y i x} ∧
          0 < mvfderiv J (C i).axial x (Y i x) ∧
          |mvfderiv J (C i).axial x (Y i x) - 1| ≤ 92354 * ε) ∧
      ∀ i j, ∀ x ∈ (C i).region (U i), x ∈ (C j).region (U j) →
        ν i x = ν j x ∧ Y i x = σ i j • Y j x ∧
          |mvfderiv J (C i).axial x (σ i j • Y j x) - 1| ≤ 92354 * ε + δ := by
  classical
  choose ν Y hu hν hY hp using fun i ↦
    (C i).exists_least_ricci_field g (hU i) ε hε (hsmall i)
  refine ⟨ν, Y, fun i ↦ ⟨hu i, hν i, hY i, hp i⟩, ?_⟩
  intro i j x hxi hxj
  obtain ⟨hin, hie, him, _, _, _, hid⟩ := hp i x hxi
  obtain ⟨hjn, hje, hjm, _, hjs, _, hjd⟩ := hp j x hxj
  have hc (z : TangentSpace J x) :
      |mvfderiv J (C i).axial x z - σ i j * mvfderiv J (C j).axial x z| ≤
        δ * Real.sqrt (g.inner x z z) :=
    (abs_mvfderiv_signed_difference_le_gradient_norm g (C i).axial (C j).axial (σ i j) x z).trans
      (mul_le_mul_of_nonneg_right (hoverlap i j x hxi hxj) (Real.sqrt_nonneg _))
  exact least_ricci_eigenpair_eq_of_signed_covector_error g x
    (mvfderiv J (C i).axial x).toLinearMap (mvfderiv J (C j).axial x).toLinearMap
    (ν i x) (ν j x) (Y i x) (Y j x) hin hjn hie hje him hjm hjs
    (σ i j) (92354 * ε) (92354 * ε) δ (hσ i j) hid hjd (by linarith) hδ hc

end DifferentialGeometry.Geometry.Neck
