import DifferentialGeometry.Geometry.Collapse.SublevelCore.FieldBandSmooth

/-!
# Consumer of the smooth LC33 product: the row's normalizations

`radialBand_gradient_diffeomorph_height` reads off LC33's normalizations `η (F (x, u)) = u` and
`F (x, 1) = x` for the diffeomorphism of manifolds with boundary
`F : η⁻¹(1) × [1/8, 3] ≅ η⁻¹[1/8, 3]` of `radialBand_gradient_diffeomorph`.
-/

set_option autoImplicit false

noncomputable section

open Set Filter Function Bundle
open scoped Manifold ContDiff Topology NNReal

namespace DifferentialGeometry.Geometry.Collapse

open DifferentialGeometry.Topology.Morse
open DifferentialGeometry.Geometry.Riemannian
open DifferentialGeometry.Geometry.Operator

variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {M : Type} [MetricSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [SigmaCompactSpace M]

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace

variable [RiemannianBundle (fun x : M => TangentSpace I x)]
  [IsRiemannianManifold I M] [CompleteSpace M]
  [IsContinuousRiemannianBundle E (fun x : M => TangentSpace I x)]

/-- LC33's normalizations for the smooth product: `η ∘ F = pr₂` and `F (·, 1) = id`. -/
theorem radialBand_gradient_diffeomorph_height {m : ℕ} (hdim : Module.finrank ℝ E = m + 1)
    (g : SmoothRiemannianMetric I M) (hEnorm : IsMetricNorm (I := I) (M := M) g) {p : M}
    {η : M → ℝ} {ε : ℝ≥0} {e : ℝ} (hε1 : (ε : ℝ) < 1) (he : e < 1 / 40)
    (hclose : ∀ x, |η x - dist p x| < e) (hlip : LipschitzWith ε (fun x => η x - dist p x))
    {W : Set M} (hW : IsOpen W) (hCW : ∀ x, 1 / 10 ≤ dist p x → dist p x ≤ 10 → x ∈ W)
    (hηW : ContMDiffOn I 𝓘(ℝ, ℝ) ∞ η W)
    (hgrad : ∀ x, 1 / 10 ≤ dist p x → dist p x ≤ 10 →
      (1 - (ε : ℝ)) ^ 2 ≤
        g.inner x (gradientFun (I := I) g η x) (gradientFun (I := I) g η x)) :
    haveI : Fact ((1 / 8 : ℝ) < 3) := ⟨by norm_num⟩
    ∃ (cs₁ : ChartedSpace (MorseModel m) ↥({x | η x = 1} : Set M))
      (cs₂ : ChartedSpace (MorseHalfSpace m) ↥(η ⁻¹' Icc (1 / 8 : ℝ) 3)),
      letI := cs₁
      letI := cs₂
      ∃ d : Diffeomorph ((𝓘(ℝ, MorseModel m)).prod (𝓡∂ 1)) (morseModelWithCornersHalfSpace m)
          (↥({x | η x = 1} : Set M) × Icc (1 / 8 : ℝ) 3) ↥(η ⁻¹' Icc (1 / 8 : ℝ) 3) ∞,
        (∀ q, η (d q : M) = q.2) ∧
        ∀ x : ↥({x | η x = 1} : Set M), (d (x, ⟨1, by norm_num, by norm_num⟩) : M) = x := by
  obtain ⟨Φ, hΦ0, -, -, -, hval, -, -, -, -, cs₁, cs₂, -, -, -, -, -, d, hd, -, -⟩ :=
    radialBand_gradient_diffeomorph hdim g hEnorm hε1 he hclose hlip hW hCW hηW hgrad
  refine ⟨cs₁, cs₂, d, fun q => ?_, fun x => ?_⟩
  · have hx : η (q.1 : M) = 1 := q.1.2
    have h := hval q.1 (by rw [hx]; norm_num) q.2 q.2.2
    rw [hx] at h
    rw [hd q]
    exact h
  · rw [hd, sub_self, hΦ0]
    rfl

end DifferentialGeometry.Geometry.Collapse
