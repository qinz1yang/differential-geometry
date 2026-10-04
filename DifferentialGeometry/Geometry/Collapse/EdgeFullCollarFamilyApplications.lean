import DifferentialGeometry.Geometry.Collapse.EdgeFullCollarFamily

/-!
# Consumer: one smoothing, rank two of the original pair at every centre of a finite family

`exists_edge_full_collar_family` at the real values `γ = 1/1000`, `β₂ = 10⁻⁷`, for a finite family
of centres all sharing ONE smoothing `F`: at every centre, in its normalization, the original pair
`(f, F/ρ)` is onto `ℝ²` at every point of the own-scale ball of every band point, and the
normalized smoothing `F/ρ(p)` is within `μΔ` of the normalized distance to `A`.
-/

set_option autoImplicit false

noncomputable section

open Bundle Manifold Set Metric
open scoped Topology ContDiff Manifold NNReal
open DifferentialGeometry.Geometry.Riemannian
open DifferentialGeometry.Geometry.Riemannian.Exponential
open GC.MetricGeometry

namespace DifferentialGeometry.Geometry.Collapse

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace

universe uE uH uM uY

/-- At every centre of a finite family sharing one smoothing, the original pair has rank two on
the whole band (quality `γ = 1/1000`, `β₂ = 10⁻⁷`). -/
theorem edge_family_shared_smoothing_rankTwo :
    ∃ σ₀ : ℝ, 0 < σ₀ ∧ ∃ Δ₀ : ℝ, 0 < Δ₀ ∧ ∀ Δ : ℝ, Δ₀ ≤ Δ →
      ∃ τ₀ : ℝ, 0 < τ₀ ∧ ∃ κ₀ : ℝ, 0 < κ₀ ∧ ∃ b₀ : ℝ, 0 < b₀ ∧
      ∀ (σ ε μ τ κ b : ℝ) (Λ : ℝ≥0), 0 ≤ σ → σ ≤ σ₀ → 0 < ε → ε < 1 / 100 →
        0 < μ → μ ≤ 1 / 1000000 → 0 < τ → τ ≤ τ₀ → 140 * Real.sqrt τ < ε ^ 2 / 20 →
        0 ≤ κ → κ ≤ κ₀ → 0 < b → b < b₀ → 100 * Δ * Λ ≤ 1 / 1000000 →
        2 * ε + 300 * Δ * Λ + Real.sqrt (504000 / Δ + 3780 * τ) < 1 / 1000000 →
      ∀ (E : Type uE) [NormedAddCommGroup E] [NormedSpace ℝ E]
        [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
        (H : Type uH) [TopologicalSpace H] (I : ModelWithCorners ℝ E H) [I.Boundaryless]
        (M : Type uM) [m : MetricSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
        [SigmaCompactSpace M] [hM : CompleteSpace M]
        [RiemannianBundle (fun x : M => TangentSpace I x)] [IsRiemannianManifold I M]
        [IsContinuousRiemannianBundle E (fun x : M => TangentSpace I x)]
        (g : SmoothRiemannianMetric I M) (hEnorm : IsMetricNorm (I := I) g)
        (A : Set M) (P : Finset M) (Q : M → M → WithLp 2 (ℝ × ℝ)) (ρ : M → ℝ)
        (hρpos : ∀ x, 0 < ρ x),
      P.Nonempty → IsClosed A → (∀ p ∈ P, Q p p = 0) →
      (∀ p ∈ P, ∀ x ∈ ball p (200 * (Δ * ρ p)), ∀ y ∈ ball p (200 * (Δ * ρ p)),
        |dist (Q p x) (Q p y) - dist x y| ≤ τ * (Δ * ρ p)) →
      (∀ p ∈ P, ∀ x ∈ ball p (200 * (Δ * ρ p)), 0 ≤ (Q p x).snd) →
      (∀ p ∈ P, ∀ z : WithLp 2 (ℝ × ℝ), |z.fst| ≤ 100 * (Δ * ρ p) →
        z.snd ∈ Icc 0 (100 * (Δ * ρ p)) →
          ∃ x ∈ ball p (200 * (Δ * ρ p)), dist (Q p x) z ≤ τ * (Δ * ρ p)) →
      (∀ p ∈ P, p ∈ A) →
      (∀ p ∈ P, ∀ a ∈ A ∩ ball p (190 * (Δ * ρ p)), (Q p a).snd ≤ τ * (Δ * ρ p)) →
      (∀ p ∈ P, ∀ t : ℝ, |t| ≤ 100 * (Δ * ρ p) →
        ∃ a ∈ A ∩ ball p (190 * (Δ * ρ p)),
          dist (Q p a) (WithLp.toLp 2 (t, (0 : ℝ))) ≤ τ * (Δ * ρ p)) →
      (∀ p ∈ P, ∀ z ∈ ball p (10000 * (Δ * ρ p)),
        SectionalBoundedBelowAt g z (-(κ / ρ p) ^ 2)) →
      LipschitzWith Λ ρ → ContMDiff I 𝓘(ℝ, ℝ) ∞ ρ →
      ∃ F : M → ℝ, ∀ p ∈ P,
        (letI := m.rescale (ρ p)⁻¹ (inv_pos.mpr (hρpos p))
          ∀ x, |F x / ρ p - infDist x A| ≤ μ * Δ) ∧
        (have hmetric := riemannianEDistOf_eq_ofReal_dist g hEnorm
        letI := m.rescale (ρ p)⁻¹ (inv_pos.mpr (hρpos p))
        letI := radialScaledBundle g (ρ p)⁻¹ (inv_pos.mpr (hρpos p))
        letI : IsContinuousRiemannianBundle E (fun x : M => TangentSpace I x) :=
          radialScaledContinuous g (ρ p)⁻¹ (inv_pos.mpr (hρpos p))
        letI : IsRiemannianManifold I M :=
          radialScaledManifold (m := m) g hmetric (ρ p)⁻¹ (inv_pos.mpr (hρpos p))
        letI : CompleteSpace M :=
          (m.rescale_completeSpace_iff (ρ p)⁻¹ (inv_pos.mpr (hρpos p))).mpr hM
        let gR : SmoothRiemannianMetric I M :=
          scaleMetric ((ρ p)⁻¹ ^ 2) (pow_pos (inv_pos.mpr (hρpos p)) 2) g
        have hnR : IsMetricNorm (I := I) (M := M) gR := isMetricNorm_of_riemannianBundle gR
        ∀ (Y : Type uY) [MetricSpace Y] (y₀ : Y)
          (α : KleinerLottApprox p (WithLp.toLp 2 ((0 : ℝ), y₀)) b),
        (∀ z ∈ ball p b⁻¹, SectionalBoundedBelowAt gR z (-b ^ 2)) →
        (∀ z ∈ ball p (200 * Δ), (Q p z).fst = ρ p * (α.toFun z).fst) →
        ∀ f : M → ℝ, ContMDiffOn I 𝓘(ℝ, ℝ) ∞ f (ball p (100 * Δ)) →
        LipschitzWith (Real.toNNReal (1 + σ)) f →
        (∀ x ∈ ball p (100 * Δ), |f x - (α.toFun x).fst| ≤ μ * Δ) →
        (∀ x ∈ ball p (100 * Δ), ∀ x' ∈ ball p (1000 * Δ), 100 * Δ < dist x x' →
          ∀ w : TangentSpace I x, gR.inner x w w = 1 →
          intrinsicGeodesic gR hnR x w (dist x x') = x' →
          |mvfderiv (I := I) f x w - ((α.toFun x').fst - (α.toFun x).fst) / dist x x'| < σ) →
        ∀ x ∈ ball p (100 * Δ), |f x| ≤ 10 * Δ →
          Δ / 10 ≤ F x / ρ p / (ρ x / ρ p) → F x / ρ p / (ρ x / ρ p) ≤ 10 * Δ →
          ∀ y ∈ ball x (100 * (ρ x / ρ p)), Function.Surjective (mvfderiv (I := I)
            (edgeReferenceCoordinates ![f, fun z => F z / ρ p / (ρ z / ρ p)]) y)) := by
  obtain ⟨σ₀, hσ₀, Δ₀, hΔ₀, hfam⟩ := exists_edge_full_collar_family.{uE, uH, uM, uY}
    (β := 1 / 10000000) (γ := 1 / 1000) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num)
  refine ⟨σ₀, hσ₀, Δ₀, hΔ₀, fun Δ hΔ => ?_⟩
  obtain ⟨τ₀, hτ₀, κ₀, hκ₀, b₀, hb₀, hΔfam⟩ := hfam Δ hΔ
  refine ⟨τ₀, hτ₀, κ₀, hκ₀, b₀, hb₀, ?_⟩
  intro σ ε μ τ κ b Λ hσ hσσ₀ hε hε1 hμ hμ1 hτ hττ₀ hθ hκ hκκ₀ hb hbb₀ hlam hbudget
    E _ _ _ _ H _ I _ M m _ _ _ hM _ _ _ g hEnorm A P Q ρ hρpos hP hA hQp hdist hheight hcover
    hpA hborder hbordercover hsec hρ hρs
  obtain ⟨F, -, -, hcent⟩ := hΔfam σ ε μ τ κ b Λ hσ hσσ₀ hε hε1 hμ hμ1 hτ hττ₀ hθ hκ hκκ₀ hb
    hbb₀ hlam (by linarith) E H I M g hEnorm A P Q ρ hρpos hP hA hQp hdist hheight hcover hpA
    hborder hbordercover hsec hρ hρs
  refine ⟨F, fun p hp => ⟨radialScaled_value_clause (A := A) (hρpos p) (hcent p hp).1, ?_⟩⟩
  intro hmetric gR hnR Y _ y₀ α hsecb hQα f hfs hfL hfval htest x hx hfx hη hη' y hy
  have hJall := (hcent p hp).2 Y y₀ α hsecb hQα f hfs hfL hfval htest x hx hfx hη hη'
  obtain ⟨_hq, _hΦ, hJ⟩ := hJall
  exact hJ.2.1 y hy

end DifferentialGeometry.Geometry.Collapse
