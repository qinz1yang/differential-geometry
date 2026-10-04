import DifferentialGeometry.Geometry.Collapse.CirclePacket
import DifferentialGeometry.Geometry.Collapse.SimultaneousComparisonData

/-!
# LFR07 with the tested residual estimate discharged (consumer of LC83 and LFR07)

`exists_circlePacket_threshold`: there is `η₀ > 0` such that, whenever the pointed complete
Riemannian manifold `(M, q)` is `σ`-close to a complete length space `C` of Hausdorff dimension at
most two with nonnegative four-point comparison and carries a `β`-splitting `F` to `ℝ² × Y`,
`σ, β ≤ η₀`, any supplied smooth rank-two `2`-Lipschitz coordinates `η` within `1/10` of `F`'s
`ℝ²`-coordinate (LFR06's output) give the LC83 enclosures, a proper surjective submersion
`η⁻¹ B(0, 100) → B(0, 100)` with compact connected fibres, and the smooth cutoff `Φ_{8,9}(|η|)`.
The residual estimate is the tree's LPA03 tier `exists_simultaneous_circle_residual_threshold`.
-/

set_option autoImplicit false

noncomputable section

open Set Function Metric Bundle
open scoped ContDiff Manifold Topology

namespace DifferentialGeometry.Geometry.Collapse

open DifferentialGeometry.Topology.Ehresmann DifferentialGeometry.Geometry.Riemannian
open GC.MetricGeometry DifferentialGeometry.Geometry.Comparison.Toponogov

local notation "ℝ²" => EuclideanSpace ℝ (Fin 2)

universe uE uH u v w

variable {E : Type uE} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
  {H : Type uH} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {M : Type u} [MetricSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [SigmaCompactSpace M]

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace

variable [RiemannianBundle (fun x : M => TangentSpace I x)]
  [IsRiemannianManifold I M] [CompleteSpace M]
  [IsContinuousRiemannianBundle E (fun x : M => TangentSpace I x)]

theorem exists_circlePacket_threshold (g : SmoothRiemannianMetric I M) (hEnorm : IsMetricNorm g)
    (q : M) :
    ∃ η₀ : ℝ, 0 < η₀ ∧
      ∀ (C : Type v) [MetricSpace C] [CompleteSpace C] (c : C),
      (∀ x y : C, ∀ e : ℝ, 0 < e →
        ∃ γ : unitInterval → C, Continuous γ ∧ γ 0 = x ∧ γ 1 = y ∧
          eVariationOn γ univ < ENNReal.ofReal (dist x y + e)) →
      dimH (univ : Set C) ≤ 2 → fourPointComparison 0 (univ : Set C) →
      ∀ (Y : Type w) [MetricSpace Y] (a : Y) (σ β : ℝ), σ ≤ η₀ → β ≤ η₀ →
        KleinerLottApprox q c σ →
        ∀ F : KleinerLottApprox q (WithLp.toLp 2 ((0 : ℝ²), a)) β,
        ∀ η : M → ℝ², ∀ hη : ContMDiffOn I 𝓘(ℝ, ℝ²) ∞ η (ball q 200),
          (∀ x ∈ ball q 200, Surjective (mfderiv I 𝓘(ℝ, ℝ²) η x)) →
          LipschitzOnWith 2 η (ball q 200) → η q = 0 →
          (∀ x ∈ ball q 200, ‖η x - (F.toFun x).fst‖ < 1 / 10) →
          (∀ x ∈ ball q 200, ‖η x‖ < 100 → x ∈ ball q 102) ∧
          (∀ x ∈ ball q 200, η x = 0 → x ∈ ball q 2) ∧
          IsProperMap (diskPreimageMap (ball q 200) isOpen_ball η hη.continuousOn 100) ∧
          Surjective (diskPreimageMap (ball q 200) isOpen_ball η hη.continuousOn 100) ∧
          (∀ z, IsConnected
            (diskPreimageMap (ball q 200) isOpen_ball η hη.continuousOn 100 ⁻¹' {z})) ∧
          ∃ ζ : M → ℝ, ContMDiff I 𝓘(ℝ, ℝ) ∞ ζ ∧ HasCompactSupport ζ ∧
            ∀ x ∈ ball q 200, ‖η x‖ ≤ 8 → ζ x = 1 := by
  obtain ⟨η₁, hη₁, -, hres⟩ := exists_simultaneous_circle_residual_threshold.{u, v, w}
  refine ⟨min η₁ (1 / 200), lt_min hη₁ (by norm_num), ?_⟩
  intro C _ _ c hlen hdim hcomp Y _ a σ β hσ hβ f F η hη hrank hlip hq hclose
  have hres' : ∀ x ∈ ball q 200, dist (F.toFun x).snd a < 1 := fun x hx =>
    hres M q C c hlen hdim hcomp Y a σ β (hσ.trans (min_le_left _ _))
      (hβ.trans (min_le_left _ _)) f F x ((mem_ball.mp hx).le.trans (by norm_num))
  obtain ⟨h102, h2, ⟨-, -, hprop, hsurj, hfib, -⟩, ζ, hζ, hζc, -, hζ1, -⟩ :=
    circlePacket_of_rank_two_coordinates g hEnorm F (hβ.trans (min_le_right _ _)) hres' hη hrank
      hlip hq hclose
  exact ⟨h102, h2, hprop, hsurj, fun z => (hfib z).2, ζ, hζ, hζc, hζ1⟩

end DifferentialGeometry.Geometry.Collapse
