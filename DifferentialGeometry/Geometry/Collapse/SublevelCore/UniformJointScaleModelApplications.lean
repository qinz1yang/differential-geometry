import DifferentialGeometry.Geometry.Collapse.SublevelCore.UniformJointScaleModel

/-!
# Consumer of the LC58 binding: a uniformly bounded ball radius with the model's smooth type

From `exists_uniform_scale_interval_joint_witnesses` (with `ρ' = 1`): for `α > α₀` every point `p`
has an open ball `B(p, r)` with `T ρ_α(p) ≤ r ≤ V ρ_α(p)` diffeomorphic to one of the models.
-/

set_option autoImplicit false

noncomputable section

open Bundle Manifold Set Real Filter
open scoped Topology ContDiff Manifold NNReal
open DifferentialGeometry.Geometry.Riemannian
open DifferentialGeometry.Geometry.Operator
open DifferentialGeometry.Analysis.Calculus
open GC.MetricGeometry

namespace DifferentialGeometry.Geometry.Collapse

open DifferentialGeometry.CheegerGromovCompactness

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace

variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
  {H : Type} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]

/-- **Consumer of `exists_uniform_scale_interval_joint_witnesses`.** For `α > α₀` every point
`p ∈ M^α` has a radius `r ∈ [T ρ_α(p), V ρ_α(p)]` and a model `N_b` with `B(p, r) ≃ N_b`. -/
theorem exists_uniform_radius_ball_model_type {mdim : ℕ}
    (hdim : Module.finrank ℝ E = mdim + 1)
    {M : ℕ → Type} [mM : ∀ α, MetricSpace (M α)] [∀ α, ChartedSpace H (M α)]
    [∀ α, IsManifold I ∞ (M α)] [∀ α, SigmaCompactSpace (M α)] [∀ α, ConnectedSpace (M α)]
    [hMc : ∀ α, CompleteSpace (M α)]
    (g : ∀ α, SmoothRiemannianMetric I (M α))
    (hmetric : ∀ α a b, riemannianEDistOf (g α) a b = ENNReal.ofReal (dist a b))
    (ρ : ∀ α, M α → ℝ) (hρ : ∀ α x, 0 < ρ α x)
    {ι : Type} {N C : ι → Type} [mN : ∀ b, MetricSpace (N b)] [∀ b, ChartedSpace H (N b)]
    [∀ b, IsManifold I ∞ (N b)] [∀ b, SigmaCompactSpace (N b)] [∀ b, ConnectedSpace (N b)]
    [∀ b, RiemannianBundle (fun x : N b => TangentSpace I x)] [∀ b, IsRiemannianManifold I (N b)]
    [∀ b, CompleteSpace (N b)]
    [∀ b, IsContinuousRiemannianBundle E (fun x : N b => TangentSpace I x)]
    [∀ b, T2Space (TangentBundle I (N b))] [mC : ∀ b, MetricSpace (C b)]
    (gN : ∀ b, SmoothRiemannianMetric I (N b)) (hgN : ∀ b, IsMetricNorm (I := I) (gN b))
    (hsecN : ∀ b x, SectionalBoundedBelowAt (gN b) x 0)
    (n : ∀ b, N b) (o : ∀ b, C b) (Hc : ∀ b, RadialConeData (o b))
    (hcone : ∀ b : ι, ∀ τ : ℝ, 0 < τ → τ < 1 → ∃ R₀ : ℝ, ∀ R : ℝ, ∀ hR : 0 < R, R₀ ≤ R →
      Nonempty (@KleinerLottApprox (N b) (C b) ((mN b).rescale R⁻¹ (inv_pos.mpr hR)) (mC b)
        (n b) (o b) τ))
    (hmodel : ∀ a : ℕ → ℕ, Tendsto a atTop atTop → ∀ z : ∀ j, M (a j),
      ∃ b : ι, ∃ k : ℕ → ℕ, StrictMono k ∧
        @PointedGHConverges (fun j => M (a (k j)))
          (fun j => (mM (a (k j))).rescale (ρ (a (k j)) (z (k j)))⁻¹ (inv_pos.mpr (hρ _ _)))
          (N b) (mN b) (fun j => z (k j)) (n b) ∧
        (∃ jm : ∀ j, PartialDiffeomorph I I (N b) (M (a (k j))) ∞, (∀ j, jm j (n b) = z (k j)) ∧
          ∀ r : ℝ, 0 < r → ∃ i₀ : ℕ, ∃ hsub : ∀ l,
            ((⟨Metric.ball (n b) r, Metric.isOpen_ball⟩ : TopologicalSpace.Opens (N b)) :
              Set (N b)) ⊆ (jm (l + i₀)).source,
            ∀ K : Set (⟨Metric.ball (n b) r, Metric.isOpen_ball⟩ : TopologicalSpace.Opens (N b)),
              IsCompact K → MetricCPConvergenceOn K 1
                (fun l => PartialDiffeomorph.pullbackMetricOn (jm (l + i₀)) _ (hsub l)
                  (scaleMetric ((ρ (a (k (l + i₀))) (z (k (l + i₀))))⁻¹ ^ 2)
                    (pow_pos (inv_pos.mpr (hρ _ _)) 2) (g (a (k (l + i₀))))))
                ((gN b).restrictOpen _) ((gN b).restrictOpen _)) ∧
        ∃ Hb : ℕ → ℝ, Tendsto Hb atTop atTop ∧ ∀ j,
          ∀ y ∈ @Metric.ball (M (a (k j)))
            ((mM (a (k j))).rescale (ρ (a (k j)) (z (k j)))⁻¹
              (inv_pos.mpr (hρ _ _))).toPseudoMetricSpace (z (k j)) (Hb j),
            SectionalBoundedBelowAt (scaleMetric ((ρ (a (k j)) (z (k j)))⁻¹ ^ 2)
              (pow_pos (inv_pos.mpr (hρ _ _)) 2) (g (a (k j)))) y (-((Hb j)⁻¹ ^ 2)))
    {δ ε e T : ℝ} (hδ : 0 < δ) (hδ1 : δ < 1) (hε : 0 < ε) (hε1 : ε < 1) (he : 0 < e)
    (he1 : e < 1 / 40) :
    ∃ V : ℝ, T ≤ V ∧ ∃ α₀ : ℕ, ∀ α : ℕ, α₀ < α → ∀ p : M α,
      ∃ r ∈ Icc (T * ρ α p) (V * ρ α p), ∃ b : ι, ∃ Ψ : PartialDiffeomorph I I (M α) (N b) ∞,
        Ψ.source = Metric.ball p r ∧ Ψ.target = univ := by
  obtain ⟨V, hTV, α₀, hall⟩ := exists_uniform_scale_interval_joint_witnesses hdim g hmetric ρ hρ
    gN hgN hsecN n o Hc hcone hmodel hδ hδ1 hε hε1 he he1
  refine ⟨V, hTV, α₀, fun α hα p => ?_⟩
  obtain ⟨s, hsI, hs, b, -, -, hball⟩ := hall α hα p
  obtain ⟨Ψ, hΨs, hΨt⟩ := hball 1 ⟨by norm_num, by norm_num⟩
  refine ⟨s * ρ α p, ⟨mul_le_mul_of_nonneg_right hsI.1 (hρ α p).le,
    mul_le_mul_of_nonneg_right hsI.2 (hρ α p).le⟩, b, Ψ, ?_, hΨt⟩
  rw [hΨs, one_mul]

end DifferentialGeometry.Geometry.Collapse
