import DifferentialGeometry.Analysis.Parabolic.MaximumPrinciple.SystemSource
import DifferentialGeometry.Geometry.Curvature.DimensionThree.CurvatureReactionRegularity
import DifferentialGeometry.Geometry.Curvature.DimensionThree.CurvatureReactionPositivity

noncomputable section

open Bundle Set CovariantDerivative
open scoped Manifold ContDiff Topology InnerProductSpace

namespace DifferentialGeometry.Analysis.Parabolic

open DifferentialGeometry.Geometry.Connection
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Geometry.Curvature.DimensionThree
open DifferentialGeometry.Geometry.Operator

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M] [T2Space M]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
  [FiniteDimensional ℝ F]
  {V : M → Type*} [TopologicalSpace (TotalSpace F V)]
  [∀ x, NormedAddCommGroup (V x)] [∀ x, InnerProductSpace ℝ (V x)]
  [FiberBundle F V] [VectorBundle ℝ F V]
  [ContMDiffVectorBundle ∞ F V I] [IsContMDiffRiemannianBundle I ∞ F V]

local notation "Q" => fun (x : M) (B : V x →L[ℝ] V x) =>
  (@LinearMap.toContinuousLinearMap ℝ _ (V x) _ _ _ _ _ (V x) _ _ _ _ _ _ _
    (VectorBundle.finiteDimensional ℝ F V x))
    (@curvatureOperatorReactionEndomorphism3 (V x) _ _
      (VectorBundle.finiteDimensional ℝ F V x) (ContinuousLinearMap.toLinearMap B))

theorem curvatureOperator_rank_spatially_constant_and_locally_constant_from_left_on_Icc
    [I.Boundaryless] [ConnectedSpace M]
    (g : ℝ → SmoothRiemannianMetric I M)
    (cov : ℝ → CovariantDerivative I F V)
    {T : ℝ} (hT : 0 < T)
    (hg : ContMDiffOn (𝓘(ℝ, ℝ).prod I)
      (I.prod 𝓘(ℝ, E →L[ℝ] E →L[ℝ] ℝ)) ∞
      (fun p : ℝ × M => (⟨p.2, (g p.1).inner p.2⟩ :
        TotalSpace (E →L[ℝ] E →L[ℝ] ℝ)
          (fun x => TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] ℝ)))
      (Icc 0 T ×ˢ (univ : Set M)))
    (hcovsmooth : ∀ q ∈ Ioo 0 T, ContMDiffCovariantDerivative (cov q) ∞)
    (hcov : ∀ q ∈ Ioo 0 T, (cov q).IsMetricCompatible)
    (A : ℝ → Cₛ^∞⟮I; F →L[ℝ] F, (fun x : M ↦ V x →L[ℝ] V x)⟯)
    (hApos : ∀ q ∈ Icc 0 T, ∀ x, (A q x).IsPositive)
    (hA : ContinuousOn
      (fun p : ℝ × M => (TotalSpace.mk' (F →L[ℝ] F) p.2 (A p.1 p.2) :
        TotalSpace (F →L[ℝ] F) (fun x => V x →L[ℝ] V x)))
      (Icc 0 T ×ˢ (univ : Set M)))
    (hevolution : ∀ q ∈ Ioo 0 T, ∀ x,
      HasDerivAt (fun r ↦ A r x)
        (rawBundleEndomorphismConnLap (I := I) (g q) (cov q)
          (fun y ↦ A q y) x + Q x (A q x)) q) :
    (∀ t ∈ Ioc 0 T, ∀ x y,
      Module.finrank ℝ (A t x).range = Module.finrank ℝ (A t y).range) ∧
    (∀ x, MonotoneOn (fun t => Module.finrank ℝ (A t x).range) (Ioc 0 T)) ∧
    (∀ t ∈ Ioc 0 T, ∀ x,
      ∃ ε ∈ Ioc 0 t, ∀ s ∈ Ioc (t - ε) t,
        Module.finrank ℝ (A s x).range = Module.finrank ℝ (A t x).range) ∧
    ∃ δ ∈ Ioc 0 T, ∃ q : ℕ, ∀ t ∈ Ioc 0 δ, ∀ x,
      Module.finrank ℝ (A t x).range = q := by
  let _ : ∀ x, FiniteDimensional ℝ (V x) :=
    fun x => VectorBundle.finiteDimensional ℝ F V x
  have hzero : ContinuousOn (fun p : ℝ × M =>
      (TotalSpace.mk' E p.2 (0 : TangentSpace I p.2) : TangentBundle I M))
      (Icc 0 T ×ˢ (univ : Set M)) :=
    ((Bundle.contMDiff_zeroSection ℝ (TangentSpace I) (IB := I) (F := E)
      (n := ∞)).continuous.comp continuous_snd).continuousOn
  apply PositiveSystem.finrank_range_spatially_constant_and_locally_constant_of_contMDiffOn_on_Icc
    g cov hT hg hcovsmooth hcov A hApos hA (fun _ _ => 0) hzero
    (fun _ x B => Q x B) ?_ ?_ ?_
  · intro q hq x B hB v hv
    exact (curvatureOperatorReactionEndomorphism3_isPositive hB.toLinearMap).inner_nonneg_left v
  · intro s t hs hst ht K hK R hR
    obtain ⟨L, hL⟩ := curvatureOperatorReactionEndomorphism3_exists_uniform_lipschitzOn_closedBall
      V (Module.finrank ℝ F) (fun x => VectorBundle.finrank_eq ℝ F V x) R
    refine ⟨L, L.coe_nonneg, ?_⟩
    intro q hq x hx B C hB hC hBR hCR
    simpa only [dist_eq_norm] using (hL x).dist_le_mul B
      (mem_closedBall_zero_iff.mpr hBR) C (mem_closedBall_zero_iff.mpr hCR)
  · intro q hq x
    simpa only [map_zero, add_zero] using hevolution q hq x

end DifferentialGeometry.Analysis.Parabolic
