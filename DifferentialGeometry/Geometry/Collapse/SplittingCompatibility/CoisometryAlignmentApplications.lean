import DifferentialGeometry.Geometry.Collapse.SplittingCompatibility.RiemannianOverlapAlignment
import DifferentialGeometry.Geometry.Metric.Approximation.TwoStratumPacketKernelsApplications

/-!
# Consumers of the AC76/AC79 coisometry alignment

* `unitPlaneSplitting_coisometry_alignment`: the all-rank FC21 alignment
  (`exists_coisometry_alignment_of_splittingCompatible`) on the identity splitting of `ℝ² × {pt}`.
* `planeSplitting_recentered_alignment`: AC79/AC80 + FC21
  (`exists_recentered_coisometry_alignment`) for the identity splitting at a small error, at any new
  centre within distance one.
* `exists_two_stratum_overlap_coisometry_parameter_riemannian`: the AC79 → AC76 → FC21 chain
  (`exists_overlap_coisometry_parameter_riemannian`, which consumes the Riemannian AC76 producer
  `exists_splitting_compatibility_parameter_riemannian` and `KleinerLottApprox.weaken`) in FC07's
  two-stratum setting: ranks `(2,2)`, `τ = 1/100`, radius `40`.
-/

set_option autoImplicit false

noncomputable section

open Set Metric Bundle Manifold
open DifferentialGeometry
open DifferentialGeometry.Geometry.Metric
open scoped Manifold ContDiff ENNReal
open DifferentialGeometry.Geometry.Riemannian
open DifferentialGeometry.Geometry.Comparison.Toponogov

namespace GC.MetricGeometry

/-- FC21 (all ranks) on the identity splitting of `ℝ² × {pt}`. -/
theorem unitPlaneSplitting_coisometry_alignment :
    ∃ Λ : EuclideanSpace ℝ (Fin 2) →L[ℝ] EuclideanSpace ℝ (Fin 2), ∃ c,
      Λ.comp (ContinuousLinearMap.adjoint Λ) = ContinuousLinearMap.id ℝ _ ∧
      ∀ x ∈ ball (WithLp.toLp 2 ((0 : EuclideanSpace ℝ (Fin 2)), ())) (1 / 10)⁻¹,
        ‖(unitPlaneSplitting.toFun x).fst‖ ≤ 4 →
          ‖(unitPlaneSplitting.toFun x).fst - Λ (unitPlaneSplitting.toFun x).fst - c‖ ≤
            (1 + 24 * ((2 : ℕ) : ℝ)) * (1 / 10) :=
  exists_coisometry_alignment_of_splittingCompatible unitPlaneSplitting unitPlaneSplitting
    unitPlaneSplitting_compatible (by norm_num) (by norm_num) (by norm_num)

/-- The identity splitting of `ℝ² × {pt}` at error `ε`. -/
def planeSplitting (ε : ℝ) (hε : 0 < ε) (hεone : ε < 1) :
    KleinerLottApprox (WithLp.toLp 2 ((0 : EuclideanSpace ℝ (Fin 2)), ()))
      (WithLp.toLp 2 ((0 : EuclideanSpace ℝ (Fin 2)), ())) ε :=
  (IsometryEquiv.refl _).toKleinerLottApprox rfl hε hεone

theorem planeSplitting_compatible (ε : ℝ) (hε : 0 < ε) (hεone : ε < 1) :
    SplittingCompatible (planeSplitting ε hε hεone) (planeSplitting ε hε hεone) ε := by
  let unique_AC7679 : Unique (EuclideanSpace ℝ (Fin (2 - 2))) :=
    { default := 0
      uniq := fun v => by ext i; exact absurd i.isLt (by simp) }
  apply splittingCompatible_of_exact_factorization (planeSplitting ε hε hεone)
    (planeSplitting ε hε hεone) le_rfl hε hεone
    (LinearIsometryEquiv.withLpProdUnique 2 ℝ (EuclideanSpace ℝ (Fin 2))
      (EuclideanSpace ℝ (Fin (2 - 2)))).symm
    ((IsometryEquiv.withLpUniqueProd 2 (EuclideanSpace ℝ (Fin (2 - 2))) Unit))
    rfl
  intro x _
  rfl

/-- AC79/AC80 + FC21 for the identity plane splitting at a small error: around every centre `c`
within distance one, the original coordinates are aligned by one coisometry on `B(c, 100)`. -/
theorem planeSplitting_recentered_alignment {ε : ℝ} (hε : 0 < ε)
    (hεtol : ε ≤ recenterTolerance (1 / 100) (1 + 1))
    (c : WithLp 2 (EuclideanSpace ℝ (Fin 2) × Unit))
    (hc : dist (WithLp.toLp 2 ((0 : EuclideanSpace ℝ (Fin 2)), ())) c ≤ 1) :
    ∃ Λ : EuclideanSpace ℝ (Fin 2) →L[ℝ] EuclideanSpace ℝ (Fin 2), ∃ b,
      Λ.comp (ContinuousLinearMap.adjoint Λ) = ContinuousLinearMap.id ℝ _ ∧
      ∀ x ∈ ball c (1 / 100)⁻¹, ‖x.fst - c.fst‖ ≤ 1 →
        ‖x.fst - Λ x.fst - b‖ ≤ (1 + 24 * ((2 : ℕ) : ℝ)) * (1 / 100) := by
  have hεone : ε < 1 := by
    have h := hεtol.trans (min_le_left _ _)
    linarith
  exact exists_recentered_coisometry_alignment (planeSplitting ε hε hεone)
    (planeSplitting ε hε hεone) (planeSplitting_compatible ε hε hεone) c (by norm_num)
    (by norm_num) zero_le_one hεtol hc one_pos (by norm_num) (by norm_num)

universe u uE uH

variable {E : Type uE} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type uH} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace

/-- FC07's two-stratum comparison (KL 12.12) on actual manifolds: two rank-two charts, the first
centred anywhere within `C` of `p`, are compared by one coisometry of `ℝ²` with error `49/100` on
`{x ∈ B(p, 100) | ‖ψ₁ x‖ ≤ 40}`, once the curvature, exclusion and error budgets hold. -/
theorem exists_two_stratum_overlap_coisometry_parameter_riemannian
    (hn : 2 ≤ Module.finrank ℝ E) {ν : ℝ} (hν : 0 < ν) (hνone : ν < 1) :
    ∃ σ : ℝ, 0 < σ ∧ σ < 1 ∧
      ∀ (M : Type u) [MetricSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
        [SigmaCompactSpace M] [CompleteSpace M] (g : SmoothRiemannianMetric I M),
      (∀ a b, riemannianEDistOf g a b = ENNReal.ofReal (dist a b)) → ∀ p : M,
      (∀ y ∈ ball p σ⁻¹, SectionalBoundedBelowAt g y (-σ)) →
      (¬ ∃ (W : Type u) (m : MetricSpace W), letI := m
        ∃ w : W, Nonempty (KleinerLottApprox p
          (WithLp.toLp 2 ((0 : EuclideanSpace ℝ (Fin (2 + 1))), w)) ν)) →
      ∀ (A B : Type u) [MetricSpace A] [MetricSpace B] (a₀ : A) (b₀ : B) (p' : M)
        {C ε₁ ε₂ : ℝ}, 0 ≤ C → dist p' p ≤ C →
      ∀ (φ : KleinerLottApprox p' (WithLp.toLp 2 ((0 : EuclideanSpace ℝ (Fin 2)), a₀)) ε₁)
        (ψ : KleinerLottApprox p (WithLp.toLp 2 ((0 : EuclideanSpace ℝ (Fin 2)), b₀)) ε₂),
        ε₁ ≤ recenterTolerance σ C → 3 * ε₂ ≤ σ →
        ∃ Λ : EuclideanSpace ℝ (Fin 2) →L[ℝ] EuclideanSpace ℝ (Fin 2), ∃ c,
          Λ.comp (ContinuousLinearMap.adjoint Λ) = ContinuousLinearMap.id ℝ _ ∧
          ∀ x ∈ ball p (1 / 100)⁻¹, ‖(ψ.toFun x).fst‖ ≤ 40 →
            ‖(φ.toFun x).fst - Λ (ψ.toFun x).fst - c‖ ≤ (1 + 24 * ((2 : ℕ) : ℝ)) * (1 / 100) :=
  exists_overlap_coisometry_parameter_riemannian.{u} (I := I) one_le_two le_rfl hn
    (by norm_num) (by norm_num) hν hνone (by norm_num) (by norm_num) (by norm_num)

end GC.MetricGeometry
