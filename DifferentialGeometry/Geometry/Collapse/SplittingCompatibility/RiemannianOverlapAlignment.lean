import DifferentialGeometry.Geometry.Collapse.SplittingCompatibility.CoisometryAlignment
import DifferentialGeometry.Geometry.Collapse.SplittingCompatibility.RiemannianUniformCompatibility

/-!
# Two charts with different centres, aligned by one coisometry (AC79 → AC76 → FC21)

Blueprint `master207B.tex`: KL 12.12 compares nearby normalized coordinates by an affine isometry
followed by an orthogonal projection (B:242–247, used by FC07 B:395–398); FC19's binding paragraph
(B:1363–1367) and FC21 (B:1445–1446): "AC79 supplies the original recentering, AC76 supplies
approximate compatibility", then ONE coisometry as in KL 4.31.

`exists_overlap_coisometry_parameter_riemannian`: given `j ≤ k ≤ n`, `τ, ν`, and a radius `a` with
`20 j τ ≤ a`, `2a ≤ τ⁻¹`, there is `σ` such that on a complete Riemannian `n`-manifold with
sectional curvature `≥ −σ` on `B(p, σ⁻¹)` and no `(k+1, ν)`-splitting at `p`: for a rank-`j`
splitting `φ` centred at ANY `p'` with `d(p',p) ≤ C` and error `ε₁ ≤ ϑ(σ, C)` (AC78's tolerance)
and a rank-`k` splitting `ψ` centred at `p` with error `3ε₂ ≤ σ`, one constant coisometry
`Λ : ℝᵏ → ℝʲ` and one translation `c` give `‖φ₁ − Λ ψ₁ − c‖ ≤ (1 + 24 j) τ` on
`{x ∈ B(p, τ⁻¹) | ‖ψ₁ x‖ ≤ a}`. The ORIGINAL coordinates `φ₁, ψ₁` appear in the conclusion; AC79's
recentring only shifts `φ₁` by the constant `φ₁(p)`, absorbed into `c`.
-/

set_option autoImplicit false

open Set Metric Bundle Manifold
open DifferentialGeometry
open DifferentialGeometry.Geometry.Metric
open scoped Manifold ContDiff ENNReal
open DifferentialGeometry.Geometry.Riemannian
open DifferentialGeometry.Geometry.Comparison.Toponogov

namespace GC.MetricGeometry

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace

universe u uE uH

variable {E : Type uE} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type uH} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]

/-- **AC79 → AC76 → FC21 on actual manifolds**: two original charts with different centres are
compared by one constant coisometry and one translation (KL 12.12's comparison form). -/
theorem exists_overlap_coisometry_parameter_riemannian {j k : ℕ}
    (hj : 1 ≤ j) (hjk : j ≤ k) (hkn : k ≤ Module.finrank ℝ E)
    {τ ν a : ℝ} (hτ : 0 < τ) (hτone : τ < 1) (hν : 0 < ν) (hνone : ν < 1)
    (ha0 : 0 < a) (ha : 20 * (j : ℝ) * τ ≤ a) (ha2 : 2 * a ≤ τ⁻¹) :
    ∃ σ : ℝ, 0 < σ ∧ σ < 1 ∧
      ∀ (M : Type u) [MetricSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
        [SigmaCompactSpace M] [CompleteSpace M] (g : SmoothRiemannianMetric I M),
      (∀ a b, riemannianEDistOf g a b = ENNReal.ofReal (dist a b)) → ∀ p : M,
      (∀ y ∈ ball p σ⁻¹, SectionalBoundedBelowAt g y (-σ)) →
      (¬ ∃ (W : Type u) (m : MetricSpace W), letI := m
        ∃ w : W, Nonempty (KleinerLottApprox p
          (WithLp.toLp 2 ((0 : EuclideanSpace ℝ (Fin (k + 1))), w)) ν)) →
      ∀ (A B : Type u) [MetricSpace A] [MetricSpace B] (a₀ : A) (b₀ : B) (p' : M)
        {C ε₁ ε₂ : ℝ}, 0 ≤ C → dist p' p ≤ C →
      ∀ (φ : KleinerLottApprox p' (WithLp.toLp 2 ((0 : EuclideanSpace ℝ (Fin j)), a₀)) ε₁)
        (ψ : KleinerLottApprox p (WithLp.toLp 2 ((0 : EuclideanSpace ℝ (Fin k)), b₀)) ε₂),
        ε₁ ≤ recenterTolerance σ C → 3 * ε₂ ≤ σ →
        ∃ Λ : EuclideanSpace ℝ (Fin k) →L[ℝ] EuclideanSpace ℝ (Fin j), ∃ c,
          Λ.comp (ContinuousLinearMap.adjoint Λ) = ContinuousLinearMap.id ℝ _ ∧
          ∀ x ∈ ball p τ⁻¹, ‖(ψ.toFun x).fst‖ ≤ a →
            ‖(φ.toFun x).fst - Λ (ψ.toFun x).fst - c‖ ≤ (1 + 24 * j) * τ := by
  obtain ⟨σ, hσ, hσone, hprop⟩ :=
    exists_splitting_compatibility_parameter_riemannian.{u} (I := I) hj hjk hkn hτ hτone hν hνone
  refine ⟨σ, hσ, hσone, ?_⟩
  intro M _ _ _ _ _ g hmetric p hsec hno A B _ _ a₀ b₀ p' C ε₁ ε₂ hC hp φ ψ hε₁ hε₂
  let φ' := φ.recenterEuclidean p hσ hσone hC hε₁ hp
  let ψ' := ψ.weaken hε₂ hσone
  obtain ⟨Λ, c, hΛ, hal⟩ := exists_coisometry_alignment_of_splittingCompatible φ' ψ'
    (hprop M g hmetric p hsec hno A B (φ.toFun p).snd b₀ φ' ψ') ha0 ha ha2
  refine ⟨Λ, c + (φ.toFun p).fst, hΛ, fun x hx hxa => ?_⟩
  have h := hal x hx hxa
  simp only [φ', ψ', KleinerLottApprox.recenterEuclidean_apply, KleinerLottApprox.weaken_toFun,
    WithLp.toLp_fst] at h
  convert h using 2
  abel

end GC.MetricGeometry
