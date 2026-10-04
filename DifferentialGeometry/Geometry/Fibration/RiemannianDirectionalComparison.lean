import DifferentialGeometry.Geometry.Fibration.RiemannianSegmentComparison
import DifferentialGeometry.Analysis.InnerProductSpace.BlockNormBounds
import DifferentialGeometry.Analysis.InnerProductSpace.DirectionalSaturation

set_option autoImplicit false
noncomputable section
open Bundle Manifold Set Metric
open DifferentialGeometry.Geometry.Riemannian
open scoped Manifold ContDiff InnerProductSpace
namespace DifferentialGeometry.Geometry.Fibration

/-- Coisometries are contractions, including the zero-dimensional target. -/
theorem norm_coisometry_le_one {V W : Type*}
    [NormedAddCommGroup V] [InnerProductSpace ℝ V] [CompleteSpace V]
    [NormedAddCommGroup W] [InnerProductSpace ℝ W] [CompleteSpace W]
    (A : V →L[ℝ] W) (hA : A.comp A.adjoint = ContinuousLinearMap.id ℝ W) : ‖A‖ ≤ 1 := by
  have hs := ContinuousLinearMap.norm_adjoint_comp_self A.adjoint
  rw [ContinuousLinearMap.adjoint_adjoint, hA, LinearIsometryEquiv.norm_map] at hs
  have hb : ‖A‖ * ‖A‖ ≤ 1 := by rw [← hs]; exact ContinuousLinearMap.norm_id_le
  nlinarith [norm_nonneg A]

/-- FC15's pointwise estimate on a genuine Hilbert tangent space. -/
theorem norm_difference_of_common_directions {V : Type*}
    [NormedAddCommGroup V] [InnerProductSpace ℝ V] [CompleteSpace V] {k m : ℕ}
    (f : V →L[ℝ] EuclideanSpace ℝ (Fin k))
    (g : V →L[ℝ] EuclideanSpace ℝ (Fin m))
    (A : EuclideanSpace ℝ (Fin m) →L[ℝ] EuclideanSpace ℝ (Fin k))
    (hA : A.comp A.adjoint = ContinuousLinearMap.id ℝ _) {ε : ℝ} (hε : 0 ≤ ε)
    (hf : ∀ a : Fin k, ‖(EuclideanSpace.proj a : StrongDual ℝ _).comp f‖ ≤ 1 + ε)
    (hg : ‖g‖ ≤ 1 + ε)
    (ht : ∀ a : Fin k, ∃ w : V, ‖w‖ = 1 ∧ 1 - ε ≤ f w a ∧ 1 - ε ≤ A (g w) a) :
    ‖f - A.comp g‖ ≤ 2 * Real.sqrt (k * (4 * ε + ε ^ 2)) := by
  have hAn := norm_coisometry_le_one A hA
  have hrow (a : Fin k) :
      ‖(EuclideanSpace.proj a : StrongDual ℝ _).comp (f - A.comp g)‖ ≤
        2 * Real.sqrt (4 * ε + ε ^ 2) := by
    obtain ⟨w, hw, hwf, hwg⟩ := ht a
    have hp : ‖(EuclideanSpace.proj a : StrongDual ℝ (EuclideanSpace ℝ (Fin k)))‖ ≤ 1 := by
      apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
      intro y
      change ‖y a‖ ≤ 1 * ‖y‖
      simpa only [one_mul] using PiLp.norm_apply_le y a
    have hAg : ‖(EuclideanSpace.proj a : StrongDual ℝ _).comp (A.comp g)‖ ≤ 1 + ε := by
      apply (ContinuousLinearMap.opNorm_comp_le _ _).trans
      calc
        _ ≤ 1 * (1 * (1 + ε)) := by
          apply mul_le_mul hp
            ((ContinuousLinearMap.opNorm_comp_le A g).trans (by gcongr))
            (norm_nonneg _) zero_le_one
        _ = 1 + ε := by ring
    have hs := ContinuousLinearMap.norm_sub_le_of_common_unit_saturation
      ((EuclideanSpace.proj a : StrongDual ℝ _).comp f)
      ((EuclideanSpace.proj a : StrongDual ℝ _).comp (A.comp g))
      hε (hf a) hAg w hw hwf hwg
    have he : (EuclideanSpace.proj a : StrongDual ℝ _).comp (f - A.comp g) =
        (EuclideanSpace.proj a : StrongDual ℝ _).comp f -
          (EuclideanSpace.proj a : StrongDual ℝ _).comp (A.comp g) := by
      ext v
      rfl
    rwa [he]
  have hh := (f - A.comp g).norm_le_sqrt_active_blocks Finset.univ
    (B := 2 * Real.sqrt (4 * ε + ε ^ 2)) (by positivity)
    (fun v a _ha => (((EuclideanSpace.proj a : StrongDual ℝ _).comp
      (f - A.comp g)).le_opNorm v).trans
        (mul_le_mul_of_nonneg_right (hrow a) (norm_nonneg v)))
    (fun _v a ha => False.elim (ha (Finset.mem_univ a)))
  simpa only [Finset.card_univ, Fintype.card_fin, Real.sqrt_mul (Nat.cast_nonneg k),
    mul_left_comm] using hh

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace
variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  [MetricSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [T2Space (TangentBundle I M)] [SigmaCompactSpace M] [ConnectedSpace M]
  [CompleteSpace M] [RiemannianBundle (fun x : M => TangentSpace I x)]
  [IsRiemannianManifold I M]
  [IsContinuousRiemannianBundle E (fun x : M => TangentSpace I x)]

/-- FC15 on an actual complete Riemannian ball, with native tangent vectors. -/
theorem centered_affine_c1_of_common_directions {k m : ℕ}
    (g : SmoothRiemannianMetric I M) (hmetric : IsMetricNorm g)
    (F : M → EuclideanSpace ℝ (Fin k)) (G : M → EuclideanSpace ℝ (Fin m))
    (A : EuclideanSpace ℝ (Fin m) →L[ℝ] EuclideanSpace ℝ (Fin k))
    (hA : A.comp A.adjoint = ContinuousLinearMap.id ℝ _)
    (p : M) {L ε : ℝ} (hL : 0 < L) (hε : 0 ≤ ε)
    (hF : ContMDiffOn I 𝓘(ℝ, EuclideanSpace ℝ (Fin k)) 1 F (ball p L))
    (hG : ContMDiffOn I 𝓘(ℝ, EuclideanSpace ℝ (Fin m)) 1 G (ball p L))
    (hrows : ∀ x ∈ ball p L, ∀ a : Fin k,
      ‖(EuclideanSpace.proj a : StrongDual ℝ _).comp (mvfderiv I F x)‖ ≤ 1 + ε)
    (hDG : ∀ x ∈ ball p L, ‖mvfderiv I G x‖ ≤ 1 + ε)
    (htests : ∀ x ∈ ball p L, ∀ a : Fin k, ∃ w : TangentSpace I x,
      ‖w‖ = 1 ∧ 1 - ε ≤ mvfderiv I F x w a ∧
        1 - ε ≤ A (mvfderiv I G x w) a) :
    let b := F p - A (G p)
    ∀ x ∈ ball p L,
      max ‖F x - (A (G x) + b)‖ ‖mvfderiv I F x - A.comp (mvfderiv I G x)‖ ≤
        2 * max 1 L * Real.sqrt (k * (4 * ε + ε ^ 2)) := by
  have hc : 0 ≤ 2 * Real.sqrt (k * (4 * ε + ε ^ 2)) := by positivity
  have hh := centered_affine_c1_of_mfderiv_bound g hmetric F G A p hL hc hF hG
    (fun x hx => norm_difference_of_common_directions
      (mvfderiv I F x) (mvfderiv I G x) A hA hε (hrows x hx) (hDG x hx) (htests x hx))
  dsimp only at hh ⊢
  intro x hx
  convert (hh x hx).2 using 1
  ring

/-- The blueprint's explicit strict FC15 error budget. -/
theorem directional_comparison_bound_lt_of_budget {k : ℕ} {L ε τ : ℝ}
    (hk : 0 < k) (hε : 0 ≤ ε) (hτ : 0 < τ)
    (hbudget : ε < min 1 (τ ^ 2 / (20 * k * max 1 L ^ 2))) :
    2 * max 1 L * Real.sqrt (k * (4 * ε + ε ^ 2)) < τ := by
  have hε1 : ε < 1 := (lt_min_iff.mp hbudget).1
  have hk' : (0 : ℝ) < k := by exact_mod_cast hk
  have hm : 0 < max 1 L := zero_lt_one.trans_le (le_max_left 1 L)
  have hb : ε * (20 * k * max 1 L ^ 2) < τ ^ 2 :=
    (lt_div_iff₀ (by positivity)).mp (lt_min_iff.mp hbudget).2
  have he : 4 * ε + ε ^ 2 ≤ 5 * ε := by nlinarith
  have hs : (2 * max 1 L * Real.sqrt (k * (4 * ε + ε ^ 2))) ^ 2 < τ ^ 2 := by
    rw [mul_pow, mul_pow, Real.sq_sqrt (by positivity)]
    calc
      _ ≤ 4 * max 1 L ^ 2 * (k * (5 * ε)) := by
        gcongr
        norm_num
      _ = ε * (20 * k * max 1 L ^ 2) := by ring
      _ < τ ^ 2 := hb
  nlinarith [mul_nonneg (by positivity : 0 ≤ 2 * max 1 L)
    (Real.sqrt_nonneg (k * (4 * ε + ε ^ 2)))]

/-- FC15 on an actual complete Riemannian ball, with native tangent vectors. -/
theorem centered_affine_c1_lt_of_common_directions {k m : ℕ}
    (g : SmoothRiemannianMetric I M) (hmetric : IsMetricNorm g)
    (F : M → EuclideanSpace ℝ (Fin k)) (G : M → EuclideanSpace ℝ (Fin m))
    (A : EuclideanSpace ℝ (Fin m) →L[ℝ] EuclideanSpace ℝ (Fin k))
    (hA : A.comp A.adjoint = ContinuousLinearMap.id ℝ _)
    (p : M) {L ε τ : ℝ} (hL : 0 < L) (hε : 0 ≤ ε)
    (hk : 0 < k) (hτ : 0 < τ)
    (hbudget : ε < min 1 (τ ^ 2 / (20 * k * max 1 L ^ 2)))
    (hF : ContMDiffOn I 𝓘(ℝ, EuclideanSpace ℝ (Fin k)) 1 F (ball p L))
    (hG : ContMDiffOn I 𝓘(ℝ, EuclideanSpace ℝ (Fin m)) 1 G (ball p L))
    (hrows : ∀ x ∈ ball p L, ∀ a : Fin k,
      ‖(EuclideanSpace.proj a : StrongDual ℝ _).comp (mvfderiv I F x)‖ ≤ 1 + ε)
    (hDG : ∀ x ∈ ball p L, ‖mvfderiv I G x‖ ≤ 1 + ε)
    (htests : ∀ x ∈ ball p L, ∀ a : Fin k, ∃ w : TangentSpace I x,
      ‖w‖ = 1 ∧ 1 - ε ≤ mvfderiv I F x w a ∧
        1 - ε ≤ A (mvfderiv I G x w) a) :
    let b := F p - A (G p)
    ∀ x ∈ ball p L,
      max ‖F x - (A (G x) + b)‖ ‖mvfderiv I F x - A.comp (mvfderiv I G x)‖ < τ := by
  have hh := centered_affine_c1_of_common_directions g hmetric F G A hA p hL hε
    hF hG hrows hDG htests
  exact fun x hx => (hh x hx).trans_lt (directional_comparison_bound_lt_of_budget hk hε hτ hbudget)

end DifferentialGeometry.Geometry.Fibration
