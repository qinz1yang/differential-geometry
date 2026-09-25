import DifferentialGeometry.Geometry.Flow.RicciFlow.Estimates.Shi.ConstantMonotonicity
import DifferentialGeometry.Geometry.Flow.RicciFlow.Estimates.Shi.BernsteinMaximum
import DifferentialGeometry.Geometry.Flow.RicciFlow.Estimates.Shi.HigherDerivativeReaction
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.StandardSolution.EndpointRiemannNorm

set_option autoImplicit false
noncomputable section
open DifferentialGeometry.Geometry.Curvature DifferentialGeometry.Geometry.Connection
open DifferentialGeometry.Geometry.Operator DifferentialGeometry.Tensor0SBundle
open DifferentialGeometry.Analysis.Parabolic
open Set Bundle
open scoped Manifold ContDiff Topology
namespace DifferentialGeometry.PDE.RicciFlow
variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)] [CompleteSpace E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [T2Space M]

omit [NeZero (Module.finrank ℝ E)] [I.Boundaryless] in
private theorem shifted_curvature_norm {D : RealTimeInterval}
    (S : SolutionOn (I := I) (M := M) D) (a t : ℝ) (k : ℕ) (x : M) :
    nablaKRm04NormSqIntrinsic (S.timeShift a) k t x =
      nablaKRm04NormSqIntrinsic S k (t + a) x := by
  unfold nablaKRm04NormSqIntrinsic
  rw [nablaKRm_eq_iterCov, nablaKRm_eq_iterCov]
  rfl

omit [NeZero (Module.finrank ℝ E)] [I.Boundaryless] [T2Space M] in
private theorem shifted_parabolic_operator {D : RealTimeInterval}
    (S : SolutionOn (I := I) (M := M) D) (F : ℝ → M → ℝ)
    {T η t : ℝ} (hT : 0 < T) (hη : 0 ≤ η) (ht : t ∈ Ioc 0 T)
    (hF : ∀ x : M, DifferentiableAt ℝ (fun s => F s x) (t + η)) (x : M) :
    parabolicOperatorWithDrift (flowG S) T (fun _ _ => 0)
        (fun s y => F (s + η) y) t x =
      parabolicOperatorWithDrift (flowG (S.timeShift (-η))) (T + η)
        (fun _ _ => 0) F (t + η) x := by
  have hTf : 0 < T + η := add_pos_of_pos_of_nonneg hT hη
  have htc : t ∈ Icc 0 T := ⟨ht.1.le, ht.2⟩
  have htη : t + η ∈ Icc 0 (T + η) := ⟨by linarith [ht.1], by linarith [ht.2]⟩
  have hd := (hF x).hasDerivAt.comp t ((hasDerivAt_id t).add_const η)
  have hd' : HasDerivAt (fun s => F (s + η) x) (deriv (fun s => F s x) (t + η)) t := by
    simpa only [mul_one, id_eq, Function.comp_def] using hd
  rw [parabolicOperatorWithDrift_eq, parabolicOperatorWithDrift_eq,
    hd'.hasDerivWithinAt.derivWithin ((uniqueDiffOn_Icc hT) t htc),
    (hF x).hasDerivAt.hasDerivWithinAt.derivWithin ((uniqueDiffOn_Icc hTf) (t + η) htη)]
  congr 1
  simp only [heatOperatorWithDrift, laplacianAt, driftTerm, flowG,
    SolutionOn.timeShift, SolutionFamily.timeShift, SolutionFamily.connection,
    add_neg_cancel_right, map_zero, zero_apply, add_zero]

private theorem shifted_bernstein_reaction
    {D : RealTimeInterval} (S : SolutionOn (I := I) (M := M) D) (hS : IsSolutionOn S)
    {T η Astar : ℝ} (hT : 0 < T) (hη : 0 ≤ η) (hAstar : 1 ≤ Astar)
    (m : ℕ) {t : ℝ} (ht : t ∈ Ioc 0 T) (hreg : t ∈ D.regular) (x : M)
    (hu0 : nablaKRm04NormSqIntrinsic S 0 t x ≤ 1)
    (hIH : ∀ j : ℕ, 1 ≤ j → j ≤ m →
      (t + η) ^ j * nablaKRm04NormSqIntrinsic S j t x ≤ Astar ^ 2) :
    let F := fun s y =>
      shiHigherBernsteinQuantity (S.timeShift (-η)) m (shiHigherShift Astar) (s + η) y
    parabolicOperatorWithDrift (flowG S) T (fun _ _ => 0) F t x ≤
      -(shiHigherBernsteinCoeff Astar / (t + η)) * F t x ^ 2 +
        shiHigherBernsteinConst (Module.finrank ℝ E) m (T + η) Astar / (t + η) := by
  have hreg' : t + η ∈ (D.timeShift (-η)).regular := by
    change t + η + -η ∈ D.regular
    simpa only [add_neg_cancel_right] using hreg
  let F := shiHigherBernsteinQuantity (S.timeShift (-η)) m (shiHigherShift Astar)
  have hd : ∀ y : M, DifferentiableAt ℝ (fun s => F s y) (t + η) :=
    fun y => differentiableAt_shiHigherBernsteinQuantity (S.timeShift (-η))
      (isSolutionOn_timeShift hS (-η)) m (shiHigherShift Astar) hreg' y
  dsimp only
  rw [shifted_parabolic_operator S F hT hη ht hd x]
  apply parabolicOperatorWithDrift_shiHigherBernsteinQuantity_sq_le
    (S.timeShift (-η)) (isSolutionOn_timeShift hS (-η))
    (add_pos_of_pos_of_nonneg hT hη) hAstar m
    (show t + η ∈ Icc 0 (T + η) from ⟨by linarith [ht.1], by linarith [ht.2]⟩)
    (by linarith [ht.1]) hreg' x
  · simpa only [shifted_curvature_norm, add_neg_cancel_right] using hu0
  · intro j hj hjm
    simpa only [shifted_curvature_norm, add_neg_cancel_right] using hIH j hj hjm

private theorem shifted_tpow_curvature_derivative_bound_of_fixedCutoff
    {D : RealTimeInterval} (S : SolutionOn (I := I) (M := M) D) (hS : IsSolutionOn S)
    {T η Astar eps A : ℝ} (hT : 0 < T) (hη : 0 < η) (hAstar : 1 ≤ Astar)
    (m : ℕ) (cut : ShiFixedCutoff (flowG S) T eps)
    (hreg : Ioc 0 T ⊆ D.regular)
    (hgram : ∀ (x₀ : M) (i j : Fin (Module.finrank ℝ E)),
      ContMDiffOn (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) ∞
        (fun p : ℝ × M => DifferentialGeometry.Tensor.Coordinates.chartGramMatrix
          (S.base.metric p.1) x₀ p.2 i j)
        (Icc 0 T ×ˢ (trivializationAt E (TangentSpace I) x₀).baseSet))
    {Ω Ω' : Set M} (hsupp : cut.support ⊆ Ω)
    (hone : ∀ t ∈ Icc 0 T, ∀ x ∈ Ω', cut.chi t x = 1)
    (hu0 : ∀ t ∈ Icc 0 T, ∀ x ∈ Ω, nablaKRm04NormSqIntrinsic S 0 t x ≤ 1)
    (hIH : ∀ j : ℕ, 1 ≤ j → j ≤ m → ∀ t ∈ Icc 0 T, ∀ x ∈ Ω,
      (t + η) ^ j * nablaKRm04NormSqIntrinsic S j t x ≤ Astar ^ 2)
    (hinit : ∀ x ∈ Ω, η ^ (m + 1) * nablaKRm04NormSqIntrinsic S (m + 1) 0 x ≤ A)
    (hA : 0 ≤ A) :
    ∀ t ∈ Icc 0 T, ∀ x ∈ Ω',
      (t + η) ^ (m + 1) * nablaKRm04NormSqIntrinsic S (m + 1) t x ≤
      max ((shiHigherShift Astar + Astar ^ 2) * A)
        (bernsteinMaximumBound (shiHigherBernsteinCoeff Astar)
          (shiHigherBernsteinConst (Module.finrank ℝ E) m (T + η) Astar) eps (T + η)) /
        shiHigherShift Astar := by
  let a := shiHigherShift Astar
  let F := fun t y => shiHigherBernsteinQuantity (S.timeShift (-η)) m a (t + η) y
  have hF (t : ℝ) (x : M) : F t x =
      (a + (t + η) ^ m * nablaKRm04NormSqIntrinsic S m t x) *
        ((t + η) ^ (m + 1) * nablaKRm04NormSqIntrinsic S (m + 1) t x) := by
    simp only [F, shiHigherBernsteinQuantity, shiWeightedNormSq,
      shifted_curvature_norm, add_neg_cancel_right]
  have hnonneg : ∀ t ∈ Icc 0 T, ∀ x : M, 0 ≤ F t x := by
    intro t ht x
    exact shiHigherBernsteinQuantity_nonneg (S.timeShift (-η)) m
      (shiHigherShift_pos Astar).le (by linarith [ht.1]) x
  have hmem : ∀ t ∈ Icc 0 T, ∀ x : M, 0 < cut.chi t x → x ∈ Ω := by
    intro t ht x hx
    by_contra h
    have hz := cut.support_zero t ht x (fun hx' => h (hsupp hx'))
    rw [hz] at hx
    exact lt_irrefl 0 hx
  have hinitF : ∀ x : M, cut.chi 0 x * F 0 x ≤ (a + Astar ^ 2) * A := by
    intro x
    have hchi := cut.range 0 ⟨le_rfl, hT.le⟩ x
    by_cases hx : 0 < cut.chi 0 x
    · have hxΩ := hmem 0 ⟨le_rfl, hT.le⟩ x hx
      have hX : η ^ m * nablaKRm04NormSqIntrinsic S m 0 x ≤ Astar ^ 2 := by
        by_cases hm : m = 0
        · subst m
          simp only [pow_zero, one_mul]
          nlinarith [hu0 0 ⟨le_rfl, hT.le⟩ x hxΩ]
        · exact (by simpa only [zero_add] using hIH m (by omega) le_rfl 0 ⟨le_rfl, hT.le⟩ x hxΩ)
      have hY := hinit x hxΩ
      have hX0 := nablaKRm04NormSqIntrinsic_nonneg S m 0 x
      have hY0 := mul_nonneg (pow_pos hη (m+1)).le (nablaKRm04NormSqIntrinsic_nonneg S (m+1) 0 x)
      have hbound : F 0 x ≤ (a + Astar ^ 2) * A := by
        rw [hF, zero_add]
        exact mul_le_mul (by linarith : a + _ ≤ a + Astar ^ 2) hY hY0
          (add_nonneg (shiHigherShift_pos Astar).le (sq_nonneg Astar))
      exact (mul_le_of_le_one_left (hnonneg 0 ⟨le_rfl, hT.le⟩ x) hchi.2).trans hbound
    · have hz : cut.chi 0 x = 0 := le_antisymm (le_of_not_gt hx) hchi.1
      rw [hz, zero_mul]
      exact mul_nonneg (add_nonneg (shiHigherShift_pos Astar).le (sq_nonneg Astar)) hA
  have hcont : ContinuousOn (fun p : ℝ × M => F p.1 p.2) (spacetimeSlab (M := M) T) := by
    have hn (j : ℕ) : ContinuousOn (fun p : ℝ × M => nablaKRm04NormSqIntrinsic S j p.1 p.2)
        (Icc 0 T ×ˢ univ) := by
      have hh := (covariantRiemannNormSq_contMDiffOn S.base.metric (Icc 0 T)
        (uniqueDiffOn_Icc hT) hgram j).continuousOn
      apply hh.congr
      intro p _
      dsimp only
      unfold nablaKRm04NormSqIntrinsic
      rw [nablaKRm_eq_iterCov]
      rfl
    have hw : ContinuousOn (fun p : ℝ × M => p.1 + η) (Icc 0 T ×ˢ univ) :=
      continuous_fst.continuousOn.add continuousOn_const
    have hh := ((continuousOn_const (c := a)).add ((hw.pow m).mul (hn m))).mul
      ((hw.pow (m+1)).mul (hn (m+1)))
    exact hh.congr (fun p _ => hF p.1 p.2)
  have hd : ∀ t ∈ Icc 0 T, 0 < t → ∀ x : M,
      DifferentiableWithinAt ℝ (fun s => F s x) (Icc 0 T) t := by
    intro t ht hp x
    have hreg' : t + η ∈ (D.timeShift (-η)).regular := by
      change t + η + -η ∈ D.regular
      simpa only [add_neg_cancel_right] using hreg ⟨hp, ht.2⟩
    exact ((differentiableAt_shiHigherBernsteinQuantity (S.timeShift (-η))
      (isSolutionOn_timeShift hS (-η)) m a hreg' x).comp t
        (differentiableAt_id.add_const η)).differentiableWithinAt
  have hspace (t : ℝ) : ContMDiff I 𝓘(ℝ, ℝ) ∞ (F t) :=
    contMDiff_shiHigherBernsteinQuantity (S.timeShift (-η)) m a (t + η)
  have hbound := bernstein_maximum_of_fixed_cutoff_of_initial_bound cut F hT
    (shiHigherBernsteinCoeff_pos Astar)
    (shiHigherBernsteinConst_nonneg (add_pos_of_pos_of_nonneg hT hη.le).le
      (zero_le_one.trans hAstar) (Module.finrank ℝ E) m) hη.le
    hnonneg hinitF hcont hd
    (fun t _ _ x => (hspace t).contMDiffAt.mdifferentiableAt (by simp))
    (fun t _ _ x => gradientFun_mdiffAt ((flowG S).metric t) (hspace t) x)
    (fun t ht hp x hx => shifted_bernstein_reaction S hS hT hη.le hAstar m
      ⟨hp, ht.2⟩ (hreg ⟨hp, ht.2⟩) x (hu0 t ht x (hmem t ht x hx))
      (fun j hj hjm => hIH j hj hjm t ht x (hmem t ht x hx)))
  intro t ht x hx
  have hb := hbound t ht x
  rw [hone t ht x hx, one_mul, hF] at hb
  have hx0 := nablaKRm04NormSqIntrinsic_nonneg S m t x
  have hx1 := nablaKRm04NormSqIntrinsic_nonneg S (m+1) t x
  have htη : 0 ≤ t + η := add_nonneg ht.1 hη.le
  apply (le_div_iff₀ (shiHigherShift_pos Astar)).mpr
  have hsecond : a * ((t+η) ^ (m+1) * nablaKRm04NormSqIntrinsic S (m+1) t x) ≤
      (a + (t+η)^m * nablaKRm04NormSqIntrinsic S m t x) *
        ((t+η) ^ (m+1) * nablaKRm04NormSqIntrinsic S (m+1) t x) := by
    exact mul_le_mul_of_nonneg_right
      (le_add_of_nonneg_right (mul_nonneg (pow_nonneg htη m) hx0))
      (mul_nonneg (pow_nonneg htη (m+1)) hx1)
  nlinarith [hsecond.trans hb]

universe u

omit [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [T2Space M] in
theorem exists_uniform_curvature_derivative_bound_of_bounded_horizon_fixedCutoffs
    (N : ℕ) (T : ℝ) (eps : Fin N → ℝ) (A : ℕ → ℝ)
    (hA : ∀ j, 1 ≤ j → j ≤ N → 0 ≤ A j) :
    ∃ B : ℝ, 1 ≤ B ∧ ∀ (X : Type u) [TopologicalSpace X] [ChartedSpace H X]
      [IsManifold I ∞ X] [T2Space X], ∀ (D : RealTimeInterval)
      (S : SolutionOn (I := I) (M := X) D), ∀ θ : ℝ, 0 < θ → θ ≤ T → IsSolutionOn S →
      Ioc 0 θ ⊆ D.regular →
      (∀ (x₀ : X) (i j : Fin (Module.finrank ℝ E)),
        ContMDiffOn (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) ∞
          (fun p : ℝ × X => DifferentialGeometry.Tensor.Coordinates.chartGramMatrix
            (S.base.metric p.1) x₀ p.2 i j)
          (Icc 0 θ ×ˢ (trivializationAt E (TangentSpace I) x₀).baseSet)) →
      ∀ (Ω : ℕ → Set X) (fc : ∀ k : Fin N, ShiFixedCutoff (flowG S) θ (eps k)),
      (∀ k, k < N → Ω (k + 1) ⊆ Ω k) →
      (∀ k : Fin N, (fc k).support ⊆ Ω k.val) →
      (∀ k : Fin N, ∀ t ∈ Icc 0 θ, ∀ x ∈ Ω (k.val + 1), (fc k).chi t x = 1) →
      (∀ t ∈ Icc 0 θ, ∀ x ∈ Ω 0, nablaKRm04NormSqIntrinsic S 0 t x ≤ 1) →
      (∀ k, 1 ≤ k → k ≤ N → ∀ x ∈ Ω 0, nablaKRm04NormSqIntrinsic S k 0 x ≤ A k) →
      ∀ k ≤ N, ∀ t ∈ Icc 0 θ, ∀ x ∈ Ω N,
        nablaKRm04NormSqIntrinsic S k t x ≤ B := by
  classical
  let Good := fun (X : Type u) [TopologicalSpace X] [ChartedSpace H X]
      [IsManifold I ∞ X] [T2Space X] (D : RealTimeInterval)
      (S : SolutionOn (I := I) (M := X) D) (θ : ℝ)
      (Ω : ℕ → Set X) (fc : ∀ k : Fin N, ShiFixedCutoff (flowG S) θ (eps k)) =>
    IsSolutionOn S ∧ Ioc 0 θ ⊆ D.regular ∧
      (∀ (x₀ : X) (i j : Fin (Module.finrank ℝ E)),
        ContMDiffOn (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) ∞
          (fun p : ℝ × X => DifferentialGeometry.Tensor.Coordinates.chartGramMatrix
            (S.base.metric p.1) x₀ p.2 i j)
          (Icc 0 θ ×ˢ (trivializationAt E (TangentSpace I) x₀).baseSet)) ∧
      (∀ k, k < N → Ω (k + 1) ⊆ Ω k) ∧
      (∀ k : Fin N, (fc k).support ⊆ Ω k.val) ∧
      (∀ k : Fin N, ∀ t ∈ Icc 0 θ, ∀ x ∈ Ω (k.val + 1), (fc k).chi t x = 1) ∧
      (∀ t ∈ Icc 0 θ, ∀ x ∈ Ω 0, nablaKRm04NormSqIntrinsic S 0 t x ≤ 1) ∧
      (∀ k, 1 ≤ k → k ≤ N → ∀ x ∈ Ω 0, nablaKRm04NormSqIntrinsic S k 0 x ≤ A k)
  have hb : ∀ m : ℕ, m ≤ N → ∃ B : ℝ, 1 ≤ B ∧
      ∀ (X : Type u) [TopologicalSpace X] [ChartedSpace H X]
      [IsManifold I ∞ X] [T2Space X], ∀ (D : RealTimeInterval) (S : SolutionOn (I := I) (M := X) D)
        (θ : ℝ) (Ω : ℕ → Set X) (fc : ∀ k : Fin N, ShiFixedCutoff (flowG S) θ (eps k)),
      0 < θ → θ ≤ T → Good X D S θ Ω fc → ∀ k ≤ m, ∀ t ∈ Icc 0 θ, ∀ x ∈ Ω m,
        (t + 1) ^ k * nablaKRm04NormSqIntrinsic S k t x ≤ B ^ 2 := by
    intro m
    induction m with
    | zero =>
      intro _
      refine ⟨1, le_rfl, ?_⟩
      intro X _ _ _ _ D S θ Ω fc hθ hθT h k hk t ht x hx
      have he : k = 0 := by omega
      subst k
      simpa only [pow_zero, one_mul, one_pow] using h.2.2.2.2.2.2.1 t ht x hx
    | succ m ih =>
      intro hm
      obtain ⟨B, hB, hbound⟩ := ih (by omega)
      let step := max ((shiHigherShift B + B ^ 2) * A (m+1))
        (bernsteinMaximumBound (shiHigherBernsteinCoeff B)
          (shiHigherBernsteinConst (Module.finrank ℝ E) m (T+1) B) (eps ⟨m, by omega⟩) (T+1)) /
          shiHigherShift B
      have hstep0 : 0 ≤ step := div_nonneg
        ((zero_le_one.trans (one_le_bernsteinMaximumBound _ _ _ _)).trans (le_max_right _ _))
        (shiHigherShift_pos B).le
      refine ⟨max B (Real.sqrt step), hB.trans (le_max_left _ _), ?_⟩
      intro X _ _ _ _ D S θ Ω fc hθ hθT h k hk t ht x hx
      obtain ⟨hS, hreg, hgram, hnest, hsupp, hone, hu0, hinit⟩ := h
      have hΩ0 : ∀ r, r ≤ N → Ω r ⊆ Ω 0 := by
        intro r
        induction r with
        | zero => exact fun _ => Subset.rfl
        | succ r ih => exact fun hr => (hnest r (by omega)).trans (ih (by omega))
      have hprev : ∀ j ≤ m, ∀ s ∈ Icc 0 θ, ∀ y ∈ Ω m,
          (s+1)^j * nablaKRm04NormSqIntrinsic S j s y ≤ B^2 :=
        hbound X D S θ Ω fc hθ hθT ⟨hS, hreg, hgram, hnest, hsupp, hone, hu0, hinit⟩
      by_cases hkm : k ≤ m
      · exact (hprev k hkm t ht x (hnest m (by omega) hx)).trans
          (pow_le_pow_left₀ (zero_le_one.trans hB) (le_max_left _ _) 2)
      · have he : k = m+1 := by omega
        subst k
        have hlocal := shifted_tpow_curvature_derivative_bound_of_fixedCutoff S hS hθ
          (η := 1) zero_lt_one hB m (fc ⟨m, by omega⟩) hreg hgram (hsupp ⟨m, by omega⟩)
          (hone ⟨m, by omega⟩)
          (fun s hs y hy => hu0 s hs y (hΩ0 m (by omega) hy))
          (fun j _ hj => hprev j hj)
          (fun y hy => by
            simpa only [one_pow, one_mul] using
              (hinit (m+1) (by omega) hm y (hΩ0 m (by omega) hy)))
          (hA (m+1) (by omega) hm)
        have hnumeric :
            bernsteinMaximumBound (shiHigherBernsteinCoeff B)
              (shiHigherBernsteinConst (Module.finrank ℝ E) m (θ + 1) B)
              (eps ⟨m, by omega⟩) (θ + 1) ≤
            bernsteinMaximumBound (shiHigherBernsteinCoeff B)
              (shiHigherBernsteinConst (Module.finrank ℝ E) m (T + 1) B)
              (eps ⟨m, by omega⟩) (T + 1) := by
          apply bernsteinMaximumBound_mono (shiHigherBernsteinCoeff_pos B)
            ((shiHigherBernsteinConst_mono_time _ _ B (zero_le_one.trans hB))
              (show θ+1 ∈ Ici 0 by change 0 ≤ θ+1; linarith)
              (show T + 1 ∈ Ici 0 by change 0 ≤ T + 1; linarith)
              (by linarith))
            (by positivity) (by linarith)
            (fc ⟨m,by omega⟩).err_nonneg le_rfl
        have hval : (t+1)^(m+1) * nablaKRm04NormSqIntrinsic S (m+1) t x ≤ step :=
          (hlocal t ht x hx).trans
            (div_le_div_of_nonneg_right (max_le_max le_rfl hnumeric) (shiHigherShift_pos B).le)
        have hsqrt : step ≤ (max B (Real.sqrt step))^2 := by
          have hh := pow_le_pow_left₀ (Real.sqrt_nonneg step)
            (le_max_right B (Real.sqrt step)) 2
          rwa [Real.sq_sqrt hstep0] at hh
        exact hval.trans hsqrt
  obtain ⟨B, hB, hbound⟩ := hb N le_rfl
  refine ⟨B^2, by nlinarith, ?_⟩
  intro X _ _ _ _ D S θ hθ hθT hS hreg hgram Ω fc hnest hsupp hone hu0 hinit k hk t ht x hx
  have hh := hbound X D S θ Ω fc hθ hθT
    ⟨hS, hreg, hgram, hnest, hsupp, hone, hu0, hinit⟩ k hk t ht x hx
  have hw : 1 ≤ (t+1)^k := one_le_pow₀ (by linarith [ht.1])
  exact (le_mul_of_one_le_left (nablaKRm04NormSqIntrinsic_nonneg S k t x) hw).trans hh

end DifferentialGeometry.PDE.RicciFlow
