import DifferentialGeometry.Geometry.Flow.RicciFlow.Estimates.InitialMetricTimeBounds
import DifferentialGeometry.Geometry.Flow.RicciFlow.Estimates.CurvatureMetricComparison
import DifferentialGeometry.Geometry.Metric.Convergence.CovariantDerivative.Self
import DifferentialGeometry.Geometry.Flow.RicciFlow.Compactness.Metric.Endpoint.CovariantContinuity
import DifferentialGeometry.Geometry.Flow.RicciFlow.Compactness.Shi.CurvatureDerivativeBounds
import DifferentialGeometry.Geometry.Metric.Convergence.CovariantDerivative.Norm.ManifoldUniformComparison

set_option autoImplicit false
noncomputable section
open Set Filter Bundle Manifold DifferentialGeometry DifferentialGeometry.Tensor0SBundle
open DifferentialGeometry.Geometry.Curvature DifferentialGeometry.CheegerGromovCompactness
open scoped Manifold ContDiff BigOperators Topology

namespace DifferentialGeometry.PDE.RicciFlow

universe u

variable {E H : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]

theorem exists_uniform_closed_metric_covariant_bounds
    (N : ℕ) (T Λ K : ℝ) (hΛ : 1 ≤ Λ) (hK : 0 ≤ K)
    (A : ℕ → ℝ) (hA : ∀ q, 1 ≤ q → q ≤ N → 0 ≤ A q) :
    ∃ C : ℕ → ℝ, (∀ q, 0 ≤ C q) ∧
      ∀ {M : Type u} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [T2Space M]
        (U : Set M), IsOpen U → ∀ (R : SmoothRiemannianMetric I M)
        (D : RealTimeInterval) (θ : ℝ), 0 ≤ θ → θ ≤ T → Ioo 0 θ ⊆ D.regular →
        ∀ S : SolutionOn (I := I) (M := M) D, IsSolutionOn S →
          (∀ (x₀ : M) (i j : Fin (Module.finrank ℝ E)),
            ContMDiffOn (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) ∞
              (fun p : ℝ × M => DifferentialGeometry.Tensor.Coordinates.chartGramMatrix
                (S.base.metric p.1) x₀ p.2 i j)
              (Icc 0 θ ×ˢ (trivializationAt E (TangentSpace I) x₀).baseSet)) →
          (∀ t ∈ Icc 0 θ, MetricUniformEquivalentOn U R (S.base.metric t) Λ) →
          (∀ q, 1 ≤ q → q ≤ N → ∀ x ∈ U,
            metricCovDerivNorm q (S.base.metric 0) R x ≤ A q) →
          MovingShiBoundOn U 0 θ (fun _ t => S.base.metric t) N K →
          ∀ q, 1 ≤ q → q ≤ N → ∀ t ∈ Icc 0 θ, ∀ x ∈ U,
            metricCovDerivNorm q (S.base.metric t) R x ≤ C q := by
  classical
  let _ : CompleteSpace E := FiniteDimensional.complete ℝ E
  have hb : ∀ q : ℕ, q ≤ N → ∃ C : ℝ, 0 ≤ C ∧
      ∀ {M : Type u} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [T2Space M]
        (U : Set M), IsOpen U → ∀ (R : SmoothRiemannianMetric I M)
        (D : RealTimeInterval) (θ : ℝ), 0 ≤ θ → θ ≤ T → Ioo 0 θ ⊆ D.regular →
        ∀ S : SolutionOn (I := I) (M := M) D, IsSolutionOn S →
          (∀ (x₀ : M) (i j : Fin (Module.finrank ℝ E)),
            ContMDiffOn (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) ∞
              (fun p : ℝ × M => DifferentialGeometry.Tensor.Coordinates.chartGramMatrix
                (S.base.metric p.1) x₀ p.2 i j)
              (Icc 0 θ ×ˢ (trivializationAt E (TangentSpace I) x₀).baseSet)) →
          (∀ t ∈ Icc 0 θ, MetricUniformEquivalentOn U R (S.base.metric t) Λ) →
          (∀ q, 1 ≤ q → q ≤ N → ∀ x ∈ U,
            metricCovDerivNorm q (S.base.metric 0) R x ≤ A q) →
          MovingShiBoundOn U 0 θ (fun _ t => S.base.metric t) N K →
          1 ≤ q → ∀ t ∈ Icc 0 θ, ∀ x ∈ U,
            metricCovDerivNorm q (S.base.metric t) R x ≤ C := by
    intro q
    induction q using Nat.strong_induction_on with
    | h q ih =>
      intro hqN
      by_cases hq : q = 0
      · subst q
        exact ⟨0, le_rfl, fun _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ h => (by omega)⟩
      · let Cg := fun r => if hr : r < q then (ih r hr (by omega)).choose else 0
        have hCg (r : ℕ) (hr : r < q) : 0 ≤ Cg r ∧
            ∀ {M : Type u} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
              [T2Space M] (U : Set M), IsOpen U → ∀ (R : SmoothRiemannianMetric I M)
              (D : RealTimeInterval) (θ : ℝ), 0 ≤ θ → θ ≤ T → Ioo 0 θ ⊆ D.regular →
              ∀ S : SolutionOn (I := I) (M := M) D, IsSolutionOn S →
                (∀ (x₀ : M) (i j : Fin (Module.finrank ℝ E)),
                  ContMDiffOn (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) ∞
                    (fun p : ℝ × M => DifferentialGeometry.Tensor.Coordinates.chartGramMatrix
                      (S.base.metric p.1) x₀ p.2 i j)
                    (Icc 0 θ ×ˢ (trivializationAt E (TangentSpace I) x₀).baseSet)) →
                (∀ t ∈ Icc 0 θ, MetricUniformEquivalentOn U R (S.base.metric t) Λ) →
                (∀ q, 1 ≤ q → q ≤ N → ∀ x ∈ U,
                  metricCovDerivNorm q (S.base.metric 0) R x ≤ A q) →
                MovingShiBoundOn U 0 θ (fun _ t => S.base.metric t) N K →
                1 ≤ r → ∀ t ∈ Icc 0 θ, ∀ x ∈ U,
                  metricCovDerivNorm r (S.base.metric t) R x ≤ Cg r := by
          simpa only [Cg, dite_eq_left hr] using (ih r hr (by omega)).choose_spec
        let cf := ricTowerCoeffs (Module.finrank ℝ E) q Λ Cg K
        refine ⟨metricCovOrderEvolutionConstant cf.slope cf.offset T (A q),
          Real.sqrt_nonneg _, ?_⟩
        intro M _ _ _ _ U hU R D θ hθ hθT hreg S hSol hgram hequiv hinit hShi hqpos t ht x hx
        have hbound := metricCovOrderBound_stage_closed S hSol θ hθ hreg hgram R U hU
          q hqpos Λ hΛ hequiv Cg
          (fun r hr hrq s hs y hy =>
            (hCg r hrq).2 U hU R D θ hθ hθT hreg S hSol hgram hequiv hinit hShi hr s hs y hy)
          K hK (fun r hr => hShi r (hr.trans hqN)) (A q) (hA q hqpos hqN)
          (hinit q hqpos hqN) t ht x hx
        refine hbound.trans ?_
        unfold metricCovOrderEvolutionConstant metricCovOrderEvolutionAlpha
          metricCovOrderEvolutionBeta
        apply Real.sqrt_le_sqrt
        apply mul_le_mul_of_nonneg_right
        · exact Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left hθT (by positivity))
        · positivity
  let C := fun q => if hq : q ≤ N then (hb q hq).choose else 0
  refine ⟨C, ?_, ?_⟩
  · intro q
    by_cases hq : q ≤ N
    · simpa only [C, dite_eq_left hq] using (hb q hq).choose_spec.1
    · simp only [C, dite_eq_right hq, le_rfl]
  · intro M _ _ _ _ U hU R D θ hθ hθT hreg S hS hgram hequiv hinit hShi q hq hqN
    simpa only [C, dite_eq_left hqN] using
      (hb q hqN).choose_spec.2 U hU R D θ hθ hθT hreg S hS hgram hequiv hinit hShi hq

theorem exists_uniform_metricDerivNorm_time_lipschitz_of_finite_ricci_bounds
    (N : ℕ) (T Λ K : ℝ) (hΛ : 1 ≤ Λ) (hK : 0 ≤ K)
    (A : ℕ → ℝ) (hA : ∀ q, 1 ≤ q → q ≤ N → 0 ≤ A q) :
    ∃ L : ℝ, 0 ≤ L ∧
      ∀ {M : Type u} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [T2Space M]
        (U : Set M), IsOpen U → ∀ (R : SmoothRiemannianMetric I M)
        (D : RealTimeInterval) (θ : ℝ), 0 ≤ θ → θ ≤ T → Ioo 0 θ ⊆ D.regular →
        ∀ S : SolutionOn (I := I) (M := M) D, IsSolutionOn S →
          (∀ (x₀ : M) (i j : Fin (Module.finrank ℝ E)),
            ContMDiffOn (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) ∞
              (fun p : ℝ × M => DifferentialGeometry.Tensor.Coordinates.chartGramMatrix
                (S.base.metric p.1) x₀ p.2 i j)
              (Icc 0 θ ×ˢ (trivializationAt E (TangentSpace I) x₀).baseSet)) →
          (∀ t ∈ Icc 0 θ, MetricUniformEquivalentOn U R (S.base.metric t) Λ) →
          (∀ q, 1 ≤ q → q ≤ N → ∀ x ∈ U,
            metricCovDerivNorm q (S.base.metric 0) R x ≤ A q) →
          MovingShiBoundOn U 0 θ (fun _ t => S.base.metric t) N K →
          ∀ q ≤ N, ∀ s ∈ Icc 0 θ, ∀ t ∈ Icc 0 θ, ∀ x ∈ U,
            metricDerivNorm q (S.base.metric s) (S.base.metric t) R x ≤ L * |s - t| := by
  classical
  let _ : CompleteSpace E := FiniteDimensional.complete ℝ E
  obtain ⟨C, hC, hCbound⟩ := exists_uniform_closed_metric_covariant_bounds.{u} (I := I)
    N T Λ K hΛ hK A hA
  let cf := fun q => ricTowerCoeffs (Module.finrank ℝ E) q Λ C K
  let Lq := fun q => if q = 0 then 2 * Λ * K else 2 * ((cf q).slope * C q + (cf q).offset)
  have hLq (q : ℕ) : 0 ≤ Lq q := by
    by_cases hq : q = 0
    · simp only [Lq, ite_eq_left hq]
      positivity
    · have hc := ricCoeffs_nonneg (Module.finrank ℝ E) q Λ C K hΛ hK
      simp only [Lq, ite_eq_right hq]
      exact mul_nonneg (by norm_num) (add_nonneg (mul_nonneg hc.1 (hC q)) hc.2)
  refine ⟨∑ q ∈ Finset.range (N + 1), Lq q, Finset.sum_nonneg (fun q _ => hLq q), ?_⟩
  intro M _ _ _ _ U hU R D θ hθ hθT hreg S hS hgram hequiv hinit hShi q hq s hs t ht x hx
  have hnorm := hCbound U hU R D θ hθ hθT hreg S hS hgram hequiv hinit hShi
  let Ev := fun r (y : M) => (-2 : ℝ) • nablaRicReal (fun _ u => S.base.metric u) R q 0 r y
  have hev : ∀ y ∈ U, ∀ r ∈ Ioo 0 θ, ∀ v : Fin (q + 2) → TangentSpace I y,
      HasDerivAt (fun u => metricCovDeriv (S.base.metric u) R q y v) (Ev r y v) r := by
    intro y _ r hr v
    have hwin : ∀ _i : ℕ, Icc r r ⊆ D.regular := by
      intro _ z hz
      have he : z = r := le_antisymm hz.2 hz.1
      exact he ▸ hreg hr
    exact hevComp_of_solutions (I := I) (N := q) (gRef := R)
      (fun _ => D) (fun _ => S) (fun _ => hS) (fun _ _ => rfl) hwin
      (fun _ => solutionTowerSwap_regularity R S hS q (fun {z} hz => D.regular_isOpen.mem_nhds hz))
      0 y r ⟨le_rfl, le_rfl⟩ v
  have hEv : ∀ y ∈ U, ∀ r ∈ Ioo 0 θ,
      Real.sqrt (normSq0S R y (q + 2) (Ev r y)) ≤ Lq q := by
    intro y hy r hr
    have hrc : r ∈ Icc 0 θ := Ioo_subset_Icc_self hr
    dsimp only [Ev]
    rw [sqrt_normSq0S_smul, show |(-2 : ℝ)| = 2 by norm_num]
    by_cases hzero : q = 0
    · subst q
      simp only [Lq, ite_eq_left rfl]
      have hcomp := sqrt_normSq0S_le_of_metric_equiv (g := S.base.metric r) (h := R) y 2 hΛ
        (fun v => (metricUniformEquivalentOn_symm (hequiv r hrc)).2 y hy v)
        (nablaRicReal (fun _ u => S.base.metric u) R 0 0 r y)
      rw [Real.sqrt_sq (zero_le_one.trans hΛ)] at hcomp
      have hh := hShi 0 (Nat.zero_le N) 0 r hrc y hy
      have hn : Real.sqrt (normSq0S (S.base.metric r) y 2
          (nablaRicReal (fun _ u => S.base.metric u) R 0 0 r y)) ≤ K := hh
      nlinarith
    · have hc := ricCoeffs_nonneg (Module.finrank ℝ E) q Λ C K hΛ hK
      have hh := ric_bound_field_on (I := I) (gSeq := fun _ u => S.base.metric u)
        (gRef := R) hU q (Nat.one_le_iff_ne_zero.mpr hzero) Λ hΛ
        (fun _ => hequiv) C
        (fun a ha haq _ u hu z hz => hnorm a ha (by omega) u hu z hz)
        K hK (fun a ha => hShi a (ha.trans hq)) 0 r hrc y hy
      have hh' := hh.trans (add_le_add
        (mul_le_mul_of_nonneg_left (hnorm q (by omega) hq r hrc y hy) hc.1) le_rfl)
      simp only [Lq, ite_eq_right hzero]
      exact mul_le_mul_of_nonneg_left hh' (by norm_num)
  have hlip := metricDerivNorm_le_of_closed_evolution S.base.metric 0 θ hgram R q Ev U
    (Lq q) (hLq q) hev hEv s hs t ht x hx
  have hsum : Lq q ≤ ∑ a ∈ Finset.range (N + 1), Lq a :=
    Finset.single_le_sum (fun a _ => hLq a) (Finset.mem_range.mpr (by omega))
  exact hlip.trans (mul_le_mul_of_nonneg_right hsum (abs_nonneg _))

omit [I.Boundaryless] in
private theorem chartGram_contMDiffOn_regular_of_isSolutionOn {M : Type*} [TopologicalSpace M]
    [ChartedSpace H M] [IsManifold I ∞ M] [T2Space M] {D : RealTimeInterval}
    {S : SolutionOn (I := I) (M := M) D} (hS : IsSolutionOn S)
    (x₀ : M) (i j : Fin (Module.finrank ℝ E)) :
    ContMDiffOn (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ) ∞
      (fun p : ℝ × M =>
        DifferentialGeometry.Tensor.Coordinates.chartGramMatrix (I := I) (S.base.metric p.1) x₀
          p.2 i j)
      (D.regular ×ˢ (trivializationAt E (TangentSpace I) x₀).baseSet) := by
  set e := trivializationAt E (TangentSpace I) x₀ with he
  have hframe : IsLocalFrameOn I E (∞ : WithTop ℕ∞)
      (e.localFrame (DifferentialGeometry.Tensor.Coordinates.chartModelBasis E)) e.baseSet :=
    e.isLocalFrameOn_localFrame_baseSet I (∞ : WithTop ℕ∞)
      (DifferentialGeometry.Tensor.Coordinates.chartModelBasis E)
  have hbridge : ∀ {x : M} (hx : x ∈ e.baseSet) (k : Fin (Module.finrank ℝ E)),
      e.localFrame (DifferentialGeometry.Tensor.Coordinates.chartModelBasis E) k x
        = DifferentialGeometry.Tensor.Coordinates.chartBasisVecFiber (I := I) x₀ k x := by
    intro x hx k
    rw [e.localFrame_apply_of_mem_baseSet
      (DifferentialGeometry.Tensor.Coordinates.chartModelBasis E) hx]
    unfold Bundle.Trivialization.basisAt
      DifferentialGeometry.Tensor.Coordinates.chartBasisVecFiber
    rw [Module.Basis.map_apply]
    exact congrFun (e.symm_continuousLinearEquivAt_eq hx)
      ((DifferentialGeometry.Tensor.Coordinates.chartModelBasis E) k)
  have h := hS.smoothMetric.frameCompSmooth
    (e.localFrame (DifferentialGeometry.Tensor.Coordinates.chartModelBasis E)) hframe i j
  refine h.congr fun p hp => ?_
  have hx : p.2 ∈ e.baseSet := hp.2
  simp only [DifferentialGeometry.Tensor.Coordinates.chartGramMatrix_apply, hbridge hx i,
    hbridge hx j, SolutionOn.family]

private theorem metric_inner_bounds_of_curvDerivNorm_zero_le {M : Type*} [TopologicalSpace M]
    [ChartedSpace H M] [IsManifold I ∞ M] [T2Space M] {T T₂ B₀ : ℝ} (hT : 0 < T)
    (hTT : T < T₂) (g : ℝ → SmoothRiemannianMetric I M)
    (hS : IsSolutionOn ({ base.metric := g } : SolutionOn (I := I) (M := M)
      (RealTimeInterval.closed (-T₂) 0 (neg_nonpos.mpr (hT.le.trans hTT.le)))))
    (hcurv : ∀ s ∈ Icc (-T) 0, ∀ x : M, curvDerivNorm 0 (g s) x ≤ B₀)
    {s t : ℝ} (hs : s ∈ Icc (-T) 0) (ht : t ∈ Icc (-T) 0) (x : M) (v : TangentSpace I x) :
    (Real.exp (2 * (Module.finrank ℝ E : ℝ) ^ 2 * |B₀| * T))⁻¹ * (g t).inner x v v ≤
        (g s).inner x v v ∧
      (g s).inner x v v ≤
        Real.exp (2 * (Module.finrank ℝ E : ℝ) ^ 2 * |B₀| * T) * (g t).inner x v v := by
  let S : SolutionOn (I := I) (M := M)
      (RealTimeInterval.closed (-T₂) 0 (neg_nonpos.mpr (hT.le.trans hTT.le))) :=
    { base.metric := g }
  have hRm : ∀ r ∈ Icc (-T) 0,
      normSq0S (S.base.metric r) x 4 (S.base.rm04 r x) ≤ B₀ ^ 2 := by
    intro r hr
    have hc := hcurv r hr x
    have hsq := curvNormSq_eq S 0 r x
    simp only [nablaKRm04NormSqIntrinsic, nablaKRm04Field_zero, Nat.add_zero] at hsq
    rw [← hsq]
    have h0 : 0 ≤ curvDerivNormSq 0 (g r) x := normSq0S_nonneg _ _ _ _
    have hsq' : curvDerivNorm 0 (g r) x ^ 2 = curvDerivNormSq 0 (g r) x := Real.sq_sqrt h0
    rw [← hsq']
    exact pow_le_pow_left₀ (Real.sqrt_nonneg _) hc 2
  have hb := metric_inner_exp_bounds_of_curvature_bound S hS
    (fun r hr => ⟨by linarith [hr.1], hr.2⟩) (fun r hr => ⟨by linarith [hr.1], hr.2⟩) x hRm
    hs ht v
  rw [Real.sqrt_sq_eq_abs] at hb
  have hst : |s - t| ≤ T := abs_le.mpr ⟨by linarith [hs.1, ht.2], by linarith [hs.2, ht.1]⟩
  have hc : 0 ≤ 2 * (Module.finrank ℝ E : ℝ) ^ 2 * |B₀| := by positivity
  have he : Real.exp (2 * (Module.finrank ℝ E : ℝ) ^ 2 * |B₀| * |s - t|) ≤
      Real.exp (2 * (Module.finrank ℝ E : ℝ) ^ 2 * |B₀| * T) :=
    Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left hst hc)
  have hn := metric_inner_self_nonneg (g t) x v
  constructor
  · refine le_trans ?_ hb.1
    rw [← Real.exp_neg]
    exact mul_le_mul_of_nonneg_right (Real.exp_le_exp.mpr (neg_le_neg
      (mul_le_mul_of_nonneg_left hst hc))) hn
  · exact hb.2.trans (mul_le_mul_of_nonneg_right he hn)

theorem exists_metricDerivNorm_initial_reference_time_lipschitz_of_curvature_jets
    [NeZero (Module.finrank ℝ E)] (p : ℕ) {T T₂ : ℝ} (hT : 0 < T) (hTT : T < T₂)
    (B : ℕ → ℝ) :
    ∃ L : ℝ, 0 ≤ L ∧ ∀ {M : Type u} [TopologicalSpace M] [ChartedSpace H M]
      [IsManifold I ∞ M] [T2Space M] [SigmaCompactSpace M]
      (g : ℝ → SmoothRiemannianMetric I M),
      IsSolutionOn ({ base.metric := g } : SolutionOn (I := I) (M := M)
        (RealTimeInterval.closed (-T₂) 0 (neg_nonpos.mpr (hT.le.trans hTT.le)))) →
      (∀ m ≤ p, ∀ s ∈ Icc (-T) 0, ∀ x : M, curvDerivNorm m (g s) x ≤ B m) →
      ∀ q ≤ p, ∀ σ ∈ Icc (-T) 0, ∀ σ' ∈ Icc (-T) 0, ∀ x : M,
        metricDerivNorm q (g σ) (g σ') (g (-T)) x ≤ L * |σ - σ'| := by
  classical
  let _ : CompleteSpace E := FiniteDimensional.complete ℝ E
  let d : ℝ := Module.finrank ℝ E
  let Λ := Real.exp (2 * d ^ 2 * |B 0| * T)
  have hΛ : 1 ≤ Λ := Real.one_le_exp (by positivity)
  let KShi := ∑ m ∈ Finset.range (p + 1), Real.sqrt (d ^ ((2 + m) + 2)) * |B m|
  have hKShi : 0 ≤ KShi := Finset.sum_nonneg fun m _ => by positivity
  obtain ⟨L, hL, hlip⟩ :=
    exists_uniform_metricDerivNorm_time_lipschitz_of_finite_ricci_bounds.{u}
      (I := I) p T Λ KShi hΛ hKShi (fun _ => 0) (fun _ _ _ => le_rfl)
  refine ⟨L, hL, ?_⟩
  intro M _ _ _ _ _ g hS hjets
  let D := RealTimeInterval.closed (-T₂) 0 (neg_nonpos.mpr (hT.le.trans hTT.le))
  let S0 : SolutionOn (I := I) (M := M) D := { base.metric := g }
  let S' := S0.timeShift (-T)
  have hS' : IsSolutionOn S' := isSolutionOn_timeShift hS (-T)
  have hmet (s : ℝ) : S'.base.metric s = g (s + -T) := rfl
  have hkey : ∀ θ : ℝ, 0 ≤ θ → θ < T → ∀ q ≤ p, ∀ s ∈ Icc 0 θ, ∀ t ∈ Icc 0 θ, ∀ x : M,
      metricDerivNorm q (g (s + -T)) (g (t + -T)) (g (-T)) x ≤ L * |s - t| := by
    intro θ hθ hθT q hq s hs t ht x
    have hsub : Icc 0 θ ⊆ (D.timeShift (-T)).regular := by
      intro r hr
      change r + -T ∈ Ioo (-T₂) 0
      exact ⟨by linarith [hr.1], by linarith [hr.2]⟩
    have hgram : ∀ (x₀ : M) (i j : Fin (Module.finrank ℝ E)),
        ContMDiffOn (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) ∞
          (fun p : ℝ × M => DifferentialGeometry.Tensor.Coordinates.chartGramMatrix
            (S'.base.metric p.1) x₀ p.2 i j)
          (Icc 0 θ ×ˢ (trivializationAt E (TangentSpace I) x₀).baseSet) :=
      fun x₀ i j => (chartGram_contMDiffOn_regular_of_isSolutionOn hS' x₀ i j).mono
        (prod_mono hsub subset_rfl)
    have hequiv : ∀ t ∈ Icc 0 θ,
        MetricUniformEquivalentOn univ (g (-T)) (S'.base.metric t) Λ := by
      intro t ht
      refine ⟨hΛ, fun y _ v => ?_⟩
      rw [hmet]
      exact metric_inner_bounds_of_curvDerivNorm_zero_le hT hTT g hS
        (fun r hr y => hjets 0 (Nat.zero_le p) r hr y)
        ⟨by linarith [ht.1], by linarith [ht.2]⟩ ⟨le_rfl, by linarith⟩ y v
    have hinit : ∀ q, 1 ≤ q → q ≤ p → ∀ x ∈ (univ : Set M),
        metricCovDerivNorm q (S'.base.metric 0) (g (-T)) x ≤ 0 := by
      intro q hq1 _ x _
      rw [hmet, zero_add]
      obtain ⟨q', rfl⟩ : ∃ q', q = q' + 1 := ⟨q - 1, by omega⟩
      have h0 : normSq0S (g (-T)) x (q' + 1 + 2) 0 = 0 :=
        ((tensor0SMetricData (g (-T)) x _).inner_self_eq_zero_iff 0).2 rfl
      unfold metricCovDerivNorm
      rw [covDeriv_self_succ]
      simp only [ContMDiffSection.coe_zero, Pi.zero_apply, h0, Real.sqrt_zero, le_refl]
    have hShi : MovingShiBoundOn univ 0 θ (fun _ t => S'.base.metric t) p KShi := by
      intro m hm _ t ht y _
      have hj := hjets m hm (t + -T) ⟨by linarith [ht.1], by linarith [ht.2]⟩ y
      calc Real.sqrt (normSq0S (S'.base.metric t) y (2 + m)
            (ricCovTower (S'.base.metric t) (S'.base.metric t) m y))
          ≤ Real.sqrt ((Module.finrank ℝ E : ℝ) ^ ((2 + m) + 2)) *
              curvDerivNorm m (S'.base.metric t) y :=
            sqrt_normSq0S_ricCovTower_le_curvDerivNorm _ m y
        _ ≤ Real.sqrt (d ^ ((2 + m) + 2)) * |B m| :=
            mul_le_mul_of_nonneg_left (hj.trans (le_abs_self _)) (Real.sqrt_nonneg _)
        _ ≤ KShi := Finset.single_le_sum (f := fun m => Real.sqrt (d ^ ((2 + m) + 2)) * |B m|)
            (fun m _ => by positivity) (Finset.mem_range.mpr (by omega))
    exact hlip univ isOpen_univ (g (-T)) (D.timeShift (-T)) θ hθ hθT.le
      (Ioo_subset_Icc_self.trans hsub) S' hS' hgram hequiv hinit hShi q hq s hs t ht x
      (mem_univ x)
  have hinter : ∀ q ≤ p, ∀ σ ∈ Ico (-T) 0, ∀ σ' ∈ Ico (-T) 0, ∀ x : M,
      metricDerivNorm q (g σ) (g σ') (g (-T)) x ≤ L * |σ - σ'| := by
    intro q hq σ hσ σ' hσ' x
    have h := hkey (max σ σ' + T) (by linarith [le_max_left σ σ', hσ.1])
      (by linarith [max_lt hσ.2 hσ'.2]) q hq (σ + T)
      ⟨by linarith [hσ.1], by linarith [le_max_left σ σ']⟩ (σ' + T)
      ⟨by linarith [hσ'.1], by linarith [le_max_right σ σ']⟩ x
    rwa [show σ + T + -T = σ by ring, show σ' + T + -T = σ' by ring,
      show σ + T - (σ' + T) = σ - σ' by ring] at h
  have hcont : ∀ q : ℕ, ∀ σ : ℝ, ∀ x : M, ContinuousWithinAt
      (fun t => metricDerivNorm q (g σ) (g t) (g (-T)) x) (Iic 0) 0 := by
    intro q σ x
    obtain ⟨basis, horth⟩ := exists_orthonormal_basis (g (-T)) x
    have hinv := metricInverseInBasis_of_orthonormal (g (-T)) basis horth
    have hnorm (h : SmoothRiemannianMetric I M) :
        metricDerivNorm q (g σ) h (g (-T)) x = Real.sqrt
          (∑ slots : Fin (q + 2) → Fin (Module.finrank ℝ (TangentSpace I x)),
            (component0S basis (metricCovDeriv (g σ) (g (-T)) q x) slots -
              component0S basis (metricCovDeriv h (g (-T)) q x) slots) ^ 2) := by
      rw [metricDerivNorm, metricDiffCovDerivAt,
        normSq0S_identity_eq_sum_sq (g (-T)) x (q + 2) basis hinv]
      congr 1
    simp only [hnorm]
    apply ContinuousWithinAt.sqrt
    apply tendsto_finsetSum
    intro slots _
    exact (continuousWithinAt_const.sub
      (solution_metricCovDeriv_component_continuousWithinAt_terminal S0 hS (neg_lt_zero.mpr hT)
        (fun r hr => ⟨by linarith [hr.1], hr.2⟩) (fun r hr => ⟨by linarith [hr.1], hr.2⟩)
        (g (-T)) q x basis slots)).pow 2
  have hright : ∀ q ≤ p, ∀ σ ∈ Ico (-T) 0, ∀ x : M,
      metricDerivNorm q (g σ) (g 0) (g (-T)) x ≤ L * |σ - 0| := by
    intro q hq σ hσ x
    have hleft := (hcont q σ x).mono Iio_subset_Iic_self
    have hlim : Tendsto (fun t : ℝ => L * |σ - t|) (𝓝[<] 0) (𝓝 (L * |σ - 0|)) :=
      (continuousAt_const.mul (continuousAt_const.sub continuousAt_id).abs).tendsto.mono_left
        nhdsWithin_le_nhds
    apply le_of_tendsto_of_tendsto hleft hlim
    filter_upwards [Ioo_mem_nhdsLT (neg_lt_zero.mpr hT)] with t ht
    exact hinter q hq σ hσ t ⟨ht.1.le, ht.2⟩ x
  intro q hq σ hσ σ' hσ' x
  rcases hσ.2.lt_or_eq with hσ0 | hσ0
  · rcases hσ'.2.lt_or_eq with hσ'0 | hσ'0
    · exact hinter q hq σ ⟨hσ.1, hσ0⟩ σ' ⟨hσ'.1, hσ'0⟩ x
    · subst hσ'0
      exact hright q hq σ ⟨hσ.1, hσ0⟩ x
  · subst hσ0
    rcases hσ'.2.lt_or_eq with hσ'0 | hσ'0
    · rw [metricDerivNorm_symm, abs_sub_comm]
      exact hright q hq σ' ⟨hσ'.1, hσ'0⟩ x
    · subst hσ'0
      rw [metricDerivNorm_self, sub_self, abs_zero, mul_zero]

omit [I.Boundaryless] in
private theorem sqrt_normSq_iterCov_metricTensorField_eq_metricDerivNorm [CompleteSpace E]
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [T2Space M]
    (h g : SmoothRiemannianMetric I M) (j : ℕ) (hj : 1 ≤ j) (x : M) :
    Real.sqrt (normSq0S g x (2 + j) (iterCov g 2 (metricTensorField h) j x)) =
      metricDerivNorm j h g g x := by
  classical
  obtain ⟨b, hb⟩ := exists_orthonormal_basis g x
  rw [metricDerivNorm_eq_iterCov h g g j b
    (metricInverseInBasis_identity_of_orthonormal g b hb)]
  obtain ⟨j', rfl⟩ : ∃ j', j = j' + 1 := ⟨j - 1, by omega⟩
  rw [iterCov_sub, iterCov_metric_zero, sub_zero]

theorem exists_metricDerivNorm_terminal_reference_time_lipschitz_of_curvature_jets
    [NeZero (Module.finrank ℝ E)] (p : ℕ) {T T₂ : ℝ} (hT : 0 < T) (hTT : T < T₂)
    (B : ℕ → ℝ) :
    ∃ L : ℝ, 0 ≤ L ∧ ∀ {M : Type u} [TopologicalSpace M] [ChartedSpace H M]
      [IsManifold I ∞ M] [T2Space M] [SigmaCompactSpace M]
      (g : ℝ → SmoothRiemannianMetric I M),
      IsSolutionOn ({ base.metric := g } : SolutionOn (I := I) (M := M)
        (RealTimeInterval.closed (-T₂) 0 (neg_nonpos.mpr (hT.le.trans hTT.le)))) →
      (∀ m ≤ p, ∀ s ∈ Icc (-T) 0, ∀ x : M, curvDerivNorm m (g s) x ≤ B m) →
      ∀ σ ∈ Icc (-T) 0, ∀ σ' ∈ Icc (-T) 0, ∀ x : M, ∀ a ≤ p,
        metricDerivNorm a (g σ) (g σ') (g 0) x ≤ L * |σ - σ'| := by
  classical
  let _ : CompleteSpace E := FiniteDimensional.complete ℝ E
  obtain ⟨L₁, hL₁, hlip⟩ :=
    exists_metricDerivNorm_initial_reference_time_lipschitz_of_curvature_jets.{u} (I := I)
      p hT hTT B
  let C := Real.exp (2 * (Module.finrank ℝ E : ℝ) ^ 2 * |B 0| * T)
  have hC : 1 ≤ C := Real.one_le_exp (by positivity)
  let Bj := Real.sqrt (C ^ (2 + p)) * (L₁ * T)
  have hBj : 0 ≤ Bj := mul_nonneg (Real.sqrt_nonneg _) (mul_nonneg hL₁ hT.le)
  obtain ⟨Dc, hDc, href⟩ :=
    exists_manifold_uniform_metric_deriv_norm_reference_bound.{u} (I := I) p hC hBj
  refine ⟨Dc * (((p : ℝ) + 1) * L₁), by positivity, ?_⟩
  intro M _ _ _ _ _ g hS hjets σ hσ σ' hσ' x a ha
  have hL := hlip g hS hjets
  have heq : ∀ y ∈ (univ : Set M), ∀ v : TangentSpace I y,
      C⁻¹ * (g (-T)).inner y v v ≤ (g 0).inner y v v ∧
        (g 0).inner y v v ≤ C * (g (-T)).inner y v v :=
    fun y _ v => metric_inner_bounds_of_curvDerivNorm_zero_le hT hTT g hS
      (fun r hr y => hjets 0 (Nat.zero_le p) r hr y) ⟨by linarith, le_rfl⟩
      ⟨le_rfl, by linarith⟩ y v
  have hb : ∀ y ∈ (univ : Set M), ∀ j : ℕ, 1 ≤ j → j ≤ p →
      Real.sqrt (normSq0S (g 0) y (2 + j)
        (iterCov (g (-T)) 2 (metricTensorField (g 0)) j y)) ≤ Bj := by
    intro y _ j hj1 hjp
    have hn := sqrt_normSq0S_le_of_metric_equiv (g (-T)) (g 0) y (2 + j) hC
      (heq y (mem_univ y)) (iterCov (g (-T)) 2 (metricTensorField (g 0)) j y)
    rw [sqrt_normSq_iterCov_metricTensorField_eq_metricDerivNorm (g 0) (g (-T)) j hj1 y] at hn
    have hl := hL j hjp 0 ⟨by linarith, le_rfl⟩ (-T) ⟨le_rfl, by linarith⟩ y
    rw [show (0 : ℝ) - -T = T by ring, abs_of_pos hT] at hl
    exact hn.trans (mul_le_mul (Real.sqrt_le_sqrt (pow_le_pow_right₀ hC (by omega))) hl
      (Real.sqrt_nonneg _) (Real.sqrt_nonneg _))
  have hr := href univ isOpen_univ (g (-T)) (g 0) heq hb (g σ) (g σ') a ha x (mem_univ x)
  calc metricDerivNorm a (g σ) (g σ') (g 0) x
      ≤ Dc * ∑ k ∈ Finset.range (p + 1), metricDerivNorm k (g σ) (g σ') (g (-T)) x := hr
    _ ≤ Dc * ∑ _k ∈ Finset.range (p + 1), L₁ * |σ - σ'| :=
        mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun k hk =>
          hL k (Nat.lt_succ_iff.mp (Finset.mem_range.mp hk)) σ hσ σ' hσ' x) hDc
    _ = Dc * (((p : ℝ) + 1) * L₁) * |σ - σ'| := by
        rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
        push_cast
        ring

end DifferentialGeometry.PDE.RicciFlow
