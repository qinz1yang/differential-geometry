import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch12.ShiInitial_S122

set_option autoImplicit false

/-!
# CH12-S122 / G2b: `hShi_gen_S122` (local Shi with initial data, general order `M`) and the S121 corollary `hShi_S122`.
Route: time shift + scale `parabolicSolution S' t t⁻¹` (S' = the flow on `↥(ball 2R)`), `|Rm| ≤ 189/r` from the Einstein defect,
`exists_uniform_initial_curvature_derivative_bound_on_compact_ball` (InitialLocalCutoff) with centre `x ∈ ball (2R-ρ)`, radius `ρ/4`,
initial `∇^j Rm` from `exists_pos_bound_intrinsic_curvature_derivative_of_metric_jets`, back via the Rm→Ric tower bridge.
-/

noncomputable section
open DifferentialGeometry DifferentialGeometry.Geometry.Hyperbolic DifferentialGeometry.Geometry.Riemannian
open DifferentialGeometry.Geometry.Connection DifferentialGeometry.Tensor0SBundle
open DifferentialGeometry.CheegerGromovCompactness DifferentialGeometry.PDE.RicciFlow
open DifferentialGeometry.Geometry.Curvature DifferentialGeometry.Geometry.Metric
open Set TopologicalSpace Manifold
open scoped Manifold ContDiff Topology ENNReal
universe u
namespace GC.LongTime.Ch12

theorem hShi_gen_S122 (H : FiniteVolumeHyperbolicModel.{u}) {R ρ : ℝ} (M : ℕ) (hR : 0 < R) (hρ : 0 < ρ) :
    ∃ KShi : ℝ, 0 ≤ KShi ∧ ∀ δ' η₀ : ℝ, 0 < δ' → δ' ≤ 1 → 0 < η₀ → η₀ ≤ 1 / 2 →
      ∀ {N : Type u} [TopologicalSpace N] [ChartedSpace (EuclideanSpace ℝ (Fin 3)) N]
        [IsManifold (𝓡 3) ∞ N] [T2Space N] [SigmaCompactSpace N]
        (g : ℝ → SmoothRiemannianMetric (𝓡 3) N) (f : H.Carrier → N) (t : ℝ), 0 < t →
        ∀ (hF : ContMDiffOn (𝓡 3) (𝓡 3) ∞ f (ballU_S98 H R))
          (hinj : ∀ y ∈ ballU_S98 H R, Function.Injective (mfderiv (𝓡 3) (𝓡 3) f y)),
        (∃ (D : RealTimeInterval) (S' : SolutionOn (I := 𝓡 3) (M := ballU_S98 H R) D),
          IsSolutionOn S' ∧ Icc t (2 * t) ⊆ D.regular ∧
          (∀ (x₀ : ballU_S98 H R) (i j : Fin (Module.finrank ℝ (EuclideanSpace ℝ (Fin 3)))),
            ContMDiffOn (𝓘(ℝ, ℝ).prod (𝓡 3)) 𝓘(ℝ, ℝ) ∞
              (fun p : ℝ × ballU_S98 H R => DifferentialGeometry.Tensor.Coordinates.chartGramMatrix
                (S'.base.metric p.1) x₀ p.2 i j)
              (Icc t (2 * t) ×ˢ
                (trivializationAt (EuclideanSpace ℝ (Fin 3)) (TangentSpace (𝓡 3)) x₀).baseSet)) ∧
          (∀ r ∈ Icc t (2 * t),
            S'.base.metric r = pullbackRestrict_S57 H (g r) f (ballU_S98 H R) hF hinj)) →
        (∀ j ≤ M + 2, ∀ p ∈ riemannianBallOf H.metric H.basepoint (2 * R),
          ckErr_S45 H (g t) t⁻¹ f j p < δ') →
        (∀ r ∈ Icc t (2 * t), ∀ p ∈ riemannianBallOf H.metric H.basepoint (2 * R),
          ckErr_S45 H (g r) r⁻¹ f 0 p < η₀) →
        (∀ r ∈ Icc t (2 * t), ∀ p ∈ riemannianBallOf H.metric H.basepoint (2 * R),
          ∀ V : TangentSpace (𝓡 3) (f p),
            |2 * r * ricciTensor (g r) (f p) V V + (g r).inner (f p) V V| ≤
              η₀ * (g r).inner (f p) V V) →
        ∀ s ≤ M, ∀ r ∈ Icc t (2 * t), ∀ x : ballU_S98 H R,
          (x : H.Carrier) ∈ riemannianBallOf H.metric H.basepoint (2 * R - ρ) →
          normSq0S (pullbackRestrict_S57 H (g r) f (ballU_S98 H R) hF hinj) x (2 + s)
            (ricCovTower (pullbackRestrict_S57 H (g r) f (ballU_S98 H R) hF hinj)
              (pullbackRestrict_S57 H (g r) f (ballU_S98 H R) hF hinj) s x) * r ^ (2 + s) ≤
            KShi ^ 2 := by
  classical
  have := sigmaCompact_ballU_S122 H R
  choose Aref hAref0 hAref using fun j : ℕ => exists_refCurv_S122 H (2 * R) j
  choose Cs hCs hCspec using fun j : ℕ =>
    exists_initCurv_S122 (X := ballU_S98 H R) j (Aref j) (hAref0 j)
  obtain ⟨B, hB1, hBspec⟩ := exists_uniform_initial_curvature_derivative_bound_on_compact_ball.{u, 0, 0}
    (I := 𝓡 3) M 1 (ρ / 4) (189 ^ 2) one_pos (by positivity) (fun k => Cs k ^ 2)
    (fun k _ _ => by positivity)
  refine ⟨Real.sqrt (3 ^ (M + 4) * 2 ^ (2 + M) * B), Real.sqrt_nonneg _, ?_⟩
  intro δ' η₀ hδ hδ1 hη hη1 N _ _ _ _ _ g f t ht hF hinj hLF h0 hC0 hdef s hs r hr x hx
  obtain ⟨D, S', hS, hreg, hgram, hmet⟩ := hLF
  have ht2 : t ∈ Icc t (2 * t) := ⟨le_rfl, by linarith⟩
  have hz : t ∈ D.carrier := D.regular_subset (hreg ht2)
  let U : Opens H.Carrier := ballU_S98 H R
  let G : SmoothRiemannianMetric (𝓡 3) U := H.metric.restrictOpen U
  let S := parabolicSolution (I := 𝓡 3) S' t t⁻¹ (inv_pos.2 ht) hz
  have hpt : ∀ τ : ℝ, parabolicTime t t⁻¹ τ = t + τ * t := fun τ => by
    unfold parabolicTime; rw [div_inv_eq_mul]
  have hmem : ∀ τ ∈ Icc (0 : ℝ) 1, t + τ * t ∈ Icc t (2 * t) := fun τ hτ =>
    ⟨by nlinarith [hτ.1], by nlinarith [hτ.2]⟩
  -- the scaled initial metric is the scaled pull-back of `g t`
  have hg0 : S.base.metric 0 =
      pullbackRestrict_S57 H (scaleMetric t⁻¹ (inv_pos.2 ht) (g t)) f U hF hinj := by
    rw [pullbackRestrict_scale_S57, ← hmet t ht2]
    change scaleMetric t⁻¹ (inv_pos.2 ht) (S'.base.metric (parabolicTime t t⁻¹ 0)) = _
    rw [parabolicTime_zero]
  have hck : ∀ (j : ℕ) (y : U), ckErr_S45 H (g t) t⁻¹ f j y = metricDerivNorm j (S.base.metric 0) G G y :=
    fun j y => by
      rw [hg0]; exact ckErr_S45_eq_metricDerivNorm_S57 H (g t) t⁻¹ (inv_pos.2 ht) f U hF hinj j y
  have hhalf : ∀ y : U, metricDerivNorm 0 (S.base.metric 0) G G y ≤ 1 / 2 := fun y => by
    rw [← hck]; exact (hC0 t ht2 y y.2).le.trans hη1
  have hequiv0 : ∀ (y : U) (v : TangentSpace (𝓡 3) y), G.inner y v v ≤ 2 * (S.base.metric 0).inner y v v :=
    fun y v => by
      have := (inner_equiv_of_half_S122 G _ y (hhalf y) v).1
      linarith
  have hcompact := isCompact_closedBall_scaled_S122 H hR hρ (S.base.metric 0) hequiv0 x hx
  have hdefS : ∀ r ∈ Icc t (2 * t), ∀ (y : U) (V : TangentSpace (𝓡 3) y),
      |2 * r * ricciTensor (S'.base.metric r) y V V + (S'.base.metric r).inner y V V| ≤
        η₀ * (S'.base.metric r).inner y V V := by
    intro r hr y V
    rw [hmet r hr]
    obtain ⟨h1, h2⟩ := ricci_pullbackRestrict_S98 H (g r) f U hF hinj y V
    rw [h1, h2]
    exact hdef r hr y y.2 _
  have hinit : ∀ k, 1 ≤ k → k ≤ M → ∀ y : U, nablaKRm04NormSqIntrinsic S k 0 y ≤ Cs k ^ 2 := by
    intro k _ hkM y
    rw [← curvNormSq_eq S k 0 y, curvDerivNormSq, ← Real.sq_sqrt (normSq0S_nonneg _ _ _ _)]
    refine pow_le_pow_left₀ (Real.sqrt_nonneg _) ?_ 2
    have := hCspec k G (S.base.metric 0) y (hhalf y) (fun s' hs' => by
        rw [← hck]
        exact (h0 s' (by omega) y y.2).le.trans hδ1) (fun s' hs' => by
        rw [sqrt_iterCov_eq_curvDerivNorm_S122, curvDerivNorm_restrictOpen]
        exact hAref k (y : H.Carrier) (le_of_lt y.2) s' hs')
    rw [curvCovDeriv_normSq_eq]
    exact this
  have hSsol := parabolicSolution_isSolutionOn S' hS t t⁻¹ (inv_pos.2 ht) hz
  have hcar : Icc (0 : ℝ) 1 ⊆ (parabolicInterval D t t⁻¹ hz).carrier := fun τ hτ => by
    change parabolicTime t t⁻¹ τ ∈ D.carrier
    rw [hpt]; exact D.regular_subset (hreg (hmem τ hτ))
  have hregI : Ioc (0 : ℝ) 1 ⊆ (parabolicInterval D t t⁻¹ hz).regular := fun τ hτ => by
    change parabolicTime t t⁻¹ τ ∈ D.regular
    rw [hpt]; exact hreg (hmem τ ⟨hτ.1.le, hτ.2⟩)
  have hgramS : ∀ (x₀ : U) (i j : Fin (Module.finrank ℝ (EuclideanSpace ℝ (Fin 3)))),
      ContMDiffOn (𝓘(ℝ, ℝ).prod (𝓡 3)) 𝓘(ℝ, ℝ) ∞
        (fun q : ℝ × U => DifferentialGeometry.Tensor.Coordinates.chartGramMatrix
          (S.base.metric q.1) x₀ q.2 i j)
        (Icc (0 : ℝ) 1 ×ˢ
          (trivializationAt (EuclideanSpace ℝ (Fin 3)) (TangentSpace (𝓡 3)) x₀).baseSet) := by
    intro x₀ i j
    have hm : ContMDiff (𝓘(ℝ, ℝ).prod (𝓡 3)) (𝓘(ℝ, ℝ).prod (𝓡 3)) ∞
        (fun q : ℝ × U => (t + q.1 * t, q.2)) :=
      (contMDiff_const.add (contMDiff_fst.mul contMDiff_const)).prodMk contMDiff_snd
    have hmap : MapsTo (fun q : ℝ × U => (t + q.1 * t, q.2))
        (Icc (0 : ℝ) 1 ×ˢ
          (trivializationAt (EuclideanSpace ℝ (Fin 3)) (TangentSpace (𝓡 3)) x₀).baseSet)
        (Icc t (2 * t) ×ˢ
          (trivializationAt (EuclideanSpace ℝ (Fin 3)) (TangentSpace (𝓡 3)) x₀).baseSet) :=
      fun q hq => ⟨hmem q.1 hq.1, hq.2⟩
    have hh := (contMDiffOn_const (c := t⁻¹)).mul ((hgram x₀ i j).comp hm.contMDiffOn hmap)
    apply hh.congr
    intro q _
    simp only [Function.comp_def, S, parabolicSolution, parabolicFamily, hpt,
      DifferentialGeometry.Tensor.Coordinates.chartGramMatrix_apply, scaleMetric_inner, Pi.mul_apply]
  have hmain := hBspec U (parabolicInterval D t t⁻¹ hz) S hSsol hcar hregI hgramS x hcompact
    (fun τ hτ y _ => rm_scaled_le_S122 S' ht (by linarith : η₀ ≤ 1) hz hdefS hτ y)
    (fun k hk1 hkM y _ => hinit k hk1 hkM y)
  have hxx : riemannianEDistOf (S.base.metric 0) x x ≤ ENNReal.ofReal (ρ / 4 / 2) := by
    rw [riemannianEDistOf_self]; exact bot_le
  have hB' : ∀ τ ∈ Icc (0 : ℝ) 1, nablaKRm04NormSqIntrinsic S s τ x ≤ B :=
    fun τ hτ => hmain s hs τ hτ x hxx
  rw [← hmet r hr]
  refine (ricTower_le_of_scaled_S122 S' ht hz s B x hB' hr).trans ?_
  rw [Real.sq_sqrt (by positivity)]
  have h3 : (3 : ℝ) ^ (s + 4) ≤ 3 ^ (M + 4) := pow_le_pow_right₀ (by norm_num) (by omega)
  have h2 : (2 : ℝ) ^ (2 + s) ≤ 2 ^ (2 + M) := pow_le_pow_right₀ (by norm_num) (by omega)
  have hB0 : 0 ≤ B := by linarith
  gcongr

/-- **`hShi_S122`**: the `[FROZEN] CH12-S121 hShi` binder with the one change `h0 : ∀ j ≤ k + 3` (`[FROZEN v2] CH12-S122`;
lead ruling: option A).  `hShi_gen_S122` at `M := k + 1`, `ρ := ℓ/2`, `ℓ = R/((k+1)+1)`. -/
theorem hShi_S122 :
    ∀ (H : FiniteVolumeHyperbolicModel.{u}) (R ε : ℝ) (k : ℕ), 0 < R → 0 < ε →
      ∃ KShi : ℝ, 0 ≤ KShi ∧ ∀ δ' η₀ : ℝ, 0 < δ' → δ' ≤ 1 → 0 < η₀ → η₀ ≤ 1 / 2 →
      ∀ {N : Type u} [TopologicalSpace N] [ChartedSpace (EuclideanSpace ℝ (Fin 3)) N]
        [IsManifold (𝓡 3) ∞ N] [T2Space N] [SigmaCompactSpace N]
        (g : ℝ → SmoothRiemannianMetric (𝓡 3) N) (f : H.Carrier → N) (t : ℝ), 0 < t →
        ∀ (hF : ContMDiffOn (𝓡 3) (𝓡 3) ∞ f (ballU_S98 H R))
          (hinj : ∀ y ∈ ballU_S98 H R, Function.Injective (mfderiv (𝓡 3) (𝓡 3) f y)),
        (∃ (D : RealTimeInterval) (S' : SolutionOn (I := 𝓡 3) (M := ballU_S98 H R) D),
          IsSolutionOn S' ∧ Icc t (2 * t) ⊆ D.regular ∧
          (∀ (x₀ : ballU_S98 H R) (i j : Fin (Module.finrank ℝ (EuclideanSpace ℝ (Fin 3)))),
            ContMDiffOn (𝓘(ℝ, ℝ).prod (𝓡 3)) 𝓘(ℝ, ℝ) ∞
              (fun p : ℝ × ballU_S98 H R => DifferentialGeometry.Tensor.Coordinates.chartGramMatrix
                (S'.base.metric p.1) x₀ p.2 i j)
              (Icc t (2 * t) ×ˢ
                (trivializationAt (EuclideanSpace ℝ (Fin 3)) (TangentSpace (𝓡 3)) x₀).baseSet)) ∧
          (∀ r ∈ Icc t (2 * t),
            S'.base.metric r = pullbackRestrict_S57 H (g r) f (ballU_S98 H R) hF hinj)) →
        (∀ j ≤ k + 3, ∀ p ∈ riemannianBallOf H.metric H.basepoint (2 * R),
          ckErr_S45 H (g t) t⁻¹ f j p < δ') →
        (∀ r ∈ Icc t (2 * t), ∀ p ∈ riemannianBallOf H.metric H.basepoint (2 * R),
          ckErr_S45 H (g r) r⁻¹ f 0 p < η₀) →
        (∀ r ∈ Icc t (2 * t), ∀ p ∈ riemannianBallOf H.metric H.basepoint (2 * R),
          ∀ V : TangentSpace (𝓡 3) (f p),
            |2 * r * ricciTensor (g r) (f p) V V + (g r).inner (f p) V V| ≤
              η₀ * (g r).inner (f p) V V) →
        ∀ s ≤ k + 1, ∀ r ∈ Icc t (2 * t), ∀ x : ballU_S98 H R,
          (x : H.Carrier) ∈ riemannianBallOf H.metric H.basepoint
            (2 * R - R / (((k + 1 : ℕ) : ℝ) + 1) / 2) →
          normSq0S (pullbackRestrict_S57 H (g r) f (ballU_S98 H R) hF hinj) x (2 + s)
            (ricCovTower (pullbackRestrict_S57 H (g r) f (ballU_S98 H R) hF hinj)
              (pullbackRestrict_S57 H (g r) f (ballU_S98 H R) hF hinj) s x) * r ^ (2 + s) ≤
            KShi ^ 2 := by
  intro H R ε k hR hε
  obtain ⟨K, hK, h⟩ := hShi_gen_S122 H (R := R) (ρ := R / (((k + 1 : ℕ) : ℝ) + 1) / 2) (k + 1) hR
    (by positivity)
  exact ⟨K, hK, h⟩

end GC.LongTime.Ch12
