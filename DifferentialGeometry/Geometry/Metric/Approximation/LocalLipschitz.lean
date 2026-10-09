import DifferentialGeometry.Geometry.Metric.EuclideanChart
import DifferentialGeometry.Analysis.Calculus.LipschitzApproximation
import DifferentialGeometry.Geometry.Metric.ChartLipschitz.DistanceComparison

set_option autoImplicit false
noncomputable section
open Bundle Manifold Filter Set DifferentialGeometry
open scoped Manifold ContDiff Topology ENNReal NNReal

namespace DifferentialGeometry.Geometry.Metric

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

private theorem norm_mvfderiv_model_le
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    {q : F → ℝ} {C : ℝ≥0} (hq : LipschitzWith C q) (z : F)
    (v : TangentSpace 𝓘(ℝ, F) z) :
    |mvfderiv (I := 𝓘(ℝ, F)) q z v| ≤ (C : ℝ) * ‖(v : F)‖ := by
  unfold mvfderiv
  rw [mfderiv_eq_fderiv]
  change |fderiv ℝ q z (v : F)| ≤ (C : ℝ) * ‖(v : F)‖
  calc
    _ ≤ ‖fderiv ℝ q z‖ * ‖(v : F)‖ := by
      exact (fderiv ℝ q z).le_opNorm (v : F)
    _ ≤ (C : ℝ) * ‖(v : F)‖ :=
      mul_le_mul_of_nonneg_right (norm_fderiv_le_of_lipschitz ℝ hq) (norm_nonneg _)


theorem exists_contMDiffOn_approx_of_riemannian_lipschitz [RegularSpace M]
    (g : SmoothRiemannianMetric I M) {f : M → ℝ}
    (hf : ∀ x y, edist (f x) (f y) ≤ riemannianEDistOf g x y) (p : M) :
    ∃ U : TopologicalSpace.Opens M, p ∈ U ∧ ∀ ε : ℝ, 0 < ε →
      ∃ u : M → ℝ, ContMDiffOn I 𝓘(ℝ, ℝ) ∞ u U ∧
        (∀ x ∈ U, |u x - f x| < ε) ∧
        ∀ x ∈ U, ∀ v : TangentSpace I x,
          |mvfderiv (I := I) u x v| ≤ 2 * Real.sqrt (g.inner x v v) := by
  let K : ℝ≥0 := 4 / 3
  have hK : (1 : ℝ) < K := by norm_num [K]
  obtain ⟨U₀, hp₀, hsrc, hdist⟩ := exists_open_riemannianEDistOf_comparison g p hK
  have hforward := eventually_norm_mfderiv_metricChartEuclideanEquiv_extChartAt_le g p hK
  obtain ⟨V, hV, hopenV, hpV⟩ := mem_nhds_iff.mp hforward
  let U : TopologicalSpace.Opens M := ⟨(U₀ : Set M) ∩ V, U₀.isOpen.inter hopenV⟩
  let A := metricChartEuclideanEquiv g p
  let φ := extChartAt I p
  let Φ : M → EuclideanSpace ℝ (Fin (Module.finrank ℝ E)) := fun x => A (φ x)
  let Ψ : EuclideanSpace ℝ (Fin (Module.finrank ℝ E)) → M := fun z => φ.symm (A.symm z)
  have hinv (x : M) (hx : x ∈ U) : Ψ (Φ x) = x := by
    dsimp only [Ψ, Φ]
    rw [A.symm_apply_apply]
    exact φ.left_inv (by simpa only [φ, extChartAt_source] using hsrc hx.1)
  have hΦsmooth : ContMDiffOn I 𝓘(ℝ, EuclideanSpace ℝ (Fin (Module.finrank ℝ E))) ∞ Φ U := by
    exact A.contDiff.contMDiff.comp_contMDiffOn
      (contMDiffOn_extChartAt.mono (fun _ hx => hsrc hx.1))
  have hlip : LipschitzOnWith K (f ∘ Ψ) (Φ '' (U : Set M)) := by
    rintro _ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩
    simp only [Function.comp_apply, hinv x hx, hinv y hy]
    calc
      edist (f x) (f y) ≤ riemannianEDistOf g x y := hf x y
      _ ≤ (K : ℝ≥0∞) * edist (Φ x) (Φ y) := by
        rw [show edist (Φ x) (Φ y) = _ from edist_metricChartEuclideanEquiv g p x y]
        simpa only [ENNReal.ofReal_coe_nnreal] using (hdist x hx.1 y hy.1).2
  refine ⟨U, ⟨hp₀, hpV⟩, ?_⟩
  intro ε hε
  obtain ⟨q, hq, hqLip, hqapprox⟩ := hlip.exists_contDiff_lipschitz_approx hε
  refine ⟨q ∘ Φ, hq.contMDiff.comp_contMDiffOn hΦsmooth, ?_, ?_⟩
  · intro x hx
    have h := hqapprox (Φ x) ⟨x, hx, rfl⟩
    simpa only [Function.comp_apply, hinv x hx, Real.dist_eq] using h
  · intro x hx v
    have hPhiDiff := (hΦsmooth x hx).contMDiffAt (U.isOpen.mem_nhds hx)
    rw [mvfderiv_comp_apply x
      (hq.contMDiff.mdifferentiableAt (by simp)) (hPhiDiff.mdifferentiableAt (by simp))]
    have hbound := norm_mvfderiv_model_le hqLip (Φ x)
      (mfderiv I 𝓘(ℝ, EuclideanSpace ℝ (Fin (Module.finrank ℝ E))) Φ x v)
    have hfwd := (hV hx.2).2 v
    change ‖mfderiv I 𝓘(ℝ, EuclideanSpace ℝ (Fin (Module.finrank ℝ E))) Φ x v‖ ≤
      (K : ℝ) * Real.sqrt (g.inner x v v) at hfwd
    refine hbound.trans ((mul_le_mul_of_nonneg_left hfwd K.coe_nonneg).trans ?_)
    calc
      (K : ℝ) * ((K : ℝ) * Real.sqrt (g.inner x v v)) =
          (16 / 9 : ℝ) * Real.sqrt (g.inner x v v) := by norm_num [K]; ring
      _ ≤ 2 * Real.sqrt (g.inner x v v) :=
        mul_le_mul_of_nonneg_right (by norm_num) (Real.sqrt_nonneg _)

end DifferentialGeometry.Geometry.Metric

end
