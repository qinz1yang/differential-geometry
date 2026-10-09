import DifferentialGeometry.Geometry.Exponential.FiniteMetric.ShortInterpolation
import DifferentialGeometry.Geometry.Geodesic.FiniteMetric.Completeness
import DifferentialGeometry.Geometry.Geodesic.FiniteMetric.SpeedBound

/-!
# Short geodesic interpolation is minimizing (add-on to the shared interface D5)

For a complete metric `g` of class `C^{r+1}` (`2 ≤ r`) whose length distance is the ambient
distance (`hnorm`), the neighbourhood `W` of `exists_shortInterpolation_chart` can be chosen so that,
with `x = κ⁻¹ z.1`, `y = κ⁻¹ z.2`, `v = dκ⁻¹(L z)` and `J_s = exp_x (s v)`:

* `J_s = π Φ_s ⟨x, v⟩` (the interpolation runs along the geodesic arc from `x` to `y`);
* `|v|_{g_x} = d(x, y)`;
* `d(x, J_s) = s · d(x, y)` and `d(J_s, y) = (1 - s) · d(x, y)` for `s ∈ [0, 1]`

(`exists_shortInterpolation_chart_dist`). Route: uniform normal charts (CM1.d) on a compact
neighbourhood of `x₀` give the first distance; the unit-speed bound of the geodesic flow and the
triangle inequality give the second.
-/

set_option autoImplicit false

noncomputable section

open Bundle Set Filter Metric
open scoped Manifold ContDiff Topology

namespace Bundle.ContMDiffRiemannianMetric

attribute [-instance] DifferentialGeometry.Tensor0SBundle.tangentSpaceNormedAddCommGroup
  DifferentialGeometry.Tensor0SBundle.tangentSpaceNormedSpace

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [I.Boundaryless] [MetricSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [RiemannianBundle (fun x : M => TangentSpace I x)] [IsRiemannianManifold I M] [CompleteSpace M]
  {r : ℕ∞}

/-- **Short geodesic interpolation with distances (add-on to D5).** All clauses of
`exists_shortInterpolation_chart`, plus: `J_s` lies on the geodesic arc from `x` to `y`,
`|v|_{g_x} = d(x, y)`, `d(x, J_s) = s d(x, y)` and `d(J_s, y) = (1 - s) d(x, y)` for `s ∈ [0, 1]`. -/
theorem exists_shortInterpolation_chart_dist
    (g : ContMDiffRiemannianMetric I ((r : ℕ∞ω) + 1) E (TangentSpace I : M → Type _))
    (hr : 2 ≤ r)
    (hnorm : ∀ (x : M) (w : TangentSpace I x), ‖w‖ₑ = ENNReal.ofReal (Real.sqrt (g.inner x w w)))
    (x₀ : M) :
    ∃ W : Set (E × E), IsOpen W ∧ ((extChartAt I x₀ x₀, extChartAt I x₀ x₀) : E × E) ∈ W ∧
      W ⊆ (extChartAt I x₀).target ×ˢ (extChartAt I x₀).target ∧
      ∃ L : E × E → E, ContDiffOn ℝ r L W ∧
        L (extChartAt I x₀ x₀, extChartAt I x₀ x₀) = 0 ∧
        HasFDerivAt L (ContinuousLinearMap.snd ℝ E E - ContinuousLinearMap.fst ℝ E E)
          (extChartAt I x₀ x₀, extChartAt I x₀ x₀) ∧
        (∀ z ∈ W, z.1 = z.2 → L z = 0) ∧
        (∀ z ∈ W, g.expMap (⟨(extChartAt I x₀).symm z.1,
          mfderiv 𝓘(ℝ, E) I (extChartAt I x₀).symm z.1 (L z)⟩ : TangentBundle I M) =
            (extChartAt I x₀).symm z.2) ∧
        (∀ z ∈ W, ∀ s ∈ Icc (0 : ℝ) 1, g.expMap (⟨(extChartAt I x₀).symm z.1,
          s • mfderiv 𝓘(ℝ, E) I (extChartAt I x₀).symm z.1 (L z)⟩ : TangentBundle I M) ∈
            (extChartAt I x₀).source) ∧
        (∀ s ∈ Icc (0 : ℝ) 1, ContDiffOn ℝ r (fun z : E × E => extChartAt I x₀
          (g.expMap (⟨(extChartAt I x₀).symm z.1,
            s • mfderiv 𝓘(ℝ, E) I (extChartAt I x₀).symm z.1 (L z)⟩ : TangentBundle I M))) W) ∧
        (∀ s : ℝ, HasFDerivAt (fun z : E × E => extChartAt I x₀
          (g.expMap (⟨(extChartAt I x₀).symm z.1,
            s • mfderiv 𝓘(ℝ, E) I (extChartAt I x₀).symm z.1 (L z)⟩ : TangentBundle I M)))
          ((1 - s) • ContinuousLinearMap.fst ℝ E E + s • ContinuousLinearMap.snd ℝ E E)
          (extChartAt I x₀ x₀, extChartAt I x₀ x₀)) ∧
        (∀ z ∈ W, ∀ s : ℝ, g.expMap (⟨(extChartAt I x₀).symm z.1,
          s • mfderiv 𝓘(ℝ, E) I (extChartAt I x₀).symm z.1 (L z)⟩ : TangentBundle I M) =
            (g.geodesicFlow (⟨(extChartAt I x₀).symm z.1,
              mfderiv 𝓘(ℝ, E) I (extChartAt I x₀).symm z.1 (L z)⟩ : TangentBundle I M) s).proj) ∧
        (∀ z ∈ W, Real.sqrt (g.inner ((extChartAt I x₀).symm z.1)
          (mfderiv 𝓘(ℝ, E) I (extChartAt I x₀).symm z.1 (L z))
          (mfderiv 𝓘(ℝ, E) I (extChartAt I x₀).symm z.1 (L z))) =
            dist ((extChartAt I x₀).symm z.1) ((extChartAt I x₀).symm z.2)) ∧
        ∀ z ∈ W, ∀ s ∈ Icc (0 : ℝ) 1,
          dist ((extChartAt I x₀).symm z.1) (g.expMap (⟨(extChartAt I x₀).symm z.1,
            s • mfderiv 𝓘(ℝ, E) I (extChartAt I x₀).symm z.1 (L z)⟩ : TangentBundle I M)) =
              s * dist ((extChartAt I x₀).symm z.1) ((extChartAt I x₀).symm z.2) ∧
          dist (g.expMap (⟨(extChartAt I x₀).symm z.1,
            s • mfderiv 𝓘(ℝ, E) I (extChartAt I x₀).symm z.1 (L z)⟩ : TangentBundle I M))
              ((extChartAt I x₀).symm z.2) =
            (1 - s) * dist ((extChartAt I x₀).symm z.1) ((extChartAt I x₀).symm z.2) := by
  have hr1 : 1 ≤ r := one_le_two.trans hr
  have hD : g.geodesicFlowDomain = univ := g.geodesicFlowDomain_eq_univ hr hnorm
  have hmem : ∀ (P : TangentBundle I M) (τ : ℝ), (P, τ) ∈ g.geodesicFlowDomain := fun P τ => by
    rw [hD]; exact mem_univ _
  obtain ⟨W, hWo, hw₀, hsub, L, hLc, hL0, hLd, hdiag, hexp, hsrc, hJc, hJd⟩ :=
    g.exists_shortInterpolation_chart hr1 x₀
  set κ := extChartAt I x₀ with hκ
  set a₀ : E := κ x₀ with ha₀
  -- a compact neighbourhood of `x₀` with uniform normal charts
  obtain ⟨ε₀, hε₀, hball₀⟩ := Metric.isOpen_iff.mp (isOpen_extChartAt_target (I := I) x₀)
    a₀ (mem_extChartAt_target x₀)
  have hcb : closedBall a₀ (ε₀ / 2) ⊆ κ.target :=
    (closedBall_subset_ball (by linarith)).trans hball₀
  have hK₀c : IsCompact (κ.symm '' closedBall a₀ (ε₀ / 2)) :=
    (isCompact_closedBall a₀ (ε₀ / 2)).image_of_continuousOn
      ((continuousOn_extChartAt_symm x₀).mono hcb)
  obtain ⟨ρ, hρ, hN⟩ := g.exists_uniform_normal_charts hr hnorm hK₀c
  -- the squared length of `v`
  set q : E × E → ℝ := fun z => g.chartInner x₀ z.1 (L z) (L z) with hq
  have hqc : ContinuousOn q W := by
    have h1 : ContinuousOn (fun z : E × E => g.chartInner x₀ z.1) W :=
      (g.contDiffOn_chartInner x₀).continuousOn.comp continuousOn_fst (fun z hz => (hsub hz).1)
    have h2 : ContinuousOn L W := hLc.continuousOn
    exact (h1.clm_apply h2).clm_apply h2
  have hq0 : q (a₀, a₀) = 0 := by
    change g.chartInner x₀ a₀ (L (a₀, a₀)) (L (a₀, a₀)) = 0
    rw [hL0]
    simp
  set W₁ : Set (E × E) := W ∩ (Prod.fst ⁻¹' ball a₀ (ε₀ / 2)) with hW₁
  have hW₁o : IsOpen W₁ := hWo.inter (isOpen_ball.preimage continuous_fst)
  set W' : Set (E × E) := W₁ ∩ q ⁻¹' Iio (ρ ^ 2) with hW'
  have hW'o : IsOpen W' := (hqc.mono inter_subset_left).isOpen_inter_preimage hW₁o isOpen_Iio
  have hw₀' : ((a₀, a₀) : E × E) ∈ W' := by
    refine ⟨⟨hw₀, mem_ball_self (by positivity)⟩, ?_⟩
    change q (a₀, a₀) < ρ ^ 2
    rw [hq0]
    positivity
  have hW'W : W' ⊆ W := fun z hz => hz.1.1
  -- the distance identities on `W'`
  have hdists : ∀ z ∈ W', ∀ s ∈ Icc (0 : ℝ) 1,
      dist (κ.symm z.1) (g.expMap (⟨κ.symm z.1,
        s • mfderiv 𝓘(ℝ, E) I κ.symm z.1 (L z)⟩ : TangentBundle I M)) = s * Real.sqrt (q z) := by
    intro z hz s hs
    have hxK : κ.symm z.1 ∈ κ.symm '' closedBall a₀ (ε₀ / 2) :=
      mem_image_of_mem _ (mem_closedBall.2 (mem_ball.1 hz.1.2).le)
    obtain ⟨e, hesrc, -, hexpe, -, -, hdist⟩ := hN _ hxK
    set v : TangentSpace I (κ.symm z.1) := mfderiv 𝓘(ℝ, E) I κ.symm z.1 (L z) with hv
    have hqv : q z = g.inner (κ.symm z.1) v v := rfl
    have hin : g.inner (κ.symm z.1) (s • v) (s • v) = s ^ 2 * q z := by
      rw [hqv]
      exact inner_smul_self_smul g (κ.symm z.1) s v
    have hqlt : q z < ρ ^ 2 := hz.2
    have hq0' : 0 ≤ q z := g.inner_self_nonneg' _ v
    have hse : s • v ∈ e.source := by
      rw [hesrc]
      change g.inner (κ.symm z.1) (s • v) (s • v) < ρ ^ 2
      rw [hin]
      have hs2 : s ^ 2 ≤ 1 := by nlinarith [hs.1, hs.2]
      nlinarith
    have hd := hdist _ hse
    rw [(hexpe _ hse).2] at hd
    rw [hd, hin, Real.sqrt_mul (sq_nonneg s), Real.sqrt_sq hs.1]
  have hdxy : ∀ z ∈ W', Real.sqrt (q z) = dist (κ.symm z.1) (κ.symm z.2) := by
    intro z hz
    have h := hdists z hz 1 ⟨zero_le_one, le_rfl⟩
    rw [one_mul] at h
    rw [← h, ← hexp z (hW'W hz)]
    exact congrArg (fun w : TangentSpace I (κ.symm z.1) =>
      dist (κ.symm z.1) (g.expMap (⟨κ.symm z.1, w⟩ : TangentBundle I M)))
      (one_smul ℝ (mfderiv 𝓘(ℝ, E) I κ.symm z.1 (L z)))
  have hflow : ∀ z ∈ W', ∀ s : ℝ, g.expMap (⟨κ.symm z.1,
      s • mfderiv 𝓘(ℝ, E) I κ.symm z.1 (L z)⟩ : TangentBundle I M) =
        (g.geodesicFlow (⟨κ.symm z.1, mfderiv 𝓘(ℝ, E) I κ.symm z.1 (L z)⟩ : TangentBundle I M)
          s).proj := fun z _ s =>
    g.expMap_smul_eq_proj_geodesicFlow hr1 _ _ s (hmem _ _)
  refine ⟨W', hW'o, hw₀', fun z hz => hsub (hW'W hz), L,
    hLc.mono hW'W, hL0, hLd, fun z hz => hdiag z (hW'W hz), fun z hz => hexp z (hW'W hz),
    fun z hz => hsrc z (hW'W hz), fun s hs => (hJc s hs).mono hW'W, hJd, hflow,
    fun z hz => hdxy z hz, fun z hz s hs => ⟨?_, ?_⟩⟩
  · rw [hdists z hz s hs, hdxy z hz]
  · set d := dist (κ.symm z.1) (κ.symm z.2) with hd
    set v : TangentSpace I (κ.symm z.1) := mfderiv 𝓘(ℝ, E) I κ.symm z.1 (L z) with hv
    set P : TangentBundle I M := ⟨κ.symm z.1, v⟩ with hP
    have h1 : dist (κ.symm z.1) (g.expMap (⟨κ.symm z.1, s • v⟩ : TangentBundle I M)) = s * d := by
      rw [hdists z hz s hs, hdxy z hz]
    have hy : (g.geodesicFlow P 1).proj = κ.symm z.2 := by
      rw [← hflow z hz 1, ← hexp z (hW'W hz)]
      exact congrArg (fun w : TangentSpace I (κ.symm z.1) => g.expMap (⟨κ.symm z.1, w⟩ :
        TangentBundle I M)) (one_smul ℝ v)
    have hup : dist (g.expMap (⟨κ.symm z.1, s • v⟩ : TangentBundle I M)) (κ.symm z.2) ≤
        (1 - s) * d := by
      rw [hflow z hz s, ← hy]
      have h := g.dist_proj_geodesicFlow_le hr1 hnorm (p := P) (s := s) (t := 1)
        (fun τ _ => hmem P τ)
      have hsq : Real.sqrt (g.inner P.proj P.snd P.snd) = d := hdxy z hz
      rw [hsq, abs_of_nonneg (sub_nonneg.2 hs.2)] at h
      linarith
    have hlow := dist_triangle (κ.symm z.1) (g.expMap (⟨κ.symm z.1, s • v⟩ : TangentBundle I M))
      (κ.symm z.2)
    rw [h1] at hlow
    linarith

end Bundle.ContMDiffRiemannianMetric
