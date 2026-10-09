import DifferentialGeometry.Geometry.Comparison.FiniteSoul.TotallyConvex
import DifferentialGeometry.Geometry.Comparison.FiniteSoul.BilinearSeparation
import DifferentialGeometry.Geometry.Exponential.FiniteMetric.ShortInterpolation
import DifferentialGeometry.Geometry.Exponential.FiniteMetric.HopfRinow
import DifferentialGeometry.Geometry.Comparison.FiniteMetric.FirstVariation
import DifferentialGeometry.Geometry.Collapse.DistanceSmoothing.Finite.ChartMetric

/-!
# The separation lemma (S-SEP; replaces CG 1.4 / 1.7 tangent cones for LFR45.1)

`exists_unit_strict_outward_of_descent` (frozen interface): `φ` Lipschitz and convex along the
geodesic arcs inside a totally convex `C`; every direction of a compact nonempty set `K` of
`g_q`-unit vectors starts a short arc in `C` along which `φ` drops below `φ q`. Then one `g_q`-unit
vector has negative `g_q`-pairing with every direction of `K`.

Route (external review §3, disposition D5). If `0 ∈ conv K`, take a finite representation
`Σ wᵢ uᵢ = 0`. Along each of the finitely many arcs, convexity gives `φ(exp_q(t uᵢ)) ≤ φ q - κ t`
for `t ∈ [0, δ]`. Iterated short geodesic interpolations `J(x, y, μ)` (shared module
`ShortInterpolation`) produce `P_t ∈ C` with `φ(P_t) ≤ φ q - κ t` and chart derivative
`D(κ ∘ P)(0) = Σ wᵢ uᵢ = 0` (`D J_μ |(q, q) = (1 - μ) I ⊕ μ I`), so `d(P_t, q) = o(t)`, which
contradicts the Lipschitz bound. Hence `0 ∉ conv K`, and the `g_q`-nearest point of `conv K`
separates (`exists_neg_pairing_of_zero_notMem_convexHull`).
-/

set_option autoImplicit false

noncomputable section

open Bundle Manifold Set Filter Metric
open scoped Manifold ContDiff ENNReal Topology NNReal

namespace DifferentialGeometry.Geometry.FiniteSoul

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [NeZero (Module.finrank ℝ E)]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {M : Type*} [MetricSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [SigmaCompactSpace M]
  [RiemannianBundle (fun x : M => TangentSpace I x)] [IsRiemannianManifold I M]
  [CompleteSpace M]

attribute [-instance] DifferentialGeometry.Tensor0SBundle.tangentSpaceNormedAddCommGroup
  DifferentialGeometry.Tensor0SBundle.tangentSpaceNormedSpace

variable {r : ℕ∞}

omit [NeZero (Module.finrank ℝ E)] [SigmaCompactSpace M] in
/-- The chart reading at `q` of the radial geodesic `t ↦ exp_q (t u)` has derivative `u` at `0`. -/
theorem hasDerivAt_extChartAt_expMap_smul
    (g : ContMDiffRiemannianMetric I ((r : ℕ∞ω) + 1) E (TangentSpace I : M → Type _))
    (hr : 2 ≤ r)
    (hnorm : ∀ (x : M) (w : TangentSpace I x), ‖w‖ₑ = ENNReal.ofReal (Real.sqrt (g.inner x w w)))
    (q : M) (u : E) :
    HasDerivAt (fun t : ℝ => extChartAt I q (g.expMap (⟨q, t • u⟩ : TangentBundle I M))) u 0 := by
  have hr1 : 1 ≤ r := one_le_two.trans hr
  have hD : g.geodesicFlowDomain = univ :=
    Bundle.ContMDiffRiemannianMetric.geodesicFlowDomain_eq_univ g hr hnorm
  set P : TangentBundle I M := ⟨q, u⟩ with hP
  have hγ := g.hasMFDerivAt_geodesicFlow_proj hr1 (p := P) (t := 0) (by rw [hD]; exact mem_univ _)
  rw [g.geodesicFlow_zero hr1] at hγ
  have h := Bundle.ContMDiffRiemannianMetric.hasDerivAt_extChartAt_comp_of_hasMFDerivAt hγ
  have h0 : (g.geodesicFlow P 0).proj = q := by rw [g.geodesicFlow_zero hr1]
  rw [h0] at h
  refine h.congr_of_eventuallyEq (Eventually.of_forall fun t => ?_)
  exact congrArg (extChartAt I q)
    (g.expMap_smul_eq_proj_geodesicFlow hr1 q u t (by rw [hD]; exact mem_univ _))

omit [NeZero (Module.finrank ℝ E)] [SigmaCompactSpace M] in
/-- **S-SEP: the separation lemma.** Deviations from the frozen interface (recorded): the descent
times are typed as REAL numbers (the frozen text elaborates `δ` and `t` as natural numbers, see
`exists_unit_strict_outward_of_descent_nat`), and `q ∈ C` is dropped (it follows from the arcs). -/
theorem exists_unit_strict_outward_of_descent
    (g : ContMDiffRiemannianMetric I ((r : ℕ∞ω) + 1) E (TangentSpace I : M → Type _))
    (hr : 2 ≤ r)
    (hnorm : ∀ (x : M) (w : TangentSpace I x), ‖w‖ₑ = ENNReal.ofReal (Real.sqrt (g.inner x w w)))
    {C : Set M} (hconv : IsTotallyConvexFinite g C) {φ : M → ℝ} {L : ℝ≥0}
    (hφ : LipschitzWith L φ)
    (hφconv : ∀ (p : TangentBundle I M) (ℓ : ℝ), 0 ≤ ℓ →
      (∀ t ∈ Icc 0 ℓ, (g.geodesicFlow p t).proj ∈ C) →
        ConvexOn ℝ (Icc 0 ℓ) (fun t => φ (g.geodesicFlow p t).proj))
    {q : M} {K : Set E} (hKc : IsCompact K) (hKne : K.Nonempty)
    (hK : ∀ u ∈ K, g.inner q u u = 1 ∧ ∃ δ > (0 : ℝ),
      (∀ t ∈ Icc (0 : ℝ) δ, g.expMap (⟨q, t • u⟩ : TangentBundle I M) ∈ C) ∧
      ∀ t ∈ Ioc (0 : ℝ) δ, φ (g.expMap (⟨q, t • u⟩ : TangentBundle I M)) < φ q) :
    ∃ v : E, g.inner q v v = 1 ∧ ∀ u ∈ K, g.inner q v u < 0 := by
  classical
  have hr1 : 1 ≤ r := one_le_two.trans hr
  have hD : g.geodesicFlowDomain = univ :=
    Bundle.ContMDiffRiemannianMetric.geodesicFlowDomain_eq_univ g hr hnorm
  have hmem : ∀ (P : TangentBundle I M) (τ : ℝ), (P, τ) ∈ g.geodesicFlowDomain := fun P τ => by
    rw [hD]; exact mem_univ _
  have hflow : ∀ (x : M) (v : TangentSpace I x) (τ : ℝ),
      g.expMap (⟨x, τ • v⟩ : TangentBundle I M) =
        (g.geodesicFlow (⟨x, v⟩ : TangentBundle I M) τ).proj :=
    fun x v τ => g.expMap_smul_eq_proj_geodesicFlow hr1 x v τ (hmem _ _)
  have hflowE : ∀ (x : M) (v : E) (τ : ℝ),
      g.expMap (⟨x, τ • v⟩ : TangentBundle I M) =
        (g.geodesicFlow (⟨x, v⟩ : TangentBundle I M) τ).proj :=
    fun x v τ => g.expMap_smul_eq_proj_geodesicFlow hr1 x v τ (hmem _ _)
  suffices h0 : (0 : E) ∉ convexHull ℝ K from
    exists_neg_pairing_of_zero_notMem_convexHull (g.inner q) (fun u w => g.symm q u w)
      (fun u hu => g.pos q u hu) hKc hKne h0
  intro h0
  obtain ⟨ι, hι, w, u, hw0, hw1, huK, hsum⟩ := mem_convexHull_iff_exists_fintype.mp h0
  have hιne : Nonempty ι := by
    by_contra hne
    rw [not_nonempty_iff] at hne
    simp at hw1
  have hK' : ∀ i, ∃ δ > (0 : ℝ),
      (∀ t ∈ Icc (0 : ℝ) δ, g.expMap (⟨q, t • u i⟩ : TangentBundle I M) ∈ C) ∧
      ∀ t ∈ Ioc (0 : ℝ) δ, φ (g.expMap (⟨q, t • u i⟩ : TangentBundle I M)) < φ q :=
    fun i => (hK (u i) (huK i)).2
  choose δ hδ hδC hδφ using hK'
  -- linear descent along each arc
  set κi : ι → ℝ := fun i =>
    (φ q - φ (g.expMap (⟨q, δ i • u i⟩ : TangentBundle I M))) / δ i with hκi
  have hκi_def : ∀ i, κi i =
      (φ q - φ (g.expMap (⟨q, δ i • u i⟩ : TangentBundle I M))) / δ i := fun _ => rfl
  have hκipos : ∀ i, 0 < κi i := fun i =>
    div_pos (sub_pos.2 (hδφ i (δ i) ⟨hδ i, le_rfl⟩)) (hδ i)
  have hdesc : ∀ i, ∀ t ∈ Icc 0 (δ i),
      φ (g.expMap (⟨q, t • u i⟩ : TangentBundle I M)) ≤ φ q - κi i * t := by
    intro i t ht
    set p : TangentBundle I M := ⟨q, u i⟩ with hp
    have harc : ∀ τ ∈ Icc 0 (δ i), (g.geodesicFlow p τ).proj ∈ C := fun τ hτ => by
      have h := hδC i τ hτ
      rw [hflowE] at h
      exact h
    have hcv := hφconv p (δ i) (hδ i).le harc
    have hδ0 := hδ i
    have hab : (1 - t / δ i) + t / δ i = 1 := by ring
    have ha : 0 ≤ 1 - t / δ i := by
      rw [sub_nonneg, div_le_one hδ0]; exact ht.2
    have hb : 0 ≤ t / δ i := div_nonneg ht.1 hδ0.le
    have h := hcv.2 (left_mem_Icc.2 hδ0.le) (right_mem_Icc.2 hδ0.le) ha hb hab
    have hpt : (1 - t / δ i) • (0 : ℝ) + (t / δ i) • δ i = t := by
      simp only [smul_eq_mul, mul_zero, zero_add]
      field_simp
    rw [hpt] at h
    simp only [smul_eq_mul] at h
    have hq0 : (g.geodesicFlow p 0).proj = q := by rw [g.geodesicFlow_zero hr1]
    rw [hq0] at h
    have e1 := hflowE q (u i) t
    have e2 := hflowE q (u i) (δ i)
    rw [e1]
    have hrw : φ q - κi i * t = (1 - t / δ i) * φ q + t / δ i *
        φ (g.geodesicFlow p (δ i)).proj := by
      rw [hκi_def, e2]
      field_simp
      ring
    rw [hrw]
    exact h
  set κ₀ : ℝ := Finset.univ.inf' Finset.univ_nonempty κi with hκ₀
  have hκ₀pos : 0 < κ₀ := (Finset.lt_inf'_iff _).2 fun i _ => hκipos i
  have hκ₀le : ∀ i, κ₀ ≤ κi i := fun i => Finset.inf'_le _ (Finset.mem_univ i)
  set δ₀ : ℝ := Finset.univ.inf' Finset.univ_nonempty δ with hδ₀
  have hδ₀pos : 0 < δ₀ := (Finset.lt_inf'_iff _).2 fun i _ => hδ i
  have hδ₀le : ∀ i, δ₀ ≤ δ i := fun i => Finset.inf'_le _ (Finset.mem_univ i)
  -- the chart at `q`
  set κ := extChartAt I q with hκ
  set a₀ : E := κ q with ha₀
  have hqs : q ∈ κ.source := mem_extChartAt_source q
  -- the radial arcs
  set A : ι → ℝ → M := fun i t => g.expMap (⟨q, t • u i⟩ : TangentBundle I M) with hA
  have hA0 : ∀ i, A i 0 = q := fun i => by
    change g.expMap (⟨q, (0 : ℝ) • u i⟩ : TangentBundle I M) = q
    rw [hflowE, g.geodesicFlow_zero hr1]
  have hAder : ∀ i, HasDerivWithinAt (fun t => κ (A i t)) (u i) (Ici 0) 0 := fun i =>
    (hasDerivAt_extChartAt_expMap_smul g hr hnorm q (u i)).hasDerivWithinAt
  have hAcont : ∀ i, ContinuousAt (A i) 0 := by
    intro i
    have hγ := g.hasMFDerivAt_geodesicFlow_proj hr1 (p := ⟨q, u i⟩) (t := 0) (hmem _ _)
    refine hγ.continuousAt.congr (Eventually.of_forall fun t => ?_)
    exact (hflowE q (u i) t).symm
  have hAgood : ∀ i, ∃ t₀ > 0, ∀ t ∈ Icc 0 t₀, A i t ∈ C ∧ A i t ∈ κ.source ∧
      φ (A i t) ≤ φ q - κ₀ * t := by
    intro i
    have hev : ∀ᶠ t in 𝓝 (0 : ℝ), A i t ∈ κ.source :=
      (hAcont i).preimage_mem_nhds (by rw [hA0 i]; exact extChartAt_source_mem_nhds q)
    obtain ⟨ε, hε, hεs⟩ := Metric.mem_nhds_iff.mp hev
    refine ⟨min δ₀ (ε / 2), lt_min hδ₀pos (by positivity), fun t ht => ⟨?_, ?_, ?_⟩⟩
    · exact hδC i t ⟨ht.1, ht.2.trans ((min_le_left _ _).trans (hδ₀le i))⟩
    · apply hεs
      rw [mem_ball, Real.dist_eq, sub_zero, abs_of_nonneg ht.1]
      linarith [ht.2, min_le_right δ₀ (ε / 2)]
    · have h := hdesc i t ⟨ht.1, ht.2.trans ((min_le_left _ _).trans (hδ₀le i))⟩
      have : κ₀ * t ≤ κi i * t := mul_le_mul_of_nonneg_right (hκ₀le i) ht.1
      change φ (g.expMap (⟨q, t • u i⟩ : TangentBundle I M)) ≤ φ q - κ₀ * t
      linarith
  -- the short geodesic interpolation at `q`
  obtain ⟨WJ, hWJo, hw₀J, hWJsub, LJ, -, hL0, -, -, hexpJ, hsrcJ, -, hJd⟩ :=
    Bundle.ContMDiffRiemannianMetric.exists_shortInterpolation_chart g hr1 q
  -- the inductive construction
  have claim : ∀ s : Finset ι, 0 < ∑ i ∈ s, w i → ∃ P : ℝ → M, ∃ t₀ > 0,
      (∀ t ∈ Icc 0 t₀, P t ∈ C ∧ P t ∈ κ.source ∧ φ (P t) ≤ φ q - κ₀ * t) ∧ κ (P 0) = a₀ ∧
      HasDerivWithinAt (fun t => κ (P t)) ((∑ i ∈ s, w i)⁻¹ • ∑ i ∈ s, w i • u i) (Ici 0) 0 := by
    intro s
    induction s using Finset.induction_on with
    | empty => intro h; simp at h
    | insert j s hj ih =>
      intro hpos
      rw [Finset.sum_insert hj] at hpos ⊢
      rw [Finset.sum_insert hj]
      obtain ⟨t₂, ht₂, hgood₂⟩ := hAgood j
      have hsingle : ∃ P : ℝ → M, ∃ t₀ > 0,
          (∀ t ∈ Icc 0 t₀, P t ∈ C ∧ P t ∈ κ.source ∧ φ (P t) ≤ φ q - κ₀ * t) ∧ κ (P 0) = a₀ ∧
          HasDerivWithinAt (fun t => κ (P t)) (u j) (Ici 0) 0 :=
        ⟨A j, t₂, ht₂, hgood₂, by rw [hA0 j], hAder j⟩
      have hWs0 : 0 ≤ ∑ i ∈ s, w i := Finset.sum_nonneg fun i _ => hw0 i
      rcases eq_or_lt_of_le hWs0 with hWs | hWs
      · -- all weights of `s` vanish
        have hzero : ∀ i ∈ s, w i = 0 := (Finset.sum_eq_zero_iff_of_nonneg
          fun i _ => hw0 i).1 hWs.symm
        have hV : ∑ i ∈ s, w i • u i = 0 :=
          Finset.sum_eq_zero fun i hi => by rw [hzero i hi, zero_smul]
        rw [← hWs, add_zero] at hpos ⊢
        rw [hV, add_zero, smul_smul, inv_mul_cancel₀ hpos.ne', one_smul]
        exact hsingle
      rcases eq_or_lt_of_le (hw0 j) with hwj | hwj
      · rw [← hwj, zero_add, zero_smul, zero_add]
        exact ih hWs
      -- both parts carry weight: one interpolation step
      obtain ⟨P', t₁, ht₁, hgood₁, hP'0, hP'd⟩ := ih hWs
      set Ws := ∑ i ∈ s, w i with hWsdef
      set Vs := ∑ i ∈ s, w i • u i with hVsdef
      set μ : ℝ := w j / (w j + Ws) with hμ
      have hμ0 : 0 ≤ μ := div_nonneg (hw0 j) hpos.le
      have hμ1 : μ ≤ 1 := by rw [hμ, div_le_one hpos]; linarith
      set z : ℝ → E × E := fun t => (κ (P' t), κ (A j t)) with hz
      have hz0 : z 0 = (a₀, a₀) := by
        change ((κ (P' 0), κ (A j 0)) : E × E) = (a₀, a₀)
        rw [hP'0, hA0 j]
      have hzd : HasDerivWithinAt z ((Ws⁻¹ • Vs, u j) : E × E) (Ici 0) 0 :=
        hP'd.prodMk (hAder j)
      set Jμ : E × E → E := fun y => κ (g.expMap (⟨κ.symm y.1,
        μ • mfderiv 𝓘(ℝ, E) I κ.symm y.1 (LJ y)⟩ : TangentBundle I M)) with hJμ
      have hJμd : HasFDerivAt Jμ ((1 - μ) • ContinuousLinearMap.fst ℝ E E +
          μ • ContinuousLinearMap.snd ℝ E E) (z 0) := by
        rw [hz0]; exact hJd μ
      have hcomp := hJμd.comp_hasDerivWithinAt (0 : ℝ) hzd
      set P : ℝ → M := fun t => g.expMap (⟨κ.symm (z t).1,
        μ • mfderiv 𝓘(ℝ, E) I κ.symm (z t).1 (LJ (z t))⟩ : TangentBundle I M) with hPdef
      -- `z t ∈ WJ` for small `t`
      have hzW : z ⁻¹' WJ ∈ 𝓝[Ici 0] (0 : ℝ) :=
        hzd.continuousWithinAt.preimage_mem_nhdsWithin (by rw [hz0]; exact hWJo.mem_nhds hw₀J)
      obtain ⟨t₃, ht₃, hzW'⟩ := mem_nhdsGE_iff_exists_Icc_subset.mp hzW
      refine ⟨P, min t₁ (min t₂ t₃), lt_min ht₁ (lt_min ht₂ ht₃), fun t ht => ?_, ?_, ?_⟩
      · have ht1 : t ∈ Icc 0 t₁ := ⟨ht.1, ht.2.trans (min_le_left _ _)⟩
        have ht2 : t ∈ Icc 0 t₂ := ⟨ht.1, ht.2.trans ((min_le_right _ _).trans (min_le_left _ _))⟩
        have ht3 : t ∈ Icc 0 t₃ := ⟨ht.1, ht.2.trans ((min_le_right _ _).trans (min_le_right _ _))⟩
        obtain ⟨hP'C, hP's, hP'φ⟩ := hgood₁ t ht1
        obtain ⟨hAC, hAs, hAφ⟩ := hgood₂ t ht2
        have hzt : z t ∈ WJ := hzW' ht3
        have hx : κ.symm (z t).1 = P' t := κ.left_inv hP's
        set v : TangentSpace I (κ.symm (z t).1) :=
          mfderiv 𝓘(ℝ, E) I κ.symm (z t).1 (LJ (z t)) with hv
        set p : TangentBundle I M := ⟨κ.symm (z t).1, v⟩ with hp
        have hp0 : (g.geodesicFlow p 0).proj = P' t := by
          rw [g.geodesicFlow_zero hr1]; exact hx
        have hp1 : (g.geodesicFlow p 1).proj = A j t := by
          rw [← hflow, ← κ.left_inv hAs]
          have h := hexpJ (z t) hzt
          rw [← h]
          exact congrArg (fun y : TangentSpace I (κ.symm (z t).1) =>
            g.expMap (⟨κ.symm (z t).1, y⟩ : TangentBundle I M)) (one_smul ℝ v)
        have hpproj : p.proj ∈ C := by
          change κ.symm (z t).1 ∈ C
          rw [hx]; exact hP'C
        have harc : ∀ τ ∈ Icc (0 : ℝ) 1, (g.geodesicFlow p τ).proj ∈ C :=
          hconv p 1 zero_le_one hpproj (by rw [hp1]; exact hAC)
        have hPt : P t = (g.geodesicFlow p μ).proj := hflow _ v μ
        refine ⟨by rw [hPt]; exact harc μ ⟨hμ0, hμ1⟩, hsrcJ (z t) hzt μ ⟨hμ0, hμ1⟩, ?_⟩
        have hcv := hφconv p 1 zero_le_one harc
        have h := hcv.2 (left_mem_Icc.2 zero_le_one) (right_mem_Icc.2 zero_le_one)
          (sub_nonneg.2 hμ1) hμ0 (by ring)
        have hpt : (1 - μ) • (0 : ℝ) + μ • (1 : ℝ) = μ := by simp
        rw [hpt] at h
        simp only [smul_eq_mul] at h
        rw [hp0, hp1] at h
        rw [hPt]
        have h1 := mul_le_mul_of_nonneg_left hP'φ (sub_nonneg.2 hμ1)
        have h2 := mul_le_mul_of_nonneg_left hAφ hμ0
        linarith
      · change Jμ (z 0) = a₀
        rw [hz0]
        change κ (g.expMap (⟨κ.symm a₀,
          μ • mfderiv 𝓘(ℝ, E) I κ.symm a₀ (LJ (a₀, a₀))⟩ : TangentBundle I M)) = a₀
        have hv0 : (⟨κ.symm a₀, μ • mfderiv 𝓘(ℝ, E) I κ.symm a₀ (LJ (a₀, a₀))⟩ :
            TangentBundle I M) = ⟨κ.symm a₀, 0⟩ := by
          congr 1
          have hm0 : mfderiv 𝓘(ℝ, E) I κ.symm a₀ (LJ (a₀, a₀)) = 0 := by
            rw [hL0]; exact map_zero _
          exact (congrArg (fun y : TangentSpace I (κ.symm a₀) => μ • y) hm0).trans (smul_zero μ)
        rw [hv0, g.expMap_zero hr1, κ.left_inv hqs]
      · have hval : ((1 - μ) • ContinuousLinearMap.fst ℝ E E + μ • ContinuousLinearMap.snd ℝ E E)
            ((Ws⁻¹ • Vs, u j) : E × E) = (w j + Ws)⁻¹ • (w j • u j + Vs) := by
          change (1 - μ) • (Ws⁻¹ • Vs) + μ • u j = (w j + Ws)⁻¹ • (w j • u j + Vs)
          have hc1 : (1 - μ) * Ws⁻¹ = (w j + Ws)⁻¹ := by
            rw [hμ]
            field_simp
            ring
          have hc2 : μ = (w j + Ws)⁻¹ * w j := by
            rw [hμ]
            field_simp
          calc (1 - μ) • (Ws⁻¹ • Vs) + μ • u j =
              (w j + Ws)⁻¹ • Vs + (w j + Ws)⁻¹ • (w j • u j) := by
                rw [smul_smul, hc1, hc2, mul_smul]
            _ = (w j + Ws)⁻¹ • (w j • u j + Vs) := by rw [smul_add, add_comm]
        rw [← hval]
        exact hcomp
  -- the contradiction
  obtain ⟨P, t₀, ht₀, hgood, hP0, hPd⟩ := claim Finset.univ (by rw [hw1]; exact one_pos)
  rw [hw1, hsum, smul_zero] at hPd
  obtain ⟨ρ, hρ, -, hlip⟩ := DifferentialGeometry.Geometry.Collapse.exists_ball_dist_chart_symm_le_finite
    g hnorm q (κ := 2) one_lt_two
  set cN : ℝ := Real.sqrt ‖DifferentialGeometry.Geometry.Collapse.finiteMetricFormAt g q‖ with hcN
  have hcN0 : 0 ≤ cN := Real.sqrt_nonneg _
  set ε : ℝ := κ₀ / (4 * ((L : ℝ) + 1) * (2 * cN + 1)) with hε
  have hε0 : 0 < ε := by positivity
  have ho := hPd.isLittleO
  have hev1 : ∀ᶠ t in 𝓝[Ici 0] (0 : ℝ), ‖κ (P t) - κ (P 0) - (t - 0) • (0 : E)‖ ≤ ε * ‖t - 0‖ :=
    ho.def hε0
  have hev2 : ∀ᶠ t in 𝓝[Ici 0] (0 : ℝ), κ (P t) ∈ ball a₀ ρ :=
    hPd.continuousWithinAt.preimage_mem_nhdsWithin (by rw [hP0]; exact ball_mem_nhds a₀ hρ)
  have hev3 : ∀ᶠ t in 𝓝[Ici 0] (0 : ℝ), t ≤ t₀ :=
    nhdsWithin_le_nhds (eventually_le_nhds ht₀)
  have hev : ∀ᶠ t in 𝓝[>] (0 : ℝ), (‖κ (P t) - κ (P 0) - (t - 0) • (0 : E)‖ ≤ ε * ‖t - 0‖ ∧
      κ (P t) ∈ ball a₀ ρ ∧ t ≤ t₀) ∧ 0 < t :=
    ((hev1.and (hev2.and hev3)).filter_mono (nhdsWithin_mono _ Ioi_subset_Ici_self)).and
      self_mem_nhdsWithin
  obtain ⟨t, ⟨h1, h2, h3⟩, htpos⟩ := hev.exists
  rw [hP0, sub_zero, smul_zero, sub_zero, Real.norm_eq_abs, abs_of_pos htpos] at h1
  obtain ⟨-, hPs, hPφ⟩ := hgood t ⟨htpos.le, h3⟩
  have hdist : dist (P t) q ≤ 2 * cN * (ε * t) := by
    have h := hlip _ h2 _ (mem_ball_self hρ)
    rw [κ.left_inv hPs, κ.left_inv hqs] at h
    have hN := DifferentialGeometry.Geometry.Collapse.finiteMetricSeminormAt_le_mul_norm g q
      (κ (P t) - a₀)
    calc dist (P t) q ≤ 2 * DifferentialGeometry.Geometry.Collapse.finiteMetricSeminormAt g q
          (κ (P t) - a₀) := h
      _ ≤ 2 * (cN * ‖κ (P t) - a₀‖) := by gcongr
      _ ≤ 2 * cN * (ε * t) := by
          rw [← mul_assoc]; exact mul_le_mul_of_nonneg_left h1 (by positivity)
  have hφlow : φ q - L * dist (P t) q ≤ φ (P t) := by
    have := hφ.dist_le_mul (P t) q
    rw [Real.dist_eq] at this
    linarith [neg_abs_le (φ (P t) - φ q)]
  have hkey : κ₀ * t ≤ L * (2 * cN * (ε * t)) := by
    have := mul_le_mul_of_nonneg_left hdist (NNReal.coe_nonneg L)
    linarith
  have hε' : (L : ℝ) * (2 * cN * ε) < κ₀ := by
    rw [hε]
    have hL0 : (0 : ℝ) ≤ L := NNReal.coe_nonneg L
    have hden : 0 < 4 * ((L : ℝ) + 1) * (2 * cN + 1) := by positivity
    rw [show (L : ℝ) * (2 * cN * (κ₀ / (4 * ((L : ℝ) + 1) * (2 * cN + 1)))) =
      κ₀ * ((L : ℝ) * (2 * cN) / (4 * ((L : ℝ) + 1) * (2 * cN + 1))) by field_simp]
    have hfrac : (L : ℝ) * (2 * cN) / (4 * ((L : ℝ) + 1) * (2 * cN + 1)) < 1 := by
      rw [div_lt_one hden]
      nlinarith
    calc κ₀ * ((L : ℝ) * (2 * cN) / (4 * ((L : ℝ) + 1) * (2 * cN + 1))) < κ₀ * 1 :=
          mul_lt_mul_of_pos_left hfrac hκ₀pos
      _ = κ₀ := mul_one κ₀
  have : κ₀ * t < κ₀ * t := by
    calc κ₀ * t ≤ L * (2 * cN * (ε * t)) := hkey
      _ = (L * (2 * cN * ε)) * t := by ring
      _ < κ₀ * t := mul_lt_mul_of_pos_right hε' htpos
  exact lt_irrefl _ this

omit [NeZero (Module.finrank ℝ E)] [SigmaCompactSpace M] in
/-- The frozen interface text of S-SEP elaborates with NATURAL descent times `δ, t : ℕ` (the
numerals `0` in `δ > 0`, `Icc 0 δ` default to `ℕ`, and `t • u` is then `ℕ`-scalar multiplication).
This literal form is also true: the arc `[0, 1]` lies in `C` by total convexity, and convexity of `φ`
turns the drop at time `1` into a drop on `(0, 1]`; it is reduced to the real form. -/
theorem exists_unit_strict_outward_of_descent_nat
    (g : ContMDiffRiemannianMetric I ((r : ℕ∞ω) + 1) E (TangentSpace I : M → Type _))
    (hr : 2 ≤ r)
    (hnorm : ∀ (x : M) (w : TangentSpace I x), ‖w‖ₑ = ENNReal.ofReal (Real.sqrt (g.inner x w w)))
    {C : Set M} (hconv : IsTotallyConvexFinite g C) {φ : M → ℝ} {L : ℝ≥0}
    (hφ : LipschitzWith L φ)
    (hφconv : ∀ (p : TangentBundle I M) (ℓ : ℝ), 0 ≤ ℓ →
      (∀ t ∈ Icc 0 ℓ, (g.geodesicFlow p t).proj ∈ C) →
        ConvexOn ℝ (Icc 0 ℓ) (fun t => φ (g.geodesicFlow p t).proj))
    {q : M} {K : Set E} (hKc : IsCompact K) (hKne : K.Nonempty)
    (hK : ∀ u ∈ K, g.inner q u u = 1 ∧ ∃ δ > 0,
      (∀ t ∈ Icc 0 δ, g.expMap (⟨q, t • u⟩ : TangentBundle I M) ∈ C) ∧
      ∀ t ∈ Ioc 0 δ, φ (g.expMap (⟨q, t • u⟩ : TangentBundle I M)) < φ q) :
    ∃ v : E, g.inner q v v = 1 ∧ ∀ u ∈ K, g.inner q v u < 0 := by
  have hr1 : 1 ≤ r := one_le_two.trans hr
  have hD : g.geodesicFlowDomain = univ :=
    Bundle.ContMDiffRiemannianMetric.geodesicFlowDomain_eq_univ g hr hnorm
  have hflowE : ∀ (x : M) (v : E) (τ : ℝ),
      g.expMap (⟨x, τ • v⟩ : TangentBundle I M) =
        (g.geodesicFlow (⟨x, v⟩ : TangentBundle I M) τ).proj :=
    fun x v τ => g.expMap_smul_eq_proj_geodesicFlow hr1 x v τ (by rw [hD]; exact mem_univ _)
  refine exists_unit_strict_outward_of_descent g hr hnorm hconv hφ hφconv hKc hKne
    fun u hu => ⟨(hK u hu).1, ?_⟩
  obtain ⟨δ, hδ, hC, hφδ⟩ := (hK u hu).2
  set p : TangentBundle I M := ⟨q, u⟩ with hp
  have h0 : (g.geodesicFlow p 0).proj = q := by rw [g.geodesicFlow_zero hr1]
  have hq : g.expMap (⟨q, (0 : ℕ) • u⟩ : TangentBundle I M) = q := by
    rw [zero_smul]
    exact g.expMap_zero hr1 q
  have h1 : (g.geodesicFlow p 1).proj = g.expMap (⟨q, (1 : ℕ) • u⟩ : TangentBundle I M) := by
    rw [← hflowE q u 1, one_smul, one_smul]
  have hδ1 : (1 : ℕ) ≤ δ := hδ
  have harc : ∀ τ ∈ Icc (0 : ℝ) 1, (g.geodesicFlow p τ).proj ∈ C := by
    refine hconv p 1 zero_le_one ?_ ?_
    · change q ∈ C
      rw [← hq]
      exact hC 0 ⟨le_rfl, Nat.zero_le δ⟩
    · rw [h1]
      exact hC 1 ⟨Nat.zero_le 1, hδ1⟩
  have hdrop : φ (g.geodesicFlow p 1).proj < φ q := by
    rw [h1]
    exact hφδ 1 ⟨Nat.one_pos, hδ1⟩
  refine ⟨1, one_pos, fun t ht => ?_, fun t ht => ?_⟩
  · rw [hflowE]
    exact harc t ht
  · rw [hflowE]
    have hcv := hφconv p 1 zero_le_one harc
    have h := hcv.2 (left_mem_Icc.2 zero_le_one) (right_mem_Icc.2 zero_le_one)
      (sub_nonneg.2 ht.2) ht.1.le (by ring)
    have hpt : (1 - t) • (0 : ℝ) + t • (1 : ℝ) = t := by simp
    rw [hpt] at h
    simp only [smul_eq_mul] at h
    rw [h0] at h
    have := mul_lt_mul_of_pos_left hdrop ht.1
    linarith

/-- The frozen interface text of S-SEP, verbatim (it elaborates with natural `δ, t`). -/
example
    (g : ContMDiffRiemannianMetric I ((r : ℕ∞ω) + 1) E (TangentSpace I : M → Type _))
    (hr : 2 ≤ r)
    (hnorm : ∀ (x : M) (w : TangentSpace I x), ‖w‖ₑ = ENNReal.ofReal (Real.sqrt (g.inner x w w)))
    {C : Set M} (hconv : IsTotallyConvexFinite g C) {φ : M → ℝ} {L : ℝ≥0}
    (hφ : LipschitzWith L φ)
    (hφconv : ∀ (p : TangentBundle I M) (ℓ : ℝ), 0 ≤ ℓ →
      (∀ t ∈ Icc 0 ℓ, (g.geodesicFlow p t).proj ∈ C) →
        ConvexOn ℝ (Icc 0 ℓ) (fun t => φ (g.geodesicFlow p t).proj))
    {q : M} (_hq : q ∈ C) {K : Set E} (hKc : IsCompact K) (hKne : K.Nonempty)
    (hK : ∀ u ∈ K, g.inner q u u = 1 ∧ ∃ δ > 0,
      (∀ t ∈ Icc 0 δ, g.expMap (⟨q, t • u⟩ : TangentBundle I M) ∈ C) ∧
      ∀ t ∈ Ioc 0 δ, φ (g.expMap (⟨q, t • u⟩ : TangentBundle I M)) < φ q) :
    ∃ v : E, g.inner q v v = 1 ∧ ∀ u ∈ K, g.inner q v u < 0 :=
  exists_unit_strict_outward_of_descent_nat g hr hnorm hconv hφ hφconv hKc hKne hK

end DifferentialGeometry.Geometry.FiniteSoul
