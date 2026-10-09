import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.StandardSolution.InitialGeodesicArc
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.StandardSolution.CarrierJoinCost
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.LGeometry.ReducedLength.Minimum.DimensionBound
import DifferentialGeometry.Geometry.Flow.RicciFlow.Estimates.MetricComparison
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.LGeometry.Action.Regularized.Length

set_option autoImplicit false

noncomputable section

open Bundle Manifold Set MeasureTheory DifferentialGeometry
open DifferentialGeometry.Tensor0SBundle
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Geometry.Riemannian
open DifferentialGeometry.PDE.RicciFlow
open DifferentialGeometry.PDE.RicciFlow.Perelman
open scoped ContDiff Manifold Topology ENNReal

namespace DifferentialGeometry.PDE.RicciFlow

private theorem initialFan_early_algebra
    (Λ Q r b C : ℝ) (hΛ : 0 ≤ Λ) (hQ : 0 ≤ Q)
    (hr : 0 ≤ r) (hb : 0 < b) (hrb : r ≤ b) (hbC : b ^ 2 ≤ C) :
    (Λ * r ^ 2 / (2 * b) + (2 / 3 : ℝ) * Q * b ^ 3) / (2 * b) ≤
      Λ / 4 + Q * C / 3 := by
  have hsq : r ^ 2 ≤ b ^ 2 := (sq_le_sq₀ hr hb.le).mpr hrb
  have hkin : Λ * r ^ 2 / (2 * b) ≤ Λ * b / 2 := by
    apply (div_le_iff₀ (by positivity : 0 < 2 * b)).mpr
    nlinarith only [mul_le_mul_of_nonneg_left hsq hΛ]
  calc
    (Λ * r ^ 2 / (2 * b) + (2 / 3 : ℝ) * Q * b ^ 3) / (2 * b) ≤
        (Λ * b / 2 + (2 / 3 : ℝ) * Q * b ^ 3) / (2 * b) :=
      div_le_div_of_nonneg_right (add_le_add hkin le_rfl) (by positivity)
    _ = Λ / 4 + Q * b ^ 2 / 3 := by field_simp [hb.ne']; ring
    _ ≤ Λ / 4 + Q * C / 3 := by
      linarith only [mul_le_mul_of_nonneg_left hbC hQ]

private theorem initialFan_late_algebra
    (n Λ Q r a b δ : ℝ) (hn : 0 ≤ n) (hΛ : 0 ≤ Λ) (hQ : 0 ≤ Q)
    (ha : 0 < a) (hab : a < b) (hδ : 0 < δ) (hδeq : δ = b ^ 2 - a ^ 2) :
    (n * a + (Λ * r ^ 2 / (2 * (b - a)) +
      (2 / 3 : ℝ) * Q * (b ^ 3 - a ^ 3))) / (2 * b) ≤
      n / 2 + Λ * r ^ 2 / (2 * δ) + Q * δ := by
  have hb : 0 < b := ha.trans hab
  have hgap : 0 < b - a := sub_pos.mpr hab
  have hkin0 : 0 ≤ Λ * r ^ 2 := mul_nonneg hΛ (sq_nonneg r)
  have hden : δ ≤ 2 * b * (b - a) := by
    rw [hδeq]
    nlinarith only [sq_nonneg (b - a)]
  have hkin : Λ * r ^ 2 / (2 * (b - a)) ≤ Λ * r ^ 2 * b / δ := by
    apply (div_le_div_iff₀ (by positivity : 0 < 2 * (b - a)) hδ).mpr
    nlinarith only [mul_le_mul_of_nonneg_left hden hkin0]
  have habsq : a ^ 2 ≤ b ^ 2 := (sq_le_sq₀ ha.le hb.le).mpr hab.le
  have habmul : a * b ≤ b ^ 2 := by
    nlinarith only [mul_le_mul_of_nonneg_right hab.le hb.le]
  have hcube : b ^ 3 - a ^ 3 ≤ 3 * b * δ := by
    calc
      b ^ 3 - a ^ 3 = (b - a) * (b ^ 2 + a * b + a ^ 2) := by ring
      _ ≤ (b - a) * (3 * b ^ 2) := by
        apply mul_le_mul_of_nonneg_left _ hgap.le
        linarith only [habsq, habmul]
      _ ≤ 3 * b * δ := by
        rw [hδeq]
        nlinarith only [mul_nonneg (mul_nonneg (by norm_num : (0 : ℝ) ≤ 3) hb.le)
          (mul_nonneg ha.le hgap.le)]
  have hpot : (2 / 3 : ℝ) * Q * (b ^ 3 - a ^ 3) ≤ 2 * Q * b * δ := by
    nlinarith only [mul_le_mul_of_nonneg_left hcube
      (mul_nonneg (by norm_num : (0 : ℝ) ≤ 2 / 3) hQ)]
  apply (div_le_iff₀ (by positivity : 0 < 2 * b)).mpr
  calc
    n * a + (Λ * r ^ 2 / (2 * (b - a)) +
        (2 / 3 : ℝ) * Q * (b ^ 3 - a ^ 3)) ≤
        n * b + (Λ * r ^ 2 * b / δ + 2 * Q * b * δ) :=
      add_le_add (mul_le_mul_of_nonneg_left hab.le hn) (add_le_add hkin hpot)
    _ = (n / 2 + Λ * r ^ 2 / (2 * δ) + Q * δ) * (2 * b) := by
      field_simp [hδ.ne']
      ring

variable {E H M : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [NeZero (Module.finrank ℝ E)]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  [PseudoMetricSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [T2Space M] [T2Space (TangentBundle I M)] [SigmaCompactSpace M]
  {D : RealTimeInterval}

private local instance : CompleteSpace E := FiniteDimensional.complete ℝ E

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
theorem redLength_initial_ball_early
    (S : SolutionOn (I := I) (M := M) D) (hS : IsSolutionOn S)
    (T : ℝ) (hT : 0 < T) (K : ℝ)
    (hsmall : T ≤ compactCurvatureControlTime (Module.finrank ℝ E) K)
    (hcomplete : RiemannianMetricComplete (I := I) (S.base.metric 0))
    (hslab : Icc (0 : ℝ) T ⊆ D.carrier)
    (hregular : Ioo (0 : ℝ) T ⊆ D.regular)
    (hbounded : ∃ B : ℝ, ∀ t ∈ Icc (0 : ℝ) T, ∀ z : M,
      normSq0S (I := I) (S.base.metric t) z 4 (S.base.rm04 t z) ≤ B)
    (hinit : ∀ z : M,
      normSq0S (I := I) (S.base.metric 0) z 4 (S.base.rm04 0 z) ≤ K ^ 2)
    (x : M) (r : ℝ) (hr : 0 < r) (y : M)
    (hy : riemannianEDistOf (I := I) (S.base.metric 0) x y <
      ENNReal.ofReal (min r (Real.sqrt T))) :
    redLength S T x y T ≤
      Real.exp (2 * ((Module.finrank ℝ E : ℝ) ^ 2 * Real.sqrt (2 * K ^ 2 + 1)) *
        compactCurvatureControlTime (Module.finrank ℝ E) K) / 4 +
      ((Module.finrank ℝ E : ℝ) ^ 2 * Real.sqrt (2 * K ^ 2 + 1)) *
        compactCurvatureControlTime (Module.finrank ℝ E) K / 3 := by
  let C := compactCurvatureControlTime (Module.finrank ℝ E) K
  let Q := (Module.finrank ℝ E : ℝ) ^ 2 * Real.sqrt (2 * K ^ 2 + 1)
  let Λ := Real.exp (2 * Q * C)
  let b := Real.sqrt T
  let R := min r b
  have hb : 0 < b := Real.sqrt_pos.mpr hT
  have hb2 : b ^ 2 = T := Real.sq_sqrt hT.le
  have hR : 0 < R := lt_min hr hb
  have hQ : 0 ≤ Q := mul_nonneg (sq_nonneg _) (Real.sqrt_nonneg _)
  obtain ⟨beta, hbeta, hbeta0, hbetab, hact⟩ :=
    exists_initial_geodesic_arc_action_le S hS T hT.le K hcomplete hslab hregular
      hbounded hinit x y R hR hy 0 b le_rfl hb hb2.le (by simpa using hsmall)
  have hact' : lRegularizedAction S T beta 0 b ≤
      Λ * R ^ 2 / (2 * b) + (2 / 3 : ℝ) * Q * b ^ 3 := by
    simpa only [sub_zero, zero_pow (by norm_num : 3 ≠ 0)] using hact
  have hback : ∀ s ∈ Icc (0 : ℝ) b, T - s ^ 2 ∈ D.carrier := by
    intro s hs
    have hs2 : s ^ 2 ≤ b ^ 2 := (sq_le_sq₀ hs.1 hb.le).mpr hs.2
    apply hslab
    exact ⟨by linarith only [hs2, hb2], sub_le_self T (sq_nonneg s)⟩
  obtain ⟨B, hB⟩ := hbounded
  have hRm : ∀ t ∈ Icc (T - b ^ 2) T, ∀ z : M,
      normSq0S (I := I) (S.base.metric t) z 4 (S.base.rm04 t z) ≤ B := by
    simpa only [hb2, sub_self] using hB
  have hcostSet := lCost_competitors_bddBelow_of_rm_on_carrier
    S hS B T b hb.le x y hback hRm
  rw [hb2] at hcostSet
  have hcost : lCost S T x y T ≤ lRegularizedAction S T beta 0 b := by
    unfold lCost
    apply csInf_le hcostSet
    refine ⟨beta, hbeta, hbeta0, hbetab, ?_⟩
    exact lLength_squareRootReparametrization_eq_lRegularizedAction (I := I) S T beta T hT.le
  change lCost S T x y T / (2 * b) ≤ Λ / 4 + Q * C / 3
  exact (div_le_div_of_nonneg_right (hcost.trans hact') (by positivity)).trans
    (initialFan_early_algebra Λ Q R b C (Real.exp_pos _).le hQ hR.le hb
      (min_le_right _ _) (by simpa only [hb2] using hsmall))

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
theorem exists_redLength_initial_ball_late [ConnectedSpace M]
    (S : SolutionOn (I := I) (M := M) D) (hS : IsSolutionOn S)
    (T K : ℝ)
    (hlate : compactCurvatureControlTime (Module.finrank ℝ E) K ≤ T)
    (hcomplete : RiemannianMetricComplete (I := I) (S.base.metric 0))
    (hslab : Icc (0 : ℝ) T ⊆ D.carrier)
    (hregular : Ioc (0 : ℝ) T ⊆ D.regular)
    (hbounded : ∃ B : ℝ, ∀ t ∈ Icc (0 : ℝ) T, ∀ z : M,
      normSq0S (I := I) (S.base.metric t) z 4 (S.base.rm04 t z) ≤ B)
    (hinit : ∀ z : M,
      normSq0S (I := I) (S.base.metric 0) z 4 (S.base.rm04 0 z) ≤ K ^ 2)
    (x : M) :
    ∃ q : M, ∀ r : ℝ, 0 < r → ∀ y : M,
      riemannianEDistOf (I := I) (S.base.metric 0) q y < ENNReal.ofReal r →
      redLength S T x y T ≤ (Module.finrank ℝ E : ℝ) / 2 +
        Real.exp (2 * ((Module.finrank ℝ E : ℝ) ^ 2 * Real.sqrt (2 * K ^ 2 + 1)) *
          compactCurvatureControlTime (Module.finrank ℝ E) K) * r ^ 2 /
          (2 * (compactCurvatureControlTime (Module.finrank ℝ E) K / 2)) +
        ((Module.finrank ℝ E : ℝ) ^ 2 * Real.sqrt (2 * K ^ 2 + 1)) *
          (compactCurvatureControlTime (Module.finrank ℝ E) K / 2) := by
  let C := compactCurvatureControlTime (Module.finrank ℝ E) K
  let δ := C / 2
  let Q := (Module.finrank ℝ E : ℝ) ^ 2 * Real.sqrt (2 * K ^ 2 + 1)
  let Λ := Real.exp (2 * Q * C)
  let tau := T - δ
  let sigma := T - δ / 2
  have hC : 0 < C := compactCurvatureControlTime_pos _ _
  have hδ : 0 < δ := half_pos hC
  have hT : 0 < T := hC.trans_le hlate
  have htau : 0 < tau := by dsimp only [tau, δ]; linarith only [hlate, hC]
  have htausigma : tau < sigma := by dsimp only [tau, sigma]; linarith only [hδ]
  have hQ : 0 ≤ Q := mul_nonneg (sq_nonneg _) (Real.sqrt_nonneg _)
  obtain ⟨B, hB⟩ := hbounded
  have hRic : ∀ t ∈ Icc (0 : ℝ) T, ∀ z : M, ∀ v : TangentSpace I z,
      |ricciTensor (I := I) (S.base.metric t) z v v| ≤
        ((Module.finrank ℝ E : ℝ) ^ 2 * Real.sqrt B) *
          (S.base.metric t).inner z v v :=
    fun t ht z v ↦ ricci_quadratic_form_bound_of_solution_curvature_bound
      (I := I) S z v (hB t ht z)
  have hcompleteT : RiemannianMetricComplete (I := I) (S.base.metric T) :=
    complete_of_ricBound S hS hslab hregular
      (mul_nonneg (sq_nonneg _) (Real.sqrt_nonneg B)) hRic hcomplete ⟨hT.le, le_rfl⟩
  have hregSigma : Icc (T - sigma) T ⊆ D.regular := by
    intro t ht
    apply hregular
    refine ⟨?_, ht.2⟩
    dsimp only [sigma] at ht
    linarith only [ht.1, hδ]
  have hRmSigma : ∀ t ∈ Icc (T - sigma) T, ∀ z : M,
      normSq0S (I := I) (S.base.metric t) z 4 (S.base.rm04 t z) ≤ B := by
    intro t ht z
    apply hB t ⟨?_, ht.2⟩ z
    dsimp only [sigma] at ht
    linarith only [ht.1, hδ]
  obtain ⟨q0, hq0⟩ := exists_redLen_le S hS B T sigma tau hcompleteT
    htau htausigma hregSigma hRmSigma x
  have hsub : Icc (T - tau) T ⊆ Icc (T - sigma) T := by
    intro t ht
    exact ⟨(sub_le_sub_left htausigma.le T).trans ht.1, ht.2⟩
  obtain ⟨q, Z, hmin, hend, _hval, hminimum⟩ :=
    exists_redMin_vec S hS B T hcompleteT tau htau
      (hsub.trans hregSigma) (fun t ht z ↦ hRmSigma t (hsub ht) z) x
  have hq : redLength S T x q tau ≤ (Module.finrank ℝ E : ℝ) / 2 :=
    (hminimum q0).trans hq0
  let a := Real.sqrt tau
  let b := Real.sqrt T
  let alpha := lRegularizedCurve S T x Z
  have ha : 0 < a := Real.sqrt_pos.mpr htau
  have hb : 0 < b := Real.sqrt_pos.mpr hT
  have ha2 : a ^ 2 = tau := Real.sq_sqrt htau.le
  have hb2 : b ^ 2 = T := Real.sq_sqrt hT.le
  have hab : a < b := by
    apply (sq_lt_sq₀ ha.le hb.le).mp
    rw [ha2, hb2]
    dsimp only [tau]
    linarith only [hδ]
  have hδeq : δ = b ^ 2 - a ^ 2 := by rw [ha2, hb2]; dsimp only [tau]; ring
  have hminSpec := (mem_lMinDomain S T x Z tau).mp hmin
  obtain ⟨_htau, _htau0, haDom⟩ :=
    (mem_lExpPosDom S T x Z tau).mp hminSpec.1
  have halpha : ContMDiffOn (modelWithCornersSelf ℝ ℝ) I 1 alpha (Icc (0 : ℝ) a) :=
    lRegularizedCurve_c1On S hS T x Z haDom
  have halpha0 : alpha 0 = x := lRegularizedCurve_zero S T x Z
  have halphaa : alpha a = q := hend
  have hheadEq : lRegularizedAction S T alpha 0 a = lCost S T x q tau := by
    calc
      lRegularizedAction S T alpha 0 a =
          lLength S T (fun s : ℝ ↦ lExp S T x Z s) 0 tau := by
        change lRegularizedAction S T alpha 0 (Real.sqrt tau) =
          lLength S T (squareRootReparametrization alpha) 0 tau
        exact (lLength_squareRootReparametrization_eq_lRegularizedAction (I := I) S T alpha tau htau.le).symm
      _ = lCost S T x q tau := by rw [hminSpec.2, hend]
  have hhead : lRegularizedAction S T alpha 0 a ≤ (Module.finrank ℝ E : ℝ) * a := by
    rw [hheadEq]
    have hcost := (div_le_iff₀ (by positivity : 0 < 2 * a)).mp hq
    nlinarith only [hcost]
  have hback : ∀ s ∈ Icc (0 : ℝ) b, T - s ^ 2 ∈ D.carrier := by
    intro s hs
    have hs2 : s ^ 2 ≤ b ^ 2 := (sq_le_sq₀ hs.1 hb.le).mpr hs.2
    apply hslab
    exact ⟨by linarith only [hs2, hb2], sub_le_self T (sq_nonneg s)⟩
  have hRmBack : ∃ B : ℝ, ∀ t ∈ Icc (T - b ^ 2) T, ∀ z : M,
      normSq0S (I := I) (S.base.metric t) z 4 (S.base.rm04 t z) ≤ B := by
    refine ⟨B, ?_⟩
    simpa only [hb2, sub_self] using hB
  refine ⟨q, ?_⟩
  intro r hr y hy
  obtain ⟨beta, hbeta, hbetaa, hbetab, htail⟩ :=
    exists_initial_geodesic_arc_action_le S hS T hT.le K hcomplete hslab
      (fun t ht ↦ hregular ⟨ht.1, ht.2.le⟩) ⟨B, hB⟩ hinit
      q y r hr hy a b ha.le hab hb2.le (by
        rw [ha2]
        dsimp only [tau, δ]
        linarith only [hC])
  have hjoin := lCost_le_join_on_carrier_of_bounded_rm S hS T b ha hab
    alpha beta halpha hbeta.contMDiffOn (halphaa.trans hbetaa.symm) hback hRmBack
  rw [halpha0, hbetab, hb2] at hjoin
  have hcost : lCost S T x y T ≤ (Module.finrank ℝ E : ℝ) * a +
      (Λ * r ^ 2 / (2 * (b - a)) + (2 / 3 : ℝ) * Q * (b ^ 3 - a ^ 3)) :=
    hjoin.trans (add_le_add hhead htail)
  change lCost S T x y T / (2 * b) ≤
    (Module.finrank ℝ E : ℝ) / 2 + Λ * r ^ 2 / (2 * δ) + Q * δ
  exact (div_le_div_of_nonneg_right hcost (by positivity)).trans
    (initialFan_late_algebra (Module.finrank ℝ E) Λ Q r a b δ
      (Nat.cast_nonneg _) (Real.exp_pos _).le hQ ha hab hδ hδeq)

end DifferentialGeometry.PDE.RicciFlow

end
