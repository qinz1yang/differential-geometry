import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.KappaSolutions.BufferedMixedCurvature
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.KappaSolutions.UniversalDerivativeEstimates
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.KappaSolutions.UniversalDerivativesJetBridge
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.KappaSolutions.RoundFlowMixedJets
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.KappaSolutions.UniversalPrecompactness

set_option autoImplicit false

noncomputable section

namespace DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions

open Bundle Filter Manifold Set
open DifferentialGeometry.Tensor0SBundle
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.CheegerGromovCompactness
open CanonicalNeighborhood CanonicalNeighborhood.FiniteHorn
open DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
open scoped Manifold ContDiff _root_.Topology ENNReal

universe u uE uH

section LocalCurvatureBound

variable {E : Type uE} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [CompleteSpace E]
  {H : Type uH} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]

private local instance localBoundTopology {D : RealTimeInterval}
    (F : PointedFlowData.{u, uE, uH} (I := I) D) : TopologicalSpace F.M := F.topology
private local instance localBoundCharted {D : RealTimeInterval}
    (F : PointedFlowData.{u, uE, uH} (I := I) D) : ChartedSpace H F.M := F.charted
private local instance localBoundSmooth {D : RealTimeInterval}
    (F : PointedFlowData.{u, uE, uH} (I := I) D) : IsManifold I ∞ F.M := F.smooth
private local instance localBoundC1 {D : RealTimeInterval}
    (F : PointedFlowData.{u, uE, uH} (I := I) D) : IsManifold I 1 F.M :=
  IsManifold.of_le (n := ∞) (by decide)
private local instance localBoundC2 {D : RealTimeInterval}
    (F : PointedFlowData.{u, uE, uH} (I := I) D) : IsManifold I 2 F.M :=
  IsManifold.of_le (n := ∞) (by decide)
private local instance localBoundT2 {D : RealTimeInterval}
    (F : PointedFlowData.{u, uE, uH} (I := I) D) : T2Space F.M := F.t2
private local instance localBoundSigma {D : RealTimeInterval}
    (F : PointedFlowData.{u, uE, uH} (I := I) D) : SigmaCompactSpace F.M := F.sigmaCompact


def KLimLocalCurvatureBound (kappa : ℝ) : Prop :=
  ∃ C : ℝ → ℝ, (∀ A, 0 < C A) ∧
    ∀ (D : RealTimeInterval) (F : PointedFlowData.{u, uE, uH} (I := I) D),
      KLim (I := I) kappa F → F.S.scalar 0 F.basepoint = 1 →
        ∀ A : ℝ, ∀ y : F.M,
          riemannianEDistOf (I := I) (F.S.base.metric 0) F.basepoint y ≤
            ENNReal.ofReal A →
          ∀ t : ℝ, t ≤ 0 →
            (0 ≤ F.S.scalar t y ∧ F.S.scalar t y ≤ C A) ∧
              F.rmNormSq (I := I) t y ≤ 3 * (C A) ^ 2


def AncientKappaUniversalKappaGap : Prop :=
  ∀ (kappa : ℝ) (F : PointedFlowData.{u, uE, uH} (I := I) ancientTimeInterval),
    IsAncientKappaSolution (I := I) kappa F →
      IsShrinkingSphericalSpaceFormFlow (I := I) F ∨
        IsAncientKappaSolution (I := I) universalKappaConstant F


theorem exists_normalized_klim_spatial_jet_constants_of_localCurvatureBound
    (hdim : Module.finrank ℝ E = 3) (kappa : ℝ)
    (h : KLimLocalCurvatureBound.{u, uE, uH} (I := I) kappa) :
    ∃ K : ℝ → ℝ, (∀ A, 0 < K A) ∧
      ∀ (D : RealTimeInterval) (F : PointedFlowData.{u, uE, uH} (I := I) D),
        KLim kappa F → F.S.scalar 0 F.basepoint = 1 →
        ∀ A : ℝ, 0 ≤ A → ∀ s : ℝ, s ≤ 0 → ∀ m : ℕ, ∀ y : F.M,
          riemannianEDistOf (I := I) (F.S.base.metric 0) F.basepoint y ≤
            ENNReal.ofReal A →
          curvDerivNorm (I := I) m (F.S.base.metric s) y ≤
            shiLocalUniformBound 3 m (K A) (Real.sqrt (K A)) * K A := by
  obtain ⟨C, hC, hbound⟩ := h
  refine ⟨fun A => 2 * C (A + 1), fun A => mul_pos (by norm_num) (hC (A + 1)), ?_⟩
  intro D F hK hbase A hA s hs m y hy
  let _ : ConnectedSpace F.M := hK.connected
  let _ : NeZero (Module.finrank ℝ E) := ⟨by omega⟩
  let K : ℝ := 2 * C (A + 1)
  have hKpos : 0 < K := mul_pos (by norm_num) (hC (A + 1))
  have hsqrt : 0 < Real.sqrt K := Real.sqrt_pos.2 hKpos
  have houter : Real.sqrt K / Real.sqrt K = 1 := div_self hsqrt.ne'
  have ha : s - 1 ≤ 0 := by linarith
  have hspan : s - (s - 1) = 1 := by ring
  have hacar : s - 1 ∈ D.carrier := by
    simpa only [hK.carrier_eq, Set.mem_Iic] using ha
  have hcomplete : RiemannianMetricComplete (I := I) (F.S.base.metric (s - 1)) :=
    ⟨MetricComplete.complete (I := I) (F.atTime (I := I) (s - 1))
      (hK.complete (s - 1) hacar)⟩
  have hball : IsCompact {z : F.M |
      riemannianEDistOf (I := I) (F.S.base.metric (s - 1)) y z ≤
        ENNReal.ofReal (Real.sqrt K / Real.sqrt K)} := by
    rw [houter]
    exact hcomplete.closedEBall_isCompact y 1
  have hcurv : ∀ q ∈ Set.Icc (s - 1) s, ∀ z : F.M,
      riemannianEDistOf (I := I) (F.S.base.metric (s - 1)) y z ≤
        ENNReal.ofReal (Real.sqrt K / Real.sqrt K) →
          curvDerivNormSq (I := I) 0 (F.S.base.metric q) z ≤ K ^ 2 := by
    intro q hq z hz
    rw [houter] at hz
    have hterminal := klim_buffered_ball_subset F hK ha hA zero_le_one
      F.basepoint y z hy hz
    have hb := hbound D F hK hbase (A + 1) z hterminal q (hq.2.trans hs)
    change F.rmNormSq (I := I) q z ≤ K ^ 2
    apply hb.2.trans
    dsimp only [K]
    nlinarith [sq_nonneg (C (A + 1))]
  have hcarrier : Set.Icc (s - 1) s ⊆ D.carrier := by
    intro q hq
    simpa only [hK.carrier_eq, Set.mem_Iic] using hq.2.trans hs
  have hregular : Set.Ico (s - 1) s ⊆ D.regular := by
    intro q hq
    simpa only [hK.regular_eq, Set.mem_Iio] using hq.2.trans_le hs
  have hcenter : riemannianEDistOf (I := I) (F.S.base.metric (s - 1)) y y ≤
      ENNReal.ofReal (Real.sqrt K / (2 * Real.sqrt K)) :=
    (riemannianEDistOf_self (I := I) (F.S.base.metric (s - 1)) y).le.trans bot_le
  have hb := shi_local_curvDerivNorm_terminal_of_solution_jets F.S F.isSolution
    hK.dimension_ge_two (a := s - 1) (b := s) (K := K) (R := Real.sqrt K)
    (by linarith) hKpos hsqrt hcarrier hregular y hball hcurv
    m s ⟨by linarith, le_rfl⟩ y hcenter
  change curvDerivNorm (I := I) m (F.S.base.metric s) y ≤
    shiLocalUniformBound 3 m K (Real.sqrt K) * K
  simpa only [hdim, hspan, mul_one, Real.sqrt_one, one_pow, div_one] using hb


theorem exists_normalized_klim_mixed_jet_bound_of_localCurvatureBound
    (hdim : Module.finrank ℝ E = 3) (kappa A : ℝ) (hA : 0 ≤ A) (p q : ℕ)
    (h : KLimLocalCurvatureBound.{u, uE, uH} (I := I) kappa) :
    ∃ C : ℝ, 0 < C ∧
      ∀ (D : RealTimeInterval) (F : PointedFlowData.{u, uE, uH} (I := I) D),
        KLim kappa F → F.S.scalar 0 F.basepoint = 1 →
        ∀ t : ℝ, t ≤ 0 → ∀ y : F.M,
          riemannianEDistOf (I := I) (F.S.base.metric 0) F.basepoint y ≤ ENNReal.ofReal A →
          DifferentiableWithinAt ℝ (fun s => mixedCurvatureTensor F.S p q s y) (Set.Iic 0) t ∧
          mixedCurvatureNorm F.S p q t y ≤ C := by
  classical
  obtain ⟨K, _, hspatial⟩ :=
    exists_normalized_klim_spatial_jet_constants_of_localCurvatureBound hdim kappa h
  choose P hP using fun j : ℕ => exists_mixed_curvature_jet_polynomials 3 p j
  let B : ℕ → ℝ := fun j => shiLocalUniformBound 3 j (K A) (Real.sqrt (K A)) * K A
  refine ⟨1 + curvatureJetPolynomialNormBound (P q) B, ?_, ?_⟩
  · exact add_pos_of_pos_of_nonneg zero_lt_one (Real.sqrt_nonneg _)
  intro D F hK hbase t ht y hy
  let _ : NeZero (Module.finrank ℝ E) := ⟨by omega⟩
  have hdim_y : Module.finrank ℝ (TangentSpace I y) = 3 := hdim
  obtain ⟨basis, horth⟩ := exists_orthonormalBasisAt (I := I) (F.S.base.metric t) y hdim_y
  have hON : ∀ i j, (F.S.base.metric t).inner y (basis i) (basis j) =
      if i = j then 1 else 0 := horth
  have hactual : DifferentiableWithinAt ℝ
        (fun s => mixedCurvatureTensor F.S p q s y) (Set.Iic 0) t ∧
      ∀ slots, component0S (I := I) basis (mixedCurvatureTensor F.S p q t y) slots =
        MvPolynomial.eval (curvatureJetPolynomialValues F.S (p + 2 * q) t basis) (P q slots) := by
    rcases lt_or_eq_of_le ht with htneg | rfl
    · have htr : t ∈ D.regular := by simpa only [hK.regular_eq, Set.mem_Iio] using htneg
      obtain ⟨hdiff, hcomp⟩ := hP q F.S F.isSolution t htr y basis
      exact ⟨hdiff.differentiableWithinAt, hcomp⟩
    · have hreg : Set.Ioo (-1 : ℝ) 0 ⊆ D.regular := by
        intro s hs
        simpa only [hK.regular_eq, Set.mem_Iio] using hs.2
      exact mixedCurvature_polynomial_terminal_of_regular F.S F.isSolution p
        (by norm_num : (-1 : ℝ) < 0) hK.carrier_eq hreg P y basis
        (fun j s hs => hP j F.S F.isSolution s (hreg hs) y basis) q
  refine ⟨hactual.1, ?_⟩
  have hbound := norm_le_curvatureJetPolynomialNormBound F.S t basis hON (P q)
    (mixedCurvatureTensor F.S p q t y) hactual.2 B
    (fun j _ => hspatial D F hK hbase A hA t ht j y hy)
  exact hbound.trans (le_add_of_nonneg_left zero_le_one)

end LocalCurvatureBound


section ThreeSpace

attribute [local instance] PointedFlowData.topology PointedFlowData.charted
  PointedFlowData.smooth PointedFlowData.t2 PointedFlowData.sigmaCompact
  PointedFlowData.t2TangentBundle

private theorem localBoundThreeSpaceFinrank : Module.finrank ℝ ThreeSpace = 3 := by
  simp [ThreeSpace]


theorem ancientKappa_mixedCurvatureTensor_differentiableWithinAt_of_rmNormSqBounded
    {kappa : ℝ} (P : PointedFlowData.{u, 0, 0} (I := I3) ancientTimeInterval)
    (hP : IsAncientKappaSolution (I := I3) kappa P) (p q : ℕ) {t : ℝ} (ht : t ≤ 0) :
    DifferentiableWithinAt ℝ
      (fun s : ℝ => mixedCurvatureTensor P.S p q s P.basepoint) (Set.Iic 0) t := by
  obtain ⟨C, hC, hrm⟩ := ancientKappa_rmNormSqBounded P localBoundThreeSpaceFinrank hP
  have hCnn : 0 ≤ C := (hC (0 : ℝ) (by simp) P.basepoint).1.trans
    (hC (0 : ℝ) (by simp) P.basepoint).2
  have hsqrt3 : 0 < Real.sqrt 3 := Real.sqrt_pos.2 (by norm_num)
  have hroot : 0 ≤ Real.sqrt 3 * C := mul_nonneg hsqrt3.le hCnn
  have hKpos : 0 < max (Real.sqrt 3 * C) 1 := lt_of_lt_of_le zero_lt_one (le_max_right _ _)
  have hcurv : ∀ s : ℝ, s ≤ 0 → ∀ z : P.M,
      P.rmNormSq (I := I3) s z ≤ (max (Real.sqrt 3 * C) 1) ^ 2 := by
    intro s hs z
    refine (hrm s (by simpa only [hP.carrier_eq, Set.mem_Iic] using hs) z).trans ?_
    exact pow_le_pow_left₀ hroot (le_max_left _ _) 2
  have hG : KLim kappa P := ancientKappaThree_toKLim P hP localBoundThreeSpaceFinrank
  obtain ⟨C', _, hbound⟩ := exists_mixed_jet_bound_of_rmNormSq_bound (I := I3)
    localBoundThreeSpaceFinrank (K := max (Real.sqrt 3 * C) 1) hKpos p q
  exact (hbound kappa ancientTimeInterval P hG hcurv t ht P.basepoint).1


theorem exists_universal_mixed_jet_bound_of_not_round_of_localCurvatureBound (a b : ℕ)
    (h : KLimLocalCurvatureBound.{u, 0, 0} (I := I3)
      universalKappaConstant)
    (hgap : AncientKappaUniversalKappaGap.{u, 0, 0} (I := I3)) :
    ∃ C : ℝ, 0 < C ∧
      ∀ (kappa : ℝ) (F : PointedFlowData.{u, 0, 0} (I := I3) ancientTimeInterval),
        IsAncientKappaSolution (I := I3) kappa F →
        ¬ IsShrinkingSphericalSpaceFormFlow (I := I3) F → ∀ t ≤ 0, ∀ x : F.M,
          mixedCurvatureNorm F.S a b t x ≤ C * F.S.scalar t x ^ mixedCurvatureWeight a b := by
  obtain ⟨C, hC, hbound⟩ := exists_normalized_klim_mixed_jet_bound_of_localCurvatureBound
    (I := I3) localBoundThreeSpaceFinrank universalKappaConstant 0 le_rfl a b h
  refine ⟨C, hC, ?_⟩
  intro kappa F hF hnotround t ht x
  set Q : ℝ := F.S.scalar t x with hQdef
  have hQ : 0 < Q := ancientKappa_scalar_pos F localBoundThreeSpaceFinrank hF ht x
  have hnormalized : IsAncientKappaSolution (I := I3) universalKappaConstant
      (universalNormalizedFlow F hF ht x) :=
    (hgap kappa (universalNormalizedFlow F hF ht x)
      (universalNormalizedFlow_isAncientKappaSolution F hF ht x)).resolve_left
      (universalNormalizedFlow_not_isShrinkingSphericalSpaceFormFlow F hF hnotround ht x)
  have hG : KLim universalKappaConstant (universalNormalizedFlow F hF ht x) :=
    ancientKappaThree_toKLim (universalNormalizedFlow F hF ht x)
      hnormalized localBoundThreeSpaceFinrank
  have hbase : (universalNormalizedFlow F hF ht x).S.scalar 0
      (universalNormalizedFlow F hF ht x).basepoint = 1 :=
    universalNormalizedFlow_scalarAtBase F hF ht x
  have hnorm := (hbound ancientTimeInterval (universalNormalizedFlow F hF ht x) hG hbase
    0 le_rfl (universalNormalizedFlow F hF ht x).basepoint
    (by simp [riemannianEDistOf_self])).2
  have hnorm' : mixedCurvatureNorm (curvatureNormalizedSolution F.S t Q hQ ht) a b 0 x ≤ C :=
    hnorm
  have hscale := mixedCurvatureNorm_curvatureNormalizedSolution (I := I3) F.S F.isSolution
    hF.carrier_eq hF.regular_eq t Q hQ ht a b (le_refl (0 : ℝ)) x
  have hpt : parabolicTime t Q 0 = t := by simp [parabolicTime]
  rw [hpt] at hscale
  have hexp : (-(1 : ℝ) - (a : ℝ) / 2 - (b : ℝ)) = -(mixedCurvatureWeight a b) := by
    simp only [mixedCurvatureWeight]; ring
  rw [hexp, Real.rpow_neg hQ.le] at hscale
  rw [hscale] at hnorm'
  have hw : 0 < Q ^ mixedCurvatureWeight a b := Real.rpow_pos_of_pos hQ _
  have hfinal := (inv_mul_le_iff₀ hw).1 hnorm'
  linarith [hfinal]


theorem exists_universal_mixed_jet_bound_of_localCurvatureBound (a b : ℕ) {C₁ : ℝ}
    (hround : RoundMixedJetBound.{u} a b C₁)
    (h : KLimLocalCurvatureBound.{u, 0, 0} (I := I3)
      universalKappaConstant)
    (hgap : AncientKappaUniversalKappaGap.{u, 0, 0} (I := I3)) :
    ∃ C : ℝ, 0 < C ∧ UniversalMixedJetBound.{u} a b C := by
  obtain ⟨C₀, hC₀, hmain⟩ :=
    exists_universal_mixed_jet_bound_of_not_round_of_localCurvatureBound.{u} a b h hgap
  refine ⟨max C₀ C₁, lt_max_of_lt_left hC₀, ?_⟩
  intro kappa F hF t ht x
  have hR : 0 ≤ F.S.scalar t x ^ mixedCurvatureWeight a b :=
    Real.rpow_nonneg (ancientKappa_scalar_pos F localBoundThreeSpaceFinrank hF ht x).le _
  by_cases hsph : IsShrinkingSphericalSpaceFormFlow (I := I3) F
  · exact (hround kappa F hF hsph t ht x).trans
      (mul_le_mul_of_nonneg_right (le_max_right _ _) hR)
  · exact (hmain kappa F hF hsph t ht x).trans
      (mul_le_mul_of_nonneg_right (le_max_left _ _) hR)


theorem exists_kappa_universal_derivatives_of_localCurvatureBound (a b : ℕ)
    (h : KLimLocalCurvatureBound.{u, 0, 0} (I := I3)
      universalKappaConstant)
    (hgap : AncientKappaUniversalKappaGap.{u, 0, 0} (I := I3)) :
    ∃ C : ℝ, 0 < C ∧ ∀ kappa : ℝ, 0 < kappa →
      ∀ P : PointedFlowData.{u, 0, 0} (I := I3) ancientTimeInterval,
        IsAncientKappaSolution (I := I3) kappa P → PointedFlowScalarAtBase (I := I3) P 1 →
        ∀ J : MixedCurvatureJet P.S, J.norm a b 0 P.basepoint ≤ C := by
  obtain ⟨C₁, _, hround⟩ := exists_round_mixed_jet_bound.{u} a b
  obtain ⟨C, hC, hU⟩ :=
    exists_universal_mixed_jet_bound_of_localCurvatureBound.{u} a b hround h hgap
  refine ⟨C, hC, ?_⟩
  intro kappa _ P hP hbase J
  have hdiff : ∀ (q : ℕ) (t : ℝ), t ≤ 0 →
      DifferentiableWithinAt ℝ
        (fun s : ℝ => mixedCurvatureTensor P.S a q s P.basepoint) (Set.Iic 0) t :=
    fun q t ht =>
      ancientKappa_mixedCurvatureTensor_differentiableWithinAt_of_rmNormSqBounded P hP a q ht
  have hbridge : J.norm a b 0 P.basepoint = mixedCurvatureNorm P.S a b 0 P.basepoint :=
    mixedCurvatureJet_norm_eq P.S J a P.basepoint hdiff b le_rfl
  have hjet := hU kappa P hP 0 le_rfl P.basepoint
  have hscalar : P.S.scalar 0 P.basepoint = 1 := hbase
  rw [hscalar, Real.one_rpow, mul_one] at hjet
  rw [hbridge]
  exact hjet


theorem exists_kappa_universal_derivatives_of_roundMixedJetBound (a b : ℕ) {C₁ : ℝ}
    (hround : RoundMixedJetBound.{u} a b C₁) :
    ∃ C : ℝ, 0 < C ∧ ∀ kappa : ℝ, 0 < kappa →
      ∀ P : PointedFlowData.{u, 0, 0} (I := I3) ancientTimeInterval,
        IsAncientKappaSolution (I := I3) kappa P →
        IsShrinkingSphericalSpaceFormFlow (I := I3) P →
        PointedFlowScalarAtBase (I := I3) P 1 →
        ∀ J : MixedCurvatureJet P.S, J.norm a b 0 P.basepoint ≤ C := by
  refine ⟨max C₁ 1, lt_of_lt_of_le zero_lt_one (le_max_right _ _), ?_⟩
  intro kappa _ P hP hroundP hbase J
  have hdiff : ∀ (q : ℕ) (t : ℝ), t ≤ 0 →
      DifferentiableWithinAt ℝ
        (fun s : ℝ => mixedCurvatureTensor P.S a q s P.basepoint) (Set.Iic 0) t :=
    fun q t ht =>
      ancientKappa_mixedCurvatureTensor_differentiableWithinAt_of_rmNormSqBounded P hP a q ht
  have hbridge : J.norm a b 0 P.basepoint = mixedCurvatureNorm P.S a b 0 P.basepoint :=
    mixedCurvatureJet_norm_eq P.S J a P.basepoint hdiff b le_rfl
  have hjet := hround kappa P hP hroundP 0 le_rfl P.basepoint
  have hscalar : P.S.scalar 0 P.basepoint = 1 := hbase
  rw [hscalar, Real.one_rpow, mul_one] at hjet
  rw [hbridge]
  exact hjet.trans (le_max_left _ _)


theorem roundShrinker_localCurvatureBound {kappa : ℝ}
    (P : PointedFlowData.{u, 0, 0} (I := I3) ancientTimeInterval)
    (hP : IsAncientKappaSolution (I := I3) kappa P)
    (hround : IsShrinkingSphericalSpaceFormFlow (I := I3) P)
    (hbase : PointedFlowScalarAtBase (I := I3) P 1) :
    ∀ t : ℝ, t ≤ 0 → ∀ y : P.M,
      (0 ≤ P.S.scalar t y ∧ P.S.scalar t y ≤ 2) ∧
        P.rmNormSq (I := I3) t y ≤ 3 * (2 : ℝ) ^ 2 := by
  intro t ht y
  have hK : KLim kappa P := ancientKappaThree_toKLim P hP localBoundThreeSpaceFinrank
  have hbase0 : P.S.scalar 0 P.basepoint = 1 := hbase
  have hterm : P.S.scalar 0 y ≤ 1 := by
    rw [sphericalSpaceFormFlow_scalar_eq P hround (le_refl (0 : ℝ)) y P.basepoint, hbase0]
  have hle1 : P.S.scalar t y ≤ 1 := (hK.scalar_le_terminal ht y).trans hterm
  refine ⟨⟨hK.scalar_nonneg ht y, hle1.trans (by norm_num)⟩, ?_⟩
  exact (hK.rmNormSq_le_of_terminal_scalar_le (B := 1) P localBoundThreeSpaceFinrank ht y
    hterm).trans (by norm_num)

end ThreeSpace

end DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions

end
