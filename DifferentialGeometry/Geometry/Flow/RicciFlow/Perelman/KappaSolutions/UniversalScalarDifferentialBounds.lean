import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.KappaSolutions.UniversalDerivativeEstimates
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.KappaSolutions.ScalarScaleComparison
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.KappaSolutions.StandardHarnackLimit
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.GoodPointDerivatives
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.ScalarLaplacianJet
import DifferentialGeometry.Geometry.Flow.RicciFlow.Evolution.Scalar.TerminalSlope


set_option autoImplicit false
noncomputable section

namespace DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions

open Set
open DifferentialGeometry.Tensor0SBundle
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.CheegerGromovCompactness
open CanonicalNeighborhood CanonicalNeighborhood.FiniteHorn
open DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
open scoped Manifold ContDiff

universe u

attribute [local instance] PointedFlowData.topology PointedFlowData.charted
  PointedFlowData.smooth PointedFlowData.t2 PointedFlowData.sigmaCompact
  PointedFlowData.t2TangentBundle

private theorem threeSpace_finrank : Module.finrank ℝ ThreeSpace = 3 := by
  simp [ThreeSpace]

private theorem threeSpace_finrank_cast : ((Module.finrank ℝ ThreeSpace : ℕ) : ℝ) = 3 := by
  rw [threeSpace_finrank]; norm_num

private local instance threeSpace_finrank_neZero : NeZero (Module.finrank ℝ ThreeSpace) :=
  ⟨by rw [threeSpace_finrank]; norm_num⟩

private local instance scalarDifferentialC1 {D : RealTimeInterval}
    (F : PointedFlowData.{u, 0, 0} (I := I3) D) : IsManifold I3 1 F.M :=
  IsManifold.of_le (n := ∞) (by decide)

private local instance scalarDifferentialC2 {D : RealTimeInterval}
    (F : PointedFlowData.{u, 0, 0} (I := I3) D) : IsManifold I3 2 F.M :=
  IsManifold.of_le (n := ∞) (by decide)


private theorem rpow_mixedCurvatureWeight_zero_zero (R : ℝ) :
    R ^ mixedCurvatureWeight 0 0 = R := by
  have hw : mixedCurvatureWeight 0 0 = 1 := by
    simp only [mixedCurvatureWeight]; norm_num
  rw [hw, Real.rpow_one]

private theorem rpow_mixedCurvatureWeight_one_zero {R : ℝ} (hR : 0 < R) :
    R ^ mixedCurvatureWeight 1 0 = R * Real.sqrt R := by
  have hw : mixedCurvatureWeight 1 0 = 1 + 1 / 2 := by
    simp only [mixedCurvatureWeight]; norm_num
  rw [hw, Real.rpow_add hR, Real.rpow_one, ← Real.sqrt_eq_rpow]

private theorem rpow_mixedCurvatureWeight_two_zero (R : ℝ) :
    R ^ mixedCurvatureWeight 2 0 = R ^ 2 := by
  have hw : mixedCurvatureWeight 2 0 = ((2 : ℕ) : ℝ) := by
    simp only [mixedCurvatureWeight]; norm_num
  rw [hw, Real.rpow_natCast]


def scalarDifferentialConstant (C₀ C₁ C₂ : ℝ) : ℝ :=
  max 1 (max (9 * C₁) (729 * C₂ + 162 * C₀ ^ 2))

theorem one_le_scalarDifferentialConstant (C₀ C₁ C₂ : ℝ) :
    1 ≤ scalarDifferentialConstant C₀ C₁ C₂ :=
  le_max_left _ _


theorem abs_scalarDifferential_le_of_universal {C₁ : ℝ}
    (h10 : UniversalMixedJetBound.{u} 1 0 C₁) (kappa : ℝ)
    (F : PointedFlowData.{u, 0, 0} (I := I3) ancientTimeInterval)
    (hF : IsAncientKappaSolution (I := I3) kappa F) {t : ℝ} (ht : t ≤ 0) (x : F.M)
    (v : TangentSpace I3 x) :
    |scalarDifferential (I := I3) F.S t x v| ≤
      9 * C₁ * F.S.scalar t x * Real.sqrt (F.S.scalar t x) *
        Real.sqrt ((F.S.base.metric t).inner x v v) := by
  have hR : 0 < F.S.scalar t x := ancientKappa_scalar_pos F threeSpace_finrank hF ht x
  have hbase := abs_scalarDifferential_le (I := I3) F.S t x v
  rw [threeSpace_finrank_cast] at hbase
  have hjet : Real.sqrt (nablaKRm04NormSqIntrinsic (I := I3) F.S 1 t x) =
      mixedCurvatureNorm F.S 1 0 t x := rfl
  rw [hjet] at hbase
  have hbound : mixedCurvatureNorm F.S 1 0 t x ≤
      C₁ * (F.S.scalar t x * Real.sqrt (F.S.scalar t x)) := by
    have h := h10 kappa F hF t ht x
    rwa [rpow_mixedCurvatureWeight_one_zero hR] at h
  have hv : (0 : ℝ) ≤ Real.sqrt ((F.S.base.metric t).inner x v v) := Real.sqrt_nonneg _
  calc |scalarDifferential (I := I3) F.S t x v|
      ≤ (3 : ℝ) ^ 2 * mixedCurvatureNorm F.S 1 0 t x *
          Real.sqrt ((F.S.base.metric t).inner x v v) := hbase
    _ ≤ (3 : ℝ) ^ 2 * (C₁ * (F.S.scalar t x * Real.sqrt (F.S.scalar t x))) *
          Real.sqrt ((F.S.base.metric t).inner x v v) :=
        mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left hbound (by norm_num)) hv
    _ = 9 * C₁ * F.S.scalar t x * Real.sqrt (F.S.scalar t x) *
          Real.sqrt ((F.S.base.metric t).inner x v v) := by ring


theorem abs_deriv_scalar_le_of_universal {C₀ C₂ : ℝ}
    (h00 : UniversalMixedJetBound.{u} 0 0 C₀) (h20 : UniversalMixedJetBound.{u} 2 0 C₂)
    (kappa : ℝ) (F : PointedFlowData.{u, 0, 0} (I := I3) ancientTimeInterval)
    (hF : IsAncientKappaSolution (I := I3) kappa F) {t : ℝ} (ht : t < 0) (x : F.M) :
    |deriv (fun s : ℝ => F.S.scalar s x) t| ≤
      (729 * C₂ + 162 * C₀ ^ 2) * F.S.scalar t x ^ 2 := by
  have hR : 0 < F.S.scalar t x := ancientKappa_scalar_pos F threeSpace_finrank hF ht.le x
  have htreg : t ∈ ancientTimeInterval.regular := by
    simpa only [ancientTimeInterval_regular, Set.mem_Iio] using ht
  have hnhds : ancientTimeInterval.carrier ∈ nhds t :=
    ancientTimeInterval.regular_mem_nhds htreg
  have hevol := scalar_curvature_evolution (I := I3) F.S F.isSolution ⟨t, htreg⟩ x
  have hderiv : deriv (fun s : ℝ => F.S.scalar s x) t =
      laplacianAt (I := I3) (flowG (I := I3) F.S) t (F.S.scalar t) x +
        2 * normSq0S (I := I3) (F.S.family.metric t) x 2 (F.S.ricci t x) :=
    (hevol.hasDerivAt hnhds).deriv
  have hlap0 := abs_laplacian_scalar_le_second_curvature (I := I3) F.S t x
  rw [threeSpace_finrank_cast] at hlap0
  have hjet2 : Real.sqrt (nablaKRm04NormSqIntrinsic (I := I3) F.S 2 t x) =
      mixedCurvatureNorm F.S 2 0 t x := rfl
  rw [hjet2] at hlap0
  have hm2 : mixedCurvatureNorm F.S 2 0 t x ≤ C₂ * F.S.scalar t x ^ 2 := by
    have h := h20 kappa F hF t ht.le x
    rwa [rpow_mixedCurvatureWeight_two_zero] at h
  have hlap : |laplacianAt (I := I3) (flowG (I := I3) F.S) t (F.S.scalar t) x| ≤
      729 * (C₂ * F.S.scalar t x ^ 2) :=
    hlap0.trans (by
      have := mul_le_mul_of_nonneg_left hm2 (by norm_num : (0 : ℝ) ≤ (3 : ℝ) ^ 6)
      norm_num at this ⊢
      linarith)
  have hric : normSq0S (I := I3) (F.S.family.metric t) x 2 (F.S.ricci t x) ≤
      (Module.finrank ℝ ThreeSpace : ℝ) ^ 4 *
        nablaKRm04NormSqIntrinsic (I := I3) F.S 0 t x :=
    ricciSq_le_rm04 (I := I3) (F.S.base.metric t) (F.S.base.metric t) x
  rw [threeSpace_finrank_cast] at hric
  have hnn0 : (0 : ℝ) ≤ nablaKRm04NormSqIntrinsic (I := I3) F.S 0 t x :=
    normSq0S_nonneg (I := I3) _ _ _ _
  have hsq0 : nablaKRm04NormSqIntrinsic (I := I3) F.S 0 t x =
      mixedCurvatureNorm F.S 0 0 t x ^ 2 := by
    have hid : mixedCurvatureNorm F.S 0 0 t x =
        Real.sqrt (nablaKRm04NormSqIntrinsic (I := I3) F.S 0 t x) := rfl
    rw [hid, Real.sq_sqrt hnn0]
  have hm0 : mixedCurvatureNorm F.S 0 0 t x ≤ C₀ * F.S.scalar t x := by
    have h := h00 kappa F hF t ht.le x
    rwa [rpow_mixedCurvatureWeight_zero_zero] at h
  have hm0nn : (0 : ℝ) ≤ mixedCurvatureNorm F.S 0 0 t x := Real.sqrt_nonneg _
  have hricsq : nablaKRm04NormSqIntrinsic (I := I3) F.S 0 t x ≤
      C₀ ^ 2 * F.S.scalar t x ^ 2 := by
    rw [hsq0]
    nlinarith [hm0, hm0nn]
  have hricnn : (0 : ℝ) ≤ normSq0S (I := I3) (F.S.family.metric t) x 2 (F.S.ricci t x) :=
    normSq0S_nonneg (I := I3) _ _ _ _
  have hric' : normSq0S (I := I3) (F.S.family.metric t) x 2 (F.S.ricci t x) ≤
      81 * (C₀ ^ 2 * F.S.scalar t x ^ 2) := by
    have := mul_le_mul_of_nonneg_left hricsq (by norm_num : (0 : ℝ) ≤ (3 : ℝ) ^ 4)
    norm_num at this hric ⊢
    linarith
  rw [hderiv]
  calc |laplacianAt (I := I3) (flowG (I := I3) F.S) t (F.S.scalar t) x +
          2 * normSq0S (I := I3) (F.S.family.metric t) x 2 (F.S.ricci t x)|
      ≤ |laplacianAt (I := I3) (flowG (I := I3) F.S) t (F.S.scalar t) x| +
          |2 * normSq0S (I := I3) (F.S.family.metric t) x 2 (F.S.ricci t x)| := abs_add_le _ _
    _ ≤ (729 * C₂ + 162 * C₀ ^ 2) * F.S.scalar t x ^ 2 := by
        rw [abs_of_nonneg (by linarith : (0 : ℝ) ≤
          2 * normSq0S (I := I3) (F.S.family.metric t) x 2 (F.S.ricci t x))]
        nlinarith [hlap, hric']


theorem abs_derivWithin_scalar_Iic_le_of_universal {C₀ C₂ B : ℝ}
    (h00 : UniversalMixedJetBound.{u} 0 0 C₀) (h20 : UniversalMixedJetBound.{u} 2 0 C₂)
    (hB : 729 * C₂ + 162 * C₀ ^ 2 ≤ B) (hB0 : 0 ≤ B) (kappa : ℝ)
    (F : PointedFlowData.{u, 0, 0} (I := I3) ancientTimeInterval)
    (hF : IsAncientKappaSolution (I := I3) kappa F) (x : F.M) :
    |derivWithin (fun s : ℝ => F.S.scalar s x) (Set.Iic 0) 0| ≤ B * F.S.scalar 0 x ^ 2 := by
  have hK : KLim kappa F := ancientKappaThree_toKLim F hF threeSpace_finrank
  have hcont : ContinuousOn (fun s : ℝ => F.S.scalar s x) (Set.Icc (-1 : ℝ) 0) := by
    have hmap : Continuous (fun s : ℝ => (s, x)) := continuous_id.prodMk continuous_const
    have h := F.isSolution.scalarCont.comp hmap.continuousOn
      (fun s (hs : s ∈ Set.Icc (-1 : ℝ) 0) =>
        ⟨by simpa only [hF.carrier_eq, Set.mem_Iic] using hs.2, Set.mem_univ x⟩)
    simpa only [Function.comp_def] using h
  have hdiff : ∀ r ∈ Set.Ioo (-1 : ℝ) 0,
      DifferentiableAt ℝ (fun s : ℝ => F.S.scalar s x) r := by
    intro r hr
    have hrreg : r ∈ ancientTimeInterval.regular := by
      simpa only [ancientTimeInterval_regular, Set.mem_Iio] using hr.2
    exact (F.isSolution.scalarTime (K := ancientTimeInterval.carrier)
      (ancientTimeInterval.regular_subset hrreg) (fun _ hs => hs) x).differentiableAt
        (ancientTimeInterval.regular_mem_nhds hrreg)
  have hbound : ∀ r ∈ Set.Ioo (-1 : ℝ) 0,
      |deriv (fun s : ℝ => F.S.scalar s x) r| ≤ B * F.S.scalar 0 x ^ 2 := by
    intro r hr
    have h1 := abs_deriv_scalar_le_of_universal h00 h20 kappa F hF hr.2 x
    have hmono : F.S.scalar r x ≤ F.S.scalar 0 x := hK.scalar_le_terminal hr.2.le x
    have hnn : 0 ≤ F.S.scalar r x := hK.scalar_nonneg hr.2.le x
    have hsq : F.S.scalar r x ^ 2 ≤ F.S.scalar 0 x ^ 2 := by nlinarith [hmono, hnn]
    calc |deriv (fun s : ℝ => F.S.scalar s x) r|
        ≤ (729 * C₂ + 162 * C₀ ^ 2) * F.S.scalar r x ^ 2 := h1
      _ ≤ B * F.S.scalar r x ^ 2 := mul_le_mul_of_nonneg_right hB (sq_nonneg _)
      _ ≤ B * F.S.scalar 0 x ^ 2 := mul_le_mul_of_nonneg_left hsq hB0
  exact abs_derivWithin_Iic_le_of_interior_bound (fun s : ℝ => F.S.scalar s x)
    (a := -1) (b := 0) (by norm_num) (mul_nonneg hB0 (sq_nonneg _)) hcont hdiff hbound


theorem exists_universal_scalarDifferentialBounds {C₀ C₁ C₂ : ℝ}
    (h00 : UniversalMixedJetBound.{u} 0 0 C₀) (h10 : UniversalMixedJetBound.{u} 1 0 C₁)
    (h20 : UniversalMixedJetBound.{u} 2 0 C₂) :
    ∃ η : ℝ, 1 ≤ η ∧
      ∀ (kappa : ℝ) (F : PointedFlowData.{u, 0, 0} (I := I3) ancientTimeInterval),
        IsAncientKappaSolution (I := I3) kappa F → ScalarDifferentialBounds F η := by
  refine ⟨scalarDifferentialConstant C₀ C₁ C₂, one_le_scalarDifferentialConstant C₀ C₁ C₂, ?_⟩
  set η : ℝ := scalarDifferentialConstant C₀ C₁ C₂ with hηdef
  have hη1 : 1 ≤ η := one_le_scalarDifferentialConstant C₀ C₁ C₂
  have hη0 : (0 : ℝ) ≤ η := le_trans zero_le_one hη1
  have hηgrad : 9 * C₁ ≤ η := le_trans (le_max_left _ _) (le_max_right _ _)
  have hηtime : 729 * C₂ + 162 * C₀ ^ 2 ≤ η := le_trans (le_max_right _ _) (le_max_right _ _)
  intro kappa F hF t htc x
  have ht : t ≤ 0 := by
    simpa only [ancientTimeInterval_carrier, Set.mem_Iic] using htc
  have hR : 0 < F.S.scalar t x := ancientKappa_scalar_pos F threeSpace_finrank hF ht x
  refine ⟨?_, ?_, ?_⟩
  · intro v
    have hgrad := abs_scalarDifferential_le_of_universal h10 kappa F hF ht x v
    have hnn : (0 : ℝ) ≤ F.S.scalar t x * Real.sqrt (F.S.scalar t x) *
        Real.sqrt ((F.S.base.metric t).inner x v v) :=
      mul_nonneg (mul_nonneg hR.le (Real.sqrt_nonneg _)) (Real.sqrt_nonneg _)
    calc |scalarDifferential (I := I3) F.S t x v|
        ≤ 9 * C₁ * F.S.scalar t x * Real.sqrt (F.S.scalar t x) *
            Real.sqrt ((F.S.base.metric t).inner x v v) := hgrad
      _ = 9 * C₁ * (F.S.scalar t x * Real.sqrt (F.S.scalar t x) *
            Real.sqrt ((F.S.base.metric t).inner x v v)) := by ring
      _ ≤ η * (F.S.scalar t x * Real.sqrt (F.S.scalar t x) *
            Real.sqrt ((F.S.base.metric t).inner x v v)) :=
          mul_le_mul_of_nonneg_right hηgrad hnn
      _ = η * F.S.scalar t x * Real.sqrt (F.S.scalar t x) *
            Real.sqrt ((F.S.base.metric t).inner x v v) := by ring
  · exact (ancientKappaThree_toKLim F hF threeSpace_finrank).scalar_derivWithin_nonneg htc x
  · rcases lt_or_eq_of_le ht with htneg | rfl
    · have htreg : t ∈ ancientTimeInterval.regular := by
        simpa only [ancientTimeInterval_regular, Set.mem_Iio] using htneg
      have hnhds : ancientTimeInterval.carrier ∈ nhds t :=
        ancientTimeInterval.regular_mem_nhds htreg
      rw [derivWithin_of_mem_nhds hnhds]
      have h1 := abs_deriv_scalar_le_of_universal h00 h20 kappa F hF htneg x
      have h2 : deriv (fun s : ℝ => F.S.scalar s x) t ≤
          (729 * C₂ + 162 * C₀ ^ 2) * F.S.scalar t x ^ 2 := le_trans (le_abs_self _) h1
      have h3 : (729 * C₂ + 162 * C₀ ^ 2) * F.S.scalar t x ^ 2 ≤ η * F.S.scalar t x ^ 2 :=
        mul_le_mul_of_nonneg_right hηtime (sq_nonneg _)
      linarith
    · rw [ancientTimeInterval_carrier]
      exact le_trans (le_abs_self _)
        (abs_derivWithin_scalar_Iic_le_of_universal h00 h20 hηtime hη0 kappa F hF x)


theorem ancientKappa_scalar_scale_comparison_of_universal {C₀ C₁ C₂ : ℝ}
    (h00 : UniversalMixedJetBound.{u} 0 0 C₀) (h10 : UniversalMixedJetBound.{u} 1 0 C₁)
    (h20 : UniversalMixedJetBound.{u} 2 0 C₂) :
    ∃ η : ℝ, 1 ≤ η ∧
      ∀ (kappa : ℝ) (F : PointedFlowData.{u, 0, 0} (I := I3) ancientTimeInterval),
        IsAncientKappaSolution (I := I3) kappa F → ∀ t ≤ (0 : ℝ),
          (∀ x y : F.M, riemannianEDistOf (I := I3) (F.S.base.metric t) x y ≤
              ENNReal.ofReal (η⁻¹ / Real.sqrt (F.S.scalar t x)) →
            4 / 9 * F.S.scalar t x ≤ F.S.scalar t y ∧
              F.S.scalar t y ≤ 4 * F.S.scalar t x) ∧
          (∀ x : F.M, ∀ s ∈ Icc (t - (2 * η * F.S.scalar t x)⁻¹) t,
            2 / 3 * F.S.scalar t x ≤ F.S.scalar s x ∧
              F.S.scalar s x ≤ F.S.scalar t x) := by
  obtain ⟨η, hη, hb⟩ := exists_universal_scalarDifferentialBounds.{u} h00 h10 h20
  refine ⟨η, hη, ?_⟩
  intro kappa F hF
  exact ancientKappa_scalar_scale_comparison_three F threeSpace_finrank hF hη (hb kappa F hF)

end DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions

end
