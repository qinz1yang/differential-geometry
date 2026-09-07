import DifferentialGeometry.Analysis.Integration.Measure.Polar.Evaluation
import DifferentialGeometry.Analysis.Integration.WeightedIntegrationByParts
import DifferentialGeometry.Geometry.Comparison.Distance.Distribution
import DifferentialGeometry.Geometry.Comparison.Volume.SegmentBallIntegral
import DifferentialGeometry.Geometry.Comparison.Volume.SegmentRadialDensity
import DifferentialGeometry.Geometry.Comparison.Volume.SegmentRayInterval

set_option autoImplicit false

noncomputable section

open Bundle Function Manifold MeasureTheory Set
open scoped ContDiff ENNReal Manifold Topology

namespace DifferentialGeometry.Geometry.Riemannian

open DifferentialGeometry.Analysis.Integration
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Geometry.Operator
open DifferentialGeometry.Integral.DivergenceTheorem
open DifferentialGeometry.Integral.L2
open DifferentialGeometry.Integral.Measure
open BonnetMyers Exponential Variation VolumeComparison

attribute [instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace Real E]
  [FiniteDimensional Real E] [NeZero (Module.finrank Real E)] [CompleteSpace E]
variable {H : Type*} [TopologicalSpace H]
variable {I : ModelWithCorners Real E H} [I.Boundaryless]
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ((⊤ : ℕ∞) : WithTop ℕ∞) M] [T2Space M]
  [T2Space (TangentBundle I M)] [SigmaCompactSpace M]
  [ConnectedSpace M]
variable [RiemannianBundle (fun x : M ↦ TangentSpace I x)]

private local instance tangentSpaceNormedAddCommGroup (x : M) :
    NormedAddCommGroup (TangentSpace I x) :=
  Bundle.instNormedAddCommGroupOfRiemannianBundleOfIsTopologicalAddGroupOfContinuousConstSMulReal
    (E := fun y : M => TangentSpace I y) x

private local instance tangentSpaceInnerProductSpace (x : M) :
    InnerProductSpace Real (TangentSpace I x) :=
  Bundle.instInnerProductSpaceReal (E := fun y : M => TangentSpace I y) x

private local instance tangentSpaceNormedSpace (x : M) :
    NormedSpace Real (TangentSpace I x) := inferInstance

private local instance : MeasurableSpace E := borel E
private local instance : BorelSpace E := ⟨rfl⟩
private local instance : MeasurableSpace M := borel M
private local instance : BorelSpace M := ⟨rfl⟩

omit [NeZero (Module.finrank Real E)] [CompleteSpace E] [I.Boundaryless]
  [ConnectedSpace M] [RiemannianBundle (fun x : M ↦ TangentSpace I x)]
  [T2Space (TangentBundle I M)] in
private theorem locInt_mul_test
    {g : SmoothRiemannianMetric I M} {f : M → Real} {U : Set M}
    (hf : LocallyIntegrableOn f U
      (riemannianVolumeMeasure (I := I) (M := M) g))
    (φ : C^∞⟮I, M; Real⟯)
    (hφ : φ ∈ compactlySupportedSmoothFunctions I M)
    (hφU : tsupport (φ : M → Real) ⊆ U) :
    Integrable (fun x : M ↦ f x * φ x)
      (riemannianVolumeMeasure (I := I) (M := M) g) := by
  have hφ_cs : HasCompactSupport (φ : M → Real) := hφ
  have hf_on : IntegrableOn f (tsupport (φ : M → Real))
      (riemannianVolumeMeasure (I := I) (M := M) g) :=
    hf.integrableOn_compact_subset hφU hφ_cs
  have hmul_on : IntegrableOn (fun x : M ↦ f x * φ x)
      (tsupport (φ : M → Real))
      (riemannianVolumeMeasure (I := I) (M := M) g) :=
    hf_on.mul_continuousOn φ.contMDiff.continuous.continuousOn hφ_cs
  exact (integrableOn_iff_integrable_of_support_subset
    ((support_mul_subset_right f (φ : M → Real)).trans
      (subset_tsupport (φ : M → Real)))).mp hmul_on

omit [NeZero (Module.finrank Real E)] [CompleteSpace E] [I.Boundaryless]
  [T2Space (TangentBundle I M)] in
private theorem dist_rhs_int
    [IsContinuousRiemannianBundle E (fun x : M ↦ TangentSpace I x)]
    (g : SmoothRiemannianMetric I M) (p : M)
    (φ : C^∞⟮I, M; Real⟯)
    (hφ : φ ∈ compactlySupportedSmoothFunctions I M)
    (hφp : tsupport (φ : M → Real) ⊆ ({p}ᶜ : Set M))
    (d : Real) :
    Integrable
      (fun y : M ↦ d / (riemannianEDist I p y).toReal * φ y)
      (riemannianVolumeMeasure (I := I) (M := M) g) := by
  exact locInt_mul_test (I := I) (locallyIntegrableOn_inv_dist (I := I) g p d)
    φ hφ hφp

omit [NeZero (Module.finrank Real E)] [CompleteSpace E] [T2Space M]
  [SigmaCompactSpace M] [T2Space (TangentBundle I M)] in
private theorem pair_support_ball
    [IsContinuousRiemannianBundle E (fun x : M ↦ TangentSpace I x)]
    (g : SmoothRiemannianMetric I M) (p : M)
    (φ : C^∞⟮I, M; Real⟯) (d R : Real) (hR : 0 < R)
    (hφR : ∀ y ∈ tsupport (φ : M → Real),
      (riemannianEDist I p y).toReal < R) :
    let ρ : M → Real := fun y ↦ (riemannianEDist I p y).toReal
    let X : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯ :=
      gradG (I := I) g φ
    Function.support (tangentSectionAction (I := I) X ρ) ⊆
        {y : M | riemannianEDist I p y < ENNReal.ofReal R} ∧
      Function.support (fun y : M ↦ d / ρ y * φ y) ⊆
        {y : M | riemannianEDist I p y < ENNReal.ofReal R} := by
  let ρ : M → Real := fun y ↦ (riemannianEDist I p y).toReal
  let X : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯ :=
    gradG (I := I) g φ
  dsimp only
  have htoBall {y : M} (hy : y ∈ tsupport (φ : M → Real)) :
      riemannianEDist I p y < ENNReal.ofReal R := by
    rw [← ENNReal.ofReal_toReal (riemannianEDist_ne_top (I := I) p y)]
    exact (ENNReal.ofReal_lt_ofReal_iff hR).2 (hφR y hy)
  constructor
  · intro y hy
    apply htoBall
    apply support_gradFun_subset (I := I) g φ
    exact support_tangentSectionAction_subset (I := I) X ρ hy
  · intro y hy
    apply htoBall
    apply subset_tsupport (φ : M → Real)
    intro hφy
    exact hy (by simp only [hφy, mul_zero])

private theorem radial_pairing_le
    [PseudoEMetricSpace M] [IsRiemannianManifold I M] [CompleteSpace M]
    [IsContinuousRiemannianBundle E (fun x : M ↦ TangentSpace I x)]
    (g : SmoothRiemannianMetric I M)
    (hEnorm : IsMetricNorm (I := I) (M := M) g)
    (p : M) (φ : C^∞⟮I, M; Real⟯)
    (hd : 0 < Module.finrank Real E - 1)
    (hRic : RicciBoundedBelow (I := I) g 0)
    {a R : Real} (ha : 0 < a) (hR : 0 < R)
    (hφa : ∀ y ∈ tsupport (φ : M → Real),
      a ≤ (riemannianEDist I p y).toReal)
    (hφ0 : ∀ y : M, 0 ≤ φ y)
    (u : Metric.sphere (0 : E) 1) :
    let d : Nat := Module.finrank Real E - 1
    let ρ : M → Real := fun y ↦ (riemannianEDist I p y).toReal
    let X : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯ :=
      gradG (I := I) g φ
    let K : Set E := SegmentInt (I := I) g hEnorm p ∩ gBall (I := I) g p R
    let F : E → M := fun v ↦ expMapIntrinsic (I := I) g hEnorm p
      (show TangentSpace I p from v)
    let D : E → Real := fun v ↦ expJacobianDensity (I := I) g hEnorm p v
    let QL : Real → Real := fun r ↦ K.indicator
      (fun v : E ↦ D v * tangentSectionAction (I := I) X ρ (F v)) (r • u.1)
    let QR : Real → Real := fun r ↦ K.indicator
      (fun v : E ↦ D v *
        (((d : Nat) : Real) / ρ (F v) * φ (F v))) (r • u.1)
    Integrable (fun r : Ioi (0 : Real) ↦ QL r.1)
        (Measure.volumeIoiPow d) →
      Integrable (fun r : Ioi (0 : Real) ↦ QR r.1)
        (Measure.volumeIoiPow d) →
      -(∫ r : Ioi (0 : Real), QL r.1 ∂Measure.volumeIoiPow d) ≤
        ∫ r : Ioi (0 : Real), QR r.1 ∂Measure.volumeIoiPow d := by
  classical
  let d : Nat := Module.finrank Real E - 1
  let ρ : M → Real := fun y ↦ (riemannianEDist I p y).toReal
  let X : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯ :=
    gradG (I := I) g φ
  let K : Set E :=
    SegmentInt (I := I) g
      (show ∀ (y : M) (w : TangentSpace I y),
        ‖w‖ₑ = ENNReal.ofReal (Real.sqrt (g.inner y w w)) from hEnorm) p ∩
      gBall (I := I) g p R
  let F : E → M := fun v ↦ expMapIntrinsic (I := I) g hEnorm p
    (show TangentSpace I p from v)
  let D : E → Real := fun v ↦ expJacobianDensity (I := I) g hEnorm p v
  let QL : Real → Real := fun r ↦ K.indicator
    (fun v : E ↦ D v * tangentSectionAction (I := I) X ρ (F v)) (r • u.1)
  let QR : Real → Real := fun r ↦ K.indicator
    (fun v : E ↦ D v * (((d : Nat) : Real) / ρ (F v) * φ (F v))) (r • u.1)
  dsimp only
  intro hQL hQR
  have hu0 : (u.1 : E) ≠ 0 := by
    intro huz
    have hu := u.2
    rw [huz] at hu
    simp at hu
  have hu : 0 < g.inner p (u.1 : TangentSpace I p) u.1 :=
    g.pos p u.1 hu0
  let L : Real := Real.sqrt (g.inner p (u.1 : TangentSpace I p) u.1)
  have hL : 0 < L := Real.sqrt_pos.mpr hu
  obtain ⟨v, hON, hperp'⟩ := exists_perp_pos (I := I) g p
    (u.1 : TangentSpace I p) hu
  have hperp : ∀ i, g.inner p (u.1 : TangentSpace I p) (v i) = 0 := by
    intro i
    calc
      g.inner p (u.1 : TangentSpace I p) (v i) =
          g.inner p (v i) (u.1 : TangentSpace I p) := g.symm p _ _
      _ = 0 := hperp' i
  have hray : ∃ b : Real, 0 < b ∧
      b ≤ R / Real.sqrt (g.inner p (u.1 : TangentSpace I p) u.1) ∧
      {t : Real | 0 < t ∧
        (t • (u.1 : TangentSpace I p)) ∈ K} = Ioo 0 b := by
    obtain ⟨b, hb, hbR, hset⟩ :=
      segIntRay_gball_eq (E := E) (I := I) (M := M) g hEnorm p
        (u.1 : TangentSpace I p) hu (R := R) hR
    refine ⟨b, hb, hbR, ?_⟩
    change {t : Real | 0 < t ∧
      (t • (u.1 : TangentSpace I p)) ∈
        SegmentInt (I := I) g
          (show ∀ (y : M) (w : TangentSpace I y),
            ‖w‖ₑ = ENNReal.ofReal (Real.sqrt (g.inner y w w)) from hEnorm) p ∩
          gBall (I := I) g p R} = Ioo 0 b
    exact hset
  obtain ⟨b, hb, _hbR, hsetK⟩ := hray
  let γ : Real → M := intrinsicGeodesic (I := I) g hEnorm p
    (u.1 : TangentSpace I p)
  let V := fun i ↦ intrinsicJacobi (I := I) g hEnorm p
    (u.1 : TangentSpace I p) (v i)
  let J : Real → Real := fun t ↦ normalChartDensity (I := I) g p 0 *
    curveDensity (I := I) g γ V t
  have hFγ (t : Real) : F (t • u.1) = γ t := by
    change intrinsicGeodesic (I := I) g hEnorm p
      (show TangentSpace I p from t • (u.1 : E)) 1 =
      intrinsicGeodesic (I := I) g hEnorm p (u.1 : TangentSpace I p) t
    have harg : (show TangentSpace I p from t • (u.1 : E)) =
        t • (u.1 : TangentSpace I p) := by
      with_unfolding_all rfl
    rw [harg]
    calc
      intrinsicGeodesic (I := I) g hEnorm p
          (t • (u.1 : TangentSpace I p)) 1 =
          intrinsicGeodesic (I := I) g hEnorm p
            (u.1 : TangentSpace I p) (t * 1) :=
        intrinsicGeodesic_smul_apply (I := I) g hEnorm p
          (u.1 : TangentSpace I p) t 1
      _ = intrinsicGeodesic (I := I) g hEnorm p
          (u.1 : TangentSpace I p) t := by rw [mul_one]
  have hseg {t : Real} (ht : t ∈ Ioo (0 : Real) b) :
      (t • (u.1 : TangentSpace I p)) ∈ SegmentInt (I := I) g hEnorm p := by
    have htK : t ∈ {s : Real | 0 < s ∧
        (s • (u.1 : TangentSpace I p)) ∈ K} := by
      rw [hsetK]
      exact ht
    exact htK.2.1
  have hρeq {t : Real} (ht : t ∈ Ioo (0 : Real) b) :
      ρ (γ t) = t * L := by
    have htDom : (t • (u.1 : TangentSpace I p)) ∈
        SegmentDom (I := I) g hEnorm p :=
      segmentInt_subset (I := I) g hEnorm p (hseg ht)
    rw [← hFγ]
    change (riemannianEDist I p (F (t • u.1))).toReal = t * L
    rw [← (mem_segmentDom (I := I)).mp htDom]
    convert sqrt_gInner_smul_self (I := I) g p ht.1.le
      (u.1 : TangentSpace I p) using 1
    all_goals rfl
  have hrad : ∀ t ∈ Ioo (0 : Real) b,
      HasDerivAt J
          (normalChartDensity (I := I) g p 0 *
            (curveMean (I := I) g γ V t * curveDensity (I := I) g γ V t)) t ∧
        deriv J t ≤ ((d : Nat) : Real) / t * J t ∧
        D (t • u.1) * t ^ d = J t := by
    dsimp only [D, J, γ, V, d]
    exact radialDensity_deriv_le_of_segmentInt (I := I) g hEnorm p
      (u.1 : TangentSpace I p) b hd hu v hON hperp
      (fun t ht ↦ hseg ht) hRic
  let a₀ : Real := min (a / (2 * L)) (b / 2)
  have haL : 0 < a / (2 * L) := div_pos ha (mul_pos (by norm_num) hL)
  have hab : 0 < b / 2 := by positivity
  have ha₀ : 0 < a₀ := lt_min haL hab
  have ha₀b : a₀ < b :=
    (min_le_right (a / (2 * L)) (b / 2)).trans_lt (half_lt_self hb)
  let ψ : Real → Real := fun t ↦ L⁻¹ * φ (γ t)
  have hφγ : ContDiff Real ∞ (fun t : Real ↦ φ (γ t)) := by
    rw [← contMDiff_iff_contDiff]
    exact φ.contMDiff.comp
      (intrinsicGeodesic_contMDiff (I := I) g hEnorm p
        (u.1 : TangentSpace I p))
  have hφγ1 : ContDiff Real 1 (fun t : Real ↦ φ (γ t)) :=
    hφγ.of_le (by norm_num)
  have hψsmooth : ContDiff Real 1 ψ := by
    simpa only [ψ] using contDiff_const.mul hφγ1
  have hψderiv (t : Real) :
      deriv ψ t = L⁻¹ * deriv (fun s : Real ↦ φ (γ s)) t := by
    simpa only [ψ] using
      deriv_const_mul L⁻¹ (hφγ1.differentiable one_ne_zero).differentiableAt
  have hJ_ac : ∀ c ∈ Ioo a₀ b, AbsolutelyContinuousOnInterval J a₀ c := by
    intro c hc
    have hsegc : ∀ t ∈ Icc a₀ c,
        (t • (u.1 : TangentSpace I p)) ∈ SegmentInt (I := I) g hEnorm p := by
      intro t ht
      exact hseg ⟨ha₀.trans_le ht.1, ht.2.trans_lt hc.2⟩
    simpa only [γ, V, J] using
      radialDensity_absolutelyContinuousOnInterval_of_segmentInt
        (I := I) g hEnorm p (u.1 : TangentSpace I p)
        ha₀ hc.1.le hu v hON hsegc
  have hψ_ac : ∀ c ∈ Ioo a₀ b, AbsolutelyContinuousOnInterval ψ a₀ c := by
    intro c hc
    have hsmooth : ContDiffOn Real 1 ψ (Icc a₀ c) :=
      hψsmooth.contDiffOn
    obtain ⟨C, hC⟩ :=
      hsmooth.exists_lipschitzOnWith one_ne_zero (convex_Icc a₀ c) isCompact_Icc
    have hCu : LipschitzOnWith C ψ (uIcc a₀ c) := by
      simpa only [uIcc_of_le hc.1.le] using hC
    exact hCu.absolutelyContinuousOnInterval
  have hψzero : EqOn ψ 0 (Ioc (0 : Real) a₀) := by
    intro t ht
    have htIoo : t ∈ Ioo (0 : Real) b := ⟨ht.1, ht.2.trans_lt ha₀b⟩
    have htUpper : t ≤ a / (2 * L) :=
      ht.2.trans (min_le_left (a / (2 * L)) (b / 2))
    have htMul : t * L ≤ a / 2 := by
      calc
        t * L ≤ (a / (2 * L)) * L :=
          mul_le_mul_of_nonneg_right htUpper hL.le
        _ = a / 2 := by field_simp [hL.ne']
    have htLt : t * L < a := htMul.trans_lt (half_lt_self ha)
    have hφzero : φ (γ t) = 0 := by
      by_contra hne
      have hmem : γ t ∈ tsupport (φ : M → Real) :=
        subset_tsupport (φ : M → Real) (Function.mem_support.mpr hne)
      have hlower := hφa (γ t) hmem
      change a ≤ ρ (γ t) at hlower
      rw [hρeq htIoo] at hlower
      exact (not_lt_of_ge hlower) htLt
    simp only [ψ, hφzero, mul_zero, Pi.zero_apply]
  have hψ0 : ∀ᵐ t ∂volume.restrict (Ioo (0 : Real) b), 0 ≤ ψ t := by
    filter_upwards with t
    exact mul_nonneg (inv_nonneg.mpr hL.le) (hφ0 (γ t))
  have hbdry : ∀ c ∈ Ioo a₀ b, 0 ≤ J c * ψ c := by
    intro c _hc
    have hJ0 : 0 ≤ J c := mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
    exact mul_nonneg hJ0 (mul_nonneg (inv_nonneg.mpr hL.le) (hφ0 (γ c)))
  have hderiv : ∀ᵐ t ∂volume.restrict (Ioo (0 : Real) b),
      deriv J t ≤ ((d : Nat) : Real) / t * J t := by
    filter_upwards [ae_restrict_mem measurableSet_Ioo] with t ht
    exact (hrad t ht).2.1
  have hQLw := (MeasureTheory.integrable_ioiPow_iff d QL).mp hQL
  have hQRw := (MeasureTheory.integrable_ioiPow_iff d QR).mp hQR
  have hQL_eq {t : Real} (ht : t ∈ Ioo (0 : Real) b) :
      t ^ d • QL t = J t * deriv ψ t := by
    have htK : (t • u.1 : E) ∈ K := by
      have ht' : t ∈ {s : Real | 0 < s ∧
          (s • (u.1 : TangentSpace I p)) ∈ K} := by
        rw [hsetK]
        exact ht
      exact ht'.2
    have hact := dist_action_scaled (I := I) g hEnorm φ
      (u.1 : TangentSpace I p) hu ht.1 (hseg ht)
    dsimp only at hact
    rw [show QL t = D (t • u.1) *
        tangentSectionAction (I := I) X ρ (γ t) by
      simp only [QL, indicator_of_mem htK, hFγ]]
    change t ^ d * (D (t • u.1) *
      tangentSectionAction (I := I) X ρ (γ t)) = J t * deriv ψ t
    rw [show tangentSectionAction (I := I) X ρ (γ t) =
        L⁻¹ * deriv (fun s : Real ↦ φ (γ s)) t by
      simpa only [X, ρ, γ, L] using hact]
    rw [hψderiv]
    calc
      t ^ d * (D (t • u.1) *
          (L⁻¹ * deriv (fun s : Real ↦ φ (γ s)) t)) =
          (D (t • u.1) * t ^ d) *
            (L⁻¹ * deriv (fun s : Real ↦ φ (γ s)) t) := by ring
      _ = J t * (L⁻¹ * deriv (fun s : Real ↦ φ (γ s)) t) := by
        rw [(hrad t ht).2.2]
  have hQR_eq {t : Real} (ht : t ∈ Ioo (0 : Real) b) :
      t ^ d • QR t = ((d : Nat) : Real) / t * J t * ψ t := by
    have htK : (t • u.1 : E) ∈ K := by
      have ht' : t ∈ {s : Real | 0 < s ∧
          (s • (u.1 : TangentSpace I p)) ∈ K} := by
        rw [hsetK]
        exact ht
      exact ht'.2
    rw [show QR t = D (t • u.1) *
        (((d : Nat) : Real) / ρ (γ t) * φ (γ t)) by
      simp only [QR, indicator_of_mem htK, hFγ]]
    change t ^ d * (D (t • u.1) *
      (((d : Nat) : Real) / ρ (γ t) * φ (γ t))) = _
    rw [hρeq ht]
    simp only [ψ]
    rw [show t ^ d * (D (t • u.1) *
        (((d : Nat) : Real) / (t * L) * φ (γ t))) =
      (D (t • u.1) * t ^ d) *
        (((d : Nat) : Real) / (t * L) * φ (γ t)) by ring]
    rw [(hrad t ht).2.2]
    field_simp [ht.1.ne', hL.ne']
  have hLint : IntegrableOn (fun t : Real ↦ J t * deriv ψ t)
      (Ioo (0 : Real) b) :=
    (hQLw.mono_set Ioo_subset_Ioi_self).congr_fun
      (fun t ht ↦ hQL_eq ht) measurableSet_Ioo
  have hRint : IntegrableOn
      (fun t : Real ↦ ((d : Nat) : Real) / t * J t * ψ t)
      (Ioo (0 : Real) b) :=
    (hQRw.mono_set Ioo_subset_Ioi_self).congr_fun
      (fun t ht ↦ hQR_eq ht) measurableSet_Ioo
  have hweighted := neg_integral_mul_deriv_le_of_locally_absolutely_continuous
    ha₀ ha₀b hJ_ac hψ_ac hψzero hbdry
    hψ0 hderiv hLint hRint
  rw [MeasureTheory.integral_ioiPow d QL,
    MeasureTheory.integral_ioiPow d QR]
  have hQLint : (∫ t in Ioi (0 : Real), t ^ d • QL t) =
      ∫ t in Ioo (0 : Real) b, J t * deriv ψ t := by
    calc
      (∫ t in Ioi (0 : Real), t ^ d • QL t) =
          ∫ t in Ioo (0 : Real) b, t ^ d • QL t := by
        apply setIntegral_eq_of_subset_of_forall_sdiff_eq_zero measurableSet_Ioi
          Ioo_subset_Ioi_self
        intro t ht
        have htK : (t • u.1 : E) ∉ K := by
          intro htK
          apply ht.2
          rw [← hsetK]
          exact ⟨ht.1, htK⟩
        simp only [QL, indicator_of_notMem htK, smul_zero]
      _ = _ := setIntegral_congr_fun measurableSet_Ioo
        (fun t ht ↦ hQL_eq ht)
  have hQRint : (∫ t in Ioi (0 : Real), t ^ d • QR t) =
      ∫ t in Ioo (0 : Real) b,
        ((d : Nat) : Real) / t * J t * ψ t := by
    calc
      (∫ t in Ioi (0 : Real), t ^ d • QR t) =
          ∫ t in Ioo (0 : Real) b, t ^ d • QR t := by
        apply setIntegral_eq_of_subset_of_forall_sdiff_eq_zero measurableSet_Ioi
          Ioo_subset_Ioi_self
        intro t ht
        have htK : (t • u.1 : E) ∉ K := by
          intro htK
          apply ht.2
          rw [← hsetK]
          exact ⟨ht.1, htK⟩
        simp only [QR, indicator_of_notMem htK, smul_zero]
      _ = _ := setIntegral_congr_fun measurableSet_Ioo
        (fun t ht ↦ hQR_eq ht)
  rw [hQLint, hQRint]
  exact hweighted

omit [NeZero (Module.finrank Real E)] [CompleteSpace E]
  [T2Space (TangentBundle I M)] in
theorem dist_gradient_pairing_le
    [PseudoEMetricSpace M] [IsRiemannianManifold I M] [CompleteSpace M]
    [IsContinuousRiemannianBundle E (fun x : M ↦ TangentSpace I x)]
    (g : SmoothRiemannianMetric I M)
    (hEnorm : IsMetricNorm (I := I) (M := M) g)
    (p : M) (hd : 0 < Module.finrank Real E - 1)
    (hRic : RicciBoundedBelow (I := I) g 0)
    (φ : C^∞⟮I, M; Real⟯)
    (hφ : φ ∈ compactlySupportedSmoothFunctions I M)
    (hφp : tsupport (φ : M → Real) ⊆ ({p}ᶜ : Set M))
  (hφ0 : ∀ y : M, 0 ≤ φ y) :
    let d : Nat := Module.finrank Real E - 1
    let ρ : M → Real := fun y ↦ (riemannianEDist I p y).toReal
    let X : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯ :=
      gradG (I := I) g φ
    (-(∫ y, tangentSectionAction (I := I) X ρ y
        ∂(riemannianVolumeMeasure (I := I) (M := M) g)) ≤
      ∫ y, ((d : Nat) : Real) / ρ y * φ y
        ∂(riemannianVolumeMeasure (I := I) (M := M) g)) := by
  classical
  let _ : NeZero (Module.finrank Real E) := ⟨by omega⟩
  let _ : CompleteSpace E := FiniteDimensional.complete Real E
  let _ : T2Space (TangentBundle I M) := inferInstance
  let : Nontrivial E := Module.nontrivial_of_finrank_pos
    (Nat.pos_of_ne_zero (NeZero.ne (Module.finrank Real E)))
  let d : Nat := Module.finrank Real E - 1
  let ρ : M → Real := fun y ↦ (riemannianEDist I p y).toReal
  let X : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯ :=
    gradG (I := I) g φ
  dsimp only
  obtain ⟨a, R, ha, haR, hφann⟩ :=
    exists_dist_bounds_on_tsupport (I := I) p φ hφ hφp
  let S : Real := R + 1
  have hR : 0 < R := ha.trans_le haR
  have hS : 0 < S := hR.trans (lt_add_one R)
  have hφa : ∀ y ∈ tsupport (φ : M → Real),
      a ≤ (riemannianEDist I p y).toReal := fun y hy ↦ (hφann y hy).1
  have hφS : ∀ y ∈ tsupport (φ : M → Real),
      (riemannianEDist I p y).toReal < S := fun y hy ↦
    (hφann y hy).2.trans_lt (lt_add_one R)
  have hsupp := pair_support_ball (I := I) g p φ ((d : Nat) : Real) S hS hφS
  dsimp only at hsupp
  have hA : Integrable (tangentSectionAction (I := I) X ρ)
      (riemannianVolumeMeasure (I := I) (M := M) g) := by
    simpa only [X, ρ] using (dist_green_identity (I := I) g hEnorm p φ hφ).1
  have hB : Integrable (fun y : M ↦ ((d : Nat) : Real) / ρ y * φ y)
      (riemannianVolumeMeasure (I := I) (M := M) g) := by
    simpa only [d, ρ] using
      dist_rhs_int (I := I) g p φ hφ hφp ((d : Nat) : Real)
  let K : Set E :=
    SegmentInt (I := I) g
      (show ∀ (y : M) (w : TangentSpace I y),
        ‖w‖ₑ = ENNReal.ofReal (Real.sqrt (g.inner y w w)) from hEnorm) p ∩
      gBall (I := I) g p S
  let F : E → M := fun v ↦ expMapIntrinsic (I := I) g hEnorm p
    (show TangentSpace I p from v)
  let D : E → Real := fun v ↦ expJacobianDensity (I := I) g hEnorm p v
  let A : E → Real := fun v ↦ D v *
    tangentSectionAction (I := I) X ρ (F v)
  let B : E → Real := fun v ↦ D v *
    (((d : Nat) : Real) / ρ (F v) * φ (F v))
  have hK : MeasurableSet K :=
    (measurableSet_segmentInt (I := I) g hEnorm p).inter
      (measurableSet_gBall (I := I) g p S)
  have hinj : Set.InjOn F K :=
    (exp_inj_segmentInt (I := I) g hEnorm p).mono inter_subset_left
  have hAon : IntegrableOn A K (modelHaar (E := E)) := by
    simpa only [A, D, F] using
      expJac_integrable (I := I) g hEnorm p hK hinj
        (tangentSectionAction (I := I) X ρ) hA.integrableOn
  have hBon : IntegrableOn B K (modelHaar (E := E)) := by
    simpa only [B, D, F] using
      expJac_integrable (I := I) g hEnorm p hK hinj
        (fun y : M ↦ ((d : Nat) : Real) / ρ y * φ y) hB.integrableOn
  have hAI : Integrable (K.indicator A) (modelHaar (E := E)) :=
    hAon.integrable_indicator hK
  have hBI : Integrable (K.indicator B) (modelHaar (E := E)) :=
    hBon.integrable_indicator hK
  have hPA := MeasureTheory.integrable_polar_prod
    (modelHaar (E := E)) (K.indicator A) hAI
  have hPB := MeasureTheory.integrable_polar_prod
    (modelHaar (E := E)) (K.indicator B) hBI
  have hpolarA :
      (∫ y, tangentSectionAction (I := I) X ρ y
          ∂(riemannianVolumeMeasure (I := I) (M := M) g)) =
        ∫ u : Metric.sphere (0 : E) 1,
          ∫ r : Ioi (0 : Real), K.indicator A (r.1 • u.1)
            ∂(Measure.volumeIoiPow d) ∂(modelHaar (E := E)).toSphere := by
    calc
      _ = ∫ y in F '' K, tangentSectionAction (I := I) X ρ y
          ∂(riemannianVolumeMeasure (I := I) (M := M) g) := by
        simpa only [K, A, D, F, d] using
          integral_eq_segmentBall_image (I := I) g hEnorm p hS
            (tangentSectionAction (I := I) X ρ) hsupp.1
      _ = _ := by
        dsimp only [K, A, D, F, d]
        exact segBall_int_polar (I := I) g hEnorm p S
          (tangentSectionAction (I := I) X ρ) hA.integrableOn
  have hpolarB :
      (∫ y, ((d : Nat) : Real) / ρ y * φ y
          ∂(riemannianVolumeMeasure (I := I) (M := M) g)) =
        ∫ u : Metric.sphere (0 : E) 1,
          ∫ r : Ioi (0 : Real), K.indicator B (r.1 • u.1)
            ∂(Measure.volumeIoiPow d) ∂(modelHaar (E := E)).toSphere := by
    calc
      _ = ∫ y in F '' K, ((d : Nat) : Real) / ρ y * φ y
          ∂(riemannianVolumeMeasure (I := I) (M := M) g) := by
        simpa only [K, B, D, F, d] using
          integral_eq_segmentBall_image (I := I) g hEnorm p hS
            (fun y : M ↦ ((d : Nat) : Real) / ρ y * φ y) hsupp.2
      _ = _ := by
        dsimp only [K, B, D, F, d]
        exact segBall_int_polar (I := I) g hEnorm p S
          (fun y : M ↦ ((d : Nat) : Real) / ρ y * φ y) hB.integrableOn
  have hslices : ∀ᵐ u ∂(modelHaar (E := E)).toSphere,
      -(∫ r : Ioi (0 : Real), K.indicator A (r.1 • u.1)
          ∂(Measure.volumeIoiPow d)) ≤
        ∫ r : Ioi (0 : Real), K.indicator B (r.1 • u.1)
          ∂(Measure.volumeIoiPow d) := by
    filter_upwards [hPA.prod_right_ae, hPB.prod_right_ae] with u huA huB
    have hr := radial_pairing_le (I := I) g hEnorm p φ hd hRic ha hS
      hφa hφ0 u
    dsimp only at hr
    exact hr huA huB
  rw [hpolarA, hpolarB]
  rw [← integral_neg]
  exact integral_mono_ae hPA.integral_prod_left.neg hPB.integral_prod_left hslices

omit [NeZero (Module.finrank Real E)] [CompleteSpace E]
  [T2Space (TangentBundle I M)] in
theorem dist_isLaplacianLEDistributionalOn
    [PseudoEMetricSpace M] [IsRiemannianManifold I M] [CompleteSpace M]
    [IsContinuousRiemannianBundle E (fun x : M ↦ TangentSpace I x)]
    (g : SmoothRiemannianMetric I M)
    (hEnorm : IsMetricNorm (I := I) (M := M) g)
    (p : M) (hd : 0 < Module.finrank Real E - 1)
    (hRic : RicciBoundedBelow (I := I) g 0) :
    let d : Nat := Module.finrank Real E - 1
    let ρ : M → Real := fun y ↦ (riemannianEDist I p y).toReal
    IsLaplacianLEDistributionalOn (I := I) g ρ
      (fun y ↦ ((d : Nat) : Real) / ρ y) ({p}ᶜ : Set M) := by
  let d : Nat := Module.finrank Real E - 1
  let ρ : M → Real := fun y ↦ (riemannianEDist I p y).toReal
  dsimp only
  refine ⟨isOpen_compl_singleton, ?_, ?_, ?_⟩
  · exact (locallyIntegrable_dist (I := I) g p).locallyIntegrableOn ({p}ᶜ : Set M)
  · simpa only [d, ρ] using
      locallyIntegrableOn_inv_dist (I := I) g p ((d : Nat) : Real)
  · intro φ hφ hφp hφ0
    rw [(dist_green_identity (I := I) g hEnorm p φ hφ).2]
    simpa only [d, ρ] using
      dist_gradient_pairing_le (I := I) g hEnorm p hd hRic φ hφ hφp hφ0

end DifferentialGeometry.Geometry.Riemannian
