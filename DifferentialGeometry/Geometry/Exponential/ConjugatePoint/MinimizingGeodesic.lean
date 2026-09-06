import DifferentialGeometry.Geometry.Exponential.Variation.Radial
import DifferentialGeometry.Geometry.Comparison.Variation.SecondVariation.NegativeDirection
import DifferentialGeometry.Geometry.Comparison.Variation.Curve.PathLength

set_option autoImplicit false

open Set Filter Manifold Bundle
open scoped Topology ContDiff Manifold

namespace DifferentialGeometry.Geometry.Riemannian.Exponential

open VolumeComparison Variation Geodesic CovariantDerivativeAlong

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [T2Space M]

theorem injective_mfderiv_expMap_of_minimising_geodesic
    (g : SmoothRiemannianMetric I M) (p : M) (u : E) {L c : ℝ}
    (hunit : g.inner p u u = 1)
    (hdom : (show TangentSpace I p from L • u) ∈ expDomain (I := I) g p)
    (hmin : ∀ η : ℝ → M, ContMDiffOn 𝓘(ℝ, ℝ) I 1 η (Icc 0 L) →
      η 0 = p → η L = expMap (I := I) g p (show TangentSpace I p from L • u) →
      arcLength (I := I) g
        (fun t => expMap (I := I) g p (show TangentSpace I p from t • u)) 0 L ≤
          arcLength (I := I) g η 0 L)
    (hc : c ∈ Ioo (0 : ℝ) L) :
    Function.Injective (mfderiv 𝓘(ℝ, E) I
      (fun v : E => expMap (I := I) g p (show TangentSpace I p from v)) (c • u)) := by
  classical
  rw [injective_iff_map_eq_zero]
  intro z hz
  change E at z
  by_contra hzne
  have hL : 0 < L := hc.1.trans hc.2
  have h0 : (0 : ℝ) ∈ Icc (0 : ℝ) L := ⟨le_rfl, hL.le⟩
  have hcc : c ∈ Icc (0 : ℝ) L := Ioo_subset_Icc_self hc
  let U : Set ℝ := {t | (show TangentSpace I p from t • u) ∈ expDomain (I := I) g p}
  have hU : IsOpen U := by
    have hopen : IsOpen {v : E | (show TangentSpace I p from v) ∈ expDomain (I := I) g p} :=
      isOpen_expDomain (I := I) g p
    exact hopen.preimage (continuous_id.smul (continuous_const : Continuous (fun _ : ℝ => u)))
  obtain ⟨η, S, hS, hconn, h0S, hLS, hη⟩ := smul_mem_expDomain_iff.mp hdom
  have hseg : uIcc (0 : ℝ) L ⊆ U := by
    intro t ht
    exact smul_mem_expDomain_iff.mpr
      ⟨η, S, hS, hconn, h0S, hconn.ordConnected.uIcc_subset h0S hLS ht, hη⟩
  have hseg' : Icc (0 : ℝ) L ⊆ U := by
    simpa only [uIcc_of_le hL.le] using hseg
  let γr : ℝ → M := fun t => expMap (I := I) g p (show TangentSpace I p from t • u)
  let Jr := radialJacobiField (I := I) g p u z
  have hJr : ContMDiffOn 𝓘(ℝ, ℝ) I.tangent (⊤ : ℕ∞)
      (fun t => (TotalSpace.mk' E (γr t) (Jr t) : TangentBundle I M)) U := by
    intro t ht
    exact (contMDiffAt_radialJacobiField (I := I) g p u z ht).contMDiffWithinAt
  obtain ⟨B, hB, hBeq⟩ := hJr.exists_extension_uIcc hU hseg
  let γ : ℝ → M := fun t => (B t).proj
  let J : ∀ t, TangentSpace I (γ t) := fun t => (B t).snd
  have hγ : ContMDiff 𝓘(ℝ, ℝ) I ∞ γ :=
    (Bundle.contMDiff_proj (TangentSpace I)).comp hB
  have hJ : ContMDiff 𝓘(ℝ, ℝ) I.tangent ∞
      (fun t => (TotalSpace.mk' E (γ t) (J t) : TangentBundle I M)) := hB
  have hfield t (ht : t ∈ Icc (0 : ℝ) L) :
      (fun r => (TotalSpace.mk' E (γ r) (J r) : TangentBundle I M)) =ᶠ[𝓝 t]
        (fun r => (TotalSpace.mk' E (γr r) (Jr r) : TangentBundle I M)) :=
    hBeq t (by simpa only [uIcc_of_le hL.le] using ht)
  have hγeq t (ht : t ∈ Icc (0 : ℝ) L) : γ =ᶠ[𝓝 t] γr := by
    filter_upwards [hfield t ht] with r hr
    exact congrArg TotalSpace.proj hr
  have hJeq t (ht : t ∈ Icc (0 : ℝ) L) :
      (fun r => (J r : E)) =ᶠ[𝓝 t] (fun r => (Jr r : E)) := by
    filter_upwards [hfield t ht] with r hr
    exact congrArg (fun b : TangentBundle I M => (b.snd : E)) hr
  have hgeo : IsGeodesicOn (I := I) g γ (Icc 0 L) := by
    intro t ht
    exact HasGeodesicEquationAt.congr_of_eventuallyEq_at (hγeq t ht).eq_of_nhds
      (hγeq t ht) (hasGeodesicEquationAt_expMap_smul (I := I) g p u (hseg' ht))
  have hJac t (ht : t ∈ Ioo (0 : ℝ) L) : IsJacobiAt (I := I) g γ J t :=
    (isJacobiAt_radialJacobiField (I := I) g p u z
      (hseg' (Ioo_subset_Icc_self ht))).congr_of_eventuallyEq
        (hfield t (Ioo_subset_Icc_self ht)).symm
  have hγ0 : γ 0 = p := by
    rw [(hγeq 0 h0).eq_of_nhds]
    simp only [γr, zero_smul]
    exact expMap_zero (I := I) g p
  have hvel0 : (curveVelocity (I := I) γ 0 : E) = u :=
    (congrArg (fun A : ℝ →L[ℝ] E => A (1 : ℝ)) (hγeq 0 h0).mfderiv_eq).trans
      (radialCurve_launch_velocity (I := I) g p u)
  have hunit0 : g.inner (γ 0) (curveVelocity (I := I) γ 0)
      (curveVelocity (I := I) γ 0) = 1 := by
    rw [hvel0, hγ0]
    exact hunit
  have hJ0 : J 0 = 0 :=
    (hJeq 0 h0).eq_of_nhds.trans (radialJacobiField_zero (I := I) g p u z)
  have hJc : J c = 0 := by
    let A : E →L[ℝ] E := mfderiv 𝓘(ℝ, E) I
      (fun v : E => expMap (I := I) g p (show TangentSpace I p from v)) (c • u)
    have hr : (Jr c : E) = A (c • z) :=
      radialJacobiField_eq_mfderiv_expMap (I := I) g p u z c (hseg' hcc)
    have hz' : A z = 0 := hz
    have hA : A (c • z) = 0 :=
      (A.map_smul c z).trans ((congrArg (fun v : E => c • v) hz').trans (smul_zero c))
    exact (hJeq c hcc).eq_of_nhds.trans (hr.trans hA)
  have hDJ0 : covDerivAlong (I := I) g γ J 0 ≠ 0 := by
    have hD : (covDerivAlong (I := I) g γ J 0 : E) = z :=
      (covDerivAlong_congr_curve (I := I) g J Jr (hγeq 0 h0) (hJeq 0 h0)).trans
        (covDerivAlong_radialJacobiField_zero (I := I) g p u z)
    intro hzero
    exact hzne (hD.symm.trans hzero)
  have hlen : arcLength (I := I) g γ 0 L = arcLength (I := I) g γr 0 L := by
    unfold arcLength
    apply intervalIntegral.integral_congr
    intro t ht
    have hev := hγeq t (by simpa only [uIcc_of_le hL.le] using ht)
    change Real.sqrt (g.inner (γ t) (mfderiv 𝓘(ℝ, ℝ) I γ t (1 : ℝ))
        (mfderiv 𝓘(ℝ, ℝ) I γ t (1 : ℝ))) =
      Real.sqrt (g.inner (γr t) (mfderiv 𝓘(ℝ, ℝ) I γr t (1 : ℝ))
        (mfderiv 𝓘(ℝ, ℝ) I γr t (1 : ℝ)))
    rw [hev.eq_of_nhds, hev.mfderiv_eq]
  have hminγ : ∀ η : ℝ → M, ContMDiffOn 𝓘(ℝ, ℝ) I 1 η (Icc 0 L) →
      η 0 = γ 0 → η L = γ L → arcLength (I := I) g γ 0 L ≤ arcLength (I := I) g η 0 L := by
    intro η hη hη0 hηL
    rw [hlen]
    exact hmin η hη (hη0.trans hγ0)
      (hηL.trans (hγeq L ⟨hL.le, le_rfl⟩).eq_of_nhds)
  exact jacobi_field_ne_zero_of_minimising_geodesic (I := I) g γ J hγ
    hJ.contMDiffOn isOpen_univ (subset_univ _) hgeo hJac hunit0 hminγ hc hJ0 hDJ0 hJc

section ENorm

variable [(y : M) → ENorm (TangentSpace I y)]

theorem injective_mfderiv_expMap_of_le_riemannianEDist
    (g : SmoothRiemannianMetric I M)
    (hEnorm : ∀ (y : M) (v : TangentSpace I y),
      ‖v‖ₑ = ENNReal.ofReal (Real.sqrt (g.inner y v v)))
    (p : M) (x : E)
    (hx : (show TangentSpace I p from x) ∈ expDomain (I := I) g p)
    (hmin : ENNReal.ofReal (Real.sqrt (g.inner p x x)) ≤
      riemannianEDist I p (expMap (I := I) g p (show TangentSpace I p from x)))
    {t : ℝ} (ht : t ∈ Ico (0 : ℝ) 1) :
    Function.Injective (mfderiv 𝓘(ℝ, E) I
      (fun v : E => expMap (I := I) g p (show TangentSpace I p from v)) (t • x)) := by
  classical
  have hzero : Function.Injective (mfderiv 𝓘(ℝ, E) I
      (fun v : E => expMap (I := I) g p (show TangentSpace I p from v)) 0) := by
    rw [mfderiv_expMap_at_zero (I := I) g p]
    exact Function.injective_id
  by_cases hx0 : x = 0
  · have heq : t • x = (0 : E) := by rw [hx0, smul_zero]
    exact (congrArg (fun y : E => Function.Injective (mfderiv 𝓘(ℝ, E) I
      (fun v : E => expMap (I := I) g p (show TangentSpace I p from v)) y)) heq).mpr hzero
  by_cases ht0 : t = 0
  · have heq : t • x = (0 : E) := by rw [ht0, zero_smul]
    exact (congrArg (fun y : E => Function.Injective (mfderiv 𝓘(ℝ, E) I
      (fun v : E => expMap (I := I) g p (show TangentSpace I p from v)) y)) heq).mpr hzero
  let : (y : M) → ENormSMulClass ℝ (TangentSpace I y) := fun y => ⟨fun r v => by
    rw [hEnorm, hEnorm, Real.enorm_eq_ofReal_abs]
    have hscale : g.inner y (r • v) (r • v) = r ^ 2 * g.inner y v v := by
      rw [(g.inner y).map_smul, _root_.smul_apply, (g.inner y v).map_smul]
      simp only [smul_eq_mul]
      ring
    rw [hscale, Real.sqrt_mul (sq_nonneg r), Real.sqrt_sq_eq_abs,
      ENNReal.ofReal_mul (abs_nonneg r)]⟩
  let ℓ : ℝ := Real.sqrt (g.inner p x x)
  have hℓ : 0 < ℓ := Real.sqrt_pos.mpr (g.pos p x hx0)
  have hℓne : ℓ ≠ 0 := hℓ.ne'
  let u : E := ℓ⁻¹ • x
  have hunit : g.inner p u u = 1 := by
    let G : E →L[ℝ] E →L[ℝ] ℝ := g.inner p
    change G (ℓ⁻¹ • x) (ℓ⁻¹ • x) = 1
    rw [G.map_smul, _root_.smul_apply, (G x).map_smul]
    simp only [smul_eq_mul]
    have hsq : G x x = ℓ ^ 2 := (Real.sq_sqrt (g.pos p x hx0).le).symm
    rw [hsq]
    field_simp
  have hlu : ℓ • u = x := by
    simp only [u, smul_smul, mul_inv_cancel₀ hℓne, one_smul]
  have hdom : (show TangentSpace I p from ℓ • u) ∈ expDomain (I := I) g p := by
    simpa only [hlu] using! hx
  have hseg s (hs : s ∈ Icc (0 : ℝ) ℓ) :
      (show TangentSpace I p from s • u) ∈ expDomain (I := I) g p := by
    have hs' : s / ℓ ∈ Icc (0 : ℝ) 1 :=
      ⟨div_nonneg hs.1 hℓ.le, (div_le_one hℓ).mpr hs.2⟩
    have heq : (s / ℓ) • x = s • u := by
      simp only [u, smul_smul, div_eq_mul_inv]
    exact (congrArg (fun v : E => (show TangentSpace I p from v) ∈ expDomain g p)
      heq).mp (smul_mem_expDomain hx hs')
  have hlen : arcLength (I := I) g
      (fun s => expMap (I := I) g p (show TangentSpace I p from s • u)) 0 ℓ = ℓ := by
    unfold arcLength
    calc
      _ = ∫ _s in (0 : ℝ)..ℓ, (1 : ℝ) := by
        apply intervalIntegral.integral_congr
        intro s hs
        have hs' : s ∈ Icc (0 : ℝ) ℓ := by
          simpa only [uIcc_of_le hℓ.le] using hs
        exact (congrArg Real.sqrt
          (inner_curveVelocity_expMap_smul (I := I) g p u (hseg s hs'))).trans
            ((congrArg Real.sqrt hunit).trans Real.sqrt_one)
      _ = ℓ := by simp
  have hminimal : ∀ η : ℝ → M, ContMDiffOn 𝓘(ℝ, ℝ) I 1 η (Icc 0 ℓ) →
      η 0 = p → η ℓ = expMap (I := I) g p (show TangentSpace I p from ℓ • u) →
      arcLength (I := I) g
        (fun s => expMap (I := I) g p (show TangentSpace I p from s • u)) 0 ℓ ≤
          arcLength (I := I) g η 0 ℓ := by
    intro η hη hη0 hηℓ
    rw [hlen]
    have hd := riemannianEDist_le_arcLength_of_enorm_eq (I := I) g hℓ.le hη
      (fun s _ => hEnorm (η s) (mfderiv 𝓘(ℝ, ℝ) I η s (1 : ℝ)))
    have hd' : riemannianEDist I p (expMap (I := I) g p (show TangentSpace I p from x)) ≤
        ENNReal.ofReal (arcLength (I := I) g η 0 ℓ) := by
      simpa only [hη0, hηℓ, hlu] using! hd
    have hn : 0 ≤ arcLength (I := I) g η 0 ℓ := by
      exact intervalIntegral.integral_nonneg hℓ.le (fun _ _ => Real.sqrt_nonneg _)
    exact (ENNReal.ofReal_le_ofReal_iff hn).mp (hmin.trans hd')
  have hc : t * ℓ ∈ Ioo (0 : ℝ) ℓ := by
    constructor
    · exact mul_pos (lt_of_le_of_ne ht.1 (Ne.symm ht0)) hℓ
    · simpa only [one_mul] using mul_lt_mul_of_pos_right ht.2 hℓ
  have hinj := injective_mfderiv_expMap_of_minimising_geodesic
    (I := I) g p u hunit hdom hminimal hc
  have heq : (t * ℓ) • u = t • x := by rw [mul_smul, hlu]
  exact (congrArg (fun y : E => Function.Injective (mfderiv 𝓘(ℝ, E) I
    (fun v : E => expMap (I := I) g p (show TangentSpace I p from v)) y)) heq).mp hinj

end ENorm

end DifferentialGeometry.Geometry.Riemannian.Exponential
