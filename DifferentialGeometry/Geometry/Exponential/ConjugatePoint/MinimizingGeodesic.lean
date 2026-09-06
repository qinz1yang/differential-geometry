import DifferentialGeometry.Geometry.Exponential.Variation.Radial
import DifferentialGeometry.Geometry.Comparison.Variation.SecondVariation.NegativeDirection

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
  have hJ0 : J 0 = 0 := by
    let A : E →L[ℝ] E := mfderiv 𝓘(ℝ, E) I
      (fun v : E => expMap (I := I) g p (show TangentSpace I p from v)) ((0 : ℝ) • u)
    have hr : (Jr 0 : E) = A ((0 : ℝ) • z) :=
      radialJacobiField_eq_mfderiv_expMap (I := I) g p u z 0 (hseg' h0)
    have hA : A ((0 : ℝ) • z) = 0 :=
      (congrArg A (zero_smul ℝ z)).trans A.map_zero
    exact (hJeq 0 h0).eq_of_nhds.trans (hr.trans hA)
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

end DifferentialGeometry.Geometry.Riemannian.Exponential
