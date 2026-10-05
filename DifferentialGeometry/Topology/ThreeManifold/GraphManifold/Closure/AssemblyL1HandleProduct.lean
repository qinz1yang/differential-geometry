import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Closure.AssemblyL1HandleProductProfile
import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Closure.AssemblyL1HandleProductMap

/-!
# Chapter-14 assembly, item L1, step T2′: a handle in product form is reparametrized explicitly

Lanes ASM-L1b2 / ASM-L1b3. Statement frozen in `build-logs/scratch/ASM-L1b/Shortcut.lean` (verbatim).

If both necks of a handle `H` are, on the handle side (`0 ≤ τ < 2ε`), the handle map composed with
`z ↦ A_b (P_b (‖z‖²) • z)` (a linear isometry times a radial profile) in the disk and a monotone
height profile `T_b` in the height, and `det A₀ = det A₁`, then `h := H.map ∘ R` with
`R (z, t) = (A₀ R_{β t α} (P_{β t} (‖z‖²) • z), φ t)` is a reparametrization of the handle that
agrees with the necks near both ends:
* `α` is the angle of the rotation `A₀⁻¹ A₁` (determinant `1`, `exists_handlePlaneRot_eq`);
* `β = handleStep (2ε) (1 - 2ε)` switches from `0` to `1` in the middle of the handle;
* `φ` is the height profile of `exists_handleHeight` (`T₀` near `0`, `1 - T₁ (1 - ·)` near `1`);
* `R` is the lift of the ambient map `handleProductMap` (`AssemblyL1HandleProductMap`): smooth, of
  bijective differential, a bijection of `ClosedCell 2 × Icc 0 1`.
-/

set_option autoImplicit false

noncomputable section

open Set Function Metric
open DifferentialGeometry DifferentialGeometry.Topology GC.Endpoint GC.Seifert GC.GraphManifold Manifold
open scoped Manifold ContDiff Topology

universe u

namespace GC.GraphManifold.Assembly

local instance diskCharts_ASML1b3H : ChartedSpace (EuclideanHalfSpace 2) (ClosedCell 2) :=
  DifferentialGeometry.Topology.Handle.closedCellChartedSpaceSucc 1

local instance diskSmooth_ASML1b3H : IsManifold (𝓡∂ 2) ∞ (ClosedCell 2) :=
  DifferentialGeometry.Topology.Handle.closedCellIsManifold 1

/-- The isometry `A₀⁻¹ A₁` between two linear isometries of `ℝ²` of equal determinant has
determinant `1`. -/
theorem det_trans_symm_eq_one {A₀ A₁ : EuclideanSpace ℝ (Fin 2) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin 2)}
    (hA : LinearMap.det A₀.toLinearMap = LinearMap.det A₁.toLinearMap) :
    LinearMap.det (A₁.trans A₀.symm).toLinearMap = 1 := by
  have e : (A₁.trans A₀.symm).toLinearMap = A₀.symm.toLinearMap ∘ₗ A₁.toLinearMap := rfl
  have e' : A₀.symm.toLinearMap ∘ₗ A₀.toLinearMap = LinearMap.id := by
    ext x
    simp
  rw [e, LinearMap.det_comp, ← hA, ← LinearMap.det_comp, e', LinearMap.det_id]

/-- **T2′ (handle ends, product form).** If both necks are, on the handle side, the handle map
composed with a product `z ↦ A_b (P_b (‖z‖²) • z)` (linear isometry times a radial profile) and a
monotone height profile `T_b`, with `det A₀ = det A₁`, the handle is reparametrized explicitly:
`(z, t) ↦ (A_t (P_t (‖z‖²) • z), φ t)`. -/
theorem EdgeHandle.exists_reparam_eq_necks_of_product {W : CompactCarrier.{u}} (H : EdgeHandle W)
    {ε : ℝ} (hε : 0 < ε) (hε' : ε ≤ 1 / 8)
    (N : Bool → PartialDiffeomorph 𝓘(ℝ, EuclideanSpace ℝ (Fin 2) × ℝ) W.model
      (EuclideanSpace ℝ (Fin 2) × ℝ) W.Carrier ∞)
    (A : Bool → EuclideanSpace ℝ (Fin 2) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin 2))
    (hA : LinearMap.det (A false).toLinearMap = LinearMap.det (A true).toLinearMap)
    (P T : Bool → ℝ → ℝ) (hP : ∀ b, ContDiff ℝ ∞ (P b)) (hT : ∀ b, ContDiff ℝ ∞ (T b))
    (hP1 : ∀ b, P b 1 = 1) (hPpos : ∀ b s, 0 ≤ s → s ≤ 1 → 0 < P b s)
    (hPmono : ∀ b r, 0 ≤ r → r ≤ 1 → 0 < deriv (fun r : ℝ => r * P b (r ^ 2)) r)
    (hT0 : ∀ b, T b 0 = 0) (hTmono : ∀ b s, 0 ≤ s → s ≤ 2 * ε → 0 < deriv (T b) s)
    (hTsep : T false (2 * ε) < 1 - T true (2 * ε))
    (hprod : ∀ b (z : ClosedCell 2) (τ : ℝ) (w : ClosedCell 2) (t : Icc (0 : ℝ) 1),
      0 ≤ τ → τ < 2 * ε →
      (w : EuclideanSpace ℝ (Fin 2)) = A b (P b (‖(z : EuclideanSpace ℝ (Fin 2))‖ ^ 2) • z) →
      (t : ℝ) = endCoord b (T b τ) → N b ((z : EuclideanSpace ℝ (Fin 2)), τ) = H.map (w, t)) :
    ∃ h : ClosedCell 2 × Icc (0 : ℝ) 1 → W.Carrier,
      ContMDiff ((𝓡∂ 2).prod (𝓡∂ 1)) W.model ∞ h ∧
      (∀ q, Bijective (mfderiv ((𝓡∂ 2).prod (𝓡∂ 1)) W.model h q)) ∧ Injective h ∧
      range h = range H.map ∧ (∀ b, h '' {q | q.2 = iccEnd b} = H.endDisk b) ∧
      ∀ b (q : ClosedCell 2 × Icc (0 : ℝ) 1), |(q.2 : ℝ) - (iccEnd b : ℝ)| < 2 * ε →
        h q = N b (handleEnd b q) := by
  -- the rotation angle of `A₀⁻¹ A₁`
  obtain ⟨α, hα⟩ := exists_handlePlaneRot_eq ((A true).trans (A false).symm)
    (det_trans_symm_eq_one hA)
  -- the step and the height profile
  have h2ε : 2 * ε < 1 - 2 * ε := by linarith
  obtain ⟨φ, hφ, hφd, hφ0, hφ1⟩ := exists_handleHeight (a := 2 * ε) (by linarith) (by linarith)
    (hT false) (hT true) (fun s hs => hTmono false s hs.1 hs.2)
    (fun s hs => hTmono true s hs.1 hs.2) hTsep
  have hφzero : φ 0 = 0 := by rw [hφ0 0 (by linarith), hT0]
  have hφone : φ 1 = 1 := by rw [hφ1 1 (by linarith), sub_self, hT0, sub_zero]
  have hφmono : StrictMonoOn φ (Icc 0 1) := by
    apply strictMonoOn_of_deriv_pos (convex_Icc 0 1) hφ.continuous.continuousOn
    intro t ht
    rw [interior_Icc] at ht
    exact hφd t (Ioo_subset_Icc_self ht)
  have hφmaps : MapsTo φ (Icc 0 1) (Icc 0 1) := by
    intro t ht
    have h0 := hφmono.monotoneOn ⟨le_rfl, zero_le_one⟩ ht ht.1
    have h1 := hφmono.monotoneOn ht ⟨zero_le_one, le_rfl⟩ ht.2
    rw [hφzero] at h0
    rw [hφone] at h1
    exact ⟨h0, h1⟩
  -- the ambient map and its lift
  set β := handleStep (2 * ε) (1 - 2 * ε) with hβdef
  set F := handleProductMap (A false) α (P false) (P true) β φ with hFdef
  have hFs : ContDiff ℝ ∞ F :=
    contDiff_handleProductMap (A false) α (hP false) (hP true) (contDiff_handleStep _ _) hφ
  have hF : MapsTo F (closedBall 0 1 ×ˢ Icc 0 1) (closedBall 0 1 ×ˢ Icc 0 1) :=
    handleProductMap_mapsTo (A false) α (hP false) (hP true) (hP1 false) (hP1 true)
      (hPpos false) (hPpos true) (hPmono false) (hPmono true) (handleStep_nonneg _ _)
      (handleStep_le_one _ _) hφmaps
  set R := handleLift F hF with hRdef
  have hRs : ContMDiff ((𝓡∂ 2).prod (𝓡∂ 1)) ((𝓡∂ 2).prod (𝓡∂ 1)) ∞ R :=
    contMDiff_handleLift hF hFs
  have hRsurj : Surjective R :=
    surjective_handleLift hF (handleProductMap_surjOn (A false) α (hP false) (hP true)
      (hP1 false) (hP1 true) hφ.continuous.continuousOn hφzero hφone)
  have hRinj : Injective R :=
    injective_handleLift hF (handleProductMap_injOn (A false) α (hP false) (hP true)
      (hPpos false) (hPpos true) (hPmono false) (hPmono true) (handleStep_nonneg _ _)
      (handleStep_le_one _ _) hφmono)
  have hR1 : ∀ q, ((R q).1 : EuclideanSpace ℝ (Fin 2)) =
      A false (handlePlaneRot (β q.2 * α) (handleProfileMix (P false) (P true) (β q.2)
        (‖(q.1 : EuclideanSpace ℝ (Fin 2))‖ ^ 2) • (q.1 : EuclideanSpace ℝ (Fin 2)))) :=
    fun _ => rfl
  have hR2 : ∀ q, ((R q).2 : ℝ) = φ q.2 := fun _ => rfl
  refine ⟨H.map ∘ R, H.smooth.comp hRs, ?_, H.injective.comp hRinj, hRsurj.range_comp _, ?_, ?_⟩
  · -- the differential
    intro q
    rw [mfderiv_comp q (H.smooth.mdifferentiableAt (by simp)) (hRs.mdifferentiableAt (by simp))]
    exact (H.mfderiv_bijective (R q)).comp (bijective_mfderiv_handleLift hF hFs q
      (bijective_fderiv_handleProductMap (A false) α (hP false) (hP true) (hPpos false)
        (hPpos true) (hPmono false) (hPmono true) (contDiff_handleStep _ _) hφ
        (mem_closedBall_zero_iff.mp (handleVal_mem q).1) (handleStep_nonneg _ _ _)
        (handleStep_le_one _ _ _) (hφd _ q.2.2).ne'))
  · -- the end disks
    intro b
    have hφe : φ (iccEnd b : ℝ) = iccEnd b := by
      cases b
      · exact hφzero
      · exact hφone
    have hS : R '' {q | q.2 = iccEnd b} = {q | q.2 = iccEnd b} := by
      ext q
      constructor
      · rintro ⟨q', hq', rfl⟩
        apply Subtype.ext
        rw [hR2, show q'.2 = iccEnd b from hq', hφe]
      · intro hq
        obtain ⟨q', rfl⟩ := hRsurj q
        refine ⟨q', ?_, rfl⟩
        apply Subtype.ext
        apply hφmono.injOn q'.2.2 (iccEnd b).2
        rw [← hR2, show (R q').2 = iccEnd b from hq, hφe]
    rw [image_comp, hS]
    ext x
    constructor
    · rintro ⟨⟨q1, q2⟩, hq, rfl⟩
      change q2 = iccEnd b at hq
      subst hq
      exact ⟨q1, rfl⟩
    · rintro ⟨x, rfl⟩
      exact ⟨(x, iccEnd b), rfl, rfl⟩
  · -- the two ends
    intro b q hq
    cases b
    · have h0 : ((iccEnd false : Icc (0 : ℝ) 1) : ℝ) = 0 := rfl
      rw [h0, sub_zero] at hq
      have ht : (q.2 : ℝ) < 2 * ε := (abs_lt.mp hq).2
      have hβq : β q.2 = 0 := handleStep_of_le h2ε ht.le
      have he : handleEnd false q = ((q.1 : EuclideanSpace ℝ (Fin 2)), (q.2 : ℝ)) := by
        simp [handleEnd, endCoord]
      rw [comp_apply, he]
      refine (hprod false q.1 q.2 (R q).1 (R q).2 q.2.2.1 ht ?_ ?_).symm
      · rw [hR1, hβq, zero_mul, handlePlaneRot_zero, handleProfileMix, sub_zero, one_mul,
          zero_mul, add_zero]
      · rw [hR2, hφ0 _ ht.le]
        simp [endCoord]
    · have h1 : ((iccEnd true : Icc (0 : ℝ) 1) : ℝ) = 1 := rfl
      rw [h1] at hq
      have ht : 1 - 2 * ε < (q.2 : ℝ) := by linarith [(abs_lt.mp hq).1]
      have hβq : β q.2 = 1 := handleStep_of_ge h2ε ht.le
      have he : handleEnd true q = ((q.1 : EuclideanSpace ℝ (Fin 2)), 1 - (q.2 : ℝ)) := by
        simp [handleEnd, endCoord]
      rw [comp_apply, he]
      refine (hprod true q.1 (1 - q.2) (R q).1 (R q).2 (by linarith [q.2.2.2]) (by linarith)
        ?_ ?_).symm
      · rw [hR1, hβq, one_mul, ← hα, handleProfileMix, sub_self, zero_mul, zero_add, one_mul,
          LinearIsometryEquiv.trans_apply, LinearIsometryEquiv.apply_symm_apply]
      · rw [hR2, hφ1 _ ht.le]
        simp [endCoord]

end GC.GraphManifold.Assembly
