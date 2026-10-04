import
DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Seifert.MoveSplitCappedCollarAdapterScalar
import DifferentialGeometry.Topology.Diffeomorph.Radial
import DifferentialGeometry.Topology.Homeomorph.Ball

/-!
The scalar compression acts on polar radius and extends smoothly across zero because it is the
identity there. The resulting actual plane diffeomorphism preserves the closed radius-three disc.
-/

set_option autoImplicit false

noncomputable section

open Set Metric TopologicalSpace
open DifferentialGeometry
open scoped Manifold ContDiff Topology

namespace GC.Seifert

private local instance : Fact (Module.finrank ℝ ℂ = 1 + 1) := ⟨by simp⟩

private def compressionPositiveRadius (D : ℝ ≃ₘ[ℝ] ℝ) (hm : StrictMono D) (h0 : D 0 = 0) :
    let V : Opens ℝ := ⟨Ioi 0, isOpen_Ioi⟩
    V ≃ₘ⟮𝓘(ℝ, ℝ), 𝓘(ℝ, ℝ)⟯ V :=
  D.restrict (U := ⟨Ioi 0, isOpen_Ioi⟩) (V := ⟨Ioi 0, isOpen_Ioi⟩) (fun r => by
    change 0 < r ↔ 0 < D r
    simpa only [h0] using (hm.lt_iff_lt (a := 0) (b := r)).symm)

private def compressionPunctured (D : ℝ ≃ₘ[ℝ] ℝ) (hm : StrictMono D) (h0 : D 0 = 0) :
    let U : Opens ℂ := ⟨{0}ᶜ, isOpen_compl_singleton⟩
    U ≃ₘ⟮𝓘(ℝ, ℂ), 𝓘(ℝ, ℂ)⟯ U :=
  ((Diffeomorph.unitSphereProd (E := ℂ) (d := 1) ∞).trans
    ((Diffeomorph.refl (𝓡 1) (sphere (0 : ℂ) 1) ∞).prodCongr
      (compressionPositiveRadius D hm h0))).trans
    (Diffeomorph.unitSphereProd (E := ℂ) (d := 1) ∞).symm

private theorem compressionPunctured_apply (D : ℝ ≃ₘ[ℝ] ℝ) (hm : StrictMono D)
    (h0 : D 0 = 0) (z : ({0}ᶜ : Set ℂ)) :
    (compressionPunctured D hm h0 z : ℂ) = D ‖z.val‖ • (‖z.val‖⁻¹ • z.val) := by
  simp only [compressionPunctured, Diffeomorph.coe_trans, Function.comp_apply,
    Diffeomorph.unitSphereProd_symm_apply_val, Diffeomorph.coe_prodCongr,
    Diffeomorph.coe_refl, Prod.map_fst, Prod.map_snd, id_eq,
    compressionPositiveRadius, Diffeomorph.restrict_apply,
    Diffeomorph.unitSphereProd_apply_fst_val, Diffeomorph.unitSphereProd_apply_snd_val]

private theorem compressionPunctured_fixed (D : ℝ ≃ₘ[ℝ] ℝ) (hm : StrictMono D)
    (h0 : D 0 = 0) (hfix : ∀ r, r ≤ 1 → D r = r)
    (z : ({0}ᶜ : Set ℂ)) (hz : ‖z.val‖ ≤ 1) : compressionPunctured D hm h0 z = z := by
  apply Subtype.ext
  rw [compressionPunctured_apply, hfix _ hz]
  exact smul_inv_smul₀ (norm_ne_zero_iff.mpr z.property) z.val

private theorem compressionSupport_subset : {z : ℂ | 1 / 2 ≤ ‖z‖} ⊆ ({0}ᶜ : Set ℂ) := by
  intro z hz
  change z ≠ 0
  intro he
  norm_num [he] at hz

private def compressionAmbient (D : ℝ ≃ₘ[ℝ] ℝ) (hm : StrictMono D)
    (h0 : D 0 = 0) (hfix : ∀ r, r ≤ 1 → D r = r) : ℂ ≃ₘ[ℝ] ℂ :=
  (compressionPunctured D hm h0).extend (C := {z : ℂ | 1 / 2 ≤ ‖z‖})
    (isClosed_le continuous_const continuous_norm) compressionSupport_subset
    (fun z hz => compressionPunctured_fixed D hm h0 hfix z (by
      have h : ‖z.val‖ < 1 / 2 := lt_of_not_ge hz
      linarith))

private theorem compressionAmbient_apply (D : ℝ ≃ₘ[ℝ] ℝ) (hm : StrictMono D)
    (h0 : D 0 = 0) (hfix : ∀ r, r ≤ 1 → D r = r) {z : ℂ} (hz : z ≠ 0) :
    compressionAmbient D hm h0 hfix z = D ‖z‖ • (‖z‖⁻¹ • z) :=
  (Diffeomorph.extend_apply (compressionPunctured D hm h0)
    (isClosed_le continuous_const continuous_norm) compressionSupport_subset
    (fun w hw => compressionPunctured_fixed D hm h0 hfix w (by
      have h : ‖w.val‖ < 1 / 2 := lt_of_not_ge hw
      linarith)) ⟨z, hz⟩).trans (compressionPunctured_apply D hm h0 ⟨z, hz⟩)

private theorem compressionAmbient_fixed (D : ℝ ≃ₘ[ℝ] ℝ) (hm : StrictMono D)
    (h0 : D 0 = 0) (hfix : ∀ r, r ≤ 1 → D r = r) (z : ℂ) (hz : ‖z‖ ≤ 1) :
    compressionAmbient D hm h0 hfix z = z := by
  by_cases hzero : z = 0
  · subst z
    unfold compressionAmbient
    apply Diffeomorph.extend_apply_of_notMem
    norm_num
  · rw [compressionAmbient_apply D hm h0 hfix hzero, hfix _ hz]
    exact smul_inv_smul₀ (norm_ne_zero_iff.mpr hzero) z

theorem exists_ambientCollarCompression {k : ℝ} (hk : 0 < k) (hk1 : k ≤ 1) :
    ∃ R : ℂ ≃ₘ[ℝ] ℂ,
      (∀ z, ‖z‖ ≤ 1 → R z = z) ∧
      (∀ (θ : Circle) (r : ℝ), 3 / 2 ≤ r → r ≤ 3 →
        R (r • (θ : ℂ)) = (3 - k * (3 - r)) • (θ : ℂ)) ∧
      R '' closedBall 0 3 = closedBall 0 3 := by
  obtain ⟨D, hm, hfix, houter⟩ := exists_scalarCollarCompression hk hk1
  have h0 : D 0 = 0 := hfix 0 (by norm_num)
  let R := compressionAmbient D hm h0 hfix
  have hRf : ∀ z, ‖z‖ ≤ 1 → R z = z := compressionAmbient_fixed D hm h0 hfix
  have hRa (z : ℂ) (hz : z ≠ 0) : R z = D ‖z‖ • (‖z‖⁻¹ • z) :=
    compressionAmbient_apply D hm h0 hfix hz
  have hRray (θ : Circle) (r : ℝ) (hr : 3 / 2 ≤ r) (hr3 : r ≤ 3) :
      R (r • (θ : ℂ)) = (3 - k * (3 - r)) • (θ : ℂ) := by
    have hr0 : 0 < r := by linarith
    have hn : ‖r • (θ : ℂ)‖ = r := by
      rw [norm_smul, Circle.norm_coe, mul_one, Real.norm_of_nonneg hr0.le]
    rw [hRa _ (norm_ne_zero_iff.mp (by rw [hn]; exact hr0.ne')), hn, houter r hr hr3,
      inv_smul_smul₀ hr0.ne']
  have hsphere : R '' sphere (0 : ℂ) 3 = sphere (0 : ℂ) 3 := by
    have hsfix (z : ℂ) (hz : z ∈ sphere (0 : ℂ) 3) : R z = z := by
      have hn : ‖z‖ = 3 := by simpa using hz
      rw [hRa z (norm_ne_zero_iff.mp (by rw [hn]; norm_num)), hn,
        houter 3 (by norm_num) le_rfl]
      simp only [sub_self, mul_zero, sub_zero]
      exact smul_inv_smul₀ (by norm_num : (3 : ℝ) ≠ 0) z
    apply Subset.antisymm
    · rintro z ⟨w, hw, rfl⟩
      rwa [hsfix w hw]
    · intro z hz
      exact ⟨z, hz, hsfix z hz⟩
  refine ⟨R, hRf, hRray, ?_⟩
  exact R.toHomeomorph.image_closedBall_of_image_sphere_eq_of_map_center
    (by norm_num) (by norm_num) hsphere (hRf 0 (by norm_num))

end GC.Seifert
