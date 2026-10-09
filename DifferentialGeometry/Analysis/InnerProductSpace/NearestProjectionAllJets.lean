import DifferentialGeometry.Analysis.InnerProductSpace.NearestTangentCorrectionAllJets
import DifferentialGeometry.Analysis.InnerProductSpace.NearestProjectionErrorJets

/-! All finite ambient nearest-error jets with one uniform second-order threshold. -/

set_option autoImplicit false
noncomputable section
open Set Metric Filter
open scoped ContDiff Topology Nat
namespace DifferentialGeometry.Analysis
universe u

theorem exists_uniform_nearest_projection_all_jets
    (F : ℕ → ℝ) (hF : ∀ m, 0 ≤ F m) :
    ∃ C : ℕ → ℝ, (∀ j, 0 ≤ C j) ∧ ∃ δ₀ : ℝ, 0 < δ₀ ∧
      ∀ (H : Type u) [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
        (L : Submodule ℝ H) [CompleteSpace L]
        (o : H) (g : L → Lᗮ) (W : Set H) (P : H → H) (R δ : ℝ),
        0 < R → 0 ≤ δ → δ ≤ δ₀ →
        ContDiffOn ℝ ∞ g (ball (0 : L) (4 * R)) →
        (∀ m i, i ≤ m → ∀ t ∈ ball (0 : L) (4 * R),
          ‖iteratedFDeriv ℝ i g t‖ ≤ F m * δ * R * (R⁻¹) ^ i) →
        (∀ t ∈ ball (0 : L) (4 * R),
          o + orthogonalCoordinateSum L (t, g t) ∈ W) →
        (∀ y ∈ W ∩ ball o (3 * R), ∃ t ∈ ball (0 : L) (4 * R),
          y = o + orthogonalCoordinateSum L (t, g t)) →
        (∀ z ∈ ball o R, P z ∈ W ∧ IsMinOn (fun w => dist z w) W (P z)) →
        ContDiffOn ℝ ∞ P (ball o R) ∧
          ∀ j, ∀ z ∈ ball o R,
            ‖iteratedFDeriv ℝ j (fun y => P y - (o + L.starProjection (y - o))) z‖ ≤
              C j * δ * R * (R⁻¹) ^ j := by
  obtain ⟨B, hB, δt, hδt, hcorrection⟩ :=
    exists_uniform_nearest_tangent_correction_all_jets.{u} F hF
  have hF2 := hF 2
  refine ⟨fun j => B j + (j ! : ℝ) * F j * (max (1 + B j) 1) ^ j,
    (by intro j; have hBj := hB j; have hFj := hF j; positivity),
    min δt (min 1 (1 / (100 * (F 2 + 1)))),
    lt_min hδt (lt_min zero_lt_one (by positivity)), ?_⟩
  intro H _ _ _ L _ o g W P R δ hR hδ0 hδsmall hg hjet hgraph hsheet hnearest
  have hδ1 : δ ≤ 1 := hδsmall.trans ((min_le_right _ _).trans (min_le_left _ _))
  have hden : 0 < 100 * (F 2 + 1) := by positivity
  have hbudget : δ * (100 * (F 2 + 1)) ≤ 1 :=
    (le_div_iff₀ hden).mp (hδsmall.trans ((min_le_right _ _).trans (min_le_right _ _)))
  let a : ℝ := F 2 * δ
  have ha0 : 0 ≤ a := mul_nonneg hF2 hδ0
  have ha : a ≤ 1 / 100 := by dsimp only [a]; nlinarith
  let u : H → L := fun z => L.orthogonalProjectionOnto (z - o)
  let c : H → L := fun z => L.orthogonalProjectionOnto (P z - o) - u z
  let T : H → L := fun z => u z + c z
  obtain ⟨hc, hcjet⟩ := hcorrection H L o g W P R δ hR hδ0
    (hδsmall.trans (min_le_left _ _)) hg hjet hgraph hsheet hnearest
  change ContDiffOn ℝ ∞ c (ball o R) at hc
  change ∀ m, ∀ z ∈ ball o R, ∀ j ≤ m,
    ‖iteratedFDeriv ℝ j c z‖ ≤ B m * δ * R * (R⁻¹) ^ j at hcjet
  have hu : ContDiff ℝ ∞ u :=
    L.orthogonalProjectionOnto.contDiff.comp (contDiff_id.sub contDiff_const)
  have hT : ContDiffOn ℝ ∞ T (ball o R) := hu.contDiffOn.add hc
  have hTproj (z : H) : T z = L.orthogonalProjectionOnto (P z - o) := by
    dsimp only [T, c]
    abel
  have hvalue (t : L) (ht : t ∈ ball (0 : L) (4 * R)) : ‖g t‖ ≤ a * R := by
    simpa only [norm_iteratedFDeriv_zero, pow_zero, mul_one] using hjet 2 0 (by omega) t ht
  have hrepresentation (z : H) (hz : z ∈ ball o R) :
      T z ∈ ball (0 : L) (4 * R) ∧ P z = o + orthogonalCoordinateSum L (T z, g (T z)) := by
    obtain ⟨_, _, t, ht, hrep⟩ := minimizer_mem_buffered_normal_graph L o g W R a
      hR ha hvalue hgraph hsheet z (P z) hz (hnearest z hz).1 (hnearest z hz).2
    have hproj : T z = t := by
      rw [hTproj]
      have hsub : P z - o = (t : H) + (g t : H) := by
        rw [hrep]
        change (o + ((t : H) + (g t : H))) - o = _
        abel
      rw [hsub, map_add, L.orthogonalProjectionOnto_mem_subspace_eq_self,
        Submodule.orthogonalProjectionOnto_apply_of_mem_orthogonal (g t).property, add_zero]
    have ht4 : t ∈ ball (0 : L) (4 * R) := by
      have hh : dist t 0 < 5 * R / 2 := ht
      change dist t 0 < 4 * R
      linarith
    exact ⟨hproj.symm ▸ ht4, by simpa only [hproj] using hrep⟩
  have hmaps : MapsTo T (ball o R) (ball (0 : L) (4 * R)) :=
    fun z hz => (hrepresentation z hz).1
  have hgq : ContDiffOn ℝ ∞ g (ball (0 : L) (4 * R)) := hg
  have hgT : ContDiffOn ℝ ∞ (g ∘ T) (ball o R) := hgq.comp hT hmaps
  have hcin : ContDiffOn ℝ ∞ (fun z => (c z : H)) (ball o R) :=
    L.subtypeL.contDiff.comp_contDiffOn hc
  have hgin : ContDiffOn ℝ ∞ (fun z => (g (T z) : H)) (ball o R) :=
    Lᗮ.subtypeL.contDiff.comp_contDiffOn hgT
  let error : H → H := fun z => (c z : H) + (g (T z) : H)
  have herr : ContDiffOn ℝ ∞ error (ball o R) := hcin.add hgin
  have heq (z : H) (hz : z ∈ ball o R) :
      P z - (o + L.starProjection (z - o)) = error z := by
    rw [(hrepresentation z hz).2]
    change (o + ((T z : H) + (g (T z) : H))) - (o + (u z : H)) =
      (c z : H) + (g (T z) : H)
    change (o + (((u z : H) + (c z : H)) + (g (T z) : H))) - (o + (u z : H)) = _
    abel
  have hud : fderiv ℝ u = fun z => L.orthogonalProjectionOnto := by
    funext z
    have hd : HasFDerivAt u L.orthogonalProjectionOnto z := by
      simpa only [ContinuousLinearMap.comp_id, Function.comp_def] using
        L.orthogonalProjectionOnto.hasFDerivAt.comp (f := fun y : H => y - o) z
          ((hasFDerivAt_id (𝕜 := ℝ) z).sub_const o)
    exact hd.fderiv
  have hujet (z : H) (i : ℕ) (hi : 1 ≤ i) :
      ‖iteratedFDeriv ℝ i u z‖ ≤ R * (R⁻¹) ^ i := by
    cases i with
    | zero => omega
    | succ i =>
      cases i with
      | zero =>
        rw [norm_iteratedFDeriv_one, hud, pow_one, mul_inv_cancel₀ hR.ne']
        apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
        intro w
        simpa only [one_mul] using L.norm_orthogonalProjectionOnto_apply_le w
      | succ i =>
        rw [← norm_iteratedFDeriv_fderiv, hud,
          iteratedFDeriv_const_of_ne (by omega), Pi.zero_apply, norm_zero]
        positivity
  let affine : H → H := fun z => o + L.starProjection (z - o)
  have haffine : ContDiff ℝ ∞ affine :=
    contDiff_const.add (L.starProjection.contDiff.comp (contDiff_id.sub contDiff_const))
  have hP : ContDiffOn ℝ ∞ P (ball o R) :=
    (haffine.contDiffOn.add herr).congr (by
      intro z hz
      rw [← heq z hz]
      dsimp only [affine]
      abel)
  refine ⟨hP, ?_⟩
  intro q z hz
  have hTjets (i : ℕ) (hi1 : 1 ≤ i) (hi : i ≤ q) :
      ‖iteratedFDeriv ℝ i T z‖ ≤ (1 + B q) * R * (R⁻¹) ^ i := by
    change ‖iteratedFDeriv ℝ i (fun y => u y + c y) z‖ ≤ _
    rw [fun_iteratedFDeriv_add_apply (hu.contDiffAt.of_le (by simp))
      ((hc.contDiffAt (isOpen_ball.mem_nhds hz)).of_le (by simp))]
    have hcsmall : ‖iteratedFDeriv ℝ i c z‖ ≤ B q * R * (R⁻¹) ^ i := by
      apply (hcjet q z hz i hi).trans
      have hBq := hB q
      have hBa : B q * δ ≤ B q := by nlinarith
      exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hBa hR.le) (by positivity)
    have hh := (norm_add_le _ _).trans (add_le_add (hujet z i hi1) hcsmall)
    convert hh using 1; ring
  have hnormal := norm_iteratedFDeriv_comp_le_scaled_on_open T g (ball o R)
    (ball (0 : L) (4 * R)) isOpen_ball isOpen_ball hmaps q
    (hT.of_le (by simp)) (hgq.of_le (by simp)) z hz R (F q * δ) (1 + B q) hR
    (fun i hi => hjet q i hi _ (hmaps hz)) hTjets
  have hcinorm : ‖iteratedFDeriv ℝ q (fun y => (c y : H)) z‖ =
      ‖iteratedFDeriv ℝ q c z‖ :=
    L.subtypeₗᵢ.norm_iteratedFDeriv_comp_left (hc.contDiffAt (isOpen_ball.mem_nhds hz)) (by simp)
  have hginorm : ‖iteratedFDeriv ℝ q (fun y => (g (T y) : H)) z‖ =
      ‖iteratedFDeriv ℝ q (g ∘ T) z‖ :=
    Lᗮ.subtypeₗᵢ.norm_iteratedFDeriv_comp_left (hgT.contDiffAt (isOpen_ball.mem_nhds hz)) (by simp)
  have hevent : (fun y => P y - (o + L.starProjection (y - o))) =ᶠ[𝓝 z] error := by
    filter_upwards [isOpen_ball.mem_nhds hz] with y hy
    exact heq y hy
  rw [(hevent.iteratedFDeriv ℝ q).eq_of_nhds]
  change ‖iteratedFDeriv ℝ q (fun y => (c y : H) + (g (T y) : H)) z‖ ≤ _
  rw [fun_iteratedFDeriv_add_apply ((hcin.contDiffAt (isOpen_ball.mem_nhds hz)).of_le (by simp))
    ((hgin.contDiffAt (isOpen_ball.mem_nhds hz)).of_le (by simp))]
  have hh := (norm_add_le _ _).trans (add_le_add
    (hcinorm.le.trans (hcjet q z hz q le_rfl)) (hginorm.le.trans hnormal))
  convert hh using 1; ring

end DifferentialGeometry.Analysis
