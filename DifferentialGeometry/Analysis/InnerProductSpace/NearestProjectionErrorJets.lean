import DifferentialGeometry.Analysis.InnerProductSpace.NearestTangentCorrectionJets
import DifferentialGeometry.Analysis.Calculus.ScaledLocalComposition
import Mathlib.Analysis.Normed.Operator.LinearIsometry

set_option autoImplicit false
noncomputable section
open Set Metric Filter
open scoped ContDiff Topology Nat
namespace DifferentialGeometry.Analysis
universe u

theorem exists_bound_nearest_projection_error_jet (q : ℕ) (hq : 1 ≤ q) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ (H : Type u) [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
        (L : Submodule ℝ H) [CompleteSpace L]
        (o : H) (g : L → Lᗮ) (W : Set H) (P : H → H) (R a : ℝ),
        0 < R → 0 ≤ a → a ≤ 1 / 100 →
        ContDiffOn ℝ (q + 1 : ℕ) g (ball (0 : L) (4 * R)) →
        (∀ i ≤ q + 1, ∀ t ∈ ball (0 : L) (4 * R),
          ‖iteratedFDeriv ℝ i g t‖ ≤ a * R * (R⁻¹) ^ i) →
        (∀ t ∈ ball (0 : L) (4 * R),
          o + orthogonalCoordinateSum L (t, g t) ∈ W) →
        (∀ y ∈ W ∩ ball o (3 * R), ∃ t ∈ ball (0 : L) (4 * R),
          y = o + orthogonalCoordinateSum L (t, g t)) →
        (∀ z ∈ ball o R, P z ∈ W ∧ IsMinOn (fun w => dist z w) W (P z)) →
        ContDiffOn ℝ q (fun z => P z - (o + L.starProjection (z - o))) (ball o R) ∧
          ∀ z ∈ ball o R,
            ‖iteratedFDeriv ℝ q (fun y => P y - (o + L.starProjection (y - o))) z‖ ≤
              C * a * R * (R⁻¹) ^ q := by
  obtain ⟨B, hB, hcorrection⟩ := exists_bound_nearest_tangent_correction_jets.{u} q hq
  refine ⟨B + (q ! : ℝ) * (max (1 + B) 1) ^ q, by positivity, ?_⟩
  intro H _ _ _ L _ o g W P R a hR ha0 ha hg hjet hgraph hsheet hnearest
  let u : H → L := fun z => L.orthogonalProjectionOnto (z - o)
  let c : H → L := fun z => L.orthogonalProjectionOnto (P z - o) - u z
  let T : H → L := fun z => u z + c z
  obtain ⟨hc, hcjet⟩ := hcorrection H L o g W P R a hR ha0 ha hg hjet hgraph hsheet hnearest
  change ContDiffOn ℝ q c (ball o R) at hc
  change ∀ z ∈ ball o R, ∀ j ≤ q,
    ‖iteratedFDeriv ℝ j c z‖ ≤ B * a * R * (R⁻¹) ^ j at hcjet
  have hu : ContDiff ℝ q u :=
    L.orthogonalProjectionOnto.contDiff.comp (contDiff_id.sub contDiff_const)
  have hT : ContDiffOn ℝ q T (ball o R) := hu.contDiffOn.add hc
  have hTproj (z : H) : T z = L.orthogonalProjectionOnto (P z - o) := by
    dsimp only [T, c]
    abel
  have hvalue (t : L) (ht : t ∈ ball (0 : L) (4 * R)) : ‖g t‖ ≤ a * R := by
    simpa only [norm_iteratedFDeriv_zero, pow_zero, mul_one] using hjet 0 (by omega) t ht
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
  have hgq : ContDiffOn ℝ q g (ball (0 : L) (4 * R)) := hg.of_le (by simp)
  have hgT : ContDiffOn ℝ q (g ∘ T) (ball o R) := hgq.comp hT hmaps
  have hcin : ContDiffOn ℝ q (fun z => (c z : H)) (ball o R) :=
    L.subtypeL.contDiff.comp_contDiffOn hc
  have hgin : ContDiffOn ℝ q (fun z => (g (T z) : H)) (ball o R) :=
    Lᗮ.subtypeL.contDiff.comp_contDiffOn hgT
  let error : H → H := fun z => (c z : H) + (g (T z) : H)
  have herr : ContDiffOn ℝ q error (ball o R) := hcin.add hgin
  have heq (z : H) (hz : z ∈ ball o R) :
      P z - (o + L.starProjection (z - o)) = error z := by
    rw [(hrepresentation z hz).2]
    change (o + ((T z : H) + (g (T z) : H))) - (o + (u z : H)) =
      (c z : H) + (g (T z) : H)
    change (o + (((u z : H) + (c z : H)) + (g (T z) : H))) - (o + (u z : H)) = _
    abel
  have hud : fderiv ℝ u = fun _ => L.orthogonalProjectionOnto := by
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
  refine ⟨herr.congr heq, ?_⟩
  intro z hz
  have hTjets (i : ℕ) (hi1 : 1 ≤ i) (hi : i ≤ q) :
      ‖iteratedFDeriv ℝ i T z‖ ≤ (1 + B) * R * (R⁻¹) ^ i := by
    change ‖iteratedFDeriv ℝ i (fun y => u y + c y) z‖ ≤ _
    rw [fun_iteratedFDeriv_add_apply (hu.contDiffAt.of_le (by exact_mod_cast hi))
      ((hc.contDiffAt (isOpen_ball.mem_nhds hz)).of_le (by exact_mod_cast hi))]
    have ha1 : a ≤ 1 := by linarith
    have hcsmall : ‖iteratedFDeriv ℝ i c z‖ ≤ B * R * (R⁻¹) ^ i := by
      apply (hcjet z hz i hi).trans
      have hBa : B * a ≤ B := by nlinarith
      exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hBa hR.le) (by positivity)
    have hh := (norm_add_le _ _).trans (add_le_add (hujet z i hi1) hcsmall)
    convert hh using 1; ring
  have hnormal := norm_iteratedFDeriv_comp_le_scaled_on_open T g (ball o R)
    (ball (0 : L) (4 * R)) isOpen_ball isOpen_ball hmaps q hT hgq z hz R a (1 + B) hR
    (fun i hi => hjet i (by omega) _ (hmaps hz)) hTjets
  have hcinorm : ‖iteratedFDeriv ℝ q (fun y => (c y : H)) z‖ =
      ‖iteratedFDeriv ℝ q c z‖ :=
    L.subtypeₗᵢ.norm_iteratedFDeriv_comp_left (hc.contDiffAt (isOpen_ball.mem_nhds hz)) le_rfl
  have hginorm : ‖iteratedFDeriv ℝ q (fun y => (g (T y) : H)) z‖ =
      ‖iteratedFDeriv ℝ q (g ∘ T) z‖ :=
    Lᗮ.subtypeₗᵢ.norm_iteratedFDeriv_comp_left (hgT.contDiffAt (isOpen_ball.mem_nhds hz)) le_rfl
  have hevent : (fun y => P y - (o + L.starProjection (y - o))) =ᶠ[𝓝 z] error := by
    filter_upwards [isOpen_ball.mem_nhds hz] with y hy
    exact heq y hy
  rw [(hevent.iteratedFDeriv ℝ q).eq_of_nhds]
  change ‖iteratedFDeriv ℝ q (fun y => (c y : H) + (g (T y) : H)) z‖ ≤ _
  rw [fun_iteratedFDeriv_add_apply (hcin.contDiffAt (isOpen_ball.mem_nhds hz))
    (hgin.contDiffAt (isOpen_ball.mem_nhds hz))]
  have hh := (norm_add_le _ _).trans (add_le_add
    (hcinorm.le.trans (hcjet z hz q le_rfl)) (hginorm.le.trans hnormal))
  convert hh using 1; ring

end DifferentialGeometry.Analysis
