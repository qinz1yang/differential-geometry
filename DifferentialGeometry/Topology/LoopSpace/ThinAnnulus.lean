import DifferentialGeometry.Topology.LoopSpace.AttachAnnulus
import Mathlib.Analysis.Normed.MulAction
import DifferentialGeometry.Analysis.Calculus.Interpolation.AffineLipschitz

noncomputable section

open Set Metric
open DifferentialGeometry.Analysis
open scoped NNReal

namespace DifferentialGeometry.Topology

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]

def thinAnnulusProjection (R : ℝ) (z : ℂ) : ℂ :=
  R • (radialDirection z : ℂ)

def thinAnnulusParameter (R h : ℝ) (z : ℂ) : ℝ :=
  (‖z‖ - (R - h)) / h

def thinAnnulusInterpolation (u v : ℂ → F) (R h : ℝ) (z : ℂ) : F :=
  (1 - thinAnnulusParameter R h z) • v (thinAnnulusProjection R z) +
    thinAnnulusParameter R h z • u (thinAnnulusProjection R z)

def attachThinAnnulus (u v : ℂ → F) (r : F → F) (R h : ℝ) (z : ℂ) : F :=
  if ‖z‖ ≤ R - h then v ((R / (R - h)) • z)
  else if R ≤ ‖z‖ then u z
  else r (thinAnnulusInterpolation u v R h z)

theorem thinAnnulusProjection_norm {R : ℝ} (hR : 0 ≤ R) (z : ℂ) :
    ‖thinAnnulusProjection R z‖ = R := by
  simp only [thinAnnulusProjection, norm_smul, Real.norm_eq_abs,
    Circle.norm_coe, mul_one, abs_of_nonneg hR]

theorem thinAnnulusProjection_eq {R : ℝ} {z : ℂ} (hz : ‖z‖ = R) :
    thinAnnulusProjection R z = z := by
  rw [thinAnnulusProjection, ← hz, radialDirection_reconstruct]

theorem thinAnnulusProjection_eq_scale {R h : ℝ} (ha : R - h ≠ 0)
    {z : ℂ} (hz : ‖z‖ = R - h) :
    thinAnnulusProjection R z = (R / (R - h)) • z := by
  symm
  calc
    (R / (R - h)) • z =
        (R / (R - h)) • (‖z‖ • (radialDirection z : ℂ)) :=
      congrArg (fun w : ℂ => (R / (R - h)) • w)
        (radialDirection_reconstruct z).symm
    _ = thinAnnulusProjection R z := by
      rw [hz, smul_smul, div_mul_cancel₀ _ ha]
      rfl

theorem thinAnnulusParameter_inner {R h : ℝ} {z : ℂ}
    (hz : ‖z‖ = R - h) : thinAnnulusParameter R h z = 0 := by
  simp only [thinAnnulusParameter, hz, sub_self, zero_div]

theorem thinAnnulusParameter_outer {R h : ℝ} (hh : h ≠ 0) {z : ℂ}
    (hz : ‖z‖ = R) : thinAnnulusParameter R h z = 1 := by
  rw [thinAnnulusParameter, hz, sub_sub_cancel, div_self hh]

theorem thinAnnulusParameter_mem_Icc {R h : ℝ} (hh : 0 < h) {z : ℂ}
    (hz : R - h ≤ ‖z‖ ∧ ‖z‖ ≤ R) : thinAnnulusParameter R h z ∈ Icc 0 1 := by
  constructor
  · exact div_nonneg (sub_nonneg.mpr hz.1) hh.le
  · exact (div_le_one hh).mpr (by linarith [hz.2])

theorem attachThinAnnulus_inner (u v : ℂ → F) (r : F → F) (R h : ℝ)
    {z : ℂ} (hz : ‖z‖ ≤ R - h) :
    attachThinAnnulus u v r R h z = v ((R / (R - h)) • z) :=
  ite_eq_left hz

theorem attachThinAnnulus_outer (u v : ℂ → F) (r : F → F) {R h : ℝ}
    (hh : 0 < h) {z : ℂ} (hz : R ≤ ‖z‖) :
    attachThinAnnulus u v r R h z = u z := by
  rw [attachThinAnnulus, ite_eq_right (by linarith), ite_eq_left hz]

theorem attachThinAnnulus_shell (u v : ℂ → F) (r : F → F) {R h : ℝ}
    (hh : 0 < h) (hhR : h < R)
    (hru : ∀ z, ‖z‖ = R → r (u z) = u z)
    (hrv : ∀ z, ‖z‖ = R → r (v z) = v z)
    {z : ℂ} (hz : R - h ≤ ‖z‖ ∧ ‖z‖ ≤ R) :
    attachThinAnnulus u v r R h z = r (thinAnnulusInterpolation u v R h z) := by
  by_cases hzin : ‖z‖ ≤ R - h
  · have hnorm : ‖z‖ = R - h := le_antisymm hzin hz.1
    rw [attachThinAnnulus_inner u v r R h hzin, thinAnnulusInterpolation,
      thinAnnulusParameter_inner hnorm, sub_zero, one_smul, zero_smul, add_zero,
      thinAnnulusProjection_eq_scale (sub_pos.mpr hhR).ne' hnorm,
      hrv _ (by
        rw [← thinAnnulusProjection_eq_scale (sub_pos.mpr hhR).ne' hnorm]
        exact thinAnnulusProjection_norm (hh.trans hhR).le z)]
  · by_cases hzout : R ≤ ‖z‖
    · have hnorm : ‖z‖ = R := le_antisymm hz.2 hzout
      rw [attachThinAnnulus_outer u v r hh hzout, thinAnnulusInterpolation,
        thinAnnulusParameter_outer hh.ne' hnorm, sub_self, zero_smul, one_smul,
        zero_add, thinAnnulusProjection_eq hnorm, hru z hnorm]
    · simp only [attachThinAnnulus, ite_eq_right hzin, ite_eq_right hzout]

theorem thinAnnulusProjection_lipschitzOn {R h : ℝ} (hh : 0 < h) (hhR : h < R) :
    LipschitzOnWith (Real.toNNReal (2 * R / (R - h))) (thinAnnulusProjection R)
      {z : ℂ | R - h ≤ ‖z‖ ∧ ‖z‖ ≤ R} := by
  have ha : 0 < R - h := sub_pos.mpr hhR
  have hR : 0 < R := hh.trans hhR
  apply LipschitzOnWith.of_dist_le'
  intro z hz w hw
  have hz0 : z ≠ 0 := norm_pos_iff.mp (ha.trans_le hz.1)
  have hw0 : w ≠ 0 := norm_pos_iff.mp (ha.trans_le hw.1)
  have hdir : dist (radialDirection z : ℂ) (radialDirection w : ℂ) ≤
      (2 / (R - h)) * dist z w := by
    rw [radialDirection_coe hz0, radialDirection_coe hw0]
    exact normalize_dist_le ha hz.1 hw.1
  calc
    dist (thinAnnulusProjection R z) (thinAnnulusProjection R w) =
        R * dist (radialDirection z : ℂ) (radialDirection w : ℂ) := by
      simp only [thinAnnulusProjection, dist_eq_norm, ← smul_sub, norm_smul,
        Real.norm_eq_abs, abs_of_pos hR]
    _ ≤ R * ((2 / (R - h)) * dist z w) :=
      mul_le_mul_of_nonneg_left hdir hR.le
    _ = (2 * R / (R - h)) * dist z w := by ring

theorem thinAnnulusParameter_lipschitz {R h : ℝ} (hh : 0 < h) :
    LipschitzWith (Real.toNNReal (1 / h)) (thinAnnulusParameter R h) := by
  apply LipschitzWith.of_dist_le'
  intro z w
  have hn : |‖z‖ - ‖w‖| ≤ dist z w := by
    simpa only [dist_eq_norm] using abs_norm_sub_norm_le z w
  calc
    dist (thinAnnulusParameter R h z) (thinAnnulusParameter R h w) =
        |‖z‖ - ‖w‖| / h := by
      rw [Real.dist_eq, thinAnnulusParameter, thinAnnulusParameter, ← sub_div,
        sub_sub_sub_cancel_right, abs_div, abs_of_pos hh]
    _ ≤ dist z w / h := div_le_div_of_nonneg_right hn hh.le
    _ = (1 / h) * dist z w := by ring

theorem thinAnnulusInterpolation_lipschitzOn {u v : ℂ → F} {R h : ℝ}
    {Ku Kv δ : ℝ≥0} (hh : 0 < h) (hhR : h < R)
    (hu : LipschitzWith Ku u) (hv : LipschitzWith Kv v)
    (hgap : ∀ z : ℂ, ‖z‖ = R → ‖u z - v z‖ ≤ δ) :
    LipschitzOnWith
      (max (Kv * Real.toNNReal (2 * R / (R - h)))
        (Ku * Real.toNNReal (2 * R / (R - h))) + Real.toNNReal (1 / h) * δ)
      (thinAnnulusInterpolation u v R h)
      {z : ℂ | R - h ≤ ‖z‖ ∧ ‖z‖ ≤ R} := by
  have hp := thinAnnulusProjection_lipschitzOn hh hhR
  exact lipschitzOnWith_affine_interpolation
    (thinAnnulusParameter_lipschitz hh).lipschitzOnWith
    (hv.comp_lipschitzOnWith hp) (hu.comp_lipschitzOnWith hp)
    (fun z hz => thinAnnulusParameter_mem_Icc hh hz)
    (fun z _ => hgap _ (thinAnnulusProjection_norm (hh.trans hhR).le z))

theorem attachThinAnnulus_lipschitz_of_sphere_gap {u v : ℂ → F} {r : F → F}
    {R h : ℝ} {Ku Kv Kr δ : ℝ≥0} {T : Set F} (hh : 0 < h) (hhR : h < R)
    (hu : LipschitzWith Ku u) (hv : LipschitzWith Kv v) (hr : LipschitzOnWith Kr r T)
    (hT : MapsTo (thinAnnulusInterpolation u v R h)
      {z : ℂ | R - h ≤ ‖z‖ ∧ ‖z‖ ≤ R} T)
    (hru : ∀ z, ‖z‖ = R → r (u z) = u z)
    (hrv : ∀ z, ‖z‖ = R → r (v z) = v z)
    (hgap : ∀ z : ℂ, ‖z‖ = R → ‖u z - v z‖ ≤ δ) :
    ∃ K : ℝ≥0, LipschitzWith K (attachThinAnnulus u v r R h) := by
  let Ki : ℝ≥0 := Kv * ‖R / (R - h)‖₊
  let Ks : ℝ≥0 := Kr *
    (max (Kv * Real.toNNReal (2 * R / (R - h)))
      (Ku * Real.toNNReal (2 * R / (R - h))) + Real.toNNReal (1 / h) * δ)
  let K : ℝ≥0 := max Ku (max Ki Ks)
  have hKi : Ki ≤ K := (le_max_left Ki Ks).trans (le_max_right Ku (max Ki Ks))
  have hKs : Ks ≤ K := (le_max_right Ki Ks).trans (le_max_right Ku (max Ki Ks))
  have hKu : Ku ≤ K := le_max_left Ku (max Ki Ks)
  have hinner : LipschitzWith K (fun z : ℂ => v ((R / (R - h)) • z)) :=
    (hv.comp (lipschitzWith_smul (R / (R - h)))).weaken hKi
  have hshell : LipschitzOnWith K (fun z => r (thinAnnulusInterpolation u v R h z))
      {z : ℂ | R - h ≤ ‖z‖ ∧ ‖z‖ ≤ R} :=
    (hr.comp (thinAnnulusInterpolation_lipschitzOn hh hhR hu hv hgap) hT).weaken hKs
  have hball : LipschitzOnWith K (attachThinAnnulus u v r R h)
      (Metric.closedBall (0 : ℂ) R) := by
    apply lipschitzOnWith_of_radial_pieces (r := R - h) (convex_closedBall 0 R)
    · intro z hz w hw
      rw [attachThinAnnulus_inner u v r R h hz.2,
        attachThinAnnulus_inner u v r R h hw.2]
      exact hinner z w
    · intro z hz w hw
      have hzR : ‖z‖ ≤ R := by simpa only [mem_closedBall, dist_zero_right] using hz.1
      have hwR : ‖w‖ ≤ R := by simpa only [mem_closedBall, dist_zero_right] using hw.1
      rw [attachThinAnnulus_shell u v r hh hhR hru hrv ⟨hz.2, hzR⟩,
        attachThinAnnulus_shell u v r hh hhR hru hrv ⟨hw.2, hwR⟩]
      exact hshell ⟨hz.2, hzR⟩ ⟨hw.2, hwR⟩
  refine ⟨K, lipschitzOnWith_univ.mp ?_⟩
  apply lipschitzOnWith_of_radial_pieces (r := R) convex_univ
  · intro z hz w hw
    exact hball (by simpa only [mem_closedBall, dist_zero_right, mem_ofPred_eq] using hz.2)
      (by simpa only [mem_closedBall, dist_zero_right, mem_ofPred_eq] using hw.2)
  · intro z hz w hw
    rw [attachThinAnnulus_outer u v r hh hz.2,
      attachThinAnnulus_outer u v r hh hw.2]
    exact (hu.weaken hKu) z w

theorem attachThinAnnulus_lipschitz {u v : ℂ → F} {r : F → F}
    {R h : ℝ} {Ku Kv Kr : ℝ≥0} (hh : 0 < h) (hhR : h < R)
    (hu : LipschitzWith Ku u) (hv : LipschitzWith Kv v) (hr : LipschitzWith Kr r)
    (hru : ∀ z, ‖z‖ = R → r (u z) = u z)
    (hrv : ∀ z, ‖z‖ = R → r (v z) = v z) :
    ∃ K : ℝ≥0, LipschitzWith K (attachThinAnnulus u v r R h) := by
  let δ : ℝ≥0 := Real.toNNReal
    ((Ku : ℝ) * R + dist (u 0) (v 0) + (Kv : ℝ) * R)
  apply attachThinAnnulus_lipschitz_of_sphere_gap hh hhR hu hv hr.lipschitzOnWith
    (fun _ _ => mem_univ _) hru hrv
    (δ := δ)
  intro z hz
  rw [← dist_eq_norm]
  calc
    dist (u z) (v z) ≤ dist (u z) (u 0) + dist (u 0) (v 0) +
        dist (v 0) (v z) := (dist_triangle (u z) (u 0) (v z)).trans
      (by linarith [dist_triangle (u 0) (v 0) (v z)])
    _ ≤ (Ku : ℝ) * R + dist (u 0) (v 0) + (Kv : ℝ) * R := by
      have hau := hu.dist_le_mul z 0
      have hav := hv.dist_le_mul 0 z
      simp only [dist_zero_right, dist_zero_left, hz] at hau hav
      linarith
    _ ≤ (δ : ℝ) := Real.le_coe_toNNReal _

theorem attachThinAnnulus_mapsTo {u v : ℂ → F} {r : F → F} {R h : ℝ}
    {S T : Set F} (hh : 0 < h) (hhR : h < R)
    (hu : MapsTo u {z : ℂ | R ≤ ‖z‖} S)
    (hv : MapsTo v (Metric.closedBall (0 : ℂ) R) S)
    (hr : MapsTo r T S)
    (hT : MapsTo (thinAnnulusInterpolation u v R h)
      {z : ℂ | R - h < ‖z‖ ∧ ‖z‖ < R} T) :
    MapsTo (attachThinAnnulus u v r R h) univ S := by
  intro z _
  unfold attachThinAnnulus
  split_ifs with hi ho
  · apply hv
    have ha : 0 < R - h := sub_pos.mpr hhR
    have hR : 0 < R := hh.trans hhR
    have hscale : ‖(R / (R - h)) • z‖ ≤ R := by
      rw [norm_smul, Real.norm_eq_abs, abs_of_pos (div_pos hR ha)]
      exact (mul_le_mul_of_nonneg_left hi (div_nonneg hR.le ha.le)).trans_eq
        (div_mul_cancel₀ R ha.ne')
    simpa only [mem_closedBall, dist_zero_right] using hscale
  · exact hu ho
  · exact hr (hT ⟨lt_of_not_ge hi, lt_of_not_ge ho⟩)

end DifferentialGeometry.Topology
