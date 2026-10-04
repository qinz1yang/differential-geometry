import DifferentialGeometry.Analysis.ODE.Flow.Planar.ConstantOutsideCompactFlow
import Mathlib.Analysis.Calculus.BumpFunction.InnerProduct
import Mathlib.Analysis.SpecialFunctions.SmoothTransition
import Mathlib.Analysis.SpecialFunctions.ExpDeriv

/-!
A compact smooth scalar flow gives a strictly increasing radial compression. It fixes radii at
most one and solves the exact affine contraction toward radius three on the whole outer half disc.
-/

set_option autoImplicit false

noncomputable section

open Set Metric Real
open DifferentialGeometry
open scoped Manifold ContDiff

namespace GC.Seifert

private def collarCompressionBump : ContDiffBump (3 : ℝ) :=
  ⟨3, 4, by norm_num, by norm_num⟩

def collarCompressionVelocity (r : ℝ) : ℝ :=
  collarCompressionBump r * smoothTransition (2 * r - 2) * (3 - r)

theorem collarCompressionVelocity_smooth : ContDiff ℝ ∞ collarCompressionVelocity :=
  (collarCompressionBump.contDiff.mul
    (smoothTransition.contDiff.comp ((contDiff_const.mul contDiff_id).sub contDiff_const))).mul
    (contDiff_const.sub contDiff_id)

theorem collarCompressionVelocity_compact : HasCompactSupport collarCompressionVelocity :=
  collarCompressionBump.hasCompactSupport.mul_right.mul_right

theorem collarCompressionVelocity_zero {r : ℝ} (hr : r ≤ 1) :
    collarCompressionVelocity r = 0 := by
  rw [collarCompressionVelocity, smoothTransition.zero_of_nonpos (by linarith), mul_zero, zero_mul]

theorem collarCompressionVelocity_outer {r : ℝ} (hr : 3 / 2 ≤ r) (hr3 : r ≤ 3) :
    collarCompressionVelocity r = 3 - r := by
  have hb : collarCompressionBump r = 1 := by
    apply collarCompressionBump.one_of_mem_closedBall
    rw [mem_closedBall, Real.dist_eq, abs_of_nonpos (by linarith)]
    change -(r - 3) ≤ 3
    linarith
  rw [collarCompressionVelocity, hb, smoothTransition.one_of_one_le (by linarith), one_mul,
    one_mul]

theorem exists_scalarCollarCompression {k : ℝ} (hk : 0 < k) (hk1 : k ≤ 1) :
    ∃ D : ℝ ≃ₘ[ℝ] ℝ, StrictMono D ∧ (∀ r, r ≤ 1 → D r = r) ∧
      ∀ r, 3 / 2 ≤ r → r ≤ 3 → D r = 3 - k * (3 - r) := by
  obtain ⟨F, hF, hderiv, hzero, hadd, hinv⟩ :=
    DifferentialGeometry.Analysis.exists_smoothFlow_of_eq_const_off_compact
      collarCompressionVelocity_smooth 0 (by
        simpa only [sub_zero] using collarCompressionVelocity_compact)
  have hfix (t : ℝ) (ht : 0 ≤ t) (r : ℝ) (hr : r ≤ 1) : F t r = r := by
    have he := DifferentialGeometry.Analysis.ODE.Flow.orbit_unique_Icc
      collarCompressionVelocity_smooth (a := 0) (b := t) (g := fun s => r)
      (fun s hs => (hderiv r s).hasDerivWithinAt)
      (fun s hs => by
        change HasDerivWithinAt (fun z : ℝ => r) (collarCompressionVelocity r) (Icc 0 t) s
        rw [collarCompressionVelocity_zero hr]
        exact (hasDerivAt_const s r).hasDerivWithinAt)
      (by rw [hzero]; rfl)
    exact he ⟨ht, le_rfl⟩
  let t := -Real.log k
  have ht : 0 ≤ t := neg_nonneg.mpr (Real.log_nonpos hk.le hk1)
  have hkexp : Real.exp (-t) = k := by simp [t, Real.exp_log hk]
  have hmono : StrictMono (F t) := by
    rcases (F t).continuous.strictMono_of_inj (F t).injective with hm | ha
    · exact hm
    · have hbad := ha (show (0 : ℝ) < 1 by norm_num)
      rw [hfix t ht 0 (by norm_num), hfix t ht 1 le_rfl] at hbad
      linarith
  refine ⟨F t, hmono, hfix t ht, ?_⟩
  intro r hr hr3
  let g : ℝ → ℝ := fun s => 3 - Real.exp (-s) * (3 - r)
  have hg (s : ℝ) (hs : s ∈ Icc 0 t) :
      HasDerivAt g (collarCompressionVelocity (g s)) s := by
    have he : Real.exp (-s) ≤ 1 := Real.exp_le_one_iff.mpr (neg_nonpos.mpr hs.1)
    have he0 := (Real.exp_pos (-s)).le
    have hm := mul_le_mul_of_nonneg_right he (sub_nonneg.mpr hr3)
    have hg3 : g s ≤ 3 := by dsimp [g]; nlinarith
    have hgr : 3 / 2 ≤ g s := by dsimp [g]; nlinarith
    rw [collarCompressionVelocity_outer hgr hg3]
    have hd := (hasDerivAt_const s 3).sub
      ((((hasDerivAt_id s).neg).exp).mul_const (3 - r))
    convert hd using 1
    · ext z
      rfl
    · dsimp [g]
      ring
  have heq := DifferentialGeometry.Analysis.ODE.Flow.orbit_unique_Icc
    collarCompressionVelocity_smooth (a := 0) (b := t)
    (fun s hs => (hderiv r s).hasDerivWithinAt)
    (fun s hs => (hg s hs).hasDerivWithinAt) (by simp [hzero, g])
  exact (heq ⟨ht, le_rfl⟩).trans (by dsimp [g]; rw [hkexp])

end GC.Seifert
