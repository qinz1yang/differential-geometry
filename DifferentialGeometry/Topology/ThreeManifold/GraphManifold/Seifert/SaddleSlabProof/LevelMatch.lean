import DifferentialGeometry.Topology.Diffeomorph.Translation
import DifferentialGeometry.Analysis.Calculus.Derivative.Coordinates.JacobianSign

/-!
# Matching the levels of two slabs

Lane RG03c. `exists_levelMatch`: for `δ ≥ 0`, `a < c - δ`, `c + δ < b`, `a' < c' - δ` and
`c' + δ < b'` there is an increasing diffeomorphism `ψ` of `ℝ` with `ψ a = a'` and `ψ b = b'`
which is the translation `t ↦ t - c + c'` on `[c - δ, c + δ]`. It is a translation followed by
two compactly supported pushes (`exists_isotopy_translation_in_open`), one on each side of the
middle interval.
-/

set_option autoImplicit false

noncomputable section

open Set
open scoped Manifold ContDiff

namespace GC.Seifert.SaddleSlabProof

def realShift (d : ℝ) : ℝ ≃ₘ[ℝ] ℝ where
  toEquiv := Equiv.addRight d
  contMDiff_toFun := (contDiff_id.add contDiff_const).contMDiff
  contMDiff_invFun := (contDiff_id.sub contDiff_const).contMDiff

theorem realShift_apply (d t : ℝ) : realShift d t = t + d := rfl

theorem strictMono_of_eqOn_compl {F : ℝ ≃ₘ[ℝ] ℝ} {K : Set ℝ} (hK : IsCompact K)
    (hfix : EqOn F id Kᶜ) : StrictMono F := by
  refine strictMono_of_deriv_pos fun x => ?_
  have h := F.det_fderiv_pos_of_eqOn_compl_isCompact hK hfix x
  simpa only [LinearMap.det_ring, ContinuousLinearMap.coe_coe, fderiv_eq_smul_deriv,
    one_smul] using h

theorem exists_push {U : Set ℝ} (hU : IsOpen U) (hUc : Convex ℝ U) {x y : ℝ} (hx : x ∈ U)
    (hy : y ∈ U) :
    ∃ F : ℝ ≃ₘ[ℝ] ℝ, StrictMono F ∧ F x = y ∧ ∀ t ∉ U, F t = t := by
  obtain ⟨H, -, -, -, hmove, -, J, hJ, hJU, hfix⟩ :=
    Diffeomorph.exists_isotopy_translation_in_open (isCompact_singleton (x := x)) hU (y - x)
      (by
        intro s hs z hz
        rw [mem_singleton_iff.mp hz]
        have h := hUc hx hy (sub_nonneg.mpr hs.2) hs.1 (sub_add_cancel 1 s)
        have heq : (1 - s) • x + s • y = x + s • (y - x) := by
          simp only [smul_eq_mul]
          ring
        rwa [heq] at h)
  refine ⟨H 1, strictMono_of_eqOn_compl hJ (hfix 1).1, ?_, fun t ht => ?_⟩
  · rw [hmove 1 ⟨zero_le_one, le_rfl⟩ x rfl, one_smul, add_sub_cancel]
  · exact (hfix 1).1 fun htJ => ht (hJU htJ)

theorem exists_levelMatch {a b c a' b' c' δ : ℝ} (hδ : 0 ≤ δ) (ha : a < c - δ) (hb : c + δ < b)
    (ha' : a' < c' - δ) (hb' : c' + δ < b') :
    ∃ ψ : ℝ ≃ₘ[ℝ] ℝ, StrictMono ψ ∧ ψ a = a' ∧ ψ b = b' ∧
      ∀ t ∈ Icc (c - δ) (c + δ), ψ t = t - c + c' := by
  obtain ⟨L, hLm, hLx, hLfix⟩ := exists_push (isOpen_Iio (a := c' - δ)) (convex_Iio _)
    (show a + (c' - c) ∈ Iio (c' - δ) by rw [mem_Iio]; linarith) (show a' ∈ Iio (c' - δ) from ha')
  obtain ⟨R, hRm, hRx, hRfix⟩ := exists_push (isOpen_Ioi (a := c' + δ)) (convex_Ioi _)
    (show b + (c' - c) ∈ Ioi (c' + δ) by rw [mem_Ioi]; linarith) (show b' ∈ Ioi (c' + δ) from hb')
  have hsh : StrictMono (realShift (c' - c)) := fun s t hst => by
    rw [realShift_apply, realShift_apply]
    linarith
  refine ⟨(realShift (c' - c)).trans (L.trans R), hRm.comp (hLm.comp hsh), ?_, ?_, ?_⟩
  · change R (L (a + (c' - c))) = a'
    rw [hLx]
    exact hRfix a' (by rw [mem_Ioi, not_lt]; linarith)
  · change R (L (b + (c' - c))) = b'
    rw [hLfix (b + (c' - c)) (by rw [mem_Iio, not_lt]; linarith), hRx]
  · intro t ht
    change R (L (t + (c' - c))) = t - c + c'
    rw [hLfix (t + (c' - c)) (by rw [mem_Iio, not_lt]; linarith [ht.1]),
      hRfix (t + (c' - c)) (by rw [mem_Ioi, not_lt]; linarith [ht.2])]
    ring

end GC.Seifert.SaddleSlabProof
