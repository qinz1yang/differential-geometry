import DifferentialGeometry.Geometry.Metric.ActualCloudZeroMarkerBound
import DifferentialGeometry.Geometry.Metric.ActualCloudContributorApplications

/-! Consumer of CFS30 on explicit data in `ℝ³`: blocks `span{e₀}` (`R = 1`), `span{e₁}` (`R = 1/100`, small) and
`span{e₂}` (`R = 1`, originally zero). One stage replaces the original image `e₀` by `e₀ + 10⁻⁴ e₂`. CFS30 gives
the exact zero small block and the bound `|v₂| ≤ R₂/32` on the whole segment, although the large originally zero
marker `v₂` does change. -/

set_option autoImplicit false
noncomputable section
open Set Metric DifferentialGeometry.Analysis

namespace GC.MetricGeometry

/-- CFS30 consumer: exact small-marker preservation and (AZM) on the segment for a changed large zero marker. -/
theorem actualCloud_zero_marker_bound_consumer :
    let e : Fin 3 → EuclideanSpace ℝ (Fin 3) := fun j => EuclideanSpace.single j 1
    let V : Fin 3 → Submodule ℝ (EuclideanSpace ℝ (Fin 3)) := fun j => ℝ ∙ e j
    let y : EuclideanSpace ℝ (Fin 3) := e 0 + (1 / 10000 : ℝ) • e 2
    (V 1).starProjection y = 0 ∧ y 2 ≠ 0 ∧ ∀ z ∈ segment ℝ (e 0) y, |z 2| ≤ 1 / 32 := by
  intro e V y
  let coord : Fin 3 → EuclideanSpace ℝ (Fin 3) →L[ℝ] ℝ := fun j => innerSL ℝ (e j)
  have hcoord : ∀ j z, coord j z = z j := by
    intro j z
    simp only [coord, e, innerSL_apply_apply, EuclideanSpace.inner_single_left, map_one, one_mul]
  have he00 : e 0 0 = 1 := by simp [e]
  have he01 : e 0 1 = 0 := by simp [e]
  have he02 : e 0 2 = 0 := by simp [e]
  have he21 : e 2 1 = 0 := by simp [e]
  have he22 : e 2 2 = 1 := by simp [e]
  have hcoord_zero_iff : ∀ (j : Fin 3) (z : EuclideanSpace ℝ (Fin 3)),
      (V j).starProjection z = 0 ↔ z j = 0 := by
    intro j z
    rw [(V j).starProjection_apply_eq_zero_iff, Submodule.mem_orthogonal_singleton_iff_inner_right,
      ← innerSL_apply_apply (𝕜 := ℝ)]
    change coord j z = 0 ↔ _
    rw [hcoord]
  have htop : ∀ z : EuclideanSpace ℝ (Fin 3),
      (⊤ : Submodule ℝ (EuclideanSpace ℝ (Fin 3))).starProjection z = z :=
    fun z => Submodule.starProjection_eq_self_iff.mpr Submodule.mem_top
  let R : Fin 3 → ℝ := ![1, 1 / 100, 1]
  have hR0 : R 0 = 1 := rfl
  have hR1 : R 1 = 1 / 100 := rfl
  have hR2 : R 2 = 1 := rfl
  have hsmall : ∀ i : Fin 3, R i < 1 / 16 → i = 1 := by
    intro i hi
    fin_cases i
    · simp only [Fin.zero_eta, Fin.isValue, hR0] at hi; norm_num at hi
    · rfl
    · simp only [Fin.reduceFinMk, hR2] at hi; norm_num at hi
  have hy1 : y 1 = 0 := by
    simp only [y, PiLp.add_apply, PiLp.smul_apply, smul_eq_mul, he01, he21, mul_zero, add_zero]
  have hy2 : y 2 = 1 / 10000 := by
    simp only [y, PiLp.add_apply, PiLp.smul_apply, smul_eq_mul, he02, he22, mul_one, zero_add]
  have hsupp : ∀ (i : Fin 3) (q : Unit), 0 < coord i (e 0) → 3 * R i / 4 ≤ (1 : ℝ) ∧ (1 : ℝ) ≤ 5 * R i / 4 := by
    intro i _ hpos
    fin_cases i
    · simp only [Fin.zero_eta, Fin.isValue, hR0]; norm_num
    · simp only [Fin.mk_one, Fin.isValue, hcoord, he01] at hpos
      exact absurd hpos (lt_irrefl 0)
    · simp only [Fin.reduceFinMk, Fin.isValue, hcoord, he02] at hpos
      exact absurd hpos (lt_irrefl 0)
  let g : ℕ → Unit → EuclideanSpace ℝ (Fin 3) := fun k _ => if k = 0 then e 0 else y
  have hg1 : g 1 () = y := rfl
  have hres := actualCloud_zero_marker_bound (M := Unit) 1 (fun _ => ⊤) (fun _ _ => y)
    (fun _ _ => Submodule.mem_top) (fun _ _ => 1) (fun _ => e 0) g (fun _ => rfl)
    (by
      intro k hk q
      have hk0 : k = 0 := by omega
      subst hk0
      simp only [g, adjustmentMap_apply, htop, one_smul, ↓reduceIte]
      abel)
    (fun _ => 1) V (fun j z => coord j z) R
    (by intro j; fin_cases j <;> simp [R])
    (by intro j q; fin_cases j <;> simp [hcoord, he00, he01, he02])
    (fun i q hpos => hsupp i q hpos)
    (fun j q hz => (hcoord_zero_iff j (e 0)).mpr (by rw [← hcoord]; exact hz))
    (fun _ _ _ => Or.inl le_top)
    (fun _ => {e 0}) (fun _ _ => ()) (fun _ => 1 / 640) (fun _ => 3 * (1 / 640) / 10)
    (fun _ _ i q hpos => hsupp i q (by rwa [htop] at hpos))
    (fun _ _ _ _ => ⟨0, by rw [htop, hcoord, he00, hR0]⟩)
    (fun _ _ x hx => by rw [htop]; exact hx.symm)
    (fun _ _ => by norm_num) (fun _ _ => le_rfl)
    (fun _ _ q _ => by rw [htop]; exact rfl)
    (by
      intro k hk q _
      have hk0 : k = 0 := by omega
      subst hk0
      simp only [g, ↓reduceIte, sub_self, norm_zero]
      norm_num)
    (by
      intro k _ x _ z _ q _ i hi
      have hi1 := hsmall i (by simpa using hi)
      subst hi1
      exact (hcoord_zero_iff 1 y).mpr hy1)
    coord
    (by
      intro i
      rw [innerSL_apply_norm]
      simp [e])
    (fun i z hz => by rw [hcoord]; exact (hcoord_zero_iff i z).mp hz)
    (E := 1 / 512) (by norm_num) le_rfl
    (by
      intro q
      simp only [g, one_ne_zero, ↓reduceIte, y, add_sub_cancel_left, norm_smul, e, PiLp.norm_single,
        norm_one, mul_one, Real.norm_eq_abs]
      norm_num)
  obtain ⟨hexact, hazm⟩ := hres
  refine ⟨(hcoord_zero_iff 1 y).mpr hy1, by rw [hy2]; norm_num, ?_⟩
  intro z hz
  have h := hazm () 2 (by rw [hcoord, he02]) z (by rw [hg1]; exact hz)
  rwa [hcoord, hR2] at h

end GC.MetricGeometry
