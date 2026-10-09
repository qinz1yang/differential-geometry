import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Seifert.ConeFoldDescentReduce

/-!
# Surjectivity of the cone-fold descent

A point `x` of `PlaneLift × S¹` over the upper half `basePlus` of the filled base is the image
under `totalMap` of a point over the triangle (`exists_totalMap_eq`): if `conePoint x = f z` with
`z ≠ v`, the fibre coordinate is chosen so that `baseMap = coneChart x`, and `coneLift ∘ coneChart
= id`; over the apex `x = (0, w)` is a value of the tube map on the central fibre. Points over the
lower half are conjugates of such points, and the conjugate preimage lies off wall 0 (where `f` is
real), so its flip is a preimage under `mirrorMap`. Hence `foldMap` is onto the interior of the
filled carrier (`foldMap_surjective`).
-/

set_option autoImplicit false
noncomputable section
open Complex Set Filter Topology
open DifferentialGeometry DifferentialGeometry.Topology GC.Endpoint GC.GraphManifold GC.Geometry
open scoped ContDiff ComplexConjugate Manifold

universe u

namespace GC.Seifert

theorem ConeFilling.down_eq_zero_of_conePoint_eq (c : ConeFilling) {x : PlaneLift.{u} × Circle}
    (hx : c.conePoint x = 3 / 2) : x.1.down = 0 := by
  by_contra h
  apply c.conePoint_ne x h
  rw [hx]
  push_cast
  rfl

namespace ConeShape.FoldData

variable {σ : ConeShape} (D : σ.FoldData) (c : ConeFilling) (hθ : σ.θ₁ * c.p = Real.pi)

theorem exists_totalMap_eq (hθ : σ.θ₁ * c.p = Real.pi) {x : PlaneLift.{u} × Circle}
    (hx : c.conePoint x ∈ σ.basePlus) :
    ∃ p : ModelCoordinates, (logPoint p : ℂ) ∈ σ.triangle ∧ D.totalMap.{u} c p = x := by
  obtain ⟨z, hzT, hfz⟩ := D.bijOn_f.surjOn hx
  have hz0 : 0 < z.im := hzT.1
  have hp : (c.p : ℝ) ≠ 0 := c.p_ne_zero
  have h2π : (2 * Real.pi : ℝ) ≠ 0 := by positivity
  by_cases hv : z = σ.vertexOne
  · have hdown : x.1.down = 0 := by
      apply c.down_eq_zero_of_conePoint_eq
      rw [← hfz, hv, D.f_vertexOne c hθ]
    obtain ⟨t, ht⟩ := Circle.exp_surjective x.2
    set p : ModelCoordinates := logCoords ⟨z, hz0⟩ (t / (2 * Real.pi * c.p))
    have hlp : (logPoint p : ℂ) = z := by
      simp only [p, logPoint_logCoords]
    refine ⟨p, by rw [hlp]; exact hzT, ?_⟩
    rw [totalMap, ite_eq_left (hlp.trans hv)]
    refine Prod.ext (ULift.ext ?_) ?_
    · rw [tubeMap_fst, hlp, hv, coneDisc_self, mul_zero, zero_mul, hdown]
    · rw [tubeMap_snd, ← ht]
      congr 1
      simp only [p, logCoords_two]
      field_simp
  · have hfne : D.f z ≠ 3 / 2 := D.f_ne_of_mem_triangle c hθ hzT hv
    have hdown : x.1.down ≠ 0 := by
      intro h
      apply hfne
      rw [hfz]
      have := c.norm_conePoint_sub x
      rw [h, norm_zero, zero_div, zero_pow (NeZero.ne c.p), zero_div, norm_eq_zero,
        sub_eq_zero] at this
      rw [this]
      push_cast
      ring
    set lam : Circle := (linearTorusMap c.chartMatrix (unitOf x.1.down, x.2)).2
    obtain ⟨t, ht⟩ := Circle.exp_surjective (lam * σ.foldPhase c.q z)
    set p : ModelCoordinates := logCoords ⟨z, hz0⟩ (t / (2 * Real.pi))
    have hlp : (logPoint p : ℂ) = z := by
      simp only [p, logPoint_logCoords]
    refine ⟨p, by rw [hlp]; exact hzT, ?_⟩
    rw [totalMap, ite_eq_right (by rw [hlp]; exact hv), liftMap,
      ← c.coneLift_coneChart x hdown]
    congr 1
    refine Prod.ext (ULift.ext ?_) ?_
    · rw [baseMap_fst, hlp, hfz]
      rfl
    · rw [baseMap_snd]
      change _ = lam
      have hs : 2 * Real.pi * p 2 = t := by
        simp only [p, logCoords_two]
        field_simp
      rw [hs, ht, hlp, mul_inv_cancel_right]

theorem foldMap_surjective (hσ : σ.θ₂ = 0) : Function.Surjective (D.foldMap.{u} c hθ hσ) := by
  intro y
  set x := c.descentIncl y
  have hu : c.conePoint x ∈ filledBase :=
    (filledFunction_neg_iff _).1 (c.filledFunction_descentIncl y)
  rcases le_or_gt 0 (c.conePoint x).im with him | him
  · have hb : c.conePoint x ∈ σ.basePlus := ⟨hu.1, him, fun _ => hu.2⟩
    obtain ⟨p, hpT, hpx⟩ := D.exists_totalMap_eq c hθ hb
    have hpN : p ∈ D.descentDomain c hθ :=
      D.mem_descentDomain_of_patches c hθ (D.triangle_subset_patches c hθ hσ hpT)
    refine ⟨⟨p, hpN⟩, c.descentIncl_injective ?_⟩
    rw [descentIncl_foldMap, D.mirrorMap_of_nonneg c (by rw [← logPoint_re_eq']; exact hpT.2 0),
      hpx]
  · have hb : c.conePoint (conjMap x) ∈ σ.basePlus := by
      rw [conePoint_conjMap]
      have hc := conj_mem_filledBase hu
      refine ⟨hc.1, ?_, fun _ => hc.2⟩
      rw [Complex.conj_im]
      linarith
    obtain ⟨p, hpT, hpx⟩ := D.exists_totalMap_eq c hθ hb
    have hpN : p ∈ D.descentDomain c hθ :=
      D.mem_descentDomain_of_patches c hθ (D.triangle_subset_patches c hθ hσ hpT)
    have hre : 0 < p 0 := by
      rw [← logPoint_re_eq']
      rcases (hpT.2 0).lt_or_eq with h | h
      · exact h
      · exfalso
        have hw : (logPoint p : ℂ) ∈ σ.foldWall 0 := ⟨hpT, h.symm⟩
        have h1 := D.f_real_of_mem_foldWall hw
        have h2 := D.conePoint_mirrorMap_of_mem_triangle c hθ hpT
        rw [D.mirrorMap_of_nonneg c (by rw [← logPoint_re_eq']; exact hpT.2 0), hpx,
          conePoint_conjMap] at h2
        rw [← h2, Complex.conj_im] at h1
        linarith
    refine ⟨⟨flipMap p, D.flipMap_mem_descentDomain c hθ hpN⟩, c.descentIncl_injective ?_⟩
    rw [descentIncl_foldMap, D.mirrorMap_of_neg c (by rw [flipMap_zero]; linarith),
      flipMap_flipMap, hpx, conjMap_conjMap]

end ConeShape.FoldData

end GC.Seifert
