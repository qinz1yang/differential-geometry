import DifferentialGeometry.Analysis.Calculus.PolygonalRounding
import DifferentialGeometry.Topology.Planar.PolygonVertexCharts
import Mathlib.Topology.Order.IntermediateValue
import Mathlib.Analysis.Calculus.AddTorsor.AffineMap
import Mathlib.Analysis.Calculus.LineDeriv.Basic

open Set
open scoped ContDiff

namespace Schoenflies

open DifferentialGeometry.Analysis (smoothCorner roundedPolygonalCurve)

theorem affine_smoothCorner_vertex_coordinates
    (e : Plane ≃ᵃ[ℝ] Plane) {a p b : Plane} {r d : ℝ}
    (ha : e a = Plane.mk (-1) 0) (hp : e p = 0)
    (hb : e b = Plane.mk r (d * r)) (h σ t : ℝ) :
    e (smoothCorner σ p (h⁻¹ • (p - a)) (h⁻¹ • (b - p)) t) =
      Plane.mk ((t + (r - 1) * Real.smoothMax σ t 0) / h)
        (d * r * Real.smoothMax σ t 0 / h) := by
  change e.toAffineMap (smoothCorner σ p _ _ t) = _
  rw [smoothCorner.map_affine]
  have he (x y : Plane) : e.linear (x - y) = e x - e y :=
    e.toAffineMap.linearMap_vsub x y
  have hv : e.linear (h⁻¹ • (p - a)) = h⁻¹ • Plane.mk 1 0 := by
    rw [map_smul, he, hp, ha]
    congr 1
    ext i
    fin_cases i <;> norm_num [Plane.mk]
  have hw : e.linear (h⁻¹ • (b - p)) = h⁻¹ • Plane.mk r (d * r) := by
    rw [map_smul, he, hp, hb, sub_zero]
  change smoothCorner σ (e p) (e.linear _) (e.linear _) t = _
  rw [hp, hv, hw]
  ext i
  fin_cases i <;> simp [smoothCorner, Plane.mk, PiLp.add_apply, PiLp.sub_apply,
    div_eq_mul_inv] <;> ring

theorem affine_smoothCorner_vertex_coordinates_of_unit
    (e : Plane ≃ᵃ[ℝ] Plane) {a p b : Plane}
    (ha : e a = Plane.mk (-1) 0) (hp : e p = 0)
    (hb : e b = Plane.mk 1 1) (h σ t : ℝ) :
    e (smoothCorner σ p (h⁻¹ • (p - a)) (h⁻¹ • (b - p)) t) =
      Plane.mk (t / h) (Real.smoothMax (σ / h) (t / h) 0) := by
  have he := affine_smoothCorner_vertex_coordinates e (r := 1) (d := 1) ha hp
    (by simpa only [one_mul] using hb) h σ t
  simpa only [sub_self, zero_mul, add_zero, one_mul, ← Real.smoothMax.div, zero_div] using he

theorem affine_image_smoothCorner_Icc
    (e : Plane ≃ᵃ[ℝ] Plane) {a p b : Plane} {r d h σ : ℝ}
    (ha : e a = Plane.mk (-1) 0) (hp : e p = 0)
    (hb : e b = Plane.mk r (d * r)) (hr : 0 < r)
    (hd : d = 0 ∨ d = 1) (hunit : d = 1 → r = 1)
    (hh : 0 < h) (hσ : 0 < σ) (hσh : σ < h / 2) :
    e '' (smoothCorner σ p (h⁻¹ • (p - a)) (h⁻¹ • (b - p)) '' Icc (-h / 2) (h / 2)) =
      {q : Plane | q 0 ∈ Icc (-(1 / 2 : ℝ)) (r / 2) ∧
        q 1 = d * Real.smoothMax (σ / h) (q 0) 0} := by
  let c := smoothCorner σ p (h⁻¹ • (p - a)) (h⁻¹ • (b - p))
  let f := smoothCorner σ (0 : ℝ) h⁻¹ (h⁻¹ * r)
  have hx (t : ℝ) : (e (c t)) 0 = f t := by
    rw [affine_smoothCorner_vertex_coordinates e ha hp hb]
    dsimp [f, smoothCorner, Plane.mk]
    ring
  have hy (t : ℝ) : (e (c t)) 1 = d * Real.smoothMax (σ / h) (f t) 0 := by
    rcases hd with rfl | rfl
    · rw [affine_smoothCorner_vertex_coordinates e ha hp hb]
      simp
    · have hr1 := hunit rfl
      have hb1 : e b = Plane.mk 1 1 := by simpa only [hr1, one_mul] using hb
      have he := affine_smoothCorner_vertex_coordinates_of_unit e ha hp hb1 h σ t
      have hx1 : f t = t / h := by
        rw [← hx, he]
        rfl
      rw [hx1]
      change (e (c t)) 1 = 1 * _
      rw [he]
      simp only [one_mul]
      rfl
  have hfc : Continuous f := (smoothCorner.contDiff σ (0 : ℝ) h⁻¹ (h⁻¹ * r)).continuous
  have hfm : StrictMono f := by
    simpa only [ContinuousLinearMap.id_apply] using
      smoothCorner.strictMono_comp σ (0 : ℝ) h⁻¹ (h⁻¹ * r)
        (ContinuousLinearMap.id ℝ ℝ) (inv_pos.mpr hh) (mul_pos (inv_pos.mpr hh) hr)
  have hleft : f (-h / 2) = -(1 / 2 : ℝ) := by
    dsimp only [f]
    rw [smoothCorner.eq_left hσ (by linarith)]
    dsimp
    field_simp [hh.ne']
    ring
  have hright : f (h / 2) = r / 2 := by
    dsimp only [f]
    rw [smoothCorner.eq_right hσ hσh.le]
    dsimp
    field_simp [hh.ne']
    ring
  have him : f '' Icc (-h / 2) (h / 2) = Icc (-(1 / 2 : ℝ)) (r / 2) := by
    rw [hfc.image_Icc_of_strictMono hfm, hleft, hright]
  ext q
  constructor
  · rintro ⟨_, ⟨t, ht, rfl⟩, rfl⟩
    change (e (c t)) 0 ∈ Icc (-(1 / 2 : ℝ)) (r / 2) ∧ _
    rw [hx]
    exact ⟨him ▸ mem_image_of_mem f ht, hy t⟩
  · intro hq
    obtain ⟨t, ht, heq⟩ := him.symm ▸ hq.1
    refine ⟨c t, ⟨t, ht, rfl⟩, ?_⟩
    ext i
    fin_cases i
    · exact (hx t).trans heq
    · exact (hy t).trans (by rw [heq]; exact hq.2.symm)

theorem range_roundedPolygonalCurve_eq_iUnion_graphs
    {n : ℕ} (p : ZMod n → Plane) (e : ZMod n → Plane ≃ᵃ[ℝ] Plane)
    (r d : ZMod n → ℝ)
    (hnorm : ∀ i, e i (p (i - 1)) = Plane.mk (-1) 0 ∧
      e i (p i) = 0 ∧ e i (p (i + 1)) = Plane.mk (r i) (d i * r i))
    (hr : ∀ i, 0 < r i) (hd : ∀ i, d i = 0 ∨ d i = 1)
    (hunit : ∀ i, d i = 1 → r i = 1) {h σ : ℝ}
    (hh : 0 < h) (hσ : 0 < σ) (hσh : σ < h / 2) :
    range (roundedPolygonalCurve h σ (fun k : ℤ => p k)) =
      ⋃ i : ZMod n, e i ⁻¹' {q : Plane |
        q 0 ∈ Icc (-(1 / 2 : ℝ)) (r i / 2) ∧
          q 1 = d i * Real.smoothMax (σ / h) (q 0) 0} := by
  rw [roundedPolygonalCurve.range_eq_iUnion_image_Icc_zmod hh hσ hσh.le]
  apply iUnion_congr
  intro i
  have he := affine_image_smoothCorner_Icc (e i) (hnorm i).1 (hnorm i).2.1
    (hnorm i).2.2 (hr i) (hd i) (hunit i) hh hσ hσh
  rw [← he, preimage_image_eq _ (e i).injective]

theorem PrePolygon.exists_affine_graphs_roundedPolygonalCurve
    {m : ℕ} (P : PrePolygon m) :
    ∃ (e : ZMod (m + 3) → Plane ≃ᵃ[ℝ] Plane)
      (U : ZMod (m + 3) → Set Plane) (r d s : ZMod (m + 3) → ℝ),
      (∀ i, IsOpen (U i) ∧ Convex ℝ (U i) ∧ P.vertex i ∈ U i ∧ 0 < r i ∧
        (d i = 0 ∨ d i = 1) ∧ (s i = -1 ∨ s i = 1) ∧
        e i (P.vertex i) = 0 ∧ e i (P.vertex (i - 1)) = Plane.mk (-1) 0 ∧
        e i (P.vertex (i + 1)) = Plane.mk (r i) (d i * r i) ∧
        (d i = 1 → r i = 1) ∧
        ∀ p ∈ U i, (p ∈ closure (inside P.carrier) ↔
          0 ≤ s i * ((e i p) 1 - d i * max ((e i p) 0) 0)) ∧
          (p ∈ P.carrier ↔ (e i p) 1 = d i * max ((e i p) 0) 0)) ∧
      ∀ h σ : ℝ, 0 < h → 0 < σ → σ < h / 2 →
        range (roundedPolygonalCurve h σ (fun k : ℤ => P.vertex k)) =
          ⋃ i, e i ⁻¹' {q : Plane | q 0 ∈ Icc (-(1 / 2 : ℝ)) (r i / 2) ∧
            q 1 = d i * Real.smoothMax (σ / h) (q 0) 0} := by
  classical
  choose e U r d s hU hcU hiU hr hd hs he0 hea heb hstraight hunit hside using
    P.exists_affine_vertex_graph_sides_normalized
  have hezero (i) : e i (P.vertex i) = 0 := by
    rw [he0 i]
    ext j
    fin_cases j <;> rfl
  refine ⟨e, U, r, d, s, ?_, ?_⟩
  · intro i
    exact ⟨hU i, hcU i, hiU i, hr i, hd i, hs i, hezero i, hea i, heb i, hunit i,
      fun p hp => ⟨(hside i p hp).1, (hside i p hp).2.2.2⟩⟩
  · intro h σ hh hσ hσh
    exact range_roundedPolygonalCurve_eq_iUnion_graphs P.vertex e r d
      (fun i => ⟨hea i, hezero i, heb i⟩) hr hd hunit hh hσ hσh

open LeanEval.Topology.ClassificationOfSurfaces.Moise in
theorem affine_smooth_corner_regular
    (e : Plane ≃ᵃ[ℝ] Plane) (ε d σ : ℝ) (hσ : σ ≠ 0) :
    ContDiff ℝ ∞ (fun p => σ * ((e p) 1 - d * Real.smoothMax ε ((e p) 0) 0)) ∧
      ∀ p, fderiv ℝ (fun q => σ * ((e q) 1 - d * Real.smoothMax ε ((e q) 0) 0)) p ≠ 0 := by
  let f := cartesianX.comp e.toAffineMap
  let g := cartesianY.comp e.toAffineMap
  have hf : ContDiff ℝ ∞ f :=
    (⟨f, f.continuous_of_finiteDimensional⟩ : Plane →ᴬ[ℝ] ℝ).contDiff
  have hg : ContDiff ℝ ∞ g :=
    (⟨g, g.continuous_of_finiteDimensional⟩ : Plane →ᴬ[ℝ] ℝ).contDiff
  have hH : ContDiff ℝ ∞ (fun p => σ * (g p - d * Real.smoothMax ε (f p) 0)) :=
    contDiff_const.mul (hg.sub (contDiff_const.mul
      ((Real.smoothMax.contDiff ε).comp (hf.prodMk contDiff_const))))
  refine ⟨hH, fun p => ?_⟩
  let w := e.linear.symm (Plane.mk 0 1)
  have hfw : f.linear w = 0 := by
    change (e.linear (e.linear.symm (Plane.mk 0 1))) 0 = 0
    rw [e.linear.apply_symm_apply]
    rfl
  have hgw : g.linear w = 1 := by
    change (e.linear (e.linear.symm (Plane.mk 0 1))) 1 = 1
    rw [e.linear.apply_symm_apply]
    rfl
  have heq : (fun t : ℝ =>
      σ * (g (p + t • w) - d * Real.smoothMax ε (f (p + t • w)) 0)) =
      fun t => σ * (g p - d * Real.smoothMax ε (f p) 0) + t * σ := by
    funext t
    rw [add_comm p (t • w)]
    change σ * (g (t • w +ᵥ p) - d * Real.smoothMax ε (f (t • w +ᵥ p)) 0) = _
    rw [g.map_vadd, f.map_vadd, map_smul, map_smul, hgw, hfw]
    change σ * ((t * 1 + g p) - d * Real.smoothMax ε (t * 0 + f p) 0) = _
    simp only [mul_zero, zero_add, mul_one]
    ring
  have hline : HasLineDerivAt ℝ
      (fun q => σ * (g q - d * Real.smoothMax ε (f q) 0)) σ p w := by
    change HasDerivAt _ σ 0
    rw [heq]
    exact (hasDerivAt_mul_const σ).const_add
        (σ * (g p - d * Real.smoothMax ε (f p) 0))
  have hd := ((hH.differentiable (by simp)).differentiableAt (x := p)).hasFDerivAt
    |>.hasLineDerivAt w |>.unique hline
  intro hz
  change fderiv ℝ (fun q => σ * (g q - d * Real.smoothMax ε (f q) 0)) p = 0 at hz
  rw [hz, zero_apply] at hd
  exact hσ hd.symm

end Schoenflies
