/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.Topology.PiecewiseLinear.PolygonalCircleEmbedding

open Set Topology

namespace DifferentialGeometry.Topology.PiecewiseLinear

local notation "E3" => EuclideanSpace ℝ (Fin 3)

theorem IsPLHomeomorphOn.exists_polygonal_circle_product_coordinates
    {T J Q : Set E3} {f : E3 × E3 → E3} (hf : IsPLHomeomorphOn f (J ×ˢ Q) T)
    (hJ : IsPLSphere 1 J) (hQ : IsPLSphere 1 Q) :
    ∃ e : (loopCircle × loopCircle) ≃ₜ T, ∀ m n u v : ℤ, u * m + v * n = 1 →
      IsPLSphere 1 (range fun t : loopCircle => (e (m • t, n • t) : E3)) := by
  obtain ⟨α, hα⟩ := hJ
  obtain ⟨β, hβ⟩ := hQ
  let eJ := stdTriangleCircleHomeomorph.trans hα.homeomorph
  let eQ := stdTriangleCircleHomeomorph.trans hβ.homeomorph
  let e : (loopCircle × loopCircle) ≃ₜ T := (eJ.prodCongr eQ).trans
    ((Homeomorph.Set.prod J Q).symm.trans hf.homeomorph)
  refine ⟨e, fun m n u v hbez => ?_⟩
  apply isPLSphere_one_range_of_piecewiseAffine_circle
  · intro x y hxy
    have h := e.injective (Subtype.ext hxy)
    have hm := congrArg Prod.fst h
    have hn := congrArg Prod.snd h
    change m • x = m • y at hm
    change n • x = n • y at hn
    calc x = (u * m + v * n) • x := by rw [hbez, one_smul]
      _ = u • (m • x) + v • (n • x) := by rw [add_smul, mul_smul, mul_smul]
      _ = u • (m • y) + v • (n • y) := by rw [hm, hn]
      _ = (u * m + v * n) • y := by rw [add_smul, mul_smul, mul_smul]
      _ = y := by rw [hbez, one_smul]
  · let A : ℝ →ᵃ[ℝ] ℝ × ℝ := AffineMap.lineMap 0 ((m : ℝ), (n : ℝ))
    have hA (t : ℝ) : A t = ((m : ℝ) * t, (n : ℝ) * t) := by
      simp only [A, AffineMap.lineMap_apply_module]
      apply Prod.ext <;> simp [smul_eq_mul, mul_comm]
    let c : ℝ → Fin 3 → ℝ := fun t => stdTriangleCircleHomeomorph (t : loopCircle)
    have hc : IsPiecewiseAffineOn c univ := isPiecewiseAffineOn_stdTriangleCircleCover
    have hp := (hc.prodMap hc).comp (isPiecewiseAffineOn_of_affine A isOpen_univ)
    have hp' : IsPiecewiseAffineOn (fun t : ℝ =>
        (c ((m : ℝ) * t), c ((n : ℝ) * t))) univ := by
      simpa only [univ_prod_univ, preimage_univ, inter_univ, Function.comp_def,
        Prod.map_apply, hA] using hp
    let g : ℝ → (Fin 3 → ℝ) × (Fin 3 → ℝ) :=
      fun t => (c ((m : ℝ) * t), c ((n : ℝ) * t))
    have hgmaps : univ ⊆ g ⁻¹' (stdSimplexBoundary 2 ×ˢ stdSimplexBoundary 2) :=
      fun t _ => ⟨(stdTriangleCircleHomeomorph _).2, (stdTriangleCircleHomeomorph _).2⟩
    have hαβ := (hα.prodMap hβ).isPiecewiseAffineOn.comp hp'
    change IsPiecewiseAffineOn (Prod.map α β ∘ g)
      (univ ∩ g ⁻¹' (stdSimplexBoundary 2 ×ˢ stdSimplexBoundary 2)) at hαβ
    rw [inter_eq_left.mpr hgmaps] at hαβ
    have hfmap : univ ⊆ (Prod.map α β ∘ g) ⁻¹' (J ×ˢ Q) := by
      intro t _
      exact ⟨hα.bijOn.mapsTo (hgmaps (mem_univ t)).1,
        hβ.bijOn.mapsTo (hgmaps (mem_univ t)).2⟩
    have hresult := hf.isPiecewiseAffineOn.comp hαβ
    rw [inter_eq_left.mpr hfmap] at hresult
    apply hresult.congr
    intro t _
    change f (α (stdTriangleCircleHomeomorph (m • (t : loopCircle))),
      β (stdTriangleCircleHomeomorph (n • (t : loopCircle)))) =
        f (α (stdTriangleCircleHomeomorph (((m : ℝ) * t : ℝ) : loopCircle)),
          β (stdTriangleCircleHomeomorph (((n : ℝ) * t : ℝ) : loopCircle)))
    rw [← AddCircle.coe_zsmul, ← AddCircle.coe_zsmul, zsmul_eq_mul, zsmul_eq_mul]

end DifferentialGeometry.Topology.PiecewiseLinear
