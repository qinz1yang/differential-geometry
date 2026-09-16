import DifferentialGeometry.Topology.PiecewiseLinear.TransverseHeight
import DifferentialGeometry.Topology.PiecewiseLinear.HeightChange

open Set Topology

namespace DifferentialGeometry.Topology.PiecewiseLinear

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

theorem eventually_exists_homeomorph_adjust_height_preserving_submodule
    (P : Submodule ℝ E) (ℓ : E →L[ℝ] ℝ) {d : E} (hd : d ∈ P) (hℓd : ℓ d = 1)
    {G : E → E} (hG : IsPiecewiseAffineOn G univ) {k : NNReal} (hGlip : LipschitzWith k G) :
    ∀ᶠ f : E →L[ℝ] ℝ in 𝓝 ℓ, ∃ g : E ≃ₜ E,
      IsPLHomeomorphOn g univ univ ∧ g 0 = 0 ∧ g '' (P : Set E) = P ∧
      ∀ x, ℓ (g x) = ℓ x + (f - ℓ) (G x) - (f - ℓ) (G 0) := by
  obtain ⟨δ, hδ, hkδ⟩ := exists_pos_mul_lt (a := (1 : ℝ)) zero_lt_one ((k : ℝ) * ‖d‖)
  filter_upwards [Metric.ball_mem_nhds ℓ hδ] with f hf
  have hfδ : ‖f - ℓ‖ < δ := by simpa only [Metric.mem_ball, dist_eq_norm] using hf
  let φ : E → ℝ := fun x => (f - ℓ) (G x) - (f - ℓ) (G 0)
  have hφpl : IsPiecewiseAffineOn φ univ :=
    hG.affine_comp ((f - ℓ).toLinearMap.toAffineMap - AffineMap.const ℝ E ((f - ℓ) (G 0)))
  have hφlip : LipschitzWith (‖f - ℓ‖₊ * k) φ := by
    apply LipschitzWith.of_dist_le_mul
    intro x y
    simpa only [φ, dist_sub_right, Function.comp_apply] using ((f - ℓ).lipschitz.comp hGlip).dist_le_mul x y
  have hvpl : IsPiecewiseAffineOn (fun x => φ x • d) univ :=
    hφpl.affine_comp (LinearMap.toSpanSingleton ℝ E d).toAffineMap
  have hvlip : LipschitzWith ((‖f - ℓ‖₊ * k) * ‖d‖₊) (fun x => φ x • d) := by
    apply LipschitzWith.of_dist_le_mul
    intro x y
    rw [dist_eq_norm, ← sub_smul, norm_smul, NNReal.coe_mul, coe_nnnorm]
    have hbound := hφlip.dist_le_mul x y
    rw [dist_eq_norm] at hbound
    calc ‖φ x - φ y‖ * ‖d‖ ≤ (((‖f - ℓ‖₊ * k : NNReal) : ℝ) * dist x y) * ‖d‖ :=
        mul_le_mul_of_nonneg_right hbound (norm_nonneg _)
      _ = ((‖f - ℓ‖₊ * k : NNReal) : ℝ) * ‖d‖ * dist x y := by ring
  have hsmall : (‖f - ℓ‖₊ * k) * ‖d‖₊ < 1 := by
    change (‖f - ℓ‖ * (k : ℝ)) * ‖d‖ < 1
    calc (‖f - ℓ‖ * (k : ℝ)) * ‖d‖ = ((k : ℝ) * ‖d‖) * ‖f - ℓ‖ := by ring
      _ ≤ ((k : ℝ) * ‖d‖) * δ :=
        mul_le_mul_of_nonneg_left hfδ.le (mul_nonneg k.property (norm_nonneg _))
      _ < 1 := hkδ
  have hg := isPLHomeomorphOn_id_add_of_lipschitz hvpl hvlip hsmall
  let g := (Homeomorph.Set.univ E).symm.trans (hg.homeomorph.trans (Homeomorph.Set.univ E))
  have hzero : g 0 = 0 := by
    change 0 + ((f - ℓ) (G 0) - (f - ℓ) (G 0)) • d = 0
    rw [sub_self, zero_smul, add_zero]
  have hpoint : ∀ x, g x ∈ P ↔ x ∈ P := fun x => P.add_mem_iff_left (P.smul_mem (φ x) hd)
  have himage : g '' (P : Set E) = P := by
    apply Subset.antisymm
    · rintro _ ⟨x, hx, rfl⟩
      exact (hpoint x).mpr hx
    · intro y hy
      refine ⟨g.symm y, ?_, g.apply_symm_apply y⟩
      exact (hpoint (g.symm y)).mp (by rwa [g.apply_symm_apply])
  refine ⟨g, hg, hzero, himage, fun x => ?_⟩
  change ℓ (x + φ x • d) = _
  rw [map_add, map_smul, hℓd, smul_eq_mul, mul_one]
  dsimp only [φ]
  ring

theorem eventually_hasPLCrossingAt_of_height_preserving_chart
    (h : E ≃ₜ E) (hh : IsPLHomeomorphOn h univ univ) (P : Submodule ℝ E)
    (hP : Module.finrank ℝ P = 2) (hdimE : Module.finrank ℝ E = 3)
    (ℓ : E →L[ℝ] ℝ) {d : E} (hd : d ∈ P) (hℓd : ℓ d ≠ 0)
    (hheight : ∀ᶠ y in 𝓝 0, ℓ (h y) = ℓ y + ℓ (h 0)) {S : Set E}
    (hS : ∀ᶠ y in 𝓝 (h 0), y ∈ S ↔ y ∈ h '' (P : Set E)) :
    ∀ᶠ f : E →L[ℝ] ℝ in 𝓝 ℓ, HasPLCrossingAt S {y | f y = f (h 0)} (h 0) := by
  obtain ⟨C, hC, -, hC0⟩ := exists_isHPolytope_subset_mem_nhds (x := (0 : E)) (U := univ) Filter.univ_mem
  have hzeroC : (0 : E) ∈ C := mem_of_mem_nhds hC0
  obtain ⟨G, k, hG, hGlip, hGC, -, -⟩ :=
    (hh.isPiecewiseAffineOn.mono_of_isPolyhedron hC.isPolyhedron (subset_univ C)).exists_lipschitz_extension
      hC.isPolyhedron isOpen_univ (subset_univ C)
  let u : E := (ℓ d)⁻¹ • d
  have huP : u ∈ P := P.smul_mem _ hd
  have hℓu : ℓ u = 1 := by
    dsimp only [u]
    rw [map_smul, smul_eq_mul, inv_mul_cancel₀ hℓd]
  have hcross : HasPLCrossingAt (P : Set E) {y | ℓ y = 0} 0 := by
    have hc := hasPLCrossingAt_affineSubspace_fiber P hP hdimE ℓ.toLinearMap hd hℓd 0
    change HasPLCrossingAt {y | y - 0 ∈ P} {y | ℓ y = ℓ 0} 0 at hc
    have hPeq : {y : E | y - 0 ∈ P} = (P : Set E) := by
      ext y
      simp only [mem_ofPred_eq, sub_zero, SetLike.mem_coe]
    rwa [hPeq, map_zero] at hc
  filter_upwards [eventually_exists_homeomorph_adjust_height_preserving_submodule P ℓ huP hℓu hG hGlip]
    with f hf
  obtain ⟨g, hg, hg0, hgP, hformula⟩ := hf
  let e : E ≃ₜ E := g.symm.trans h
  have he : IsPLHomeomorphOn e univ univ := hg.homeomorph_symm.trans hh
  have hgs0 : g.symm 0 = 0 := g.injective ((g.apply_symm_apply 0).trans hg0.symm)
  have he0 : e 0 = h 0 := by
    change h (g.symm 0) = h 0
    rw [hgs0]
  have hgsP : g.symm '' (P : Set E) = P := by
    calc g.symm '' (P : Set E) = g.symm '' (g '' (P : Set E)) :=
        congrArg (fun A : Set E => g.symm '' A) hgP.symm
      _ = P := by rw [image_image]; simp only [g.symm_apply_apply, image_id']
  have heP : e '' (P : Set E) = h '' (P : Set E) := by
    change (h ∘ g.symm) '' (P : Set E) = h '' (P : Set E)
    rw [image_comp, hgsP]
  have hinv : Filter.Tendsto h.symm (𝓝 (h 0)) (𝓝 0) := by
    simpa only [h.symm_apply_apply] using (h.symm.continuous.continuousAt (x := h 0)).tendsto
  have hnear : ∀ᶠ y in 𝓝 (h 0), h.symm y ∈ C ∧
      ℓ (h (h.symm y)) = ℓ (h.symm y) + ℓ (h 0) :=
    hinv.eventually (Filter.Eventually.and hC0 hheight)
  have hplane : ∀ᶠ y in 𝓝 (h 0), y ∈ e '' {z | ℓ z = 0} ↔ f y = f (h 0) := by
    filter_upwards [hnear] with y hy
    have hmem : y ∈ e '' {z | ℓ z = 0} ↔ ℓ (e.symm y) = 0 := by
      constructor
      · rintro ⟨z, hz, rfl⟩
        simpa only [e.symm_apply_apply, mem_ofPred_eq] using hz
      · intro hz
        exact ⟨e.symm y, hz, e.apply_symm_apply y⟩
    rw [hmem]
    change ℓ (g (h.symm y)) = 0 ↔ f y = f (h 0)
    rw [hformula, hGC hy.1, hGC hzeroC, h.apply_symm_apply]
    simp only [sub_apply]
    have hhy : ℓ y = ℓ (h.symm y) + ℓ (h 0) := by
      simpa only [h.apply_symm_apply] using hy.2
    constructor <;> intro heq <;> linarith
  have htransport := hcross.image_homeomorph e he
  rw [heP, he0] at htransport
  exact htransport.congr (hS.mono fun _ hy => hy.symm) hplane

end DifferentialGeometry.Topology.PiecewiseLinear
