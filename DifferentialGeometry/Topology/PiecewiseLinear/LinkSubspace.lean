import DifferentialGeometry.Topology.PiecewiseLinear.GeneralPosition
import DifferentialGeometry.Topology.PiecewiseLinear.ConeComplex
import Mathlib.LinearAlgebra.Dual.Lemmas

open Set Topology

namespace DifferentialGeometry.Topology.PiecewiseLinear

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem eventually_mem_closedStar_iff (K : Geometry.SimplicialComplex ℝ E) [Finite K.faces] (p : E) :
    ∀ᶠ x in 𝓝 p, x ∈ closedStar K p ↔ x ∈ K.space := by
  obtain ⟨V, hV, hVstar⟩ := mem_nhdsWithin_iff_exists_mem_nhds_inter.mp
    (closedStar_mem_nhdsWithin K p)
  filter_upwards [hV] with x hx
  exact ⟨fun h => closedStar_subset_space K p h, fun h => hVstar ⟨hx, h⟩⟩

theorem geometricLink_space_eq_inter_submodule_of_eventually [DecidableEq E]
    (K M : Geometry.SimplicialComplex ℝ E) [Finite M.faces] (hM : M.faces ⊆ K.faces)
    {p : E} (hp : {p} ∈ M.faces) (P : Submodule ℝ E)
    (hlocal : ∀ᶠ x in 𝓝 p, x ∈ M.space ↔ x - p ∈ P) :
    (SimplicialComplex.geometricLink M {p}).space =
      (SimplicialComplex.geometricLink K {p}).space ∩ {x | x - p ∈ P} := by
  have hsub : (SimplicialComplex.geometricLink M {p}).space ⊆
      (SimplicialComplex.geometricLink K {p}).space := by
    apply space_mono_of_faces_subset
    intro s hs
    obtain ⟨hne, hp, hs⟩ := (SimplicialComplex.mem_geometricLink_singleton M p s).mp hs
    exact (SimplicialComplex.mem_geometricLink_singleton K p s).mpr ⟨hne, hp, hM hs⟩
  have hstar : ∀ᶠ x in 𝓝 p, x ∈ closedStar M p ↔ x - p ∈ P := by
    filter_upwards [eventually_mem_closedStar_iff M p, hlocal] with x hx hy
    exact hx.trans hy
  have hray (z : E) : Filter.Tendsto (fun r : ℝ => p + r • (z - p)) (𝓝[>] 0) (𝓝 p) := by
    have hcont : Continuous (fun r : ℝ => p + r • (z - p)) :=
      continuous_const.add (continuous_id.smul continuous_const)
    simpa only [zero_smul, add_zero] using (hcont.tendsto 0).mono_left nhdsWithin_le_nhds
  apply Subset.antisymm
  · intro z hz
    obtain ⟨r, hrLocal, hr, hr1⟩ := ((hray z).eventually hlocal).and
      (Ioo_mem_nhdsGT (zero_lt_one' ℝ)) |>.exists
    have hzP := hrLocal.mp (mem_convexHull_insert_of_mem_geometricLink_space M hz hr.le hr1.le)
    have hsmul : r • (z - p) ∈ P := by simpa only [add_sub_cancel_left] using hzP
    have hzP' : z - p ∈ P := by
      have h := P.smul_mem r⁻¹ hsmul
      simpa only [smul_smul, inv_mul_cancel₀ hr.ne', one_smul] using h
    exact ⟨hsub hz, hzP'⟩
  · rintro z ⟨hzK, hzP⟩
    obtain ⟨r, hrStar, hr, hr1⟩ := ((hray z).eventually hstar).and
      (Ioo_mem_nhdsGT (zero_lt_one' ℝ)) |>.exists
    have hxstar : p + r • (z - p) ∈ closedStar M p := hrStar.mpr (by
      simpa only [add_sub_cancel_left] using P.smul_mem r hzP)
    rw [closedStar_eq_coneComplex_space M hp] at hxstar
    rcases (mem_coneComplex_space_iff _).mp hxstar with hx | ⟨w, hw, t, ht, -, hwt⟩
    · have hzero : r • (z - p) = 0 := by simpa only [add_eq_left] using hx
      have hzp := sub_eq_zero.mp ((smul_eq_zero.mp hzero).resolve_left hr.ne')
      exact (notMem_geometricLink_space K (hzp ▸ hzK)).elim
    · have hzw := (isRadiallyInjective_geometricLink K).eq_of_add_smul_eq hzK (hsub hw) hr ht hwt
      exact hzw.symm ▸ hw

theorem exists_pair_geometricLink_inter_span_singleton [dE : DecidableEq E]
    (K : Geometry.SimplicialComplex ℝ E) [Finite K.faces] {p : E} (hp : {p} ∈ K.faces)
    (hK : K.space ∈ 𝓝 p) {d : E} (hd : d ≠ 0) :
    ∃ a b : E, a ≠ b ∧ (SimplicialComplex.geometricLink K {p}).space ∩
      {x | x - p ∈ Submodule.span ℝ ({d} : Set E)} = {a, b} := by
  classical
  cases Subsingleton.elim dE (Classical.decEq E)
  have hdir (v : E) : ∀ᶠ r : ℝ in 𝓝 0, 0 < r → p + r • v ∈ K.space := by
    have hcont : Continuous (fun r : ℝ => p + r • v) :=
      continuous_const.add (continuous_id.smul continuous_const)
    have htend : Filter.Tendsto (fun r : ℝ => p + r • v) (𝓝 0) (𝓝 p) := by
      simpa only [zero_smul, add_zero] using hcont.tendsto 0
    exact (htend.eventually_mem hK).mono fun _ h _ => h
  obtain ⟨a, ha, haK⟩ := exists_ray_mem_geometricLink_space_of_eventually K hp hd (hdir d)
  obtain ⟨b, hb, hbK⟩ := exists_ray_mem_geometricLink_space_of_eventually K hp (neg_ne_zero.mpr hd) (hdir (-d))
  have hab : p + a • d ≠ p + b • (-d) := by
    intro h
    have hvec : a • d = b • (-d) := add_left_cancel h
    have hzero : (a + b) • d = 0 := by rw [add_smul, hvec, smul_neg, neg_add_cancel]
    exact (ne_of_gt (add_pos ha hb)) ((smul_eq_zero.mp hzero).resolve_right hd)
  refine ⟨p + a • d, p + b • (-d), hab, ?_⟩
  ext x
  constructor
  · rintro ⟨hx, hxd⟩
    obtain ⟨t, ht⟩ := Submodule.mem_span_singleton.mp hxd
    rcases lt_trichotomy t 0 with htneg | htzero | htpos
    · have hbx : p + b • (-d) = p + ((-b) / t) • (x - p) := by
        rw [← ht, smul_smul, div_mul_cancel₀ _ htneg.ne, neg_smul, smul_neg]
      have heq := isRadiallyInjective_geometricLink K x hx _ hbK ((-b) / t)
        (div_pos_of_neg_of_neg (neg_neg_of_pos hb) htneg) hbx
      exact Or.inr heq.symm
    · have hxp : x = p := by rw [htzero, zero_smul] at ht; exact sub_eq_zero.mp ht.symm
      exact (notMem_geometricLink_space K (hxp ▸ hx)).elim
    · have hax : p + a • d = p + (a / t) • (x - p) := by
        rw [← ht, smul_smul, div_mul_cancel₀ _ htpos.ne']
      have heq := isRadiallyInjective_geometricLink K x hx _ haK (a / t) (div_pos ha htpos) hax
      exact Or.inl heq.symm
  · rintro (rfl | rfl)
    · exact ⟨haK, Submodule.mem_span_singleton.mpr ⟨a, by simp only [add_sub_cancel_left]⟩⟩
    · exact ⟨hbK, Submodule.mem_span_singleton.mpr ⟨-b, by
        simp only [add_sub_cancel_left, neg_smul, smul_neg]⟩⟩

theorem exists_pair_geometricLink_fiber_of_eventually_plane
    [FiniteDimensional ℝ E] [dE : DecidableEq E]
    (K M : Geometry.SimplicialComplex ℝ E) [Finite K.faces] [Finite M.faces]
    (hM : M.faces ⊆ K.faces) {p : E} (hp : {p} ∈ M.faces) (hK : K.space ∈ 𝓝 p)
    (P : Submodule ℝ E) (hP : Module.finrank ℝ P = 2)
    (hlocal : ∀ᶠ x in 𝓝 p, x ∈ M.space ↔ x - p ∈ P)
    (ℓ : E →ₗ[ℝ] ℝ) (hpℓ : ℓ p = 0) {v : E} (hvP : v ∈ P) (hvℓ : ℓ v ≠ 0) :
    (∃ a b : E, a ≠ b ∧ (SimplicialComplex.geometricLink M {p}).space ∩ {x | ℓ x = 0} = {a, b}) ∧
      (∃ x ∈ (SimplicialComplex.geometricLink M {p}).space, 0 < ℓ x) ∧
      (∃ x ∈ (SimplicialComplex.geometricLink M {p}).space, ℓ x < 0) := by
  classical
  cases Subsingleton.elim dE (Classical.decEq E)
  have hℓ : ℓ ≠ 0 := fun h => hvℓ (by rw [h, LinearMap.zero_apply])
  have hsup : P ⊔ LinearMap.ker ℓ = ⊤ := sup_ker_eq_top_of_apply_ne_zero P ℓ hvP hvℓ
  have hker := Module.Dual.finrank_ker_add_one_of_ne_zero hℓ
  have hinf : Module.finrank ℝ (P ⊓ LinearMap.ker ℓ : Submodule ℝ E) = 1 := by
    have h := Submodule.finrank_sup_add_finrank_inf_eq P (LinearMap.ker ℓ)
    rw [hsup, finrank_top, hP] at h
    omega
  let I := P ⊓ LinearMap.ker ℓ
  have : Nontrivial I := Module.nontrivial_of_finrank_pos (by rw [show Module.finrank ℝ I = 1 from hinf]; norm_num)
  obtain ⟨d, hd⟩ := exists_ne (0 : I)
  have hd0 : (d : E) ≠ 0 := fun h => hd (Subtype.ext h)
  have hspan : I = Submodule.span ℝ ({(d : E)} : Set E) :=
    eq_span_singleton_of_mem_of_finrank_eq_one hinf d.property hd0
  have hlink := geometricLink_space_eq_inter_submodule_of_eventually K M hM hp P hlocal
  have hpair : ∃ a b : E, a ≠ b ∧
      (SimplicialComplex.geometricLink M {p}).space ∩ {x | ℓ x = 0} = {a, b} := by
    obtain ⟨a, b, hab, hpair⟩ := exists_pair_geometricLink_inter_span_singleton K (hM hp) hK hd0
    refine ⟨a, b, hab, ?_⟩
    rw [← hpair, ← hspan, hlink]
    ext x
    simp only [mem_inter_iff, mem_ofPred_eq, I, Submodule.mem_inf, LinearMap.mem_ker,
      map_sub, hpℓ, sub_zero]
    tauto
  have hray (w : E) (hw : w ≠ 0) :
      ∃ s : ℝ, 0 < s ∧ p + s • w ∈ (SimplicialComplex.geometricLink K {p}).space := by
    apply exists_ray_mem_geometricLink_space_of_eventually K (hM hp) hw
    have hcont : Continuous (fun s : ℝ => p + s • w) :=
      continuous_const.add (continuous_id.smul continuous_const)
    have htend : Filter.Tendsto (fun s : ℝ => p + s • w) (𝓝 0) (𝓝 p) := by
      simpa only [zero_smul, add_zero] using hcont.tendsto 0
    exact (htend.eventually_mem hK).mono fun _ h _ => h
  let w := (ℓ v)⁻¹ • v
  have hwP : w ∈ P := P.smul_mem _ hvP
  have hwℓ : ℓ w = 1 := by simp only [w, map_smul, smul_eq_mul, inv_mul_cancel₀ hvℓ]
  have hw : w ≠ 0 := fun h => one_ne_zero (hwℓ.symm.trans (by rw [h, map_zero]))
  obtain ⟨s, hs, hsK⟩ := hray w hw
  obtain ⟨t, ht, htK⟩ := hray (-w) (neg_ne_zero.mpr hw)
  refine ⟨hpair, ⟨p + s • w, ?_, ?_⟩, ⟨p + t • (-w), ?_, ?_⟩⟩
  · rw [hlink]
    exact ⟨hsK, by simpa only [mem_ofPred_eq, add_sub_cancel_left] using P.smul_mem s hwP⟩
  · simpa only [map_add, hpℓ, map_smul, hwℓ, smul_eq_mul, mul_one, zero_add] using hs
  · rw [hlink]
    exact ⟨htK, by simpa only [mem_ofPred_eq, add_sub_cancel_left] using P.smul_mem t (P.neg_mem hwP)⟩
  · simpa only [map_add, hpℓ, map_smul, map_neg, hwℓ, smul_eq_mul, mul_neg, mul_one,
      zero_add, neg_lt_zero] using ht
end DifferentialGeometry.Topology.PiecewiseLinear
