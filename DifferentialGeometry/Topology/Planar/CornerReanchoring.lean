import DifferentialGeometry.Topology.Planar.CornerNormalization
import DifferentialGeometry.Analysis.Convex.SegmentGerm
import DifferentialGeometry.Topology.Planar.PolygonCorners

open Set

namespace Schoenflies

theorem exists_pos_smul_pair_of_sameRay_or
    {u v x y : Plane} (huv : Plane.det u v ≠ 0) (hx : x ≠ 0) (hy : y ≠ 0)
    (hu : SameRay ℝ u x ∨ SameRay ℝ u y)
    (hv : SameRay ℝ v x ∨ SameRay ℝ v y) :
    Plane.det x y ≠ 0 ∧ ∃ r s : ℝ, 0 < r ∧ 0 < s ∧
      ((u = r • x ∧ v = s • y) ∨ (u = r • y ∧ v = s • x)) := by
  have hune : u ≠ 0 := by intro he; apply huv; simp [he, Plane.det]
  have hvne : v ≠ 0 := by intro he; apply huv; simp [he, Plane.det]
  rcases hu with hu | hu <;> rcases hv with hv | hv
  · obtain ⟨r, _, hur⟩ := hu.exists_pos_right hune hx
    obtain ⟨s, _, hvs⟩ := hv.exists_pos_right hvne hx
    exact False.elim (huv (by simp [hur, hvs]))
  · obtain ⟨r, hr, hur⟩ := hu.exists_pos_right hune hx
    obtain ⟨s, hs, hvs⟩ := hv.exists_pos_right hvne hy
    refine ⟨?_, r, s, hr, hs, Or.inl ⟨hur, hvs⟩⟩
    intro he
    exact huv (by simp [hur, hvs, he])
  · obtain ⟨r, hr, hur⟩ := hu.exists_pos_right hune hy
    obtain ⟨s, hs, hvs⟩ := hv.exists_pos_right hvne hx
    refine ⟨?_, r, s, hr, hs, Or.inr ⟨hur, hvs⟩⟩
    intro he
    have hyx : Plane.det y x = 0 := by rw [Plane.det_comm, he, neg_zero]
    exact huv (by simp [hur, hvs, hyx])
  · obtain ⟨r, _, hur⟩ := hu.exists_pos_right hune hy
    obtain ⟨s, _, hvs⟩ := hv.exists_pos_right hvne hy
    exact False.elim (huv (by simp [hur, hvs]))

def cornerSwap : Plane ≃ₗ[ℝ] Plane := by
  let L : Plane →ₗ[ℝ] Plane :=
    { toFun := fun p => Plane.mk (-p 0) (p 1 - p 0)
      map_add' := by
        intro p q
        ext i
        fin_cases i <;> simp [Plane.mk] <;> ring
      map_smul' := by
        intro r p
        ext i
        fin_cases i <;> simp [Plane.mk]
        ring }
  exact LinearEquiv.ofInvolutive L (by
    intro p
    ext i
    fin_cases i <;> simp [L, Plane.mk])

private theorem cornerSwap_profiles (p : Plane) :
    (cornerSwap p) 1 - max ((cornerSwap p) 0) 0 = p 1 - max (p 0) 0 ∧
    ∀ ε : ℝ, ε ≠ 0 → (cornerSwap p) 1 - Real.smoothMax ε ((cornerSwap p) 0) 0 =
      p 1 - Real.smoothMax ε (p 0) 0 := by
  change (p 1 - p 0) - max (-p 0) 0 = p 1 - max (p 0) 0 ∧ _
  constructor
  · rcases le_total (p 0) 0 with h | h
    · rw [max_eq_right h, max_eq_left (neg_nonneg.mpr h)]
      ring
    · rw [max_eq_left h, max_eq_right (neg_nonpos.mpr h)]
      ring
  · intro ε hε
    change (p 1 - p 0) - Real.smoothMax ε (-p 0) 0 = _
    have h := Real.smoothMax.add_right ε 0 (p 0) (-p 0)
    simp only [zero_add, add_neg_cancel] at h
    rw [h, Real.smoothMax.comm hε 0 (p 0)]
    ring

private theorem corner_profiles_smul {a : ℝ} (ha : 0 < a) (p : Plane) :
    (a • p) 1 - max ((a • p) 0) 0 = a * (p 1 - max (p 0) 0) ∧
    ∀ ε : ℝ, (a • p) 1 - Real.smoothMax (a * ε) ((a • p) 0) 0 =
      a * (p 1 - Real.smoothMax ε (p 0) 0) := by
  have hmax := mul_max_of_nonneg (p 0) (0 : ℝ) ha.le
  simp only [mul_zero] at hmax
  constructor
  · change a * p 1 - max (a * p 0) 0 = _
    rw [← hmax]
    ring
  · intro ε
    have h := Real.smoothMax.mul_left a ε (p 0) 0
    simp only [mul_zero] at h
    change a * p 1 - Real.smoothMax (a * ε) (a * p 0) 0 = _
    rw [h]
    ring

private theorem exists_scaled_affine_corner_chart
    (e : Plane ≃ᵃ[ℝ] Plane) {a b c : Plane} {A B : ℝ} (hA : A ≠ 0)
    (ha : e a = Plane.mk (-A) 0) (hb : e b = Plane.mk B B) (hc : e c = 0) :
    ∃ f : Plane ≃ᵃ[ℝ] Plane, f c = 0 ∧ f a = Plane.mk (-1) 0 ∧
      f b = Plane.mk (B / A) (B / A) ∧ ∀ p, f p = A⁻¹ • e p := by
  let f := e.trans (LinearEquiv.smulOfNeZero ℝ Plane A⁻¹ (inv_ne_zero hA)).toAffineEquiv
  have hf (p : Plane) : f p = A⁻¹ • e p := rfl
  refine ⟨f, ?_, ?_, ?_, hf⟩
  · rw [hf, hc, smul_zero]
  · rw [hf, ha]
    ext i
    fin_cases i
    · change A⁻¹ * (-A) = -1
      rw [mul_neg, inv_mul_cancel₀ hA]
    · change A⁻¹ * 0 = 0
      exact mul_zero _
  · rw [hf, hb]
    ext i
    fin_cases i <;> change A⁻¹ * B = B / A <;> ring

theorem exists_reanchored_affine_corner_chart
    (e : Plane ≃ᵃ[ℝ] Plane) {a b c a' b' : Plane} {r α β : ℝ}
    (hr : 0 < r) (hα : 0 < α) (hβ : 0 < β)
    (ha' : e a' = Plane.mk (-1) 0) (hb' : e b' = Plane.mk r r) (hc : e c = 0)
    (hmatch : (a - c = α • (a' - c) ∧ b - c = β • (b' - c)) ∨
      (a - c = α • (b' - c) ∧ b - c = β • (a' - c))) :
    ∃ (f : Plane ≃ᵃ[ℝ] Plane) (ρ ℓ : ℝ), 0 < ρ ∧ 0 < ℓ ∧
      f c = 0 ∧ f a = Plane.mk (-1) 0 ∧ f b = Plane.mk ρ ρ ∧
      ((∀ p, f p = ℓ • e p) ∨ (∀ p, f p = ℓ • cornerSwap (e p))) ∧
      (∀ p, (f p) 1 - max ((f p) 0) 0 = ℓ * ((e p) 1 - max ((e p) 0) 0)) ∧
      ∀ ε : ℝ, ε ≠ 0 → ∀ p,
        (f p) 1 - Real.smoothMax (ℓ * ε) ((f p) 0) 0 =
          ℓ * ((e p) 1 - Real.smoothMax ε ((e p) 0) 0) := by
  have hmap (x y : Plane) (s : ℝ) (h : x - c = s • (y - c)) : e x = s • e y := by
    have hv (q : Plane) : e.linear (q - c) = e q := by
      have hv' : e.linear (q - c) = e q - e c := e.toAffineMap.linearMap_vsub q c
      simpa only [hc, sub_zero] using hv'
    rw [← hv, h, map_smul, hv]
  obtain ⟨f, ρ, ℓ, hρ, hℓ, hfc, hfa, hfb, hform⟩ :
      ∃ (f : Plane ≃ᵃ[ℝ] Plane) (ρ ℓ : ℝ), 0 < ρ ∧ 0 < ℓ ∧
        f c = 0 ∧ f a = Plane.mk (-1) 0 ∧ f b = Plane.mk ρ ρ ∧
        ((∀ p, f p = ℓ • e p) ∨ (∀ p, f p = ℓ • cornerSwap (e p))) := by
    rcases hmatch with h | h
    · have hea : e a = Plane.mk (-α) 0 := by
        rw [hmap a a' α h.1, ha']
        ext i
        fin_cases i <;> simp [Plane.mk]
      have heb : e b = Plane.mk (β * r) (β * r) := by
        rw [hmap b b' β h.2, hb']
        ext i
        fin_cases i <;> rfl
      obtain ⟨f, hfc, hfa, hfb, hf⟩ :=
        exists_scaled_affine_corner_chart e hα.ne' hea heb hc
      exact ⟨f, β * r / α, α⁻¹, div_pos (mul_pos hβ hr) hα, inv_pos.mpr hα,
        hfc, hfa, hfb, Or.inl hf⟩
    · let E := e.trans cornerSwap.toAffineEquiv
      have hEc : E c = 0 := by change cornerSwap (e c) = 0; rw [hc, map_zero]
      have hEa : E a = Plane.mk (-(α * r)) 0 := by
        change cornerSwap (e a) = _
        rw [hmap a b' α h.1, hb']
        change Plane.mk (-(α * r)) (α * r - α * r) = Plane.mk (-(α * r)) 0
        rw [sub_self]
      have hEb : E b = Plane.mk β β := by
        change cornerSwap (e b) = _
        rw [hmap b a' β h.2, ha']
        change Plane.mk (-(β * (-1))) (β * 0 - β * (-1)) = Plane.mk β β
        simp only [mul_neg_one, neg_neg, mul_zero, zero_sub]
      obtain ⟨f, hfc, hfa, hfb, hf⟩ :=
        exists_scaled_affine_corner_chart E (mul_pos hα hr).ne' hEa hEb hEc
      exact ⟨f, β / (α * r), (α * r)⁻¹, div_pos hβ (mul_pos hα hr),
        inv_pos.mpr (mul_pos hα hr), hfc, hfa, hfb, Or.inr hf⟩
  refine ⟨f, ρ, ℓ, hρ, hℓ, hfc, hfa, hfb, hform, ?_, ?_⟩
  · intro p
    rcases hform with h | h
    · rw [h p]
      exact (corner_profiles_smul hℓ (e p)).1
    · rw [h p, (corner_profiles_smul hℓ (cornerSwap (e p))).1,
        (cornerSwap_profiles (e p)).1]
  · intro ε hε p
    rcases hform with h | h
    · rw [h p]
      exact (corner_profiles_smul hℓ (e p)).2 ε
    · rw [h p, (corner_profiles_smul hℓ (cornerSwap (e p))).2 ε,
        (cornerSwap_profiles (e p)).2 ε hε]


theorem PrePolygon.sameRay_incident_edges_of_local_graph
    {m : ℕ} (P : PrePolygon m) (i : ZMod (m + 3)) (e : Plane ≃ᵃ[ℝ] Plane)
    {U : Set Plane} {d : ℝ} (hU : IsOpen U) (hiU : P.vertex i ∈ U)
    (hec : e (P.vertex i) = 0)
    (hgraph : ∀ p ∈ U, p ∈ P.carrier → (e p) 1 = d * max ((e p) 0) 0) :
    (SameRay ℝ (P.vertex (i - 1) - P.vertex i)
        (e.symm (Plane.mk (-1) 0) - P.vertex i) ∨
      SameRay ℝ (P.vertex (i - 1) - P.vertex i)
        (e.symm (Plane.mk 1 d) - P.vertex i)) ∧
    (SameRay ℝ (P.vertex (i + 1) - P.vertex i)
        (e.symm (Plane.mk (-1) 0) - P.vertex i) ∨
      SameRay ℝ (P.vertex (i + 1) - P.vertex i)
        (e.symm (Plane.mk 1 d) - P.vertex i)) := by
  let a := e.symm (Plane.mk (-1) 0)
  let b := e.symm (Plane.mk 1 d)
  have heca : e.symm (Plane.mk 0 0) = P.vertex i := by
    apply e.injective
    rw [e.apply_symm_apply, hec]
    ext j
    fin_cases j <;> rfl
  let V := U ∩ e ⁻¹' {q : Plane | q 0 ∈ Ioo (-1 : ℝ) 1}
  have hcoordinate : Continuous (fun q : Plane => q 0) := by fun_prop
  have hV : IsOpen V := hU.inter
    ((isOpen_Ioo.preimage hcoordinate).preimage e.toAffineMap.continuous_of_finiteDimensional)
  have hiV : P.vertex i ∈ V := by
    refine ⟨hiU, ?_⟩
    change (e (P.vertex i)) 0 ∈ Ioo (-1 : ℝ) 1
    rw [hec]
    norm_num
  have hlocal (p : Plane) (hp : p ∈ V) (hpP : p ∈ P.carrier) :
      p ∈ segment ℝ (P.vertex i) a ∪ segment ℝ (P.vertex i) b := by
    have hpgraph : e p ∈ segment ℝ (Plane.mk (-1) 0) (Plane.mk 0 0) ∪
        segment ℝ (Plane.mk 0 0) (Plane.mk 1 d) := by
      simpa only [mul_one] using
        (mem_union_segments_iff_max (d := d) zero_lt_one zero_lt_one).mpr
          ⟨⟨hp.2.1.le, hp.2.2.le⟩, hgraph p hp.1 hpP⟩
    rcases hpgraph with hpgraph | hpgraph
    · have himage := mem_image_of_mem e.symm.toAffineMap hpgraph
      rw [image_segment] at himage
      change e.symm (e p) ∈ segment ℝ a (e.symm (Plane.mk 0 0)) at himage
      rw [heca, e.symm_apply_apply, segment_symm] at himage
      exact Or.inl himage
    · have himage := mem_image_of_mem e.symm.toAffineMap hpgraph
      rw [image_segment] at himage
      change e.symm (e p) ∈ segment ℝ (e.symm (Plane.mk 0 0)) b at himage
      rw [heca, e.symm_apply_apply] at himage
      exact Or.inr himage
  have hprev := sameRay_or_of_local_segment_subset hV hiV (fun p hp hseg =>
    hlocal p hp (P.edge_subset_carrier (i - 1) (by
      change p ∈ segment ℝ (P.vertex (i - 1)) (P.vertex (i - 1 + 1))
      rw [sub_add_cancel, segment_symm]
      exact hseg)))
  have hnext := sameRay_or_of_local_segment_subset hV hiV (fun p hp hseg =>
    hlocal p hp (P.edge_subset_carrier i hseg))
  exact ⟨hprev, hnext⟩

theorem PrePolygon.exists_affine_corner_chart_of_local_graph
    {m : ℕ} (P : PrePolygon m) (i : ZMod (m + 3)) (e : Plane ≃ᵃ[ℝ] Plane)
    {U : Set Plane} (hU : IsOpen U) (hiU : P.vertex i ∈ U) (hec : e (P.vertex i) = 0)
    (hgraph : ∀ p ∈ U, p ∈ P.carrier → (e p) 1 = max ((e p) 0) 0) :
    ∃ (f : Plane ≃ᵃ[ℝ] Plane) (r l : ℝ), 0 < r ∧ 0 < l ∧
      f (P.vertex i) = 0 ∧ f (P.vertex (i - 1)) = Plane.mk (-1) 0 ∧
      f (P.vertex (i + 1)) = Plane.mk r r ∧
      (∀ p, (f p) 1 - max ((f p) 0) 0 = l * ((e p) 1 - max ((e p) 0) 0)) ∧
      ∀ ε : ℝ, ε ≠ 0 → ∀ p,
        (f p) 1 - Real.smoothMax (l * ε) ((f p) 0) 0 =
          l * ((e p) 1 - Real.smoothMax ε ((e p) 0) 0) := by
  let a := e.symm (Plane.mk (-1) 0)
  let b := e.symm (Plane.mk 1 1)
  have hca : a - P.vertex i ≠ 0 := by
    intro h
    have he := congrArg (fun p => (e p) 0) (sub_eq_zero.mp h)
    change (e (e.symm (Plane.mk (-1) 0))) 0 = (e (P.vertex i)) 0 at he
    rw [e.apply_symm_apply, hec] at he
    norm_num [Plane.mk] at he
  have hcb : b - P.vertex i ≠ 0 := by
    intro h
    have he := congrArg (fun p => (e p) 0) (sub_eq_zero.mp h)
    change (e (e.symm (Plane.mk 1 1))) 0 = (e (P.vertex i)) 0 at he
    rw [e.apply_symm_apply, hec] at he
    norm_num [Plane.mk] at he
  obtain ⟨hprev, hnext⟩ := P.sameRay_incident_edges_of_local_graph i e hU hiU hec
    (d := 1) (fun p hp hpP => by simpa only [one_mul] using hgraph p hp hpP)
  have hmap (x : Plane) : e.linear (x - P.vertex i) = e x := by
    have h : e.linear (x - P.vertex i) = e x - e (P.vertex i) :=
      e.toAffineMap.linearMap_vsub x (P.vertex i)
    simpa only [hec, sub_zero] using h
  have hpositive (x : Plane) (hx : x ≠ P.vertex i)
      (hray : SameRay ℝ (x - P.vertex i) (a - P.vertex i) ∨
        SameRay ℝ (x - P.vertex i) (b - P.vertex i)) :
      0 < (e x) 1 - (e x) 0 / 2 := by
    rcases hray with h | h
    · obtain ⟨t, ht, he⟩ := h.exists_pos_right (sub_ne_zero.mpr hx) hca
      have heq : e x = t • Plane.mk (-1) 0 := by
        rw [← hmap, he, map_smul, hmap]
        change t • e (e.symm (Plane.mk (-1) 0)) = _
        rw [e.apply_symm_apply]
      rw [heq]
      change 0 < t * 0 - t * (-1) / 2
      linarith
    · obtain ⟨t, ht, he⟩ := h.exists_pos_right (sub_ne_zero.mpr hx) hcb
      have heq : e x = t • Plane.mk 1 1 := by
        rw [← hmap, he, map_smul, hmap]
        change t • e (e.symm (Plane.mk 1 1)) = _
        rw [e.apply_symm_apply]
      rw [heq]
      change 0 < t * 1 - t * 1 / 2
      linarith
  have hprevne : P.vertex (i - 1) ≠ P.vertex i := by
    intro h
    exact ClosedPolygon.succ_ne_self (i - 1)
      (by simpa only [sub_add_cancel] using (P.vertex_inj h).symm)
  have hnextne : P.vertex (i + 1) ≠ P.vertex i :=
    fun h => ClosedPolygon.succ_ne_self i (P.vertex_inj h)
  have hdet : Plane.det (P.vertex (i - 1) - P.vertex i)
      (P.vertex (i + 1) - P.vertex i) ≠ 0 := by
    intro h
    have hseg : e (P.vertex i) ∈ openSegment ℝ
        (e (P.vertex (i - 1))) (e (P.vertex (i + 1))) := by
      change e.toAffineMap (P.vertex i) ∈ openSegment ℝ
        (e.toAffineMap (P.vertex (i - 1))) (e.toAffineMap (P.vertex (i + 1)))
      rw [← image_openSegment ℝ e.toAffineMap]
      exact mem_image_of_mem e.toAffineMap (P.mem_openSegment_of_det_eq_zero i h)
    rw [hec] at hseg
    obtain ⟨s, t, hs, ht, _, he⟩ := hseg
    have hx := congrArg (fun q : Plane => q 0) he
    have hy := congrArg (fun q : Plane => q 1) he
    change s * (e (P.vertex (i - 1))) 0 + t * (e (P.vertex (i + 1))) 0 = 0 at hx
    change s * (e (P.vertex (i - 1))) 1 + t * (e (P.vertex (i + 1))) 1 = 0 at hy
    have hp := add_pos (mul_pos hs (hpositive _ hprevne hprev))
      (mul_pos ht (hpositive _ hnextne hnext))
    nlinarith only [hp, hx, hy]
  obtain ⟨_, α, β, hα, hβ, hmatch⟩ :=
    exists_pos_smul_pair_of_sameRay_or hdet hca hcb hprev hnext
  obtain ⟨f, r, l, hr, hl, hfc, hfa, hfb, _, hraw, hsmooth⟩ :=
    exists_reanchored_affine_corner_chart e zero_lt_one hα hβ
      (e.apply_symm_apply _) (e.apply_symm_apply _) hec hmatch
  exact ⟨f, r, l, hr, hl, hfc, hfa, hfb, hraw, hsmooth⟩

private theorem PrePolygon.det_eq_zero_of_centered_local_line
    {m : ℕ} (P : PrePolygon m) (i : ZMod (m + 3)) (e : Plane ≃ᵃ[ℝ] Plane)
    {U : Set Plane} (hU : IsOpen U) (hiU : P.vertex i ∈ U) (hec : e (P.vertex i) = 0)
    (hline : ∀ p ∈ U, p ∈ P.carrier → (e p) 1 = 0) :
    Plane.det (P.vertex (i - 1) - P.vertex i) (P.vertex (i + 1) - P.vertex i) = 0 := by
  by_contra hdet
  obtain ⟨hprev, hnext⟩ := P.sameRay_incident_edges_of_local_graph i e hU hiU hec
    (d := 0) (fun p hp hpP => by simpa only [zero_mul] using hline p hp hpP)
  have hne {q : Plane} (hq : q ≠ 0) : e.symm q - P.vertex i ≠ 0 := by
    intro h
    apply hq
    calc
      q = e (e.symm q) := (e.apply_symm_apply q).symm
      _ = e (P.vertex i) := congrArg e (sub_eq_zero.mp h)
      _ = 0 := hec
  have ha : e.symm (Plane.mk (-1) 0) - P.vertex i ≠ 0 := hne (by
    intro h
    have hx := congrArg (fun p : Plane => p 0) h
    norm_num [Plane.mk] at hx)
  have hb : e.symm (Plane.mk 1 0) - P.vertex i ≠ 0 := hne (by
    intro h
    have hx := congrArg (fun p : Plane => p 0) h
    norm_num [Plane.mk] at hx)
  have h := (exists_pos_smul_pair_of_sameRay_or hdet ha hb hprev hnext).1
  apply h
  have hmap (x : Plane) : e.linear (x - P.vertex i) = e x := by
    have hh : e.linear (x - P.vertex i) = e x - e (P.vertex i) :=
      e.toAffineMap.linearMap_vsub x (P.vertex i)
    simpa only [hec, sub_zero] using hh
  have hneg : e.symm (Plane.mk 1 0) - P.vertex i =
      (-1 : ℝ) • (e.symm (Plane.mk (-1) 0) - P.vertex i) := by
    apply e.linear.injective
    rw [map_smul, hmap, hmap, e.apply_symm_apply, e.apply_symm_apply]
    ext j
    fin_cases j <;> norm_num [Plane.mk]
  rw [hneg, Plane.det_smul_right, Plane.det_self, mul_zero]

theorem PrePolygon.exists_vertex_affine_corner_chart_of_local_graph
    {m : ℕ} (P : PrePolygon m) (e : Plane ≃ᵃ[ℝ] Plane) {U : Set Plane} {p : Plane}
    (hU : IsOpen U) (hpU : p ∈ U) (hep : e p = 0)
    (hgraph : ∀ x ∈ U, x ∈ P.carrier ↔ (e x) 1 = max ((e x) 0) 0) :
    ∃ (i : ZMod (m + 3)) (f : Plane ≃ᵃ[ℝ] Plane) (r l : ℝ),
      P.vertex i = p ∧ 0 < r ∧ 0 < l ∧
      f (P.vertex i) = 0 ∧ f (P.vertex (i - 1)) = Plane.mk (-1) 0 ∧
      f (P.vertex (i + 1)) = Plane.mk r r ∧
      (∀ x, (f x) 1 - max ((f x) 0) 0 = l * ((e x) 1 - max ((e x) 0) 0)) ∧
      ∀ ε : ℝ, ε ≠ 0 → ∀ x,
        (f x) 1 - Real.smoothMax (l * ε) ((f x) 0) 0 =
          l * ((e x) 1 - Real.smoothMax ε ((e x) 0) 0) := by
  have hcorner : IsCornerAt P.carrier p :=
    isCornerAt_of_local_affine_graph e one_ne_zero hU hpU hep
      (fun x hx he => (hgraph x hx).mpr (by simpa only [one_mul] using he))
  obtain ⟨i, hi⟩ := P.exists_vertex_eq_of_isCornerAt hcorner
  obtain ⟨f, r, l, hr, hl, hfc, hfa, hfb, hraw, hsmooth⟩ :=
    P.exists_affine_corner_chart_of_local_graph i e hU (hi.symm ▸ hpU)
      (by simpa only [hi] using hep) (fun x hx => (hgraph x hx).mp)
  exact ⟨i, f, r, l, hi, hr, hl, hfc, hfa, hfb, hraw, hsmooth⟩

theorem PrePolygon.exists_normalized_smooth_corner_of_local_graph
    {m : ℕ} (P : PrePolygon m) (e₀ : Plane ≃ᵃ[ℝ] Plane)
    {p : Plane} {U : Set Plane} {u v : ℝ}
    (hU : IsOpen U) (hpU : p ∈ U) (he₀p : e₀ p = 0)
    (hgraph : ∀ x ∈ U, x ∈ P.carrier ↔
      (e₀ x) 1 = u * (e₀ x) 0 + (v - u) * max ((e₀ x) 0) 0) :
    ∃ (e : Plane ≃ᵃ[ℝ] Plane) (d κ L : ℝ),
      (d = 0 ∨ d = 1) ∧ (d = 0 ↔ u = v) ∧ 0 < κ ∧ L ≠ 0 ∧ e p = 0 ∧
      (∀ x, (e₀ x) 1 - u * (e₀ x) 0 - (v - u) * max ((e₀ x) 0) 0 =
        L * ((e x) 1 - d * max ((e x) 0) 0)) ∧
      (∀ ε : ℝ, 0 < ε → ∀ x,
        (e₀ x) 1 - u * (e₀ x) 0 - (v - u) * Real.smoothMax ε ((e₀ x) 0) 0 =
          L * ((e x) 1 - d * Real.smoothMax (κ * ε) ((e x) 0) 0)) ∧
      (d = 1 → ∃ (i : ZMod (m + 3)) (r : ℝ),
        P.vertex i = p ∧ 0 < r ∧ e (P.vertex (i - 1)) = Plane.mk (-1) 0 ∧
          e (P.vertex (i + 1)) = Plane.mk r r) := by
  obtain ⟨e, r, d, l, hr, hd, hl, _, hep, _, hsmooth, hraw, hstraight⟩ :=
    exists_affine_smooth_corner_normalization e₀
      (a := e₀.symm (Plane.mk (-1) (-u))) (b := e₀.symm (Plane.mk 1 v))
      (u := u) (v := v) zero_lt_one zero_lt_one
      (by simpa only [mul_one] using e₀.apply_symm_apply (Plane.mk (-1) (-u)))
      he₀p (by simpa only [mul_one] using e₀.apply_symm_apply (Plane.mk 1 v))
  rcases hd with rfl | rfl
  · refine ⟨e, 0, 1, l, Or.inl rfl, hstraight, one_pos, hl, hep, hraw, ?_, ?_⟩
    · intro ε _ x
      simpa only [div_one, one_mul] using hsmooth ε x
    · norm_num
  · have hnormalized : ∀ x ∈ U, x ∈ P.carrier ↔ (e x) 1 = max ((e x) 0) 0 := by
      intro x hx
      have heq := hraw x
      simp only [one_mul] at heq
      constructor
      · intro hxc
        have hz : (e₀ x) 1 - u * (e₀ x) 0 - (v - u) * max ((e₀ x) 0) 0 = 0 := by
          linarith only [(hgraph x hx).mp hxc]
        exact sub_eq_zero.mp ((mul_eq_zero.mp (heq.symm.trans hz)).resolve_left hl)
      · intro hxe
        apply (hgraph x hx).mpr
        rw [hxe, sub_self, mul_zero] at heq
        linarith only [heq]
    obtain ⟨i, f, ρ, κ, hi, hρ, hκ, hfp, hfa, hfb, hrawf, hsmoothf⟩ :=
      P.exists_vertex_affine_corner_chart_of_local_graph e hU hpU hep hnormalized
    refine ⟨f, 1, κ, l / κ, Or.inr rfl, hstraight, hκ,
      div_ne_zero hl hκ.ne', ?_, ?_, ?_, ?_⟩
    · simpa only [hi] using hfp
    · intro x
      rw [one_mul, hrawf]
      have heq := hraw x
      simp only [one_mul] at heq
      rw [heq]
      field_simp
    · intro ε hε x
      rw [one_mul, hsmoothf ε hε.ne']
      have heq := hsmooth ε x
      simp only [one_mul, div_one] at heq
      rw [heq]
      field_simp
    · exact fun _ => ⟨i, ρ, hi, hρ, hfa, hfb⟩

theorem PrePolygon.det_eq_zero_of_local_line
    {m : ℕ} (P : PrePolygon m) (i : ZMod (m + 3)) (e : Plane ≃ᵃ[ℝ] Plane)
    {U : Set Plane} {c : ℝ} (hU : IsOpen U) (hiU : P.vertex i ∈ U)
    (hline : ∀ x ∈ U, x ∈ P.carrier → (e x) 1 = c) :
    Plane.det (P.vertex (i - 1) - P.vertex i) (P.vertex (i + 1) - P.vertex i) = 0 := by
  let f := e.trans (AffineEquiv.constVAdd ℝ Plane (-e (P.vertex i)))
  have hf (x : Plane) : f x = -e (P.vertex i) + e x := rfl
  have hfc : f (P.vertex i) = 0 := by rw [hf, neg_add_cancel]
  apply P.det_eq_zero_of_centered_local_line i f hU hiU hfc
  intro x hx hxC
  rw [hf]
  change -(e (P.vertex i)) 1 + (e x) 1 = 0
  rw [hline _ hiU (P.vertex_mem_carrier i), hline x hx hxC]
  exact neg_add_cancel c

theorem PrePolygon.vertex_eq_of_local_corner_graph
    {m : ℕ} (P : PrePolygon m) (e : Plane ≃ᵃ[ℝ] Plane) {U : Set Plane} {p : Plane}
    (hU : IsOpen U) (hep : e p = 0)
    (hgraph : ∀ x ∈ U, x ∈ P.carrier → (e x) 1 = max ((e x) 0) 0)
    (i : ZMod (m + 3)) (hiU : P.vertex i ∈ U)
    (hdet : Plane.det (P.vertex (i - 1) - P.vertex i)
      (P.vertex (i + 1) - P.vertex i) ≠ 0) : P.vertex i = p := by
  have hnot_line (f : Plane ≃ᵃ[ℝ] Plane) {V : Set Plane}
      (hV : IsOpen V) (hiV : P.vertex i ∈ V)
      (hline : ∀ x ∈ V, x ∈ P.carrier → (f x) 1 = 0) : False :=
    hdet (P.det_eq_zero_of_local_line i f hV hiV hline)
  have hcont : Continuous (fun x : Plane => (e x) 0) := by
    exact (by fun_prop : Continuous (fun x : Plane => x 0)).comp
      e.toAffineMap.continuous_of_finiteDimensional
  have hxzero : (e (P.vertex i)) 0 = 0 := by
    by_contra hn
    rcases lt_or_gt_of_ne hn with hneg | hpos
    · apply hnot_line e (hU.inter (isOpen_lt hcont continuous_const)) ⟨hiU, hneg⟩
      intro x hx hxC
      rw [hgraph x hx.1 hxC, max_eq_right hx.2.le]
    · let f := e.trans cornerSwap.toAffineEquiv
      apply hnot_line f (hU.inter (isOpen_lt continuous_const hcont)) ⟨hiU, hpos⟩
      intro x hx hxC
      change (e x) 1 - (e x) 0 = 0
      rw [hgraph x hx.1 hxC, max_eq_left hx.2.le, sub_self]
  apply e.injective
  rw [hep]
  ext j
  fin_cases j
  · exact hxzero
  · change (e (P.vertex i)) 1 = 0
    have hy := hgraph _ hiU (P.vertex_mem_carrier i)
    simpa only [hxzero, max_self] using hy

theorem PrePolygon.vertex_eq_of_local_piecewise_affine_graph
    {m : ℕ} (P : PrePolygon m) (e₀ : Plane ≃ᵃ[ℝ] Plane)
    {U : Set Plane} {p : Plane} {u v : ℝ}
    (hU : IsOpen U) (he₀p : e₀ p = 0)
    (hgraph : ∀ x ∈ U, x ∈ P.carrier →
      (e₀ x) 1 = u * (e₀ x) 0 + (v - u) * max ((e₀ x) 0) 0)
    (i : ZMod (m + 3)) (hiU : P.vertex i ∈ U)
    (hdet : Plane.det (P.vertex (i - 1) - P.vertex i)
      (P.vertex (i + 1) - P.vertex i) ≠ 0) : P.vertex i = p := by
  obtain ⟨e, r, d, l, _, hd, hl, _, hep, _, _, hraw, _⟩ :=
    exists_affine_smooth_corner_normalization e₀
      (a := e₀.symm (Plane.mk (-1) (-u))) (b := e₀.symm (Plane.mk 1 v))
      (u := u) (v := v) zero_lt_one zero_lt_one
      (by simpa only [mul_one] using e₀.apply_symm_apply (Plane.mk (-1) (-u)))
      he₀p (by simpa only [mul_one] using e₀.apply_symm_apply (Plane.mk 1 v))
  have hegraph (x : Plane) (hx : x ∈ U) (hxP : x ∈ P.carrier) :
      (e x) 1 = d * max ((e x) 0) 0 := by
    have hzero : (e₀ x) 1 - u * (e₀ x) 0 - (v - u) * max ((e₀ x) 0) 0 = 0 := by
      linarith only [hgraph x hx hxP]
    exact sub_eq_zero.mp ((mul_eq_zero.mp ((hraw x).symm.trans hzero)).resolve_left hl)
  rcases hd with rfl | rfl
  · exact False.elim (hdet (P.det_eq_zero_of_local_line i e hU hiU
      (fun x hx hxP => by simpa only [zero_mul] using hegraph x hx hxP)))
  · exact P.vertex_eq_of_local_corner_graph e hU hep
      (fun x hx hxP => by simpa only [one_mul] using hegraph x hx hxP) i hiU hdet

end Schoenflies
