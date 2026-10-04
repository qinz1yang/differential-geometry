import Mathlib.Topology.Order.OrderClosed
import Mathlib.Topology.Homeomorph.Lemmas
import Mathlib.Topology.Instances.AddCircle.Defs
import Mathlib.Analysis.Normed.Module.Basic
import Mathlib.Analysis.SpecialFunctions.Sqrt

/-!
# Gluing a calibrated tube to a half-infinite band product (S6 gluing kernel, disposition D7)

Package CM-S (finite soul), lane CMS-T, part C (S6 as a HOMEOMORPHISM). Pure topology.

Data on both sides: continuous "distance" functions `ρ : P → ℝ` (the model) and `η : M → ℝ`, a
gluing level `0 < a < ε`,
* a calibrated tube `T : {ρ < ε} ≃ₜ {η < ε}` with `η ∘ T = ρ`;
* half-band products `{ρ = a} × [a, ∞) ≃ₜ {ρ ≥ a}` and `{η = a} × [a, ∞) ≃ₜ {η ≥ a}` that are the
  identity on the level `a` and carry the second coordinate to the distance.

* `exists_continuous_tube_halfBand_glue`: one direction of the glued map (pasting on the closed
  pieces `{ρ ≤ a}` and `{ρ ≥ a}`, which meet in the level `a` where both pieces agree).
* `exists_homeomorph_tube_halfBand_glue`: `P ≃ₜ M`, calibrated (`η ∘ F = ρ`) and equal to the tube
  on `{ρ ≤ a}`.
* `exists_scaling_halfBand_product`: the model half-band product from a scaling action with
  `ρ (scale t p) = t ρ p` (`p ↦ (scale (a / ρ p) p, ρ p)`).
* `exists_smul_sqrt_halfBand_product` (a normed space with `ρ v = √(B v v)`, e.g. `(T_x M, g_x)`)
  and `exists_cylinder_halfBand_product` (`AddCircle 1 × ℝ` with `ρ = |h|`).
-/

set_option autoImplicit false

noncomputable section

open Set Topology

namespace DifferentialGeometry.Geometry.FiniteSoul

section Glue

variable {P M : Type*} [TopologicalSpace P] [TopologicalSpace M] {ρ : P → ℝ} {η : M → ℝ}
  {a ε : ℝ}

/-- **One direction of the gluing.** From a continuous tube map on `{ρ < ε}`, a continuous level
map `L` agreeing with it, the model half-band product `eP` and a continuous half-band map `eM`
fixing the level `a`, a continuous `F : P → M` that is the tube on `{ρ ≤ a}` and is
`eP (z, s) ↦ eM (L z, s)` on `{ρ ≥ a}`. -/
theorem exists_continuous_tube_halfBand_glue (hρ : Continuous ρ) (haε : a < ε)
    (T : {p // ρ p < ε} → M) (hT : Continuous T)
    (L : {p // ρ p = a} → {y // η y = a}) (hL : Continuous L)
    (hLT : ∀ z : {p // ρ p = a}, (L z : M) = T ⟨z, by rw [z.2]; exact haε⟩)
    (eP : ({p // ρ p = a} × Ici a) ≃ₜ {p // ρ p ∈ Ici a}) (heP : ∀ z, ρ (eP z) = z.2)
    (heP0 : ∀ z, (eP (z, ⟨a, self_mem_Ici⟩) : P) = z)
    (eM : ({y // η y = a} × Ici a) → {y // η y ∈ Ici a}) (heM : Continuous eM)
    (heM0 : ∀ z, (eM (z, ⟨a, self_mem_Ici⟩) : M) = z) :
    ∃ F : P → M, Continuous F ∧ (∀ p (hp : ρ p < ε), ρ p ≤ a → F p = T ⟨p, hp⟩) ∧
      ∀ z s, F (eP (z, s)) = eM (L z, s) := by
  classical
  set G₀ : {p // ρ p ∈ Ici a} → M := fun q => (eM (L (eP.symm q).1, (eP.symm q).2) : M) with hG₀
  have hG₀c : Continuous G₀ :=
    continuous_subtype_val.comp (heM.comp
      ((hL.comp (continuous_fst.comp eP.symm.continuous)).prodMk
        (continuous_snd.comp eP.symm.continuous)))
  set Tt : P → M := fun p => if h : ρ p < ε then T ⟨p, h⟩
    else G₀ ⟨p, show a ≤ ρ p from (haε.trans_le (not_lt.mp h)).le⟩ with hTt
  set Gt : P → M := fun p => if h : a ≤ ρ p then G₀ ⟨p, h⟩
    else T ⟨p, (not_le.mp h).trans haε⟩ with hGt
  have hTtc : ContinuousOn Tt {p | ρ p ≤ a} := by
    have h1 : ContinuousOn Tt {p | ρ p < ε} := by
      rw [continuousOn_iff_continuous_domRestrict]
      have he : ({p | ρ p < ε}.domRestrict Tt) = fun q => T ⟨q.1, q.2⟩ :=
        funext fun q => dite_eq_left q.2
      rw [he]
      exact hT.comp (continuous_subtype_val.subtype_mk _)
    exact h1.mono fun p hp => lt_of_le_of_lt hp haε
  have hGtc : ContinuousOn Gt {p | a ≤ ρ p} := by
    rw [continuousOn_iff_continuous_domRestrict]
    have he : ({p | a ≤ ρ p}.domRestrict Gt) = fun q => G₀ ⟨q.1, q.2⟩ :=
      funext fun q => dite_eq_left q.2
    rw [he]
    exact hG₀c.comp (continuous_subtype_val.subtype_mk _)
  -- on the level `a` the outer piece is the tube
  have hG₀lev : ∀ p (h : a ≤ ρ p) (hp : ρ p < ε), ρ p = a → G₀ ⟨p, h⟩ = T ⟨p, hp⟩ := by
    intro p h hp hpa
    set w := eP.symm ⟨p, h⟩ with hw
    have hew : eP w = ⟨p, h⟩ := eP.apply_symm_apply _
    have hw2 : w.2 = ⟨a, self_mem_Ici⟩ := by
      apply Subtype.ext
      have := heP w
      rw [hew] at this
      change ρ p = (w.2 : ℝ) at this
      rw [← this, hpa]
    have hw1 : ((w.1 : P)) = p := by
      have h2 : w = (w.1, ⟨a, self_mem_Ici⟩) := Prod.ext rfl hw2
      have h3 := heP0 w.1
      rw [← h2, hew] at h3
      exact h3.symm
    change (eM (L w.1, w.2) : M) = T ⟨p, hp⟩
    rw [hw2, heM0, hLT]
    congr 1
    exact Subtype.ext hw1
  set F : P → M := fun p => if ρ p ≤ a then Tt p else Gt p with hF
  have hFc : Continuous F := by
    refine continuous_if_le hρ continuous_const hTtc hGtc fun p hpa => ?_
    have hp : ρ p < ε := hpa ▸ haε
    have h : a ≤ ρ p := hpa.ge
    change Tt p = Gt p
    rw [hTt, hGt]
    simp only [dite_eq_left hp, dite_eq_left h]
    exact (hG₀lev p h hp hpa).symm
  have hFT : ∀ p (hp : ρ p < ε), ρ p ≤ a → F p = T ⟨p, hp⟩ := by
    intro p hp hpa
    change (if ρ p ≤ a then Tt p else Gt p) = _
    rw [ite_eq_left hpa, hTt]
    simp only [dite_eq_left hp]
  have hFG : ∀ p (h : a ≤ ρ p), F p = G₀ ⟨p, h⟩ := by
    intro p h
    change (if ρ p ≤ a then Tt p else Gt p) = _
    by_cases hpa : ρ p ≤ a
    · have hp : ρ p < ε := lt_of_le_of_lt hpa haε
      rw [ite_eq_left hpa, hTt]
      simp only [dite_eq_left hp]
      exact (hG₀lev p h hp (le_antisymm hpa h)).symm
    · rw [ite_eq_right hpa, hGt]
      simp only [dite_eq_left h]
  refine ⟨F, hFc, hFT, fun z s => ?_⟩
  have hmem : a ≤ ρ (eP (z, s)) := (eP (z, s)).2
  rw [hFG _ hmem]
  change (eM (L (eP.symm ⟨(eP (z, s) : P), hmem⟩).1, (eP.symm ⟨(eP (z, s) : P), hmem⟩).2) : M) = _
  have hq : (⟨(eP (z, s) : P), hmem⟩ : {p // ρ p ∈ Ici a}) = eP (z, s) := Subtype.coe_eta _ _
  rw [hq, eP.symm_apply_apply]

/-- **S6 gluing kernel.** A calibrated tube `{ρ < ε} ≃ₜ {η < ε}` and half-band products on both
sides (identity on the level `a < ε`, second coordinate = distance) glue to a calibrated
homeomorphism `P ≃ₜ M` that is the tube on `{ρ ≤ a}`. -/
theorem exists_homeomorph_tube_halfBand_glue (hρ : Continuous ρ) (hη : Continuous η)
    (haε : a < ε) (T : {p // ρ p < ε} ≃ₜ {y // η y < ε}) (hT : ∀ p, η (T p) = ρ p)
    (eP : ({p // ρ p = a} × Ici a) ≃ₜ {p // ρ p ∈ Ici a}) (heP : ∀ z, ρ (eP z) = z.2)
    (heP0 : ∀ z, (eP (z, ⟨a, self_mem_Ici⟩) : P) = z)
    (eM : ({y // η y = a} × Ici a) ≃ₜ {y // η y ∈ Ici a}) (heM : ∀ z, η (eM z) = z.2)
    (heM0 : ∀ z, (eM (z, ⟨a, self_mem_Ici⟩) : M) = z) :
    ∃ F : P ≃ₜ M, (∀ p, η (F p) = ρ p) ∧ ∀ p (hp : ρ p < ε), ρ p ≤ a → F p = T ⟨p, hp⟩ := by
  have hTs : ∀ y, ρ (T.symm y) = η y := fun y => by
    rw [← hT, T.apply_symm_apply]
  set L : {p // ρ p = a} → {y // η y = a} :=
    fun z => ⟨T ⟨z, by rw [z.2]; exact haε⟩, by rw [hT]; exact z.2⟩ with hLdef
  set L' : {y // η y = a} → {p // ρ p = a} :=
    fun y => ⟨T.symm ⟨y, by rw [y.2]; exact haε⟩, by rw [hTs]; exact y.2⟩ with hL'def
  have hLc : Continuous L :=
    ((continuous_subtype_val.comp T.continuous).comp
      (continuous_subtype_val.subtype_mk _)).subtype_mk _
  have hL'c : Continuous L' :=
    ((continuous_subtype_val.comp T.symm.continuous).comp
      (continuous_subtype_val.subtype_mk _)).subtype_mk _
  have hL'L : ∀ z, L' (L z) = z := fun z => by
    apply Subtype.ext
    change (T.symm ⟨(T ⟨z, _⟩ : M), _⟩ : P) = z
    rw [Subtype.coe_eta, T.symm_apply_apply]
  have hLL' : ∀ y, L (L' y) = y := fun y => by
    apply Subtype.ext
    change (T ⟨(T.symm ⟨y, _⟩ : P), _⟩ : M) = y
    rw [Subtype.coe_eta, T.apply_symm_apply]
  obtain ⟨F₁, hF₁c, hF₁T, hF₁e⟩ := exists_continuous_tube_halfBand_glue hρ haε
    (fun p => (T p : M)) (continuous_subtype_val.comp T.continuous) L hLc (fun _ => rfl)
    eP heP heP0 eM eM.continuous heM0
  obtain ⟨F₂, hF₂c, hF₂T, hF₂e⟩ := exists_continuous_tube_halfBand_glue hη haε
    (fun y => (T.symm y : P)) (continuous_subtype_val.comp T.symm.continuous) L' hL'c
    (fun _ => rfl) eM heM heM0 eP eP.continuous heP0
  -- points of the closed outer pieces are images of the half-band products
  have hPout : ∀ p, a ≤ ρ p → ∃ w, (eP w : P) = p := fun p h =>
    ⟨eP.symm ⟨p, h⟩, by rw [eP.apply_symm_apply]⟩
  have hMout : ∀ y, a ≤ η y → ∃ w, (eM w : M) = y := fun y h =>
    ⟨eM.symm ⟨y, h⟩, by rw [eM.apply_symm_apply]⟩
  have hηF₁ : ∀ p, η (F₁ p) = ρ p := by
    intro p
    by_cases hpa : ρ p ≤ a
    · have hp : ρ p < ε := lt_of_le_of_lt hpa haε
      rw [hF₁T p hp hpa]
      exact hT _
    · obtain ⟨w, rfl⟩ := hPout p (not_le.mp hpa).le
      rw [hF₁e, heM, heP]
  have hρF₂ : ∀ y, ρ (F₂ y) = η y := by
    intro y
    by_cases hya : η y ≤ a
    · have hy : η y < ε := lt_of_le_of_lt hya haε
      rw [hF₂T y hy hya]
      exact hTs _
    · obtain ⟨w, rfl⟩ := hMout y (not_le.mp hya).le
      rw [hF₂e, heP, heM]
  have hleft : ∀ p, F₂ (F₁ p) = p := by
    intro p
    by_cases hpa : ρ p ≤ a
    · have hp : ρ p < ε := lt_of_le_of_lt hpa haε
      have hy : η (F₁ p) < ε := by rw [hηF₁]; exact hp
      have hya : η (F₁ p) ≤ a := by rw [hηF₁]; exact hpa
      rw [hF₂T _ hy hya]
      have hq : (⟨F₁ p, hy⟩ : {y // η y < ε}) = T ⟨p, hp⟩ := by
        apply Subtype.ext
        exact hF₁T p hp hpa
      rw [hq, T.symm_apply_apply]
    · obtain ⟨w, rfl⟩ := hPout p (not_le.mp hpa).le
      rw [hF₁e, hF₂e, hL'L]
  have hright : ∀ y, F₁ (F₂ y) = y := by
    intro y
    by_cases hya : η y ≤ a
    · have hy : η y < ε := lt_of_le_of_lt hya haε
      have hp : ρ (F₂ y) < ε := by rw [hρF₂]; exact hy
      have hpa : ρ (F₂ y) ≤ a := by rw [hρF₂]; exact hya
      rw [hF₁T _ hp hpa]
      have hq : (⟨F₂ y, hp⟩ : {p // ρ p < ε}) = T.symm ⟨y, hy⟩ := by
        apply Subtype.ext
        exact hF₂T y hy hya
      rw [hq, T.apply_symm_apply]
    · obtain ⟨w, rfl⟩ := hMout y (not_le.mp hya).le
      rw [hF₂e, hF₁e, hLL']
  refine ⟨{ toFun := F₁, invFun := F₂, left_inv := hleft, right_inv := hright,
            continuous_toFun := hF₁c, continuous_invFun := hF₂c }, hηF₁, hF₁T⟩

end Glue

section Radial

/-- **Model half-band product from a scaling.** If `ρ (scale t p) = t ρ p` for `t ≥ 0`, then for
`a > 0`, `(z, s) ↦ scale (s / a) z` is a homeomorphism `{ρ = a} × [a, ∞) ≃ₜ {ρ ≥ a}`. -/
theorem exists_scaling_halfBand_product {P : Type*} [TopologicalSpace P] {ρ : P → ℝ}
    (hρ : Continuous ρ) (scale : ℝ → P → P) (hscale : Continuous (fun q : ℝ × P => scale q.1 q.2))
    (hscale1 : ∀ p, scale 1 p = p) (hscale_mul : ∀ s t p, scale s (scale t p) = scale (s * t) p)
    (hρscale : ∀ t p, 0 ≤ t → ρ (scale t p) = t * ρ p) {a : ℝ} (ha : 0 < a) :
    ∃ e : ({p // ρ p = a} × Ici a) ≃ₜ {p // ρ p ∈ Ici a},
      (∀ z, (e z : P) = scale ((z.2 : ℝ) / a) z.1) ∧ (∀ z, ρ (e z) = z.2) ∧
      ∀ z, (e (z, ⟨a, self_mem_Ici⟩) : P) = z := by
  have hfwd : ∀ z : {p // ρ p = a} × Ici a, ρ (scale ((z.2 : ℝ) / a) z.1) = z.2 := by
    rintro ⟨z, s, hs⟩
    change ρ (scale (s / a) z) = s
    rw [hρscale _ _ (div_nonneg (ha.le.trans hs) ha.le), z.2]
    field_simp
  have hpos : ∀ q : {p // ρ p ∈ Ici a}, 0 < ρ q := fun q => lt_of_lt_of_le ha q.2
  have hbwd : ∀ q : {p // ρ p ∈ Ici a}, ρ (scale (a / ρ q) q) = a := fun q => by
    rw [hρscale _ _ (div_nonneg ha.le (hpos q).le)]
    field_simp [(hpos q).ne']
  refine ⟨{ toFun := fun z => ⟨scale ((z.2 : ℝ) / a) z.1, show a ≤ _ by rw [hfwd]; exact z.2.2⟩
            invFun := fun q => (⟨scale (a / ρ q) q, hbwd q⟩, ⟨ρ q, q.2⟩)
            left_inv := ?_, right_inv := ?_, continuous_toFun := ?_, continuous_invFun := ?_ },
    fun _ => rfl, fun z => hfwd z, fun z => ?_⟩
  · rintro ⟨z, s, hs⟩
    have hs0 : 0 < s := lt_of_lt_of_le ha hs
    have hρs : ρ (scale (s / a) z) = s := hfwd (z, ⟨s, hs⟩)
    apply Prod.ext
    · apply Subtype.ext
      change scale (a / ρ (scale (s / a) z)) (scale (s / a) z) = z
      rw [hρs, hscale_mul, show a / s * (s / a) = 1 by field_simp, hscale1]
    · apply Subtype.ext
      exact hρs
  · intro q
    apply Subtype.ext
    change scale (ρ q / a) (scale (a / ρ q) q) = q
    rw [hscale_mul, show ρ q / a * (a / ρ q) = 1 by field_simp [(hpos q).ne'], hscale1]
  · apply Continuous.subtype_mk
    exact hscale.comp (((continuous_subtype_val.comp continuous_snd).div_const a).prodMk
      (continuous_subtype_val.comp continuous_fst))
  · apply Continuous.prodMk
    · apply Continuous.subtype_mk
      exact hscale.comp ((continuous_const.div (hρ.comp continuous_subtype_val)
        fun q => (hpos q).ne').prodMk continuous_subtype_val)
    · exact (hρ.comp continuous_subtype_val).subtype_mk _
  · change scale (a / a) (z : P) = z
    rw [div_self ha.ne', hscale1]

/-- **The model `(V, √(B v v))`**: for a continuous bilinear form `B` on a normed space, radial
scaling gives `{√(B v v) = a} × [a, ∞) ≃ₜ {√(B v v) ≥ a}` (`(z, s) ↦ (s / a) • z`). -/
theorem exists_smul_sqrt_halfBand_product {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    (B : V →L[ℝ] V →L[ℝ] ℝ) {a : ℝ} (ha : 0 < a) :
    ∃ e : ({v // Real.sqrt (B v v) = a} × Ici a) ≃ₜ {v // Real.sqrt (B v v) ∈ Ici a},
      (∀ z, (e z : V) = ((z.2 : ℝ) / a) • (z.1 : V)) ∧ (∀ z, Real.sqrt (B (e z) (e z)) = z.2) ∧
      ∀ z, (e (z, ⟨a, self_mem_Ici⟩) : V) = z := by
  have hρ : Continuous (fun v : V => Real.sqrt (B v v)) :=
    Real.continuous_sqrt.comp (B.continuous₂.comp (continuous_id.prodMk continuous_id))
  exact exists_scaling_halfBand_product hρ (fun t v => t • v) continuous_smul (fun v => one_smul ℝ v)
    (fun s t v => smul_smul s t v) (fun t v ht => by
      have hB : B (t • v) (t • v) = (t * t) * B v v := by
        simp only [map_smul, FunLike.coe_smul, Pi.smul_apply, smul_eq_mul]
        ring
      rw [hB, Real.sqrt_mul (mul_self_nonneg t), Real.sqrt_mul_self ht]) ha

/-- **The model `AddCircle 1 × ℝ` with `ρ = |h|`**: `(z, s) ↦ (z.1, (s / a) z.2)` is a
homeomorphism `{|h| = a} × [a, ∞) ≃ₜ {|h| ≥ a}`. -/
theorem exists_cylinder_halfBand_product {a : ℝ} (ha : 0 < a) :
    ∃ e : ({q : AddCircle (1 : ℝ) × ℝ // |q.2| = a} × Ici a) ≃ₜ
        {q : AddCircle (1 : ℝ) × ℝ // |q.2| ∈ Ici a},
      (∀ z, (e z : AddCircle (1 : ℝ) × ℝ) = ((z.1 : AddCircle (1 : ℝ) × ℝ).1,
        (z.2 : ℝ) / a * (z.1 : AddCircle (1 : ℝ) × ℝ).2)) ∧ (∀ z, |(e z : AddCircle (1 : ℝ) × ℝ).2| = z.2) ∧
      ∀ z, (e (z, ⟨a, self_mem_Ici⟩) : AddCircle (1 : ℝ) × ℝ) = z :=
  exists_scaling_halfBand_product (continuous_abs.comp continuous_snd)
    (fun t q => (q.1, t * q.2))
    ((continuous_fst.comp continuous_snd).prodMk (continuous_fst.mul (continuous_snd.comp continuous_snd)))
    (fun q => by simp) (fun s t q => by simp [mul_assoc])
    (fun t q ht => by simp [abs_mul, abs_of_nonneg ht]) ha

end Radial

end DifferentialGeometry.Geometry.FiniteSoul
