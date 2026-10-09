/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.Topology.PiecewiseLinear.LoopTheorem.CutAndPaste

open Set Topology

namespace DifferentialGeometry.Topology.PiecewiseLinear

universe u

theorem exists_homeomorph_loopCircle_of_isLoop
    {P : Set (EuclideanSpace ℝ (Fin 2))} {a' : frontier P} (pth : Path a' a')
    {f : ℝ → EuclideanSpace ℝ (Fin 2)} (hloop : Schoenflies.IsLoop f)
    (hline : ∀ (t : ℝ) (ht : t ∈ Set.Icc (0 : ℝ) 1),
      ((pth ⟨t, ht⟩ : frontier P) : EuclideanSpace ℝ (Fin 2)) = f t)
    (hrange : Set.range (fun t : unitInterval => pth t) = Set.univ) :
    ∃ ev : loopCircle ≃ₜ frontier P, ∀ θ, ev θ = pathToCircle pth θ := by
  have hFcontinuous : Continuous (pathToCircle pth) := (pathToCircle pth).continuous
  have hFinjective : Function.Injective (pathToCircle pth) := by
    intro θ η hθη
    let t := AddCircle.equivIco (1 : ℝ) 0 θ
    let s := AddCircle.equivIco (1 : ℝ) 0 η
    have htCircle : (((t : ℝ) : loopCircle)) = θ := by simp [t]
    have hsCircle : (((s : ℝ) : loopCircle)) = η := by simp [s]
    have htIco : (t : ℝ) ∈ Set.Ico (0 : ℝ) 1 := by simpa [t] using t.property
    have hsIco : (s : ℝ) ∈ Set.Ico (0 : ℝ) 1 := by simpa [s] using s.property
    have htI : (t : ℝ) ∈ Set.Icc (0 : ℝ) 1 := ⟨htIco.1, htIco.2.le⟩
    have hsI : (s : ℝ) ∈ Set.Icc (0 : ℝ) 1 := ⟨hsIco.1, hsIco.2.le⟩
    have hpEq : pth ⟨t, htI⟩ = pth ⟨s, hsI⟩ := by
      calc
        pth ⟨t, htI⟩ = pathToCircle pth ((t : ℝ) : loopCircle) :=
          (pathToCircle_coe pth ⟨t, htI⟩).symm
        _ = pathToCircle pth θ := congrArg (pathToCircle pth) htCircle
        _ = pathToCircle pth η := hθη
        _ = pathToCircle pth ((s : ℝ) : loopCircle) :=
          congrArg (pathToCircle pth) hsCircle.symm
        _ = pth ⟨s, hsI⟩ := pathToCircle_coe pth ⟨s, hsI⟩
    have hreal : f t = f s := by
      rw [← hline t htI, ← hline s hsI]
      exact congrArg Subtype.val hpEq
    have hts : (t : ℝ) = s := hloop.injOn htIco hsIco hreal
    calc
      θ = ((t : ℝ) : loopCircle) := htCircle.symm
      _ = ((s : ℝ) : loopCircle) := congrArg (fun x : ℝ => (x : loopCircle)) hts
      _ = η := hsCircle
  have hFsurjective : Function.Surjective (pathToCircle pth) := by
    intro x
    have hx : x ∈ Set.range fun t : unitInterval => pth t := by
      rw [hrange]; exact Set.mem_univ x
    obtain ⟨t, rfl⟩ := hx
    exact ⟨((t : unitInterval).val : loopCircle), pathToCircle_coe pth t⟩
  let e₀ : loopCircle ≃ frontier P :=
    Equiv.ofBijective (pathToCircle pth) ⟨hFinjective, hFsurjective⟩
  exact ⟨Continuous.homeoOfEquivCompactToT2 (f := e₀) hFcontinuous, fun _ => rfl⟩

open Classical in
theorem exists_injective_boundaryParam_four_paths
    {P A₁ A₂ A₃ A₄ : Set (EuclideanSpace ℝ (Fin 2))}
    {p q r s : EuclideanSpace ℝ (Fin 2)}
    (h₁ : Schoenflies.IsArcBetween A₁ p q) (h₂ : Schoenflies.IsArcBetween A₂ q r)
    (h₃ : Schoenflies.IsArcBetween A₃ r s) (h₄ : Schoenflies.IsArcBetween A₄ s p)
    (hm₃₄ : ∀ z ∈ A₃, z ∈ A₄ → z = s)
    (hm₂ : ∀ z ∈ A₂, z ∈ A₃ ∪ A₄ → z = r)
    (hm₁ : ∀ z ∈ A₁, z ∈ A₂ ∪ (A₃ ∪ A₄) → z = p ∨ z = q)
    (hfront : frontier P = A₁ ∪ (A₂ ∪ (A₃ ∪ A₄))) :
    ∃ (p' q' r' s' : frontier P) (σ : Path p' q') (τ : Path q' r') (υ : Path r' s')
        (φ : Path s' p') (ev : loopCircle ≃ₜ frontier P),
      ((p' : EuclideanSpace ℝ (Fin 2)) = p ∧ (q' : EuclideanSpace ℝ (Fin 2)) = q ∧
      (r' : EuclideanSpace ℝ (Fin 2)) = r ∧ (s' : EuclideanSpace ℝ (Fin 2)) = s ∧
      Set.range (fun t => ((σ t : frontier P) : EuclideanSpace ℝ (Fin 2))) = A₁ ∧
      Set.range (fun t => ((τ t : frontier P) : EuclideanSpace ℝ (Fin 2))) = A₂ ∧
      Set.range (fun t => ((υ t : frontier P) : EuclideanSpace ℝ (Fin 2))) = A₃ ∧
      Set.range (fun t => ((φ t : frontier P) : EuclideanSpace ℝ (Fin 2))) = A₄ ∧
      ∀ θ, ev θ = pathToCircle (σ.trans (τ.trans (υ.trans φ))) θ) ∧
      Function.Injective ⇑σ ∧ Function.Injective ⇑τ ∧
      Function.Injective ⇑υ ∧ Function.Injective ⇑φ := by
  have hpfront : p ∈ frontier P := by rw [hfront]; exact Or.inl h₁.left_mem
  have hqfront : q ∈ frontier P := by rw [hfront]; exact Or.inl h₁.right_mem
  have hrfront : r ∈ frontier P := by
    rw [hfront]; exact Or.inr (Or.inl h₂.right_mem)
  have hsfront : s ∈ frontier P := by
    rw [hfront]; exact Or.inr (Or.inr (Or.inl h₃.right_mem))
  obtain ⟨f₁, hf₁c, hf₁i, hf₁im, hf₁0, hf₁1⟩ := h₁
  obtain ⟨f₂, hf₂c, hf₂i, hf₂im, hf₂0, hf₂1⟩ := h₂
  obtain ⟨f₃, hf₃c, hf₃i, hf₃im, hf₃0, hf₃1⟩ := h₃
  obtain ⟨f₄, hf₄c, hf₄i, hf₄im, hf₄0, hf₄1⟩ := h₄
  set H : ℝ → EuclideanSpace ℝ (Fin 2) := Schoenflies.concatenate f₃ f₄ with hH
  set G : ℝ → EuclideanSpace ℝ (Fin 2) := Schoenflies.concatenate f₂ H with hG
  have hmid₃ : f₃ 1 = f₄ 0 := by rw [hf₃1, hf₄0]
  have hmeet₃ : ∀ z ∈ f₃ '' unitInterval, z ∈ f₄ '' unitInterval → z = f₃ 1 := by
    intro z hz hz'
    rw [hf₃im] at hz
    rw [hf₄im] at hz'
    rw [hf₃1]
    exact hm₃₄ z hz hz'
  have hHc : ContinuousOn H unitInterval :=
    Schoenflies.continuousOn_concatenate hf₃c hf₄c hmid₃
  have hHi : InjOn H unitInterval :=
    Schoenflies.injOn_concatenate hf₃i hf₄i hmid₃ hmeet₃
  have hHim : H '' unitInterval = A₃ ∪ A₄ := by
    rw [hH, Schoenflies.image_concatenate hmid₃, hf₃im, hf₄im]
  have hH0 : H 0 = r := by rw [hH, Schoenflies.concatenate_zero, hf₃0]
  have hH1 : H 1 = p := by rw [hH, Schoenflies.concatenate_one, hf₄1]
  have hmid₂ : f₂ 1 = H 0 := by rw [hf₂1, hH0]
  have hmeet₂ : ∀ z ∈ f₂ '' unitInterval, z ∈ H '' unitInterval → z = f₂ 1 := by
    intro z hz hz'
    rw [hf₂im] at hz
    rw [hHim] at hz'
    rw [hf₂1]
    exact hm₂ z hz hz'
  have hGc : ContinuousOn G unitInterval :=
    Schoenflies.continuousOn_concatenate hf₂c hHc hmid₂
  have hGi : InjOn G unitInterval :=
    Schoenflies.injOn_concatenate hf₂i hHi hmid₂ hmeet₂
  have hGim : G '' unitInterval = A₂ ∪ (A₃ ∪ A₄) := by
    rw [hG, Schoenflies.image_concatenate hmid₂, hf₂im, hHim]
  have hG0 : G 0 = q := by rw [hG, Schoenflies.concatenate_zero, hf₂0]
  have hG1 : G 1 = p := by rw [hG, Schoenflies.concatenate_one, hH1]
  have hmid₁ : f₁ 1 = G 0 := by rw [hf₁1, hG0]
  have hclose : G 1 = f₁ 0 := by rw [hG1, hf₁0]
  have hmeet₁ : ∀ z ∈ f₁ '' unitInterval, z ∈ G '' unitInterval →
      z = f₁ 0 ∨ z = f₁ 1 := by
    intro z hz hz'
    rw [hf₁im] at hz
    rw [hGim] at hz'
    rw [hf₁0, hf₁1]
    exact hm₁ z hz hz'
  have hloop : Schoenflies.IsLoop (Schoenflies.concatenate f₁ G) :=
    Schoenflies.IsLoop.concatenate hf₁c hf₁i hGc hGi hmid₁ hclose hmeet₁
  have hmem₁ (t : unitInterval) : f₁ t ∈ frontier P := by
    rw [hfront]; exact Or.inl (hf₁im ▸ ⟨t, t.property, rfl⟩)
  have hmem₂ (t : unitInterval) : f₂ t ∈ frontier P := by
    rw [hfront]; exact Or.inr (Or.inl (hf₂im ▸ ⟨t, t.property, rfl⟩))
  have hmem₃ (t : unitInterval) : f₃ t ∈ frontier P := by
    rw [hfront]; exact Or.inr (Or.inr (Or.inl (hf₃im ▸ ⟨t, t.property, rfl⟩)))
  have hmem₄ (t : unitInterval) : f₄ t ∈ frontier P := by
    rw [hfront]; exact Or.inr (Or.inr (Or.inr (hf₄im ▸ ⟨t, t.property, rfl⟩)))
  let p' : frontier P := ⟨p, hpfront⟩
  let q' : frontier P := ⟨q, hqfront⟩
  let r' : frontier P := ⟨r, hrfront⟩
  let s' : frontier P := ⟨s, hsfront⟩
  let σ : Path p' q' :=
    { toFun := fun t => ⟨f₁ t, hmem₁ t⟩
      continuous_toFun := hf₁c.domRestrict.subtype_mk _
      source' := Subtype.ext hf₁0
      target' := Subtype.ext hf₁1 }
  let τ : Path q' r' :=
    { toFun := fun t => ⟨f₂ t, hmem₂ t⟩
      continuous_toFun := hf₂c.domRestrict.subtype_mk _
      source' := Subtype.ext hf₂0
      target' := Subtype.ext hf₂1 }
  let υ : Path r' s' :=
    { toFun := fun t => ⟨f₃ t, hmem₃ t⟩
      continuous_toFun := hf₃c.domRestrict.subtype_mk _
      source' := Subtype.ext hf₃0
      target' := Subtype.ext hf₃1 }
  let φ : Path s' p' :=
    { toFun := fun t => ⟨f₄ t, hmem₄ t⟩
      continuous_toFun := hf₄c.domRestrict.subtype_mk _
      source' := Subtype.ext hf₄0
      target' := Subtype.ext hf₄1 }
  have hline₃ : ∀ (t : ℝ) (ht : t ∈ Set.Icc (0 : ℝ) 1),
      (((υ.trans φ) ⟨t, ht⟩ : frontier P) : EuclideanSpace ℝ (Fin 2)) = H t := by
    intro t ht
    rw [Path.trans_apply]
    split_ifs with hhalf
    · change t ≤ 1 / 2 at hhalf
      change f₃ (2 * t) = H t
      rw [hH, Schoenflies.concatenate, ite_eq_left hhalf]
    · change ¬t ≤ 1 / 2 at hhalf
      change f₄ (2 * t - 1) = H t
      rw [hH, Schoenflies.concatenate, ite_eq_right hhalf]
  have hline₂ : ∀ (t : ℝ) (ht : t ∈ Set.Icc (0 : ℝ) 1),
      (((τ.trans (υ.trans φ)) ⟨t, ht⟩ : frontier P) : EuclideanSpace ℝ (Fin 2)) = G t := by
    intro t ht
    rw [Path.trans_apply]
    split_ifs with hhalf
    · change t ≤ 1 / 2 at hhalf
      change f₂ (2 * t) = G t
      rw [hG, Schoenflies.concatenate, ite_eq_left hhalf]
    · change ¬t ≤ 1 / 2 at hhalf
      rw [hG, Schoenflies.concatenate, ite_eq_right hhalf]
      exact hline₃ (2 * t - 1) _
  have hline₁ : ∀ (t : ℝ) (ht : t ∈ Set.Icc (0 : ℝ) 1),
      (((σ.trans (τ.trans (υ.trans φ))) ⟨t, ht⟩ : frontier P) :
        EuclideanSpace ℝ (Fin 2)) = Schoenflies.concatenate f₁ G t := by
    intro t ht
    rw [Path.trans_apply]
    split_ifs with hhalf
    · change t ≤ 1 / 2 at hhalf
      change f₁ (2 * t) = Schoenflies.concatenate f₁ G t
      rw [Schoenflies.concatenate, ite_eq_left hhalf]
    · change ¬t ≤ 1 / 2 at hhalf
      rw [Schoenflies.concatenate, ite_eq_right hhalf]
      exact hline₂ (2 * t - 1) _
  have hrangeσ : Set.range (fun t : unitInterval => σ t) =
      {x : frontier P | (x : EuclideanSpace ℝ (Fin 2)) ∈ A₁} := by
    ext x
    constructor
    · rintro ⟨t, rfl⟩
      change f₁ t ∈ A₁
      rw [← hf₁im]
      exact ⟨t, t.property, rfl⟩
    · intro hx
      change (x : EuclideanSpace ℝ (Fin 2)) ∈ A₁ at hx
      rw [← hf₁im] at hx
      obtain ⟨t, ht, htx⟩ := hx
      exact ⟨⟨t, ht⟩, Subtype.ext htx⟩
  have hrangeτ : Set.range (fun t : unitInterval => τ t) =
      {x : frontier P | (x : EuclideanSpace ℝ (Fin 2)) ∈ A₂} := by
    ext x
    constructor
    · rintro ⟨t, rfl⟩
      change f₂ t ∈ A₂
      rw [← hf₂im]
      exact ⟨t, t.property, rfl⟩
    · intro hx
      change (x : EuclideanSpace ℝ (Fin 2)) ∈ A₂ at hx
      rw [← hf₂im] at hx
      obtain ⟨t, ht, htx⟩ := hx
      exact ⟨⟨t, ht⟩, Subtype.ext htx⟩
  have hrangeυ : Set.range (fun t : unitInterval => υ t) =
      {x : frontier P | (x : EuclideanSpace ℝ (Fin 2)) ∈ A₃} := by
    ext x
    constructor
    · rintro ⟨t, rfl⟩
      change f₃ t ∈ A₃
      rw [← hf₃im]
      exact ⟨t, t.property, rfl⟩
    · intro hx
      change (x : EuclideanSpace ℝ (Fin 2)) ∈ A₃ at hx
      rw [← hf₃im] at hx
      obtain ⟨t, ht, htx⟩ := hx
      exact ⟨⟨t, ht⟩, Subtype.ext htx⟩
  have hrangeφ : Set.range (fun t : unitInterval => φ t) =
      {x : frontier P | (x : EuclideanSpace ℝ (Fin 2)) ∈ A₄} := by
    ext x
    constructor
    · rintro ⟨t, rfl⟩
      change f₄ t ∈ A₄
      rw [← hf₄im]
      exact ⟨t, t.property, rfl⟩
    · intro hx
      change (x : EuclideanSpace ℝ (Fin 2)) ∈ A₄ at hx
      rw [← hf₄im] at hx
      obtain ⟨t, ht, htx⟩ := hx
      exact ⟨⟨t, ht⟩, Subtype.ext htx⟩
  have hrange : Set.range (fun t : unitInterval => (σ.trans (τ.trans (υ.trans φ))) t) =
      Set.univ := by
    rw [Path.trans_range, Path.trans_range, Path.trans_range, hrangeσ, hrangeτ, hrangeυ,
      hrangeφ]
    ext x
    simp only [Set.mem_union, Set.mem_ofPred_eq, Set.mem_univ, iff_true]
    have hx : (x : EuclideanSpace ℝ (Fin 2)) ∈ A₁ ∪ (A₂ ∪ (A₃ ∪ A₄)) :=
      hfront.subset x.property
    rcases hx with hx | hx | hx | hx
    · exact Or.inl hx
    · exact Or.inr (Or.inl hx)
    · exact Or.inr (Or.inr (Or.inl hx))
    · exact Or.inr (Or.inr (Or.inr hx))
  obtain ⟨ev, hev⟩ :=
    exists_homeomorph_loopCircle_of_isLoop (σ.trans (τ.trans (υ.trans φ))) hloop hline₁
      hrange
  refine ⟨p', q', r', s', σ, τ, υ, φ, ev,
    ⟨rfl, rfl, rfl, rfl, ?_, ?_, ?_, ?_, hev⟩, ?_, ?_, ?_, ?_⟩
  · ext x
    constructor
    · rintro ⟨t, rfl⟩
      change f₁ t ∈ A₁
      rw [← hf₁im]
      exact ⟨t, t.property, rfl⟩
    · intro hx
      rw [← hf₁im] at hx
      obtain ⟨t, ht, htx⟩ := hx
      exact ⟨⟨t, ht⟩, htx⟩
  · ext x
    constructor
    · rintro ⟨t, rfl⟩
      change f₂ t ∈ A₂
      rw [← hf₂im]
      exact ⟨t, t.property, rfl⟩
    · intro hx
      rw [← hf₂im] at hx
      obtain ⟨t, ht, htx⟩ := hx
      exact ⟨⟨t, ht⟩, htx⟩
  · ext x
    constructor
    · rintro ⟨t, rfl⟩
      change f₃ t ∈ A₃
      rw [← hf₃im]
      exact ⟨t, t.property, rfl⟩
    · intro hx
      rw [← hf₃im] at hx
      obtain ⟨t, ht, htx⟩ := hx
      exact ⟨⟨t, ht⟩, htx⟩
  · ext x
    constructor
    · rintro ⟨t, rfl⟩
      change f₄ t ∈ A₄
      rw [← hf₄im]
      exact ⟨t, t.property, rfl⟩
    · intro hx
      rw [← hf₄im] at hx
      obtain ⟨t, ht, htx⟩ := hx
      exact ⟨⟨t, ht⟩, htx⟩
  · intro z₁ z₂ hz
    exact Subtype.ext (hf₁i z₁.2 z₂.2 (congrArg Subtype.val hz))
  · intro z₁ z₂ hz
    exact Subtype.ext (hf₂i z₁.2 z₂.2 (congrArg Subtype.val hz))
  · intro z₁ z₂ hz
    exact Subtype.ext (hf₃i z₁.2 z₂.2 (congrArg Subtype.val hz))
  · intro z₁ z₂ hz
    exact Subtype.ext (hf₄i z₁.2 z₂.2 (congrArg Subtype.val hz))

open Classical in
theorem exists_boundaryParam_four_paths
    {P A₁ A₂ A₃ A₄ : Set (EuclideanSpace ℝ (Fin 2))}
    {p q r s : EuclideanSpace ℝ (Fin 2)}
    (h₁ : Schoenflies.IsArcBetween A₁ p q) (h₂ : Schoenflies.IsArcBetween A₂ q r)
    (h₃ : Schoenflies.IsArcBetween A₃ r s) (h₄ : Schoenflies.IsArcBetween A₄ s p)
    (hm₃₄ : ∀ z ∈ A₃, z ∈ A₄ → z = s)
    (hm₂ : ∀ z ∈ A₂, z ∈ A₃ ∪ A₄ → z = r)
    (hm₁ : ∀ z ∈ A₁, z ∈ A₂ ∪ (A₃ ∪ A₄) → z = p ∨ z = q)
    (hfront : frontier P = A₁ ∪ (A₂ ∪ (A₃ ∪ A₄))) :
    ∃ (p' q' r' s' : frontier P) (σ : Path p' q') (τ : Path q' r') (υ : Path r' s')
        (φ : Path s' p') (ev : loopCircle ≃ₜ frontier P),
      (p' : EuclideanSpace ℝ (Fin 2)) = p ∧ (q' : EuclideanSpace ℝ (Fin 2)) = q ∧
      (r' : EuclideanSpace ℝ (Fin 2)) = r ∧ (s' : EuclideanSpace ℝ (Fin 2)) = s ∧
      Set.range (fun t => ((σ t : frontier P) : EuclideanSpace ℝ (Fin 2))) = A₁ ∧
      Set.range (fun t => ((τ t : frontier P) : EuclideanSpace ℝ (Fin 2))) = A₂ ∧
      Set.range (fun t => ((υ t : frontier P) : EuclideanSpace ℝ (Fin 2))) = A₃ ∧
      Set.range (fun t => ((φ t : frontier P) : EuclideanSpace ℝ (Fin 2))) = A₄ ∧
      ∀ θ, ev θ = pathToCircle (σ.trans (τ.trans (υ.trans φ))) θ := by
  obtain ⟨p', q', r', s', σ, τ, υ, φ, ev, hbody, -⟩ :=
    exists_injective_boundaryParam_four_paths h₁ h₂ h₃ h₄ hm₃₄ hm₂ hm₁ hfront
  exact ⟨p', q', r', s', σ, τ, υ, φ, ev, hbody⟩

open Classical in
theorem exists_four_arcs_of_two_disjoint_subarcs
    {J S₁ S₃ : Set (EuclideanSpace ℝ (Fin 2))} {p q r s : EuclideanSpace ℝ (Fin 2)}
    (hJ : IsPLSphere 1 J)
    (h₁ : Schoenflies.IsArcBetween S₁ p q) (h₃ : Schoenflies.IsArcBetween S₃ r s)
    (h₁J : S₁ ⊆ J) (h₃J : S₃ ⊆ J) (hdisj : Disjoint S₁ S₃) :
    ∃ (u v : EuclideanSpace ℝ (Fin 2)) (T₂ T₄ : Set (EuclideanSpace ℝ (Fin 2))),
      ((u = r ∧ v = s) ∨ (u = s ∧ v = r)) ∧
      Schoenflies.IsArcBetween T₂ q u ∧ Schoenflies.IsArcBetween S₃ u v ∧
      Schoenflies.IsArcBetween T₄ v p ∧
      (∀ z ∈ S₃, z ∈ T₄ → z = v) ∧
      (∀ z ∈ T₂, z ∈ S₃ ∪ T₄ → z = u) ∧
      (∀ z ∈ S₁, z ∈ T₂ ∪ (S₃ ∪ T₄) → z = p ∨ z = q) ∧
      J = S₁ ∪ (T₂ ∪ (S₃ ∪ T₄)) := by
  obtain ⟨G, hcut, -, -⟩ := exists_isCutPair_of_isArcBetween_subset_isPLSphere hJ h₁ h₁J
  have hG : Schoenflies.IsArcBetween G p q := hcut.snd
  have hS₃G : S₃ ⊆ G := by
    intro z hz
    have hzJ : z ∈ J := h₃J hz
    rw [← hcut.union_eq] at hzJ
    rcases hzJ with hz₁ | hzG
    · exact absurd hz (Set.disjoint_left.mp hdisj hz₁)
    · exact hzG
  have hrG : r ∈ G := hS₃G h₃.left_mem
  have hsG : s ∈ G := hS₃G h₃.right_mem
  have hrs : r ≠ s := h₃.ne
  have hrp : r ≠ p := fun h =>
    Set.disjoint_left.mp hdisj h₁.left_mem (h ▸ h₃.left_mem)
  have hrq : r ≠ q := fun h =>
    Set.disjoint_left.mp hdisj h₁.right_mem (h ▸ h₃.left_mem)
  have hsp : s ≠ p := fun h =>
    Set.disjoint_left.mp hdisj h₁.left_mem (h ▸ h₃.right_mem)
  have hsq : s ≠ q := fun h =>
    Set.disjoint_left.mp hdisj h₁.right_mem (h ▸ h₃.right_mem)
  obtain ⟨G₁, G₂, hG₁, hG₂, hGunion, hGinter⟩ := hG.exists_split hrG hrp hrq
  have hsplit : s ∈ G₁ ∪ G₂ := by rw [hGunion]; exact hsG
  have hG₁G : G₁ ⊆ G := by rw [← hGunion]; exact Set.subset_union_left
  have hG₂G : G₂ ⊆ G := by rw [← hGunion]; exact Set.subset_union_right
  have hmeetS₁ : ∀ z ∈ S₁, z ∈ G → z = p ∨ z = q := by
    intro z hz₁ hzG
    have : z ∈ ({p, q} : Set (EuclideanSpace ℝ (Fin 2))) := hcut.inter_eq ▸ ⟨hz₁, hzG⟩
    simpa using this
  rcases hsplit with hsG₁ | hsG₂
  · obtain ⟨G₅, G₆, hG₅, hG₆, hG₁union, hG₁inter⟩ :=
      hG₁.exists_split hsG₁ hsp hrs.symm
    have hG₆G : G₆ ⊆ G := fun z hz => hG₁G (by rw [← hG₁union]; exact Or.inr hz)
    have hG₅G : G₅ ⊆ G := fun z hz => hG₁G (by rw [← hG₁union]; exact Or.inl hz)
    have hS₃eq : S₃ = G₆ := h₃.reverse.eq_of_subset_arc hG₆ hG hS₃G hG₆G
    have hGeq : G₂ ∪ (G₆ ∪ G₅) = G := by
      rw [← hGunion, ← hG₁union]
      ext z
      simp only [Set.mem_union]
      tauto
    refine ⟨r, s, G₂, G₅, Or.inl ⟨rfl, rfl⟩, hG₂.reverse, h₃, hG₅.reverse, ?_, ?_, ?_, ?_⟩
    · intro z hz hz₅
      rw [hS₃eq] at hz
      have : z ∈ ({s} : Set (EuclideanSpace ℝ (Fin 2))) := hG₁inter ▸ ⟨hz₅, hz⟩
      simpa using this
    · intro z hz₂ hz
      have hz₁ : z ∈ G₁ := by
        rw [← hG₁union]
        rcases hz with hz | hz
        · exact Or.inr (hS₃eq ▸ hz)
        · exact Or.inl hz
      have : z ∈ ({r} : Set (EuclideanSpace ℝ (Fin 2))) := hGinter ▸ ⟨hz₁, hz₂⟩
      simpa using this
    · intro z hz₁ hz
      refine hmeetS₁ z hz₁ ?_
      rw [← hGeq]
      rcases hz with hz | hz | hz
      · exact Or.inl hz
      · exact Or.inr (Or.inl (hS₃eq ▸ hz))
      · exact Or.inr (Or.inr hz)
    · rw [hS₃eq, hGeq, hcut.union_eq]
  · obtain ⟨G₃, G₄, hG₃, hG₄, hG₂union, hG₂inter⟩ :=
      hG₂.exists_split hsG₂ hrs.symm hsq
    have hG₃G : G₃ ⊆ G := fun z hz => hG₂G (by rw [← hG₂union]; exact Or.inl hz)
    have hG₄G : G₄ ⊆ G := fun z hz => hG₂G (by rw [← hG₂union]; exact Or.inr hz)
    have hS₃eq : S₃ = G₃ := h₃.eq_of_subset_arc hG₃ hG hS₃G hG₃G
    have hGeq : G₄ ∪ (G₃ ∪ G₁) = G := by
      rw [← hGunion, ← hG₂union]
      ext z
      simp only [Set.mem_union]
      tauto
    refine ⟨s, r, G₄, G₁, Or.inr ⟨rfl, rfl⟩, hG₄.reverse, h₃.reverse, hG₁.reverse,
      ?_, ?_, ?_, ?_⟩
    · intro z hz hz₁
      rw [hS₃eq] at hz
      have hz₂ : z ∈ G₂ := by rw [← hG₂union]; exact Or.inl hz
      have : z ∈ ({r} : Set (EuclideanSpace ℝ (Fin 2))) := hGinter ▸ ⟨hz₁, hz₂⟩
      simpa using this
    · intro z hz₄ hz
      rcases hz with hz | hz
      · rw [hS₃eq] at hz
        have : z ∈ ({s} : Set (EuclideanSpace ℝ (Fin 2))) := hG₂inter ▸ ⟨hz, hz₄⟩
        simpa using this
      · have hz₂ : z ∈ G₂ := by rw [← hG₂union]; exact Or.inr hz₄
        have hzr : z = r := by
          have : z ∈ ({r} : Set (EuclideanSpace ℝ (Fin 2))) := hGinter ▸ ⟨hz, hz₂⟩
          simpa using this
        have : r ∈ ({s} : Set (EuclideanSpace ℝ (Fin 2))) :=
          hG₂inter ▸ ⟨hG₃.left_mem, hzr ▸ hz₄⟩
        exact absurd (by simpa using this) hrs
    · intro z hz₁ hz
      refine hmeetS₁ z hz₁ ?_
      rw [← hGeq]
      rcases hz with hz | hz | hz
      · exact Or.inl hz
      · exact Or.inr (Or.inl (hS₃eq ▸ hz))
      · exact Or.inr (Or.inr hz)
    · rw [hS₃eq, hGeq, hcut.union_eq]

theorem trans_apply_eq_map {Q R : Type*} [TopologicalSpace Q] [TopologicalSpace R]
    {f : Q → R} {u v w : Q} {u' v' w' : R} {α : Path u v} {β : Path v w}
    {α' : Path u' v'} {β' : Path v' w'}
    (hα : ∀ t, α' t = f (α t)) (hβ : ∀ t, β' t = f (β t)) :
    ∀ t, (α'.trans β') t = f ((α.trans β) t) := by
  intro t
  rw [Path.trans_apply, Path.trans_apply]
  split_ifs with h
  · exact hα _
  · exact hβ _

theorem pathToCircle_eq_of_forall {Q R : Type*} [TopologicalSpace Q] [TopologicalSpace R]
    {u : Q} {u' : R} {f : Q → R} (pth : Path u u) (pth' : Path u' u')
    (h : ∀ t, pth' t = f (pth t)) (θ : loopCircle) :
    pathToCircle pth' θ = f (pathToCircle pth θ) := by
  obtain ⟨t, rfl⟩ := unitInterval_to_loopCircle_surjective θ
  rw [pathToCircle_coe, pathToCircle_coe]
  exact h t

theorem not_loopClassMeets_or_not_loopClassMeets_of_four_boundary_arcs_reversing
    {Q : Type*} [TopologicalSpace Q] {X : Type u} [TopologicalSpace X]
    [PathConnectedSpace X] {p' q' r' s' : Q} (σ₀ : Path p' q') (τ₀ : Path q' r')
    (υ₀ : Path r' s') (φ₀ : Path s' p') (ev : loopCircle → Q)
    (hev : ∀ θ, ev θ = pathToCircle (σ₀.trans (τ₀.trans (υ₀.trans φ₀))) θ)
    {f : Q → X} {x a b : X} (qq : Path x a) (cc : Path a b)
    {σ υ : Path a b} {τ φ : Path b a}
    (hσ : ∀ t, σ t = f (σ₀ t)) (hτ : ∀ t, τ t = f (τ₀ t))
    (hυ : ∀ t, υ t = f (υ₀ t)) (hφ : ∀ t, φ t = f (φ₀ t))
    (γ : freeLoop X) (hγ : ∀ θ, γ θ = f (ev θ))
    (N : Subgroup (FundamentalGroup X x)) [N.Normal]
    (hL : ¬loopClassMeets γ x N) :
    ¬loopClassMeets (pathToCircle (σ.trans υ.symm)) x N ∨
      ¬loopClassMeets (pathToCircle (σ.trans (φ.trans (υ.trans τ)))) x N := by
  have hmother : ∀ t, (σ.trans (τ.trans (υ.trans φ))) t =
      f ((σ₀.trans (τ₀.trans (υ₀.trans φ₀))) t) :=
    trans_apply_eq_map hσ (trans_apply_eq_map hτ (trans_apply_eq_map hυ hφ))
  have hγeq : γ = pathToCircle (σ.trans (τ.trans (υ.trans φ))) := by
    ext θ
    rw [hγ θ, hev θ]
    exact (pathToCircle_eq_of_forall _ _ hmother θ).symm
  rw [hγeq] at hL
  exact not_loopClassMeets_or_not_loopClassMeets_of_endpoint_reversing_reconnection
    qq cc σ υ τ φ N hL

theorem not_loopClassMeets_or_not_loopClassMeets_of_four_boundary_arcs_preserving
    {Q : Type*} [TopologicalSpace Q] {X : Type u} [TopologicalSpace X]
    [PathConnectedSpace X] {p' q' r' s' : Q} (σ₀ : Path p' q') (τ₀ : Path q' r')
    (υ₀ : Path r' s') (φ₀ : Path s' p') (ev : loopCircle → Q)
    (hev : ∀ θ, ev θ = pathToCircle (σ₀.trans (τ₀.trans (υ₀.trans φ₀))) θ)
    {f : Q → X} {x a b : X} (qq : Path x a) (cc : Path a b)
    {σ : Path a b} {τ : Path b b} {υ : Path b a} {φ : Path a a}
    (hσ : ∀ t, σ t = f (σ₀ t)) (hτ : ∀ t, τ t = f (τ₀ t))
    (hυ : ∀ t, υ t = f (υ₀ t)) (hφ : ∀ t, φ t = f (φ₀ t))
    (γ : freeLoop X) (hγ : ∀ θ, γ θ = f (ev θ))
    (N : Subgroup (FundamentalGroup X x)) [N.Normal]
    (hL : ¬loopClassMeets γ x N) :
    ¬loopClassMeets (pathToCircle (σ.trans υ)) x N ∨
      ¬loopClassMeets (pathToCircle (σ.trans (τ.symm.trans (υ.trans φ.symm)))) x N := by
  have hmother : ∀ t, (σ.trans (τ.trans (υ.trans φ))) t =
      f ((σ₀.trans (τ₀.trans (υ₀.trans φ₀))) t) :=
    trans_apply_eq_map hσ (trans_apply_eq_map hτ (trans_apply_eq_map hυ hφ))
  have hγeq : γ = pathToCircle (σ.trans (τ.trans (υ.trans φ))) := by
    ext θ
    rw [hγ θ, hev θ]
    exact (pathToCircle_eq_of_forall _ _ hmother θ).symm
  rw [hγeq] at hL
  exact not_loopClassMeets_or_not_loopClassMeets_of_endpoint_preserving_reconnection
    qq cc σ τ υ φ N hL

namespace NormalSingularCellData

open Classical in
theorem exists_boundary_four_arc_word_of_cut
    {M : Type u} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
    {D : SingularTwoCell M} {BdM B : Set M}
    (hD : NormalSingularCellData D BdM B) {c : hD.singularSet.Branch}
    {A C : Set (EuclideanSpace ℝ (Fin 2))} {p q r s : EuclideanSpace ℝ (Fin 2)}
    {g : EuclideanSpace ℝ (Fin 2) → EuclideanSpace ℝ (Fin 2)}
    {D₁ D₂ D₃ : SingularTwoCell M}
    (hcut : hD.IsBoundaryBranchCut c A C p q r s g D₁ D₂ D₃) :
    ∃ (A₂ A₄ : Set (EuclideanSpace ℝ (Fin 2))) (u v : EuclideanSpace ℝ (Fin 2))
        (p' q' u' v' : frontier D.domain)
        (σ : Path p' q') (τ : Path q' u') (υ : Path u' v') (φ : Path v' p')
        (ev : loopCircle ≃ₜ frontier D.domain),
      (IsPLBall 1 A ∧ IsPLBall 1 C ∧ Disjoint A C ∧
      hD.branchPreimage c = A ∪ C ∧
      Schoenflies.IsArcBetween A p q ∧ Schoenflies.IsArcBetween C u v ∧
      (p' : EuclideanSpace ℝ (Fin 2)) = p ∧ (q' : EuclideanSpace ℝ (Fin 2)) = q ∧
      (u' : EuclideanSpace ℝ (Fin 2)) = u ∧ (v' : EuclideanSpace ℝ (Fin 2)) = v ∧
      Set.range (fun t => ((σ t : frontier D.domain) : EuclideanSpace ℝ (Fin 2))) =
        D₁.domain ∩ frontier D.domain ∧
      Set.range (fun t => ((τ t : frontier D.domain) : EuclideanSpace ℝ (Fin 2))) = A₂ ∧
      Set.range (fun t => ((υ t : frontier D.domain) : EuclideanSpace ℝ (Fin 2))) =
        D₃.domain ∩ frontier D.domain ∧
      Set.range (fun t => ((φ t : frontier D.domain) : EuclideanSpace ℝ (Fin 2))) = A₄ ∧
      frontier D.domain = (D₁.domain ∩ frontier D.domain) ∪
        (A₂ ∪ ((D₃.domain ∩ frontier D.domain) ∪ A₄)) ∧
      (∀ θ, ev θ = pathToCircle (σ.trans (τ.trans (υ.trans φ))) θ) ∧
      ((D u = D p ∧ D v = D q) ∨ (D u = D q ∧ D v = D p))) ∧
      Function.Injective ⇑σ ∧ Function.Injective ⇑τ ∧
      Function.Injective ⇑υ ∧ Function.Injective ⇑φ ∧
      ((u = r ∧ v = s) ∨ (u = s ∧ v = r)) ∧
      (∀ z ∈ D₃.domain ∩ frontier D.domain, z ∈ A₄ → z = v) ∧
      (∀ z ∈ A₂, z ∈ (D₃.domain ∩ frontier D.domain) ∪ A₄ → z = u) ∧
      (∀ z ∈ D₁.domain ∩ frontier D.domain,
        z ∈ A₂ ∪ ((D₃.domain ∩ frontier D.domain) ∪ A₄) → z = p ∨ z = q) ∧
      (D₁.domain ∪ D₂.domain) ∩ frontier D.domain =
        A₂ ∪ ((D₁.domain ∩ frontier D.domain) ∪ A₄) := by
  obtain ⟨hAb, hCb, hAC, hcover, -, -, hg, hcompat, hdomains, -, hinter₂₃, -, -, -, -,
    hdisjoint₁₃, -, -, -, -, -, hcut₁, hcut₃⟩ := hcut
  have horientation :=
    IsPLHomeomorphOn.maps_arc_endpoints hAb hCb hcut₁.fst hcut₃.fst hg
  have hdisjS : Disjoint (D₁.domain ∩ frontier D.domain)
      (D₃.domain ∩ frontier D.domain) :=
    hdisjoint₁₃.mono inter_subset_left inter_subset_left
  obtain ⟨u, v, T₂, T₄, huv, hT₂, hS₃arc, hT₄, hm₃₄, hm₂, hm₁, hJ⟩ :=
    exists_four_arcs_of_two_disjoint_subarcs D.isPLBall_domain.isPLSphere_frontier
      hcut₁.snd hcut₃.snd inter_subset_right inter_subset_right hdisjS
  obtain ⟨p', q', u', v', σ, τ, υ, φ, ev,
    ⟨hp', hq', hu', hv', hr₁, hr₂, hr₃, hr₄, hev⟩, hσinj, hτinj, hυinj, hφinj⟩ :=
    exists_injective_boundaryParam_four_paths hcut₁.snd hT₂ hS₃arc hT₄ hm₃₄ hm₂ hm₁ hJ
  have hDp : D p = D (g p) := hcompat hcut₁.fst.left_mem
  have hDq : D q = D (g q) := hcompat hcut₁.fst.right_mem
  have hCbuv : Schoenflies.IsArcBetween C u v := by
    rcases huv with ⟨hu, hv⟩ | ⟨hu, hv⟩
    · rw [hu, hv]; exact hcut₃.fst
    · rw [hu, hv]; exact hcut₃.fst.reverse
  have hpair : (D u = D p ∧ D v = D q) ∨ (D u = D q ∧ D v = D p) := by
    rcases huv with ⟨hu, hv⟩ | ⟨hu, hv⟩ <;>
      rcases horientation with ⟨hgp, hgq⟩ | ⟨hgp, hgq⟩
    · exact Or.inl ⟨by rw [hu, ← hgp]; exact hDp.symm,
        by rw [hv, ← hgq]; exact hDq.symm⟩
    · exact Or.inr ⟨by rw [hu, ← hgq]; exact hDq.symm,
        by rw [hv, ← hgp]; exact hDp.symm⟩
    · exact Or.inr ⟨by rw [hu, ← hgq]; exact hDq.symm,
        by rw [hv, ← hgp]; exact hDp.symm⟩
    · exact Or.inl ⟨by rw [hu, ← hgp]; exact hDp.symm,
        by rw [hv, ← hgq]; exact hDq.symm⟩
  have hCuv : u ∈ C ∧ v ∈ C := by
    rcases huv with ⟨hu, hv⟩ | ⟨hu, hv⟩
    · exact ⟨by rw [hu]; exact hcut₃.fst.left_mem,
        by rw [hv]; exact hcut₃.fst.right_mem⟩
    · exact ⟨by rw [hu]; exact hcut₃.fst.right_mem,
        by rw [hv]; exact hcut₃.fst.left_mem⟩
  have hCD₂ : C ⊆ D₂.domain := by
    rw [← hinter₂₃]
    exact inter_subset_left
  have huT₂ : u ∈ T₂ := hT₂.right_mem
  have hvT₄ : v ∈ T₄ := hT₄.left_mem
  have hrs : ∀ z ∈ ({r, s} : Set (EuclideanSpace ℝ (Fin 2))), z ∈ T₂ ∪ T₄ := by
    rcases huv with ⟨hu, hv⟩ | ⟨hu, hv⟩
    · rintro z (rfl | rfl)
      · exact Or.inl (hu ▸ huT₂)
      · exact Or.inr (hv ▸ hvT₄)
    · rintro z (rfl | rfl)
      · exact Or.inr (hv ▸ hvT₄)
      · exact Or.inl (hu ▸ huT₂)
  have hkey : (D₁.domain ∪ D₂.domain) ∩ frontier D.domain =
      T₂ ∪ ((D₁.domain ∩ frontier D.domain) ∪ T₄) := by
    apply Subset.antisymm
    · rintro z ⟨hz12, hzf⟩
      have hzJ : z ∈ (D₁.domain ∩ frontier D.domain) ∪
          (T₂ ∪ ((D₃.domain ∩ frontier D.domain) ∪ T₄)) := hJ ▸ hzf
      rcases hzJ with hz₁ | hz₂ | hz₃ | hz₄
      · exact Or.inr (Or.inl hz₁)
      · exact Or.inl hz₂
      · rcases hz12 with hzD₁ | hzD₂
        · exact absurd hz₃.1 (Set.disjoint_left.mp hdisjoint₁₃ hzD₁)
        · have hzC : z ∈ C := hinter₂₃.subset ⟨hzD₂, hz₃.1⟩
          have hzrs : z ∈ ({r, s} : Set (EuclideanSpace ℝ (Fin 2))) :=
            hcut₃.inter_eq.subset ⟨hzC, hz₃⟩
          rcases hrs z hzrs with hzT₂ | hzT₄
          · exact Or.inl hzT₂
          · exact Or.inr (Or.inr hzT₄)
      · exact Or.inr (Or.inr hz₄)
    · rintro z (hzT₂ | hz₁ | hzT₄)
      · have hzf : z ∈ frontier D.domain := by
          rw [hJ]
          exact Or.inr (Or.inl hzT₂)
        refine ⟨?_, hzf⟩
        rcases hdomains.symm.subset (D.frontier_subset_domain hzf) with
          (hzD₁ | hzD₂) | hzD₃
        · exact Or.inl hzD₁
        · exact Or.inr hzD₂
        · have hzu : z = u := hm₂ z hzT₂ (Or.inl ⟨hzD₃, hzf⟩)
          exact Or.inr (hCD₂ (by rw [hzu]; exact hCuv.1))
      · exact ⟨Or.inl hz₁.1, hz₁.2⟩
      · have hzf : z ∈ frontier D.domain := by
          rw [hJ]
          exact Or.inr (Or.inr (Or.inr hzT₄))
        refine ⟨?_, hzf⟩
        rcases hdomains.symm.subset (D.frontier_subset_domain hzf) with
          (hzD₁ | hzD₂) | hzD₃
        · exact Or.inl hzD₁
        · exact Or.inr hzD₂
        · have hzv : z = v := hm₃₄ z ⟨hzD₃, hzf⟩ hzT₄
          exact Or.inr (hCD₂ (by rw [hzv]; exact hCuv.2))
  exact ⟨T₂, T₄, u, v, p', q', u', v', σ, τ, υ, φ, ev,
    ⟨hAb, hCb, hAC, hcover, hcut₁.fst, hCbuv, hp', hq', hu', hv',
      hr₁, hr₂, hr₃, hr₄, hJ, hev, hpair⟩,
    hσinj, hτinj, hυinj, hφinj, huv, hm₃₄, hm₂, hm₁, hkey⟩

open Classical in
theorem exists_boundary_four_arc_word_of_boundaryBranch
    {M : Type u} [TopologicalSpace M] [T2Space M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
    {D : SingularTwoCell M} {BdM B : Set M}
    (hD : NormalSingularCellData D BdM B)
    {c : hD.singularSet.Branch} (hc : hD.singularSet.IsBoundaryBranch c) :
    ∃ (Ab Cb A₁ A₂ A₃ A₄ : Set (EuclideanSpace ℝ (Fin 2)))
        (p q u v : EuclideanSpace ℝ (Fin 2)) (p' q' u' v' : frontier D.domain)
        (σ : Path p' q') (τ : Path q' u') (υ : Path u' v') (φ : Path v' p')
        (ev : loopCircle ≃ₜ frontier D.domain),
      IsPLBall 1 Ab ∧ IsPLBall 1 Cb ∧ Disjoint Ab Cb ∧
      hD.branchPreimage c = Ab ∪ Cb ∧
      Schoenflies.IsArcBetween Ab p q ∧ Schoenflies.IsArcBetween Cb u v ∧
      (p' : EuclideanSpace ℝ (Fin 2)) = p ∧ (q' : EuclideanSpace ℝ (Fin 2)) = q ∧
      (u' : EuclideanSpace ℝ (Fin 2)) = u ∧ (v' : EuclideanSpace ℝ (Fin 2)) = v ∧
      Set.range (fun t => ((σ t : frontier D.domain) : EuclideanSpace ℝ (Fin 2))) = A₁ ∧
      Set.range (fun t => ((τ t : frontier D.domain) : EuclideanSpace ℝ (Fin 2))) = A₂ ∧
      Set.range (fun t => ((υ t : frontier D.domain) : EuclideanSpace ℝ (Fin 2))) = A₃ ∧
      Set.range (fun t => ((φ t : frontier D.domain) : EuclideanSpace ℝ (Fin 2))) = A₄ ∧
      frontier D.domain = A₁ ∪ (A₂ ∪ (A₃ ∪ A₄)) ∧
      (∀ θ, ev θ = pathToCircle (σ.trans (τ.trans (υ.trans φ))) θ) ∧
      ((D u = D p ∧ D v = D q) ∨ (D u = D q ∧ D v = D p)) := by
  obtain ⟨A, C, p, q, r, s, g, D₁, D₂, D₃, hcut⟩ :=
    hD.exists_isBoundaryBranchCut_of_boundaryBranch hc
  obtain ⟨A₂, A₄, u, v, p', q', u', v', σ, τ, υ, φ, ev, hbody, -⟩ :=
    hD.exists_boundary_four_arc_word_of_cut hcut
  exact ⟨A, C, D₁.domain ∩ frontier D.domain, A₂, D₃.domain ∩ frontier D.domain, A₄,
    p, q, u, v, p', q', u', v', σ, τ, υ, φ, ev, hbody⟩

end NormalSingularCellData

end DifferentialGeometry.Topology.PiecewiseLinear
