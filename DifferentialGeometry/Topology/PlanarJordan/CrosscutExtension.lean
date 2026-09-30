import DifferentialGeometry.Topology.PlanarJordan.Crosscut
import DifferentialGeometry.Topology.Homeomorph.ClosedExtension

open Set

namespace DifferentialGeometry.Topology.PlanarJordan

open Schoenflies

theorem exists_homeomorph_closed_disk_extending_crosscut
    {C P Q : Set Plane} {p q : Plane}
    (hC : IsJordanCurve C) (hP : IsArcBetween P p q) (hQ : IsArcBetween Q p q)
    (hp : p ∈ C) (hq : q ∈ C)
    (hPC : P \ {p, q} ⊆ inside C) (hQC : Q \ {p, q} ⊆ inside C)
    (f : ArcHomeo P Q p q p q) :
    ∃ d : ↥(C ∪ inside C) ≃ₜ ↥(C ∪ inside C),
      (∀ x : ↥(C ∪ inside C), (x : Plane) ∈ P → (d x : Plane) = f.toFun x) ∧
      ∀ x : ↥(C ∪ inside C), (x : Plane) ∈ C → d x = x := by
  have hpq : p ≠ q := by
    obtain ⟨a, _, ha, _, ha₀, ha₁⟩ := hP
    intro heq
    exact zero_ne_one (ha zero_mem_I one_mem_I (ha₀.trans (heq.trans ha₁.symm)))
  obtain ⟨A₁, A₂, hcut⟩ := exists_isCutPair hC hp hq hpq
  let reflArc (A : Set Plane) : ArcHomeo A A p q p q := {
    toFun := id
    invFun := id
    continuousOn_toFun := continuousOn_id
    continuousOn_invFun := continuousOn_id
    leftInvOn := fun _ _ => rfl
    rightInvOn := fun _ _ => rfl
    image_eq := image_id _
    map_left := rfl
    map_right := rfl }
  have hmeetP {A : Set Plane} (hA : A ⊆ C) :
      ∀ x ∈ A, x ∈ P → x = p ∨ x = q := by
    intro x hxA hxP
    have hx := (arc_inter_curve_eq_pair hP hp hq hPC).subset ⟨hxP, hA hxA⟩
    simpa only [mem_insert_iff, mem_singleton_iff] using hx
  have hmeetQ {A : Set Plane} (hA : A ⊆ C) :
      ∀ x ∈ A, x ∈ Q → x = p ∨ x = q := by
    intro x hxA hxQ
    have hx := (arc_inter_curve_eq_pair hQ hp hq hQC).subset ⟨hxQ, hA hxA⟩
    simpa only [mem_insert_iff, mem_singleton_iff] using hx
  obtain ⟨e₁, he₁A, he₁P⟩ := exists_homeomorph_extending_two_arcs
    hcut.fst hP hcut.fst hQ (hmeetP hcut.fst_subset) (hmeetQ hcut.fst_subset) (reflArc A₁) f
  obtain ⟨e₂, he₂A, he₂P⟩ := exists_homeomorph_extending_two_arcs
    hcut.snd hP hcut.snd hQ (hmeetP hcut.snd_subset) (hmeetQ hcut.snd_subset) (reflArc A₂) f
  have he₁curve : e₁ '' (A₁ ∪ P) = A₁ ∪ Q := by
    rw [image_union, he₁A.image_eq, he₁P.image_eq, f.image_eq]
    exact congrArg (fun S => S ∪ Q) (image_id A₁)
  have he₂curve : e₂ '' (A₂ ∪ P) = A₂ ∪ Q := by
    rw [image_union, he₂A.image_eq, he₂P.image_eq, f.image_eq]
    exact congrArg (fun S => S ∪ Q) (image_id A₂)
  let D₁ := closure (inside (A₁ ∪ P))
  let D₂ := closure (inside (A₂ ∪ P))
  let T₁ := closure (inside (A₁ ∪ Q))
  let T₂ := closure (inside (A₂ ∪ Q))
  have he₁image : e₁ '' D₁ = T₁ := by
    dsimp [D₁, T₁]
    rw [e₁.image_closure, image_inside, he₁curve]
  have he₂image : e₂ '' D₂ = T₂ := by
    dsimp [D₂, T₂]
    rw [e₂.image_closure, image_inside, he₂curve]
  have hsep₁ := jordan_curve_theorem (isJordanCurve_cut_arc_union hP hcut hPC)
  have hsep₂ := jordan_curve_theorem (isJordanCurve_cut_arc_union hP hcut.symm hPC)
  have hA₁sub : A₁ ⊆ D₁ := fun _ hx =>
    (IsRegionOf.inside (A₁ ∪ P)).subset_closure hsep₁ (Or.inl hx)
  have hA₂sub : A₂ ⊆ D₂ := fun _ hx =>
    (IsRegionOf.inside (A₂ ∪ P)).subset_closure hsep₂ (Or.inl hx)
  have hPsub : P ⊆ D₁ := fun _ hx =>
    (IsRegionOf.inside (A₁ ∪ P)).subset_closure hsep₁ (Or.inr hx)
  obtain ⟨hcoverP, hinterP⟩ := closed_crosscut_regions hC hP hcut hPC
  obtain ⟨hcoverQ, hinterQ⟩ := closed_crosscut_regions hC hQ hcut hQC
  have hbij₁ : BijOn e₁ D₁ T₁ := he₁image ▸ e₁.injective.injOn.bijOn_image
  have hbij₂ : BijOn e₂ D₂ T₂ := he₂image ▸ e₂.injective.injOn.bijOn_image
  obtain ⟨e, heD₁, heD₂⟩ := Homeomorph.exists_gluing_of_isCompact
    hsep₁.isBounded_inside.isCompact_closure hsep₂.isBounded_inside.isCompact_closure
    e₁.continuous.continuousOn e₂.continuous.continuousOn hbij₁ hbij₂
    (fun x hx => (he₁P (hinterP ▸ hx)).trans (he₂P (hinterP ▸ hx)).symm) (by
      change SurjOn e₁ (D₁ ∩ D₂) (T₁ ∩ T₂)
      rw [show D₁ ∩ D₂ = P from hinterP, show T₁ ∩ T₂ = Q from hinterQ]
      intro y hy
      obtain ⟨x, hx, hxy⟩ := f.image_eq.symm ▸ hy
      exact ⟨x, hx, (he₁P hx).trans hxy⟩)
  let d : ↥(C ∪ inside C) ≃ₜ ↥(C ∪ inside C) :=
    (Homeomorph.setCongr hcoverP.symm).trans (e.trans (Homeomorph.setCongr hcoverQ))
  have hd₁ (x : ↥(C ∪ inside C)) (hx : (x : Plane) ∈ D₁) :
      (d x : Plane) = e₁ x := heD₁ x hx
  have hd₂ (x : ↥(C ∪ inside C)) (hx : (x : Plane) ∈ D₂) :
      (d x : Plane) = e₂ x := heD₂ x hx
  refine ⟨d, fun x hx => (hd₁ x (hPsub hx)).trans (he₁P hx), ?_⟩
  intro x hx
  apply Subtype.ext
  rcases hcut.union_eq.symm.subset hx with hx | hx
  · exact (hd₁ x (hA₁sub hx)).trans (he₁A hx)
  · exact (hd₂ x (hA₂sub hx)).trans (he₂A hx)

theorem exists_homeomorph_extending_crosscut
    {C P Q : Set Plane} {p q : Plane}
    (hC : IsJordanCurve C) (hP : IsArcBetween P p q) (hQ : IsArcBetween Q p q)
    (hp : p ∈ C) (hq : q ∈ C)
    (hPC : P \ {p, q} ⊆ inside C) (hQC : Q \ {p, q} ⊆ inside C)
    (f : ArcHomeo P Q p q p q) :
    ∃ e : Plane ≃ₜ Plane, EqOn e f.toFun P ∧ EqOn e id (inside C)ᶜ ∧
      ∀ x, dist (e x) x ≤ Metric.diam (C ∪ inside C) := by
  obtain ⟨d, hdP, hdC⟩ :=
    exists_homeomorph_closed_disk_extending_crosscut hC hP hQ hp hq hPC hQC f
  have hsep := jordan_curve_theorem hC
  have hclosed := isClosed_union_inside hsep
  have hfrontier : frontier (C ∪ inside C) ⊆ C := by
    have hclosure : C ∪ inside C = closure (inside C) := by
      rw [(IsRegionOf.inside C).closure_eq hsep, union_comm]
    rw [hclosure]
    exact (frontier_closure_subset (s := inside C)).trans hsep.frontier_inside.subset
  have hdfront : ∀ x : ↥(C ∪ inside C), (x : Plane) ∈ frontier (C ∪ inside C) →
      d x = x := fun x hx => hdC x (hfrontier hx)
  have hbounded : Bornology.IsBounded (C ∪ inside C) :=
    hC.isCompact.isBounded.union hsep.isBounded_inside
  refine ⟨d.extendById hclosed hdfront, ?_, ?_,
    d.dist_extendById_le_diam hclosed hdfront hbounded⟩
  · intro x hx
    have hxD : x ∈ C ∪ inside C := by
      by_cases hends : x ∈ ({p, q} : Set Plane)
      · rcases hends with rfl | rfl
        · exact Or.inl hp
        · exact Or.inl hq
      · exact Or.inr (hPC ⟨hx, hends⟩)
    rw [d.extendById_apply_of_mem hclosed hdfront hxD]
    exact hdP ⟨x, hxD⟩ hx
  · intro x hx
    by_cases hxD : x ∈ C ∪ inside C
    · rw [d.extendById_apply_of_mem hclosed hdfront hxD]
      exact congrArg Subtype.val (hdC ⟨x, hxD⟩ (hxD.elim id (fun h => (hx h).elim)))
    · exact d.extendById_apply_of_notMem hclosed hdfront hxD

theorem exists_homeomorph_image_crosscut_dist_lt
    {C P Q : Set Plane} {p q : Plane}
    (hC : IsJordanCurve C) (hP : IsArcBetween P p q) (hQ : IsArcBetween Q p q)
    (hp : p ∈ C) (hq : q ∈ C)
    (hPC : P \ {p, q} ⊆ inside C) (hQC : Q \ {p, q} ⊆ inside C)
    {ε : Plane → ℝ} (hε : ∀ x, 0 < ε x)
    (hdiam : ∀ x ∈ C ∪ inside C, Metric.diam (C ∪ inside C) < ε x) :
    ∃ e : Plane ≃ₜ Plane, e '' P = Q ∧ EqOn e id (inside C)ᶜ ∧
      ∀ x, dist (e x) x < ε x := by
  obtain ⟨f⟩ := exists_arcHomeo hP hQ
  obtain ⟨e, heP, hefix, hedist⟩ :=
    exists_homeomorph_extending_crosscut hC hP hQ hp hq hPC hQC f
  refine ⟨e, heP.image_eq.trans f.image_eq, hefix, fun x => ?_⟩
  by_cases hx : x ∈ C ∪ inside C
  · exact (hedist x).trans_lt (hdiam x hx)
  · rw [hefix (fun h => hx (Or.inr h)), id_eq, dist_self]
    exact hε x

end DifferentialGeometry.Topology.PlanarJordan
