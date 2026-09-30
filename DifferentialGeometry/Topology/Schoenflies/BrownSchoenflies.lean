import DifferentialGeometry.Topology.Schoenflies.BrownTwoFiberTransport
import DifferentialGeometry.Topology.Schoenflies.CollaredSphereMap
import DifferentialGeometry.Topology.Cellular.CellularLocalization
import DifferentialGeometry.Topology.Sphere.SphereHemispheres

namespace DifferentialGeometry.Topology

open Set Metric _root_.Topology

section Recognition

variable {n : ℕ} {X Y : Type*} [MetricSpace X] [CompactSpace X]
    [TopologicalSpace Y] [T2Space Y]

theorem isCellular.exists_homeomorph_preserving_preimage {K : Set X} (hK : isCellular n K)
    {f : X → Y} (hf : Continuous f) (hfs : Function.Surjective f)
    (hfK : collapsesExactly f K) {T : Set Y} (hT : IsClosed T)
    (hKT : Disjoint K (f ⁻¹' T)) :
    ∃ e : X ≃ₜ Y, (∀ x, f x ∈ T → e x = f x) ∧ e ⁻¹' T = f ⁻¹' T := by
  obtain ⟨q, hqs, hqK, hqfix⟩ := hK.exists_collapse_supported
    (U := (f ⁻¹' T)ᶜ) (hT.preimage hf).isOpen_compl
    (fun x hx => disjoint_left.mp hKT hx)
  let e : X ≃ₜ Y := homeomorphOfSameFibers q.continuous hqs hf hfs
    (fun x y => (hqK x y).trans (hfK x y).symm)
  have heq (x : X) : e (q x) = f x :=
    quotientHomeomorphOfSameFibers_apply _ _ _ x
  have hfix (x : X) (hx : f x ∈ T) : q x = x := hqfix x (not_not.mpr hx)
  refine ⟨e, ?_, ?_⟩
  · intro x hx
    exact (congrArg e (hfix x hx)).symm.trans (heq x)
  · ext x
    constructor
    · intro hx
      obtain ⟨y, rfl⟩ := hqs x
      have hy : f y ∈ T := by
        change e (q y) ∈ T at hx
        rwa [heq] at hx
      rwa [hfix y hy]
    · intro hx
      change e x ∈ T
      rw [← hfix x hx, heq]
      exact hx

theorem exists_disk_embedding_of_cellular_quotient {D E K : Set X}
    (hD : IsClosed D) (hED : E ⊆ D)
    (hK : isCellular n (Subtype.val ⁻¹' K : Set D))
    (f : D → Disk n) (hf : Continuous f) (hfs : Function.Surjective f)
    (hfK : collapsesExactly f (Subtype.val ⁻¹' K))
    (hboundary : ∀ x : D, f x ∈ diskSphere n ↔ (x : X) ∈ E)
    (hKE : Disjoint K E) :
    ∃ e : Disk n → X, IsClosedEmbedding e ∧ range e = D ∧ e '' diskSphere n = E := by
  have : CompactSpace D := isCompact_iff_compactSpace.mp hD.isCompact
  obtain ⟨H, -, hH⟩ := hK.exists_homeomorph_preserving_preimage hf hfs hfK
    (isClosed_diskSphere n) (disjoint_left.mpr (by
      intro x hx hxb
      exact disjoint_left.mp hKE hx ((hboundary x).mp hxb)))
  have hHboundary (x : D) : H x ∈ diskSphere n ↔ (x : X) ∈ E := by
    have heq : H x ∈ diskSphere n ↔ f x ∈ diskSphere n := by
      change x ∈ H ⁻¹' diskSphere n ↔ x ∈ f ⁻¹' diskSphere n
      rw [hH]
    exact heq.trans (hboundary x)
  let e : Disk n → X := Subtype.val ∘ H.symm
  refine ⟨e, hD.isClosedEmbedding_subtypeVal.comp H.symm.isClosedEmbedding, ?_, ?_⟩
  · change range (Subtype.val ∘ H.symm) = D
    rw [range_comp, H.symm.surjective.range_eq, image_univ, Subtype.range_coe]
  · ext x
    constructor
    · rintro ⟨z, hz, rfl⟩
      exact (hHboundary (H.symm z)).mp (by simpa using hz)
    · intro hx
      let y : D := ⟨x, hED hx⟩
      exact ⟨H y, (hHboundary y).mpr hx, by simp [e, y]⟩

end Recognition

section SphereRecognition

variable {m : ℕ} {X : Type*} [MetricSpace X] [CompactSpace X]

theorem exists_side_disks_of_sphere_collapse (t : X → ℝ) (ht : Continuous t)
    (F : X → sphere (0 : EuclideanSpace ℝ (Fin (m + 2))) 1)
    (hF : Continuous F) (hFs : Function.Surjective F)
    (hfiber : ∀ x y, F x = F y ↔ x = y ∨
      (t x ≤ -1 ∧ t y ≤ -1) ∨ (1 ≤ t x ∧ 1 ≤ t y))
    (hlower : ∀ x, (F x : EuclideanSpace ℝ (Fin (m + 2))) (Fin.last (m + 1)) ≤ 0 ↔ t x ≤ 0)
    (hupper : ∀ x, 0 ≤ (F x : EuclideanSpace ℝ (Fin (m + 2))) (Fin.last (m + 1)) ↔ 0 ≤ t x)
    (hA : isCellular (m + 1) {x | t x ≤ -1})
    (hB : isCellular (m + 1) {x | 1 ≤ t x}) :
    (∃ e : Disk (m + 1) → X, IsClosedEmbedding e ∧
      range e = {x | t x ≤ 0} ∧ e '' diskSphere (m + 1) = {x | t x = 0}) ∧
    (∃ e : Disk (m + 1) → X, IsClosedEmbedding e ∧
      range e = {x | 0 ≤ t x} ∧ e '' diskSphere (m + 1) = {x | t x = 0}) := by
  have hzero (x : X) :
      (F x : EuclideanSpace ℝ (Fin (m + 2))) (Fin.last (m + 1)) = 0 ↔ t x = 0 := by
    rw [le_antisymm_iff, hlower, hupper, ← le_antisymm_iff]
  constructor
  · let D : Set X := {x | t x ≤ 0}
    have hD : IsClosed D := isClosed_Iic.preimage ht
    have hAD : {x | t x ≤ -1} ⊆ interior D := by
      apply Subset.trans (b := {x | t x < 0}) (fun x hx => by dsimp at *; linarith)
      exact interior_maximal (fun x hx => by change t x ≤ 0; exact le_of_lt hx)
        (isOpen_Iio.preimage ht)
    let f₀ : D → lowerClosedHemisphere m := fun x => ⟨F x, (hlower x).mpr x.2⟩
    have hf₀ : Continuous f₀ := (hF.comp continuous_subtype_val).subtype_mk _
    have hfs₀ : Function.Surjective f₀ := by
      intro y
      obtain ⟨x, hx⟩ := hFs y.val
      have hxD : x ∈ D := (hlower x).mp (hx ▸ y.2)
      exact ⟨⟨x, hxD⟩, Subtype.ext hx⟩
    let f := lowerClosedHemisphereHomeomorph m ∘ f₀
    have hffiber : collapsesExactly f (Subtype.val ⁻¹' {x | t x ≤ -1}) := by
      intro x y
      have heq : f x = f y ↔ F x = F y := by
        exact (lowerClosedHemisphereHomeomorph m).injective.eq_iff.trans Subtype.ext_iff
      rw [heq, hfiber]
      constructor
      · rintro (hxy | ha | hb)
        · exact Or.inl (Subtype.ext hxy)
        · exact Or.inr ha
        · have hx := x.2; dsimp [D] at hx; linarith [hb.1]
      · rintro (rfl | ha)
        · exact Or.inl rfl
        · exact Or.inr (Or.inl ha)
    apply exists_disk_embedding_of_cellular_quotient hD
      (fun x hx => by change t x = 0 at hx; exact hx.le)
      (hA.subtype_of_subset_interior hAD) f
      ((lowerClosedHemisphereHomeomorph m).continuous.comp hf₀)
      ((lowerClosedHemisphereHomeomorph m).surjective.comp hfs₀) hffiber
    · intro x
      exact (lowerClosedHemisphereHomeomorph_mem_diskSphere_iff m (f₀ x)).trans (hzero x)
    · apply disjoint_left.mpr
      intro x hx he
      change t x ≤ -1 at hx
      change t x = 0 at he
      linarith
  · let D : Set X := {x | 0 ≤ t x}
    have hD : IsClosed D := isClosed_Ici.preimage ht
    have hBD : {x | 1 ≤ t x} ⊆ interior D := by
      apply Subset.trans (b := {x | 0 < t x}) (fun x hx => by dsimp at *; linarith)
      exact interior_maximal (fun x hx => by change 0 ≤ t x; exact le_of_lt hx)
        (isOpen_Ioi.preimage ht)
    let f₀ : D → upperClosedHemisphere m := fun x => ⟨F x, (hupper x).mpr x.2⟩
    have hf₀ : Continuous f₀ := (hF.comp continuous_subtype_val).subtype_mk _
    have hfs₀ : Function.Surjective f₀ := by
      intro y
      obtain ⟨x, hx⟩ := hFs y.val
      have hxD : x ∈ D := (hupper x).mp (hx ▸ y.2)
      exact ⟨⟨x, hxD⟩, Subtype.ext hx⟩
    let f := upperClosedHemisphereHomeomorph m ∘ f₀
    have hffiber : collapsesExactly f (Subtype.val ⁻¹' {x | 1 ≤ t x}) := by
      intro x y
      have heq : f x = f y ↔ F x = F y := by
        exact (upperClosedHemisphereHomeomorph m).injective.eq_iff.trans Subtype.ext_iff
      rw [heq, hfiber]
      constructor
      · rintro (hxy | ha | hb)
        · exact Or.inl (Subtype.ext hxy)
        · have hx := x.2; dsimp [D] at hx; linarith [ha.1]
        · exact Or.inr hb
      · rintro (rfl | hb)
        · exact Or.inl rfl
        · exact Or.inr (Or.inr hb)
    apply exists_disk_embedding_of_cellular_quotient hD
      (fun x hx => by change t x = 0 at hx; exact hx.ge)
      (hB.subtype_of_subset_interior hBD) f
      ((upperClosedHemisphereHomeomorph m).continuous.comp hf₀)
      ((upperClosedHemisphereHomeomorph m).surjective.comp hfs₀) hffiber
    · intro x
      exact (upperClosedHemisphereHomeomorph_mem_diskSphere_iff m (f₀ x)).trans (hzero x)
    · apply disjoint_left.mpr
      intro x hx he
      change 1 ≤ t x at hx
      change t x = 0 at he
      linarith

end SphereRecognition

section Schoenflies

variable {m : ℕ} {X : Type*} [MetricSpace X] [CompactSpace X]

theorem exists_side_disks_of_height_collar
    (eX : X ≃ₜ sphere (0 : EuclideanSpace ℝ (Fin (m + 2))) 1)
    (t : X → ℝ) (ht : Continuous t)
    (Φ : (sphere (0 : EuclideanSpace ℝ (Fin (m + 1))) 1 × SuspensionInterval) ≃ₜ
      {x : X // t x ∈ Icc (-1 : ℝ) 1})
    (hΦ : ∀ p, t (Φ p).val = (p.2 : ℝ)) :
    (∃ e : Disk (m + 1) → X, IsClosedEmbedding e ∧
      range e = {x | t x ≤ 0} ∧ e '' diskSphere (m + 1) = {x | t x = 0}) ∧
    (∃ e : Disk (m + 1) → X, IsClosedEmbedding e ∧
      range e = {x | 0 ≤ t x} ∧ e '' diskSphere (m + 1) = {x | t x = 0}) := by
  obtain ⟨F, hFs, hfiber, hlower, hupper⟩ :=
    exists_sphere_collapse_of_height_collar t ht Φ hΦ
  let A : Set X := {x | t x ≤ -1}
  let B : Set X := {x | 1 ≤ t x}
  have hA : IsCompact A := (isClosed_Iic.preimage ht).isCompact
  have hB : IsCompact B := (isClosed_Ici.preimage ht).isCompact
  obtain ⟨s, hs⟩ : (sphere (0 : EuclideanSpace ℝ (Fin (m + 1))) 1).Nonempty :=
    NormedSpace.sphere_nonempty.mpr zero_le_one
  let s₀ : sphere (0 : EuclideanSpace ℝ (Fin (m + 1))) 1 := ⟨s, hs⟩
  have hneA : A.Nonempty := by
    refine ⟨(Φ (s₀, ⟨-1, by norm_num⟩)).val, ?_⟩
    change t _ ≤ -1
    rw [hΦ]
  have hneB : B.Nonempty := by
    refine ⟨(Φ (s₀, ⟨1, by norm_num⟩)).val, ?_⟩
    change 1 ≤ t _
    rw [hΦ]
  have hAB : Disjoint A B := by
    apply disjoint_left.mpr
    intro x hx hy
    change t x ≤ -1 at hx
    change 1 ≤ t x at hy
    linarith
  have hproper : A ∪ B ≠ univ := by
    intro hall
    have hx : (Φ (s₀, ⟨0, by norm_num⟩)).val ∈ A ∪ B := hall ▸ mem_univ _
    change t _ ≤ -1 ∨ 1 ≤ t _ at hx
    rw [hΦ] at hx
    norm_num at hx
  obtain ⟨hcellA, hcellB⟩ := isCellular_two_fibers_of_homeomorph eX
    F.continuous hFs hfiber hA hB hneA hneB hAB hproper
  exact exists_side_disks_of_sphere_collapse t ht F F.continuous hFs hfiber
    hlower hupper hcellA hcellB

end Schoenflies

end DifferentialGeometry.Topology
