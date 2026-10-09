import DifferentialGeometry.Geometry.Collapse.EdgeDisk.CompactDomain

/-!
# FDC02's face-point lemma: a frontier point of the edge base carries a face point

Lane S-EDP-FDC3, group G7. Blueprint `master207B.tex`, FDC02 / EDP05 (B:7040–7090, 7246–7283):
"Near a horizontal face, an ambient defining function for `M₂` descends to a smooth function `b`
on the edge base" — the descent is needed at every frontier point `c₀` of `C₂`, and EDP05's
classification of the faces is a statement about the points of the whole disk over `c₀` on
`∂M₂`. This kernel provides such a point.

**`exists_face_point_EFE`.** `Y` compact, `π : Y → W` continuous into a Hausdorff space, a global
continuous height `hg`, the whole disks `D c = {y | π y = ι c ∧ hg y ≤ L}` (`ι : B → W` an
embedding), preconnected and nonempty (E0: each is a disk), and the edge base
`C₂ = {c | D c ∩ M₂ ≠ ∅}` compact: for `c₀ ∈ ∂C₂` the disk over `c₀` meets `∂M₂`.
Proof: if it did not, the preconnected disk lies in `int M₂` or in `(cl M₂)ᶜ`. In the second case
`c₀ ∈ cl C₂ = C₂` (compact in a Hausdorff space) puts a point of `M₂` on the disk. In the first
case `F = {hg ≤ L} ∖ int M₂` is compact, `π(F)` is closed, its complement `G` is open and contains
`ι c₀`, and for `ι c ∈ G` the nonempty disk over `c` lies in `int M₂`, whence `ι⁻¹ G ⊆ C₂` and
`c₀ ∈ int C₂`.
-/

set_option autoImplicit false

noncomputable section

open Set Function Filter Topology

namespace DifferentialGeometry.Geometry.Collapse.EdgeDisk

variable {Y W B : Type*} [TopologicalSpace Y] [TopologicalSpace W] [TopologicalSpace B]

/-- **The face-point lemma** (see the module docstring). -/
theorem exists_face_point_EFE [CompactSpace Y] [T2Space W] {ι : B → W} (hι : IsEmbedding ι)
    {π : Y → W} (hπ : Continuous π) {hg : Y → ℝ} (hgc : Continuous hg) {L : ℝ} {M₂ : Set Y}
    (D : B → Set Y) (hD : ∀ c, D c = {y | π y = ι c ∧ hg y ≤ L})
    (hconn : ∀ c, IsPreconnected (D c)) (hne : ∀ c, (D c).Nonempty)
    (hC : IsCompact {c : B | (D c ∩ M₂).Nonempty}) {c₀ : B}
    (hc₀ : c₀ ∈ frontier {c : B | (D c ∩ M₂).Nonempty}) : (D c₀ ∩ frontier M₂).Nonempty := by
  by_contra hno
  have hdisj : Disjoint (D c₀) (frontier M₂) :=
    Set.disjoint_iff_inter_eq_empty.mpr (Set.not_nonempty_iff_eq_empty.mp hno)
  rcases DifferentialGeometry.Topology.isPreconnected_subset_interior_or_subset_compl_closure
      (hconn c₀) hdisj with h | h
  · have hFc : IsClosed {y : Y | hg y ≤ L ∧ y ∉ interior M₂} :=
      (isClosed_le hgc continuous_const).inter isOpen_interior.isClosed_compl
    have hGc : IsClosed (π '' {y : Y | hg y ≤ L ∧ y ∉ interior M₂}) :=
      (hFc.isCompact.image hπ).isClosed
    have hc₀G : ι c₀ ∈ (π '' {y : Y | hg y ≤ L ∧ y ∉ interior M₂})ᶜ := by
      rintro ⟨y, ⟨hy1, hy2⟩, hyπ⟩
      exact hy2 (h (by rw [hD]; exact ⟨hyπ, hy1⟩))
    have hsub : ι ⁻¹' (π '' {y : Y | hg y ≤ L ∧ y ∉ interior M₂})ᶜ ⊆
        {c : B | (D c ∩ M₂).Nonempty} := by
      intro c hc
      obtain ⟨y, hy⟩ := hne c
      have hy' := hy
      rw [hD] at hy'
      have hyi : y ∈ interior M₂ := by
        by_contra hyi
        exact hc ⟨y, ⟨hy'.2, hyi⟩, hy'.1⟩
      exact ⟨y, hy, interior_subset hyi⟩
    have hint : c₀ ∈ interior {c : B | (D c ∩ M₂).Nonempty} :=
      mem_interior.mpr ⟨_, hsub, hGc.isOpen_compl.preimage hι.continuous, hc₀G⟩
    exact hc₀.2 hint
  · have hCcl : IsClosed {c : B | (D c ∩ M₂).Nonempty} := by
      have h1 : IsClosed (ι '' {c : B | (D c ∩ M₂).Nonempty}) :=
        (hC.image hι.continuous).isClosed
      have h2 : ι ⁻¹' (ι '' {c : B | (D c ∩ M₂).Nonempty}) = {c : B | (D c ∩ M₂).Nonempty} :=
        hι.injective.preimage_image _
      rw [← h2]
      exact h1.preimage hι.continuous
    have hc₀C : c₀ ∈ {c : B | (D c ∩ M₂).Nonempty} := hCcl.closure_eq ▸ hc₀.1
    obtain ⟨y, hyD, hyM⟩ := hc₀C
    exact h hyD (subset_closure hyM)

end DifferentialGeometry.Geometry.Collapse.EdgeDisk
