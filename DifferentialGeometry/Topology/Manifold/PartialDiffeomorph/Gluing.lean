import Mathlib.Geometry.Manifold.LocalDiffeomorph

noncomputable section

open Set
open scoped Manifold ContDiff

namespace DifferentialGeometry.PartialDiffeomorph

variable {𝕜 E H M : Type*} [NontriviallyNormedField 𝕜]
  [NormedAddCommGroup E] [NormedSpace 𝕜 E] [TopologicalSpace H]
  [TopologicalSpace M] [ChartedSpace H M] {I : ModelWithCorners 𝕜 E H} {n : ℕ∞ω}

theorem exists_disjoint_gluing {ι : Type*} (Φ : ι → PartialDiffeomorph I I M M n)
    (hs : Pairwise fun i j => Disjoint (Φ i).source (Φ j).source)
    (ht : Pairwise fun i j => Disjoint (Φ i).target (Φ j).target) :
    ∃ Ψ : PartialDiffeomorph I I M M n,
      Ψ.source = ⋃ i, (Φ i).source ∧ Ψ.target = ⋃ i, (Φ i).target ∧
      (∀ i, EqOn Ψ (Φ i) (Φ i).source) ∧
      ∀ i, EqOn Ψ.symm (Φ i).symm (Φ i).target := by
  classical
  let F (x : M) := if h : ∃ i, x ∈ (Φ i).source then Φ h.choose x else x
  let G (x : M) := if h : ∃ i, x ∈ (Φ i).target then (Φ h.choose).symm x else x
  have hF (i : ι) (x : M) (hx : x ∈ (Φ i).source) : F x = Φ i x := by
    have hex : ∃ j, x ∈ (Φ j).source := ⟨i, hx⟩
    have hi : hex.choose = i := by
      by_contra hne
      exact disjoint_left.mp (hs hne) hex.choose_spec hx
    simp only [F, dite_eq_left hex, hi]
  have hG (i : ι) (x : M) (hx : x ∈ (Φ i).target) : G x = (Φ i).symm x := by
    have hex : ∃ j, x ∈ (Φ j).target := ⟨i, hx⟩
    have hi : hex.choose = i := by
      by_contra hne
      exact disjoint_left.mp (ht hne) hex.choose_spec hx
    simp only [G, dite_eq_left hex, hi]
  let Ψ : PartialDiffeomorph I I M M n :=
    { toFun := F
      invFun := G
      source := ⋃ i, (Φ i).source
      target := ⋃ i, (Φ i).target
      map_source' := by
        intro x hx
        obtain ⟨i, hi⟩ := mem_iUnion.mp hx
        rw [hF i x hi]
        exact mem_iUnion.mpr ⟨i, (Φ i).map_source' hi⟩
      map_target' := by
        intro x hx
        obtain ⟨i, hi⟩ := mem_iUnion.mp hx
        rw [hG i x hi]
        exact mem_iUnion.mpr ⟨i, (Φ i).map_target' hi⟩
      left_inv' := by
        intro x hx
        obtain ⟨i, hi⟩ := mem_iUnion.mp hx
        rw [hF i x hi, hG i _ ((Φ i).map_source' hi)]
        exact (Φ i).left_inv' hi
      right_inv' := by
        intro x hx
        obtain ⟨i, hi⟩ := mem_iUnion.mp hx
        rw [hG i x hi]
        exact (hF i ((Φ i).symm x) ((Φ i).map_target' hi)).trans ((Φ i).right_inv' hi)
      open_source := isOpen_iUnion fun i => (Φ i).open_source
      open_target := isOpen_iUnion fun i => (Φ i).open_target
      contMDiffOn_toFun := ContMDiffOn.iUnion_of_isOpen
        (fun i => (Φ i).contMDiffOn_toFun.congr (hF i)) (fun i => (Φ i).open_source)
      contMDiffOn_invFun := ContMDiffOn.iUnion_of_isOpen
        (fun i => (Φ i).contMDiffOn_invFun.congr (hG i)) (fun i => (Φ i).open_target) }
  exact ⟨Ψ, rfl, rfl, hF, hG⟩

theorem exists_extension_by_identity (Φ : PartialDiffeomorph I I M M n)
    {V : Set M} (hV : IsOpen V) (hinter : Φ.source ∩ V = Φ.target ∩ V)
    (hfix : EqOn Φ id (Φ.source ∩ V)) :
    ∃ Ψ : PartialDiffeomorph I I M M n,
      Ψ.source = Φ.source ∪ V ∧ Ψ.target = Φ.target ∪ V ∧
      EqOn Ψ Φ Φ.source ∧ EqOn Ψ id V ∧
      EqOn Ψ.symm Φ.symm Φ.target ∧ EqOn Ψ.symm id V := by
  classical
  let F := Φ.source.piecewise Φ id
  let G := Φ.target.piecewise Φ.symm id
  have hF (x : M) (hx : x ∈ Φ.source) : F x = Φ x := piecewise_eq_of_mem _ _ _ hx
  have hG (x : M) (hx : x ∈ Φ.target) : G x = Φ.symm x := piecewise_eq_of_mem _ _ _ hx
  have hFi (x : M) (hx : x ∈ V) : F x = x := by
    by_cases hs : x ∈ Φ.source
    · exact (hF x hs).trans (hfix ⟨hs, hx⟩)
    · exact piecewise_eq_of_notMem _ _ _ hs
  have hGi (x : M) (hx : x ∈ V) : G x = x := by
    by_cases ht : x ∈ Φ.target
    · have hs : x ∈ Φ.source := ((hinter.symm ▸ (show x ∈ Φ.target ∩ V from ⟨ht, hx⟩))).1
      have heq := Φ.left_inv' hs
      rw [hfix ⟨hs, hx⟩] at heq
      exact (hG x ht).trans heq
    · exact piecewise_eq_of_notMem _ _ _ ht
  let Ψ : PartialDiffeomorph I I M M n :=
    { toFun := F
      invFun := G
      source := Φ.source ∪ V
      target := Φ.target ∪ V
      map_source' := by
        intro x hx
        rcases hx with hx | hx
        · rw [hF x hx]
          exact Or.inl (Φ.map_source' hx)
        · rw [hFi x hx]
          exact Or.inr hx
      map_target' := by
        intro x hx
        rcases hx with hx | hx
        · rw [hG x hx]
          exact Or.inl (Φ.map_target' hx)
        · rw [hGi x hx]
          exact Or.inr hx
      left_inv' := by
        intro x hx
        rcases hx with hx | hx
        · rw [hF x hx, hG _ (Φ.map_source' hx)]
          exact Φ.left_inv' hx
        · rw [hFi x hx, hGi x hx]
      right_inv' := by
        intro x hx
        rcases hx with hx | hx
        · rw [hG x hx]
          exact (hF (Φ.symm x) (Φ.map_target' hx)).trans (Φ.right_inv' hx)
        · rw [hGi x hx, hFi x hx]
      open_source := Φ.open_source.union hV
      open_target := Φ.open_target.union hV
      contMDiffOn_toFun := (Φ.contMDiffOn_toFun.congr hF).union_of_isOpen
        (contMDiffOn_id.congr hFi) Φ.open_source hV
      contMDiffOn_invFun := (Φ.contMDiffOn_invFun.congr hG).union_of_isOpen
        (contMDiffOn_id.congr hGi) Φ.open_target hV }
  exact ⟨Ψ, rfl, rfl, hF, hFi, hG, hGi⟩

end DifferentialGeometry.PartialDiffeomorph
