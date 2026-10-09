import DifferentialGeometry.Topology.ClosedCover
import Mathlib.Topology.Homeomorph.Lemmas
import Mathlib.Topology.Instances.Real.Lemmas

noncomputable section

open Set

namespace DifferentialGeometry.Topology

private theorem exists_continuousMap_of_cylindrical_cover
    {ι X Y : Type*} [Finite ι] [TopologicalSpace X] [TopologicalSpace Y]
    {C : ι → Type*} [∀ i, TopologicalSpace (C i)]
    (e : ∀ i, C i × Ici (0 : ℝ) → X)
    (he : ∀ i, _root_.Topology.IsClosedEmbedding (e i))
    (hdis : Pairwise fun i j ↦ Disjoint (range (e i)) (range (e j)))
    {K : Set X} (hK : IsClosed K) (hcover : K ∪ ⋃ i, range (e i) = univ)
    (f : C(K, Y)) (g : ∀ i, C(C i × Ici (0 : ℝ), Y))
    (hmatch : ∀ i p (hp : e i p ∈ K), f ⟨e i p, hp⟩ = g i p) :
    ∃ F : C(X, Y), (∀ p : K, F p = f p) ∧ ∀ i p, F (e i p) = g i p := by
  let S : Option ι → Set X
    | none => K
    | some i => range (e i)
  let φ : ∀ i, C(S i, Y)
    | none => f
    | some i => (g i).comp ⟨(he i).isEmbedding.toHomeomorph.symm,
        (he i).isEmbedding.toHomeomorph.symm.continuous⟩
  have hφ (i : ι) (p : C i × Ici (0 : ℝ)) :
      φ (some i) ⟨e i p, mem_range_self p⟩ = g i p := by
    change g i ((he i).isEmbedding.toHomeomorph.symm ⟨e i p, mem_range_self p⟩) = _
    rw [_root_.Topology.IsEmbedding.toHomeomorph_symm_apply]
  have hcompat : ∀ (i j) (x : X) (hxi : x ∈ S i) (hxj : x ∈ S j),
      φ i ⟨x, hxi⟩ = φ j ⟨x, hxj⟩ := by
    intro i j x hxi hxj
    cases i with
    | none =>
      cases j with
      | none => rfl
      | some j =>
        obtain ⟨p, rfl⟩ := hxj
        exact (hmatch j p hxi).trans (hφ j p).symm
    | some i =>
      cases j with
      | none =>
        obtain ⟨p, rfl⟩ := hxi
        exact (hφ i p).trans (hmatch i p hxj).symm
      | some j =>
        by_cases hij : i = j
        · subst j
          rfl
        · exact False.elim (disjoint_left.mp (hdis hij) hxi hxj)
  have hS : ⋃ i, S i = univ := by
    rw [iUnion_option]
    exact hcover
  have hclosed : ∀ i, IsClosed (S i)
    | none => hK
    | some i => (he i).isClosed_range
  let F := ContinuousMap.liftClosedCover S φ hcompat hS hclosed (locallyFinite_of_finite S)
  refine ⟨F, ?_, ?_⟩
  · intro p
    exact ContinuousMap.liftClosedCover_coe
      (S := S) (φ := φ) (hφ := hcompat) (hcov := hS) (hclosed := hclosed)
      (hfinite := locallyFinite_of_finite S) (i := none) p
  · intro i p
    exact (ContinuousMap.liftClosedCover_coe
      (S := S) (φ := φ) (hφ := hcompat) (hcov := hS) (hclosed := hclosed)
      (hfinite := locallyFinite_of_finite S) (i := some i) ⟨e i p, mem_range_self p⟩).trans
      (hφ i p)

theorem exists_homeomorph_of_cylindrical_cover
    {ι X Y : Type*} [Finite ι] [TopologicalSpace X] [TopologicalSpace Y]
    {C D : ι → Type*} [∀ i, TopologicalSpace (C i)] [∀ i, TopologicalSpace (D i)]
    (e : ∀ i, C i × Ici (0 : ℝ) → X) (f : ∀ i, D i × Ici (0 : ℝ) → Y)
    (he : ∀ i, _root_.Topology.IsClosedEmbedding (e i))
    (hf : ∀ i, _root_.Topology.IsClosedEmbedding (f i))
    (hedis : Pairwise fun i j ↦ Disjoint (range (e i)) (range (e j)))
    (hfdis : Pairwise fun i j ↦ Disjoint (range (f i)) (range (f j)))
    {K : Set X} {L : Set Y} (hK : IsClosed K) (hL : IsClosed L)
    (hcoverX : K ∪ ⋃ i, range (e i) = univ) (hcoverY : L ∪ ⋃ i, range (f i) = univ)
    (hzeroX : ∀ i p, e i p ∈ K ↔ p.2.val = 0)
    (hzeroY : ∀ i p, f i p ∈ L ↔ p.2.val = 0)
    (κ : K ≃ₜ L) (φ : ∀ i, C i ≃ₜ D i)
    (hboundary : ∀ i c,
      (κ ⟨e i (c, ⟨0, by simp⟩), (hzeroX i _).mpr rfl⟩ : Y) =
        f i (φ i c, ⟨0, by simp⟩)) :
    ∃ F : X ≃ₜ Y, (∀ p : K, F p = (κ p : Y)) ∧
      (∀ i c t, F (e i (c, t)) = f i (φ i c, t)) ∧
      (∀ p : L, F.symm p = (κ.symm p : X)) ∧
      ∀ i d t, F.symm (f i (d, t)) = e i ((φ i).symm d, t) := by
  let g : ∀ i, C(C i × Ici (0 : ℝ), Y) := fun i ↦
    ⟨fun p ↦ f i (φ i p.1, p.2), (hf i).continuous.comp
      (((φ i).continuous.comp continuous_fst).prodMk continuous_snd)⟩
  let h : ∀ i, C(D i × Ici (0 : ℝ), X) := fun i ↦
    ⟨fun p ↦ e i ((φ i).symm p.1, p.2), (he i).continuous.comp
      (((φ i).symm.continuous.comp continuous_fst).prodMk continuous_snd)⟩
  have hforward (i : ι) (p : C i × Ici (0 : ℝ)) (hp : e i p ∈ K) :
      (κ ⟨e i p, hp⟩ : Y) = g i p := by
    have ht : p.2 = ⟨0, by simp⟩ := Subtype.ext ((hzeroX i p).mp hp)
    change (κ ⟨e i p, hp⟩ : Y) = f i (φ i p.1, p.2)
    have hb := hboundary i p.1
    simpa only [← ht, Prod.eta] using hb
  have hback (i : ι) (p : D i × Ici (0 : ℝ)) (hp : f i p ∈ L) :
      (κ.symm ⟨f i p, hp⟩ : X) = h i p := by
    have ht : p.2 = ⟨0, by simp⟩ := Subtype.ext ((hzeroY i p).mp hp)
    have hmem : e i ((φ i).symm p.1, p.2) ∈ K := (hzeroX i _).mpr (hzeroY i p |>.mp hp)
    have hb : (κ ⟨e i ((φ i).symm p.1, p.2), hmem⟩ : Y) = f i p := by
      have hb := hboundary i ((φ i).symm p.1)
      simpa only [Homeomorph.apply_symm_apply, ← ht] using hb
    have heq : κ ⟨e i ((φ i).symm p.1, p.2), hmem⟩ = ⟨f i p, hp⟩ := Subtype.ext hb
    exact congrArg Subtype.val ((congrArg κ.symm heq).symm.trans
      (κ.symm_apply_apply ⟨e i ((φ i).symm p.1, p.2), hmem⟩))
  obtain ⟨F, hFK, hFe⟩ := exists_continuousMap_of_cylindrical_cover e he hedis hK
    hcoverX ⟨fun p ↦ (κ p : Y), continuous_subtype_val.comp κ.continuous⟩ g hforward
  obtain ⟨G, hGL, hGf⟩ := exists_continuousMap_of_cylindrical_cover f hf hfdis hL
    hcoverY ⟨fun p ↦ (κ.symm p : X), continuous_subtype_val.comp κ.symm.continuous⟩ h hback
  have hleft (x : X) : G (F x) = x := by
    rcases hcoverX.symm.subset (mem_univ x) with hx | hx
    · rw [hFK ⟨x, hx⟩]
      change G (κ ⟨x, hx⟩) = x
      rw [hGL (κ ⟨x, hx⟩)]
      exact congrArg Subtype.val (κ.symm_apply_apply ⟨x, hx⟩)
    · obtain ⟨i, p, rfl⟩ := mem_iUnion.mp hx
      rw [hFe]
      change G (f i (φ i p.1, p.2)) = _
      rw [hGf]
      change e i ((φ i).symm (φ i p.1), p.2) = e i p
      rw [Homeomorph.symm_apply_apply]
  have hright (y : Y) : F (G y) = y := by
    rcases hcoverY.symm.subset (mem_univ y) with hy | hy
    · rw [hGL ⟨y, hy⟩]
      change F (κ.symm ⟨y, hy⟩) = y
      rw [hFK (κ.symm ⟨y, hy⟩)]
      exact congrArg Subtype.val (κ.apply_symm_apply ⟨y, hy⟩)
    · obtain ⟨i, p, rfl⟩ := mem_iUnion.mp hy
      rw [hGf]
      change F (e i ((φ i).symm p.1, p.2)) = _
      rw [hFe]
      change f i (φ i ((φ i).symm p.1), p.2) = f i p
      rw [Homeomorph.apply_symm_apply]
  exact ⟨⟨⟨F, G, hleft, hright⟩, F.continuous, G.continuous⟩,
    hFK, fun i c t ↦ hFe i (c, t), hGL, fun i d t ↦ hGf i (d, t)⟩

end DifferentialGeometry.Topology
