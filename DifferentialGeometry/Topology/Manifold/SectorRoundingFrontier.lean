import DifferentialGeometry.Topology.Manifold.SectorRoundingComparison
import DifferentialGeometry.Topology.Diffeomorph.SmoothMax

open Set

namespace Real.smoothAbs

private theorem rounded_quadrant_topology {P : Type*} [TopologicalSpace P]
    (ε : ℝ) :
    let Q : Set (P × (ℝ × ℝ)) :=
      {p | Real.smoothAbs ε (p.2.1 - p.2.2) ≤ p.2.1 + p.2.2}
    closure (interior Q) = Q ∧
      frontier Q = {p | Real.smoothAbs ε (p.2.1 - p.2.2) = p.2.1 + p.2.2} := by
  let Q : Set (P × (ℝ × ℝ)) :=
    {p | Real.smoothAbs ε (p.2.1 - p.2.2) ≤ p.2.1 + p.2.2}
  let H : (P × (ℝ × ℝ)) ≃ₜ (P × (ℝ × ℝ)) :=
    (Homeomorph.refl P).prodCongr
      ((Homeomorph.prodComm ℝ ℝ).trans
        ((ContinuousLinearEquiv.neg ℝ : (ℝ × ℝ) ≃L[ℝ] (ℝ × ℝ)).toHomeomorph.trans
          (Diffeomorph.smoothMax ε).toHomeomorph))
  let B : Set (P × (ℝ × ℝ)) := univ ×ˢ (univ ×ˢ Iic (0 : ℝ))
  have hH (p : P × (ℝ × ℝ)) :
      H p = (p.1, (-p.2.2 - -p.2.1, Real.smoothMax ε (-p.2.2) (-p.2.1))) := rfl
  have him : H.toOpenPartialHomeomorph.IsImage Q B := by
    intro p _
    change (H p ∈ B) ↔ p ∈ Q
    rw [hH]
    simp only [B, mem_prod, mem_univ, true_and, mem_Iic]
    change Real.smoothMax ε (-p.2.2) (-p.2.1) ≤ 0 ↔ _
    rw [Real.smoothMax, show -p.2.2 - -p.2.1 = p.2.1 - p.2.2 by ring]
    change _ ↔ Real.smoothAbs ε (p.2.1 - p.2.2) ≤ p.2.1 + p.2.2
    constructor <;> intro h <;> linarith
  have hB : closure (interior B) = B := by
    simp only [B, interior_prod_eq, interior_univ, interior_Iic, closure_prod_eq,
      closure_univ, closure_Iio]
  refine ⟨?_, ?_⟩
  · ext p
    exact ((him.interior.closure (mem_univ p)).symm.trans
      (by rw [hB])).trans (him (mem_univ p))
  · ext p
    rw [← him.frontier (mem_univ p)]
    change H p ∈ frontier B ↔ _
    rw [hH]
    simp only [B, frontier_univ_prod_eq, frontier_Iic, mem_prod, mem_univ,
      true_and, mem_singleton_iff]
    rw [Real.smoothMax, show -p.2.2 - -p.2.1 = p.2.1 - p.2.2 by ring]
    change _ ↔ Real.smoothAbs ε (p.2.1 - p.2.2) = p.2.1 + p.2.2
    constructor <;> intro h <;> linarith

theorem closure_interior_quadrant {P : Type*} [TopologicalSpace P]
    (ε : ℝ) :
    closure (interior {p : P × (ℝ × ℝ) |
      Real.smoothAbs ε (p.2.1 - p.2.2) ≤ p.2.1 + p.2.2}) =
      {p | Real.smoothAbs ε (p.2.1 - p.2.2) ≤ p.2.1 + p.2.2} :=
  (rounded_quadrant_topology ε).1

theorem frontier_quadrant {P : Type*} [TopologicalSpace P]
    (ε : ℝ) :
    frontier {p : P × (ℝ × ℝ) |
      Real.smoothAbs ε (p.2.1 - p.2.2) ≤ p.2.1 + p.2.2} =
      {p | Real.smoothAbs ε (p.2.1 - p.2.2) = p.2.1 + p.2.2} :=
  (rounded_quadrant_topology ε).2

theorem interior_quadrant {P : Type*} [TopologicalSpace P]
    (ε : ℝ) :
    interior {p : P × (ℝ × ℝ) |
      Real.smoothAbs ε (p.2.1 - p.2.2) ≤ p.2.1 + p.2.2} =
      {p | Real.smoothAbs ε (p.2.1 - p.2.2) < p.2.1 + p.2.2} := by
  rw [← self_sdiff_frontier, frontier_quadrant ε]
  ext p
  change (Real.smoothAbs ε (p.2.1 - p.2.2) ≤ p.2.1 + p.2.2 ∧
    ¬ Real.smoothAbs ε (p.2.1 - p.2.2) = p.2.1 + p.2.2) ↔
      Real.smoothAbs ε (p.2.1 - p.2.2) < p.2.1 + p.2.2
  exact lt_iff_le_and_ne.symm

private theorem complementary_quadrant_eq_compl_interior {P : Type*} [TopologicalSpace P]
    (ε : ℝ) :
    {p : P × (ℝ × ℝ) | p.2.1 + p.2.2 ≤ Real.smoothAbs ε (p.2.1 - p.2.2)} =
      (interior {p | Real.smoothAbs ε (p.2.1 - p.2.2) ≤ p.2.1 + p.2.2})ᶜ := by
  rw [interior_quadrant ε]
  ext p
  change p.2.1 + p.2.2 ≤ Real.smoothAbs ε (p.2.1 - p.2.2) ↔
    ¬ Real.smoothAbs ε (p.2.1 - p.2.2) < p.2.1 + p.2.2
  exact not_lt.symm

theorem closure_interior_complementary_quadrant {P : Type*} [TopologicalSpace P]
    (ε : ℝ) :
    closure (interior {p : P × (ℝ × ℝ) |
      p.2.1 + p.2.2 ≤ Real.smoothAbs ε (p.2.1 - p.2.2)}) =
      {p | p.2.1 + p.2.2 ≤ Real.smoothAbs ε (p.2.1 - p.2.2)} := by
  rw [complementary_quadrant_eq_compl_interior ε, interior_compl,
    closure_interior_quadrant ε, closure_compl]

theorem frontier_complementary_quadrant {P : Type*} [TopologicalSpace P]
    (ε : ℝ) :
    frontier {p : P × (ℝ × ℝ) |
      p.2.1 + p.2.2 ≤ Real.smoothAbs ε (p.2.1 - p.2.2)} =
      {p | Real.smoothAbs ε (p.2.1 - p.2.2) = p.2.1 + p.2.2} := by
  rw [complementary_quadrant_eq_compl_interior ε, frontier_compl,
    frontier, interior_interior, closure_interior_quadrant ε]
  have hclosed : IsClosed {p : P × (ℝ × ℝ) |
      Real.smoothAbs ε (p.2.1 - p.2.2) ≤ p.2.1 + p.2.2} :=
    isClosed_le ((Real.smoothAbs.contDiff ε).continuous.comp (continuous_snd.fst.sub continuous_snd.snd))
      (continuous_snd.fst.add continuous_snd.snd)
  rw [← hclosed.frontier_eq, frontier_quadrant ε]

end Real.smoothAbs

namespace OpenPartialHomeomorph

private theorem smoothAbsQuadrantSet_locality
    {X P : Type*} [TopologicalSpace X] [T2Space X] [TopologicalSpace P] [CompactSpace P]
    (e : OpenPartialHomeomorph X (P × (ℝ × ℝ))) {A : Set X} {ε : ℝ} (hε : 0 < ε)
    (hraw : ∀ p ∈ e.target, e.symm p ∈ A ↔ 0 ≤ p.2.1 ∧ 0 ≤ p.2.2)
    (hstrip : {p : P × (ℝ × ℝ) | 0 ≤ p.2.1 ∧ 0 ≤ p.2.2 ∧ p.2.1 + p.2.2 ≤ ε} ⊆
      e.target) :
    e.smoothAbsQuadrantSet A ε ⊆ A ∧ ∃ K : Set X, ∃ hK : IsCompact K,
      K ⊆ e.source ∧ (ofSet Kᶜ hK.isClosed.isOpen_compl).IsImage
        (e.smoothAbsQuadrantSet A ε) A := by
  let C := e.smoothAbsQuadrantSet A ε
  let Q : Set (P × (ℝ × ℝ)) :=
    {p | Real.smoothAbs ε (p.2.1 - p.2.2) ≤ p.2.1 + p.2.2}
  let T : Set (P × (ℝ × ℝ)) :=
    {p | 0 ≤ p.2.1 ∧ 0 ≤ p.2.2 ∧ p.2.1 + p.2.2 ≤ ε}
  let K := e.symm '' T
  have hT : IsCompact T := by
    have hc := (isCompact_univ (X := P)).prod
      ((isCompact_Icc (a := (0 : ℝ)) (b := ε)).prod
        (isCompact_Icc (a := (0 : ℝ)) (b := ε)))
    have ht : IsClosed T := (isClosed_le continuous_const continuous_snd.fst).inter
      ((isClosed_le continuous_const continuous_snd.snd).inter
        (isClosed_le (continuous_snd.fst.add continuous_snd.snd) continuous_const))
    apply hc.of_isClosed_subset ht
    intro p hp
    exact ⟨mem_univ _, ⟨hp.1, by linarith [hp.2.1, hp.2.2]⟩,
      ⟨hp.2.1, by linarith [hp.1, hp.2.2]⟩⟩
  have hK : IsCompact K := hT.image_of_continuousOn (e.continuousOn_symm.mono hstrip)
  have hKs : K ⊆ e.source := by
    rintro _ ⟨p, hp, rfl⟩
    exact e.map_target (hstrip hp)
  have him : e.IsImage C Q := by
    intro x hx
    exact (e.mem_smoothAbsQuadrantSet_iff A ε hx).symm
  have hsub : C ⊆ A := by
    intro x hx
    by_cases hxs : x ∈ e.source
    · have hh := (him hxs).mpr hx
      have hl := (Real.smoothAbs.sub_abs_mem_Icc hε ((e x).2.1 - (e x).2.2)).1
      have hn := neg_abs_le ((e x).2.1 - (e x).2.2)
      have hp := le_abs_self ((e x).2.1 - (e x).2.2)
      have hq : 0 ≤ (e x).2.1 ∧ 0 ≤ (e x).2.2 := by
        change Real.smoothAbs ε ((e x).2.1 - (e x).2.2) ≤ (e x).2.1 + (e x).2.2 at hh
        constructor <;> linarith
      have ha := (hraw (e x) (e.map_source hxs)).mpr hq
      rwa [e.left_inv hxs] at ha
    · rcases hx with hx | ⟨p, hp, rfl⟩
      · exact hx.1
      · exact False.elim (hxs (e.map_target hp.1))
  have hout {x : X} (hxK : x ∉ K) : x ∈ C ↔ x ∈ A := by
    refine ⟨fun hx => hsub hx, ?_⟩
    intro hx
    by_cases hxs : x ∈ e.source
    · apply (him hxs).mp
      have hq : 0 ≤ (e x).2.1 ∧ 0 ≤ (e x).2.2 := by
        apply (hraw (e x) (e.map_source hxs)).mp
        rwa [e.left_inv hxs]
      have hs : ε ≤ (e x).2.1 + (e x).2.2 := by
        by_contra hn
        exact hxK ⟨e x, ⟨hq.1, hq.2, (lt_of_not_ge hn).le⟩, e.left_inv hxs⟩
      change Real.smoothAbs ε ((e x).2.1 - (e x).2.2) ≤ (e x).2.1 + (e x).2.2
      calc
        Real.smoothAbs ε ((e x).2.1 - (e x).2.2) =
            Real.smoothAbs ε |(e x).2.1 - (e x).2.2| := (Real.smoothAbs.abs hε.ne' _).symm
        _ ≤ Real.smoothAbs ε ((e x).2.1 + (e x).2.2) := by
          apply (Real.smoothAbs.strictMonoOn_Ici hε).monotoneOn
            (show |(e x).2.1 - (e x).2.2| ∈ Ici 0 from abs_nonneg ((e x).2.1 - (e x).2.2))
            (show (e x).2.1 + (e x).2.2 ∈ Ici 0 from add_nonneg hq.1 hq.2)
          rw [abs_le]
          constructor <;> linarith [hq.1, hq.2]
        _ = (e x).2.1 + (e x).2.2 := Real.smoothAbs.eq_self_of_le hε hs
    · exact Or.inl ⟨hx, hxs⟩
  have haway : (ofSet Kᶜ hK.isClosed.isOpen_compl).IsImage C A := by
    intro x hx
    exact (hout hx).symm
  exact ⟨hsub, K, hK, hKs, haway⟩

theorem isClosed_smoothAbsQuadrantSet
    {X P : Type*} [TopologicalSpace X] [T2Space X] [TopologicalSpace P] [CompactSpace P]
    (e : OpenPartialHomeomorph X (P × (ℝ × ℝ))) {A : Set X} {ε : ℝ} (hε : 0 < ε)
    (hraw : ∀ p ∈ e.target, e.symm p ∈ A ↔ 0 ≤ p.2.1 ∧ 0 ≤ p.2.2)
    (hstrip : {p : P × (ℝ × ℝ) | 0 ≤ p.2.1 ∧ 0 ≤ p.2.2 ∧ p.2.1 + p.2.2 ≤ ε} ⊆
      e.target) (hA : IsClosed A) :
    IsClosed (e.smoothAbsQuadrantSet A ε) := by
  let C := e.smoothAbsQuadrantSet A ε
  let Q : Set (P × (ℝ × ℝ)) :=
    {p | Real.smoothAbs ε (p.2.1 - p.2.2) ≤ p.2.1 + p.2.2}
  obtain ⟨hsub, K, hK, hKs, haway⟩ := e.smoothAbsQuadrantSet_locality hε hraw hstrip
  have him : e.IsImage C Q := by
    intro x hx
    exact (e.mem_smoothAbsQuadrantSet_iff A ε hx).symm
  apply closure_subset_iff_isClosed.mp
  intro x hx
  by_cases hxs : x ∈ e.source
  · apply (him hxs).mp
    have hq := (him.closure hxs).mpr hx
    have hQ : IsClosed Q := isClosed_le
      ((Real.smoothAbs.contDiff ε).continuous.comp (continuous_snd.fst.sub continuous_snd.snd))
      (continuous_snd.fst.add continuous_snd.snd)
    rwa [hQ.closure_eq] at hq
  · have hxK : x ∉ K := fun h => hxs (hKs h)
    have ha := (haway.closure hxK).mpr hx
    change x ∈ closure A at ha
    exact (haway hxK).mp (hA.closure_eq ▸ ha)

theorem isCompact_smoothAbsQuadrantSet
    {X P : Type*} [TopologicalSpace X] [T2Space X] [TopologicalSpace P] [CompactSpace P]
    (e : OpenPartialHomeomorph X (P × (ℝ × ℝ))) {A : Set X} {ε : ℝ} (hε : 0 < ε)
    (hraw : ∀ p ∈ e.target, e.symm p ∈ A ↔ 0 ≤ p.2.1 ∧ 0 ≤ p.2.2)
    (hstrip : {p : P × (ℝ × ℝ) | 0 ≤ p.2.1 ∧ 0 ≤ p.2.2 ∧ p.2.1 + p.2.2 ≤ ε} ⊆
      e.target) (hA : IsCompact A) :
    IsCompact (e.smoothAbsQuadrantSet A ε) := by
  exact hA.of_isClosed_subset (e.isClosed_smoothAbsQuadrantSet hε hraw hstrip hA.isClosed)
    (e.smoothAbsQuadrantSet_locality hε hraw hstrip).1

theorem closure_interior_smoothAbsQuadrantSet
    {X P : Type*} [TopologicalSpace X] [T2Space X] [TopologicalSpace P] [CompactSpace P]
    (e : OpenPartialHomeomorph X (P × (ℝ × ℝ))) {A : Set X} {ε : ℝ} (hε : 0 < ε)
    (hraw : ∀ p ∈ e.target, e.symm p ∈ A ↔ 0 ≤ p.2.1 ∧ 0 ≤ p.2.2)
    (hstrip : {p : P × (ℝ × ℝ) | 0 ≤ p.2.1 ∧ 0 ≤ p.2.2 ∧ p.2.1 + p.2.2 ≤ ε} ⊆
      e.target) (hAreg : closure (interior A) = A) :
    closure (interior (e.smoothAbsQuadrantSet A ε)) = e.smoothAbsQuadrantSet A ε := by
  let C := e.smoothAbsQuadrantSet A ε
  let Q : Set (P × (ℝ × ℝ)) :=
    {p | Real.smoothAbs ε (p.2.1 - p.2.2) ≤ p.2.1 + p.2.2}
  obtain ⟨hsub, K, hK, hKs, haway⟩ := e.smoothAbsQuadrantSet_locality hε hraw hstrip
  have him : e.IsImage C Q := by
    intro x hx
    exact (e.mem_smoothAbsQuadrantSet_iff A ε hx).symm
  have hA : IsClosed A := hAreg ▸ isClosed_closure
  have hC := e.isClosed_smoothAbsQuadrantSet hε hraw hstrip hA
  have hQreg := Real.smoothAbs.closure_interior_quadrant (P := P) ε
  apply Subset.antisymm hC.closure_interior_subset
  intro x hx
  by_cases hxs : x ∈ e.source
  · apply (him.interior.closure hxs).mp
    rw [hQreg]
    exact (him hxs).mpr hx
  · have hxK : x ∉ K := fun h => hxs (hKs h)
    apply (haway.interior.closure hxK).mp
    change x ∈ closure (interior A)
    rw [hAreg]
    exact hsub hx

theorem frontier_smoothAbsQuadrantSet
    {X P : Type*} [TopologicalSpace X] [T2Space X] [TopologicalSpace P] [CompactSpace P]
    (e : OpenPartialHomeomorph X (P × (ℝ × ℝ))) {A : Set X} {ε : ℝ} (hε : 0 < ε)
    (hraw : ∀ p ∈ e.target, e.symm p ∈ A ↔ 0 ≤ p.2.1 ∧ 0 ≤ p.2.2)
    (hstrip : {p : P × (ℝ × ℝ) | 0 ≤ p.2.1 ∧ 0 ≤ p.2.2 ∧ p.2.1 + p.2.2 ≤ ε} ⊆
      e.target) :
    frontier (e.smoothAbsQuadrantSet A ε) = (frontier A \ e.source) ∪
      e.symm '' (e.target ∩
        {p | Real.smoothAbs ε (p.2.1 - p.2.2) = p.2.1 + p.2.2}) := by
  let C := e.smoothAbsQuadrantSet A ε
  let Q : Set (P × (ℝ × ℝ)) :=
    {p | Real.smoothAbs ε (p.2.1 - p.2.2) ≤ p.2.1 + p.2.2}
  obtain ⟨hsub, K, hK, hKs, haway⟩ := e.smoothAbsQuadrantSet_locality hε hraw hstrip
  have him : e.IsImage C Q := by
    intro x hx
    exact (e.mem_smoothAbsQuadrantSet_iff A ε hx).symm
  have hQfront := Real.smoothAbs.frontier_quadrant (P := P) ε
  ext x
  by_cases hxs : x ∈ e.source
  · have hi := him.frontier hxs
    rw [hQfront] at hi
    constructor
    · intro hx
      exact Or.inr ⟨e x, ⟨e.map_source hxs, hi.mpr hx⟩, e.left_inv hxs⟩
    · rintro (hx | ⟨p, hp, hpx⟩)
      · exact False.elim (hx.2 hxs)
      · apply hi.mp
        have he : e x = p := by rw [← hpx, e.right_inv hp.1]
        simpa only [he] using hp.2
  · have hxK : x ∉ K := fun h => hxs (hKs h)
    have hi := haway.frontier hxK
    change (x ∈ frontier A ↔ x ∈ frontier C) at hi
    constructor
    · intro hx
      exact Or.inl ⟨hi.mpr hx, hxs⟩
    · rintro (hx | ⟨p, hp, rfl⟩)
      · exact hi.mp hx.1
      · exact False.elim (hxs (e.map_target hp.1))

end OpenPartialHomeomorph
