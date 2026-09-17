import DifferentialGeometry.Topology.Homeomorph.ChartExtension
import DifferentialGeometry.Topology.Manifold.ComplementarySectorRounding
import DifferentialGeometry.Topology.Manifold.SectorRoundingComparison
import DifferentialGeometry.Topology.Manifold.LocalDiffeomorph.PartialDiffeomorph
import DifferentialGeometry.Topology.Manifold.LocalDiffeomorph.Inverse

open Set Metric
open scoped ContDiff Manifold Topology

namespace OpenPartialHomeomorph

private theorem prod_smoothAbsCorner_image {P : Type*} [TopologicalSpace P]
    {ε : ℝ} (hε : 0 < ε) {U : Set (P × (ℝ × ℝ))}
    (hstrip : (univ : Set P) ×ˢ closedBall (0 : ℝ × ℝ) ε ⊆ U) :
    ((Homeomorph.refl P).prodCongr (Homeomorph.smoothAbsCorner hε)) '' U = U := by
  let F := (Homeomorph.refl P).prodCongr (Homeomorph.smoothAbsCorner hε)
  have hfix : EqOn F id Uᶜ := by
    intro p hp
    have hp' : p.2 ∉ closedBall (0 : ℝ × ℝ) ε := fun h => hp (hstrip ⟨mem_univ _, h⟩)
    exact Prod.ext rfl ((Homeomorph.smoothAbsCorner_eqOn_compl hε).1 hp')
  have hc := hfix.image_eq_self
  rw [F.image_compl] at hc
  exact compl_injective hc

theorem exists_homeomorph_smoothAbs_corner {X P : Type*}
    [TopologicalSpace X] [T2Space X] [TopologicalSpace P] [CompactSpace P]
    (e : OpenPartialHomeomorph X (P × (ℝ × ℝ))) {ε : ℝ} (hε : 0 < ε)
    (hstrip : (univ : Set P) ×ˢ closedBall (0 : ℝ × ℝ) ε ⊆ e.target) :
    ∃ H : X ≃ₜ X,
      (∀ x ∈ e.source, H x = e.symm ((e x).1, Homeomorph.smoothAbsCorner hε (e x).2)) ∧
      (∀ x ∈ e.source, H.symm x = e.symm ((e x).1, (Homeomorph.smoothAbsCorner hε).symm (e x).2)) ∧
      IsCompact (e.symm '' ((univ : Set P) ×ˢ closedBall (0 : ℝ × ℝ) ε)) ∧
      e.symm '' ((univ : Set P) ×ˢ closedBall (0 : ℝ × ℝ) ε) ⊆ e.source ∧
      EqOn H id (e.symm '' ((univ : Set P) ×ˢ closedBall (0 : ℝ × ℝ) ε))ᶜ ∧
      EqOn H.symm id (e.symm '' ((univ : Set P) ×ˢ closedBall (0 : ℝ × ℝ) ε))ᶜ ∧
      (∀ A : Set X, (∀ p ∈ e.target, e.symm p ∈ A ↔ 0 ≤ p.2.1 ∧ 0 ≤ p.2.2) →
        H '' A = e.smoothAbsQuadrantSet A ε) ∧
      (∀ A : Set X, (∀ p ∈ e.target, e.symm p ∈ A ↔ p.2.1 ≤ 0 ∨ p.2.2 ≤ 0) →
        H '' A = (A \ e.source) ∪ e.symm ''
          (e.target ∩ {p | p.2.1 + p.2.2 ≤ Real.smoothAbs ε (p.2.1 - p.2.2)})) := by
  let F := (Homeomorph.refl P).prodCongr (Homeomorph.smoothAbsCorner hε)
  let K := (univ : Set P) ×ˢ closedBall (0 : ℝ × ℝ) ε
  have hK : IsCompact K := isCompact_univ.prod (isCompact_closedBall 0 ε)
  have hfix : EqOn F id Kᶜ := by
    intro p hp
    have hp' : p.2 ∉ closedBall (0 : ℝ × ℝ) ε := fun h => hp ⟨mem_univ _, h⟩
    exact Prod.ext rfl ((Homeomorph.smoothAbsCorner_eqOn_compl hε).1 hp')
  have hFtarget : F '' e.target = e.target :=
    prod_smoothAbsCorner_image hε hstrip
  obtain ⟨H, hH, hHi, hC, hCs, hHfix, hHifix, hImage⟩ :=
    e.exists_homeomorph_extension F hK hstrip hfix
  have hsector (A : Set X) (S T : Set (ℝ × ℝ))
      (hraw : ∀ p ∈ e.target, e.symm p ∈ A ↔ p.2 ∈ S)
      (hST : ∀ p, Homeomorph.smoothAbsCorner hε p ∈ T ↔ p ∈ S) :
      F '' (e '' (A ∩ e.source)) = e.target ∩ {p | p.2 ∈ T} := by
    have hsource : e '' (A ∩ e.source) = e.target ∩ {p | p.2 ∈ S} := by
      ext p
      constructor
      · rintro ⟨x, hx, rfl⟩
        refine ⟨e.map_source hx.2, (hraw _ (e.map_source hx.2)).mp ?_⟩
        rw [e.left_inv hx.2]
        exact hx.1
      · intro hp
        exact ⟨e.symm p, ⟨(hraw p hp.1).mpr hp.2, e.map_target hp.1⟩, e.right_inv hp.1⟩
    have hshape : F '' {p : P × (ℝ × ℝ) | p.2 ∈ S} = {p | p.2 ∈ T} := by
      ext p
      constructor
      · rintro ⟨q, hq, rfl⟩
        exact (hST q.2).mpr hq
      · intro hp
        refine ⟨F.symm p, ?_, F.apply_symm_apply p⟩
        apply (hST _).mp
        change Homeomorph.smoothAbsCorner hε ((Homeomorph.smoothAbsCorner hε).symm p.2) ∈ T
        rw [(Homeomorph.smoothAbsCorner hε).apply_symm_apply]
        exact hp
    rw [hsource, image_inter F.injective, hFtarget, hshape]
  refine ⟨H, hH, hHi, hC, hCs, hHfix, hHifix, ?_, ?_⟩
  · intro A hraw
    rw [hImage, hsector A {p | 0 ≤ p.1 ∧ 0 ≤ p.2}
      {p | Real.smoothAbs ε (p.1 - p.2) ≤ p.1 + p.2} hraw
      (Homeomorph.smoothAbsCorner_mem_quadrant_iff hε)]
    rfl
  · intro A hraw
    rw [hImage, hsector A {p | p.1 ≤ 0 ∨ p.2 ≤ 0}
      {p | p.1 + p.2 ≤ Real.smoothAbs ε (p.1 - p.2)} hraw
      (Homeomorph.smoothAbsCorner_mem_complementary_quadrant_iff hε)]
    rfl

end OpenPartialHomeomorph

namespace DifferentialGeometry.Topology.Manifold

theorem isLocalDiffeomorphAt_prod_smoothAbsCorner
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {G : Type*} [TopologicalSpace G] {J : ModelWithCorners ℝ E G}
    {P : Type*} [TopologicalSpace P] [ChartedSpace G P]
    {ε : ℝ} (hε : 0 < ε) {p : P × (ℝ × ℝ)} (hp : p.2 ≠ 0) :
    IsLocalDiffeomorphAt (J.prod 𝓘(ℝ, ℝ × ℝ)) (J.prod 𝓘(ℝ, ℝ × ℝ)) ∞
      (fun z : P × (ℝ × ℝ) => (z.1, Homeomorph.smoothAbsCorner hε z.2)) p := by
  obtain ⟨φ, hφ, heq⟩ := Homeomorph.isLocalDiffeomorphAt_smoothAbsCorner hε hp
  let ψ := DifferentialGeometry.Topology.PartialDiffeomorph.prod
    (Diffeomorph.refl J P ∞).toPartialDiffeomorph φ
  exact ⟨ψ, ⟨mem_univ _, hφ⟩, fun z hz => Prod.ext rfl (heq hz.2)⟩

end DifferentialGeometry.Topology.Manifold

namespace PartialDiffeomorph

theorem exists_homeomorph_smoothAbs_corner
    {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    {G H : Type*} [TopologicalSpace G] [TopologicalSpace H]
    {I : ModelWithCorners ℝ E G} {J : ModelWithCorners ℝ F H}
    {M P : Type*} [TopologicalSpace M] [ChartedSpace G M] [T2Space M]
    [TopologicalSpace P] [ChartedSpace H P] [CompactSpace P]
    (e : PartialDiffeomorph I (J.prod 𝓘(ℝ, ℝ × ℝ)) M (P × (ℝ × ℝ)) ∞)
    {ε : ℝ} (hε : 0 < ε)
    (hstrip : (univ : Set P) ×ˢ closedBall (0 : ℝ × ℝ) ε ⊆ e.target) :
    ∃ H : M ≃ₜ M,
      (∀ x ∈ e.source, H x = e.symm ((e x).1, Homeomorph.smoothAbsCorner hε (e x).2)) ∧
      (∀ x ∈ e.source, H.symm x = e.symm ((e x).1, (Homeomorph.smoothAbsCorner hε).symm (e x).2)) ∧
      IsCompact (e.symm '' ((univ : Set P) ×ˢ closedBall (0 : ℝ × ℝ) ε)) ∧
      e.symm '' ((univ : Set P) ×ˢ closedBall (0 : ℝ × ℝ) ε) ⊆ e.source ∧
      EqOn H id (e.symm '' ((univ : Set P) ×ˢ closedBall (0 : ℝ × ℝ) ε))ᶜ ∧
      EqOn H.symm id (e.symm '' ((univ : Set P) ×ˢ closedBall (0 : ℝ × ℝ) ε))ᶜ ∧
      (∀ A : Set M, (∀ p ∈ e.target, e.symm p ∈ A ↔ 0 ≤ p.2.1 ∧ 0 ≤ p.2.2) →
        H '' A = e.toOpenPartialHomeomorph.smoothAbsQuadrantSet A ε) ∧
      (∀ A : Set M, (∀ p ∈ e.target, e.symm p ∈ A ↔ p.2.1 ≤ 0 ∨ p.2.2 ≤ 0) →
        H '' A = (A \ e.source) ∪ e.symm ''
          (e.target ∩ {p | p.2.1 + p.2.2 ≤ Real.smoothAbs ε (p.2.1 - p.2.2)})) ∧
      ∀ x : M, x ∉ e.symm '' ((univ : Set P) ×ˢ {(0 : ℝ × ℝ)}) →
        IsLocalDiffeomorphAt I I ∞ H x ∧ IsLocalDiffeomorphAt I I ∞ H.symm (H x) := by
  obtain ⟨H, hH, hHi, hC, hCs, hfix, hfixi, hquad, hreflex⟩ :=
    e.toOpenPartialHomeomorph.exists_homeomorph_smoothAbs_corner hε hstrip
  refine ⟨H, hH, hHi, hC, hCs, hfix, hfixi, hquad, hreflex, ?_⟩
  intro x hx
  have hloc : IsLocalDiffeomorphAt I I ∞ H x := by
    by_cases hxs : x ∈ e.source
    · have hp : (e x).2 ≠ 0 := by
        intro hh
        exact hx ⟨e x, ⟨mem_univ _, hh⟩, e.toPartialEquiv.left_inv hxs⟩
      have ht : ((e x).1, Homeomorph.smoothAbsCorner hε (e x).2) ∈ e.target := by
        rw [← OpenPartialHomeomorph.prod_smoothAbsCorner_image hε hstrip]
        exact ⟨e x, e.map_source hxs, rfl⟩
      have hl := ((e.isLocalDiffeomorphAt _ _ ∞ hxs).comp _ _
        (DifferentialGeometry.Topology.Manifold.isLocalDiffeomorphAt_prod_smoothAbsCorner hε hp)).comp
        _ _ (e.symm.isLocalDiffeomorphAt _ _ ∞ ht)
      apply DifferentialGeometry.IsLocalDiffeomorphAt.of_eventuallyEq (hg := hl)
      filter_upwards [e.open_source.mem_nhds hxs] with y hy
      exact hH y hy
    · have hxC : x ∉ e.symm '' ((univ : Set P) ×ˢ closedBall (0 : ℝ × ℝ) ε) :=
        fun h => hxs (hCs h)
      apply DifferentialGeometry.IsLocalDiffeomorphAt.of_eventuallyEq
        (hg := (Diffeomorph.refl I M ∞).isLocalDiffeomorph x)
      filter_upwards [hC.isClosed.isOpen_compl.mem_nhds hxC] with y hy
      exact hfix hy
  exact ⟨hloc, H.isLocalDiffeomorphAt_symm hloc⟩

end PartialDiffeomorph
