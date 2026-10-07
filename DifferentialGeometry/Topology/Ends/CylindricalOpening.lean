import DifferentialGeometry.Topology.Manifold.IntervalOpening
import DifferentialGeometry.Topology.Manifold.PartialDiffeomorph.Gluing
import DifferentialGeometry.Topology.Manifold.PartialDiffeomorph
import DifferentialGeometry.Topology.Ends.CylindricalCoreBoundary
import DifferentialGeometry.Topology.Compactness.ProductChartThickening
import Mathlib.Geometry.Manifold.Algebra.LieGroup

noncomputable section

open Set
open scoped Manifold ContDiff

namespace DifferentialGeometry.Topology

private theorem partialDiffeomorph_of_intervalDiffeomorph {R : ℝ} (hR : 0 < R)
    (θ : Diffeomorph 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ)
      (⟨Ioo 0 R, isOpen_Ioo⟩ : TopologicalSpace.Opens ℝ)
      (⟨Ioi 0, isOpen_Ioi⟩ : TopologicalSpace.Opens ℝ) ∞) :
    ∃ σ : _root_.PartialDiffeomorph 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) ℝ ℝ ∞,
      σ.source = Ioo 0 R ∧ σ.target = Ioi 0 ∧
      (∀ x (hx : x ∈ Ioo 0 R), σ x = (θ ⟨x, hx⟩ : ℝ)) ∧
      ∀ y (hy : y ∈ Ioi 0), σ.symm y = (θ.symm ⟨y, hy⟩ : ℝ) := by
  let U : TopologicalSpace.Opens ℝ := ⟨Ioo 0 R, isOpen_Ioo⟩
  let V : TopologicalSpace.Opens ℝ := ⟨Ioi 0, isOpen_Ioi⟩
  have hU : Nonempty U := ⟨⟨R / 2, by constructor <;> linarith⟩⟩
  have hV : Nonempty V := ⟨⟨1, by change (0 : ℝ) < 1; norm_num⟩⟩
  let A := PartialDiffeomorph.subtypeVal (I := 𝓘(ℝ, ℝ)) U hU
  let B := PartialDiffeomorph.subtypeVal (I := 𝓘(ℝ, ℝ)) V hV
  have hAt : A.target = (U : Set ℝ) := U.openPartialHomeomorphSubtypeCoe_target hU
  have hBt : B.target = (V : Set ℝ) := V.openPartialHomeomorphSubtypeCoe_target hV
  let σ := A.symm.trans (θ.toPartialDiffeomorph.trans B)
  refine ⟨σ, ?_, ?_, ?_, ?_⟩
  · ext x
    change (x ∈ A.target ∧ (True ∧ True)) ↔ x ∈ Ioo 0 R
    rw [hAt]
    simp only [and_self, and_true]
    rfl
  · ext y
    change ((y ∈ B.target ∧ True) ∧ True) ↔ y ∈ Ioi 0
    rw [hBt]
    simp only [and_true]
    rfl
  · intro x hx
    have ha : A.symm x = (⟨x, hx⟩ : U) := by
      apply Subtype.ext
      exact A.right_inv' (hAt.symm ▸ hx)
    change ((θ (A.symm x) : V) : ℝ) = _
    rw [ha]
  · intro y hy
    have hb : B.symm y = (⟨y, hy⟩ : V) := by
      apply Subtype.ext
      exact B.right_inv' (hBt.symm ▸ hy)
    change ((θ.symm (B.symm y) : U) : ℝ) = _
    rw [hb]


variable {E H M F G C : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace H] [TopologicalSpace M] [ChartedSpace H M]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [TopologicalSpace G]
  [TopologicalSpace C] [ChartedSpace G C]
  {I : ModelWithCorners ℝ E H} {J : ModelWithCorners ℝ F G}

private theorem exists_conjugate_interval_expansion
    (χ : _root_.PartialDiffeomorph I (J.prod 𝓘(ℝ, ℝ)) M (C × ℝ) ∞)
    (hχ : χ.target = {p | 0 < p.2})
    (σ : _root_.PartialDiffeomorph 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) ℝ ℝ ∞)
    {R : ℝ} (hs : σ.source = Ioo 0 R) (ht : σ.target = Ioi 0) :
    ∃ Φ : _root_.PartialDiffeomorph I I M M ∞,
      Φ.source = {x | x ∈ χ.source ∧ (χ x).2 ∈ Ioo 0 R} ∧
      Φ.target = χ.source ∧
      (∀ x, Φ x = χ.symm ((χ x).1, σ (χ x).2)) ∧
      ∀ x, Φ.symm x = χ.symm ((χ x).1, σ.symm (χ x).2) := by
  let P := PartialDiffeomorph.prod (Diffeomorph.refl J C ∞).toPartialDiffeomorph σ
  let Φ := χ.trans (P.trans χ.symm)
  refine ⟨Φ, ?_, ?_, fun _ => rfl, fun _ => rfl⟩
  · ext x
    change (x ∈ χ.source ∧ (True ∧ (χ x).2 ∈ σ.source) ∧
      ((χ x).1, σ (χ x).2) ∈ χ.target) ↔ _
    constructor
    · rintro ⟨hx, ⟨_, hσ⟩, _⟩
      exact ⟨hx, hs ▸ hσ⟩
    · rintro ⟨hx, hσ⟩
      have hm : (χ x).2 ∈ σ.source := hs.symm ▸ hσ
      refine ⟨hx, ⟨trivial, hm⟩, ?_⟩
      rw [hχ]
      have hp := σ.map_source' hm
      rw [ht] at hp
      exact hp
  · ext x
    change ((x ∈ χ.source ∧ (True ∧ (χ x).2 ∈ σ.target)) ∧
      ((χ x).1, σ.symm (χ x).2) ∈ χ.target) ↔ x ∈ χ.source
    constructor
    · exact fun hx => hx.1.1
    · intro hx
      have hp := χ.map_source' hx
      rw [hχ] at hp
      have hm : (χ x).2 ∈ σ.target := ht.symm ▸ hp
      refine ⟨⟨hx, trivial, hm⟩, ?_⟩
      rw [hχ]
      exact (show σ.symm (χ x).2 ∈ Ioo 0 R from hs ▸ σ.map_target' hm).1


private theorem cylindrical_opening_cover
    {ι X : Type*} [Finite ι] [TopologicalSpace X]
    {D : ι → Type*} [∀ i, TopologicalSpace (D i)]
    (e : ∀ i, D i × Ici (0 : ℝ) → X)
    (he : ∀ i, _root_.Topology.IsClosedEmbedding (e i))
    (hdis : Pairwise fun i j => Disjoint (range (e i)) (range (e j)))
    (R : ι → ℝ) (hR : ∀ i, 0 < R i) :
    ((⋃ i, e i '' {p | 0 < p.2.val ∧ p.2.val < R i}) ∪
      interior (cylindricalCore e (fun i => R i / 2))) = interior (cylindricalCore e R) ∧
    ((⋃ i, e i '' {p | 0 < p.2.val}) ∪
      interior (cylindricalCore e (fun i => R i / 2))) = univ := by
  constructor
  · apply Subset.antisymm
    · rintro x (hx | hx)
      · obtain ⟨i, p, hp, rfl⟩ := mem_iUnion.mp hx
        exact (mem_interior_cylindricalCore_image_iff e he hdis R i p).mpr hp.2
      · exact cylindricalCore_subset_interior_of_lt e he (fun i => R i / 2) R
          (fun i => by linarith [hR i]) (interior_subset hx)
    · intro x hx
      by_cases hi : x ∈ interior (cylindricalCore e (fun i => R i / 2))
      · exact Or.inr hi
      · rw [interior_cylindricalCore e he] at hi
        obtain ⟨i, p, hp, rfl⟩ := mem_iUnion.mp (not_not.mp hi)
        change R i / 2 ≤ p.2.val at hp
        have ht := (mem_interior_cylindricalCore_image_iff e he hdis R i p).mp hx
        exact Or.inl (mem_iUnion.mpr ⟨i, p, ⟨by linarith [hR i], ht⟩, rfl⟩)
  · apply eq_univ_of_forall
    intro x
    by_cases hi : x ∈ interior (cylindricalCore e (fun i => R i / 2))
    · exact Or.inr hi
    · rw [interior_cylindricalCore e he] at hi
      obtain ⟨i, p, hp, rfl⟩ := mem_iUnion.mp (not_not.mp hi)
      change R i / 2 ≤ p.2.val at hp
      exact Or.inl (mem_iUnion.mpr ⟨i, p, (div_pos (hR i) (by norm_num : (0 : ℝ) < 2)).trans_le hp, rfl⟩)


private theorem exists_partialDiffeomorph_cylindricalCore
    {ι : Type*} [Finite ι] {D : ι → Type*}
    [∀ i, TopologicalSpace (D i)] [∀ i, ChartedSpace G (D i)]
    (e : ∀ i, D i × Ici (0 : ℝ) → M)
    (he : ∀ i, _root_.Topology.IsClosedEmbedding (e i))
    (hdis : Pairwise fun i j => Disjoint (range (e i)) (range (e j)))
    (χ : ∀ i, _root_.PartialDiffeomorph I (J.prod 𝓘(ℝ, ℝ)) M (D i × ℝ) ∞)
    (hχs : ∀ i, (χ i).source = e i '' {p | 0 < p.2.val})
    (hχt : ∀ i, (χ i).target = {p | 0 < p.2})
    (hχe : ∀ i (p : D i × Ici (0 : ℝ)), 0 < p.2.val → χ i (e i p) = (p.1, p.2.val))
    (R : ι → ℝ) (hR : ∀ i, 0 < R i) :
    ∃ Ψ : _root_.PartialDiffeomorph I I M M ∞,
      Ψ.source = interior (cylindricalCore e R) ∧ Ψ.target = univ ∧
      EqOn Ψ id (cylindricalCore e (fun i => R i / 2)) ∧
      EqOn Ψ.symm id (cylindricalCore e (fun i => R i / 2)) := by
  classical
  have ht (i : ι) := DifferentialGeometry.Manifold.exists_diffeomorph_Ioo_Ioi_eq_self
    (a := 0) (b := R i / 2) (c := R i) (by linarith [hR i]) (by linarith [hR i])
  choose θ hθmono hθfix hθinv using ht
  choose σ hσs hσt hσ hσinv using fun i => partialDiffeomorph_of_intervalDiffeomorph (hR i) (θ i)
  choose Φ hΦs hΦt hΦ hΦinv using fun i =>
    exists_conjugate_interval_expansion (χ i) (hχt i) (σ i) (hσs i) (hσt i)
  have hΦs' (i : ι) : (Φ i).source = e i '' {p | 0 < p.2.val ∧ p.2.val < R i} := by
    rw [hΦs i]
    ext x
    constructor
    · rintro ⟨hx, ht⟩
      obtain ⟨p, hp, rfl⟩ := (hχs i) ▸ hx
      rw [hχe i p hp] at ht
      exact ⟨p, ⟨hp, ht.2⟩, rfl⟩
    · rintro ⟨p, hp, rfl⟩
      refine ⟨(hχs i).symm ▸ ⟨p, hp.1, rfl⟩, ?_⟩
      rw [hχe i p hp.1]
      exact hp
  have hΦt' (i : ι) : (Φ i).target = e i '' {p | 0 < p.2.val} :=
    (hΦt i).trans (hχs i)
  have hsRange (i : ι) : (Φ i).source ⊆ range (e i) := by
    rw [hΦs' i]
    exact image_subset_range _ _
  have htRange (i : ι) : (Φ i).target ⊆ range (e i) := by
    rw [hΦt' i]
    exact image_subset_range _ _
  obtain ⟨P, hPs, hPt, hP, _⟩ := DifferentialGeometry.PartialDiffeomorph.exists_disjoint_gluing Φ
    (fun i j hij => (hdis hij).mono (hsRange i) (hsRange j))
    (fun i j hij => (hdis hij).mono (htRange i) (htRange j))
  let V := interior (cylindricalCore e (fun i => R i / 2))
  have hheight (i : ι) (x : M) (hx : x ∈ (χ i).source)
      (hc : x ∈ cylindricalCore e (fun i => R i / 2)) : (χ i x).2 ≤ R i / 2 := by
    obtain ⟨p, hp, rfl⟩ := (hχs i) ▸ hx
    rw [hχe i p hp]
    exact (mem_cylindricalCore_image_iff e (fun j => (he j).injective)
      hdis (fun j => R j / 2) i p).mp hc
  have hlocalfix (i : ι) (x : M) (hx : x ∈ (Φ i).source)
      (hh : (χ i x).2 ≤ R i / 2) : Φ i x = x := by
    have hx' := hx
    rw [hΦs i] at hx'
    have hσfix := (hσ i (χ i x).2 hx'.2).trans (hθfix i _ hh)
    rw [hΦ i x, hσfix]
    exact (χ i).left_inv' hx'.1
  have hinter : P.source ∩ V = P.target ∩ V := by
    ext x
    constructor
    · rintro ⟨hx, hV⟩
      obtain ⟨i, hi⟩ := mem_iUnion.mp (hPs ▸ hx)
      have hχx : x ∈ (χ i).source := (show x ∈ (χ i).source ∧ _ from hΦs i ▸ hi).1
      exact ⟨hPt.symm ▸ mem_iUnion.mpr ⟨i, (hΦt i).symm ▸ hχx⟩, hV⟩
    · rintro ⟨hx, hV⟩
      obtain ⟨i, hi⟩ := mem_iUnion.mp (hPt ▸ hx)
      have hχx : x ∈ (χ i).source := hΦt i ▸ hi
      have hp := (χ i).map_source' hχx
      rw [hχt i] at hp
      have hh := hheight i x hχx (interior_subset hV)
      have hxΦ : x ∈ (Φ i).source := by
        rw [hΦs i]
        exact ⟨hχx, hp, by linarith [hR i]⟩
      exact ⟨hPs.symm ▸ mem_iUnion.mpr ⟨i, hxΦ⟩, hV⟩
  have hfix : EqOn P id (P.source ∩ V) := by
    rintro x ⟨hx, hV⟩
    obtain ⟨i, hi⟩ := mem_iUnion.mp (hPs ▸ hx)
    have hχx : x ∈ (χ i).source := (show x ∈ (χ i).source ∧ _ from hΦs i ▸ hi).1
    exact (hP i hi).trans (hlocalfix i x hi (hheight i x hχx (interior_subset hV)))
  obtain ⟨Ψ, hΨs, hΨt, hΨP, hΨV, _, _⟩ :=
    DifferentialGeometry.PartialDiffeomorph.exists_extension_by_identity P isOpen_interior hinter hfix
  have hcover := cylindrical_opening_cover e he hdis R hR
  have hs : Ψ.source = interior (cylindricalCore e R) := by
    rw [hΨs, hPs]
    simp only [hΦs']
    exact hcover.1
  have ht : Ψ.target = univ := by
    rw [hΨt, hPt]
    simp only [hΦt']
    exact hcover.2
  have hsub := cylindricalCore_subset_interior_of_lt e he (fun i => R i / 2) R
    (fun i => by linarith [hR i])
  have hfix' : EqOn Ψ id (cylindricalCore e (fun i => R i / 2)) := by
    intro x hx
    have hxΨ : x ∈ Ψ.source := hs.symm ▸ hsub hx
    rcases hΨs ▸ hxΨ with hxP | hxV
    · obtain ⟨i, hi⟩ := mem_iUnion.mp (hPs ▸ hxP)
      have hχx : x ∈ (χ i).source := (show x ∈ (χ i).source ∧ _ from hΦs i ▸ hi).1
      exact (hΨP hxP).trans ((hP i hi).trans (hlocalfix i x hi (hheight i x hχx hx)))
    · exact hΨV hxV
  refine ⟨Ψ, hs, ht, hfix', ?_⟩
  intro x hx
  have hi := Ψ.left_inv' (hs.symm ▸ hsub hx)
  rw [hfix' hx] at hi
  exact hi


theorem exists_diffeomorph_interior_cylindricalCore
    {ι : Type*} [Finite ι] {D : ι → Type*}
    [∀ i, TopologicalSpace (D i)] [∀ i, ChartedSpace G (D i)]
    (e : ∀ i, D i × Ici (0 : ℝ) → M)
    (he : ∀ i, _root_.Topology.IsClosedEmbedding (e i))
    (hdis : Pairwise fun i j => Disjoint (range (e i)) (range (e j)))
    (χ : ∀ i, _root_.PartialDiffeomorph I (J.prod 𝓘(ℝ, ℝ)) M (D i × ℝ) ∞)
    (hχs : ∀ i, (χ i).source = e i '' {p | 0 < p.2.val})
    (hχt : ∀ i, (χ i).target = {p | 0 < p.2})
    (hχe : ∀ i (p : D i × Ici (0 : ℝ)), 0 < p.2.val → χ i (e i p) = (p.1, p.2.val))
    (R : ι → ℝ) (hR : ∀ i, 0 < R i) :
    let U : TopologicalSpace.Opens M := ⟨interior (cylindricalCore e R), isOpen_interior⟩
    ∃ f : Diffeomorph I I U M ∞,
      (∀ x : U, (x : M) ∈ cylindricalCore e (fun i => R i / 2) → f x = (x : M)) ∧
      ∀ y ∈ cylindricalCore e (fun i => R i / 2), (f.symm y : M) = y := by
  let U : TopologicalSpace.Opens M := ⟨interior (cylindricalCore e R), isOpen_interior⟩
  obtain ⟨Ψ, hs, ht, hfix, hifix⟩ :=
    exists_partialDiffeomorph_cylindricalCore e he hdis χ hχs hχt hχe R hR
  let f : Diffeomorph I I U M ∞ :=
    { toFun := fun x => Ψ x
      invFun := fun y => ⟨Ψ.symm y, by
        change Ψ.symm y ∈ interior (cylindricalCore e R)
        exact hs ▸ Ψ.map_target' (ht.symm ▸ mem_univ y)⟩
      left_inv := fun x => Subtype.ext (Ψ.left_inv' (hs.symm ▸ x.property))
      right_inv := fun y => Ψ.right_inv' (ht.symm ▸ mem_univ y)
      contMDiff_toFun := by
        intro x
        apply contMDiffAt_subtype_iff.mpr
        exact Ψ.contMDiffOn_toFun.contMDiffAt (Ψ.open_source.mem_nhds (hs.symm ▸ x.property))
      contMDiff_invFun := by
        intro y
        apply (ContMDiffAt.subtypeVal_comp_iff U _ y).mp
        exact Ψ.contMDiffOn_invFun.contMDiffAt (Ψ.open_target.mem_nhds (ht.symm ▸ mem_univ y)) }
  exact ⟨f, fun _ hx => hfix hx, fun _ hy => hifix hy⟩

end DifferentialGeometry.Topology

namespace DifferentialGeometry.Topology

private theorem isClosedEmbedding_inward_cylinder
    {C M : Type*} [TopologicalSpace C] [CompactSpace C]
    [TopologicalSpace M] [T2Space M]
    (e : C × Ici (0 : ℝ) → M) (he : _root_.Topology.IsClosedEmbedding e)
    (A : OpenPartialHomeomorph (C × ℝ) M) {ε : ℝ} (hε : 0 < ε)
    (hsource : ∀ c t, -ε ≤ t → (c, t) ∈ A.source)
    (heq : ∀ p : C × Ici (0 : ℝ), e p = A (p.1, p.2.val)) :
    _root_.Topology.IsClosedEmbedding (fun p : C × Ici (0 : ℝ) => A (p.1, p.2.val - ε)) := by
  let T : C × ℝ ≃ₜ C × ℝ :=
    { toFun := fun z => (z.1, z.2 - ε)
      invFun := fun z => (z.1, z.2 + ε)
      left_inv := fun _ => Prod.ext rfl (sub_add_cancel _ _)
      right_inv := fun _ => Prod.ext rfl (add_sub_cancel_right _ _)
      continuous_toFun := continuous_fst.prodMk (continuous_snd.sub continuous_const)
      continuous_invFun := continuous_fst.prodMk (continuous_snd.add continuous_const) }
  have hcoords : _root_.Topology.IsEmbedding
      (fun p : C × Ici (0 : ℝ) => (p.1, p.2.val - ε)) :=
    T.isEmbedding.comp (_root_.Topology.IsEmbedding.id.prodMap _root_.Topology.IsEmbedding.subtypeVal)
  have hmem (p : C × Ici (0 : ℝ)) : (p.1, p.2.val - ε) ∈ A.source :=
    hsource p.1 _ (by have hp : 0 ≤ p.2.val := p.2.property; linarith)
  have hemb : _root_.Topology.IsEmbedding
      (fun p : C × Ici (0 : ℝ) => A (p.1, p.2.val - ε)) :=
    A.isEmbedding_restrict.comp (hcoords.codRestrict A.source hmem)
  have hrange : range (fun p : C × Ici (0 : ℝ) => A (p.1, p.2.val - ε)) =
      range e ∪ A '' (univ ×ˢ Icc (-ε) 0) := by
    ext x
    constructor
    · rintro ⟨p, rfl⟩
      by_cases hp : ε ≤ p.2.val
      · exact Or.inl ⟨(p.1, ⟨p.2.val - ε, sub_nonneg.mpr hp⟩), heq _⟩
      · exact Or.inr ⟨(p.1, p.2.val - ε), ⟨mem_univ _, by have hp : 0 ≤ p.2.val := p.2.property; linarith,
          sub_nonpos.mpr (le_of_not_ge hp)⟩, rfl⟩
    · rintro (⟨p, rfl⟩ | ⟨⟨c, t⟩, ht, rfl⟩)
      · refine ⟨(p.1, ⟨p.2.val + ε, add_nonneg p.2.property hε.le⟩), ?_⟩
        change A (p.1, p.2.val + ε - ε) = e p
        rw [add_sub_cancel_right, heq]
      · refine ⟨(c, ⟨t + ε, by change 0 ≤ t + ε; linarith [show -ε ≤ t from ht.2.1]⟩), ?_⟩
        change A (c, t + ε - ε) = A (c, t)
        rw [add_sub_cancel_right]
  refine ⟨hemb, ?_⟩
  rw [hrange]
  apply he.isClosed_range.union
  apply IsCompact.isClosed
  apply (isCompact_univ.prod isCompact_Icc).image_of_continuousOn
  exact A.continuousOn.mono (fun p hp => hsource p.1 p.2 hp.2.1)


private theorem exists_disjoint_inward_cylinders
    {ι M : Type*} [Finite ι] [TopologicalSpace M] [T2Space M]
    {C : ι → Type*} [∀ i, TopologicalSpace (C i)] [∀ i, CompactSpace (C i)]
    (e : ∀ i, C i × Ici (0 : ℝ) → M)
    (he : ∀ i, _root_.Topology.IsClosedEmbedding (e i))
    (hdis : Pairwise fun i j => Disjoint (range (e i)) (range (e j)))
    (A : ∀ i, OpenPartialHomeomorph (C i × ℝ) M)
    (hsource : ∀ i c t, 0 ≤ t → (c, t) ∈ (A i).source)
    (heq : ∀ i (p : C i × Ici (0 : ℝ)), e i p = A i (p.1, p.2.val)) :
    ∃ ε : ι → ℝ, (∀ i, 0 < ε i) ∧
      (∀ i c t, -ε i ≤ t → (c, t) ∈ (A i).source) ∧
      Pairwise fun i j =>
        Disjoint (range (fun p : C i × Ici (0 : ℝ) => A i (p.1, p.2.val - ε i)))
          (range (fun p : C j × Ici (0 : ℝ) => A j (p.1, p.2.val - ε j))) := by
  classical
  let zero : Ici (0 : ℝ) := ⟨0, by simp⟩
  let K (i : ι) := range (fun c : C i => e i (c, zero))
  have hK (i : ι) : IsCompact (K i) :=
    isCompact_range ((he i).continuous.comp (continuous_id.prodMk continuous_const))
  have hKr (i : ι) : K i ⊆ range (e i) := by
    rintro x ⟨c, rfl⟩
    exact mem_range_self (c, zero)
  obtain ⟨U, hU, hKU, hUd⟩ := Compactness.exists_open_supersets_preserving_disjointness
    K hK (fun i j => i ≠ j) (fun i j hij => (hdis hij).mono (hKr i) (hKr j))
  let W (i : ι) := U i ∩ (⋃ j : {j : ι // j ≠ i}, range (e j.val))ᶜ
  have hW (i : ι) : IsOpen (W i) :=
    (hU i).inter (isClosed_iUnion_of_finite (fun j : {j : ι // j ≠ i} => (he j.val).isClosed_range)).isOpen_compl
  have hKW (i : ι) : K i ⊆ W i := by
    intro x hx
    refine ⟨hKU i hx, ?_⟩
    intro hn
    obtain ⟨j, hj⟩ := mem_iUnion.mp hn
    exact disjoint_left.mp (hdis j.property).symm (hKr i hx) hj
  have hlarge (i : ι) := Compactness.exists_larger_product_chart_band (A i)
    (a := 0) (b := 0) le_rfl
    (by rintro ⟨c, t⟩ ⟨_, ht⟩; exact hsource i c t ht.1) (hW i)
    (by
      rintro x ⟨⟨c, t⟩, ⟨_, ht⟩, rfl⟩
      have ht0 : t = 0 := le_antisymm ht.2 ht.1
      subst t
      exact hKW i ⟨c, heq i (c, zero)⟩)
  choose a b ha hb hband himage using hlarge
  let ε (i : ι) := -a i / 2
  have hε (i : ι) : 0 < ε i := by dsimp only [ε]; linarith [ha i]
  have hleft (i : ι) : a i < -ε i := by dsimp only [ε]; linarith [ha i]
  have hsource' (i : ι) (c : C i) (t : ℝ) (ht : -ε i ≤ t) : (c, t) ∈ (A i).source := by
    by_cases hp : 0 ≤ t
    · exact hsource i c t hp
    · exact hband i ⟨mem_univ _, (hleft i).trans_le ht, (lt_of_not_ge hp).trans (hb i)⟩
  have hnegative (i : ι) (c : C i) (t : ℝ) (ht : -ε i ≤ t) (ht0 : t < 0) :
      A i (c, t) ∈ W i :=
    himage i ⟨(c, t), ⟨mem_univ _, (hleft i).trans_le ht, ht0.trans (hb i)⟩, rfl⟩
  have hmaps (i : ι) (p : C i × Ici (0 : ℝ)) :
      A i (p.1, p.2.val - ε i) ∈ range (e i) ∪ W i := by
    by_cases ht : 0 ≤ p.2.val - ε i
    · exact Or.inl ⟨(p.1, ⟨p.2.val - ε i, ht⟩), heq i _⟩
    · exact Or.inr (hnegative i p.1 _ (by have hp : 0 ≤ p.2.val := p.2.property; linarith) (lt_of_not_ge ht))
  refine ⟨ε, hε, hsource', ?_⟩
  intro i j hij
  apply disjoint_left.mpr
  rintro x ⟨p, hp⟩ ⟨q, hq⟩
  have hi : x ∈ range (e i) ∪ W i := hp ▸ hmaps i p
  have hj : x ∈ range (e j) ∪ W j := hq ▸ hmaps j q
  rcases hi with hi | hi <;> rcases hj with hj | hj
  · exact disjoint_left.mp (hdis hij) hi hj
  · exact hj.2 (mem_iUnion.mpr ⟨⟨i, hij⟩, hi⟩)
  · exact hi.2 (mem_iUnion.mpr ⟨⟨j, hij.symm⟩, hj⟩)
  · exact disjoint_left.mp (hUd i j hij) hi.1 hj.1


variable {E H M F G C : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace H] [TopologicalSpace M] [ChartedSpace H M]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [TopologicalSpace G]
  [TopologicalSpace C] [ChartedSpace G C]
  {I : ModelWithCorners ℝ E H} {J : ModelWithCorners ℝ F G}

private theorem exists_inward_cylinder_chart
    (A : _root_.PartialDiffeomorph (J.prod 𝓘(ℝ, ℝ)) I (C × ℝ) M ∞) (ε : ℝ)
    (hsource : ∀ c t, -ε ≤ t → (c, t) ∈ A.source) :
    ∃ χ : _root_.PartialDiffeomorph I (J.prod 𝓘(ℝ, ℝ)) M (C × ℝ) ∞,
      χ.source = (fun p : C × Ici (0 : ℝ) => A (p.1, p.2.val - ε)) '' {p | 0 < p.2.val} ∧
      χ.target = {p | 0 < p.2} ∧
      ∀ p : C × Ici (0 : ℝ), 0 < p.2.val → χ (A (p.1, p.2.val - ε)) = (p.1, p.2.val) := by
  let T : Diffeomorph (J.prod 𝓘(ℝ, ℝ)) (J.prod 𝓘(ℝ, ℝ)) (C × ℝ) (C × ℝ) ∞ :=
    { toFun := fun z => (z.1, z.2 - ε)
      invFun := fun z => (z.1, z.2 + ε)
      left_inv := fun _ => Prod.ext rfl (sub_add_cancel _ _)
      right_inv := fun _ => Prod.ext rfl (add_sub_cancel_right _ _)
      contMDiff_toFun := contMDiff_fst.prodMk (contMDiff_snd.sub contMDiff_const)
      contMDiff_invFun := contMDiff_fst.prodMk (contMDiff_snd.add contMDiff_const) }
  let Ψ := PartialDiffeomorph.restrict (T.toPartialDiffeomorph.trans A) {p | 0 < p.2}
    (isOpen_lt continuous_const continuous_snd)
  have hs : Ψ.source = {p | 0 < p.2} := by
    ext p
    change ((True ∧ (p.1, p.2 - ε) ∈ A.source) ∧ 0 < p.2) ↔ 0 < p.2
    refine ⟨fun hp => hp.2, fun hp => ⟨⟨trivial, ?_⟩, hp⟩⟩
    exact hsource p.1 _ (by linarith)
  refine ⟨Ψ.symm, ?_, hs, ?_⟩
  · change Ψ.target = _
    have hi := Ψ.toPartialEquiv.image_source_eq_target
    rw [hs] at hi
    rw [← hi]
    ext x
    constructor
    · rintro ⟨⟨c, t⟩, ht, rfl⟩
      change 0 < t at ht
      exact ⟨(c, ⟨t, ht.le⟩), ht, rfl⟩
    · rintro ⟨p, hp, rfl⟩
      exact ⟨(p.1, p.2.val), hp, rfl⟩
  · intro p hp
    change Ψ.symm (Ψ (p.1, p.2.val)) = (p.1, p.2.val)
    apply Ψ.left_inv'
    rw [hs]
    exact hp


private theorem cylindricalCore_inward_shift
    {ι X : Type*} {D : ι → Type*}
    (e : ∀ i, D i × Ici (0 : ℝ) → X) (A : ∀ i, D i × ℝ → X)
    (heq : ∀ i (p : D i × Ici (0 : ℝ)), e i p = A i (p.1, p.2.val))
    (ε : ι → ℝ) (hε : ∀ i, 0 ≤ ε i) :
    cylindricalCore (fun i (p : D i × Ici (0 : ℝ)) => A i (p.1, p.2.val - ε i)) ε =
      cylindricalCore e (fun _ => 0) := by
  unfold cylindricalCore
  congr 1
  apply iUnion_congr
  intro i
  ext x
  constructor
  · rintro ⟨p, hp, rfl⟩
    have ht : ε i < p.2.val := hp
    exact ⟨(p.1, ⟨p.2.val - ε i, (sub_pos.mpr ht).le⟩), sub_pos.mpr ht, heq i _⟩
  · rintro ⟨p, hp, rfl⟩
    have ht : 0 < p.2.val := hp
    refine ⟨(p.1, ⟨p.2.val + ε i, add_nonneg p.2.property (hε i)⟩), ?_, ?_⟩
    · change ε i < p.2.val + ε i
      linarith
    · change A i (p.1, p.2.val + ε i - ε i) = e i p
      rw [add_sub_cancel_right, heq i p]

theorem exists_diffeomorph_interior_cylindricalCore_zero
    [T2Space M] {ι : Type*} [Finite ι] {D : ι → Type*}
    [∀ i, TopologicalSpace (D i)] [∀ i, CompactSpace (D i)] [∀ i, ChartedSpace G (D i)]
    (e : ∀ i, D i × Ici (0 : ℝ) → M)
    (he : ∀ i, _root_.Topology.IsClosedEmbedding (e i))
    (hdis : Pairwise fun i j => Disjoint (range (e i)) (range (e j)))
    (A : ∀ i, _root_.PartialDiffeomorph (J.prod 𝓘(ℝ, ℝ)) I (D i × ℝ) M ∞)
    (hsource : ∀ i c t, 0 ≤ t → (c, t) ∈ (A i).source)
    (heq : ∀ i (p : D i × Ici (0 : ℝ)), e i p = A i (p.1, p.2.val)) :
    let U : TopologicalSpace.Opens M :=
      ⟨interior (cylindricalCore e (fun _ => 0)), isOpen_interior⟩
    ∃ f : Diffeomorph I I U M ∞,
      (∀ x : U, (∀ i, (x : M) ∉ (A i).target) → f x = (x : M)) ∧
      ∀ y, (∀ i, y ∉ (A i).target) → (f.symm y : M) = y := by
  classical
  obtain ⟨ε, hε, hsource', hdis'⟩ := exists_disjoint_inward_cylinders e he hdis
    (fun i => (A i).toOpenPartialHomeomorph) hsource heq
  let e' (i : ι) (p : D i × Ici (0 : ℝ)) := A i (p.1, p.2.val - ε i)
  have he' (i : ι) : _root_.Topology.IsClosedEmbedding (e' i) :=
    isClosedEmbedding_inward_cylinder (e i) (he i) (A i).toOpenPartialHomeomorph
      (hε i) (hsource' i) (heq i)
  choose χ hχs hχt hχe using fun i => exists_inward_cylinder_chart (A i) (ε i) (hsource' i)
  obtain ⟨f, hf, hfi⟩ := exists_diffeomorph_interior_cylindricalCore
    e' he' hdis' χ hχs hχt hχe ε hε
  have hcore : cylindricalCore e' ε = cylindricalCore e (fun _ => 0) :=
    cylindricalCore_inward_shift e (fun i => A i) heq ε (fun i => (hε i).le)
  have houtside (x : M) (hx : ∀ i, x ∉ (A i).target) :
      x ∈ cylindricalCore e' (fun i => ε i / 2) := by
    intro hn
    obtain ⟨i, p, _, rfl⟩ := mem_iUnion.mp hn
    exact hx i ((A i).map_source' (hsource' i p.1 _
      (by have hp : 0 ≤ p.2.val := p.2.property; linarith)))
  dsimp only
  rw [← hcore]
  exact ⟨f, fun x hx => hf x (houtside x hx), fun y hy => hfi y (houtside y hy)⟩

end DifferentialGeometry.Topology
