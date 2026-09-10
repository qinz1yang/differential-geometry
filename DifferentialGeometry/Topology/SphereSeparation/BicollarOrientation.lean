import DifferentialGeometry.Topology.SphereSeparation.BicollarOrder

set_option autoImplicit false

open Function Set Topology
open scoped Manifold ContDiff Topology

namespace Poincare.Topology.SphereSeparation

theorem lowerAxis_connected {a : ℝ} (c : AxialInterval a) :
    IsConnected (Iio c : Set (AxialInterval a)) := by
  have hI : IsConnected (Ioo (-a) (c : ℝ)) :=
    isConnected_Ioo c.2.1
  let _ : ConnectedSpace (Ioo (-a) (c : ℝ)) :=
    Subtype.connectedSpace hI
  let f : Ioo (-a) (c : ℝ) → AxialInterval a := fun r =>
    ⟨r.1, r.2.1, lt_trans r.2.2 c.2.2⟩
  have hf : Continuous f := by fun_prop
  have hrange : Set.range f = Iio c := by
    ext r
    constructor
    · rintro ⟨q, rfl⟩
      exact q.2.2
    · intro hr
      exact ⟨⟨r.1, r.2.1, hr⟩, Subtype.ext rfl⟩
  rw [← hrange]
  exact isConnected_range hf

theorem upperAxis_connected {a : ℝ} (c : AxialInterval a) :
    IsConnected (Ioi c : Set (AxialInterval a)) := by
  have hI : IsConnected (Ioo (c : ℝ) a) :=
    isConnected_Ioo c.2.2
  let _ : ConnectedSpace (Ioo (c : ℝ) a) :=
    Subtype.connectedSpace hI
  let f : Ioo (c : ℝ) a → AxialInterval a := fun r =>
    ⟨r.1, lt_trans c.2.1 r.2.1, r.2.2⟩
  have hf : Continuous f := by fun_prop
  have hrange : Set.range f = Ioi c := by
    ext r
    constructor
    · rintro ⟨q, rfl⟩
      exact q.2.1
    · intro hr
      exact ⟨⟨r.1, hr, r.2.2⟩, Subtype.ext rfl⟩
  rw [← hrange]
  exact isConnected_range hf


theorem isConnected_lowerHalfImage
    {N : Type*} [TopologicalSpace N] {a : ℝ}
    (Φ : SphereTwo × AxialInterval a → N) (hΦ : Continuous Φ)
    (c : AxialInterval a) :
    IsConnected (lowerHalfImage Φ c) :=
  (isConnected_sphereTwo.prod (lowerAxis_connected c)).image Φ
    hΦ.continuousOn


theorem isConnected_upperHalfImage
    {N : Type*} [TopologicalSpace N] {a : ℝ}
    (Φ : SphereTwo × AxialInterval a → N) (hΦ : Continuous Φ)
    (c : AxialInterval a) :
    IsConnected (upperHalfImage Φ c) :=
  (isConnected_sphereTwo.prod (upperAxis_connected c)).image Φ
    hΦ.continuousOn

theorem bicollar_halves_opposite_at
    {N : Type*} [TopologicalSpace N] [ChartedSpace EuclideanThree N]
    {a : ℝ} (Φ : SphereTwo × AxialInterval a → N)
    (hΦ : Manifold.IsSmoothEmbedding
      ((𝓘(ℝ, EuclideanSpace ℝ (Fin 2))).prod 𝓘(ℝ))
      (𝓘(ℝ, EuclideanThree)) ∞ Φ)
    (c : AxialInterval a) (d : SphereSides (sliceImage Φ c)) :
    Xor
      (lowerHalfImage Φ c ⊆ d.compactSide ∧
        upperHalfImage Φ c ⊆ d.endSide)
      (lowerHalfImage Φ c ⊆ d.endSide ∧
        upperHalfImage Φ c ⊆ d.compactSide) := by
  have hΦcont : Continuous Φ := hΦ.contMDiff.continuous
  have hlower : IsConnected (lowerHalfImage Φ c) :=
    isConnected_lowerHalfImage Φ hΦcont c
  have hupper : IsConnected (upperHalfImage Φ c) :=
    isConnected_upperHalfImage Φ hΦcont c
  have hlowerCompl : lowerHalfImage Φ c ⊆ (sliceImage Φ c)ᶜ := by
    intro y hylower hyslice
    rcases hylower with ⟨p, hp, rfl⟩
    rcases hyslice with ⟨q, hq, hqp⟩
    have hpq : q = p := hΦ.isEmbedding.injective hqp
    have hqc : q.2 = c := hq.2
    have hplt : p.2 < c := hp.2
    rw [← hpq, hqc] at hplt
    exact lt_irrefl _ hplt
  have hupperCompl : upperHalfImage Φ c ⊆ (sliceImage Φ c)ᶜ := by
    intro y hyupper hyslice
    rcases hyupper with ⟨p, hp, rfl⟩
    rcases hyslice with ⟨q, hq, hqp⟩
    have hpq : q = p := hΦ.isEmbedding.injective hqp
    have hqc : q.2 = c := hq.2
    have hcplt : c < p.2 := hp.2
    rw [← hpq, hqc] at hcplt
    exact lt_irrefl _ hcplt
  have hopen : IsOpen (Set.range Φ) := by
    have hrank :
        Module.finrank ℝ (EuclideanSpace ℝ (Fin 2) × ℝ) =
          Module.finrank ℝ EuclideanThree := by
      norm_num [Module.finrank_prod, Module.finrank_fin_fun, EuclideanThree]
    exact Manifold.isOpen_range_of_isSmoothEmbedding
      (I := ((𝓘(ℝ, EuclideanSpace ℝ (Fin 2))).prod 𝓘(ℝ)))
      (J := 𝓘(ℝ, EuclideanThree)) hrank hΦ
  have hsliceNonempty : (sliceImage Φ c).Nonempty := by
    obtain ⟨p, hp⟩ := isConnected_sphereTwo.nonempty
    exact ⟨Φ (p, c), ⟨(p, c), ⟨hp, rfl⟩, rfl⟩⟩
  have hsliceRange : sliceImage Φ c ⊆ Set.range Φ := by
    rintro y ⟨p, -, rfl⟩
    exact ⟨p, rfl⟩
  have hrangeDecomp : Set.range Φ ⊆
      (lowerHalfImage Φ c ∪ sliceImage Φ c) ∪
        upperHalfImage Φ c := by
    rintro y ⟨p, rfl⟩
    rcases lt_trichotomy p.2 c with hp | hp | hp
    · exact Or.inl (Or.inl ⟨p, ⟨Set.mem_univ _, hp⟩, rfl⟩)
    · exact Or.inl (Or.inr ⟨p, ⟨Set.mem_univ _, hp⟩, rfl⟩)
    · exact Or.inr ⟨p, ⟨Set.mem_univ _, hp⟩, rfl⟩
  exact d.neighborhood_halves_opposite hsliceNonempty hlower hupper
    hlowerCompl hupperCompl hopen hsliceRange hrangeDecomp

structure IsAxiallyOrientedAtZero
    {N : Type*} [TopologicalSpace N] {a : ℝ} (ha : 0 < a)
    (Φ : SphereTwo × AxialInterval a → N)
    (d : ∀ c, SphereSides (sliceImage Φ c)) : Prop where
  lower_subset_compact :
    lowerHalfImage Φ (axialZero ha) ⊆ (d (axialZero ha)).compactSide
  upper_subset_end :
    upperHalfImage Φ (axialZero ha) ⊆ (d (axialZero ha)).endSide

private theorem axialIcc_isCompact_orientation {a : ℝ}
    (s t : AxialInterval a) :
    IsCompact (Icc s t : Set (AxialInterval a)) := by
  let f : Icc (s : ℝ) (t : ℝ) → AxialInterval a := fun r =>
    ⟨r.1, lt_of_lt_of_le s.2.1 r.2.1,
      lt_of_le_of_lt r.2.2 t.2.2⟩
  have hf : Continuous f := by fun_prop
  have hrange : Set.range f = Icc s t := by
    ext r
    constructor
    · rintro ⟨q, rfl⟩
      exact q.2
    · intro hr
      exact ⟨⟨r.1, hr⟩, Subtype.ext rfl⟩
  rw [← hrange]
  exact isCompact_range hf

private theorem closedSlabImage_isCompact
    {N : Type*} [TopologicalSpace N] {a : ℝ}
    (Φ : SphereTwo × AxialInterval a → N) (hΦ : Continuous Φ)
    (s t : AxialInterval a) :
    IsCompact (closedSlabImage Φ s t) := by
  exact (isCompact_univ.prod (axialIcc_isCompact_orientation s t)).image hΦ

private theorem lowerHalf_disjoint_slice
    {N : Type*} {a : ℝ} {Φ : SphereTwo × AxialInterval a → N}
    (hΦ : Injective Φ) (c : AxialInterval a) :
    Disjoint (lowerHalfImage Φ c) (sliceImage Φ c) := by
  rw [Set.disjoint_left]
  intro y hylower hyslice
  rcases hylower with ⟨p, hp, rfl⟩
  rcases hyslice with ⟨q, hq, hqp⟩
  have hpq : q = p := hΦ hqp
  have hqc : q.2 = c := hq.2
  have hplt : p.2 < c := hp.2
  rw [← hpq, hqc] at hplt
  exact lt_irrefl _ hplt

private theorem upperHalf_disjoint_slice
    {N : Type*} {a : ℝ} {Φ : SphereTwo × AxialInterval a → N}
    (hΦ : Injective Φ) (c : AxialInterval a) :
    Disjoint (upperHalfImage Φ c) (sliceImage Φ c) := by
  rw [Set.disjoint_left]
  intro y hyupper hyslice
  rcases hyupper with ⟨p, hp, rfl⟩
  rcases hyslice with ⟨q, hq, hqp⟩
  have hpq : q = p := hΦ hqp
  have hqc : q.2 = c := hq.2
  have hcplt : c < p.2 := hp.2
  rw [← hpq, hqc] at hcplt
  exact lt_irrefl _ hcplt

private theorem positive_slice_oriented
    {N : Type*} [TopologicalSpace N] [T2Space N]
    [ChartedSpace EuclideanThree N] {a : ℝ} (ha : 0 < a)
    (Φ : SphereTwo × AxialInterval a → N)
    (hΦ : Manifold.IsSmoothEmbedding
      ((𝓘(ℝ, EuclideanSpace ℝ (Fin 2))).prod 𝓘(ℝ))
      (𝓘(ℝ, EuclideanThree)) ∞ Φ)
    (d : ∀ c, SphereSides (sliceImage Φ c))
    (o₀ : IsAxiallyOrientedAtZero ha Φ d)
    (c : AxialInterval a) (hc : axialZero ha < c) :
    lowerHalfImage Φ c ⊆ (d c).compactSide ∧
      upperHalfImage Φ c ⊆ (d c).endSide := by
  let z := axialZero ha
  let C : Set N := (d z).compactSide ∪ lowerHalfImage Φ c
  have hopenRange : IsOpen (Set.range Φ) := by
    have hrank :
        Module.finrank ℝ (EuclideanSpace ℝ (Fin 2) × ℝ) =
          Module.finrank ℝ EuclideanThree := by
      norm_num [Module.finrank_prod, Module.finrank_fin_fun, EuclideanThree]
    exact Manifold.isOpen_range_of_isSmoothEmbedding
      (I := ((𝓘(ℝ, EuclideanSpace ℝ (Fin 2))).prod 𝓘(ℝ)))
      (J := 𝓘(ℝ, EuclideanThree)) hrank hΦ
  let hΦopen : IsOpenEmbedding Φ := ⟨hΦ.isEmbedding, hopenRange⟩
  have hCopen : IsOpen C := by
    exact (d z).isOpen_compactSide.union
      (hΦopen.isOpenMap _ (isOpen_univ.prod isOpen_Iio))
  have hlowerConn : IsConnected (lowerHalfImage Φ c) :=
    (isConnected_sphereTwo.prod (lowerAxis_connected c)).image Φ
      hΦ.contMDiff.continuous.continuousOn
  have hinter : ((d z).compactSide ∩ lowerHalfImage Φ c).Nonempty := by
    obtain ⟨p, hp⟩ := isConnected_sphereTwo.nonempty
    let r : AxialInterval a :=
      ⟨-a / 2, by linarith, by linarith⟩
    have hrz : r < z := by
      change -a / 2 < 0
      linarith
    have hrc : r < c := hrz.trans hc
    refine ⟨Φ (p, r), ?_, ?_⟩
    · exact o₀.lower_subset_compact ⟨(p, r), ⟨hp, hrz⟩, rfl⟩
    · exact ⟨(p, r), ⟨hp, hrc⟩, rfl⟩
  have hCconn : IsConnected C :=
    IsConnected.union hinter (d z).isConnected_compactSide hlowerConn
  have hScUpper : sliceImage Φ c ⊆ upperHalfImage Φ z := by
    rintro y ⟨p, hp, rfl⟩
    exact ⟨p, ⟨hp.1, hp.2 ▸ hc⟩, rfl⟩
  have hCcompl : C ⊆ (sliceImage Φ c)ᶜ := by
    rintro y (hyB | hyLower) hySc
    · have hyE : y ∈ (d z).endSide :=
        o₀.upper_subset_end (hScUpper hySc)
      exact (d z).disjoint.le_bot ⟨hyB, hyE⟩
    · exact (lowerHalf_disjoint_slice hΦ.isEmbedding.injective c).le_bot
        ⟨hyLower, hySc⟩
  have hCeq : C = (d z).compactSide ∪ halfOpenSlabImage Φ z c := by
    ext y
    constructor
    · rintro (hyB | ⟨p, hp, rfl⟩)
      · exact Or.inl hyB
      · rcases lt_trichotomy p.2 z with hpz | hpz | hzp
        · exact Or.inl
            (o₀.lower_subset_compact ⟨p, ⟨hp.1, hpz⟩, rfl⟩)
        · exact Or.inr ⟨p, ⟨hp.1, hpz.ge, hp.2⟩, rfl⟩
        · exact Or.inr ⟨p, ⟨hp.1, hzp.le, hp.2⟩, rfl⟩
    · rintro (hyB | ⟨p, hp, rfl⟩)
      · exact Or.inl hyB
      · exact Or.inr ⟨p, ⟨hp.1, hp.2.2⟩, rfl⟩
  have hslabCompact : IsCompact (closedSlabImage Φ z c) :=
    closedSlabImage_isCompact Φ hΦ.contMDiff.continuous z c
  have hclosureBound : closure C ⊆
      closure (d z).compactSide ∪ closedSlabImage Φ z c := by
    rw [hCeq]
    apply closure_minimal
    · rintro y (hyB | ⟨p, hp, rfl⟩)
      · exact Or.inl (subset_closure hyB)
      · exact Or.inr ⟨p, ⟨hp.1, hp.2.1, hp.2.2.le⟩, rfl⟩
    · exact isClosed_closure.union hslabCompact.isClosed
  have hclosure : closure C ⊆ C ∪ sliceImage Φ c := by
    intro y hy
    rcases hclosureBound hy with hyK | hySlab
    · rw [(d z).closure_compactSide] at hyK
      rcases hyK with hyB | hySz
      · exact Or.inl (Or.inl hyB)
      · exact Or.inl (Or.inr (by
          rcases hySz with ⟨p, hp, rfl⟩
          exact ⟨p, ⟨hp.1, hp.2 ▸ hc⟩, rfl⟩))
    · rcases hySlab with ⟨p, hp, rfl⟩
      rcases lt_or_eq_of_le hp.2.2 with hpc | hpc
      · exact Or.inl (Or.inr ⟨p, ⟨hp.1, hpc⟩, rfl⟩)
      · exact Or.inr ⟨p, ⟨hp.1, hpc⟩, rfl⟩
  have hcomponent : C = (d c).compactSide ∨ C = (d c).endSide :=
    (d c).eq_compactSide_or_eq_endSide_of_isOpen_of_closure_subset
      hCopen hCconn hCcompl hclosure
  have hCcompact : IsCompact (closure C) :=
    ((d z).isCompact_closure_compactSide.union hslabCompact).of_isClosed_subset
      isClosed_closure hclosureBound
  have hCcompactSide : C = (d c).compactSide := by
    rcases hcomponent with h | h
    · exact h
    · exfalso
      apply (d c).not_isCompact_closure_endSide
      rw [← h]
      exact hCcompact
  have hlowerCompact : lowerHalfImage Φ c ⊆ (d c).compactSide := by
    rw [← hCcompactSide]
    exact subset_union_right
  rcases (bicollar_halves_opposite_at Φ hΦ c (d c)).or with hgood | hbad
  · exact hgood
  · obtain ⟨y, hy⟩ := hlowerConn.nonempty
    exact False.elim ((d c).disjoint.le_bot
      ⟨hlowerCompact hy, hbad.1 hy⟩)

private theorem negative_slice_oriented
    {N : Type*} [TopologicalSpace N] [T2Space N]
    [ChartedSpace EuclideanThree N] {a : ℝ} (ha : 0 < a)
    (Φ : SphereTwo × AxialInterval a → N)
    (hΦ : Manifold.IsSmoothEmbedding
      ((𝓘(ℝ, EuclideanSpace ℝ (Fin 2))).prod 𝓘(ℝ))
      (𝓘(ℝ, EuclideanThree)) ∞ Φ)
    (d : ∀ c, SphereSides (sliceImage Φ c))
    (o₀ : IsAxiallyOrientedAtZero ha Φ d)
    (c : AxialInterval a) (hc : c < axialZero ha) :
    lowerHalfImage Φ c ⊆ (d c).compactSide ∧
      upperHalfImage Φ c ⊆ (d c).endSide := by
  let z := axialZero ha
  let C : Set N := (d z).endSide ∪ upperHalfImage Φ c
  have hopenRange : IsOpen (Set.range Φ) := by
    have hrank :
        Module.finrank ℝ (EuclideanSpace ℝ (Fin 2) × ℝ) =
          Module.finrank ℝ EuclideanThree := by
      norm_num [Module.finrank_prod, Module.finrank_fin_fun, EuclideanThree]
    exact Manifold.isOpen_range_of_isSmoothEmbedding
      (I := ((𝓘(ℝ, EuclideanSpace ℝ (Fin 2))).prod 𝓘(ℝ)))
      (J := 𝓘(ℝ, EuclideanThree)) hrank hΦ
  let hΦopen : IsOpenEmbedding Φ := ⟨hΦ.isEmbedding, hopenRange⟩
  have hCopen : IsOpen C := by
    exact (d z).isOpen_endSide.union
      (hΦopen.isOpenMap _ (isOpen_univ.prod isOpen_Ioi))
  have hupperConn : IsConnected (upperHalfImage Φ c) :=
    (isConnected_sphereTwo.prod (upperAxis_connected c)).image Φ
      hΦ.contMDiff.continuous.continuousOn
  have hinter : ((d z).endSide ∩ upperHalfImage Φ c).Nonempty := by
    obtain ⟨p, hp⟩ := isConnected_sphereTwo.nonempty
    let r : AxialInterval a :=
      ⟨a / 2, by linarith, by linarith⟩
    have hzr : z < r := by
      change 0 < a / 2
      linarith
    have hcr : c < r := hc.trans hzr
    refine ⟨Φ (p, r), ?_, ?_⟩
    · exact o₀.upper_subset_end ⟨(p, r), ⟨hp, hzr⟩, rfl⟩
    · exact ⟨(p, r), ⟨hp, hcr⟩, rfl⟩
  have hCconn : IsConnected C :=
    IsConnected.union hinter (d z).isConnected_endSide hupperConn
  have hScLower : sliceImage Φ c ⊆ lowerHalfImage Φ z := by
    rintro y ⟨p, hp, rfl⟩
    exact ⟨p, ⟨hp.1, hp.2 ▸ hc⟩, rfl⟩
  have hCcompl : C ⊆ (sliceImage Φ c)ᶜ := by
    rintro y (hyE | hyUpper) hySc
    · have hyB : y ∈ (d z).compactSide :=
        o₀.lower_subset_compact (hScLower hySc)
      exact (d z).disjoint.le_bot ⟨hyB, hyE⟩
    · exact (upperHalf_disjoint_slice hΦ.isEmbedding.injective c).le_bot
        ⟨hyUpper, hySc⟩
  have hslabCompact : IsCompact (closedSlabImage Φ c z) :=
    closedSlabImage_isCompact Φ hΦ.contMDiff.continuous c z
  have hCsubset : C ⊆
      closure (d z).endSide ∪ closedSlabImage Φ c z := by
    rintro y (hyE | ⟨p, hp, rfl⟩)
    · exact Or.inl (subset_closure hyE)
    · rcases lt_trichotomy p.2 z with hpz | hpz | hzp
      · exact Or.inr ⟨p, ⟨hp.1, hp.2.le, hpz.le⟩, rfl⟩
      · exact Or.inr ⟨p, ⟨hp.1, hp.2.le, hpz.le⟩, rfl⟩
      · exact Or.inl (subset_closure
          (o₀.upper_subset_end ⟨p, ⟨hp.1, hzp⟩, rfl⟩))
  have hclosureBound : closure C ⊆
      closure (d z).endSide ∪ closedSlabImage Φ c z := by
    exact closure_minimal hCsubset
      (isClosed_closure.union hslabCompact.isClosed)
  have hclosure : closure C ⊆ C ∪ sliceImage Φ c := by
    intro y hy
    rcases hclosureBound hy with hyK | hySlab
    · rw [(d z).closure_endSide] at hyK
      rcases hyK with hyE | hySz
      · exact Or.inl (Or.inl hyE)
      · exact Or.inl (Or.inr (by
          rcases hySz with ⟨p, hp, rfl⟩
          exact ⟨p, ⟨hp.1, hp.2 ▸ hc⟩, rfl⟩))
    · rcases hySlab with ⟨p, hp, rfl⟩
      rcases eq_or_lt_of_le hp.2.1 with hpc | hcp
      · exact Or.inr ⟨p, ⟨hp.1, hpc.symm⟩, rfl⟩
      · exact Or.inl (Or.inr ⟨p, ⟨hp.1, hcp⟩, rfl⟩)
  have hcomponent : C = (d c).compactSide ∨ C = (d c).endSide :=
    (d c).eq_compactSide_or_eq_endSide_of_isOpen_of_closure_subset
      hCopen hCconn hCcompl hclosure
  have hCendSide : C = (d c).endSide := by
    rcases hcomponent with h | h
    · exfalso
      apply (d z).not_isCompact_closure_endSide
      exact (d c).isCompact_closure_compactSide.of_isClosed_subset
        isClosed_closure (closure_mono (by
          intro y hyE
          rw [← h]
          exact Or.inl hyE))
    · exact h
  have hupperEnd : upperHalfImage Φ c ⊆ (d c).endSide := by
    rw [← hCendSide]
    exact subset_union_right
  rcases (bicollar_halves_opposite_at Φ hΦ c (d c)).or with hgood | hbad
  · exact hgood
  · obtain ⟨y, hy⟩ := hupperConn.nonempty
    exact False.elim ((d c).disjoint.le_bot
      ⟨hbad.2 hy, hupperEnd hy⟩)

theorem axiallyOriented_of_atZero
    {N : Type*} [TopologicalSpace N] [T2Space N]
    [ChartedSpace EuclideanThree N] {a : ℝ} (ha : 0 < a)
    (Φ : SphereTwo × AxialInterval a → N)
    (hΦ : Manifold.IsSmoothEmbedding
      ((𝓘(ℝ, EuclideanSpace ℝ (Fin 2))).prod 𝓘(ℝ))
      (𝓘(ℝ, EuclideanThree)) ∞ Φ)
    (d : ∀ c, SphereSides (sliceImage Φ c))
    (o₀ : IsAxiallyOrientedAtZero ha Φ d) :
    IsAxiallyOriented Φ d := by
  constructor
  · intro c
    rcases lt_trichotomy c (axialZero ha) with hc | hc | hc
    · exact (negative_slice_oriented ha Φ hΦ d o₀ c hc).1
    · subst c
      exact o₀.lower_subset_compact
    · exact (positive_slice_oriented ha Φ hΦ d o₀ c hc).1
  · intro c
    rcases lt_trichotomy c (axialZero ha) with hc | hc | hc
    · exact (negative_slice_oriented ha Φ hΦ d o₀ c hc).2
    · subst c
      exact o₀.upper_subset_end
    · exact (positive_slice_oriented ha Φ hΦ d o₀ c hc).2

theorem bicollar_order_of_atZero
    {N : Type*} [TopologicalSpace N] [T2Space N]
    [ChartedSpace EuclideanThree N] {a : ℝ} (ha : 0 < a)
    (Φ : SphereTwo × AxialInterval a → N)
    (hΦ : Manifold.IsSmoothEmbedding
      ((𝓘(ℝ, EuclideanSpace ℝ (Fin 2))).prod 𝓘(ℝ))
      (𝓘(ℝ, EuclideanThree)) ∞ Φ)
    (d : ∀ c, SphereSides (sliceImage Φ c))
    (o₀ : IsAxiallyOrientedAtZero ha Φ d)
    {s t : AxialInterval a} (hst : s < t) :
    (closure (d s).compactSide ⊆ (d t).compactSide ∧
      (d t).compactSide = interior (closure (d t).compactSide)) ∧
    closure (d t).compactSide =
      closure (d s).compactSide ∪ closedSlabImage Φ s t ∧
    ((closedSlabImage Φ s t)ᶜ =
        (d s).compactSide ∪ (d t).endSide ∧
      Disjoint (d s).compactSide (d t).endSide) ∧
    closure (d s).compactSide ⊂ (d t).compactSide ∧
    closure (d s).compactSide ⊂ closure (d t).compactSide := by
  let o : IsAxiallyOriented Φ d :=
    axiallyOriented_of_atZero ha Φ hΦ d o₀
  exact ⟨o.compactClosure_subset_later_compact_and_interior hst,
    o.compactClosure_eq_union_closedSlab
      ⟨hΦ.isEmbedding, by
        have hrank :
            Module.finrank ℝ (EuclideanSpace ℝ (Fin 2) × ℝ) =
              Module.finrank ℝ EuclideanThree := by
          norm_num [Module.finrank_prod, Module.finrank_fin_fun,
            EuclideanThree]
        exact Manifold.isOpen_range_of_isSmoothEmbedding
          (I := ((𝓘(ℝ, EuclideanSpace ℝ (Fin 2))).prod 𝓘(ℝ)))
          (J := 𝓘(ℝ, EuclideanThree)) hrank hΦ⟩ hst,
    o.compl_closedSlab_eq_union_and_disjoint
      ⟨hΦ.isEmbedding, by
        have hrank :
            Module.finrank ℝ (EuclideanSpace ℝ (Fin 2) × ℝ) =
              Module.finrank ℝ EuclideanThree := by
          norm_num [Module.finrank_prod, Module.finrank_fin_fun,
            EuclideanThree]
        exact Manifold.isOpen_range_of_isSmoothEmbedding
          (I := ((𝓘(ℝ, EuclideanSpace ℝ (Fin 2))).prod 𝓘(ℝ)))
          (J := 𝓘(ℝ, EuclideanThree)) hrank hΦ⟩ hst,
    o.compactClosure_ssubset_later_compact hst,
    o.compactClosure_ssubset hst⟩

end Poincare.Topology.SphereSeparation
