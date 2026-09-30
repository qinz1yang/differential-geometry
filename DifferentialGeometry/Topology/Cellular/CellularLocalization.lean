import DifferentialGeometry.Topology.Cellular.CellularCollapse

namespace DifferentialGeometry.Topology

open Set Metric _root_.Topology

variable {X : Type*} [TopologicalSpace X] [T2Space X] {n : ℕ}

namespace EmbeddedClosedCell

noncomputable def subtype (c : EmbeddedClosedCell n X) {D : Set X} (hD : c.carrier ⊆ D) :
    EmbeddedClosedCell n D where
  map x := ⟨c.map x, hD (mem_range_self x)⟩
  isClosedEmbedding := by
    have : CompactSpace (Disk n) := isCompact_iff_compactSpace.mp (isCompact_closedBall _ _)
    exact (c.isClosedEmbedding.continuous.subtype_mk _).isClosedEmbedding
      (fun a b h => c.isClosedEmbedding.injective (congrArg Subtype.val h))
  isOpen_interior := by
    have he : (fun x : Disk n => (⟨c.map x, hD (mem_range_self x)⟩ : D)) '' diskInterior n =
        Subtype.val ⁻¹' c.interiorSet := by
      ext x
      constructor
      · rintro ⟨y, hy, he⟩
        exact ⟨y, hy, congrArg Subtype.val he⟩
      · rintro ⟨y, hy, he⟩
        exact ⟨y, hy, Subtype.ext he⟩
    rw [he]
    exact c.isOpen_interior.preimage continuous_subtype_val

theorem subtype_carrier (c : EmbeddedClosedCell n X) {D : Set X} (hD : c.carrier ⊆ D) :
    (c.subtype hD).carrier = Subtype.val ⁻¹' c.carrier := by
  ext x
  constructor
  · rintro ⟨y, hy⟩
    exact ⟨y, congrArg Subtype.val hy⟩
  · rintro ⟨y, hy⟩
    exact ⟨y, Subtype.ext hy⟩

theorem subtype_interiorSet (c : EmbeddedClosedCell n X) {D : Set X} (hD : c.carrier ⊆ D) :
    (c.subtype hD).interiorSet = Subtype.val ⁻¹' c.interiorSet := by
  ext x
  constructor
  · rintro ⟨y, hy, he⟩
    exact ⟨y, hy, congrArg Subtype.val he⟩
  · rintro ⟨y, hy, he⟩
    exact ⟨y, hy, Subtype.ext he⟩

end EmbeddedClosedCell

omit [T2Space X] in
theorem isCellular.mapHomeomorph {Y : Type*} [TopologicalSpace Y]
    {K : Set X} (hK : isCellular n K) (e : X ≃ₜ Y) : isCellular n (e '' K) := by
  obtain ⟨c, hc, rfl⟩ := hK
  refine ⟨fun i => (c i).mapHomeomorph e, ?_, ?_⟩
  · intro i
    simpa only [EmbeddedClosedCell.mapHomeomorph_carrier, EmbeddedClosedCell.mapHomeomorph_interiorSet]
      using image_mono (hc i)
  · simpa only [EmbeddedClosedCell.mapHomeomorph_carrier] using image_iInter e.bijective
      (fun i => (c i).carrier)

theorem isCellular.subtype_of_subset_interior {K D : Set X} (hK : isCellular n K)
    (hKD : K ⊆ interior D) : isCellular n (Subtype.val ⁻¹' K : Set D) := by
  obtain ⟨c, hc, hK⟩ := hK
  have hanti : Antitone (fun i => (c i).carrier) :=
    antitone_nat_of_succ_le (fun i => (hc i).trans (c i).interiorSet_subset_carrier)
  obtain ⟨N, hN⟩ := exists_subset_nhds_of_isCompact'
    (V := fun i => (c i).carrier)
    (fun i j => ⟨max i j, hanti (le_max_left _ _), hanti (le_max_right _ _)⟩)
    (fun i => (c i).isCompact_carrier) (fun i => (c i).isClosed_carrier)
    (isOpen_interior.mem_nhdsSet.mpr (hK ▸ hKD))
  have htail (i : ℕ) : (c (N + i)).carrier ⊆ D :=
    (hanti (Nat.le_add_right N i)).trans (hN.trans interior_subset)
  let d : ℕ → EmbeddedClosedCell n D := fun i => (c (N + i)).subtype (htail i)
  have hd (i : ℕ) : (d i).carrier = Subtype.val ⁻¹' (c (N + i)).carrier :=
    (c (N + i)).subtype_carrier (htail i)
  have hdi (i : ℕ) : (d i).interiorSet = Subtype.val ⁻¹' (c (N + i)).interiorSet :=
    (c (N + i)).subtype_interiorSet (htail i)
  refine ⟨d, ?_, ?_⟩
  · intro i
    rw [hd, hdi]
    apply preimage_mono
    simpa only [Nat.add_assoc] using hc (N + i)
  · ext x
    constructor
    · intro hx
      apply mem_iInter.mpr
      intro i
      rw [hd]
      exact mem_iInter.mp (hK ▸ hx) (N + i)
    · intro hx
      change (x : X) ∈ K
      rw [hK]
      apply mem_iInter.mpr
      intro i
      have hi : (x : X) ∈ (c (N + i)).carrier := by
        have hi := mem_iInter.mp hx i
        rwa [hd] at hi
      exact hanti (Nat.le_add_left i N) hi

theorem isCellular.subtype {K D : Set X} (hK : isCellular n K)
    (_hD : IsClosed D) (hKD : K ⊆ interior D) :
    isCellular n (Subtype.val ⁻¹' K : Set D) :=
  hK.subtype_of_subset_interior hKD

theorem isCellular.exists_collapse_supported {Z : Type*} [MetricSpace Z] [CompactSpace Z]
    {K : Set Z} (hK : isCellular n K) (U : Set Z) (hU : IsOpen U) (hKU : K ⊆ U) :
    ∃ f : C(Z, Z), Function.Surjective f ∧ collapsesExactly f K ∧
      (∀ x ∉ U, f x = x) := by
  obtain ⟨c, hc, hK⟩ := hK
  have hanti : Antitone (fun i => (c i).carrier) :=
    antitone_nat_of_succ_le (fun i => (hc i).trans (c i).interiorSet_subset_carrier)
  obtain ⟨N, hN⟩ := exists_subset_nhds_of_isCompact'
    (V := fun i => (c i).carrier)
    (fun i j => ⟨max i j, hanti (le_max_left _ _), hanti (le_max_right _ _)⟩)
    (fun i => (c i).isCompact_carrier) (fun i => (c i).isClosed_carrier)
    (hU.mem_nhdsSet.mpr (hK ▸ hKU))
  have htail : K = ⋂ i, (c (N + i)).carrier := by
    rw [hK]
    ext x
    constructor
    · exact fun hx => mem_iInter.mpr (fun i => mem_iInter.mp hx (N + i))
    · intro hx
      exact mem_iInter.mpr (fun i => hanti (Nat.le_add_left i N) (mem_iInter.mp hx i))
  obtain ⟨f, hsurj, hfiber, hfix⟩ := exists_cellular_collapse_of_cells
    (fun i => c (N + i)) (fun i => by simpa only [Nat.add_assoc] using hc (N + i))
  refine ⟨f, hsurj, htail ▸ hfiber, ?_⟩
  intro x hx
  apply hfix
  exact fun hi => hx (hN ((c N).interiorSet_subset_carrier (by simpa using hi)))

end DifferentialGeometry.Topology
