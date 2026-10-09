import DifferentialGeometry.Topology.PiecewiseLinear.Section34DiskTraceDeletion
import DifferentialGeometry.Topology.PiecewiseLinear.Section34PiercingEssentialGenerator

open Set Topology

namespace DifferentialGeometry.Topology.PiecewiseLinear

universe u

variable {Ea : Type} [NormedAddCommGroup Ea] [NormedSpace ℝ Ea]
  {M₁ M₂ : Type u} [TopologicalSpace M₁] [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M₁]
  [MetricSpace M₂] [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M₂] {U : Set M₁} {h : M₁ → M₂}
  {𝒦 𝒦' : LocallyFinitePLPieceIn Ea 3 M₁ U}
  {src : Section34CutLabelOf 𝒦 𝒦' → Set M₁}
  {Q : Section34VertexIndex 𝒦 𝒦' → Set M₂}
  {Cp CpBd Cc CcBd Kcore : Section34VertexIndex 𝒦 𝒦' → Set M₁}
  {ε : Section34VertexIndex 𝒦 𝒦' → ℝ}
  {ends : Section34EdgeIndex 𝒦 𝒦' →
    Section34VertexIndex 𝒦 𝒦' × Section34VertexIndex 𝒦 𝒦'}
  {Sn Tn Aa Ab₀ Ab₁ Bb Bb₀ Bb₁ Bc Bc₀ Bc₁ : Section34EdgeIndex 𝒦 𝒦' → Set M₁}
  {Sp Tp : Section34EdgeIndex 𝒦 𝒦' → Set M₂} {cnt : Section34EdgeIndex 𝒦 𝒦' → ℕ}
  {Pg : Section34EdgeIndex 𝒦 𝒦' → ℕ → Set M₂}
  {G : Section34VertexIndex 𝒦 𝒦' → M₁ → M₂}

theorem exists_section34_strict_trace_subfamily_after_disk
    (hprep : Section34VertexPreparation U 𝒦 𝒦' h src Q ends Cp CpBd Cc CcBd Kcore Sn Tn Aa Ab₀ Ab₁
      Bb Bb₀ Bb₁ Bc Bc₀ Bc₁ ε)
    (hpack : Section34PiercingConditions U 𝒦 𝒦' h Q ends Cp CpBd Cc Sn Tn Aa Ab₀ Ab₁ Bb Bb₀
      Bb₁ Sp Tp cnt Pg G) (e : Section34EdgeIndex 𝒦 𝒦') {i : ℕ} (hi : i < cnt e)
    {D : Set M₂} (hD : IsPLCellOn 2 D (Pg e i)) (hDA : D ⊆ G (ends e).1 '' Aa e) :
    ∃ I : Set (Fin (cnt e)), I.Nonempty ∧ Nat.card I < cnt e ∧
      ((G (ends e).1 '' CpBd (ends e).1 ∩ G (ends e).2 '' CpBd (ends e).2) \ D) =
        ⋃ j : I, Pg e j.1.val ∧
      (∀ j : I, Disjoint D (Pg e j.1.val)) ∧
      IsClosed ((G (ends e).1 '' CpBd (ends e).1 ∩ G (ends e).2 '' CpBd (ends e).2) \ D) := by
  obtain ⟨k, hk, -, hgen, -⟩ := exists_section34_piercing_circle_carrying_generators hprep hpack e
  have htor := (section34_tubes_are_topological_solid_tori hprep hpack e).2
  obtain ⟨-, -, -, -, hCp, -, -, -, -, -, -, -, -, -, hAa, hBb, -⟩ := hprep
  obtain ⟨-, -, -, htube, -, -, hbound, -, -, -, hG, -, -, -, -, -, hcount, hPg, hdis, -⟩ :=
    hpack
  have hAB : G (ends e).1 '' Aa e ⊆ G (ends e).1 '' CpBd (ends e).1 :=
    image_mono ((hAa e).1 ▸ inter_subset_left)
  have hBB : G (ends e).2 '' Bb e ⊆ G (ends e).2 '' CpBd (ends e).2 :=
    image_mono (hBb e).1
  have hJ (j : Fin (cnt e)) : IsConnected (Pg e j.val) := by
    obtain ⟨T, hT⟩ := (hPg e j.val j.isLt).1
    exact T.piece.bijOn.image_eq ▸ hT.isConnected.image _ T.piece.continuousOn
  have hclosed (j : Fin (cnt e)) : IsClosed (Pg e j.val) := by
    obtain ⟨T, -⟩ := (hPg e j.val j.isLt).1
    exact T.piece.isCompact.isClosed
  have hJB (j : Fin (cnt e)) : Pg e j.val ⊆ G (ends e).1 '' CpBd (ends e).1 :=
    fun _ hx => hAB (image_mono sdiff_subset ((hPg e j.val j.isLt).2 hx).1)
  have hpair : Pairwise fun j k : Fin (cnt e) => Disjoint (Pg e j.val) (Pg e k.val) :=
    fun j k hne => hdis e j.val j.isLt k.val k.isLt (fun h => hne (Fin.ext h))
  obtain ⟨I, hcard, htrace, hsep, hclose⟩ :=
    ((hCp _).image (hG _)).exists_strict_trace_subfamily_after_disk ⟨i, hi⟩ hD
      (hDA.trans hAB) hJ hJB hclosed hpair
  have hfull : (⋃ j : Fin (cnt e), Pg e j.val) =
      G (ends e).1 '' CpBd (ends e).1 ∩ G (ends e).2 '' CpBd (ends e).2 := by
    apply Subset.antisymm
    · rintro x hx
      obtain ⟨j, hxj⟩ := mem_iUnion.mp hx
      exact ⟨hJB j hxj, hBB (image_mono sdiff_subset ((hPg e j.val j.isLt).2 hxj).2)⟩
    · intro x hx
      have hx' := (hbound e hx).1
      have hxann : x ∈ G (ends e).1 '' Aa e ∩ G (ends e).2 '' Bb e :=
        ⟨image_mono sdiff_subset hx'.1, image_mono sdiff_subset hx'.2⟩
      obtain ⟨j, hj, hxj⟩ := mem_iUnion₂.mp ((hcount e).2 ▸ hxann)
      exact mem_iUnion.mpr ⟨⟨j, hj⟩, hxj⟩
  have hDT : D ⊆ Tp e := by
    rw [(htube e).2]
    exact hDA.trans (image_mono ((hAa e).1 ▸ inter_subset_right))
  have hnot : ¬ Pg e k ⊆ D := fun hsub =>
    htor.not_carriesFundamentalGroupOnto_of_subset_isPLCellOn hD hDT
      (hJ ⟨k, hk⟩).nonempty hsub hgen
  have hne : I.Nonempty := by
    obtain ⟨x, hxJ, hxD⟩ := not_subset.mp hnot
    have hx : x ∈ (⋃ j : Fin (cnt e), Pg e j.val) \ D :=
      ⟨mem_iUnion.mpr ⟨⟨k, hk⟩, hxJ⟩, hxD⟩
    obtain ⟨j, -⟩ := mem_iUnion.mp (htrace ▸ hx)
    exact ⟨j.1, j.2⟩
  rw [hfull] at htrace hclose
  exact ⟨I, hne, by simpa only [Nat.card_fin] using hcard, htrace, hsep, hclose⟩

end DifferentialGeometry.Topology.PiecewiseLinear
