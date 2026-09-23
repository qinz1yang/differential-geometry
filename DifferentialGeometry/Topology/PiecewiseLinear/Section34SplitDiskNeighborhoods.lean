import DifferentialGeometry.Topology.LocallyFiniteSeparation
import DifferentialGeometry.Topology.PiecewiseLinear.Section34EdgeEnds

open Set Topology

namespace DifferentialGeometry.Topology.PiecewiseLinear

universe u

variable {Ea : Type} [NormedAddCommGroup Ea] [NormedSpace ℝ Ea]
  {M₁ : Type u} [TopologicalSpace M₁] [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M₁]
  {U : Set M₁} {𝒦 𝒦' : LocallyFinitePLPieceIn Ea 3 M₁ U}
  {src srcBd : Section34CutLabelOf 𝒦 𝒦' → Set M₁}

theorem section34_splitDisks_pairwise_disjoint
    (hframe : Section34CutFrame U 𝒦 𝒦' src srcBd) :
    Pairwise fun e d : Section34EdgeIndex 𝒦 𝒦' =>
      Disjoint (src (.splitDisk e)) (src (.splitDisk d)) := by
  obtain ⟨ends, hends⟩ := exists_section34_edge_ends hframe
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, hinc, -⟩ :=
    hframe
  intro e d hed
  apply Set.disjoint_left.mpr
  intro x hxe hxd
  have hxab := (hends e).2.2.subset hxe
  have ha := hinc (ends e).1 d ⟨x, hxab.1, hxd⟩
  have hb := hinc (ends e).2 d ⟨x, hxab.2, hxd⟩
  have hesub : e.1 ⊆ d.1 := by
    intro z hz
    have hz' : z ∈ ((ends e).1.1 : Set Ea) ∪ ((ends e).2.1 : Set Ea) :=
      (hends e).2.1 ▸ hz
    exact hz'.elim (fun h => ha h) (fun h => hb h)
  apply hed
  apply Subtype.ext
  exact Finset.eq_of_subset_of_card_le hesub (by rw [e.2.2.1, d.2.2.1])

theorem exists_section34_splitDisk_neighborhoods [T2Space M₁]
    {M₂ : Type*} [MetricSpace M₂] {h : M₁ → M₂}
    (hU : IsOpen U) (hh : IsEmbedding (U.domRestrict h))
    (hframe : Section34CutFrame U 𝒦 𝒦' src srcBd) :
    ∃ O : Section34EdgeIndex 𝒦 𝒦' → Set M₁,
      (∀ e, IsOpen (O e)) ∧
      (∀ e, src (.splitDisk e) ⊆ O e) ∧
      (∀ e, O e ⊆ U) ∧
      (LocallyFinite fun e => {x : U | (x : M₁) ∈ O e}) ∧
      Pairwise fun e d => Disjoint (O e) (O d) := by
  have : TopologicalSpace.MetrizableSpace U := hh.metrizableSpace
  let : MetricSpace U := TopologicalSpace.metrizableSpaceMetric U
  have hdis := section34_splitDisks_pairwise_disjoint hframe
  obtain ⟨-, -, -, hcell, -, -, -, hLF, hcover, -⟩ := hframe
  have hsrcU : ∀ l, src l ⊆ U := fun l => (subset_iUnion src l).trans hcover.subset
  let F : Section34CutLabelOf 𝒦 𝒦' → Set U := fun l =>
    (Subtype.val : U → M₁) ⁻¹' src l
  have hFlf : LocallyFinite F := by
    intro x
    obtain ⟨V, hV, hfin⟩ := hLF x x.2
    refine ⟨Subtype.val ⁻¹' V, continuous_subtype_val.continuousAt hV, hfin.subset ?_⟩
    rintro l ⟨y, hyl, hyV⟩
    exact ⟨y, hyl, hyV⟩
  let D : Section34EdgeIndex 𝒦 𝒦' → Set U := fun e => F (.splitDisk e)
  have hDlf : LocallyFinite D :=
    hFlf.comp_injective (fun _ _ heq => Section34Label.splitDisk.inj heq)
  have hDclosed (e) : IsClosed (D e) :=
    (hcell (.splitDisk e)).isCompact.isClosed.preimage continuous_subtype_val
  have hDdis : Pairwise fun e d => Disjoint (D e) (D d) :=
    fun e d hed => (hdis hed).preimage Subtype.val
  obtain ⟨V, hVo, hDV, -, hVlf, hVdis⟩ :=
    DifferentialGeometry.Topology.exists_locallyFinite_pairwise_disjoint_open_supersets
      D hDclosed hDlf hDdis isOpen_univ (fun _ => subset_univ _)
  refine ⟨fun e => Subtype.val '' V e, fun e => hU.isOpenMap_subtype_val _ (hVo e),
    ?_, ?_, ?_, ?_⟩
  · intro e x hx
    exact ⟨⟨x, hsrcU _ hx⟩, hDV e hx, rfl⟩
  · rintro e x ⟨y, -, rfl⟩
    exact y.2
  · change LocallyFinite fun e => Subtype.val ⁻¹' (Subtype.val '' V e)
    simpa only [preimage_image_eq _ Subtype.val_injective] using hVlf
  · intro e d hed
    exact (Set.disjoint_image_iff Subtype.val_injective).mpr (hVdis hed)

end DifferentialGeometry.Topology.PiecewiseLinear
