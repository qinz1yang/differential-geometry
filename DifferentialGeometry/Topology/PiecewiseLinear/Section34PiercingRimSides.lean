import DifferentialGeometry.Topology.PiecewiseLinear.Section34AnnulusCircleDichotomy
import DifferentialGeometry.Topology.PiecewiseLinear.Section34PiercingEssentialGenerator
import DifferentialGeometry.Topology.PiecewiseLinear.Section34PiercingSideConnectivity

open Set Topology

namespace DifferentialGeometry.Topology.PiecewiseLinear

theorem closure_connectedComponentIn_subset_of_closed_partition
    {X : Type*} [TopologicalSpace X] {S T D₀ D₁ J : Set X}
    (h₀ : IsClosed D₀) (h₁ : IsClosed D₁) (hU : D₀ ∪ D₁ = S)
    (hI : D₀ ∩ D₁ = J) (hTS : T ⊆ S) (hTJ : Disjoint T J)
    {x : X} (hx : x ∈ T) (hx₀ : x ∈ D₀) :
    closure (connectedComponentIn T x) ⊆ D₀ := by
  have hsub := connectedComponentIn_subset T x
  have hcover : connectedComponentIn T x ⊆ D₀ ∪ D₁ := hU.symm ▸ hsub.trans hTS
  have hdis : connectedComponentIn T x ∩ (D₀ ∩ D₁) = ∅ := by
    rw [hI]
    exact (hTJ.mono_left hsub).inter_eq
  rcases isPreconnected_iff_subset_of_disjoint_closed.mp isPreconnected_connectedComponentIn
      D₀ D₁ h₀ h₁ hcover hdis with h | h
  · exact closure_minimal h h₀
  · exact False.elim (disjoint_left.mp hTJ hx (hI.subset ⟨hx₀, h (mem_connectedComponentIn hx)⟩))

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

theorem section34_second_rims_disjoint_first_boundary
    (hprep : Section34VertexPreparation U 𝒦 𝒦' h src Q ends Cp CpBd Cc CcBd Kcore Sn Tn Aa Ab₀ Ab₁
      Bb Bb₀ Bb₁ Bc Bc₀ Bc₁ ε)
    (hpack : Section34PiercingConditions U 𝒦 𝒦' h Q ends Cp CpBd Cc Sn Tn Aa Ab₀ Ab₁ Bb Bb₀
      Bb₁ Sp Tp cnt Pg G) (e : Section34EdgeIndex 𝒦 𝒦') :
    Disjoint (G (ends e).2 '' Bb₀ e ∪ G (ends e).2 '' Bb₁ e)
      (G (ends e).1 '' CpBd (ends e).1) := by
  have hann := (section34_piercing_annuli hprep hpack e).2
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, -, hBb, -⟩ := hprep
  obtain ⟨-, -, -, -, -, -, hmeet, -, hdis, -⟩ := hpack
  have hRdis : Disjoint (G (ends e).2 '' Bb₀ e ∪ G (ends e).2 '' Bb₁ e) (Tp e) := by
    rw [← image_union]
    exact (hdis e).2
  refine disjoint_left.mpr fun x hxR hxA => ?_
  have hxB := (union_subset hann.first_subset hann.second_subset) hxR
  exact disjoint_left.mp hRdis hxR
    (interior_subset (hmeet e ⟨hxA, image_mono (hBb e).1 hxB⟩).2)

theorem section34_opposite_second_rim_sides_of_essential_circle
    (hprep : Section34VertexPreparation U 𝒦 𝒦' h src Q ends Cp CpBd Cc CcBd Kcore Sn Tn Aa Ab₀ Ab₁
      Bb Bb₀ Bb₁ Bc Bc₀ Bc₁ ε)
    (hpack : Section34PiercingConditions U 𝒦 𝒦' h Q ends Cp CpBd Cc Sn Tn Aa Ab₀ Ab₁ Bb Bb₀
      Bb₁ Sp Tp cnt Pg G) (e : Section34EdgeIndex 𝒦 𝒦') {i : ℕ} (hi : i < cnt e)
    (hess : ¬ ∃ D : Set M₂, IsPLCellOn 2 D (Pg e i) ∧ D ⊆ G (ends e).2 '' Bb e) :
    (G (ends e).2 '' Bb₀ e ⊆ interior (G (ends e).1 '' Cp (ends e).1) ∧
      G (ends e).2 '' Bb₁ e ⊆ (G (ends e).1 '' Cp (ends e).1)ᶜ) ∨
    (G (ends e).2 '' Bb₀ e ⊆ (G (ends e).1 '' Cp (ends e).1)ᶜ ∧
      G (ends e).2 '' Bb₁ e ⊆ interior (G (ends e).1 '' Cp (ends e).1)) := by
  obtain ⟨D₀, D₁, hDU, hDI, hD₀, hD₁, hR₀, hR₁⟩ :=
    (section34_piercing_circle_disk_or_separating_ends hprep hpack e hi).resolve_left hess
  have hann := (section34_piercing_annuli hprep hpack e).2
  have hRdis := section34_second_rims_disjoint_first_boundary hprep hpack e
  obtain ⟨a, ha⟩ := hann.ends_nonempty.1
  obtain ⟨b, hb⟩ := hann.ends_nonempty.2
  have haT : a ∈ G (ends e).2 '' Bb e \ G (ends e).1 '' CpBd (ends e).1 :=
    ⟨hann.first_subset ha, disjoint_left.mp hRdis (Or.inl ha)⟩
  have hbT : b ∈ G (ends e).2 '' Bb e \ G (ends e).1 '' CpBd (ends e).1 :=
    ⟨hann.second_subset hb, disjoint_left.mp hRdis (Or.inr hb)⟩
  have hR₀C : G (ends e).2 '' Bb₀ e ⊆ connectedComponentIn
      (G (ends e).2 '' Bb e \ G (ends e).1 '' CpBd (ends e).1) a :=
    hann.isPreconnected_ends.1.subset_connectedComponentIn ha
      (fun _ hy => ⟨hann.first_subset hy, disjoint_left.mp hRdis (Or.inl hy)⟩)
  have hR₁C : G (ends e).2 '' Bb₁ e ⊆ connectedComponentIn
      (G (ends e).2 '' Bb e \ G (ends e).1 '' CpBd (ends e).1) b :=
    hann.isPreconnected_ends.2.subset_connectedComponentIn hb
      (fun _ hy => ⟨hann.second_subset hy, disjoint_left.mp hRdis (Or.inr hy)⟩)
  have hside₀ := (section34_trace_free_component_side hprep hpack e a).imp
    (fun h => hR₀C.trans h) (fun h => hR₀C.trans h)
  have hside₁ := (section34_trace_free_component_side hprep hpack e b).imp
    (fun h => hR₁C.trans h) (fun h => hR₁C.trans h)
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, hAa, hBb, -⟩ := id hprep
  obtain ⟨-, -, -, -, -, -, -, -, hBdis, -, -, -, -, -, hinside, houtside, -, hPg, -⟩ :=
    id hpack
  have hRdisT : Disjoint (G (ends e).2 '' Bb₀ e ∪ G (ends e).2 '' Bb₁ e) (Tp e) := by
    rw [← image_union]
    exact (hBdis e).2
  have haNotT : a ∉ Tp e := disjoint_left.mp hRdisT (Or.inl ha)
  have hbNotT : b ∉ Tp e := disjoint_left.mp hRdisT (Or.inr hb)
  have hAaBd : Aa e ⊆ CpBd (ends e).1 := by
    rw [(hAa e).1]
    exact inter_subset_left
  have hJBd : Pg e i ⊆ G (ends e).1 '' CpBd (ends e).1 :=
    fun _ hy => image_mono hAaBd (image_mono sdiff_subset ((hPg e i hi).2 hy).1)
  have hcap : closure (connectedComponentIn
      (G (ends e).2 '' Bb e \ G (ends e).1 '' CpBd (ends e).1) a) ⊆ D₀ := by
    apply closure_connectedComponentIn_subset_of_closed_partition hD₀.isCompact.isClosed
      hD₁.isCompact.isClosed hDU hDI (sdiff_subset.trans (image_mono (hBb e).1))
      (disjoint_left.mpr fun x hx hxJ => hx.2 (hJBd hxJ)) haT (hR₀ ha)
  have hbNotD₀ : b ∉ D₀ := fun hbD => hbT.2 (hJBd (hDI.subset ⟨hbD, hR₁ hb⟩))
  have hnotin : ¬ (a ∈ interior (G (ends e).1 '' Cp (ends e).1) ∧
      b ∈ interior (G (ends e).1 '' Cp (ends e).1)) := by
    rintro ⟨haA, hbA⟩
    obtain ⟨z, -, hcomp⟩ := hinside e
    have haC := hcomp a ⟨haT.1, interior_subset haA⟩ haNotT
    have hbC := hcomp b ⟨hbT.1, interior_subset hbA⟩ hbNotT
    have hba : b ∈ connectedComponentIn
        (G (ends e).2 '' Bb e ∩ G (ends e).1 '' Cp (ends e).1) a :=
      (connectedComponentIn_eq haC) ▸ hbC
    exact hbNotD₀ (hcap ((section34_inside_component_closure_eq hprep hpack e a
      ⟨haT.1, haA⟩).symm ▸ hba))
  have hnotout : ¬ (a ∈ (G (ends e).1 '' Cp (ends e).1)ᶜ ∧
      b ∈ (G (ends e).1 '' Cp (ends e).1)ᶜ) := by
    rintro ⟨haA, hbA⟩
    obtain ⟨z, -, hcomp⟩ := houtside e
    have haC := hcomp a ⟨haT.1, haA⟩ haNotT
    have hbC := hcomp b ⟨hbT.1, hbA⟩ hbNotT
    have hba : b ∈ connectedComponentIn
        (G (ends e).2 '' Bb e \ G (ends e).1 '' Cp (ends e).1) a :=
      (connectedComponentIn_eq haC) ▸ hbC
    exact hbNotD₀ (hcap (subset_closure
      ((section34_trace_free_component_eq_outside hprep hpack e a ⟨haT.1, haA⟩).symm ▸ hba)))
  rcases hside₀ with h₀ | h₀ <;> rcases hside₁ with h₁ | h₁
  · exact False.elim (hnotin ⟨h₀ ha, h₁ hb⟩)
  · exact Or.inl ⟨h₀, h₁⟩
  · exact Or.inr ⟨h₀, h₁⟩
  · exact False.elim (hnotout ⟨h₀ ha, h₁ hb⟩)

theorem section34_opposite_second_rim_sides
    (hprep : Section34VertexPreparation U 𝒦 𝒦' h src Q ends Cp CpBd Cc CcBd Kcore Sn Tn Aa Ab₀ Ab₁
      Bb Bb₀ Bb₁ Bc Bc₀ Bc₁ ε)
    (hpack : Section34PiercingConditions U 𝒦 𝒦' h Q ends Cp CpBd Cc Sn Tn Aa Ab₀ Ab₁ Bb Bb₀
      Bb₁ Sp Tp cnt Pg G) (e : Section34EdgeIndex 𝒦 𝒦') :
    (G (ends e).2 '' Bb₀ e ⊆ interior (G (ends e).1 '' Cp (ends e).1) ∧
      G (ends e).2 '' Bb₁ e ⊆ (G (ends e).1 '' Cp (ends e).1)ᶜ) ∨
    (G (ends e).2 '' Bb₀ e ⊆ (G (ends e).1 '' Cp (ends e).1)ᶜ ∧
      G (ends e).2 '' Bb₁ e ⊆ interior (G (ends e).1 '' Cp (ends e).1)) := by
  obtain ⟨i, hi, -, -, hess⟩ := exists_section34_piercing_circle_carrying_generators hprep hpack e
  exact section34_opposite_second_rim_sides_of_essential_circle hprep hpack e hi hess

end DifferentialGeometry.Topology.PiecewiseLinear
