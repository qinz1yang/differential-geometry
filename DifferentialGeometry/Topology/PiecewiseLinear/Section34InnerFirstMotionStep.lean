import DifferentialGeometry.Topology.PiecewiseLinear.Section34InnerFirstMotionComponents
import DifferentialGeometry.Topology.PiecewiseLinear.Section34PiercingConditionsAfterCancellation
import DifferentialGeometry.Topology.PiecewiseLinear.Section34ModelMotionTransport
import DifferentialGeometry.Topology.PiecewiseLinear.Section34SupportedVertexModification
import DifferentialGeometry.Topology.PiecewiseLinear.Section34CrossingPreservation
import DifferentialGeometry.Topology.PiecewiseLinear.Section34InnerTubeRims
import DifferentialGeometry.Topology.PiecewiseLinear.Section34SurvivingTrace

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

theorem section34_removal_step_of_inner_first_motion
    (hprep : Section34VertexPreparation U 𝒦 𝒦' h src Q ends Cp CpBd Cc CcBd Kcore Sn Tn Aa Ab₀ Ab₁
      Bb Bb₀ Bb₁ Bc Bc₀ Bc₁ ε)
    (hpack : Section34PiercingConditions U 𝒦 𝒦' h Q ends Cp CpBd Cc Sn Tn Aa Ab₀ Ab₁ Bb Bb₀
      Bb₁ Sp Tp cnt Pg G) (e₀ : Section34EdgeIndex 𝒦 𝒦')
    (I : Set (Fin (cnt e₀))) (hcard : Nat.card I < cnt e₀)
    (φ : M₂ ≃ₜ M₂) {K : Set M₂} (hK : IsCompact K) (hKT : K ⊆ interior (Tp e₀))
    (hfix : EqOn φ id Kᶜ) (hφ : IsPLOn 3 3 φ (interior (G (ends e₀).1 '' Cc (ends e₀).1)))
    (hkeep : ∀ j : I, Disjoint K (Pg e₀ j.1.val))
    (hcancel : φ '' (G (ends e₀).1 '' CpBd (ends e₀).1) ∩ G (ends e₀).2 '' CpBd (ends e₀).2 =
      ⋃ j : I, Pg e₀ j.1.val) :
    ∃ (G' : Section34VertexIndex 𝒦 𝒦' → M₁ → M₂) (cnt' : Section34EdgeIndex 𝒦 𝒦' → ℕ)
      (Pg' : Section34EdgeIndex 𝒦 𝒦' → ℕ → Set M₂),
      Section34PiercingConditions U 𝒦 𝒦' h Q ends Cp CpBd Cc Sn Tn Aa Ab₀ Ab₁ Bb Bb₀ Bb₁
          Sp Tp cnt' Pg' G' ∧ cnt' e₀ < cnt e₀ ∧
        (∀ e, e ≠ e₀ → cnt' e = cnt e) ∧
        (∀ w, EqOn (G' w) (G w) {x ∈ Cc w | G w x ∉ interior (Sp e₀)}) ∧
        ∀ e, e ≠ e₀ → G' (ends e).1 '' Aa e = G (ends e).1 '' Aa e ∧
          G' (ends e).2 '' Bb e = G (ends e).2 '' Bb e := by
  have hrim : Disjoint K (G (ends e₀).1 '' (Ab₀ e₀ ∪ Ab₁ e₀)) :=
    disjoint_interior_frontier.mono hKT
      (section34_first_rims_subset_inner_frontier hprep hpack e₀)
  have hfixRims : EqOn φ id (G (ends e₀).1 '' (Ab₀ e₀ ∪ Ab₁ e₀)) :=
    fun _ hx => hfix (disjoint_right.mp hrim hx)
  obtain ⟨x, hx⟩ := section34_modified_first_boundary_trace_nonempty hprep hpack e₀ φ hfixRims
  obtain ⟨j, -⟩ := mem_iUnion.mp (hcancel.subset hx)
  have hne : I.Nonempty := ⟨j.1, j.2⟩
  let a := (ends e₀).1
  let b := (ends e₀).2
  let G' := section34VertexModification G a φ
  have hTS := section34_inner_tube_subset_interior_outer hprep hpack e₀
  have hKS : K ⊆ interior (Sp e₀) := hKT.trans (interior_subset.trans hTS)
  have hfixS : EqOn φ id (interior (Sp e₀))ᶜ :=
    hfix.mono (compl_subset_compl.mpr hKS)
  have hfixT : EqOn φ id (interior (Tp e₀))ᶜ :=
    hfix.mono (compl_subset_compl.mpr hKT)
  have hoff : ∀ w, EqOn (G' w) (G w) {x ∈ Cc w | G w x ∉ interior (Sp e₀)} :=
    fun w x hx => section34VertexModification_eqOn G a φ hfixS w hx.2
  have hin : ∀ w, ∀ x ∈ Cp w, G w x ∈ interior (Sp e₀) → G' w x ∈ interior (Sp e₀) :=
    fun w x _ hx => (section34VertexModification_mem_iff G a φ hfixS w x).mpr hx
  have hQ' := section34VertexModification_carrier hprep hpack e₀ φ hfixS
  have hSn' := section34VertexModification_cross_carriers hprep hpack e₀ φ hfixS
  have htubes := section34VertexModification_tube_images hprep hpack e₀ φ hfixT
  obtain ⟨-, hCc, -, -, -, -, -, -, hends, -, -, -, hSnCc, -, hAa, hBb, -⟩ := id hprep
  obtain ⟨hG, -, -, htube, -, -, hmeetOld, hsideOld, hBbOld, -, -, -, -, -, -, -, -, hPg,
    hdis, hcross, -⟩ := id hpack
  have hGa : G' a = φ ∘ G a := section34VertexModification_self G a φ
  have hGb : G' b = G b := section34VertexModification_of_ne G a φ (hends e₀).1.symm
  have hGother {w : Section34VertexIndex 𝒦 𝒦'} (hw : w ≠ a) : G' w = G w :=
    section34VertexModification_of_ne G a φ hw
  have hSpCc : Sp e₀ ⊆ G a '' Cc a := by
    rw [(htube e₀).1]
    exact image_mono (hSnCc e₀ a (Or.inl rfl))
  have hG' : ∀ w, IsPLHomeomorphInto 3 (G' w) (Cc w) := by
    intro w
    by_cases hw : w = a
    · subst w
      rw [hGa]
      exact (hG a).postcomp_of_supported_isPLOn (hCc a) φ hφ isOpen_interior hK.isClosed
        (hKS.trans (interior_mono hSpCc)) hfix
    · rw [hGother hw]
      exact hG w
  have hAB : Aa e₀ ⊆ CpBd a := (hAa e₀).1 ▸ inter_subset_left
  have hBB : Bb e₀ ⊆ CpBd b := (hBb e₀).1
  have hfixPg (j : I) : EqOn φ id (Pg e₀ j.1.val) :=
    fun _ hx => hfix (disjoint_right.mp (hkeep j) hx)
  have hfull : G' a '' CpBd a ∩ G' b '' CpBd b = ⋃ j : I, Pg e₀ j.1.val := by
    rw [hGa, hGb, image_comp]
    exact hcancel
  have hmeet : G' a '' CpBd a ∩ G' b '' CpBd b ⊆
      G' a '' (Aa e₀ \ (Ab₀ e₀ ∪ Ab₁ e₀)) ∩
        G' b '' (Bb e₀ \ (Bb₀ e₀ ∪ Bb₁ e₀)) ∩ interior (Tp e₀) := by
    intro x hx
    obtain ⟨j, hxj⟩ := mem_iUnion.mp (hfull ▸ hx)
    have hold := (hPg e₀ j.1.val j.1.isLt).2 hxj
    have hxbd : x ∈ G a '' CpBd a ∩ G b '' CpBd b :=
      ⟨image_mono (sdiff_subset.trans hAB) hold.1, image_mono (sdiff_subset.trans hBB) hold.2⟩
    rw [hGa, hGb, image_comp]
    exact ⟨⟨⟨x, hold.1, hfixPg j hxj⟩, hold.2⟩, (hmeetOld e₀ hxbd).2⟩
  have hfixRim : EqOn (G' a) (G a) (Ab₀ e₀ ∪ Ab₁ e₀) := by
    intro x hx
    rw [hGa, Function.comp_apply]
    exact hfix (disjoint_right.mp hrim ⟨x, hx, rfl⟩)
  have hside : G' a '' Ab₀ e₀ ⊆ interior (G' b '' Cp b) ∧
      Disjoint (G' a '' Ab₁ e₀) (G' b '' Cp b) := by
    rw [(hfixRim.mono subset_union_left).image_eq,
      (hfixRim.mono subset_union_right).image_eq, hGb]
    exact hsideOld e₀
  have hBb' : Disjoint (G' b '' (Bb₀ e₀ ∪ Bb₁ e₀)) (Tp e₀) := by
    rw [hGb]
    exact (hBbOld e₀).2
  have htr : G' a '' Aa e₀ ∩ G' b '' Bb e₀ = ⋃ j : I, Pg e₀ j.1.val := by
    apply Subset.antisymm
    · exact fun _ hx => hfull ▸ And.intro (image_mono hAB hx.1) (image_mono hBB hx.2)
    · intro x hx
      have hm := hmeet (hfull.symm ▸ hx)
      exact ⟨image_mono sdiff_subset hm.1.1, image_mono sdiff_subset hm.1.2⟩
  have hCcross : ∀ y ∈ G' a '' Aa e₀ ∩ G' b '' Bb e₀,
      ∃ c ∈ (plGroupoid 3).maximalAtlas M₂, y ∈ c.source ∧
        HasPLCrossingAt (c '' (G' a '' Aa e₀ ∩ c.source))
          (c '' (G' b '' Bb e₀ ∩ c.source)) (c y) := by
    intro y hy
    obtain ⟨j, hyj⟩ := mem_iUnion.mp (htr ▸ hy)
    have hold := (hPg e₀ j.1.val j.1.isLt).2 hyj
    obtain ⟨c, hc, hyc, hcrossc⟩ := hcross e₀ y
      ⟨image_mono sdiff_subset hold.1, image_mono sdiff_subset hold.2⟩
    refine ⟨c, hc, hyc, ?_⟩
    rw [hGa, hGb, image_comp]
    exact (hcrossc.symm.image_right_of_fixed_neighborhood φ hK.isClosed.isOpen_compl hfix
      (disjoint_right.mp (hkeep j) hyj) hyc).symm
  have hcomponents := section34_piercing_components_of_inner_first_motion hprep hpack e₀ φ
    (hfixT.mono (compl_subset_compl.mpr interior_subset))
    (fun x hx => by
      obtain ⟨j, hxj⟩ := mem_iUnion.mp (hcancel.subset ⟨hx.1, image_mono hBB hx.2⟩)
      exact image_mono (sdiff_subset.trans hAB) ((hPg e₀ j.1.val j.1.isLt).2 hxj).1)
    (by
      obtain ⟨j, hj⟩ := hne
      obtain ⟨P, hP⟩ := (hPg e₀ j.val j.isLt).1
      obtain ⟨x, hx⟩ := P.piece.bijOn.image_eq ▸ hP.nonempty.image P.piece.map
      have hold := (hPg e₀ j.val j.isLt).2 hx
      refine ⟨x, ⟨image_mono (sdiff_subset.trans hAB) hold.1,
        image_mono sdiff_subset hold.2⟩, ?_⟩
      filter_upwards [hK.isClosed.isOpen_compl.mem_nhds
        (disjoint_right.mp (hkeep ⟨j, hj⟩) hx)] with y hy
      exact hfix hy)
  have hcompIn : ∃ z ∈ G' b '' Bb e₀ ∩ G' a '' Cp a,
      ∀ y ∈ G' b '' Bb e₀ ∩ G' a '' Cp a, y ∉ Tp e₀ →
        y ∈ connectedComponentIn (G' b '' Bb e₀ ∩ G' a '' Cp a) z := by
    rw [hGa, hGb, image_comp]
    exact hcomponents.1
  have hcompOut : ∃ z ∈ G' b '' Bb e₀ \ G' a '' Cp a,
      ∀ y ∈ G' b '' Bb e₀ \ G' a '' Cp a, y ∉ Tp e₀ →
        y ∈ connectedComponentIn (G' b '' Bb e₀ \ G' a '' Cp a) z := by
    rw [hGa, hGb, image_comp]
    exact hcomponents.2
  let _ : Nonempty I := hne.to_subtype
  let r : I ≃ Fin (Nat.card I) := Nat.equivFinOfCardPos Nat.card_pos.ne'
  let C : Fin (Nat.card I) → Set M₂ := fun j => Pg e₀ (r.symm j).1.val
  have hcover : (⋃ j, C j) = ⋃ j : I, Pg e₀ j.1.val := by
    apply Subset.antisymm
    · exact iUnion_subset fun j => subset_iUnion (fun k : I => Pg e₀ k.1.val) (r.symm j)
    · refine iUnion_subset fun j => ?_
      simpa only [C, r.symm_apply_apply] using (subset_iUnion C (r j))
  have hCdis : Pairwise fun j k : Fin (Nat.card I) => Disjoint (C j) (C k) := by
    intro j k hjk
    exact hdis e₀ _ (r.symm j).1.isLt _ (r.symm k).1.isLt
      (fun h => hjk (r.symm.injective (Subtype.ext (Fin.ext h))))
  obtain ⟨cnt', Pg', hp, hlt, hcnt, hann⟩ := piercing_conditions_after_cancellation hprep hpack
    G' e₀ (Nat.card I) C hcard hoff hin (htubes e₀) hG' hQ' hSn' hmeet hside hBb'
    hcompIn hcompOut (htr.trans hcover.symm)
    (fun j => (hPg e₀ (r.symm j).1.val (r.symm j).1.isLt).1) hCdis hCcross
  exact ⟨G', cnt', Pg', hp, hlt, hcnt, hoff, hann⟩

end DifferentialGeometry.Topology.PiecewiseLinear
