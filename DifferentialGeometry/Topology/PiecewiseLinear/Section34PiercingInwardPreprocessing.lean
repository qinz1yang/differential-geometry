import DifferentialGeometry.Topology.PiecewiseLinear.Section34CrossingPreservation
import DifferentialGeometry.Topology.PiecewiseLinear.Section34ModelMotionTransport
import DifferentialGeometry.Topology.PiecewiseLinear.Section34PiercingComponentTransport
import DifferentialGeometry.Topology.PiecewiseLinear.Section34PiercingConditionsAfterCancellation
import DifferentialGeometry.Topology.PiecewiseLinear.Section34SupportedVertexModification

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


theorem section34_piercing_conditions_after_inward_motion
    (hprep : Section34VertexPreparation U 𝒦 𝒦' h src Q ends Cp CpBd Cc CcBd Kcore Sn Tn Aa Ab₀ Ab₁
      Bb Bb₀ Bb₁ Bc Bc₀ Bc₁ ε)
    (hpack : Section34PiercingConditions U 𝒦 𝒦' h Q ends Cp CpBd Cc Sn Tn Aa Ab₀ Ab₁ Bb Bb₀
      Bb₁ Sp Tp cnt Pg G) (e₀ : Section34EdgeIndex 𝒦 𝒦') (φ : M₂ ≃ₜ M₂) {O : Set M₂}
    (hfix : EqOn φ id Oᶜ)
    (hO : closure O ⊆ interior (Sp e₀) ∩ interior (Q (ends e₀).1) ∩
      interior (Q (ends e₀).2))
    (hfirst : Disjoint (closure O) (G (ends e₀).1 '' CpBd (ends e₀).1))
    (hforeign : ∀ d, d ≠ e₀ → ((ends e₀).2 = (ends d).1 ∨ (ends e₀).2 = (ends d).2) →
      Disjoint (closure O) (G (ends e₀).2 '' Sn d))
    (hrim : Disjoint (closure O) (G (ends e₀).2 '' (Bb₀ e₀ ∪ Bb₁ e₀)))
    (hφ : IsPLOn 3 3 φ (interior (G (ends e₀).1 '' Cc (ends e₀).1)))
    (hcell : φ '' (G (ends e₀).1 '' Cp (ends e₀).1) = G (ends e₀).1 '' Cp (ends e₀).1)
    (hTp : MapsTo φ (Tp e₀) (Tp e₀)) :
    Section34PiercingConditions U 𝒦 𝒦' h Q ends Cp CpBd Cc Sn Tn Aa Ab₀ Ab₁ Bb Bb₀ Bb₁
      Sp Tp cnt Pg (section34VertexModification G (ends e₀).2 φ) := by
  let a := (ends e₀).1
  let b := (ends e₀).2
  let G' := section34VertexModification G b φ
  obtain ⟨-, hCc, hsub, -, hCp, -, -, -, hends, -, -, htor, hSnCc, -, hAa, hBb, -⟩ := id hprep
  obtain ⟨hG, hQ, hSn, htubes, hlf, hdisj, hmeetOld, hsideOld, hBbOld, hgraph, hGp,
    hmark, -, -, hcompInOld, hcompOutOld, htraceOld, hsphereOld, hdisjtrace, hcrossOld, -⟩ :=
    id hpack
  have hab : a ≠ b := (hends e₀).1
  have hGa : G' a = G a := section34VertexModification_of_ne G b φ hab
  have hGb : G' b = φ ∘ G b := section34VertexModification_self G b φ
  have hGother {w : Section34VertexIndex 𝒦 𝒦'} (hw : w ≠ b) : G' w = G w :=
    section34VertexModification_of_ne G b φ hw
  have hOsp : O ⊆ interior (Sp e₀) := fun x hx => (hO (subset_closure hx)).1.1
  have hfixSp : EqOn φ id (interior (Sp e₀))ᶜ :=
    hfix.mono (compl_subset_compl.mpr hOsp)
  have hoff : ∀ w, EqOn (G' w) (G w) {x ∈ Cc w | G w x ∉ interior (Sp e₀)} :=
    fun w x hx => section34VertexModification_eqOn G b φ hfixSp w hx.2
  have hin : ∀ w, ∀ x ∈ Cp w, G w x ∈ interior (Sp e₀) → G' w x ∈ interior (Sp e₀) :=
    fun w x _ hx => (section34VertexModification_mem_iff G b φ hfixSp w x).mpr hx
  have hSpCc : Sp e₀ ⊆ G a '' Cc a := by
    rw [(htubes e₀).1]
    exact image_mono (hSnCc e₀ a (Or.inl rfl))
  have hOdom : closure O ⊆ interior (G a '' Cc a) :=
    fun x hx => interior_mono hSpCc (hO hx).1.1
  have hfixCl : EqOn φ id (closure O)ᶜ :=
    hfix.mono (compl_subset_compl.mpr subset_closure)
  have hG' : ∀ w, IsPLHomeomorphInto 3 (G' w) (Cc w) := by
    intro w
    by_cases hw : w = b
    · subst w
      rw [hGb]
      exact (hG b).postcomp_of_supported_isPLOn (hCc b) φ hφ isOpen_interior
        isClosed_closure hOdom hfixCl
    · rw [hGother hw]
      exact hG w
  have hGp' : ∀ w, IsPLHomeomorphInto 3 (G' w) (Cp w) :=
    fun w => (hG' w).mono_of_isPLCellOn (hCp w) (hsub w).2.1
  have hfixS (S : Set M₁) (hS : Disjoint (closure O) (G b '' S)) : EqOn (G' b) (G b) S := by
    intro x hx
    rw [hGb, Function.comp_apply]
    exact hfix fun hy => disjoint_left.mp hS (subset_closure hy) ⟨x, hx, rfl⟩
  have hforeignSn : ∀ d, d ≠ e₀ →
      EqOn (G' (ends d).1) (G (ends d).1) (Sn d) ∧
        EqOn (G' (ends d).2) (G (ends d).2) (Sn d) := by
    intro d hd
    have hboth : ∀ w, w = (ends d).1 ∨ w = (ends d).2 → EqOn (G' w) (G w) (Sn d) := by
      intro w hw
      by_cases hwb : w = b
      · subst w
        exact hfixS (Sn d) (hforeign d hd hw)
      · rw [hGother hwb]
        exact fun _ _ => rfl
    exact ⟨hboth _ (Or.inl rfl), hboth _ (Or.inr rfl)⟩
  have hφQa : φ '' Q a = Q a := image_eq_of_homeomorph_eqOn_compl_of_subset φ hfix
    (fun x hx => interior_subset (hO (subset_closure hx)).1.2)
  have hφQb : φ '' Q b = Q b := image_eq_of_homeomorph_eqOn_compl_of_subset φ hfix
    (fun x hx => interior_subset (hO (subset_closure hx)).2)
  have hQ' : ∀ w, G' w '' Cc w ⊆ Q w := by
    intro w
    by_cases hw : w = b
    · subst w
      rw [hGb, image_comp, ← hφQb]
      exact image_mono (hQ b)
    · rw [hGother hw]
      exact hQ w
  have hSn' : ∀ e, G' (ends e).2 '' Sn e ⊆ Q (ends e).1 ∧
      G' (ends e).1 '' Sn e ⊆ Q (ends e).2 := by
    intro e
    by_cases he : e = e₀
    · subst e
      change G' b '' Sn e₀ ⊆ Q a ∧ G' a '' Sn e₀ ⊆ Q b
      rw [hGa, hGb, image_comp]
      exact ⟨fun x hx => hφQa ▸ image_mono (hSn e₀).1 hx, (hSn e₀).2⟩
    · rw [(hforeignSn e he).1.image_eq, (hforeignSn e he).2.image_eq]
      exact hSn e
  have hfixA : EqOn φ id (G a '' CpBd a) := fun x hx =>
    hfix fun hmem => disjoint_left.mp hfirst (subset_closure hmem) hx
  have hASub : Aa e₀ ⊆ CpBd a := (hAa e₀).1 ▸ inter_subset_left
  have hinter (S B : Set M₂) (hS : S ⊆ G a '' CpBd a) : S ∩ φ '' B = S ∩ B := by
    apply Subset.antisymm
    · rintro x ⟨hx, y, hy, hyx⟩
      exact ⟨hx, φ.injective (hyx.trans (hfixA (hS hx)).symm) ▸ hy⟩
    · intro x hx
      exact ⟨hx.1, x, hx.2, hfixA (hS hx.1)⟩
  have hbd : G' a '' CpBd a ∩ G' b '' CpBd b = G a '' CpBd a ∩ G b '' CpBd b := by
    rw [hGa, hGb, image_comp]
    exact hinter _ _ Subset.rfl
  have htrace : G' a '' Aa e₀ ∩ G' b '' Bb e₀ = G a '' Aa e₀ ∩ G b '' Bb e₀ := by
    rw [hGa, hGb, image_comp]
    exact hinter _ _ (image_mono hASub)
  have hmeet : G' a '' CpBd a ∩ G' b '' CpBd b ⊆
      G' a '' (Aa e₀ \ (Ab₀ e₀ ∪ Ab₁ e₀)) ∩
        G' b '' (Bb e₀ \ (Bb₀ e₀ ∪ Bb₁ e₀)) ∩ interior (Tp e₀) := by
    intro y hy
    have hold := hbd ▸ hy
    have hm := hmeetOld e₀ hold
    refine ⟨⟨?_, ?_⟩, hm.2⟩
    · rw [hGa]
      exact hm.1.1
    · obtain ⟨x, hx, hxy⟩ := hm.1.2
      refine ⟨x, hx, ?_⟩
      rw [hGb, Function.comp_apply, hxy, hfixA hold.1]
      rfl
  have hA₀ : G a '' Ab₀ e₀ ⊆ G a '' CpBd a :=
    image_mono ((hAa e₀).2.first_subset.trans hASub)
  have hA₁ : G a '' Ab₁ e₀ ⊆ G a '' CpBd a :=
    image_mono ((hAa e₀).2.second_subset.trans hASub)
  have hside : G' a '' Ab₀ e₀ ⊆ interior (G' b '' Cp b) ∧
      Disjoint (G' a '' Ab₁ e₀) (G' b '' Cp b) := by
    rw [hGa, hGb, image_comp, ← φ.image_interior]
    refine ⟨?_, disjoint_iff_inter_eq_empty.mpr ?_⟩
    · intro y hy
      exact ⟨y, (hsideOld e₀).1 hy, hfixA (hA₀ hy)⟩
    · rw [hinter _ _ hA₁]
      exact (hsideOld e₀).2.inter_eq
  have hcomponents := section34_piercing_components_of_preserving_first_cell hpack e₀ φ hcell
    (fun _ _ hnot hmem => hnot (hTp hmem))
  have htubes' : ∀ e, Sp e = G' (ends e).1 '' Sn e ∧ Tp e = G' (ends e).1 '' Tn e := by
    intro e
    by_cases he : e = e₀
    · subst e
      change Sp e₀ = G' a '' Sn e₀ ∧ Tp e₀ = G' a '' Tn e₀
      rw [hGa]
      exact htubes e₀
    · rw [(hforeignSn e he).1.image_eq,
        ((hforeignSn e he).1.mono ((htor e).1.trans interior_subset)).image_eq]
      exact htubes e
  have hforeignAnn := section34Step_eqOn_other_annuli hprep hpack G' e₀ hoff
  have htrace' : ∀ e, 0 < cnt e ∧
      G' (ends e).1 '' Aa e ∩ G' (ends e).2 '' Bb e = ⋃ i < cnt e, Pg e i := by
    intro e
    by_cases he : e = e₀
    · subst e
      exact ⟨(htraceOld e₀).1, htrace.trans (htraceOld e₀).2⟩
    · rw [(hforeignAnn e he).1.image_eq, (hforeignAnn e he).2.image_eq]
      exact htraceOld e
  have hsphere' : ∀ e, ∀ i < cnt e, IsPolyhedralSphere (n := 3) 1 (Pg e i) ∧
      Pg e i ⊆ G' (ends e).1 '' (Aa e \ (Ab₀ e ∪ Ab₁ e)) ∩
        G' (ends e).2 '' (Bb e \ (Bb₀ e ∪ Bb₁ e)) := by
    intro e i hi
    by_cases he : e = e₀
    · subst e
      refine ⟨(hsphereOld e₀ i hi).1, ?_⟩
      intro x hx
      have hxtrace : x ∈ G' a '' Aa e₀ ∩ G' b '' Bb e₀ :=
        (htrace' e₀).2 ▸ mem_iUnion₂.mpr ⟨i, hi, hx⟩
      exact (hmeet ⟨image_mono hASub hxtrace.1, image_mono (hBb e₀).1 hxtrace.2⟩).1
    · rw [((hforeignAnn e he).1.mono sdiff_subset).image_eq,
        ((hforeignAnn e he).2.mono sdiff_subset).image_eq]
      exact hsphereOld e i hi
  have hcross' : ∀ e, ∀ y ∈ G' (ends e).1 '' Aa e ∩ G' (ends e).2 '' Bb e,
      ∃ c ∈ (plGroupoid 3).maximalAtlas M₂, y ∈ c.source ∧
        HasPLCrossingAt (c '' (G' (ends e).1 '' Aa e ∩ c.source))
          (c '' (G' (ends e).2 '' Bb e ∩ c.source)) (c y) := by
    intro e y hy
    by_cases he : e = e₀
    · subst e
      have hyold := htrace ▸ hy
      obtain ⟨c, hc, hyc, hcross⟩ := hcrossOld e₀ y hyold
      refine ⟨c, hc, hyc, ?_⟩
      change HasPLCrossingAt (c '' (G' a '' Aa e₀ ∩ c.source))
        (c '' (G' b '' Bb e₀ ∩ c.source)) (c y)
      rw [hGa, hGb, image_comp]
      exact hcross.image_right_of_fixed_neighborhood φ isClosed_closure.isOpen_compl hfixCl
        (fun hyO => disjoint_left.mp hfirst hyO (image_mono hASub hyold.1)) hyc
    · rw [(hforeignAnn e he).1.image_eq, (hforeignAnn e he).2.image_eq] at hy ⊢
      exact hcrossOld e y hy
  have hmarkers := (section34Step_eqOn_marker_and_boundary hprep hpack G' e₀ hoff).1
  have hmark' : ∀ w e, Disjoint (G' w '' simplexBody 𝒦' w.1) (Sp e) := by
    intro w e
    rw [(hmarkers w).image_eq]
    exact hmark w e
  refine ⟨hG', hQ', hSn', htubes', hlf, hdisj, ?_, ?_, ?_, hgraph, hGp', hmark',
    section34Step_support_disjoint_other_boundaries hprep hpack G' e₀ hoff hin,
    section34Step_disjoint_cells hprep hpack G' e₀ hoff hin, ?_, ?_, htrace', hsphere',
    hdisjtrace, hcross', section34Step_lenses_disjoint hprep hpack G' e₀ hoff hin,
    section34Step_marker_exclusion hprep hpack G' e₀ hoff hin⟩
  · intro e
    by_cases he : e = e₀
    · subst e
      exact hmeet
    · exact section34Step_other_boundary_containment hprep hpack G' e₀ hoff hin e he
  · intro e
    by_cases he : e = e₀
    · subst e
      exact hside
    · exact section34Step_other_piercing_sides hprep hpack G' e₀ hoff hin hGp' e he
  · intro e
    by_cases he : e = e₀
    · subst e
      refine ⟨?_, ?_⟩
      · rintro _ ⟨x, hx, rfl⟩
        exact hin _ x ((hCp _).boundary_subset ((hBb e₀).1 hx))
          ((hBbOld e₀).1 ⟨x, hx, rfl⟩)
      · rw [(hfixS _ hrim).image_eq]
        exact (hBbOld e₀).2
    · rw [(hforeignAnn e he).2.image_eq,
        ((hforeignAnn e he).2.mono (union_subset (hBb e).2.first_subset
          (hBb e).2.second_subset)).image_eq]
      exact hBbOld e
  · intro e
    by_cases he : e = e₀
    · subst e
      change ∃ y₀ ∈ G' b '' Bb e₀ ∩ G' a '' Cp a,
        ∀ z ∈ G' b '' Bb e₀ ∩ G' a '' Cp a, z ∉ Tp e₀ →
          z ∈ connectedComponentIn (G' b '' Bb e₀ ∩ G' a '' Cp a) y₀
      rw [hGa, hGb]
      exact hcomponents.1
    · rw [(section34Step_other_component_sets hprep hpack G' e₀ hoff hin e he).1]
      exact hcompInOld e
  · intro e
    by_cases he : e = e₀
    · subst e
      change ∃ y₀ ∈ G' b '' Bb e₀ \ G' a '' Cp a,
        ∀ z ∈ G' b '' Bb e₀ \ G' a '' Cp a, z ∉ Tp e₀ →
          z ∈ connectedComponentIn (G' b '' Bb e₀ \ G' a '' Cp a) y₀
      rw [hGa, hGb]
      exact hcomponents.2
    · rw [(section34Step_other_component_sets hprep hpack G' e₀ hoff hin e he).2]
      exact hcompOutOld e

end DifferentialGeometry.Topology.PiecewiseLinear
