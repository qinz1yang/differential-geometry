import DifferentialGeometry.Topology.PiecewiseLinear.Section34SingleCrossingComponents
import DifferentialGeometry.Topology.PiecewiseLinear.Section34SecondMotionCarriers
import DifferentialGeometry.Topology.PiecewiseLinear.Section34DiskMotionTrace
import DifferentialGeometry.Topology.PiecewiseLinear.Section34PiercingConditionsAfterCancellation
import DifferentialGeometry.Topology.PiecewiseLinear.Section34PiercingSideConnectivity

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

theorem section34_second_motion_cross_carriers_of_mapsTo
    (hprep : Section34VertexPreparation U 𝒦 𝒦' h src Q ends Cp CpBd Cc CcBd Kcore Sn Tn Aa Ab₀ Ab₁
      Bb Bb₀ Bb₁ Bc Bc₀ Bc₁ ε)
    (hpack : Section34PiercingConditions U 𝒦 𝒦' h Q ends Cp CpBd Cc Sn Tn Aa Ab₀ Ab₁ Bb Bb₀
      Bb₁ Sp Tp cnt Pg G) (e₀ : Section34EdgeIndex 𝒦 𝒦') (ψ : M₂ ≃ₜ M₂)
    (hfix : EqOn ψ id (interior (Sp e₀))ᶜ)
    (hforeign : ∀ e, e ≠ e₀ → (ends e).2 = (ends e₀).2 →
      MapsTo ψ (G (ends e₀).2 '' Sn e ∩ interior (Sp e₀)) (Q (ends e).1)) :
    let G' := section34VertexModification G (ends e₀).2 ψ
    ∀ e, G' (ends e).2 '' Sn e ⊆ Q (ends e).1 ∧
      G' (ends e).1 '' Sn e ⊆ Q (ends e).2 := by
  let a := (ends e₀).1
  let b := (ends e₀).2
  let G' := section34VertexModification G b ψ
  obtain ⟨-, -, -, -, -, -, -, -, hends, -, -, -, hSnCc, -⟩ := hprep
  obtain ⟨-, hQ, hSn, htube, -, hdis, -⟩ := hpack
  have hGb : G' b = ψ ∘ G b := section34VertexModification_self G b ψ
  have hGother {w : Section34VertexIndex 𝒦 𝒦'} (hw : w ≠ b) : G' w = G w :=
    section34VertexModification_of_ne G b ψ hw
  have hSpQa : interior (Sp e₀) ⊆ Q a := by
    rw [(htube e₀).1]
    exact interior_subset.trans ((image_mono (hSnCc e₀ a (Or.inl rfl))).trans (hQ a))
  have hψQa : ψ '' Q a = Q a :=
    image_eq_of_homeomorph_eqOn_compl_of_subset ψ hfix hSpQa
  have hfirst (e : Section34EdgeIndex 𝒦 𝒦') :
      G' (ends e).1 '' Sn e = G (ends e).1 '' Sn e := by
    by_cases heb : (ends e).1 = b
    · have he : e ≠ e₀ := by
        intro h
        subst e
        exact (hends e₀).1 heb
      have hfixed : EqOn ψ id (G (ends e).1 '' Sn e) := by
        intro x hx
        apply hfix
        exact fun hin => disjoint_left.mp (hdis e e₀ he)
          ((htube e).1.symm ▸ hx) (interior_subset hin)
      rw [show G' (ends e).1 = ψ ∘ G (ends e).1 by
        rw [heb]; exact section34VertexModification_self G b ψ, image_comp]
      exact hfixed.image_eq.trans (image_id' _)
    · rw [hGother heb]
  change ∀ e, G' (ends e).2 '' Sn e ⊆ Q (ends e).1 ∧
    G' (ends e).1 '' Sn e ⊆ Q (ends e).2
  intro e
  refine ⟨?_, by rw [hfirst]; exact (hSn e).2⟩
  by_cases he : e = e₀
  · subst e
    change (section34VertexModification G b ψ b) '' Sn e₀ ⊆ Q a
    rw [section34VertexModification_self, image_comp]
    exact fun x hx => hψQa.subset (image_mono (hSn e₀).1 hx)
  · by_cases heb : (ends e).2 = b
    · rw [heb, hGb, image_comp]
      rintro y ⟨x, hx, rfl⟩
      by_cases hxin : x ∈ interior (Sp e₀)
      · exact hforeign e he heb ⟨hx, hxin⟩
      · rw [hfix hxin]
        exact (hSn e).1 (heb.symm ▸ hx)
    · rw [hGother heb]
      exact (hSn e).1

theorem section34_single_trace_carrier_motion_conditions
    (hprep : Section34VertexPreparation U 𝒦 𝒦' h src Q ends Cp CpBd Cc CcBd Kcore Sn Tn Aa Ab₀ Ab₁
      Bb Bb₀ Bb₁ Bc Bc₀ Bc₁ ε)
    (hpack : Section34PiercingConditions U 𝒦 𝒦' h Q ends Cp CpBd Cc Sn Tn Aa Ab₀ Ab₁ Bb Bb₀
      Bb₁ Sp Tp cnt Pg G) (e₀ : Section34EdgeIndex 𝒦 𝒦') (k : Fin (cnt e₀))
    (ψ : M₂ ≃ₜ M₂) {K : Set M₂} (hK : IsCompact K) (hKS : K ⊆ interior (Sp e₀))
    (hfix : EqOn ψ id Kᶜ) (hψ : IsPLOn 3 3 ψ (interior (G (ends e₀).1 '' Cc (ends e₀).1)))
    (hrimA : Disjoint K (G (ends e₀).1 '' (Ab₀ e₀ ∪ Ab₁ e₀)))
    (hrimB : Disjoint K (G (ends e₀).2 '' (Bb₀ e₀ ∪ Bb₁ e₀)))
    (hkeep : Disjoint K (Pg e₀ k.val))
    (hcancel : G (ends e₀).1 '' CpBd (ends e₀).1 ∩ ψ '' (G (ends e₀).2 '' CpBd (ends e₀).2) =
      Pg e₀ k.val) :
    (G (ends e₀).1 '' CpBd (ends e₀).1 ∩ ψ '' (G (ends e₀).2 '' CpBd (ends e₀).2) ⊆
      G (ends e₀).1 '' (Aa e₀ \ (Ab₀ e₀ ∪ Ab₁ e₀)) ∩
        ψ '' (G (ends e₀).2 '' (Bb e₀ \ (Bb₀ e₀ ∪ Bb₁ e₀))) ∩ interior (Tp e₀)) ∧
    (G (ends e₀).1 '' Ab₀ e₀ ⊆ interior (ψ '' (G (ends e₀).2 '' Cp (ends e₀).2)) ∧
      Disjoint (G (ends e₀).1 '' Ab₁ e₀) (ψ '' (G (ends e₀).2 '' Cp (ends e₀).2))) ∧
    (ψ '' (G (ends e₀).2 '' Bb e₀) ⊆ interior (Sp e₀) ∧
      Disjoint (ψ '' (G (ends e₀).2 '' (Bb₀ e₀ ∪ Bb₁ e₀))) (Tp e₀)) ∧
    (∃ y₀ ∈ ψ '' (G (ends e₀).2 '' Bb e₀) ∩ G (ends e₀).1 '' Cp (ends e₀).1,
      ∀ z ∈ ψ '' (G (ends e₀).2 '' Bb e₀) ∩ G (ends e₀).1 '' Cp (ends e₀).1, z ∉ Tp e₀ →
        z ∈ connectedComponentIn
          (ψ '' (G (ends e₀).2 '' Bb e₀) ∩ G (ends e₀).1 '' Cp (ends e₀).1) y₀) ∧
    (∃ y₀ ∈ ψ '' (G (ends e₀).2 '' Bb e₀) \ G (ends e₀).1 '' Cp (ends e₀).1,
      ∀ z ∈ ψ '' (G (ends e₀).2 '' Bb e₀) \ G (ends e₀).1 '' Cp (ends e₀).1, z ∉ Tp e₀ →
        z ∈ connectedComponentIn
          (ψ '' (G (ends e₀).2 '' Bb e₀) \ G (ends e₀).1 '' Cp (ends e₀).1) y₀) ∧
    G (ends e₀).1 '' Aa e₀ ∩ ψ '' (G (ends e₀).2 '' Bb e₀) = Pg e₀ k.val ∧
    IsPolyhedralSphere (n := 3) 1 (Pg e₀ k.val) ∧
    ∀ y ∈ G (ends e₀).1 '' Aa e₀ ∩ ψ '' (G (ends e₀).2 '' Bb e₀),
      ∃ c ∈ (plGroupoid 3).maximalAtlas M₂, y ∈ c.source ∧
        HasPLCrossingAt (c '' (G (ends e₀).1 '' Aa e₀ ∩ c.source))
          (c '' (ψ '' (G (ends e₀).2 '' Bb e₀) ∩ c.source)) (c y) := by
  classical
  let I : Set (Fin (cnt e₀)) := {k}
  have hcover : (⋃ j : I, Pg e₀ j.1.val) = Pg e₀ k.val := by simp [I]
  have hkeepI : ∀ j : I, Disjoint K (Pg e₀ j.1.val) := by
    intro j
    have hj : j.1 = k := j.2
    exact hj.symm ▸ hkeep
  obtain ⟨-, hGp', -, -, -, -, -⟩ :=
    section34_second_vertex_motion_properties hprep hpack e₀ ψ hK hKS hfix hψ
  obtain ⟨hmeet, hside, hBb, htr, hsph, -, hcross⟩ :=
    section34_disk_motion_active_trace hprep hpack e₀ I ψ hK hKS hfix hrimA hrimB hkeepI
      (hcancel.trans hcover.symm)
  rw [hcover] at htr
  obtain ⟨-, -, -, -, hCp, -, -, -, hends, -, -, -, -, -, hAa, hBbOld, -⟩ := id hprep
  have hGa : section34VertexModification G (ends e₀).2 ψ (ends e₀).1 = G (ends e₀).1 :=
    section34VertexModification_of_ne G (ends e₀).2 ψ (hends e₀).1
  have hGb : section34VertexModification G (ends e₀).2 ψ (ends e₀).2 = ψ ∘ G (ends e₀).2 :=
    section34VertexModification_self G (ends e₀).2 ψ
  have hAB : Aa e₀ ⊆ CpBd (ends e₀).1 := (hAa e₀).1 ▸ inter_subset_left
  have hBB : Bb e₀ ⊆ CpBd (ends e₀).2 := (hBbOld e₀).1
  have hfull : section34VertexModification G (ends e₀).2 ψ (ends e₀).1 '' CpBd (ends e₀).1 ∩
      section34VertexModification G (ends e₀).2 ψ (ends e₀).2 '' CpBd (ends e₀).2 =
      Pg e₀ k.val := by
    rw [hGa, hGb, image_comp]
    exact hcancel
  have htrace : section34VertexModification G (ends e₀).2 ψ (ends e₀).2 '' Bb e₀ ∩
      section34VertexModification G (ends e₀).2 ψ (ends e₀).1 '' CpBd (ends e₀).1 =
      Pg e₀ k.val := by
    apply Subset.antisymm
    · exact fun _ hx => hfull.subset ⟨hx.2, image_mono hBB hx.1⟩
    · exact fun _ hx =>
        ⟨(htr.superset hx).2, image_mono hAB (htr.superset hx).1⟩
  have hJT : Pg e₀ k.val ⊆ interior (Tp e₀) :=
    fun _ hx => (hmeet (hfull.superset hx)).2
  have hann := (section34_piercing_annuli hprep hpack e₀).2.image_of_continuousOn_injOn
    ψ.continuous.continuousOn ψ.injective.injOn
  have hAeq : section34VertexModification G (ends e₀).2 ψ (ends e₀).1 '' Aa e₀ =
      section34VertexModification G (ends e₀).2 ψ (ends e₀).1 '' CpBd (ends e₀).1 ∩ Tp e₀ := by
    rw [hGa]
    exact section34_first_annulus_eq_boundary_inter_tube hprep hpack e₀
  have hsingleCross : ∀ x ∈ Pg e₀ k.val,
      ∃ c : OpenPartialHomeomorph M₂ (EuclideanSpace ℝ (Fin 3)), x ∈ c.source ∧
        HasPLCrossingAt
          (c '' (section34VertexModification G (ends e₀).2 ψ (ends e₀).2 '' Bb e₀ ∩ c.source))
          (c '' (section34VertexModification G (ends e₀).2 ψ (ends e₀).1 '' CpBd (ends e₀).1 ∩
            c.source)) (c x) := by
    intro x hx
    obtain ⟨c, -, hxc, hc⟩ := hcross x (htr.superset hx)
    refine ⟨c, hxc, hc.symm.congr (Filter.Eventually.of_forall fun _ => Iff.rfl) ?_⟩
    filter_upwards [(c.isOpen_image_source_inter isOpen_interior).mem_nhds
      ⟨x, ⟨hxc, hJT hx⟩, rfl⟩] with y hy
    obtain ⟨z, ⟨hzs, hzT⟩, rfl⟩ := hy
    have hmem (V : Set M₂) : c z ∈ c '' (V ∩ c.source) ↔ z ∈ V := by
      constructor
      · rintro ⟨w, ⟨hw, hws⟩, hwz⟩
        exact c.injOn hws hzs hwz ▸ hw
      · exact fun hz => ⟨z, ⟨hz, hzs⟩, rfl⟩
    rw [hmem, hmem, hAeq]
    exact and_iff_left (interior_subset hzT)
  have hann' : IsAnnulusOn (section34VertexModification G (ends e₀).2 ψ (ends e₀).2 '' Bb e₀)
      (section34VertexModification G (ends e₀).2 ψ (ends e₀).2 '' Bb₀ e₀)
      (section34VertexModification G (ends e₀).2 ψ (ends e₀).2 '' Bb₁ e₀) := by
    rw [hGb, image_comp, image_comp, image_comp]
    exact hann
  have hJends : Disjoint (Pg e₀ k.val)
      (section34VertexModification G (ends e₀).2 ψ (ends e₀).2 '' Bb₀ e₀ ∪
        section34VertexModification G (ends e₀).2 ψ (ends e₀).2 '' Bb₁ e₀) := by
    rw [← image_union]
    exact disjoint_left.mpr fun _ hx hy => disjoint_left.mp hBb.2 hy (interior_subset (hJT hx))
  obtain ⟨hcompIn, hcompOut⟩ :=
    ((hCp (ends e₀).2).image (hGp' (ends e₀).2)).component_conditions_of_single_crossing
      ((hCp (ends e₀).1).image (hGp' (ends e₀).1)) hann' (image_mono hBB) (hsph ⟨k, by simp [I]⟩)
      hJends htrace hsingleCross (Tp e₀)
  simp only [hGa, hGb, image_comp] at hmeet hside hBb htr hcross hcompIn hcompOut
  exact ⟨hmeet, hside, hBb, hcompIn, hcompOut, htr, hsph ⟨k, by simp [I]⟩, hcross⟩

theorem section34_removal_step_of_single_trace_carrier_motion
    (hprep : Section34VertexPreparation U 𝒦 𝒦' h src Q ends Cp CpBd Cc CcBd Kcore Sn Tn Aa Ab₀ Ab₁
      Bb Bb₀ Bb₁ Bc Bc₀ Bc₁ ε)
    (hpack : Section34PiercingConditions U 𝒦 𝒦' h Q ends Cp CpBd Cc Sn Tn Aa Ab₀ Ab₁ Bb Bb₀
      Bb₁ Sp Tp cnt Pg G) (e₀ : Section34EdgeIndex 𝒦 𝒦')
    (k : Fin (cnt e₀)) (hlt : 1 < cnt e₀)
    (ψ : M₂ ≃ₜ M₂) {K : Set M₂} (hK : IsCompact K) (hKS : K ⊆ interior (Sp e₀))
    (hfix : EqOn ψ id Kᶜ) (hψ : IsPLOn 3 3 ψ (interior (G (ends e₀).1 '' Cc (ends e₀).1)))
    (hrimA : Disjoint K (G (ends e₀).1 '' (Ab₀ e₀ ∪ Ab₁ e₀)))
    (hrimB : Disjoint K (G (ends e₀).2 '' (Bb₀ e₀ ∪ Bb₁ e₀)))
    (hkeep : Disjoint K (Pg e₀ k.val))
    (hforeign : ∀ e, e ≠ e₀ → (ends e).2 = (ends e₀).2 →
      MapsTo ψ (G (ends e₀).2 '' Sn e ∩ interior (Sp e₀)) (Q (ends e).1))
    (hcancel : G (ends e₀).1 '' CpBd (ends e₀).1 ∩ ψ '' (G (ends e₀).2 '' CpBd (ends e₀).2) =
      Pg e₀ k.val) :
    ∃ (G' : Section34VertexIndex 𝒦 𝒦' → M₁ → M₂) (cnt' : Section34EdgeIndex 𝒦 𝒦' → ℕ)
      (Pg' : Section34EdgeIndex 𝒦 𝒦' → ℕ → Set M₂),
      Section34PiercingConditions U 𝒦 𝒦' h Q ends Cp CpBd Cc Sn Tn Aa Ab₀ Ab₁ Bb Bb₀ Bb₁
          Sp Tp cnt' Pg' G' ∧ cnt' e₀ < cnt e₀ ∧
        (∀ e, e ≠ e₀ → cnt' e = cnt e) ∧
        (∀ w, EqOn (G' w) (G w) {x ∈ Cc w | G w x ∉ interior (Sp e₀)}) ∧
        ∀ e, e ≠ e₀ → G' (ends e).1 '' Aa e = G (ends e).1 '' Aa e ∧
          G' (ends e).2 '' Bb e = G (ends e).2 '' Bb e := by
  classical
  obtain ⟨hG', hGp', hQ', htubes, hoff, hin, -⟩ :=
    section34_second_vertex_motion_properties hprep hpack e₀ ψ hK hKS hfix hψ
  obtain ⟨hmeet, hside, hBb, hcompIn, hcompOut, htr, hsph, hcross⟩ :=
    section34_single_trace_carrier_motion_conditions hprep hpack e₀ k ψ hK hKS hfix hψ hrimA
      hrimB hkeep hcancel
  have hcrossQ := section34_second_motion_cross_carriers_of_mapsTo hprep hpack e₀ ψ
    (hfix.mono (compl_subset_compl.mpr hKS)) hforeign
  obtain ⟨-, -, -, -, -, -, -, -, hends, -⟩ := id hprep
  have hGa : section34VertexModification G (ends e₀).2 ψ (ends e₀).1 = G (ends e₀).1 :=
    section34VertexModification_of_ne G (ends e₀).2 ψ (hends e₀).1
  have hGb : section34VertexModification G (ends e₀).2 ψ (ends e₀).2 = ψ ∘ G (ends e₀).2 :=
    section34VertexModification_self G (ends e₀).2 ψ
  let C : Fin 1 → Set M₂ := fun _ => Pg e₀ k.val
  have hC : (⋃ i, C i) = Pg e₀ k.val := iUnion_const _
  obtain ⟨cnt', Pg', hp, hlt', hcnt, hannOther⟩ := piercing_conditions_after_cancellation
    hprep hpack (section34VertexModification G (ends e₀).2 ψ) e₀ 1 C hlt hoff hin (htubes e₀)
    hG' hQ' hcrossQ (by simpa only [hGa, hGb, image_comp] using hmeet)
    (by simpa only [hGa, hGb, image_comp] using hside)
    (by simpa only [hGb, image_comp] using hBb.2)
    (by simpa only [hGa, hGb, image_comp] using hcompIn)
    (by simpa only [hGa, hGb, image_comp] using hcompOut)
    (by simpa only [hGa, hGb, image_comp, hC] using htr) (fun _ => hsph)
    (fun j l hne => (hne (Subsingleton.elim j l)).elim)
    (by simpa only [hGa, hGb, image_comp] using hcross)
  exact ⟨section34VertexModification G (ends e₀).2 ψ, cnt', Pg', hp, hlt', hcnt, hoff, hannOther⟩

end DifferentialGeometry.Topology.PiecewiseLinear
