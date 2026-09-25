import DifferentialGeometry.Topology.PiecewiseLinear.Section34PiercingInwardMotion
import DifferentialGeometry.Topology.PiecewiseLinear.Section34PiercingInwardPreprocessing
import DifferentialGeometry.Topology.PiecewiseLinear.Section34InwardComponentTransport

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


theorem exists_section34_inward_preparation_fixing_first
    (hprep : Section34VertexPreparation U 𝒦 𝒦' h src Q ends Cp CpBd Cc CcBd Kcore Sn Tn Aa Ab₀ Ab₁
      Bb Bb₀ Bb₁ Bc Bc₀ Bc₁ ε)
    (hpack : Section34PiercingConditions U 𝒦 𝒦' h Q ends Cp CpBd Cc Sn Tn Aa Ab₀ Ab₁ Bb Bb₀
      Bb₁ Sp Tp cnt Pg G) (e : Section34EdgeIndex 𝒦 𝒦') :
    ∃ G' : Section34VertexIndex 𝒦 𝒦' → M₁ → M₂,
      Section34PiercingConditions U 𝒦 𝒦' h Q ends Cp CpBd Cc Sn Tn Aa Ab₀ Ab₁ Bb Bb₀ Bb₁
        Sp Tp cnt Pg G' ∧
      (∀ w, EqOn (G' w) (G w) {x ∈ Cc w | G w x ∉ interior (Sp e)}) ∧
      (∀ d, d ≠ e → G' (ends d).1 '' Aa d = G (ends d).1 '' Aa d ∧
        G' (ends d).2 '' Bb d = G (ends d).2 '' Bb d) ∧
      G' (ends e).1 = G (ends e).1 ∧
      ∃ a ∈ G' (ends e).2 '' Bb e ∩ G' (ends e).1 '' Cp (ends e).1,
        ∃ b ∈ G' (ends e).2 '' Bb e \ G' (ends e).1 '' Cp (ends e).1,
          (∀ y ∈ G' (ends e).2 '' Bb e ∩ G' (ends e).1 '' Cp (ends e).1,
            y ∉ connectedComponentIn
              (G' (ends e).2 '' Bb e ∩ G' (ends e).1 '' Cp (ends e).1) a →
            closure (connectedComponentIn
              (G' (ends e).2 '' Bb e ∩ G' (ends e).1 '' Cp (ends e).1) y) ⊆ interior (Tp e)) ∧
          ∀ y ∈ G' (ends e).2 '' Bb e \ G' (ends e).1 '' Cp (ends e).1,
            y ∉ connectedComponentIn
              (G' (ends e).2 '' Bb e \ G' (ends e).1 '' Cp (ends e).1) b →
            closure (connectedComponentIn
              (G' (ends e).2 '' Bb e \ G' (ends e).1 '' Cp (ends e).1) y) ⊆ interior (Tp e) := by
  obtain ⟨O, ψ, -, -, hO, hfirst, hforeign, hrim, hfix, hψ, hcell, hTp, hpush, -⟩ :=
    exists_section34_piercing_inward_motion hprep hpack e
  let G' := section34VertexModification G (ends e).2 ψ
  have hpack' := section34_piercing_conditions_after_inward_motion hprep hpack e ψ
    hfix hO hfirst hforeign hrim hψ hcell hTp
  have hfixSp : EqOn ψ id (interior (Sp e))ᶜ := hfix.mono
    (compl_subset_compl.mpr fun x hx => (hO (subset_closure hx)).1.1)
  have hoff : ∀ w, EqOn (G' w) (G w) {x ∈ Cc w | G w x ∉ interior (Sp e)} :=
    fun w x hx => section34VertexModification_eqOn G (ends e).2 ψ hfixSp w hx.2
  have hne : (ends e).1 ≠ (ends e).2 := by
    obtain ⟨-, -, -, -, -, -, -, -, he, -⟩ := hprep
    exact (he e).1
  have hGa : G' (ends e).1 = G (ends e).1 :=
    section34VertexModification_of_ne G (ends e).2 ψ hne
  refine ⟨G', hpack', hoff,
    section34Step_other_annulus_images hprep hpack G' e hoff, hGa, ?_⟩
  obtain ⟨a, ha, b, hb, hin, hout⟩ := section34_piercing_components_trapped hprep hpack e
  have hB := (section34_piercing_annuli hprep hpack e).2.isCompact.isClosed
  have htrap := Homeomorph.exists_piercing_components_interior_trapped ψ hcell hB
    hTp hpush ha hb hin hout
  change ∃ a ∈ G' (ends e).2 '' Bb e ∩ G' (ends e).1 '' Cp (ends e).1,
    ∃ b ∈ G' (ends e).2 '' Bb e \ G' (ends e).1 '' Cp (ends e).1,
      (∀ y ∈ G' (ends e).2 '' Bb e ∩ G' (ends e).1 '' Cp (ends e).1,
        y ∉ connectedComponentIn
          (G' (ends e).2 '' Bb e ∩ G' (ends e).1 '' Cp (ends e).1) a →
        closure (connectedComponentIn
          (G' (ends e).2 '' Bb e ∩ G' (ends e).1 '' Cp (ends e).1) y) ⊆ interior (Tp e)) ∧
      ∀ y ∈ G' (ends e).2 '' Bb e \ G' (ends e).1 '' Cp (ends e).1,
        y ∉ connectedComponentIn
          (G' (ends e).2 '' Bb e \ G' (ends e).1 '' Cp (ends e).1) b →
        closure (connectedComponentIn
          (G' (ends e).2 '' Bb e \ G' (ends e).1 '' Cp (ends e).1) y) ⊆ interior (Tp e)
  simpa only [G', section34VertexModification_self,
    section34VertexModification_of_ne G (ends e).2 ψ hne, image_comp] using htrap

theorem exists_section34_inward_preparation
    (hprep : Section34VertexPreparation U 𝒦 𝒦' h src Q ends Cp CpBd Cc CcBd Kcore Sn Tn Aa Ab₀ Ab₁
      Bb Bb₀ Bb₁ Bc Bc₀ Bc₁ ε)
    (hpack : Section34PiercingConditions U 𝒦 𝒦' h Q ends Cp CpBd Cc Sn Tn Aa Ab₀ Ab₁ Bb Bb₀
      Bb₁ Sp Tp cnt Pg G) (e : Section34EdgeIndex 𝒦 𝒦') :
    ∃ G' : Section34VertexIndex 𝒦 𝒦' → M₁ → M₂,
      Section34PiercingConditions U 𝒦 𝒦' h Q ends Cp CpBd Cc Sn Tn Aa Ab₀ Ab₁ Bb Bb₀ Bb₁
        Sp Tp cnt Pg G' ∧
      (∀ w, EqOn (G' w) (G w) {x ∈ Cc w | G w x ∉ interior (Sp e)}) ∧
      (∀ d, d ≠ e → G' (ends d).1 '' Aa d = G (ends d).1 '' Aa d ∧
        G' (ends d).2 '' Bb d = G (ends d).2 '' Bb d) ∧
      ∃ a ∈ G' (ends e).2 '' Bb e ∩ G' (ends e).1 '' Cp (ends e).1,
        ∃ b ∈ G' (ends e).2 '' Bb e \ G' (ends e).1 '' Cp (ends e).1,
          (∀ y ∈ G' (ends e).2 '' Bb e ∩ G' (ends e).1 '' Cp (ends e).1,
            y ∉ connectedComponentIn
              (G' (ends e).2 '' Bb e ∩ G' (ends e).1 '' Cp (ends e).1) a →
            closure (connectedComponentIn
              (G' (ends e).2 '' Bb e ∩ G' (ends e).1 '' Cp (ends e).1) y) ⊆ interior (Tp e)) ∧
          ∀ y ∈ G' (ends e).2 '' Bb e \ G' (ends e).1 '' Cp (ends e).1,
            y ∉ connectedComponentIn
              (G' (ends e).2 '' Bb e \ G' (ends e).1 '' Cp (ends e).1) b →
            closure (connectedComponentIn
              (G' (ends e).2 '' Bb e \ G' (ends e).1 '' Cp (ends e).1) y) ⊆ interior (Tp e) := by
  obtain ⟨G', hp, ho, hi, -, ha⟩ :=
    exists_section34_inward_preparation_fixing_first hprep hpack e
  exact ⟨G', hp, ho, hi, ha⟩

end DifferentialGeometry.Topology.PiecewiseLinear
