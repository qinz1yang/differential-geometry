import DifferentialGeometry.Topology.PiecewiseLinear.IsPLHomeomorphIntoMonoOfIsPLCellOn
import DifferentialGeometry.Topology.PiecewiseLinear.Section34ModelMotionTransport
import DifferentialGeometry.Topology.PiecewiseLinear.Section34ProtectedCircleSupport
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

theorem section34_second_vertex_motion_properties
    (hprep : Section34VertexPreparation U 𝒦 𝒦' h src Q ends Cp CpBd Cc CcBd Kcore Sn Tn Aa Ab₀ Ab₁
      Bb Bb₀ Bb₁ Bc Bc₀ Bc₁ ε)
    (hpack : Section34PiercingConditions U 𝒦 𝒦' h Q ends Cp CpBd Cc Sn Tn Aa Ab₀ Ab₁ Bb Bb₀
      Bb₁ Sp Tp cnt Pg G) (e₀ : Section34EdgeIndex 𝒦 𝒦') (ψ : M₂ ≃ₜ M₂) {K : Set M₂}
    (hK : IsCompact K) (hKS : K ⊆ interior (Sp e₀)) (hfix : EqOn ψ id Kᶜ)
    (hψ : IsPLOn 3 3 ψ (interior (G (ends e₀).1 '' Cc (ends e₀).1))) :
    let G' := section34VertexModification G (ends e₀).2 ψ
    (∀ w, IsPLHomeomorphInto 3 (G' w) (Cc w)) ∧
    (∀ w, IsPLHomeomorphInto 3 (G' w) (Cp w)) ∧
    (∀ w, G' w '' Cc w ⊆ Q w) ∧
    (∀ e, Sp e = G' (ends e).1 '' Sn e ∧ Tp e = G' (ends e).1 '' Tn e) ∧
    (∀ w, EqOn (G' w) (G w) {x ∈ Cc w | G w x ∉ interior (Sp e₀)}) ∧
    (∀ w, ∀ x ∈ Cp w, G w x ∈ interior (Sp e₀) → G' w x ∈ interior (Sp e₀)) ∧
    ∀ e, e ≠ e₀ → G' (ends e).1 '' Aa e = G (ends e).1 '' Aa e ∧
      G' (ends e).2 '' Bb e = G (ends e).2 '' Bb e := by
  let a := (ends e₀).1
  let b := (ends e₀).2
  let G' := section34VertexModification G b ψ
  obtain ⟨-, hCc, hsub, -, hCp, -, -, -, hends, -, -, -, hSnCc, -⟩ := id hprep
  obtain ⟨hG, hQ, hSn, htubes, -⟩ := id hpack
  have hGa : G' a = G a := section34VertexModification_of_ne G b ψ (hends e₀).1
  have hGb : G' b = ψ ∘ G b := section34VertexModification_self G b ψ
  have hGother {w : Section34VertexIndex 𝒦 𝒦'} (hw : w ≠ b) : G' w = G w :=
    section34VertexModification_of_ne G b ψ hw
  have hfixS : EqOn ψ id (interior (Sp e₀))ᶜ :=
    hfix.mono (compl_subset_compl.mpr hKS)
  have hoff : ∀ w, EqOn (G' w) (G w) {x ∈ Cc w | G w x ∉ interior (Sp e₀)} :=
    fun w x hx => section34VertexModification_eqOn G b ψ hfixS w hx.2
  have hin : ∀ w, ∀ x ∈ Cp w, G w x ∈ interior (Sp e₀) → G' w x ∈ interior (Sp e₀) :=
    fun w x _ hx => (section34VertexModification_mem_iff G b ψ hfixS w x).mpr hx
  have hSpCc : Sp e₀ ⊆ G a '' Cc a := by
    rw [(htubes e₀).1]
    exact image_mono (hSnCc e₀ a (Or.inl rfl))
  have hG' : ∀ w, IsPLHomeomorphInto 3 (G' w) (Cc w) := by
    intro w
    by_cases hw : w = b
    · subst w
      rw [hGb]
      exact (hG b).postcomp_of_supported_isPLOn (hCc b) ψ hψ isOpen_interior
        hK.isClosed (hKS.trans (interior_mono hSpCc)) hfix
    · rw [hGother hw]
      exact hG w
  have hQb : Sp e₀ ⊆ Q b := (htubes e₀).1 ▸ (hSn e₀).2
  have hψQb : ψ '' Q b = Q b :=
    image_eq_of_homeomorph_eqOn_compl_of_subset ψ hfix (hKS.trans (interior_subset.trans hQb))
  have hQ' : ∀ w, G' w '' Cc w ⊆ Q w := by
    intro w
    by_cases hw : w = b
    · subst w
      rw [hGb, image_comp, ← hψQb]
      exact image_mono (hQ b)
    · rw [hGother hw]
      exact hQ w
  have htubes' : ∀ e, Sp e = G' (ends e).1 '' Sn e ∧ Tp e = G' (ends e).1 '' Tn e := by
    intro e
    by_cases he : e = e₀
    · subst e
      change Sp e₀ = G' a '' Sn e₀ ∧ Tp e₀ = G' a '' Tn e₀
      rw [hGa]
      exact htubes e₀
    · exact section34Step_other_tube_images hprep hpack G' e₀ hoff e he
  exact ⟨hG', fun w => (hG' w).mono_of_isPLCellOn (hCp w) (hsub w).2.1,
    hQ', htubes', hoff, hin, section34Step_other_annulus_images hprep hpack G' e₀ hoff⟩

end DifferentialGeometry.Topology.PiecewiseLinear
