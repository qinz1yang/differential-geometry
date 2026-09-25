import DifferentialGeometry.Topology.PiecewiseLinear.Section34SecondVertexMotion

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

theorem section34_second_motion_cross_carriers
    (hprep : Section34VertexPreparation U 𝒦 𝒦' h src Q ends Cp CpBd Cc CcBd Kcore Sn Tn Aa Ab₀ Ab₁
      Bb Bb₀ Bb₁ Bc Bc₀ Bc₁ ε)
    (hpack : Section34PiercingConditions U 𝒦 𝒦' h Q ends Cp CpBd Cc Sn Tn Aa Ab₀ Ab₁ Bb Bb₀
      Bb₁ Sp Tp cnt Pg G) (e₀ : Section34EdgeIndex 𝒦 𝒦') (ψ : M₂ ≃ₜ M₂)
    (hfix : EqOn ψ id (interior (Sp e₀))ᶜ)
    (hforeign : ∀ e, e ≠ e₀ →
      ((ends e₀).2 = (ends e).1 ∨ (ends e₀).2 = (ends e).2) →
        EqOn ψ id (G (ends e₀).2 '' Sn e)) :
    let G' := section34VertexModification G (ends e₀).2 ψ
    ∀ e, G' (ends e).2 '' Sn e ⊆ Q (ends e).1 ∧
      G' (ends e).1 '' Sn e ⊆ Q (ends e).2 := by
  let a := (ends e₀).1
  let b := (ends e₀).2
  let G' := section34VertexModification G b ψ
  obtain ⟨-, -, -, -, -, -, -, -, hends, -, -, -, hSnCc, -⟩ := hprep
  obtain ⟨-, hQ, hSn, htube, -⟩ := hpack
  have hGa : G' a = G a := section34VertexModification_of_ne G b ψ (hends e₀).1
  have hGb : G' b = ψ ∘ G b := section34VertexModification_self G b ψ
  have hSpQa : interior (Sp e₀) ⊆ Q a := by
    rw [(htube e₀).1]
    exact interior_subset.trans ((image_mono (hSnCc e₀ a (Or.inl rfl))).trans (hQ a))
  have hψQa : ψ '' Q a = Q a :=
    image_eq_of_homeomorph_eqOn_compl_of_subset ψ hfix hSpQa
  have hforeignImage (e : Section34EdgeIndex 𝒦 𝒦') (he : e ≠ e₀)
      (w : Section34VertexIndex 𝒦 𝒦') (hw : w = (ends e).1 ∨ w = (ends e).2) :
      G' w '' Sn e = G w '' Sn e := by
    by_cases hwb : w = b
    · subst w
      rw [hGb, image_comp]
      exact ((hforeign e he hw).image_eq).trans (image_id' _)
    · have heq : G' w = G w := section34VertexModification_of_ne G b ψ hwb
      rw [heq]
  change ∀ e, G' (ends e).2 '' Sn e ⊆ Q (ends e).1 ∧
    G' (ends e).1 '' Sn e ⊆ Q (ends e).2
  intro e
  by_cases he : e = e₀
  · subst e
    change G' b '' Sn e₀ ⊆ Q a ∧ G' a '' Sn e₀ ⊆ Q b
    rw [hGa, hGb, image_comp]
    exact ⟨fun x hx => hψQa ▸ image_mono (hSn e₀).1 hx, (hSn e₀).2⟩
  · rw [hforeignImage e he _ (Or.inr rfl), hforeignImage e he _ (Or.inl rfl)]
    exact hSn e

end DifferentialGeometry.Topology.PiecewiseLinear
