import DifferentialGeometry.Topology.PiecewiseLinear.LocallyFiniteSupportedModification
import DifferentialGeometry.Topology.PiecewiseLinear.Section34Frame

open Set

namespace DifferentialGeometry.Topology.PiecewiseLinear

noncomputable def section34VertexModification {V X Y : Type*}
    (G : V → X → Y) (w₀ : V) (φ : Y → Y) : V → X → Y := by
  classical
  exact Function.update G w₀ (φ ∘ G w₀)

@[simp] theorem section34VertexModification_self {V X Y : Type*}
    (G : V → X → Y) (w₀ : V) (φ : Y → Y) :
    section34VertexModification G w₀ φ w₀ = φ ∘ G w₀ := by
  classical
  exact Function.update_self _ _ _

@[simp] theorem section34VertexModification_of_ne {V X Y : Type*}
    (G : V → X → Y) (w₀ : V) (φ : Y → Y) {w : V} (hw : w ≠ w₀) :
    section34VertexModification G w₀ φ w = G w := by
  classical
  exact Function.update_of_ne hw _ _

theorem section34VertexModification_eqOn {V X Y : Type*}
    (G : V → X → Y) (w₀ : V) (φ : Y → Y) {S : Set Y} (hfix : EqOn φ id Sᶜ) (w : V) :
    EqOn (section34VertexModification G w₀ φ w) (G w) {x | G w x ∉ S} := by
  by_cases hw : w = w₀
  · subst w
    intro x hx
    rw [section34VertexModification_self]
    exact hfix hx
  · rw [section34VertexModification_of_ne G w₀ φ hw]
    exact fun _ _ => rfl

theorem section34VertexModification_mem_iff {V X Y : Type*} [TopologicalSpace Y]
    (G : V → X → Y) (w₀ : V) (φ : Y ≃ₜ Y) {S : Set Y} (hfix : EqOn φ id Sᶜ)
    (w : V) (x : X) :
    section34VertexModification G w₀ φ w x ∈ S ↔ G w x ∈ S := by
  by_cases hw : w = w₀
  · subst w
    rw [section34VertexModification_self, Function.comp_apply]
    have himage := image_eq_of_homeomorph_eqOn_compl_of_subset φ hfix (Subset.refl S)
    constructor
    · intro hx
      obtain ⟨y, hy, heq⟩ := himage.symm.subset hx
      exact φ.injective heq ▸ hy
    · intro hx
      exact himage.subset (mem_image_of_mem φ hx)
  · rw [section34VertexModification_of_ne G w₀ φ hw]

theorem section34VertexModification_image_self {V X Y : Type*} [TopologicalSpace Y]
    (G : V → X → Y) (w₀ : V) (φ : Y ≃ₜ Y) {S : Set Y} {A : Set X}
    (hfix : EqOn φ id Sᶜ) (hSA : S ⊆ G w₀ '' A) :
    section34VertexModification G w₀ φ w₀ '' A = G w₀ '' A := by
  rw [section34VertexModification_self, image_comp]
  exact image_eq_of_homeomorph_eqOn_compl_of_subset φ hfix hSA

theorem section34VertexModification_isPLHomeomorphInto {V X Y : Type*} {n : ℕ}
    [TopologicalSpace X] [ChartedSpace (EuclideanSpace ℝ (Fin n)) X]
    [TopologicalSpace Y] [ChartedSpace (EuclideanSpace ℝ (Fin n)) Y]
    {G : V → X → Y} {Cc : V → Set X} (hG : ∀ w, IsPLHomeomorphInto n (G w) (Cc w))
    (w₀ : V) (φ : Y → Y) (hφ : IsPLHomeomorphInto n φ (G w₀ '' Cc w₀)) :
    ∀ w, IsPLHomeomorphInto n (section34VertexModification G w₀ φ w) (Cc w) := by
  intro w
  by_cases hw : w = w₀
  · subst w
    rw [section34VertexModification_self]
    exact (hG w₀).comp_of_image_eq hφ
  · rw [section34VertexModification_of_ne G w₀ φ hw]
    exact hG w

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

theorem section34VertexModification_eqOn_other_tubes
    (hprep : Section34VertexPreparation U 𝒦 𝒦' h src Q ends Cp CpBd Cc CcBd Kcore Sn Tn Aa Ab₀ Ab₁
      Bb Bb₀ Bb₁ Bc Bc₀ Bc₁ ε)
    (hpack : Section34PiercingConditions U 𝒦 𝒦' h Q ends Cp CpBd Cc Sn Tn Aa Ab₀ Ab₁ Bb Bb₀
      Bb₁ Sp Tp cnt Pg G)
    (e₀ : Section34EdgeIndex 𝒦 𝒦') (φ : M₂ → M₂)
    (hfix : EqOn φ id (interior (Sp e₀))ᶜ)
    (e : Section34EdgeIndex 𝒦 𝒦') (he : e ≠ e₀) :
    EqOn (section34VertexModification G (ends e₀).1 φ (ends e).1) (G (ends e).1) (Sn e) ∧
      EqOn (section34VertexModification G (ends e₀).1 φ (ends e).2) (G (ends e).2) (Sn e) := by
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, hSnCc, hdisj, -⟩ := hprep
  obtain ⟨hG, -, -, hSp, -⟩ := hpack
  have hfixw : ∀ w, w = (ends e).1 ∨ w = (ends e).2 →
      EqOn (section34VertexModification G (ends e₀).1 φ w) (G w) (Sn e) := by
    intro w hw x hx
    by_cases hw₀ : w = (ends e₀).1
    · subst w
      apply section34VertexModification_eqOn G (ends e₀).1 φ hfix (ends e₀).1
      intro hin
      obtain ⟨y, hy, hxy⟩ : G (ends e₀).1 x ∈ G (ends e₀).1 '' Sn e₀ :=
        (hSp e₀).1 ▸ interior_subset hin
      have hyx := (hG (ends e₀).1).injOn (hSnCc e₀ _ (Or.inl rfl) hy) (hSnCc e _ hw hx) hxy
      exact disjoint_left.mp (hdisj e e₀ he) hx (hyx ▸ hy)
    · rw [section34VertexModification_of_ne G (ends e₀).1 φ hw₀]
  exact ⟨hfixw _ (Or.inl rfl), hfixw _ (Or.inr rfl)⟩

theorem section34VertexModification_carrier
    (hprep : Section34VertexPreparation U 𝒦 𝒦' h src Q ends Cp CpBd Cc CcBd Kcore Sn Tn Aa Ab₀ Ab₁
      Bb Bb₀ Bb₁ Bc Bc₀ Bc₁ ε)
    (hpack : Section34PiercingConditions U 𝒦 𝒦' h Q ends Cp CpBd Cc Sn Tn Aa Ab₀ Ab₁ Bb Bb₀
      Bb₁ Sp Tp cnt Pg G)
    (e₀ : Section34EdgeIndex 𝒦 𝒦') (φ : M₂ ≃ₜ M₂)
    (hfix : EqOn φ id (interior (Sp e₀))ᶜ) :
    ∀ w, section34VertexModification G (ends e₀).1 φ w '' Cc w ⊆ Q w := by
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, hSnCc, -⟩ := hprep
  obtain ⟨-, hQ, -, hSp, -⟩ := hpack
  intro w y hy
  by_cases hw : w = (ends e₀).1
  · subst w
    obtain ⟨x, hx, rfl⟩ := hy
    by_cases hin : G (ends e₀).1 x ∈ interior (Sp e₀)
    · have hy := (section34VertexModification_mem_iff G (ends e₀).1 φ hfix _ x).mpr hin
      have hSpQ : Sp e₀ ⊆ Q (ends e₀).1 := by
        rw [(hSp e₀).1]
        exact (image_mono (hSnCc e₀ _ (Or.inl rfl))).trans (hQ _)
      exact hSpQ (interior_subset hy)
    · rw [section34VertexModification_eqOn G (ends e₀).1 φ hfix _ hin]
      exact hQ _ ⟨x, hx, rfl⟩
  · rw [section34VertexModification_of_ne G (ends e₀).1 φ hw] at hy
    exact hQ w hy

theorem section34VertexModification_cross_carriers
    (hprep : Section34VertexPreparation U 𝒦 𝒦' h src Q ends Cp CpBd Cc CcBd Kcore Sn Tn Aa Ab₀ Ab₁
      Bb Bb₀ Bb₁ Bc Bc₀ Bc₁ ε)
    (hpack : Section34PiercingConditions U 𝒦 𝒦' h Q ends Cp CpBd Cc Sn Tn Aa Ab₀ Ab₁ Bb Bb₀
      Bb₁ Sp Tp cnt Pg G)
    (e₀ : Section34EdgeIndex 𝒦 𝒦') (φ : M₂ ≃ₜ M₂)
    (hfix : EqOn φ id (interior (Sp e₀))ᶜ) :
    ∀ e, section34VertexModification G (ends e₀).1 φ (ends e).2 '' Sn e ⊆ Q (ends e).1 ∧
      section34VertexModification G (ends e₀).1 φ (ends e).1 '' Sn e ⊆ Q (ends e).2 := by
  have hforeign := section34VertexModification_eqOn_other_tubes hprep hpack e₀ φ hfix
  obtain ⟨-, -, -, -, -, -, -, -, hends, -⟩ := hprep
  obtain ⟨-, -, hQ, hSp, -⟩ := hpack
  intro e
  by_cases he : e = e₀
  · subst e
    rw [section34VertexModification_of_ne G (ends e₀).1 φ (hends e₀).1.symm,
      section34VertexModification_image_self G (ends e₀).1 φ hfix
        ((hSp e₀).1 ▸ interior_subset)]
    exact hQ e₀
  · rw [(hforeign e he).1.image_eq, (hforeign e he).2.image_eq]
    exact hQ e

theorem section34VertexModification_tube_images_of_image_eq
    (hprep : Section34VertexPreparation U 𝒦 𝒦' h src Q ends Cp CpBd Cc CcBd Kcore Sn Tn Aa Ab₀ Ab₁
      Bb Bb₀ Bb₁ Bc Bc₀ Bc₁ ε)
    (hpack : Section34PiercingConditions U 𝒦 𝒦' h Q ends Cp CpBd Cc Sn Tn Aa Ab₀ Ab₁ Bb Bb₀
      Bb₁ Sp Tp cnt Pg G)
    (e₀ : Section34EdgeIndex 𝒦 𝒦') (φ : M₂ ≃ₜ M₂)
    (hfix : EqOn φ id (interior (Sp e₀))ᶜ) (hinner : φ '' Tp e₀ = Tp e₀) :
    ∀ e, Sp e = section34VertexModification G (ends e₀).1 φ (ends e).1 '' Sn e ∧
      Tp e = section34VertexModification G (ends e₀).1 φ (ends e).1 '' Tn e := by
  have hother := section34VertexModification_eqOn_other_tubes hprep hpack e₀ φ hfix
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, hTnSn, -⟩ := hprep
  obtain ⟨-, -, -, hSp, -⟩ := hpack
  intro e
  by_cases he : e = e₀
  · subst e
    constructor
    · rw [section34VertexModification_image_self G (ends e₀).1 φ hfix
        ((hSp e₀).1 ▸ interior_subset)]
      exact (hSp e₀).1
    · rw [section34VertexModification_self, image_comp, ← (hSp e₀).2, hinner]
  · have hforeign := (hother e he).1
    rw [hforeign.image_eq, (hforeign.mono ((hTnSn e).1.trans interior_subset)).image_eq]
    exact hSp e

theorem section34VertexModification_tube_images
    (hprep : Section34VertexPreparation U 𝒦 𝒦' h src Q ends Cp CpBd Cc CcBd Kcore Sn Tn Aa Ab₀ Ab₁
      Bb Bb₀ Bb₁ Bc Bc₀ Bc₁ ε)
    (hpack : Section34PiercingConditions U 𝒦 𝒦' h Q ends Cp CpBd Cc Sn Tn Aa Ab₀ Ab₁ Bb Bb₀
      Bb₁ Sp Tp cnt Pg G)
    (e₀ : Section34EdgeIndex 𝒦 𝒦') (φ : M₂ ≃ₜ M₂)
    (hfix : EqOn φ id (interior (Tp e₀))ᶜ) :
    ∀ e, Sp e = section34VertexModification G (ends e₀).1 φ (ends e).1 '' Sn e ∧
      Tp e = section34VertexModification G (ends e₀).1 φ (ends e).1 '' Tn e := by
  have htubes := section34VertexModification_tube_images_of_image_eq hprep hpack e₀ φ
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, hTnSn, -⟩ := hprep
  obtain ⟨-, -, -, hSp, -⟩ := hpack
  have hTpSp : Tp e₀ ⊆ Sp e₀ := by
    rw [(hSp e₀).1, (hSp e₀).2]
    exact image_mono ((hTnSn e₀).1.trans interior_subset)
  have hfixSp : EqOn φ id (interior (Sp e₀))ᶜ :=
    hfix.mono (compl_subset_compl.mpr (interior_mono hTpSp))
  exact htubes hfixSp (image_eq_of_homeomorph_eqOn_compl_of_subset φ hfix interior_subset)

end DifferentialGeometry.Topology.PiecewiseLinear
