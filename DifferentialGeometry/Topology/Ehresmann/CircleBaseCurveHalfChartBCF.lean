import DifferentialGeometry.Topology.Ehresmann.CircleBaseHalfChartBCF
import DifferentialGeometry.Topology.Ehresmann.CircleBaseLabelsBCF

/-!
# A half chart of the circle-base curve at every point (lane S-BCF03b; BCF03 G7 K-D1..D3 + labels)

`exists_halfChart_at_BCF`: at a point `y` of the base curve `Γ = f '' (Bd ∩ Rc)` of the
two-dimensional base `B₀` of a circle fibration `f : M → H` (`M` a `3`-manifold) with a circle
chart `(σ, φ)` at `y` and a corner record `(O, L, ψ)` of the circle-base remainder `C₁ = f '' Rc`
(face labels `Λ ⊕ Unit`, independent differentials through `f`, `C₁ ∩ O = {ψ ≤ 0}`, zero sets =
whole-fibre-in-face, all labels whose face contains the fibre belong to `L`): `Γ` has a half chart
`d` at `y` whose chart coordinate vanishes exactly when `y` is a rim base point `Rb y`.

It combines the label analysis `circleBase_labels_BCF` with the half charts of the corner
(`exists_halfChart_of_circleCorner_BCF`) and interior (`exists_halfChart_of_circleInterior_BCF`)
cases.
-/

set_option autoImplicit false

open Set Function Manifold Topology
open scoped ContDiff Manifold

noncomputable section

namespace DifferentialGeometry.Topology

local notation "E2" => EuclideanSpace ℝ (Fin 2)

variable {EM HM M : Type*} [NormedAddCommGroup EM] [NormedSpace ℝ EM] [FiniteDimensional ℝ EM]
  [TopologicalSpace HM] {I : ModelWithCorners ℝ EM HM} [TopologicalSpace M] [ChartedSpace HM M]
  {H : Type*} [NormedAddCommGroup H] [NormedSpace ℝ H] {Λ : Type*} [Finite Λ]

/-- **A half chart of the base curve at every point, with the rim base points as its corners.** -/
theorem exists_halfChart_at_BCF (hdim : Module.finrank ℝ EM = 3) {f : M → H}
    {X Rc Bd M₂ : Set M} {B₀ : Set H} {F : Λ → Set M} {V : Set M} (hRcM : Rc ⊆ M₂)
    (hRsat : ∀ q ∈ X, f q ∈ f '' Rc → q ∈ Rc) (hRcX : Rc ⊆ X) (hB : ∀ q ∈ X, f q ∈ B₀)
    (hdisj : ∀ ℓ ℓ', ℓ ≠ ℓ' → Disjoint (F ℓ ∩ M₂) (F ℓ' ∩ M₂)) (hFBd : ∀ ℓ, F ℓ ∩ M₂ ⊆ Bd)
    (hKcl : ∀ ℓ, ∃ G : Set H, IsClosed G ∧ ∀ y ∈ B₀, (X ∩ f ⁻¹' {y} ⊆ F ℓ ↔ y ∈ G))
    (hsat1 : ∀ p ∈ Bd ∩ Rc, ∃ ℓ, X ∩ f ⁻¹' {f p} ⊆ F ℓ) {Rb : H → Prop}
    (hRb1 : ∀ y ∈ f '' (Bd ∩ Rc), Rb y → X ∩ f ⁻¹' {y} ⊆ V)
    (hRb2 : ∀ y ∈ f '' (Bd ∩ Rc), X ∩ f ⁻¹' {y} ⊆ V → Rb y) {y : H}
    (hyΓ : y ∈ f '' (Bd ∩ Rc)) {σ : E2 → H} {φ : E2 × Circle → M} {Oσ : Set H}
    (hσ0 : σ 0 = y) (hσ : ContDiff ℝ ∞ σ) (hσe : IsEmbedding σ)
    (hσd : ∀ x, Injective (fderiv ℝ σ x)) (hOσ : IsOpen Oσ) (hrange : range σ = B₀ ∩ Oσ)
    (hφ : IsSmoothEmbedding ((𝓡 2).prod (𝓡 1)) I ∞ φ) (hf : ∀ x z, f (φ (x, z)) = σ x)
    (hφr : range φ = X ∩ f ⁻¹' range σ) {O : Set H} (hO : IsOpen O) (hyO : y ∈ O)
    (L : Finset (Λ ⊕ Unit)) (ψ : Λ ⊕ Unit → H → ℝ)
    (hψ : ∀ s ∈ L, ContDiffOn ℝ ∞ (ψ s) O ∧ ψ s y = 0 ∧
      {y' | y' ∈ O ∧ y' ∈ f '' Rc ∧ ψ s y' = 0} =
        {y' | y' ∈ O ∧ y' ∈ f '' Rc ∧ X ∩ f ⁻¹' {y'} ⊆ Sum.elim F (fun _ => V) s})
    (hsurj : ∀ p ∈ X ∩ f ⁻¹' {y}, Surjective fun w : TangentSpace I p =>
      fun s : L => mvfderiv I (fun q => ψ s.1 (f q)) p w)
    (hC₁ : f '' Rc ∩ O = {y' | y' ∈ O ∩ B₀ ∧ ∀ s ∈ L, ψ s y' ≤ 0})
    (hcl : ∀ s, X ∩ f ⁻¹' {y} ⊆ Sum.elim F (fun _ => V) s → s ∈ L) :
    ∃ (B : Set H) (d : HalfChart_BCF B (f '' (Bd ∩ Rc))), y ∈ d.O ∧ (d.L y + d.κ = 0 ↔ Rb y) := by
  classical
  obtain ⟨ℓ₀, O', hO'o, hyO', hO'O, hℓ₀L, hLh, hZ0, hvR⟩ := circleBase_labels_BCF hRcM hRsat hRcX
    hB hdisj hFBd hKcl hsat1 hRb1 hRb2 hyΓ hO hyO L ψ (fun s hs => ⟨(hψ s hs).2.1, (hψ s hs).2.2⟩)
    hcl
  have hΓB : f '' (Bd ∩ Rc) ⊆ B₀ := by
    rintro _ ⟨q, hq, rfl⟩
    exact hB q (hRcX hq.2)
  -- the point `φ (0, 1)` of the fibre over `y`
  have hp : φ (0, (1 : Circle)) ∈ X ∩ f ⁻¹' {y} := by
    have hr : φ (0, (1 : Circle)) ∈ range φ := mem_range_self _
    rw [hφr] at hr
    exact ⟨hr.1, by rw [mem_preimage, mem_singleton_iff, hf, hσ0]⟩
  have hsurj' : Surjective fun w : TangentSpace I (φ (0, (1 : Circle))) =>
      fun i : L => mvfderiv I (fun q => ψ i.1 (f q)) (φ (0, (1 : Circle))) w := hsurj _ hp
  have hψc : ∀ i : L, ContDiffOn ℝ ∞ (ψ i.1) O' := fun i => (hψ i.1 i.2).1.mono hO'O
  have hψ0 : ∀ i : L, ψ i.1 y = 0 := fun i => (hψ i.1 i.2).2.1
  -- the points of `C₁ ∩ O'` and the sublevel description
  have hmemC : ∀ y' ∈ O' ∩ B₀, (∀ s ∈ L, ψ s y' ≤ 0) → y' ∈ f '' Rc := by
    intro y' hy' h
    have : y' ∈ f '' Rc ∩ O := by
      rw [hC₁]
      exact ⟨⟨hO'O hy'.1, hy'.2⟩, h⟩
    exact this.1
  have hsub : ∀ y' ∈ O', y' ∈ f '' Rc → ∀ s ∈ L, ψ s y' ≤ 0 := by
    intro y' hy' hC s hs
    have : y' ∈ f '' Rc ∩ O := ⟨hC, hO'O hy'⟩
    rw [hC₁] at this
    exact this.2 s hs
  by_cases hv : (Sum.inr () : Λ ⊕ Unit) ∈ L
  · -- a corner: the horizontal and the vertical label
    have hne : (⟨Sum.inl ℓ₀, hℓ₀L⟩ : L) ≠ ⟨Sum.inr (), hv⟩ := fun h => by
      have := congrArg Subtype.val h
      exact Sum.inl_ne_inr this
    have hι : ∀ i : L, i = ⟨Sum.inl ℓ₀, hℓ₀L⟩ ∨ i = ⟨Sum.inr (), hv⟩ := fun i =>
      (hLh i.1 i.2).imp Subtype.ext Subtype.ext
    obtain ⟨B, d, hd1, hd2⟩ := exists_halfChart_of_circleCorner_BCF (I := I) (f := f) (B₀ := B₀)
      (Γ := f '' (Bd ∩ Rc)) (σ := σ) (φ := φ) (Oσ := Oσ) hσ0 hσ hσe hσd hOσ hrange hφ hdim hf hΓB
      hO'o hyO' (fun i : L => ψ i.1) hψc hψ0 ⟨Sum.inl ℓ₀, hℓ₀L⟩ ⟨Sum.inr (), hv⟩ hne hι
      (1 : Circle) hsurj' (fun y' hy' => by
        constructor
        · intro hΓ
          obtain ⟨hC, h0⟩ := (hZ0 y' hy').mp hΓ
          exact ⟨h0, hsub y' hy'.1 hC _ hv⟩
        · rintro ⟨h0, hle⟩
          refine (hZ0 y' hy').mpr ⟨hmemC y' hy' fun s hs => ?_, h0⟩
          rcases hLh s hs with rfl | rfl
          · exact h0.le
          · exact hle)
    exact ⟨B, d, hd1, ⟨fun _ => hvR.mp hv, fun _ => hd2⟩⟩
  · -- an interior point of the curve
    have hι : ∀ i : L, i = ⟨Sum.inl ℓ₀, hℓ₀L⟩ := fun i => by
      rcases hLh i.1 i.2 with h | h
      · exact Subtype.ext h
      · exact absurd (h ▸ i.2) hv
    obtain ⟨B, d, hd1, hd2⟩ := exists_halfChart_of_circleInterior_BCF (I := I) (f := f)
      (B₀ := B₀) (Γ := f '' (Bd ∩ Rc)) (σ := σ) (φ := φ) (Oσ := Oσ) hσ0 hσ hσe hσd hOσ hrange hφ
      hdim hf hΓB hO'o hyO' (fun i : L => ψ i.1) hψc hψ0 ⟨Sum.inl ℓ₀, hℓ₀L⟩ (1 : Circle) hsurj'
      (fun y' hy' => by
        constructor
        · intro hΓ
          exact ((hZ0 y' hy').mp hΓ).2
        · intro h0
          refine (hZ0 y' hy').mpr ⟨hmemC y' hy' fun s hs => ?_, h0⟩
          rcases hLh s hs with rfl | rfl
          · exact h0.le
          · exact absurd hs hv)
    exact ⟨B, d, hd1, ⟨fun h => absurd h hd2.ne', fun h => absurd (hvR.mpr h) hv⟩⟩

end DifferentialGeometry.Topology
