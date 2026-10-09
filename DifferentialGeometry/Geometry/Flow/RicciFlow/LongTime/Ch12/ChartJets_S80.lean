import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch12.CkErrInverse_S80
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch12.HPS01Reduction_O26

set_option autoImplicit false

/-!
# CH12-S80 / G2b: `ckErr_of_chartJets_S80`

Frozen statement: `[FROZEN] CH12-S80` (DELIVERIES).  From the CX3 transfer-isotopy output (joint
smoothness, two-time group law, `Ψ 0 t = scaledExp X t` on `D`, chart-displacement jets of
`scaledExp X t`) and the speed/location input `Ψ μ 0 '' B ⊆ D'` to `ckErr_S45 H H.metric 1 (Ψ μ · 0) j ≤ ε`
for all `μ ∈ [0,1]`.  The forward conversion chart jets ⇒ `ckErr` is the inline binder `hchart` (awaits O35's
chart connection identity); the inverse step is `ckErr_inverse_S80`.
-/

noncomputable section

open DifferentialGeometry DifferentialGeometry.Geometry.Hyperbolic
open DifferentialGeometry.CheegerGromovCompactness
open DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions
open Set TopologicalSpace
open scoped Manifold ContDiff

namespace GC.LongTime.Ch12

universe u

theorem ckErr_of_chartJets_S80 (H : FiniteVolumeHyperbolicModel.{u})
    (hchart : ∀ (A : CkAtlas_S15 (𝓡 3) H.Carrier) (D : Set H.Carrier) (k : ℕ) (ε : ℝ),
      IsCompact D → D ⊆ A.cover → 0 < ε → ∃ δ : ℝ, 0 < δ ∧
        ∀ (F : H.Carrier → H.Carrier) (O : Set H.Carrier), IsOpen O → D ⊆ O →
          ContMDiffOn (𝓡 3) (𝓡 3) ∞ F O → CkCloseInAtlas_CX3 A D (k + 1) δ F →
          ∀ j : ℕ, j ≤ k → ∀ q ∈ D, ckErr_S45 H H.metric 1 F j q ≤ ε)
    (A : CkAtlas_S15 (𝓡 3) H.Carrier) (D D' : Set H.Carrier) (B : Opens H.Carrier)
    (hD'c : IsCompact D') (hD'D : D' ⊆ interior D) (hD'A : D' ⊆ A.cover) (k : ℕ)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ ε₀ : ℝ, 0 < ε₀ ∧ ∀ (Ψ : ℝ → ℝ → H.Carrier → H.Carrier) (W : ℝ → H.Carrier → H.Carrier),
      ContMDiff ((𝓘(ℝ, ℝ).prod 𝓘(ℝ, ℝ)).prod (𝓡 3)) (𝓡 3) ∞
        (fun q : (ℝ × ℝ) × H.Carrier => Ψ q.1.1 q.1.2 q.2) →
      (∀ s y, Ψ s s y = y) → (∀ s t u y, Ψ t u (Ψ s t y) = Ψ s u y) →
      (∀ t ∈ Icc (0 : ℝ) 1, ∀ x ∈ D, Ψ 0 t x = W t x) →
      (∀ t ∈ Icc (0 : ℝ) 1, CkCloseInAtlas_CX3 A D (k + 1) ε₀ (W t)) →
      (∀ μ ∈ Icc (0 : ℝ) 1, ∀ p ∈ (B : Set H.Carrier), Ψ μ 0 p ∈ D') →
      ∀ μ ∈ Icc (0 : ℝ) 1, ∀ j : ℕ, j ≤ k → ∀ p ∈ (B : Set H.Carrier),
        ckErr_S45 H H.metric 1 (fun x => Ψ μ 0 x) j p ≤ ε := by
  obtain ⟨δi, hδi, hinv⟩ := ckErr_inverse_S80 H B k hε
  obtain ⟨δc, hδc, hfwd⟩ := hchart A D' k (δi / 2) hD'c hD'A (by positivity)
  refine ⟨δc, hδc, fun Ψ W hΨ hself hcoc hW hjets hloc μ hμ j hj p hp => ?_⟩
  have hsm : ∀ a b : ℝ, ContMDiff (𝓡 3) (𝓡 3) ∞ (fun x : H.Carrier => Ψ a b x) := fun a b =>
    hΨ.comp (contMDiff_const (c := ((a, b) : ℝ × ℝ)).prodMk contMDiff_id)
  let e : H.Carrier ≃ₘ⟮𝓡 3, 𝓡 3⟯ H.Carrier :=
    { toEquiv :=
        { toFun := fun x => Ψ μ 0 x
          invFun := fun y => Ψ 0 μ y
          left_inv := fun x => by
            change Ψ 0 μ (Ψ μ 0 x) = x
            rw [hcoc μ 0 μ x, hself]
          right_inv := fun y => by
            change Ψ μ 0 (Ψ 0 μ y) = y
            rw [hcoc 0 μ 0 y, hself] }
      contMDiff_toFun := hsm μ 0
      contMDiff_invFun := hsm 0 μ }
  have hsymm : (e.symm : H.Carrier → H.Carrier) = fun y => Ψ 0 μ y := rfl
  have hone : ∀ j ≤ k, ∀ y ∈ e '' (B : Set H.Carrier),
      ckErr_S45 H H.metric 1 (e.symm : H.Carrier → H.Carrier) j y < δi := by
    rintro j' hj' y ⟨p', hp', rfl⟩
    have hDcl : CkCloseInAtlas_CX3 A D' (k + 1) δc (fun y => Ψ 0 μ y) :=
      CkCloseInAtlas_congr_O26 (O := interior D) isOpen_interior hD'D
        (fun z hz => (hW μ hμ z (interior_subset hz)).symm)
        (fun i x hx hxD => hjets μ hμ i x hx (interior_subset (hD'D hxD)))
    have := hfwd (fun y => Ψ 0 μ y) (interior D) isOpen_interior hD'D (hsm 0 μ).contMDiffOn hDcl
      j' hj' (e p') (hloc μ hμ p' hp')
    rw [hsymm]
    exact lt_of_le_of_lt this (by linarith)
  exact (hinv e hone j hj p hp).le

end GC.LongTime.Ch12
