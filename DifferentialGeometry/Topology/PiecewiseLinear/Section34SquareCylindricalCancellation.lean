import DifferentialGeometry.Topology.PiecewiseLinear.Section34CylindricalBigonCancellation
import DifferentialGeometry.Topology.PiecewiseLinear.FourSpokeSquareWitness

open Set Topology

namespace DifferentialGeometry.Topology.PiecewiseLinear

theorem exists_strict_square_cylindrical_cancellation_of_two_crossing_crosscuts
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    {N J L : Set (ℝ × ℝ)} (hN : IsPLBall 2 N) {γ δ : ℝ → ℝ × ℝ}
    (hγ : IsPLHomeomorphOn γ (Icc 0 1) J) (hJN : J ⊆ N)
    (hJends : J ∩ frontier N = {γ 0, γ 1})
    (hδ : IsPLHomeomorphOn δ (Icc 0 1) L) (hLN : L ⊆ N)
    (hLends : L ∩ frontier N = {δ 0, δ 1})
    (t : Fin 2 → ℝ) (h₀ : 0 < t 0) (h₀₁ : t 0 < t 1) (h₁ : t 1 < 1)
    (htrace : J ∩ L = {γ (t 0), γ (t 1)})
    (e : Fin 2 → OpenPartialHomeomorph (ℝ × ℝ) (ℝ × ℝ))
    (ε : Fin 2 → ℝ) (hε : ∀ i, 0 < ε i)
    (hsource : ∀ i, Ioo (-ε i) (ε i) ×ˢ Ioo (-ε i) (ε i) ⊆ (e i).source)
    (hcenter : ∀ i, e i (0, 0) = γ (t i))
    (hcurve : ∀ i, ∀ p ∈ Ioo (-ε i) (ε i) ×ˢ Ioo (-ε i) (ε i),
      e i p ∈ L ↔ p.2 = 0)
    (haxis : ∀ i, ∀ s ∈ Ioo (-ε i) (ε i), e i (0, s) ∈ J)
    {f : (ℝ × ℝ) × ℝ → E} {S X Y : Set E}
    (hf : IsCylindricalDiagram f N S) (hends : ∀ x ∈ N, f (x, 0) = f (x, 1))
    (hfront : frontier S ⊆ f '' (frontier N ×ˢ Icc (0 : ℝ) 1))
    (hX : X ∩ S = f '' (J ×ˢ Icc (0 : ℝ) 1))
    (hY : Y ∩ S = f '' (L ×ˢ Icc (0 : ℝ) 1))
    {ι : Type*} [Finite ι] {Γ : ι → Set E} (hΓ : ∀ i, IsPLSphere 1 (Γ i))
    (hΓdis : Pairwise fun i j => Disjoint (Γ i) (Γ j)) (hfull : X ∩ Y = ⋃ i, Γ i) :
    ∃ (I : Set ι) (H : E ≃ₜ E), Nat.card I < Nat.card ι ∧
      IsPLHomeomorphOn H univ univ ∧ EqOn H id Sᶜ ∧
      (∀ i : I, Disjoint S (Γ i.1)) ∧
      (∀ i : I, ∀ x ∈ Γ i.1, H =ᶠ[𝓝 x] id) ∧ H '' X ∩ Y = ⋃ i : I, Γ i.1 := by
  let ℓ := fourSpokePlaneEquiv
  have hℓN : IsPLHomeomorphOn ℓ N (ℓ '' N) :=
    isPLHomeomorphOn_fourSpokePlaneEquiv hN.isPolyhedron
  have hℓJ : IsPLHomeomorphOn ℓ J (ℓ '' J) :=
    isPLHomeomorphOn_fourSpokePlaneEquiv
      ((isPLBall_Icc (by norm_num : (0 : ℝ) < 1)).of_isPLHomeomorphOn hγ).isPolyhedron
  have hℓL : IsPLHomeomorphOn ℓ L (ℓ '' L) :=
    isPLHomeomorphOn_fourSpokePlaneEquiv
      ((isPLBall_Icc (by norm_num : (0 : ℝ) < 1)).of_isPLHomeomorphOn hδ).isPolyhedron
  have hℓinv : IsPLHomeomorphOn ℓ.symm (ℓ '' N) N := by
    apply hℓN.symm.congr
    intro x hx
    have hh := congrArg ℓ.symm (hℓN.bijOn.invOn_invFunOn.2 hx)
    simpa only [ContinuousLinearEquiv.symm_apply_apply] using hh.symm
  let f' := f ∘ Prod.map ℓ.symm id
  have hf' : IsCylindricalDiagram f' (ℓ '' N) S := hf.precomp_base_equivalence hℓinv
  have hends' (x) (hx : x ∈ ℓ '' N) : f' (x, 0) = f' (x, 1) := by
    obtain ⟨p, hp, rfl⟩ := hx
    simpa only [f', Function.comp_apply, Prod.map_apply, id_eq,
      ContinuousLinearEquiv.symm_apply_apply] using hends p hp
  have hregion (B : Set (ℝ × ℝ)) :
      f' '' ((ℓ '' B) ×ˢ Icc (0 : ℝ) 1) = f '' (B ×ˢ Icc (0 : ℝ) 1) := by
    rw [show f' = f ∘ Prod.map ℓ.symm id from rfl, image_comp,
      prodMap_image_prod, image_id, ℓ.symm_image_image]
  have hℓfront : ℓ '' frontier N = frontier (ℓ '' N) :=
    ℓ.toHomeomorph.image_frontier N
  have hfront' : frontier S ⊆ f' '' (frontier (ℓ '' N) ×ˢ Icc (0 : ℝ) 1) := by
    rw [← hℓfront, hregion]
    exact hfront
  have hJends' : (ℓ '' J) ∩ frontier (ℓ '' N) = {(ℓ ∘ γ) 0, (ℓ ∘ γ) 1} := by
    rw [← hℓfront, ← image_inter ℓ.injective, hJends, image_pair]
    rfl
  have hLends' : (ℓ '' L) ∩ frontier (ℓ '' N) = {(ℓ ∘ δ) 0, (ℓ ∘ δ) 1} := by
    rw [← hℓfront, ← image_inter ℓ.injective, hLends, image_pair]
    rfl
  have htrace' : (ℓ '' J) ∩ (ℓ '' L) = {(ℓ ∘ γ) (t 0), (ℓ ∘ γ) (t 1)} := by
    rw [← image_inter ℓ.injective, htrace, image_pair]
    rfl
  let e' := fun i => (e i).transHomeomorph ℓ.toHomeomorph
  apply exists_strict_cylindrical_cancellation_of_two_crossing_crosscuts
    (hN.of_isPLHomeomorphOn hℓN) (hγ.trans hℓJ) (image_mono hJN) hJends'
    (hδ.trans hℓL) (image_mono hLN) hLends' t h₀ h₀₁ h₁ htrace' e' ε hε
    (fun i => hsource i) (fun i => congrArg ℓ (hcenter i))
    (fun i p hp => ?_) (fun i s hs => ?_) hf' hends' hfront'
    (hX.trans (hregion J).symm) (hY.trans (hregion L).symm) hΓ hΓdis hfull
  · change ℓ (e i p) ∈ ℓ '' L ↔ p.2 = 0
    rw [ℓ.injective.mem_set_image]
    exact hcurve i p hp
  · exact mem_image_of_mem ℓ (haxis i s hs)

end DifferentialGeometry.Topology.PiecewiseLinear
