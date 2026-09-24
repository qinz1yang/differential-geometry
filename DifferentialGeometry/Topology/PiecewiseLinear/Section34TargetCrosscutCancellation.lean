import DifferentialGeometry.Topology.PiecewiseLinear.Section34SquareCrosscutCancellation
import DifferentialGeometry.Topology.PiecewiseLinear.Section34SecondTraceTransport

open Set Topology

namespace DifferentialGeometry.Topology.PiecewiseLinear

private theorem pullback_trace {E M : Type*} {u : E → M} {P S T : Set E}
    (hu : InjOn u P) (hSP : S ⊆ P) (hTS : T ⊆ S) {B : Set M}
    (htrace : u '' S ∩ B = u '' T) : (P ∩ u ⁻¹' B) ∩ S = T := by
  ext x
  constructor
  · rintro ⟨⟨hxP, hxB⟩, hxS⟩
    have hxT : u x ∈ u '' T := htrace ▸ ⟨mem_image_of_mem u hxS, hxB⟩
    obtain ⟨z, hz, hzx⟩ := hxT
    exact hu (hSP (hTS hz)) hxP hzx ▸ hz
  · intro hx
    have hxB : u x ∈ B := (htrace.symm ▸ mem_image_of_mem u hx).2
    exact ⟨⟨hSP (hTS hx), hxB⟩, hTS hx⟩

theorem IsPLHomeomorphInto.exists_second_trace_motion_of_two_interior_crossings
    {M : Type*} [TopologicalSpace M] [T2Space M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
    {P S : Set (EuclideanSpace ℝ (Fin 3))} {u : EuclideanSpace ℝ (Fin 3) → M}
    (hu : IsPLHomeomorphInto 3 u P) (hP : IsPolyhedron P)
    (hS : IsCompact S) (hSP : S ⊆ interior P) {A B : Set M} (hAP : A ⊆ u '' P)
    {N J L : Set (ℝ × ℝ)} (hN : IsPLBall 2 N) {γ δ : ℝ → ℝ × ℝ}
    (hγ : IsPLHomeomorphOn γ (Icc 0 1) J) (hJN : J ⊆ N)
    (hJends : J ∩ frontier N = {γ 0, γ 1})
    (hδ : IsPLHomeomorphOn δ (Icc 0 1) L) (hLN : L ⊆ N)
    (hLends : L ∩ frontier N = {δ 0, δ 1})
    (p : Fin 2 → ℝ × ℝ) (hpN : ∀ i, p i ∈ interior N) (hpne : p 0 ≠ p 1)
    (htrace : J ∩ L = {p 0, p 1})
    (e : Fin 2 → OpenPartialHomeomorph (ℝ × ℝ) (ℝ × ℝ))
    (ε : Fin 2 → ℝ) (hε : ∀ i, 0 < ε i)
    (hsource : ∀ i, Ioo (-ε i) (ε i) ×ˢ Ioo (-ε i) (ε i) ⊆ (e i).source)
    (hcenter : ∀ i, e i (0, 0) = p i)
    (hcurve : ∀ i, ∀ z ∈ Ioo (-ε i) (ε i) ×ˢ Ioo (-ε i) (ε i),
      e i z ∈ L ↔ z.2 = 0)
    (haxis : ∀ i, ∀ s ∈ Ioo (-ε i) (ε i), e i (0, s) ∈ J)
    {f : (ℝ × ℝ) × ℝ → EuclideanSpace ℝ (Fin 3)}
    (hf : IsCylindricalDiagram f N S) (hends : ∀ x ∈ N, f (x, 0) = f (x, 1))
    (hfront : frontier S ⊆ f '' (frontier N ×ˢ Icc (0 : ℝ) 1))
    (hB : u '' S ∩ B = (u ∘ f) '' (J ×ˢ Icc (0 : ℝ) 1))
    (hA : u '' S ∩ A = (u ∘ f) '' (L ×ˢ Icc (0 : ℝ) 1))
    {ι : Type*} [Finite ι] {Γ : ι → Set M}
    (hΓ : ∀ i, IsPolyhedralSphere (n := 3) 1 (Γ i))
    (hΓdis : Pairwise fun i j => Disjoint (Γ i) (Γ j)) (hfull : A ∩ B = ⋃ i, Γ i) :
    ∃ (I : Set ι) (ψ : M ≃ₜ M), Nat.card I < Nat.card ι ∧
      IsCompact (u '' S) ∧ EqOn ψ id (u '' S)ᶜ ∧
      IsPLOn 3 3 ψ (interior (u '' P)) ∧
      (∀ i : I, Disjoint (u '' S) (Γ i.1)) ∧
      (∀ i : I, ∀ x ∈ Γ i.1, ψ =ᶠ[𝓝 x] id) ∧ A ∩ ψ '' B = ⋃ i : I, Γ i.1 := by
  let τ := Function.invFunOn u P
  have hSP' : S ⊆ P := hSP.trans interior_subset
  have hJS : f '' (J ×ˢ Icc (0 : ℝ) 1) ⊆ S := by
    rw [← hf.image_eq]
    exact image_mono (prod_mono hJN Subset.rfl)
  have hLS : f '' (L ×ˢ Icc (0 : ℝ) 1) ⊆ S := by
    rw [← hf.image_eq]
    exact image_mono (prod_mono hLN Subset.rfl)
  have hX : (P ∩ u ⁻¹' B) ∩ S = f '' (J ×ˢ Icc (0 : ℝ) 1) :=
    pullback_trace hu.injOn hSP' hJS (hB.trans (image_comp u f _))
  have hYeq : τ '' A = P ∩ u ⁻¹' A := by
    have hleft : LeftInvOn τ u P := hu.injOn.leftInvOn_invFunOn
    have hright : RightInvOn τ u (u '' P) := hu.injOn.bijOn_image.invOn_invFunOn.2
    have hmap : MapsTo τ (u '' P) P := hu.injOn.bijOn_image.surjOn.mapsTo_invFunOn
    ext x
    constructor
    · rintro ⟨a, ha, rfl⟩
      refine ⟨hmap (hAP ha), ?_⟩
      change u (τ a) ∈ A
      rwa [hright (hAP ha)]
    · rintro ⟨hxP, hxA⟩
      exact ⟨u x, hxA, hleft hxP⟩
  have hY : (τ '' A) ∩ S = f '' (L ×ˢ Icc (0 : ℝ) 1) := by
    rw [hYeq]
    exact pullback_trace hu.injOn hSP' hLS (hA.trans (image_comp u f _))
  obtain ⟨hmodelΓ, hmodelDis, hmodelFull⟩ :=
    hu.invFunOn_second_trace_family hAP hΓ hΓdis hfull
  obtain ⟨I, H, hlt, hH, hfix, hkeep, -, hmodelTrace⟩ :=
    exists_strict_square_cylindrical_cancellation_of_two_interior_crossings
      hN hγ hJN hJends hδ hLN hLends p hpN hpne htrace e ε hε hsource hcenter
      hcurve haxis hf hends hfront hX hY hmodelΓ hmodelDis hmodelFull
  obtain ⟨ψ, hcompact, hoff, hPL, hdis, hgerms, hfinal⟩ :=
    hu.exists_second_trace_motion_of_model_motion hP hS hSP hAP hfull I H
      hH hfix hkeep hmodelTrace
  exact ⟨I, ψ, hlt, hcompact, hoff, hPL, hdis, hgerms, hfinal⟩

end DifferentialGeometry.Topology.PiecewiseLinear
