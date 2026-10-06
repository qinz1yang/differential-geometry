import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.CuspP1.FamilyIsotopyMain

/-!
# CH12-S15, H1 group A: ambient isotopy of a smooth family of transfer maps

The family `E_λ(p) = exp_p (λ χ(p) exp_p⁻¹ Φ(p))` of HPS03 starts at the identity.  Once it is a
jointly smooth family of immersions injective on `K`, the CuspP1 isotopy extension (CPD5) gives
globally defined diffeomorphisms `Ê_λ` of the ambient manifold, compactly supported, with
`Ê_λ = E_λ` on `K`.  This is the global-diffeomorphism assertion of HPS03 for the part of the
isotopy that is seen by the compact core, without the covering/homotopy argument.
-/

set_option autoImplicit false
open scoped Manifold ContDiff Topology
open Set Function
noncomputable section
namespace GC.LongTime.Ch12

open GC.LongTime.CuspP1

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [T2Space M] [SigmaCompactSpace M]

/-- **HPS03 (global part).**  A jointly smooth family `F` of immersions, starting at the identity
on a compact `K` and injective on `K` for each `λ`, extends over `K` to a compactly supported
smooth ambient isotopy `Ψ`; in particular each `Ψ 0 λ` is a global diffeomorphism with
`Ψ 0 0 = id` and `Ψ 0 λ = F λ` on `K`. -/
theorem transfer_ambient_isotopy_S15
    {F : ℝ × M → M} {J : Set ℝ} {U : Set M} (hJ : IsOpen J) (hU : IsOpen U)
    {K : Set M} (hK : IsCompact K) (hKU : K ⊆ U) {a b : ℝ} (hab : a ≤ b)
    (hJab : Icc a b ⊆ J) (h0 : 0 ∈ Icc a b)
    (hF : ContMDiffOn (𝓘(ℝ, ℝ).prod I) I ∞ F (J ×ˢ U))
    (himm : ∀ t ∈ J, ∀ x ∈ U, Function.Injective (mfderiv I I (fun y => F (t, y)) x))
    (hinj : ∀ t ∈ J, InjOn (fun y => F (t, y)) K)
    (hstart : ∀ x ∈ K, F (0, x) = x) :
    ∃ (Ψ : ℝ → ℝ → M → M) (C : Set M), IsCompact C ∧
      ContMDiff ((𝓘(ℝ, ℝ).prod 𝓘(ℝ, ℝ)).prod I) I ∞
        (fun q : (ℝ × ℝ) × M => Ψ q.1.1 q.1.2 q.2) ∧
      (∀ s y, Ψ s s y = y) ∧ (∀ s t u y, Ψ t u (Ψ s t y) = Ψ s u y) ∧
      (∀ s t y, y ∉ C → Ψ s t y = y) ∧
      (∀ t ∈ Icc a b, ∀ x ∈ K, Ψ 0 t x = F (t, x)) := by
  obtain ⟨Ψ, C, hC, hsm, hself, hcoc, hsupp, hF'⟩ :=
    exists_ambient_isotopy_of_smooth_family_CPD5 (I := I) hJ hU hK hKU hab hJab hF himm hinj
  refine ⟨Ψ, C, hC, hsm, hself, hcoc, hsupp, fun t ht x hx => ?_⟩
  have := hF' 0 h0 t ht x hx
  rwa [hstart x hx] at this

/-- each time-slice of the ambient isotopy is a global smooth diffeomorphism. -/
def transferDiffeo_S15 (Ψ : ℝ → ℝ → M → M)
    (hsm : ContMDiff ((𝓘(ℝ, ℝ).prod 𝓘(ℝ, ℝ)).prod I) I ∞
      (fun q : (ℝ × ℝ) × M => Ψ q.1.1 q.1.2 q.2))
    (hself : ∀ s y, Ψ s s y = y) (hcoc : ∀ s t u y, Ψ t u (Ψ s t y) = Ψ s u y) (s t : ℝ) :
    Diffeomorph I I M M ∞ where
  toEquiv :=
    { toFun := Ψ s t, invFun := Ψ t s
      left_inv := fun y => by rw [hcoc, hself]
      right_inv := fun y => by rw [hcoc, hself] }
  contMDiff_toFun := by
    have : ContMDiff I ((𝓘(ℝ, ℝ).prod 𝓘(ℝ, ℝ)).prod I) ∞ (fun y : M => ((s, t), y)) :=
      contMDiff_const.prodMk contMDiff_id
    exact hsm.comp this
  contMDiff_invFun := by
    have : ContMDiff I ((𝓘(ℝ, ℝ).prod 𝓘(ℝ, ℝ)).prod I) ∞ (fun y : M => ((t, s), y)) :=
      contMDiff_const.prodMk contMDiff_id
    exact hsm.comp this

end GC.LongTime.Ch12
