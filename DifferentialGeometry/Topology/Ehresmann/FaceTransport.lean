import DifferentialGeometry.Topology.Ehresmann.BandMargin
import DifferentialGeometry.Analysis.ODE.TimeDependentFlow.FiniteOrder.CompactSupportFlow

set_option autoImplicit false

noncomputable section

open Set Filter Function Manifold
open scoped ContDiff Manifold Topology

namespace DifferentialGeometry.Topology.Ehresmann

section LocalLift

variable {E F H M : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

/-- A spatial submersion has an actual local smooth lift of time tangent to every fibre. -/
theorem exists_local_smoothTimeLift_of_spatial_surjective
    (h : M × ℝ → F) (hh : ContMDiff (I.prod 𝓘(ℝ)) 𝓘(ℝ, F) ∞ h)
    (x₀ : M × ℝ)
    (hrank : Surjective (mfderiv I 𝓘(ℝ, F) (fun y => h (y, x₀.2)) x₀.1)) :
    ∃ U ∈ 𝓝 x₀, ∃ X : ∀ x : M × ℝ, TangentSpace (I.prod 𝓘(ℝ)) x,
      ContMDiffOn (I.prod 𝓘(ℝ)) (I.prod 𝓘(ℝ)).tangent ∞
        (fun x => (⟨x, X x⟩ : TangentBundle (I.prod 𝓘(ℝ)) (M × ℝ))) U ∧
      ∀ x ∈ U,
        mfderiv (I.prod 𝓘(ℝ)) 𝓘(ℝ, F) h x (X x) = 0 ∧ (X x).2 = 1 := by
  let G : M × ℝ → F × ℝ := fun x => (h x, x.2)
  have hG : ContMDiff (I.prod 𝓘(ℝ)) 𝓘(ℝ, F × ℝ) ∞ G := hh.prodMk_space contMDiff_snd
  have hd := (hh x₀).mdifferentiableAt (by simp)
  have hincl : MDifferentiableAt I (I.prod 𝓘(ℝ)) (fun y : M => (y, x₀.2)) x₀.1 :=
    mdifferentiableAt_id.prodMk mdifferentiableAt_const
  have hchain := mfderiv_comp x₀.1 hd hincl
  rw [mfderiv_prod_left] at hchain
  have hsurj : Surjective (mfderiv (I.prod 𝓘(ℝ)) 𝓘(ℝ, F × ℝ) G x₀) := by
    rintro ⟨v, t⟩
    obtain ⟨w, hw⟩ := hrank (v - t • (show F from mfderiv (I.prod 𝓘(ℝ)) 𝓘(ℝ, F) h x₀ (0, 1)))
    have hw' : mfderiv (I.prod 𝓘(ℝ)) 𝓘(ℝ, F) h x₀ (w, 0) =
        v - t • (show F from mfderiv (I.prod 𝓘(ℝ)) 𝓘(ℝ, F) h x₀ (0, 1)) := by
      change mfderiv I 𝓘(ℝ, F) (h ∘ fun y : M => (y, x₀.2)) x₀.1 w = _ at hw
      rw [hchain] at hw
      exact hw
    refine ⟨(w, t), ?_⟩
    change mfderiv (I.prod 𝓘(ℝ)) 𝓘(ℝ, F × ℝ) (fun x => (h x, x.2)) x₀ (w, t) = _
    rw [modelWithCornersSelf_prod, ← chartedSpaceSelf_prod, mfderiv_prodMk hd mdifferentiableAt_snd]
    apply Prod.ext
    · change (show E × ℝ →L[ℝ] F from mfderiv (I.prod 𝓘(ℝ)) 𝓘(ℝ, F) h x₀)
        ((show E from w), t) = v
      have heq : ((show E from w), t) = ((show E from w), (0 : ℝ)) +
          t • ((0 : E), (1 : ℝ)) := by
        apply Prod.ext
        · change (show E from w) = (show E from w) + t • (0 : E)
          rw [smul_zero]
          exact (add_zero (show E from w)).symm
        · change t = (0 : ℝ) + t * 1
          ring
      erw [heq, map_add, map_smul, hw', sub_add_cancel]
    · rw [mfderiv_snd]
      rfl
  let Z : (x : F × ℝ) → TangentSpace 𝓘(ℝ, F × ℝ) x := fun _x => (0, 1)
  have hZ : ContMDiff 𝓘(ℝ, F × ℝ) 𝓘(ℝ, F × ℝ).tangent ∞
      (fun x => (⟨x, Z x⟩ : TangentBundle 𝓘(ℝ, F × ℝ) (F × ℝ))) :=
    contMDiff_vectorSpace_iff_contDiff.mpr contDiff_const
  obtain ⟨U, hU, X, hXs, hrel, _hzero⟩ :=
    exists_local_smoothDerivativeLift_of_surjective G hG Z hZ x₀ hsurj
  refine ⟨U, hU, X, hXs, fun x hx => ?_⟩
  have hd' := (hh x).mdifferentiableAt (by simp)
  have heq := hrel x hx
  change mfderiv (I.prod 𝓘(ℝ)) 𝓘(ℝ, F × ℝ) (fun x => (h x, x.2)) x (X x) = (0, 1) at heq
  rw [modelWithCornersSelf_prod, ← chartedSpaceSelf_prod,
    mfderiv_prodMk hd' mdifferentiableAt_snd] at heq
  constructor
  · exact congrArg Prod.fst heq
  · have hsnd := congrArg Prod.snd heq
    rw [mfderiv_snd] at hsnd
    change (X x).2 = 1 at hsnd
    exact hsnd

end LocalLift

variable {E V H M ι : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup V] [NormedSpace ℝ V]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [T2Space M] [SigmaCompactSpace M]

/-- Partition of unity preserves every specified affine equation on its own stratum. -/
theorem exists_smoothAffineConstraintSection_of_local
    (A : ∀ _i : ι, ∀ x : M, TangentSpace I x →L[ℝ] V)
    (b : ι → M → V) (stratum : ι → Set M)
    {K : Set M} (hK : IsCompact K)
    (hlocal : ∀ x₀ : M, ∃ U ∈ 𝓝 x₀, ∃ X : ∀ x : M, TangentSpace I x,
      ContMDiffOn I I.tangent ∞ (fun x => (⟨x, X x⟩ : TangentBundle I M)) U ∧
      (∀ x ∈ U, ∀ i, x ∈ stratum i → A i x (X x) = b i x) ∧
      (∀ x ∈ U, x ∉ K → X x = 0)) :
    ∃ X : Cₛ^∞⟮I; E, TangentSpace I⟯,
      (∀ x i, x ∈ stratum i → A i x (X x) = b i x) ∧
      tsupport X ⊆ K ∧ IsCompact (tsupport X) := by
  let S : ∀ x : M, Set (TangentSpace I x) := fun x =>
    {v | (∀ i, x ∈ stratum i → A i x v = b i x) ∧ (x ∉ K → v = 0)}
  have hconv : ∀ x, Convex ℝ (S x) := by
    intro x v hv w hw α β hα hβ hsum
    constructor
    · intro i hi
      rw [map_add, map_smul, map_smul, hv.1 i hi, hw.1 i hi,
        ← add_smul, hsum, one_smul]
    · intro hx
      rw [hv.2 hx, hw.2 hx, smul_zero, smul_zero, add_zero]
  have hloc : ∀ x₀ : M, ∃ U ∈ 𝓝 x₀, ∃ X : ∀ x : M, TangentSpace I x,
      ContMDiffOn I I.tangent ∞ (fun x => (⟨x, X x⟩ : TangentBundle I M)) U ∧
      ∀ x ∈ U, X x ∈ S x := by
    intro x₀
    obtain ⟨U, hU, X, hX, hA, hzero⟩ := hlocal x₀
    exact ⟨U, hU, X, hX, fun x hx => ⟨hA x hx, hzero x hx⟩⟩
  obtain ⟨X, hX⟩ := exists_contMDiffSection_forall_mem_convex_of_local
    I (TangentSpace I) S hconv hloc
  have hsupp : tsupport X ⊆ K := by
    apply closure_minimal _ hK.isClosed
    intro x hx
    by_contra hxK
    exact hx ((hX x).2 hxK)
  exact ⟨X, fun x i hi => (hX x).1 i hi, hsupp,
    hK.of_isClosed_subset (isClosed_tsupport X) hsupp⟩

open DifferentialGeometry.Analysis.ODE

omit [SigmaCompactSpace M] in
/-- A jointly smooth field with common compact spatial support gives ambient diffeomorphisms. -/
theorem exists_compactSupport_ambientTransport
    [I.Boundaryless]
    (X : ℝ → ∀ x : M, TangentSpace I x)
    (hX : ContMDiff (𝓘(ℝ).prod I) I.tangent ∞
      (fun p : ℝ × M => (⟨p.2, X p.1 p.2⟩ : TangentBundle I M)))
    {K : Set M} (hK : IsCompact K) (hzero : ∀ t x, x ∉ K → X t x = 0) :
    ∃ Ψ : ℝ → ℝ → M ≃ₘ⟮I, I⟯ M,
      (∀ s x, Ψ s s x = x) ∧
      (∀ s t u x, Ψ t u (Ψ s t x) = Ψ s u x) ∧
      (∀ s t x, x ∉ K → Ψ s t x = x) ∧
      ∀ s t x, HasMFDerivAt 𝓘(ℝ) I (fun u => Ψ s u x) t
        ((1 : ℝ →L[ℝ] ℝ).smulRight (X t (Ψ s t x))) := by
  let V := X
  have hW := (contMDiff_autonomizedFlowVF_section V hX).of_le
    (by simp : (1 : ℕ∞ω) ≤ ∞)
  have hs : ∀ s x, finiteOrderFlow V s s x = x :=
    fun s x => finiteOrderFlow_self V hW hK hzero s x
  have hcomp := finiteOrderFlow_trans V hW hK hzero
  have hsm := contMDiff_finiteOrderFlow (n := (⊤ : ℕ∞)) (by simp) V hX hK hzero
  let D : ℝ → ℝ → M ≃ₘ⟮I, I⟯ M := fun s t =>
    { toEquiv :=
        { toFun := finiteOrderFlow V s t
          invFun := finiteOrderFlow V t s
          left_inv := fun x => (hcomp s t s x).trans (hs s x)
          right_inv := fun x => (hcomp t s t x).trans (hs t x) }
      contMDiff_toFun := hsm.comp ((contMDiff_const.prodMk contMDiff_const).prodMk contMDiff_id)
      contMDiff_invFun := hsm.comp ((contMDiff_const.prodMk contMDiff_const).prodMk contMDiff_id) }
  refine ⟨D, fun s x => hs s x, hcomp, ?_, ?_⟩
  · intro s t x hx
    exact finiteOrderFlow_eq_self_of_forall_eq_zero V hW (fun t => hzero t x hx) s t
  · intro s t x
    exact hasMFDerivAt_finiteOrderFlow V hW hK hzero s t x

end DifferentialGeometry.Topology.Ehresmann
