import DifferentialGeometry.Topology.Manifold.FiniteOrderFlow.DerivativeLift
import DifferentialGeometry.Analysis.ODE.TimeDependentFlow.FiniteOrder.Suspension
import Mathlib.Geometry.Manifold.PartitionOfUnity
import Mathlib.Geometry.Manifold.VectorBundle.ContMDiffSection

/-!
# The time-lifting field of a regular sublevel of a regular level

Let `Ψ : ℝ × M → G` and `B : ℝ × M → ℝ` be `C^m`. Suppose that for every time `t` the slice
`Ψ (t, ·)` is a submersion along `W_t = {Ψ (t, ·) = 0, B (t, ·) ≥ 0}` and that the slice
`(Ψ, B) (t, ·)` is a submersion along `∂W_t = {Ψ (t, ·) = 0, B (t, ·) = 0}`, and that all the
`W_t` lie in one compact set `S` inside an open set `N`. Then there is a jointly `C^n` time-dependent
vector field `V` (`n + 1 ≤ m`), vanishing off a compact set `K ⊆ N`, with
`dΨ (1, V) = 0` on an open neighbourhood of the trace `{Ψ = 0, B ≥ 0}` and `dB (1, V) = 0` on an
open neighbourhood of the boundary trace `{Ψ = 0, B = 0}` (kernel A of
`build-logs/resume/sheet-W5-FLOW.md`, statement S2).

This is the construction of the field in blueprint LFR03 (A:24982–24995): local right inverses
of the spatial derivative (here: local lifts of `(1, 0)` through `q ↦ (q.1, Ψ q)` resp.
`q ↦ (q.1, Ψ q, B q)`, `exists_local_derivativeLift_of_surjective_Cn`), a partition of unity on
`ℝ × M` (`exists_contMDiffSection_forall_mem_convex_of_local`, with an affine, hence convex,
constraint), and a spatial cutoff. `M` may have boundary here; only the later flow needs a
boundaryless `M`.
-/

set_option autoImplicit false

noncomputable section

open Set Function Filter Bundle
open scoped ContDiff Manifold Topology

namespace DifferentialGeometry.Analysis.ODE

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

/-- **Local time lift.** If `Λ : ℝ × M → G''` is `C^m` and its slice `Λ (q₀.1, ·)` has surjective
derivative at `q₀.2`, then near `q₀` there is a `C^n` vector field `Y` on `ℝ × M` (`n + 1 ≤ m`)
with time component `1` and `dΛ (Y q) = 0`. -/
theorem exists_local_timeLift_Cn
    {G'' : Type*} [NormedAddCommGroup G''] [NormedSpace ℝ G''] [FiniteDimensional ℝ G'']
    {n : ℕ∞} {m : WithTop ℕ∞} (hmn : (n : WithTop ℕ∞) + 1 ≤ m)
    {Λ : ℝ × M → G''} (hΛ : ContMDiff (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, G'') m Λ) {q₀ : ℝ × M}
    (hsurj : Surjective (mfderiv I 𝓘(ℝ, G'') (fun y => Λ (q₀.1, y)) q₀.2)) :
    ∃ U ∈ 𝓝 q₀, ∃ Y : (q : ℝ × M) → TangentSpace (𝓘(ℝ, ℝ).prod I) q,
      ContMDiffOn (𝓘(ℝ, ℝ).prod I) (𝓘(ℝ, ℝ).prod I).tangent n
        (fun q ↦ (⟨q, Y q⟩ : TangentBundle (𝓘(ℝ, ℝ).prod I) (ℝ × M))) U ∧
      ∀ q ∈ U, (Y q).1 = 1 ∧ mfderiv (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, G'') Λ q (Y q) = 0 := by
  have hm0 : m ≠ 0 := by
    intro h
    rw [h] at hmn
    exact absurd hmn (by simp)
  have hΛd : MDifferentiable (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, G'') Λ := hΛ.mdifferentiable hm0
  set Θ : ℝ × M → ℝ × G'' := fun q => (q.1, Λ q) with hΘdef
  have hΘ : ContMDiff (𝓘(ℝ, ℝ).prod I) (𝓘(ℝ, ℝ).prod 𝓘(ℝ, G'')) m Θ :=
    contMDiff_fst.prodMk hΛ
  have hdΘ : ∀ (q : ℝ × M) (w : TangentSpace (𝓘(ℝ, ℝ).prod I) q),
      mfderiv (𝓘(ℝ, ℝ).prod I) (𝓘(ℝ, ℝ).prod 𝓘(ℝ, G'')) Θ q w =
        (w.1, mfderiv (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, G'') Λ q w) := by
    intro q w
    rw [hΘdef, mfderiv_prodMk mdifferentiableAt_fst (hΛd q), mfderiv_fst]
    rfl
  have hsurjΘ : Surjective (mfderiv (𝓘(ℝ, ℝ).prod I) (𝓘(ℝ, ℝ).prod 𝓘(ℝ, G'')) Θ q₀) := by
    rintro ⟨a, g⟩
    set d₀ : G'' := mfderiv (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, G'') Λ q₀
      (show TangentSpace (𝓘(ℝ, ℝ).prod I) q₀ from ((a, 0) : ℝ × E)) with hd₀
    obtain ⟨v, hv⟩ := hsurj (show TangentSpace 𝓘(ℝ, G'') (Λ (q₀.1, q₀.2)) from g - d₀)
    have hslice : mfderiv I 𝓘(ℝ, G'') (fun y => Λ (q₀.1, y)) q₀.2 v =
        mfderiv (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, G'') Λ q₀
          (show TangentSpace (𝓘(ℝ, ℝ).prod I) q₀ from ((0, show E from v) : ℝ × E)) := by
      have h := mfderiv_comp_apply (I := I) (I' := 𝓘(ℝ, ℝ).prod I) (I'' := 𝓘(ℝ, G''))
        (f := fun y : M => ((q₀.1, y) : ℝ × M)) (g := Λ) (x := q₀.2) (hΛd _)
        (mdifferentiableAt_const.prodMk mdifferentiableAt_id) v
      rw [mfderiv_prod_right] at h
      exact h
    refine ⟨show TangentSpace (𝓘(ℝ, ℝ).prod I) q₀ from ((a, show E from v) : ℝ × E), ?_⟩
    rw [hdΘ q₀]
    refine Prod.ext rfl ?_
    have hsplit : (show TangentSpace (𝓘(ℝ, ℝ).prod I) q₀ from ((a, show E from v) : ℝ × E)) =
        (show TangentSpace (𝓘(ℝ, ℝ).prod I) q₀ from ((a, 0) : ℝ × E)) +
          (show TangentSpace (𝓘(ℝ, ℝ).prod I) q₀ from ((0, show E from v) : ℝ × E)) := by
      refine Prod.ext ?_ ?_
      · change a = a + 0
        rw [add_zero]
      · change (show E from v) = 0 + (show E from v)
        rw [zero_add]
    change mfderiv (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, G'') Λ q₀ _ = g
    rw [hsplit, map_add, ← hslice, hv, ← hd₀]
    exact add_sub_cancel d₀ g
  obtain ⟨U, hU, Y, hY, hlift, -⟩ := exists_local_derivativeLift_of_surjective_Cn hmn Θ hΘ
    (fun y : ℝ × G'' =>
      ((((1 : ℝ), (0 : G'')) : ℝ × G'') : TangentSpace (𝓘(ℝ, ℝ).prod 𝓘(ℝ, G'')) y))
    (by
      have hone : ContMDiff 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ).tangent n
          (fun x : ℝ => (⟨x, ((1 : ℝ) : TangentSpace 𝓘(ℝ, ℝ) x)⟩ : TangentBundle 𝓘(ℝ, ℝ) ℝ)) := by
        intro x₀
        exact (contMDiffAt_vectorSpace_iff_contDiffAt
          (V := fun x : ℝ => ((1 : ℝ) : TangentSpace 𝓘(ℝ, ℝ) x))).2 contDiffAt_const
      have hzero : ContMDiff 𝓘(ℝ, G'') 𝓘(ℝ, G'').tangent n
          (fun y : G'' => (⟨y, ((0 : G'') : TangentSpace 𝓘(ℝ, G'') y)⟩ :
            TangentBundle 𝓘(ℝ, G'') G'')) := by
        intro y₀
        exact (contMDiffAt_vectorSpace_iff_contDiffAt
          (V := fun y : G'' => ((0 : G'') : TangentSpace 𝓘(ℝ, G'') y))).2 contDiffAt_const
      exact (contMDiff_equivTangentBundleProd_symm (I := 𝓘(ℝ, ℝ)) (M := ℝ)
        (I' := 𝓘(ℝ, G'')) (M' := G'')).comp
        ((hone.comp contMDiff_fst).prodMk (hzero.comp contMDiff_snd)))
    q₀ hsurjΘ
  refine ⟨U, hU, Y, hY, fun q hq => ?_⟩
  have h := hlift q hq
  rw [hdΘ] at h
  exact ⟨congrArg Prod.fst h, congrArg Prod.snd h⟩

omit [FiniteDimensional ℝ E] [IsManifold I ∞ M] in
/-- The derivative of a map into a product of vector spaces, componentwise. -/
theorem mfderiv_prodMk_space_apply {G₁ G₂ : Type*} [NormedAddCommGroup G₁] [NormedSpace ℝ G₁]
    [NormedAddCommGroup G₂] [NormedSpace ℝ G₂] {Λ₁ : ℝ × M → G₁} {Λ₂ : ℝ × M → G₂} {q : ℝ × M}
    (h₁ : MDifferentiableAt (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, G₁) Λ₁ q)
    (h₂ : MDifferentiableAt (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, G₂) Λ₂ q)
    (w : TangentSpace (𝓘(ℝ, ℝ).prod I) q) :
    mfderiv (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, G₁ × G₂) (fun p => (Λ₁ p, Λ₂ p)) q w =
      (mfderiv (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, G₁) Λ₁ q w, mfderiv (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, G₂) Λ₂ q w) := by
  have hd := (h₁.prodMk_space h₂)
  have e₁ : Λ₁ = (ContinuousLinearMap.fst ℝ G₁ G₂) ∘ (fun p => (Λ₁ p, Λ₂ p)) := rfl
  have e₂ : Λ₂ = (ContinuousLinearMap.snd ℝ G₁ G₂) ∘ (fun p => (Λ₁ p, Λ₂ p)) := rfl
  have k₁ : mfderiv (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, G₁) Λ₁ q w =
      (ContinuousLinearMap.fst ℝ G₁ G₂)
        (mfderiv (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, G₁ × G₂) (fun p => (Λ₁ p, Λ₂ p)) q w) := by
    conv_lhs => rw [e₁]
    rw [mfderiv_comp_apply _ (ContinuousLinearMap.fst ℝ G₁ G₂).mdifferentiableAt hd,
      ContinuousLinearMap.mfderiv_eq]
    rfl
  have k₂ : mfderiv (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, G₂) Λ₂ q w =
      (ContinuousLinearMap.snd ℝ G₁ G₂)
        (mfderiv (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, G₁ × G₂) (fun p => (Λ₁ p, Λ₂ p)) q w) := by
    conv_lhs => rw [e₂]
    rw [mfderiv_comp_apply _ (ContinuousLinearMap.snd ℝ G₁ G₂).mdifferentiableAt hd,
      ContinuousLinearMap.mfderiv_eq]
    rfl
  rw [k₁, k₂]
  rfl

section Global

variable [T2Space M] [SigmaCompactSpace M]
  {G : Type*} [NormedAddCommGroup G] [NormedSpace ℝ G] [FiniteDimensional ℝ G]

/-- **Kernel A (statement S2 of W5-FLOW): the time-lifting field.** Let `Ψ : ℝ × M → G` and
`B : ℝ × M → ℝ` be `C^m`, with `n + 1 ≤ m`. Suppose the slice `Ψ (t, ·)` is a submersion at every
point of `W_t = {Ψ (t, ·) = 0, B (t, ·) ≥ 0}`, the slice `(Ψ, B) (t, ·)` is a submersion at every
point of `∂W_t = {Ψ (t, ·) = 0, B (t, ·) = 0}`, and every `W_t` lies in the compact set `S ⊆ N`,
`N` open. Then there are a jointly `C^n` time-dependent vector field `V`, a compact `K ⊆ N` off
which `V` vanishes, and open sets `O ⊇ {Ψ = 0, B ≥ 0}`, `O' ⊇ {Ψ = 0, B = 0}` in `ℝ × M` with
`dΨ (1, V) = 0` on `O` and `dB (1, V) = 0` on `O'`. -/
theorem exists_timeLift_field_Cn {n : ℕ∞} {m : WithTop ℕ∞}
    (hmn : (n : WithTop ℕ∞) + 1 ≤ m)
    {Ψ : ℝ × M → G} (hΨ : ContMDiff (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, G) m Ψ)
    {B : ℝ × M → ℝ} (hB : ContMDiff (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) m B)
    (htrans : ∀ q : ℝ × M, Ψ q = 0 → 0 ≤ B q →
      Surjective (mfderiv I 𝓘(ℝ, G) (fun y => Ψ (q.1, y)) q.2))
    (htransb : ∀ q : ℝ × M, Ψ q = 0 → B q = 0 →
      Surjective (mfderiv I 𝓘(ℝ, G × ℝ) (fun y => (Ψ (q.1, y), B (q.1, y))) q.2))
    {S : Set M} (hS : IsCompact S) (hWS : ∀ q : ℝ × M, Ψ q = 0 → 0 ≤ B q → q.2 ∈ S)
    {N : Set M} (hN : IsOpen N) (hSN : S ⊆ N) :
    ∃ (V : ℝ → (x : M) → TangentSpace I x) (K : Set M) (O O' : Set (ℝ × M)),
      ContMDiff (𝓘(ℝ, ℝ).prod I) I.tangent n
        (fun q : ℝ × M => (⟨q.2, V q.1 q.2⟩ : TangentBundle I M)) ∧
      IsCompact K ∧ K ⊆ N ∧ (∀ t x, x ∉ K → V t x = 0) ∧
      IsOpen O ∧ {q | Ψ q = 0 ∧ 0 ≤ B q} ⊆ O ∧
      IsOpen O' ∧ {q | Ψ q = 0 ∧ B q = 0} ⊆ O' ∧
      (∀ q ∈ O, mfderiv (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, G) Ψ q ((1 : ℝ), V q.1 q.2) = 0) ∧
      ∀ q ∈ O', mfderiv (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) B q ((1 : ℝ), V q.1 q.2) = 0 := by
  classical
  have hm0 : m ≠ 0 := by
    intro h
    rw [h] at hmn
    exact absurd hmn (by simp)
  have hΨd : MDifferentiable (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, G) Ψ := hΨ.mdifferentiable hm0
  have hBd : MDifferentiable (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) B := hB.mdifferentiable hm0
  have : LocallyCompactSpace H := I.locallyCompactSpace
  have : LocallyCompactSpace M := ChartedSpace.locallyCompactSpace H M
  -- the sets of points with a local time lift preserving `Ψ`, resp. `Ψ` and `B`
  set Oφ : Set (ℝ × M) := {q | ∃ U ∈ 𝓝 q, ∃ Y : (p : ℝ × M) → TangentSpace (𝓘(ℝ, ℝ).prod I) p,
      ContMDiffOn (𝓘(ℝ, ℝ).prod I) (𝓘(ℝ, ℝ).prod I).tangent n
        (fun p ↦ (⟨p, Y p⟩ : TangentBundle (𝓘(ℝ, ℝ).prod I) (ℝ × M))) U ∧
      ∀ p ∈ U, (Y p).1 = 1 ∧ mfderiv (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, G) Ψ p (Y p) = 0} with hOφ
  set Oβ : Set (ℝ × M) := {q | ∃ U ∈ 𝓝 q, ∃ Y : (p : ℝ × M) → TangentSpace (𝓘(ℝ, ℝ).prod I) p,
      ContMDiffOn (𝓘(ℝ, ℝ).prod I) (𝓘(ℝ, ℝ).prod I).tangent n
        (fun p ↦ (⟨p, Y p⟩ : TangentBundle (𝓘(ℝ, ℝ).prod I) (ℝ × M))) U ∧
      ∀ p ∈ U, (Y p).1 = 1 ∧ mfderiv (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, G) Ψ p (Y p) = 0 ∧
        mfderiv (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) B p (Y p) = 0} with hOβ
  have hOφo : IsOpen Oφ := by
    refine isOpen_iff_mem_nhds.2 fun q hq => ?_
    obtain ⟨U, hU, Y, hY, hYU⟩ := hq
    exact mem_of_superset (interior_mem_nhds.2 hU) fun q' hq' =>
      ⟨U, mem_interior_iff_mem_nhds.1 hq', Y, hY, hYU⟩
  have hOβo : IsOpen Oβ := by
    refine isOpen_iff_mem_nhds.2 fun q hq => ?_
    obtain ⟨U, hU, Y, hY, hYU⟩ := hq
    exact mem_of_superset (interior_mem_nhds.2 hU) fun q' hq' =>
      ⟨U, mem_interior_iff_mem_nhds.1 hq', Y, hY, hYU⟩
  have hWφ : {q | Ψ q = 0 ∧ 0 ≤ B q} ⊆ Oφ := by
    rintro q ⟨h1, h2⟩
    exact exists_local_timeLift_Cn hmn hΨ (htrans q h1 h2)
  have hbβ : {q | Ψ q = 0 ∧ B q = 0} ⊆ Oβ := by
    rintro q ⟨h1, h2⟩
    obtain ⟨U, hU, Y, hY, hYU⟩ := exists_local_timeLift_Cn hmn (hΨ.prodMk_space hB)
      (htransb q h1 h2)
    refine ⟨U, hU, Y, hY, fun p hp => ?_⟩
    obtain ⟨hp1, hp2⟩ := hYU p hp
    rw [mfderiv_prodMk_space_apply (hΨd p) (hBd p)] at hp2
    exact ⟨hp1, congrArg Prod.fst hp2, congrArg Prod.snd hp2⟩
  have hWc : IsClosed {q : ℝ × M | Ψ q = 0 ∧ 0 ≤ B q} :=
    (isClosed_eq hΨ.continuous continuous_const).inter
      (isClosed_le continuous_const hB.continuous)
  have hbc : IsClosed {q : ℝ × M | Ψ q = 0 ∧ B q = 0} :=
    (isClosed_eq hΨ.continuous continuous_const).inter
      (isClosed_eq hB.continuous continuous_const)
  obtain ⟨O₀, hO₀o, hWO₀, hO₀C⟩ := normal_exists_closure_subset hWc hOφo hWφ
  obtain ⟨O₀', hO₀'o, hbO₀', hO₀'C⟩ := normal_exists_closure_subset hbc hOβo hbβ
  -- the affine constraint
  set T : (q : ℝ × M) → Set (TangentSpace (𝓘(ℝ, ℝ).prod I) q) := fun q =>
    {w | w.1 = 1 ∧ (q ∈ closure O₀ → mfderiv (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, G) Ψ q w = 0) ∧
      (q ∈ closure O₀' → mfderiv (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) B q w = 0)} with hT
  have hTconv : ∀ q, Convex ℝ (T q) := by
    intro q w₁ hw₁ w₂ hw₂ a b ha hb hab
    refine ⟨?_, fun hq => ?_, fun hq => ?_⟩
    · change a * w₁.1 + b * w₂.1 = 1
      rw [hw₁.1, hw₂.1, mul_one, mul_one, hab]
    · rw [map_add, map_smul, map_smul, hw₁.2.1 hq, hw₂.2.1 hq, smul_zero, smul_zero, add_zero]
    · rw [map_add, map_smul, map_smul, hw₁.2.2 hq, hw₂.2.2 hq, smul_zero, smul_zero, add_zero]
  have hloc : ∀ q₀ : ℝ × M, ∃ U ∈ 𝓝 q₀,
      ∃ Y : (p : ℝ × M) → TangentSpace (𝓘(ℝ, ℝ).prod I) p,
        ContMDiffOn (𝓘(ℝ, ℝ).prod I) (𝓘(ℝ, ℝ).prod I).tangent n
          (fun p ↦ (⟨p, Y p⟩ : TangentBundle (𝓘(ℝ, ℝ).prod I) (ℝ × M))) U ∧
        ∀ p ∈ U, Y p ∈ T p := by
    intro q₀
    by_cases h' : q₀ ∈ closure O₀'
    · obtain ⟨U, hU, Y, hY, hYU⟩ := hO₀'C h'
      exact ⟨U, hU, Y, hY, fun p hp =>
        ⟨(hYU p hp).1, fun _ => (hYU p hp).2.1, fun _ => (hYU p hp).2.2⟩⟩
    by_cases h : q₀ ∈ closure O₀
    · obtain ⟨U, hU, Y, hY, hYU⟩ := hO₀C h
      refine ⟨U ∩ (closure O₀')ᶜ, inter_mem hU (isClosed_closure.isOpen_compl.mem_nhds h'),
        Y, hY.mono inter_subset_left, fun p hp => ⟨(hYU p hp.1).1, fun _ => (hYU p hp.1).2,
          fun hp' => absurd hp' hp.2⟩⟩
    · have hzero : ContMDiff (𝓘(ℝ, ℝ).prod I) I.tangent n
          (fun q : ℝ × M => (⟨q.2, (0 : TangentSpace I q.2)⟩ : TangentBundle I M)) :=
        (contMDiff_zeroSection ℝ (TangentSpace I : M → Type _)).comp contMDiff_snd
      refine ⟨(closure O₀ ∪ closure O₀')ᶜ,
        (isClosed_closure.union isClosed_closure).isOpen_compl.mem_nhds
          (by simp only [mem_compl_iff, mem_union, not_or]; exact ⟨h, h'⟩),
        autonomizedFlowVF (fun (_ : ℝ) (x : M) => (0 : TangentSpace I x)),
        (contMDiff_autonomizedFlowVF_section _ hzero).contMDiffOn, fun p hp => ?_⟩
      simp only [mem_compl_iff, mem_union, not_or] at hp
      exact ⟨rfl, fun hp' => absurd hp' hp.1, fun hp' => absurd hp' hp.2⟩
  obtain ⟨Y, hYT⟩ := exists_contMDiffSection_forall_mem_convex_of_local
    (I := 𝓘(ℝ, ℝ).prod I) (n := n) (TangentSpace (𝓘(ℝ, ℝ).prod I)) T hTconv hloc
  -- the spatial cutoff
  obtain ⟨K, hK, hSK, hKN⟩ := exists_compact_between hS hN hSN
  obtain ⟨χ, hχ1, hχ0, -⟩ := exists_contMDiffMap_one_nhds_of_subset_interior I (n := n)
    hS.isClosed hSK
  obtain ⟨U₁, hU₁o, hSU₁, hU₁χ⟩ := mem_nhdsSet_iff_exists.1 hχ1
  set V : ℝ → (x : M) → TangentSpace I x := fun t x => χ x • (Y (t, x)).2 with hVdef
  have hYs : ContMDiff (𝓘(ℝ, ℝ).prod I) (𝓘(ℝ, ℝ).prod I).tangent n
      (fun q ↦ (⟨q, Y q⟩ : TangentBundle (𝓘(ℝ, ℝ).prod I) (ℝ × M))) := Y.contMDiff
  have hχP : ContMDiff (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) n (fun q : ℝ × M => χ q.2) :=
    χ.contMDiff.comp contMDiff_snd
  have hZs : ContMDiff (𝓘(ℝ, ℝ).prod I) (𝓘(ℝ, ℝ).prod I).tangent n
      (fun q ↦ (⟨q, χ q.2 • Y q⟩ : TangentBundle (𝓘(ℝ, ℝ).prod I) (ℝ × M))) :=
    hχP.smul_section hYs
  have hV : ContMDiff (𝓘(ℝ, ℝ).prod I) I.tangent n
      (fun q : ℝ × M => (⟨q.2, V q.1 q.2⟩ : TangentBundle I M)) :=
    contMDiff_snd.comp ((contMDiff_equivTangentBundleProd (I := 𝓘(ℝ, ℝ)) (M := ℝ) (I' := I)
      (M' := M)).comp hZs)
  have hVY : ∀ q : ℝ × M, q.2 ∈ U₁ →
      ((((1 : ℝ), V q.1 q.2) : ℝ × E) : TangentSpace (𝓘(ℝ, ℝ).prod I) q) = Y q := by
    intro q hq
    have h1 : χ q.2 = 1 := hU₁χ hq
    refine Prod.ext (hYT q).1.symm ?_
    change χ q.2 • (Y q).2 = (Y q).2
    rw [h1, one_smul]
  refine ⟨V, K, O₀ ∩ Prod.snd ⁻¹' U₁, O₀' ∩ Prod.snd ⁻¹' U₁, hV, hK, hKN, ?_,
    hO₀o.inter (hU₁o.preimage continuous_snd), ?_,
    hO₀'o.inter (hU₁o.preimage continuous_snd), ?_, ?_, ?_⟩
  · intro t x hx
    change χ x • (Y (t, x)).2 = 0
    rw [hχ0 x hx, zero_smul]
  · intro q hq
    exact ⟨hWO₀ hq, hSU₁ (hWS q hq.1 hq.2)⟩
  · intro q hq
    exact ⟨hbO₀' hq, hSU₁ (hWS q hq.1 hq.2.ge)⟩
  · intro q hq
    rw [hVY q hq.2]
    exact (hYT q).2.1 (subset_closure hq.1)
  · intro q hq
    rw [hVY q hq.2]
    exact (hYT q).2.2 (subset_closure hq.1)

end Global

end DifferentialGeometry.Analysis.ODE
