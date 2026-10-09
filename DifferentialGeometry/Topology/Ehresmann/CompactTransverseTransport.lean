import DifferentialGeometry.Topology.Ehresmann.FiberType
import Mathlib.Analysis.SpecialFunctions.SmoothTransition

/-!
# Compact transverse transport of level sets (FC34, boundaryless level form)

A smooth family `h τ : Y → F`, `τ ∈ [0,1]`, of maps that are submersions along the level `a`, whose whole
trace `{(y, τ) : h τ y = a}` lies in one compact set `Q × [0,1]`, has diffeomorphic end levels
`h 0 ⁻¹ a ≅ h 1 ⁻¹ a` (with their regular-level-set manifold structures).

Proof: reparametrize time by `Real.smoothTransition`; the total level set `S ⊆ Y × ℝ` is a regular fibre,
the time coordinate `S → ℝ` is a proper submersion, and the tree's Ehresmann theorem
`nonempty_diffeomorph_regularFiber_of_mem_connectedComponent` identifies its fibres over `0` and `1`.
-/

set_option autoImplicit false

noncomputable section
open Set Function
open scoped ContDiff Manifold Topology
open DifferentialGeometry.Topology.Manifold

namespace DifferentialGeometry.Topology.Ehresmann

variable {E F H Y : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [TopologicalSpace Y] [ChartedSpace H Y]

/-- The time-`τ` slice of a smooth family is smooth. -/
theorem contMDiff_familySlice {h : Y × ℝ → F}
    (hh : ContMDiff (I.prod 𝓘(ℝ)) 𝓘(ℝ, F) ∞ h) (τ : ℝ) :
    ContMDiff I 𝓘(ℝ, F) ∞ (fun y => h (y, τ)) :=
  hh.comp (contMDiff_id.prodMk contMDiff_const)

/-- A map on `Y × ℝ` whose spatial slice has surjective differential has surjective differential. -/
theorem surjective_mfderiv_of_surjective_slice {G : Y × ℝ → F}
    (hG : ContMDiff (I.prod 𝓘(ℝ)) 𝓘(ℝ, F) ∞ G) (x : Y × ℝ)
    (hslice : Surjective (mfderiv I 𝓘(ℝ, F) (fun z => G (z, x.2)) x.1)) :
    Surjective (mfderiv (I.prod 𝓘(ℝ)) 𝓘(ℝ, F) G x) := by
  have hι : MDifferentiableAt I (I.prod 𝓘(ℝ)) (fun z : Y => (z, x.2)) x.1 :=
    ((contMDiff_id.prodMk contMDiff_const : ContMDiff I (I.prod 𝓘(ℝ)) ∞
      (fun z : Y => (z, x.2))) x.1).mdifferentiableAt (by simp)
  have hGd : MDifferentiableAt (I.prod 𝓘(ℝ)) 𝓘(ℝ, F) G (x.1, x.2) :=
    (hG _).mdifferentiableAt (by simp)
  have hcomp := mfderiv_comp x.1 hGd hι
  intro v
  obtain ⟨w, hw⟩ := hslice v
  refine ⟨mfderiv I (I.prod 𝓘(ℝ)) (fun z : Y => (z, x.2)) x.1 w, ?_⟩
  have h1 : mfderiv I 𝓘(ℝ, F) (G ∘ fun z : Y => (z, x.2)) x.1 w = v := hw
  rw [hcomp] at h1
  exact h1

variable [IsManifold I ∞ Y] [FiniteDimensional ℝ E] [FiniteDimensional ℝ F] [I.Boundaryless]

/-- On the regular level set of `G : Y × ℝ → F` whose spatial slices are submersions along the level,
the time coordinate has surjective differential. -/
theorem surjective_mfderiv_levelSet_time {G : Y × ℝ → F}
    (hG : ContMDiff (I.prod 𝓘(ℝ)) 𝓘(ℝ, F) ∞ G) (a : F)
    (hslice : ∀ x, G x = a → Surjective (mfderiv I 𝓘(ℝ, F) (fun z => G (z, x.2)) x.1)) :
    let _ := regularFiberChartedSpace G a hG
      (fun x hx => surjective_mfderiv_of_surjective_slice hG x (hslice x hx))
    ∀ s : {x : Y × ℝ // G x = a},
      Surjective (mfderiv 𝓘(ℝ, Fin (Module.finrank ℝ (E × ℝ) - Module.finrank ℝ F) → ℝ) 𝓘(ℝ)
        (fun s : {x : Y × ℝ // G x = a} => s.1.2) s) := by
  dsimp only
  have hGreg : ∀ x, G x = a → Surjective (mfderiv (I.prod 𝓘(ℝ)) 𝓘(ℝ, F) G x) :=
    fun x hx => surjective_mfderiv_of_surjective_slice hG x (hslice x hx)
  let _ := regularFiberChartedSpace G a hG hGreg
  have _ : IsManifold 𝓘(ℝ, Fin (Module.finrank ℝ (E × ℝ) - Module.finrank ℝ F) → ℝ) ∞
      {x : Y × ℝ // G x = a} := regularFiberIsManifold G a hG hGreg
  intro s
  let K := Fin (Module.finrank ℝ (E × ℝ) - Module.finrank ℝ F) → ℝ
  set x : Y × ℝ := s.1 with hxdef
  have hval : MDifferentiableAt 𝓘(ℝ, K) (I.prod 𝓘(ℝ))
      (Subtype.val : {x : Y × ℝ // G x = a} → Y × ℝ) s :=
    ((contMDiff_regularFiberInclusion G a hG hGreg) s).mdifferentiableAt (by simp)
  have hGd : MDifferentiableAt (I.prod 𝓘(ℝ)) 𝓘(ℝ, F) G x := (hG x).mdifferentiableAt (by simp)
  let T : K →L[ℝ] E × ℝ :=
    mfderiv 𝓘(ℝ, K) (I.prod 𝓘(ℝ)) (Subtype.val : {x : Y × ℝ // G x = a} → Y × ℝ) s
  let D : E × ℝ →L[ℝ] F := mfderiv (I.prod 𝓘(ℝ)) 𝓘(ℝ, F) G x
  -- the inclusion differential lands in the kernel of `D`
  have hDT : D.comp T = 0 := by
    have hc := mfderiv_comp s hGd hval
    have hconst : (G ∘ (Subtype.val : {x : Y × ℝ // G x = a} → Y × ℝ)) = fun _ => a :=
      funext fun t => t.2
    rw [hconst, mfderiv_const] at hc
    exact hc.symm
  have hle : LinearMap.range (T : K →ₗ[ℝ] E × ℝ) ≤ LinearMap.ker (D : E × ℝ →ₗ[ℝ] F) := by
    rintro _ ⟨u, rfl⟩
    change D (T u) = 0
    have := congrArg (fun L : K →L[ℝ] F => L u) hDT
    simpa using this
  have hinj : Injective T := mfderiv_regularFiberInclusion_injective G a hG hGreg s
  have hsurjD : Surjective D := hGreg x s.2
  have hrange : LinearMap.range (T : K →ₗ[ℝ] E × ℝ) = LinearMap.ker (D : E × ℝ →ₗ[ℝ] F) := by
    apply Submodule.eq_of_le_of_finrank_eq hle
    rw [LinearMap.finrank_range_of_inj hinj]
    have hrk := LinearMap.finrank_range_add_finrank_ker (D : E × ℝ →ₗ[ℝ] F)
    rw [LinearMap.range_eq_top.mpr hsurjD, finrank_top] at hrk
    change Module.finrank ℝ K = _
    rw [Module.finrank_fin_fun]
    omega
  -- a kernel vector with time component one
  let L : E →L[ℝ] E × ℝ := mfderiv I (I.prod 𝓘(ℝ)) (fun z : Y => (z, x.2)) x.1
  have hι : MDifferentiableAt I (I.prod 𝓘(ℝ)) (fun z : Y => (z, x.2)) x.1 :=
    ((contMDiff_id.prodMk contMDiff_const : ContMDiff I (I.prod 𝓘(ℝ)) ∞
      (fun z : Y => (z, x.2))) x.1).mdifferentiableAt (by simp)
  have hDL : Surjective (D.comp L) := by
    have hc := mfderiv_comp x.1 hGd hι
    intro v
    obtain ⟨w, hw⟩ := hslice x s.2 v
    refine ⟨w, ?_⟩
    have h1 : mfderiv I 𝓘(ℝ, F) (G ∘ fun z : Y => (z, x.2)) x.1 w = v := hw
    rw [hc] at h1
    exact h1
  have hsnd : MDifferentiableAt (I.prod 𝓘(ℝ)) 𝓘(ℝ) (Prod.snd : Y × ℝ → ℝ) x :=
    mdifferentiableAt_snd
  have hPL : (ContinuousLinearMap.snd ℝ E ℝ).comp L = 0 := by
    have hc := mfderiv_comp x.1 hsnd hι
    have hconst : (Prod.snd ∘ fun z : Y => (z, x.2)) = fun _ => x.2 := rfl
    rw [hconst, mfderiv_const, mfderiv_snd] at hc
    exact hc.symm
  obtain ⟨w, hw⟩ := hDL (D ((0 : E), (1 : ℝ)))
  let V : E × ℝ := ((0 : E), (1 : ℝ)) - L w
  have hV : V ∈ LinearMap.ker (D : E × ℝ →ₗ[ℝ] F) := by
    change D V = 0
    change D (((0 : E), (1 : ℝ)) - L w) = 0
    rw [map_sub]
    change D ((0 : E), (1 : ℝ)) - (D.comp L) w = 0
    rw [hw, sub_self]
  have hVsnd : V.2 = 1 := by
    have := congrArg (fun P : E →L[ℝ] ℝ => P w) hPL
    change (L w).2 = 0 at this
    change (1 : ℝ) - (L w).2 = 1
    rw [this, sub_zero]
  rw [← hrange] at hV
  obtain ⟨u, hu⟩ := hV
  have hΦ := mfderiv_comp s hsnd hval
  intro r
  refine ⟨(show ℝ from r) • u, ?_⟩
  have h1 : mfderiv 𝓘(ℝ, K) 𝓘(ℝ) (Prod.snd ∘ (Subtype.val : {x : Y × ℝ // G x = a} → Y × ℝ)) s
      ((show ℝ from r) • u) = r := by
    rw [hΦ, mfderiv_snd]
    change ((T ((show ℝ from r) • u)) : E × ℝ).2 = r
    rw [map_smul]
    change (show ℝ from r) * (T u).2 = r
    have hTu : T u = V := hu
    rw [hTu, hVsnd, mul_one]
  exact h1

variable [T2Space Y] [SigmaCompactSpace Y]

/-- **FC34a.** Compact transverse transport of a level set: if the slices of a smooth family are submersions
along the level `a` for every `τ ∈ [0,1]`, and the whole trace lies in one compact set, then the end level
sets are diffeomorphic. -/
theorem nonempty_diffeomorph_levelSet_of_compact_transport
    (h : Y × ℝ → F) (hh : ContMDiff (I.prod 𝓘(ℝ)) 𝓘(ℝ, F) ∞ h) (a : F)
    (hreg : ∀ τ ∈ Icc (0 : ℝ) 1, ∀ y, h (y, τ) = a →
      Surjective (mfderiv I 𝓘(ℝ, F) (fun z => h (z, τ)) y))
    {Q : Set Y} (hQ : IsCompact Q)
    (hloc : ∀ τ ∈ Icc (0 : ℝ) 1, ∀ y, h (y, τ) = a → y ∈ Q) :
    let _ := regularFiberChartedSpace (fun y => h (y, 0)) a (contMDiff_familySlice hh 0)
      (hreg 0 (left_mem_Icc.mpr zero_le_one))
    let _ := regularFiberChartedSpace (fun y => h (y, 1)) a (contMDiff_familySlice hh 1)
      (hreg 1 (right_mem_Icc.mpr zero_le_one))
    Nonempty ({y : Y // h (y, 0) = a} ≃ₘ⟮𝓘(ℝ, Fin (Module.finrank ℝ E - Module.finrank ℝ F) → ℝ),
      𝓘(ℝ, Fin (Module.finrank ℝ E - Module.finrank ℝ F) → ℝ)⟯ {y : Y // h (y, 1) = a}) := by
  dsimp only
  let σ : ℝ → ℝ := Real.smoothTransition
  have hσ : ContMDiff 𝓘(ℝ) 𝓘(ℝ) ∞ σ := Real.smoothTransition.contDiff.contMDiff
  have hσI : ∀ t, σ t ∈ Icc (0 : ℝ) 1 :=
    fun t => ⟨Real.smoothTransition.nonneg t, Real.smoothTransition.le_one t⟩
  let G : Y × ℝ → F := fun x => h (x.1, σ x.2)
  have hG : ContMDiff (I.prod 𝓘(ℝ)) 𝓘(ℝ, F) ∞ G :=
    hh.comp (contMDiff_fst.prodMk (hσ.comp contMDiff_snd))
  have hslice : ∀ x, G x = a → Surjective (mfderiv I 𝓘(ℝ, F) (fun z => G (z, x.2)) x.1) :=
    fun x hx => hreg (σ x.2) (hσI x.2) x.1 hx
  have hGreg : ∀ x, G x = a → Surjective (mfderiv (I.prod 𝓘(ℝ)) 𝓘(ℝ, F) G x) :=
    fun x hx => surjective_mfderiv_of_surjective_slice hG x (hslice x hx)
  let S := {x : Y × ℝ // G x = a}
  let _ : ChartedSpace (Fin (Module.finrank ℝ (E × ℝ) - Module.finrank ℝ F) → ℝ) S :=
    regularFiberChartedSpace G a hG hGreg
  have _ : IsManifold 𝓘(ℝ, Fin (Module.finrank ℝ (E × ℝ) - Module.finrank ℝ F) → ℝ) ∞ S :=
    regularFiberIsManifold G a hG hGreg
  have hSclosed : IsClosed {x : Y × ℝ | G x = a} := isClosed_eq hG.continuous continuous_const
  have _ : SigmaCompactSpace S := hSclosed.sigmaCompactSpace
  let Φ : S → ℝ := fun s => s.1.2
  have hΦ : ContMDiff 𝓘(ℝ, Fin (Module.finrank ℝ (E × ℝ) - Module.finrank ℝ F) → ℝ) 𝓘(ℝ) ∞ Φ :=
    contMDiff_snd.comp (contMDiff_regularFiberInclusion G a hG hGreg)
  have hΦreg := surjective_mfderiv_levelSet_time hG a hslice
  have hproper : IsProperMap Φ := by
    rw [isProperMap_iff_isCompact_preimage]
    refine ⟨hΦ.continuous, fun K hK => ?_⟩
    have heq : Φ ⁻¹' K = (Subtype.val : S → Y × ℝ) ⁻¹' (Q ×ˢ K) := by
      ext s
      simp only [mem_preimage, mem_prod]
      constructor
      · intro hs
        exact ⟨hloc (σ s.1.2) (hσI s.1.2) s.1.1 s.2, hs⟩
      · exact fun hs => hs.2
    rw [heq]
    exact hSclosed.isClosedEmbedding_subtypeVal.isCompact_preimage (hQ.prod hK)
  have hconn : (1 : ℝ) ∈ connectedComponent (0 : ℝ) := by
    rw [PreconnectedSpace.connectedComponent_eq_univ]
    trivial
  have hmid := nonempty_diffeomorph_regularFiber_of_mem_connectedComponent Φ hΦ hΦreg hproper
    0 1 hconn
  dsimp only at hmid
  let _ (w : ℝ) := regularFiberChartedSpace Φ w hΦ (fun s _ => hΦreg s)
  have _ (w : ℝ) : IsManifold 𝓘(ℝ, Fin (Module.finrank ℝ
      (Fin (Module.finrank ℝ (E × ℝ) - Module.finrank ℝ F) → ℝ) - Module.finrank ℝ ℝ) → ℝ) ∞
      {s : S // Φ s = w} := regularFiberIsManifold Φ w hΦ (fun s _ => hΦreg s)
  obtain ⟨d⟩ := hmid
  -- identify a slice level set with the corresponding fibre of the time coordinate
  have hident : ∀ (c : ℝ) (hc : c ∈ Icc (0 : ℝ) 1), σ c = c →
      let _ := regularFiberChartedSpace (fun y => h (y, c)) a (contMDiff_familySlice hh c) (hreg c hc)
      Nonempty ({y : Y // h (y, c) = a} ≃ₘ⟮𝓘(ℝ, Fin (Module.finrank ℝ E - Module.finrank ℝ F) → ℝ),
        𝓘(ℝ, Fin (Module.finrank ℝ (Fin (Module.finrank ℝ (E × ℝ) - Module.finrank ℝ F) → ℝ) -
          Module.finrank ℝ ℝ) → ℝ)⟯ {s : S // Φ s = c}) := by
    intro c hc hσc
    dsimp only
    let _ := regularFiberChartedSpace (fun y => h (y, c)) a (contMDiff_familySlice hh c) (hreg c hc)
    have hfwd : ∀ y : {y : Y // h (y, c) = a}, G (y.1, c) = a := by
      intro y
      change h (y.1, σ c) = a
      rw [hσc]
      exact y.2
    have hinv : ∀ t : {s : S // Φ s = c}, h (t.1.1.1, c) = a := by
      intro t
      have h1 : h (t.1.1.1, σ t.1.1.2) = a := t.1.2
      have h2 : t.1.1.2 = c := t.2
      rw [h2, hσc] at h1
      exact h1
    let fwd : {y : Y // h (y, c) = a} → {s : S // Φ s = c} := fun y => ⟨⟨(y.1, c), hfwd y⟩, rfl⟩
    let inv : {s : S // Φ s = c} → {y : Y // h (y, c) = a} := fun t => ⟨t.1.1.1, hinv t⟩
    have hfwd_smooth : ContMDiff 𝓘(ℝ, Fin (Module.finrank ℝ E - Module.finrank ℝ F) → ℝ)
        𝓘(ℝ, Fin (Module.finrank ℝ (Fin (Module.finrank ℝ (E × ℝ) - Module.finrank ℝ F) → ℝ) -
          Module.finrank ℝ ℝ) → ℝ) ∞ fwd := by
      apply (contMDiff_regularFiber_iff Φ c hΦ (fun s _ => hΦreg s) fwd).mpr
      apply (contMDiff_regularFiber_iff G a hG hGreg _).mpr
      exact (contMDiff_regularFiberInclusion (fun y => h (y, c)) a (contMDiff_familySlice hh c)
        (hreg c hc)).prodMk contMDiff_const
    have hinv_smooth : ContMDiff
        𝓘(ℝ, Fin (Module.finrank ℝ (Fin (Module.finrank ℝ (E × ℝ) - Module.finrank ℝ F) → ℝ) -
          Module.finrank ℝ ℝ) → ℝ)
        𝓘(ℝ, Fin (Module.finrank ℝ E - Module.finrank ℝ F) → ℝ) ∞ inv := by
      apply (contMDiff_regularFiber_iff (fun y => h (y, c)) a (contMDiff_familySlice hh c)
        (hreg c hc) inv).mpr
      exact contMDiff_fst.comp ((contMDiff_regularFiberInclusion G a hG hGreg).comp
        (contMDiff_regularFiberInclusion Φ c hΦ (fun s _ => hΦreg s)))
    exact ⟨{ toEquiv :=
              { toFun := fwd
                invFun := inv
                left_inv := fun y => rfl
                right_inv := fun t => by
                  apply Subtype.ext
                  apply Subtype.ext
                  exact Prod.ext rfl t.2.symm }
             contMDiff_toFun := hfwd_smooth
             contMDiff_invFun := hinv_smooth }⟩
  let _ := regularFiberChartedSpace (fun y => h (y, 0)) a (contMDiff_familySlice hh 0)
    (hreg 0 (left_mem_Icc.mpr zero_le_one))
  let _ := regularFiberChartedSpace (fun y => h (y, 1)) a (contMDiff_familySlice hh 1)
    (hreg 1 (right_mem_Icc.mpr zero_le_one))
  obtain ⟨e₀⟩ := hident 0 (left_mem_Icc.mpr zero_le_one) Real.smoothTransition.zero
  obtain ⟨e₁⟩ := hident 1 (right_mem_Icc.mpr zero_le_one) Real.smoothTransition.one
  exact ⟨(e₀.trans d).trans e₁.symm⟩

/-- Consumer (closed carrier form, the ZSP02 level-surface instance): on a compact manifold, a smooth family
whose slices are submersions along the level `a` has diffeomorphic end level sets. -/
theorem nonempty_diffeomorph_levelSet_of_compactSpace [CompactSpace Y]
    (h : Y × ℝ → F) (hh : ContMDiff (I.prod 𝓘(ℝ)) 𝓘(ℝ, F) ∞ h) (a : F)
    (hreg : ∀ τ ∈ Icc (0 : ℝ) 1, ∀ y, h (y, τ) = a →
      Surjective (mfderiv I 𝓘(ℝ, F) (fun z => h (z, τ)) y)) :
    let _ := regularFiberChartedSpace (fun y => h (y, 0)) a (contMDiff_familySlice hh 0)
      (hreg 0 (left_mem_Icc.mpr zero_le_one))
    let _ := regularFiberChartedSpace (fun y => h (y, 1)) a (contMDiff_familySlice hh 1)
      (hreg 1 (right_mem_Icc.mpr zero_le_one))
    Nonempty ({y : Y // h (y, 0) = a} ≃ₘ⟮𝓘(ℝ, Fin (Module.finrank ℝ E - Module.finrank ℝ F) → ℝ),
      𝓘(ℝ, Fin (Module.finrank ℝ E - Module.finrank ℝ F) → ℝ)⟯ {y : Y // h (y, 1) = a}) :=
  nonempty_diffeomorph_levelSet_of_compact_transport h hh a hreg isCompact_univ
    (fun _ _ _ _ => mem_univ _)

end DifferentialGeometry.Topology.Ehresmann
