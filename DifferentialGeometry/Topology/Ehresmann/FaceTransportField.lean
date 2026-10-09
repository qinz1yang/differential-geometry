import DifferentialGeometry.Topology.Ehresmann.FaceTransport

set_option autoImplicit false

noncomputable section

open Set Filter Function Manifold
open scoped ContDiff Manifold Topology

namespace DifferentialGeometry.Topology.Ehresmann

variable {E F H Y : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [TopologicalSpace Y] [ChartedSpace H Y] [IsManifold I ∞ Y]
  [T2Space Y] [SigmaCompactSpace Y]

/-- One compactly supported spatial field satisfies the total h and face equations together. -/
theorem exists_compactSupport_faceTransportField
    (h : Y × ℝ → F) (T : Y × ℝ → ℝ)
    (hh : ContMDiff (I.prod 𝓘(ℝ)) 𝓘(ℝ, F) ∞ h)
    (hT : ContMDiff (I.prod 𝓘(ℝ)) 𝓘(ℝ) ∞ T)
    {SA SB K : Set (Y × ℝ)} (hSA : IsCompact SA) (hSB : IsCompact SB)
    (hK : IsCompact K) (hSK : SA ∪ SB ⊆ interior K)
    (hRA : ∀ x ∈ SA,
      Surjective (mfderiv I 𝓘(ℝ, F) (fun z => h (z, x.2)) x.1))
    (hRB : ∀ x ∈ SB, Surjective (mfderiv I 𝓘(ℝ, F × ℝ)
      (fun z => (h (z, x.2), T (z, x.2))) x.1)) :
    ∃ X : ℝ → ∀ y : Y, TangentSpace I y,
      ContMDiff (𝓘(ℝ).prod I) I.tangent ∞
        (fun p : ℝ × Y => (⟨p.2, X p.1 p.2⟩ : TangentBundle I Y)) ∧
      (∀ τ y, y ∉ Prod.fst '' K → X τ y = 0) ∧
      (∀ x ∈ SA, mfderiv (I.prod 𝓘(ℝ)) 𝓘(ℝ, F) h x (X x.2 x.1, 1) = 0) ∧
      ∀ x ∈ SB,
        mfderiv (I.prod 𝓘(ℝ)) 𝓘(ℝ, F) h x (X x.2 x.1, 1) = 0 ∧
        mfderiv (I.prod 𝓘(ℝ)) 𝓘(ℝ) T x (X x.2 x.1, 1) = 0 := by
  classical
  let A : Bool → ∀ x : Y × ℝ, TangentSpace (I.prod 𝓘(ℝ)) x →L[ℝ] (F × ℝ) × ℝ :=
    fun i x => ((mfderiv (I.prod 𝓘(ℝ)) 𝓘(ℝ, F) h x).prod
      (if i then mfderiv (I.prod 𝓘(ℝ)) 𝓘(ℝ) T x else 0)).prod
      (ContinuousLinearMap.snd ℝ E ℝ)
  let b : Bool → Y × ℝ → (F × ℝ) × ℝ := fun _i _x => ((0, 0), 1)
  let stratum : Bool → Set (Y × ℝ) := fun i => if i then SB else SA
  have hlocal : ∀ x₀ : Y × ℝ, ∃ U ∈ 𝓝 x₀,
      ∃ W : ∀ x : Y × ℝ, TangentSpace (I.prod 𝓘(ℝ)) x,
      ContMDiffOn (I.prod 𝓘(ℝ)) (I.prod 𝓘(ℝ)).tangent ∞
        (fun x => (⟨x, W x⟩ : TangentBundle (I.prod 𝓘(ℝ)) (Y × ℝ))) U ∧
      (∀ x ∈ U, ∀ i, x ∈ stratum i → A i x (W x) = b i x) ∧
      ∀ x ∈ U, x ∉ K → W x = 0 := by
    intro x₀
    by_cases hxB : x₀ ∈ SB
    · obtain ⟨U, hU, W, hW, hrel⟩ := exists_local_smoothTimeLift_of_spatial_surjective
        (fun x => (h x, T x)) (hh.prodMk_space hT) x₀ (hRB x₀ hxB)
      refine ⟨U ∩ interior K, inter_mem hU
        (isOpen_interior.mem_nhds (hSK (Or.inr hxB))), W,
        hW.mono inter_subset_left, ?_, ?_⟩
      · intro x hx i _hi
        have hw := (hrel x hx.1).1
        rw [modelWithCornersSelf_prod, ← chartedSpaceSelf_prod,
          mfderiv_prodMk ((hh x).mdifferentiableAt (by simp))
            ((hT x).mdifferentiableAt (by simp))] at hw
        have hwh := congrArg Prod.fst hw
        have hwT := congrArg Prod.snd hw
        cases i <;> simp only [A, b, Bool.false_eq_true, ↓reduceIte]
        · exact Prod.ext (Prod.ext hwh rfl) (hrel x hx.1).2
        · exact Prod.ext (Prod.ext hwh hwT) (hrel x hx.1).2
      · intro x hx hxK
        exact False.elim (hxK (interior_subset hx.2))
    · by_cases hxA : x₀ ∈ SA
      · obtain ⟨U, hU, W, hW, hrel⟩ := exists_local_smoothTimeLift_of_spatial_surjective
          h hh x₀ (hRA x₀ hxA)
        refine ⟨(U ∩ SBᶜ) ∩ interior K,
          inter_mem (inter_mem hU (hSB.isClosed.isOpen_compl.mem_nhds hxB))
            (isOpen_interior.mem_nhds (hSK (Or.inl hxA))), W,
          hW.mono (inter_subset_left.trans inter_subset_left), ?_, ?_⟩
        · intro x hx i hi
          cases i
          · simp only [A, b, Bool.false_eq_true, ↓reduceIte]
            exact Prod.ext (Prod.ext (hrel x hx.1.1).1 rfl) (hrel x hx.1.1).2
          · exact False.elim (hx.1.2 hi)
        · intro x hx hxK
          exact False.elim (hxK (interior_subset hx.2))
      · refine ⟨SAᶜ ∩ SBᶜ, inter_mem (hSA.isClosed.isOpen_compl.mem_nhds hxA)
          (hSB.isClosed.isOpen_compl.mem_nhds hxB), fun _x => 0,
          (Bundle.contMDiff_zeroSection ℝ (TangentSpace (I.prod 𝓘(ℝ)))).contMDiffOn, ?_, ?_⟩
        · intro x hx i hi
          cases i
          · exact False.elim (hx.1 hi)
          · exact False.elim (hx.2 hi)
        · intro _x _hx _hxK
          rfl
  obtain ⟨W, hW, hWsupp, _hWc⟩ :=
    exists_smoothAffineConstraintSection_of_local A b stratum hK hlocal
  let X : ℝ → ∀ y : Y, TangentSpace I y := fun τ y => (W (y, τ)).1
  have hX : ContMDiff (𝓘(ℝ).prod I) I.tangent ∞
      (fun p : ℝ × Y => (⟨p.2, X p.1 p.2⟩ : TangentBundle I Y)) := by
    have hf : ContMDiff (I.prod 𝓘(ℝ)) I ∞ (Prod.fst : Y × ℝ → Y) := contMDiff_fst
    have ht := (hf.contMDiff_tangentMap (m := ∞) (by simp)).comp W.contMDiff
    have ht' := ht.comp (contMDiff_snd.prodMk contMDiff_fst)
    change ContMDiff (𝓘(ℝ).prod I) I.tangent ∞
      (fun p : ℝ × Y => tangentMap (I.prod 𝓘(ℝ)) I Prod.fst
        (⟨(p.2, p.1), W (p.2, p.1)⟩ : TangentBundle (I.prod 𝓘(ℝ)) (Y × ℝ))) at ht'
    simpa only [tangentMap_prodFst] using ht'
  have hzero : ∀ τ y, y ∉ Prod.fst '' K → X τ y = 0 := by
    intro τ y hy
    have hyK : (y, τ) ∉ K := fun hmem => hy ⟨(y, τ), hmem, rfl⟩
    have hw : W (y, τ) = 0 := by
      by_contra hn
      exact hyK (hWsupp (subset_closure hn))
    exact congrArg Prod.fst hw
  have hWA : ∀ x ∈ SA,
      mfderiv (I.prod 𝓘(ℝ)) 𝓘(ℝ, F) h x (X x.2 x.1, 1) = 0 := by
    intro x hx
    have hw := hW x false hx
    have ht : (W x).2 = 1 := congrArg Prod.snd hw
    have hhW : mfderiv (I.prod 𝓘(ℝ)) 𝓘(ℝ, F) h x (W x) = 0 :=
      congrArg (fun v : (F × ℝ) × ℝ => v.1.1) hw
    have hp : (W x).1 = X x.2 x.1 := rfl
    rw [← hp, ← ht]
    exact hhW
  refine ⟨X, hX, hzero, hWA, ?_⟩
  intro x hx
  have hw := hW x true hx
  have ht : (W x).2 = 1 := congrArg Prod.snd hw
  have hhW : mfderiv (I.prod 𝓘(ℝ)) 𝓘(ℝ, F) h x (W x) = 0 :=
    congrArg (fun v : (F × ℝ) × ℝ => v.1.1) hw
  have hTW : mfderiv (I.prod 𝓘(ℝ)) 𝓘(ℝ) T x (W x) = 0 :=
    congrArg (fun v : (F × ℝ) × ℝ => v.1.2) hw
  have hp : (W x).1 = X x.2 x.1 := rfl
  rw [← hp, ← ht]
  exact ⟨hhW, hTW⟩

end DifferentialGeometry.Topology.Ehresmann
