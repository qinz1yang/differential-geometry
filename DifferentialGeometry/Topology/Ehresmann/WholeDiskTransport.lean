import DifferentialGeometry.Topology.Ehresmann.FaceTransportProducer
import DifferentialGeometry.Topology.Embedding.Diffeomorph
import DifferentialGeometry.Topology.Handle.Manifold
import DifferentialGeometry.Topology.Manifold.SmoothEmbeddingOpenTarget
import DifferentialGeometry.Topology.Manifold.SmoothEmbeddingFromOpen
import DifferentialGeometry.Topology.Manifold.OpenSubtype

/-!
# E0: the whole disk fibre of a compact transverse trace is a smooth disk (FC34 for EDP04)

Package E0 of draft 74 (`wholeDisk_of_compact_transverse_trace74`, disposition D74-11 / D74-17):
"EDP04's two-strata rank + the whole compact trace + the original disk ⟹ the whole smooth disk".
Blueprint `master207B.tex`, EDP04 (B:6949–7038: the family (EI) `𝓗_τ = ((1-τ)η_i + τg_i, (1-τ)H₀ +
τT)` on the original source `Y_i`, `X_a = {a} × (-∞, 4Δ]`; "the ENTIRE time-dependent inverse image
lies in the interior of the SAME compact `Q_i`", "transversality to BOTH `X_a` and `∂X_a` throughout
the family"; "Apply FC34 ...  The initial fiber ... is LFR28's closed smooth disk"; "Each WHOLE disk
fiber is smoothly ambient isotopic inside some `Y_i` to a fiber of the SAME original LFR28 disk
packet") and FC34 (B:6187–6205). Abstract kernel: no chain object, no family; the row-level binding
(EDP04 on the actual `Y_i`, `g_i = u_i(E)/R_i`, `T = A/s`, the original LFR28 disk as a smooth
embedding) is a separate step.

* `exists_compact_faceTrace_rankNeighborhoods_exact_EFC`,
  `exists_diffeomorph_face_of_compact_trace_EFC`: the tree's FC34 face transport
  (`exists_diffeomorph_face_of_compact_transport`) with transversality and localization assumed ONLY
  on the trace (`T ≤ c`) and its face (`T = c`) — the band margin of the original statement is not
  needed (its proof uses the margins only at the exact level).
* **`wholeDisk_of_compact_transverse_trace74`** (E0 head): if the time-0 fibre `{h₀ = a, T₀ ≤ c}` is
  the range of a smooth embedding `φ₀ : ClosedCell 2 → Y` whose boundary circle goes onto the time-0
  rim `{h₀ = a, T₀ = c}`, then the WHOLE time-1 fibre `{h₁ = a, T₁ ≤ c}` is the range of the smooth
  embedding `Ψ ∘ φ₀` (boundary circle onto the time-1 rim), for a compactly supported ambient
  diffeomorphism `Ψ` (the ambient isotopy's time-one map).
* `wholeDisk_range_of_compact_transverse_trace_EFC`: the same without the boundary clause.
* `wholeDisk_of_compact_transverse_trace_opens_EFC`: the family on an open source `O ⊆ M` (EDP04's
  `Y_i`), the disks as smooth embeddings into the ambient `M`.
-/

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

/-- **Exact-level form** of `exists_compact_faceTrace_rankNeighborhoods`: the compact face trace has
compact neighbourhoods inside both spatial rank sets, with transversality and localization assumed
ONLY on the trace itself (`T ≤ c`, resp. `T = c`), no band margin. -/
theorem exists_compact_faceTrace_rankNeighborhoods_exact_EFC
    (h : Y × ℝ → F) (T : Y × ℝ → ℝ)
    (hh : ContMDiff (I.prod 𝓘(ℝ)) 𝓘(ℝ, F) ∞ h)
    (hT : ContMDiff (I.prod 𝓘(ℝ)) 𝓘(ℝ) ∞ T) (a : F) (c : ℝ)
    (hreg : ∀ τ ∈ Icc (0 : ℝ) 1, ∀ y, h (y, τ) = a → T (y, τ) ≤ c →
      Surjective (mfderiv I 𝓘(ℝ, F) (fun z => h (z, τ)) y))
    (hface : ∀ τ ∈ Icc (0 : ℝ) 1, ∀ y, h (y, τ) = a → T (y, τ) = c →
      Surjective (mfderiv I 𝓘(ℝ, F × ℝ) (fun z => (h (z, τ), T (z, τ))) y))
    {Q : Set Y} (hQ : IsCompact Q)
    (hloc : ∀ τ ∈ Icc (0 : ℝ) 1, ∀ y, h (y, τ) = a → T (y, τ) ≤ c → y ∈ Q) :
    ∃ SA SB K : Set (Y × ℝ), IsCompact SA ∧ IsCompact SB ∧ IsCompact K ∧
      {x | x.2 ∈ Icc (0 : ℝ) 1 ∧ h x = a ∧ T x ≤ c} ⊆ interior SA ∧
      {x | x.2 ∈ Icc (0 : ℝ) 1 ∧ h x = a ∧ T x = c} ⊆ interior SB ∧
      SA ⊆ {x | Surjective (mfderiv I 𝓘(ℝ, F) (fun z => h (z, x.2)) x.1)} ∧
      SB ⊆ {x | Surjective (mfderiv I 𝓘(ℝ, F × ℝ)
        (fun z => (h (z, x.2), T (z, x.2))) x.1)} ∧ SA ∪ SB ⊆ interior K := by
  let : LocallyCompactSpace H := I.locallyCompactSpace
  let : LocallyCompactSpace Y := ChartedSpace.locallyCompactSpace H Y
  let A : Set (Y × ℝ) := {x | x.2 ∈ Icc (0 : ℝ) 1 ∧ h x = a ∧ T x ≤ c}
  let B : Set (Y × ℝ) := {x | x.2 ∈ Icc (0 : ℝ) 1 ∧ h x = a ∧ T x = c}
  have hAclosed : IsClosed A :=
    (isClosed_Icc.preimage continuous_snd).inter
      ((isClosed_eq hh.continuous continuous_const).inter
        (isClosed_le hT.continuous continuous_const))
  have hBclosed : IsClosed B :=
    (isClosed_Icc.preimage continuous_snd).inter
      ((isClosed_eq hh.continuous continuous_const).inter
        (isClosed_eq hT.continuous continuous_const))
  have hAc : IsCompact A := (hQ.prod isCompact_Icc).of_isClosed_subset hAclosed
    (fun x hx => ⟨hloc x.2 hx.1 x.1 hx.2.1 hx.2.2, hx.1⟩)
  have hBc : IsCompact B := hAc.of_isClosed_subset hBclosed
    (fun x hx => ⟨hx.1, hx.2.1, le_of_eq hx.2.2⟩)
  obtain ⟨SA, hSA, hASA, hSAR⟩ := exists_compact_between hAc
    (isOpen_spatial_surjective_mfderiv h hh)
    (fun x hx => hreg x.2 hx.1 x.1 hx.2.1 hx.2.2)
  obtain ⟨SB, hSB, hBSB, hSBR⟩ := exists_compact_between hBc
    (isOpen_spatial_surjective_mfderiv (fun x => (h x, T x)) (hh.prodMk_space hT))
    (fun x hx => hface x.2 hx.1 x.1 hx.2.1 hx.2.2)
  obtain ⟨K, hK, hSK, _hKU⟩ := exists_compact_between (hSA.union hSB) isOpen_univ
    (subset_univ (SA ∪ SB))
  exact ⟨SA, SB, K, hSA, hSB, hK, hASA, hBSB, hSAR, hSBR, hSK⟩

variable [I.Boundaryless] [T2Space Y] [SigmaCompactSpace Y]

omit [FiniteDimensional ℝ E] [FiniteDimensional ℝ F]
  [IsManifold I ∞ Y] [I.Boundaryless] [T2Space Y] [SigmaCompactSpace Y] in
theorem hasFDerivAt_time_comp_of_total_zero_EFC
    (g : Y × ℝ → F) (hg : ContMDiff (I.prod 𝓘(ℝ)) 𝓘(ℝ, F) ∞ g)
    (γ : ℝ → Y) (t : ℝ) (v : TangentSpace I (γ t))
    (hγ : HasMFDerivAt 𝓘(ℝ) I γ t ((1 : ℝ →L[ℝ] ℝ).smulRight v))
    (hz : mfderiv (I.prod 𝓘(ℝ)) 𝓘(ℝ, F) g (γ t, t) (v, 1) = 0) :
    HasFDerivAt (fun u => g (γ u, u)) (0 : ℝ →L[ℝ] F) t := by
  have hq : HasMFDerivAt 𝓘(ℝ) (I.prod 𝓘(ℝ)) (fun u => (γ u, u)) t
      (((1 : ℝ →L[ℝ] ℝ).smulRight v).prod (1 : ℝ →L[ℝ] ℝ)) :=
    hγ.prodMk (hasMFDerivAt_id (I := 𝓘(ℝ)) (x := t))
  have hdg : HasMFDerivAt (I.prod 𝓘(ℝ)) 𝓘(ℝ, F) g (γ t, t)
      (mfderiv (I.prod 𝓘(ℝ)) 𝓘(ℝ, F) g (γ t, t)) :=
    ((hg (γ t, t)).mdifferentiableAt (by simp)).hasMFDerivAt
  have hc := hdg.comp (f := fun u => (γ u, u)) t hq
  let L : E × ℝ →L[ℝ] F := mfderiv (I.prod 𝓘(ℝ)) 𝓘(ℝ, F) g (γ t, t)
  let w : E := v
  have hz' : L (w, 1) = (0 : F) := hz
  have heq : L.comp (((1 : ℝ →L[ℝ] ℝ).smulRight w).prod (1 : ℝ →L[ℝ] ℝ)) = 0 := by
    apply ContinuousLinearMap.ext
    intro r
    change L (r • w, r) = 0
    have hp : (r • w, r) = r • (w, (1 : ℝ)) := by
      apply Prod.ext
      · rfl
      · change r = r * 1
        exact (mul_one r).symm
    rw [hp, map_smul]
    rw [hz', smul_zero]
  have hc' : HasFDerivAt (fun u => g (γ u, u))
      (L.comp (((1 : ℝ →L[ℝ] ℝ).smulRight w).prod (1 : ℝ →L[ℝ] ℝ))) t := hc.hasFDerivAt
  rw [heq] at hc'
  exact hc'

/-- **FC34, face form, exact-level hypotheses** (`exists_diffeomorph_face_of_compact_transport`
without the band margin): a smooth family `(h_τ, T_τ)`, `τ ∈ [0,1]`, transverse to the level `h = a`
on the whole trace `{h_τ = a, T_τ ≤ c}` and of rank two on its face `{h_τ = a, T_τ = c}`, with the
whole trace in one compact set, has a compactly supported ambient diffeomorphism carrying the time-0
trace and face onto the time-1 trace and face. -/
theorem exists_diffeomorph_face_of_compact_trace_EFC
    (h : Y × ℝ → F) (T : Y × ℝ → ℝ)
    (hh : ContMDiff (I.prod 𝓘(ℝ)) 𝓘(ℝ, F) ∞ h)
    (hT : ContMDiff (I.prod 𝓘(ℝ)) 𝓘(ℝ) ∞ T) (a : F) (c : ℝ)
    (hreg : ∀ τ ∈ Icc (0 : ℝ) 1, ∀ y, h (y, τ) = a → T (y, τ) ≤ c →
      Surjective (mfderiv I 𝓘(ℝ, F) (fun z => h (z, τ)) y))
    (hface : ∀ τ ∈ Icc (0 : ℝ) 1, ∀ y, h (y, τ) = a → T (y, τ) = c →
      Surjective (mfderiv I 𝓘(ℝ, F × ℝ) (fun z => (h (z, τ), T (z, τ))) y))
    {Q : Set Y} (hQ : IsCompact Q)
    (hloc : ∀ τ ∈ Icc (0 : ℝ) 1, ∀ y, h (y, τ) = a → T (y, τ) ≤ c → y ∈ Q) :
    ∃ Ψ : Y ≃ₘ⟮I, I⟯ Y,
      (∃ K : Set Y, IsCompact K ∧ ∀ y ∉ K, Ψ y = y) ∧
      Ψ '' {y | h (y, 0) = a ∧ T (y, 0) ≤ c} = {y | h (y, 1) = a ∧ T (y, 1) ≤ c} ∧
      Ψ '' {y | h (y, 0) = a ∧ T (y, 0) = c} = {y | h (y, 1) = a ∧ T (y, 1) = c} := by
  obtain ⟨SA, SB, K, hSA, hSB, hK, hASA, hBSB, hRA, hRB, hSK⟩ :=
    exists_compact_faceTrace_rankNeighborhoods_exact_EFC h T hh hT a c hreg hface hQ hloc
  obtain ⟨X, hX, hzero, hXA, hXB⟩ :=
    exists_compactSupport_faceTransportField h T hh hT hSA hSB hK hSK hRA hRB
  have hsp : IsCompact (Prod.fst '' K) := hK.image continuous_fst
  obtain ⟨Ψ, hself, hcomp, hout, hflow⟩ :=
    exists_compactSupport_ambientTransport X hX hsp hzero
  have hpres : ∀ s ∈ Icc (0 : ℝ) 1, ∀ y,
      (h (y, s) = a ∧ T (y, s) ≤ c → ∀ t ∈ Icc (0 : ℝ) 1,
        h (Ψ s t y, t) = a ∧ T (Ψ s t y, t) ≤ c) ∧
      (h (y, s) = a ∧ T (y, s) = c → ∀ t ∈ Icc (0 : ℝ) 1,
        h (Ψ s t y, t) = a ∧ T (Ψ s t y, t) = c) := by
    intro s hs y
    let γ : ℝ → Y := fun t => Ψ s t y
    let q : ℝ → Y × ℝ := fun t => (γ t, t)
    have hγc : Continuous γ := continuous_iff_continuousAt.mpr
      (fun t => (hflow s t y).continuousAt)
    have hqc : Continuous q := hγc.prodMk continuous_id
    have hInv := face_invariant_on_Icc_of_neighborhood_derivatives
      (fun t => h (q t)) (fun t => T (q t)) (hh.continuous.comp hqc) (hT.continuous.comp hqc)
      a c (isOpen_interior.preimage hqc) (isOpen_interior.preimage hqc)
      (fun t ht hta htc => hASA ⟨ht, hta, htc⟩)
      (fun t ht hta htc => hBSB ⟨ht, hta, htc⟩)
      (fun t _ht htu => hasFDerivAt_time_comp_of_total_zero_EFC h hh γ t
        (X t (γ t)) (hflow s t y) (hXA (q t) (interior_subset htu)))
      (fun t _ht htv => by
        have hd := hasFDerivAt_time_comp_of_total_zero_EFC T hT γ t
          (X t (γ t)) (hflow s t y) (hXB (q t) (interior_subset htv)).2
        simpa only [zero_apply] using hd.hasDerivAt) hs
    simpa only [q, γ, hself] using hInv
  have h0 : (0 : ℝ) ∈ Icc (0 : ℝ) 1 := ⟨le_rfl, zero_le_one⟩
  have h1 : (1 : ℝ) ∈ Icc (0 : ℝ) 1 := ⟨zero_le_one, le_rfl⟩
  refine ⟨Ψ 0 1, ⟨Prod.fst '' K, hsp, fun y hy => hout 0 1 y hy⟩, ?_, ?_⟩
  · apply subset_antisymm
    · rintro _z ⟨y, hy, rfl⟩
      exact (hpres 0 h0 y).1 hy 1 h1
    · intro z hz
      refine ⟨Ψ 1 0 z, (hpres 1 h1 z).1 hz 0 h0, ?_⟩
      exact (hcomp 1 0 1 z).trans (hself 1 z)
  · apply subset_antisymm
    · rintro _z ⟨y, hy, rfl⟩
      exact (hpres 0 h0 y).2 hy 1 h1
    · intro z hz
      refine ⟨Ψ 1 0 z, (hpres 1 h1 z).2 hz 0 h0, ?_⟩
      exact (hcomp 1 0 1 z).trans (hself 1 z)


omit [FiniteDimensional ℝ E] [FiniteDimensional ℝ F] [IsManifold I ∞ Y] [I.Boundaryless]
  [T2Space Y] [SigmaCompactSpace Y] in
/-- The derivative of a function smooth at a point of an open subset agrees with the derivative of
its restriction to that open subset. -/
theorem mfderiv_restrict_opens_EFC (O : TopologicalSpace.Opens Y) (f : Y → F) (y : O)
    (hf : MDifferentiableAt I 𝓘(ℝ, F) f y) :
    mfderiv I 𝓘(ℝ, F) (fun z : O => f z) y = mfderiv I 𝓘(ℝ, F) f y := by
  have hd : HasMFDerivAt I 𝓘(ℝ, F) (fun z : O => f z) y
      ((mfderiv I 𝓘(ℝ, F) f y).comp (ContinuousLinearMap.id ℝ E)) :=
    hf.hasMFDerivAt.comp y (DifferentialGeometry.hasMFDerivAt_subtype_val (I := I) O y)
  rw [hd.mfderiv]
  rfl

omit [FiniteDimensional ℝ E] [FiniteDimensional ℝ F] [IsManifold I ∞ Y] [I.Boundaryless]
  [T2Space Y] [SigmaCompactSpace Y] in
/-- A slice of a family smooth on `O × ℝ` is differentiable at the points of `O`. -/
theorem mdifferentiableAt_slice_opens_EFC (O : TopologicalSpace.Opens Y) {f : Y × ℝ → F}
    (hf : ContMDiffOn (I.prod 𝓘(ℝ)) 𝓘(ℝ, F) ∞ f ((O : Set Y) ×ˢ univ)) (τ : ℝ) {y : Y}
    (hy : y ∈ O) : MDifferentiableAt I 𝓘(ℝ, F) (fun z => f (z, τ)) y := by
  have hι : ContMDiff I (I.prod 𝓘(ℝ)) ∞ (fun z : Y => (z, τ)) :=
    contMDiff_id.prodMk contMDiff_const
  have hs : ContMDiffOn I 𝓘(ℝ, F) ∞ (fun z => f (z, τ)) O :=
    hf.comp hι.contMDiffOn (fun z hz => ⟨hz, mem_univ _⟩)
  exact ((hs y hy).contMDiffAt (O.isOpen.mem_nhds hy)).mdifferentiableAt (by simp)

omit [FiniteDimensional ℝ E] [FiniteDimensional ℝ F] [IsManifold I ∞ Y] [I.Boundaryless]
  [T2Space Y] [SigmaCompactSpace Y] in
/-- A family smooth on `O × ℝ` restricts to a smooth family on the open submanifold `O`. -/
theorem contMDiff_restrict_opens_family_EFC (O : TopologicalSpace.Opens Y) {f : Y × ℝ → F}
    (hf : ContMDiffOn (I.prod 𝓘(ℝ)) 𝓘(ℝ, F) ∞ f ((O : Set Y) ×ˢ univ)) :
    ContMDiff (I.prod 𝓘(ℝ)) 𝓘(ℝ, F) ∞ (fun x : O × ℝ => f (x.1, x.2)) := by
  have hι : ContMDiff (I.prod 𝓘(ℝ)) (I.prod 𝓘(ℝ)) ∞ (fun x : O × ℝ => ((x.1 : Y), x.2)) :=
    (contMDiff_subtype_val.comp contMDiff_fst).prodMk contMDiff_snd
  exact hf.comp_contMDiff hι (fun x => ⟨x.1.2, mem_univ _⟩)

open DifferentialGeometry.Topology.Handle in
attribute [local instance] closedCellChartedSpaceSucc closedCellIsManifold

/-- **E0 (`wholeDisk_of_compact_transverse_trace74`): the whole time-one fibre is a smooth disk.**
A smooth family `(h_τ, T_τ) : Y → ℝ²` (`τ ∈ [0,1]`) transverse to `{h = a}` on the whole trace
`{h_τ = a, T_τ ≤ c}` and of rank two on the rim `{h_τ = a, T_τ = c}` (EDP04's two strata), with the
whole trace in one compact `Q`, and an original smooth disk `φ₀` exactly filling the time-0 fibre
with its boundary circle onto the time-0 rim: then `Ψ ∘ φ₀` is a smooth embedding exactly filling
the time-1 fibre, with boundary circle onto the time-1 rim, for a compactly supported
diffeomorphism `Ψ`. -/
theorem wholeDisk_of_compact_transverse_trace74
    (h T : Y × ℝ → ℝ) (hh : ContMDiff (I.prod 𝓘(ℝ)) 𝓘(ℝ) ∞ h)
    (hT : ContMDiff (I.prod 𝓘(ℝ)) 𝓘(ℝ) ∞ T) (a c : ℝ)
    (hreg : ∀ τ ∈ Icc (0 : ℝ) 1, ∀ y, h (y, τ) = a → T (y, τ) ≤ c →
      Surjective (mfderiv I 𝓘(ℝ) (fun z => h (z, τ)) y))
    (hface : ∀ τ ∈ Icc (0 : ℝ) 1, ∀ y, h (y, τ) = a → T (y, τ) = c →
      Surjective (mfderiv I 𝓘(ℝ, ℝ × ℝ) (fun z => (h (z, τ), T (z, τ))) y))
    {Q : Set Y} (hQ : IsCompact Q)
    (hloc : ∀ τ ∈ Icc (0 : ℝ) 1, ∀ y, h (y, τ) = a → T (y, τ) ≤ c → y ∈ Q)
    {φ₀ : ClosedCell 2 → Y} (hφ₀ : IsSmoothEmbedding (𝓡∂ 2) I ∞ φ₀)
    (hφ₀r : range φ₀ = {y | h (y, 0) = a ∧ T (y, 0) ≤ c})
    (hφ₀b : range (φ₀ ∘ cellBoundaryInclusion 2) = {y | h (y, 0) = a ∧ T (y, 0) = c}) :
    ∃ Ψ : Y ≃ₘ⟮I, I⟯ Y, (∃ K : Set Y, IsCompact K ∧ ∀ y ∉ K, Ψ y = y) ∧
      IsSmoothEmbedding (𝓡∂ 2) I ∞ (Ψ ∘ φ₀) ∧
      range (Ψ ∘ φ₀) = {y | h (y, 1) = a ∧ T (y, 1) ≤ c} ∧
      range ((Ψ ∘ φ₀) ∘ cellBoundaryInclusion 2) = {y | h (y, 1) = a ∧ T (y, 1) = c} := by
  obtain ⟨Ψ, hK, himage, hface'⟩ :=
    exists_diffeomorph_face_of_compact_trace_EFC h T hh hT a c hreg hface hQ hloc
  refine ⟨Ψ, hK, hφ₀.diffeomorph_comp Ψ, ?_, ?_⟩
  · rw [range_comp, hφ₀r, himage]
  · rw [comp_assoc, range_comp, hφ₀b, hface']

/-- **E0 without the boundary clause**: the whole time-one fibre is the range of `Ψ ∘ φ₀`. -/
theorem wholeDisk_range_of_compact_transverse_trace_EFC
    (h T : Y × ℝ → ℝ) (hh : ContMDiff (I.prod 𝓘(ℝ)) 𝓘(ℝ) ∞ h)
    (hT : ContMDiff (I.prod 𝓘(ℝ)) 𝓘(ℝ) ∞ T) (a c : ℝ)
    (hreg : ∀ τ ∈ Icc (0 : ℝ) 1, ∀ y, h (y, τ) = a → T (y, τ) ≤ c →
      Surjective (mfderiv I 𝓘(ℝ) (fun z => h (z, τ)) y))
    (hface : ∀ τ ∈ Icc (0 : ℝ) 1, ∀ y, h (y, τ) = a → T (y, τ) = c →
      Surjective (mfderiv I 𝓘(ℝ, ℝ × ℝ) (fun z => (h (z, τ), T (z, τ))) y))
    {Q : Set Y} (hQ : IsCompact Q)
    (hloc : ∀ τ ∈ Icc (0 : ℝ) 1, ∀ y, h (y, τ) = a → T (y, τ) ≤ c → y ∈ Q)
    {φ₀ : ClosedCell 2 → Y} (hφ₀ : IsSmoothEmbedding (𝓡∂ 2) I ∞ φ₀)
    (hφ₀r : range φ₀ = {y | h (y, 0) = a ∧ T (y, 0) ≤ c}) :
    ∃ Ψ : Y ≃ₘ⟮I, I⟯ Y, (∃ K : Set Y, IsCompact K ∧ ∀ y ∉ K, Ψ y = y) ∧
      IsSmoothEmbedding (𝓡∂ 2) I ∞ (Ψ ∘ φ₀) ∧
      range (Ψ ∘ φ₀) = {y | h (y, 1) = a ∧ T (y, 1) ≤ c} := by
  obtain ⟨Ψ, hK, himage, -⟩ :=
    exists_diffeomorph_face_of_compact_trace_EFC h T hh hT a c hreg hface hQ hloc
  refine ⟨Ψ, hK, hφ₀.diffeomorph_comp Ψ, ?_⟩
  rw [range_comp, hφ₀r, himage]

/-- **E0 on an open source** (EDP04's `Y_i ⊆ M`): the family `(h, T)` smooth on `O × ℝ`, transverse
on the whole trace in `O` and of rank two on its rim, with the whole trace in one compact `Q ⊆ O`,
and an original smooth disk `φ₀ : ClosedCell 2 → M` exactly filling the time-0 fibre in `O`
(boundary circle onto the time-0 rim). Then a smooth embedding `φ : ClosedCell 2 → M` exactly fills
the time-1 fibre in `O` (boundary circle onto the time-1 rim), and `φ = Ψ ∘ φ₀` for a compactly
supported diffeomorphism `Ψ` of `O` (smooth ambient isotopy inside `O`). -/
theorem wholeDisk_of_compact_transverse_trace_opens_EFC {M : Type*} [TopologicalSpace M]
    [ChartedSpace H M] [IsManifold I ∞ M] [T2Space M] [SecondCountableTopology M]
    (O : TopologicalSpace.Opens M) (h T : M × ℝ → ℝ)
    (hh : ContMDiffOn (I.prod 𝓘(ℝ)) 𝓘(ℝ) ∞ h ((O : Set M) ×ˢ univ))
    (hT : ContMDiffOn (I.prod 𝓘(ℝ)) 𝓘(ℝ) ∞ T ((O : Set M) ×ˢ univ)) (a c : ℝ)
    (hreg : ∀ τ ∈ Icc (0 : ℝ) 1, ∀ y ∈ O, h (y, τ) = a → T (y, τ) ≤ c →
      Surjective (mfderiv I 𝓘(ℝ) (fun z => h (z, τ)) y))
    (hface : ∀ τ ∈ Icc (0 : ℝ) 1, ∀ y ∈ O, h (y, τ) = a → T (y, τ) = c →
      Surjective (mfderiv I 𝓘(ℝ, ℝ × ℝ) (fun z => (h (z, τ), T (z, τ))) y))
    {Q : Set M} (hQ : IsCompact Q) (hQO : Q ⊆ O)
    (hloc : ∀ τ ∈ Icc (0 : ℝ) 1, ∀ y ∈ O, h (y, τ) = a → T (y, τ) ≤ c → y ∈ Q)
    {φ₀ : ClosedCell 2 → M} (hφ₀ : IsSmoothEmbedding (𝓡∂ 2) I ∞ φ₀)
    (hφ₀r : range φ₀ = {y | y ∈ O ∧ h (y, 0) = a ∧ T (y, 0) ≤ c})
    (hφ₀b : range (φ₀ ∘ cellBoundaryInclusion 2) =
      {y | y ∈ O ∧ h (y, 0) = a ∧ T (y, 0) = c}) :
    ∃ φ : ClosedCell 2 → M, IsSmoothEmbedding (𝓡∂ 2) I ∞ φ ∧
      range φ = {y | y ∈ O ∧ h (y, 1) = a ∧ T (y, 1) ≤ c} ∧
      range (φ ∘ cellBoundaryInclusion 2) = {y | y ∈ O ∧ h (y, 1) = a ∧ T (y, 1) = c} ∧
      ∃ Ψ : O ≃ₘ⟮I, I⟯ O, (∃ K : Set O, IsCompact K ∧ ∀ y ∉ K, Ψ y = y) ∧
        ∀ x (hx : φ₀ x ∈ O), φ x = (Ψ ⟨φ₀ x, hx⟩ : M) := by
  have : LocallyCompactSpace H := I.locallyCompactSpace
  have : LocallyCompactSpace M := ChartedSpace.locallyCompactSpace H M
  have : LocallyCompactSpace O := O.isOpen.locallyCompactSpace
  let h' : O × ℝ → ℝ := fun x => h (x.1, x.2)
  let T' : O × ℝ → ℝ := fun x => T (x.1, x.2)
  have hh' : ContMDiff (I.prod 𝓘(ℝ)) 𝓘(ℝ) ∞ h' := contMDiff_restrict_opens_family_EFC O hh
  have hT' : ContMDiff (I.prod 𝓘(ℝ)) 𝓘(ℝ) ∞ T' := contMDiff_restrict_opens_family_EFC O hT
  have hreg' : ∀ τ ∈ Icc (0 : ℝ) 1, ∀ y : O, h' (y, τ) = a → T' (y, τ) ≤ c →
      Surjective (mfderiv I 𝓘(ℝ) (fun z => h' (z, τ)) y) := by
    intro τ hτ y hy hyc
    have e := mfderiv_restrict_opens_EFC O (fun z => h (z, τ)) y
      (mdifferentiableAt_slice_opens_EFC O hh τ y.2)
    change Surjective (mfderiv I 𝓘(ℝ) (fun z : O => h ((z : M), τ)) y)
    rw [e]
    exact hreg τ hτ y y.2 hy hyc
  have hface' : ∀ τ ∈ Icc (0 : ℝ) 1, ∀ y : O, h' (y, τ) = a → T' (y, τ) = c →
      Surjective (mfderiv I 𝓘(ℝ, ℝ × ℝ) (fun z => (h' (z, τ), T' (z, τ))) y) := by
    intro τ hτ y hy hyc
    have hpair : ContMDiffOn (I.prod 𝓘(ℝ)) 𝓘(ℝ, ℝ × ℝ) ∞ (fun x => (h x, T x))
        ((O : Set M) ×ˢ univ) := hh.prodMk_space hT
    have e := mfderiv_restrict_opens_EFC O (fun z => (h (z, τ), T (z, τ))) y
      (mdifferentiableAt_slice_opens_EFC O hpair τ y.2)
    change Surjective (mfderiv I 𝓘(ℝ, ℝ × ℝ) (fun z : O => (h ((z : M), τ), T ((z : M), τ))) y)
    rw [e]
    exact hface τ hτ y y.2 hy hyc
  have hQ' : IsCompact (Subtype.val ⁻¹' Q : Set O) :=
    (Topology.IsInducing.subtypeVal.isCompact_preimage_iff
      (by rw [Subtype.range_coe_subtype]; exact hQO)).mpr hQ
  have hloc' : ∀ τ ∈ Icc (0 : ℝ) 1, ∀ y : O, h' (y, τ) = a → T' (y, τ) ≤ c →
      y ∈ (Subtype.val ⁻¹' Q : Set O) :=
    fun τ hτ y hy hyc => hloc τ hτ y y.2 hy hyc
  have hmem : ∀ x, φ₀ x ∈ O := fun x => by
    have hx : φ₀ x ∈ range φ₀ := mem_range_self x
    rw [hφ₀r] at hx
    exact hx.1
  let φ₀' : ClosedCell 2 → O := fun x => ⟨φ₀ x, hmem x⟩
  have hφ₀' : IsSmoothEmbedding (𝓡∂ 2) I ∞ φ₀' :=
    DifferentialGeometry.Topology.Manifold.isSmoothEmbedding_intoOpen (𝓡∂ 2) I O φ₀' hφ₀
  have hr' : range φ₀' = {y : O | h' (y, 0) = a ∧ T' (y, 0) ≤ c} := by
    ext y
    constructor
    · rintro ⟨x, rfl⟩
      have hx : φ₀ x ∈ range φ₀ := mem_range_self x
      rw [hφ₀r] at hx
      exact hx.2
    · intro hy
      have hy' : (y : M) ∈ range φ₀ := by rw [hφ₀r]; exact ⟨y.2, hy⟩
      obtain ⟨x, hx⟩ := hy'
      exact ⟨x, Subtype.ext hx⟩
  have hb' : range (φ₀' ∘ cellBoundaryInclusion 2) =
      {y : O | h' (y, 0) = a ∧ T' (y, 0) = c} := by
    ext y
    constructor
    · rintro ⟨x, rfl⟩
      have hx : φ₀ (cellBoundaryInclusion 2 x) ∈ range (φ₀ ∘ cellBoundaryInclusion 2) :=
        mem_range_self x
      rw [hφ₀b] at hx
      exact hx.2
    · intro hy
      have hy' : (y : M) ∈ range (φ₀ ∘ cellBoundaryInclusion 2) := by
        rw [hφ₀b]; exact ⟨y.2, hy⟩
      obtain ⟨x, hx⟩ := hy'
      exact ⟨x, Subtype.ext hx⟩
  obtain ⟨Ψ, hK, hemb, hrange, hbound⟩ := wholeDisk_of_compact_transverse_trace74 h' T' hh' hT'
    a c hreg' hface' hQ' hloc' hφ₀' hr' hb'
  refine ⟨Subtype.val ∘ (Ψ ∘ φ₀'),
    DifferentialGeometry.Topology.Manifold.isSmoothEmbedding_fromOpen (𝓡∂ 2) I O _ hemb,
    ?_, ?_, Ψ, hK, fun x hx => rfl⟩
  · rw [range_comp, hrange]
    ext y
    constructor
    · rintro ⟨z, hz, rfl⟩
      exact ⟨z.2, hz⟩
    · rintro ⟨hy, hz⟩
      exact ⟨⟨y, hy⟩, hz, rfl⟩
  · rw [comp_assoc, range_comp, hbound]
    ext y
    constructor
    · rintro ⟨z, hz, rfl⟩
      exact ⟨z.2, hz⟩
    · rintro ⟨hy, hz⟩
      exact ⟨⟨y, hy⟩, hz, rfl⟩

end DifferentialGeometry.Topology.Ehresmann
