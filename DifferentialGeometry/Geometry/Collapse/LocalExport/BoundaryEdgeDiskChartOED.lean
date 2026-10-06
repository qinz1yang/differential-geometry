import DifferentialGeometry.Geometry.Collapse.LocalExport.BoundaryEdgeDiskKernelOED
import DifferentialGeometry.Geometry.Collapse.LocalExport.BoundaryProductChartLocal

/-!
# The edge disk chart `SmoothDiskChartAt_BIFc` from a local record (lane O-EDGEDISK, G1b)

Step f of the edge disk route (S-BAUG-D2 handover §3): the M-level packaging of the N-level
kernel `exists_diskChart_of_sideBoundary_trivialization_OED` into
`SmoothDiskChartAt_BIFc IM 1 f T a X B y`, in the shape of lane O-WF's
`smoothProductChartAt_of_localRecord_OWF` (local record `(κ, σ₀, Dset)` of one marked chart,
open pieces `Mk`, `Pi`, the interior manifold `N` with an embedding `ι : N → M`). The edge
source is NOT open: `X = Xo ∩ {T ≤ a}` with `ι⁻¹ Xo` open; the side function of the kernel is
`a - T ∘ ι`, and the submersion hypothesis on the rim is asked for `(κ ∘ f ∘ ι, T ∘ ι)`.

* `surjective_mfderiv_pair_const_sub_OED`: if `d(g, t)` is onto, so is `d(g, a - t)`;
* **`smoothDiskChartAt_of_localRecord_OED`**: the edge disk chart at `y`;
* `isSmoothEmbedding_comp_diskChart_of_boundaryless_OED`: the cross-model composition argument
  `hιc` for a boundaryless target model.

The composition of the disk chart with `ι` is the explicit argument `hιc` (handover §3 f): for a
target manifold with boundary (`W.Carrier`, ι the inclusion of `W°`) it comes from lane O-CROSS's
half-space tools; for a boundaryless target it is discharged below.
-/

set_option autoImplicit false

noncomputable section

open Set Function Metric Topology Manifold
open scoped ContDiff Manifold Topology
open DifferentialGeometry.Topology

namespace DifferentialGeometry.Geometry.Collapse

attribute [local instance] DifferentialGeometry.Topology.Handle.closedCellChartedSpaceSucc
  DifferentialGeometry.Topology.Handle.closedCellIsManifold

local notation "ℝ²" => EuclideanSpace ℝ (Fin 2)
local notation "ℝ¹" => EuclideanSpace ℝ (Fin 1)

section Chart

variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {HN : Type} [TopologicalSpace HN] {I : ModelWithCorners ℝ E HN} [I.Boundaryless]
  {N : Type} [TopologicalSpace N] [ChartedSpace HN N] [IsManifold I ∞ N] [T2Space N]
  [LocallyCompactSpace N] [SecondCountableTopology N]
  {EM : Type} [NormedAddCommGroup EM] [NormedSpace ℝ EM]
  {HM : Type} [TopologicalSpace HM] {IM : ModelWithCorners ℝ EM HM}
  {M : Type} [TopologicalSpace M] [ChartedSpace HM M]
  {H : Type} [NormedAddCommGroup H] [NormedSpace ℝ H]

omit [FiniteDimensional ℝ E] [I.Boundaryless] [IsManifold I ∞ N] [T2Space N]
  [LocallyCompactSpace N] [SecondCountableTopology N] in
/-- If `(g, t)` is a submersion at `x`, so is `(g, a - t)`. -/
theorem surjective_mfderiv_pair_const_sub_OED {g : N → ℝ¹} {t : N → ℝ} {x : N} (a : ℝ)
    (hg : MDifferentiableAt I 𝓘(ℝ, ℝ¹) g x) (ht : MDifferentiableAt I 𝓘(ℝ, ℝ) t x)
    (hs : Surjective (mfderiv I 𝓘(ℝ, ℝ¹ × ℝ) (fun z => (g z, t z)) x)) :
    Surjective (mfderiv I 𝓘(ℝ, ℝ¹ × ℝ) (fun z => (g z, a - t z)) x) := by
  let L : (ℝ¹ × ℝ) →L[ℝ] ℝ¹ × ℝ :=
    (ContinuousLinearMap.fst ℝ ℝ¹ ℝ).prod (-(ContinuousLinearMap.snd ℝ ℝ¹ ℝ))
  have hF : HasMFDerivAt I 𝓘(ℝ, ℝ¹ × ℝ) (fun z => (g z, t z)) x
      (mfderiv I 𝓘(ℝ, ℝ¹ × ℝ) (fun z => (g z, t z)) x) :=
    (hg.prodMk_space ht).hasMFDerivAt
  have hA := ((L.hasMFDerivAt (x := (g x, t x))).comp x hF).add
    (hasMFDerivAt_const (I := I) (I' := 𝓘(ℝ, ℝ¹ × ℝ)) ((0 : ℝ¹), a) x)
  have heq : (fun z => (g z, a - t z)) =
      ((L ∘ fun z => (g z, t z)) + fun _ => ((0 : ℝ¹), a)) := by
    funext z
    refine Prod.ext (add_zero _).symm ?_
    change a - t z = -t z + a
    ring
  intro q
  obtain ⟨v, hv⟩ := hs (q.1, -q.2)
  refine ⟨v, ?_⟩
  rw [heq, hA.mfderiv]
  change L (mfderiv I 𝓘(ℝ, ℝ¹ × ℝ) (fun z => (g z, t z)) x v) + 0 = q
  rw [hv, add_zero]
  exact Prod.ext rfl (neg_neg _)


/-- **The edge disk chart from the local record of one marked chart** (see the module
docstring). -/
theorem smoothDiskChartAt_of_localRecord_OED (hdim : Module.finrank ℝ E = 1 + 1 + 1)
    (ι : N → M) (hιe : IsEmbedding ι)
    (hιc : ∀ Φ : ℝ¹ × ClosedCell 2 → N, IsSmoothEmbedding ((𝓡 1).prod (𝓡∂ 2)) I ∞ Φ →
      IsSmoothEmbedding ((𝓡 1).prod (𝓡∂ 2)) IM ∞ (ι ∘ Φ))
    (f : M → H) (T : M → ℝ) (a : ℝ) (Xo X : Set M) (B : Set H)
    (κ : H →L[ℝ] ℝ¹) (σ₀ : ℝ¹ → H)
    (Wb Mk O' Pi : Set H) {Dset : Set ℝ¹} (hD : IsOpen Dset)
    (hB : B = Wb ∩ O') (hO' : IsOpen O') (hMk : IsOpen Mk) (hPi : IsOpen Pi)
    (ha : ContDiffOn ℝ ∞ σ₀ Dset)
    (hb : ∀ b ∈ Dset, σ₀ b ∈ Wb ∩ Mk ∧ κ (σ₀ b) = b)
    (hc : ∀ y ∈ Wb ∩ Mk, κ y ∈ Dset ∧ σ₀ (κ y) = y)
    (hX : X = Xo ∩ {p | T p ≤ a})
    (hXι : X ⊆ range ι) (himg : f '' X = B) (hXopen : IsOpen (ι ⁻¹' Xo))
    (hfι : Continuous (f ∘ ι))
    (hg : ContMDiff I (𝓡 1) ∞ (fun x => κ (f (ι x))))
    (hT : ContMDiff I 𝓘(ℝ, ℝ) ∞ (fun x => T (ι x)))
    (hreg : ∀ x, ι x ∈ X → f (ι x) ∈ Mk → f (ι x) ∈ Pi →
      Surjective (mfderiv I (𝓡 1) (fun x => κ (f (ι x))) x))
    (hregb : ∀ x, ι x ∈ X → T (ι x) = a → f (ι x) ∈ Mk → f (ι x) ∈ Pi →
      Surjective (mfderiv I 𝓘(ℝ, ℝ¹ × ℝ) (fun z => (κ (f (ι z)), T (ι z))) x))
    (hprop : ∀ Kc ⊆ B, IsCompact Kc → IsCompact (X ∩ f ⁻¹' Kc))
    {y : H} (hy : y ∈ B) (hyM : y ∈ Mk) (hyP : y ∈ Pi)
    (ψ : ClosedCell 2 → N) (hψ : IsSmoothEmbedding (𝓡∂ 2) I ∞ ψ)
    (hψr : range ψ = {x | ι x ∈ X ∧ f (ι x) = y})
    (hψrim : ∀ w, T (ι (ψ w)) = a ↔ ‖(w : ℝ²)‖ = 1) :
    SmoothDiskChartAt_BIFc IM 1 f T a X B y := by
  classical
  have hyWO : y ∈ Wb ∩ O' := hB ▸ hy
  have hy' : y ∈ Wb ∩ (O' ∩ Pi) ∩ Mk := ⟨⟨hyWO.1, hyWO.2, hyP⟩, hyM⟩
  obtain ⟨hκy, hσy⟩ := hc y ⟨hyWO.1, hyM⟩
  obtain ⟨ε, hε, hsub, hO⟩ := exists_radius_baseChart_OWF σ₀ (O' ∩ Pi) (hO'.inter hPi) hD ha hκy
    (by rw [hσy]; exact ⟨hyWO.2, hyP⟩)
  let g : N → ℝ¹ := fun x => κ (f (ι x))
  let Bh : N → ℝ := fun x => a - T (ι x)
  have hBh : ContMDiff I 𝓘(ℝ, ℝ) ∞ Bh := contMDiff_const.sub hT
  have hXmem : ∀ x, ι x ∈ X ↔ ι x ∈ Xo ∧ 0 ≤ Bh x := by
    intro x
    rw [hX]
    exact and_congr_right' (show T (ι x) ≤ a ↔ 0 ≤ a - T (ι x) from sub_nonneg.symm)
  let R : Set N := {x | ι x ∈ Xo ∧ f (ι x) ∈ Mk ∩ Pi ∧ g x ∈ ball (κ y) ε}
  have hR : IsOpen R :=
    hXopen.inter (((hMk.inter hPi).preimage hfι).inter (isOpen_ball.preimage hg.continuous))
  have hpoint : ∀ x, ι x ∈ X → f (ι x) ∈ Mk → f (ι x) = σ₀ (g x) := by
    intro x hx hxM
    have hfB : f (ι x) ∈ B := himg ▸ mem_image_of_mem f hx
    rw [hB] at hfB
    exact (hc _ ⟨hfB.1, hxM⟩).2.symm
  have hσB : ∀ b ∈ ball (κ y) ε, σ₀ b ∈ B ∧ σ₀ b ∈ Mk ∩ Pi := by
    intro b hb'
    have h := hb b (hsub hb')
    exact ⟨hB ▸ ⟨h.1.1, (hO b hb').1⟩, h.1.2, (hO b hb').2⟩
  have hhprop : ∀ K ⊆ ball (κ y) ε, IsCompact K →
      IsCompact {x | x ∈ R ∧ g x ∈ K ∧ 0 ≤ Bh x} := by
    intro K hK hKc
    have hS : IsCompact (σ₀ '' K) :=
      hKc.image_of_continuousOn (ha.continuousOn.mono (hK.trans hsub))
    have hSB : σ₀ '' K ⊆ B := by
      rintro _ ⟨b, hbK, rfl⟩
      exact (hσB b (hK hbK)).1
    have hcpt := hprop _ hSB hS
    have himage : ι '' {x | x ∈ R ∧ g x ∈ K ∧ 0 ≤ Bh x} = X ∩ f ⁻¹' (σ₀ '' K) := by
      ext p
      constructor
      · rintro ⟨x, ⟨hxR, hxK, hxB⟩, rfl⟩
        have hxX : ι x ∈ X := (hXmem x).mpr ⟨hxR.1, hxB⟩
        exact ⟨hxX, ⟨g x, hxK, (hpoint x hxX hxR.2.1.1).symm⟩⟩
      · rintro ⟨hpX, b, hbK, hbp⟩
        obtain ⟨x, rfl⟩ := hXι hpX
        have hκb : g x = b := by
          change κ (f (ι x)) = b
          rw [← hbp]
          exact (hb b (hsub (hK hbK))).2
        obtain ⟨hxo, hxB⟩ := (hXmem x).mp hpX
        refine ⟨x, ⟨⟨hxo, ?_, ?_⟩, ?_, hxB⟩, rfl⟩
        · rw [← hbp]; exact (hσB b (hK hbK)).2
        · rw [hκb]; exact hK hbK
        · rw [hκb]; exact hbK
    exact hιe.isCompact_iff.mpr (himage ▸ hcpt)
  have hψr' : range ψ = {x | x ∈ R ∧ g x = κ y ∧ 0 ≤ Bh x} := by
    rw [hψr]
    ext x
    constructor
    · rintro ⟨hxX, hxy⟩
      obtain ⟨hxo, hxB⟩ := (hXmem x).mp hxX
      refine ⟨⟨hxo, by rw [hxy]; exact ⟨hyM, hyP⟩, ?_⟩, ?_, hxB⟩
      · change κ (f (ι x)) ∈ ball (κ y) ε
        rw [hxy]
        exact mem_ball_self hε
      · change κ (f (ι x)) = κ y
        rw [hxy]
    · rintro ⟨hxR, hxg, hxB⟩
      have hxX : ι x ∈ X := (hXmem x).mpr ⟨hxR.1, hxB⟩
      refine ⟨hxX, ?_⟩
      rw [hpoint x hxX hxR.2.1.1, show g x = κ y from hxg, hσy]
  have hregR : ∀ x ∈ R, 0 ≤ Bh x → Surjective (mfderiv I (𝓡 1) g x) :=
    fun x hx hxB => hreg x ((hXmem x).mpr ⟨hx.1, hxB⟩) hx.2.1.1 hx.2.1.2
  have hregbR : ∀ x ∈ R, Bh x = 0 →
      Surjective (mfderiv I 𝓘(ℝ, ℝ¹ × ℝ) (fun z => (g z, Bh z)) x) := by
    intro x hx hxB
    have hTa : T (ι x) = a := (sub_eq_zero.mp hxB).symm
    exact surjective_mfderiv_pair_const_sub_OED a ((hg x).mdifferentiableAt (by simp))
      ((hT x).mdifferentiableAt (by simp))
      (hregb x ((hXmem x).mpr ⟨hx.1, hxB.ge⟩) hTa hx.2.1.1 hx.2.1.2)
  have hrim : ∀ w, Bh (ψ w) = 0 ↔ ‖(w : ℝ²)‖ = 1 := by
    intro w
    rw [← hψrim w]
    exact sub_eq_zero.trans eq_comm
  obtain ⟨ε', hε', hball, Φ, hΦemb, hΦrange, hΦg, hΦrim⟩ :=
    exists_diskChart_of_sideBoundary_trivialization_OED hdim g Bh hg hBh R hR hε hregR hregbR
      hhprop ψ hψ hψr' hrim
  obtain ⟨h0, hσsm, hσemb, hσinj, -, hσrange⟩ := baseChart_of_localRecord_OWF κ σ₀ Wb Mk
    (O' ∩ Pi) ha hb hc hy' hε' (hball.trans hsub) (fun b hb' => hO b (hball hb'))
  set c := OpenPartialHomeomorph.univBall (κ y) ε' with hcdef
  have hιΦ : IsSmoothEmbedding ((𝓡 1).prod (𝓡∂ 2)) IM ∞ (ι ∘ Φ) := hιc Φ hΦemb
  have hΦR : ∀ q, Φ q ∈ R ∧ 0 ≤ Bh (Φ q) := fun q => by
    have h : Φ q ∈ range Φ := mem_range_self q
    rw [hΦrange] at h
    exact ⟨h.1, h.2.2⟩
  refine ⟨σ₀ ∘ c, ι ∘ Φ, (Mk ∩ Pi) ∩ κ ⁻¹' ball (κ y) ε', h0, hσsm, hσemb, hσinj,
    (hMk.inter hPi).inter (isOpen_ball.preimage κ.continuous), ?_, hιΦ, ?_, ?_, ?_⟩
  · rw [hσrange, hB]
    ext w
    simp only [mem_inter_iff, mem_preimage]
    tauto
  · have hrange : range (ι ∘ Φ) = ι '' {x | x ∈ R ∧ g x ∈ ball (κ y) ε' ∧ 0 ≤ Bh x} := by
      rw [← hΦrange, range_comp]
    rw [hrange, hσrange]
    ext p
    constructor
    · rintro ⟨x, ⟨hxR, hxg, hxB⟩, rfl⟩
      have hxX : ι x ∈ X := (hXmem x).mpr ⟨hxR.1, hxB⟩
      have hfB : f (ι x) ∈ B := himg ▸ mem_image_of_mem f hxX
      rw [hB] at hfB
      exact ⟨hxX, ⟨hfB.1, hfB.2, hxR.2.1.2⟩, hxR.2.1.1, hxg⟩
    · rintro ⟨hpX, ⟨hpW, hpO, hpP⟩, hpM, hpκ⟩
      obtain ⟨x, rfl⟩ := hXι hpX
      obtain ⟨hxo, hxB⟩ := (hXmem x).mp hpX
      exact ⟨x, ⟨⟨hxo, ⟨hpM, hpP⟩, hball hpκ⟩, hpκ, hxB⟩, rfl⟩
  · intro x w
    have hq := hΦR (x, w)
    have hqX : ι (Φ (x, w)) ∈ X := (hXmem _).mpr ⟨hq.1.1, hq.2⟩
    change f (ι (Φ (x, w))) = σ₀ (c x)
    rw [hpoint _ hqX hq.1.2.1.1, hΦg x w]
  · intro x w
    rw [← hΦrim x w]
    change T (ι (Φ (x, w))) = a ↔ a - T (ι (Φ (x, w))) = 0
    rw [sub_eq_zero]
    exact eq_comm

omit [T2Space N] [LocallyCompactSpace N] [SecondCountableTopology N] in
/-- The cross-model composition argument `hιc` of `smoothDiskChartAt_of_localRecord_OED` for a
BOUNDARYLESS target model `IM` (composition through the boundaryless middle manifold `N`). For a
target with boundary (e.g. `W.Carrier` with ι the inclusion of `W°`) it is supplied by lane
O-CROSS's half-space tools (`IsSmoothEmbedding.diffeomorph_comp_toHalfSpace_OCX`). -/
theorem isSmoothEmbedding_comp_diskChart_of_boundaryless_OED [FiniteDimensional ℝ EM]
    [IM.Boundaryless] {ι : N → M} (hι : IsSmoothEmbedding I IM ∞ ι)
    (Φ : ℝ¹ × ClosedCell 2 → N) (hΦ : IsSmoothEmbedding ((𝓡 1).prod (𝓡∂ 2)) I ∞ Φ) :
    IsSmoothEmbedding ((𝓡 1).prod (𝓡∂ 2)) IM ∞ (ι ∘ Φ) :=
  hι.comp_of_boundarylessManifold_middle hΦ (by simp)

end Chart

end DifferentialGeometry.Geometry.Collapse
