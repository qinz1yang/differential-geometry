import DifferentialGeometry.Topology.Manifold.SmoothApproximation.Hypersurface.SliceCorestrict
import Mathlib.Analysis.Calculus.ImplicitContDiff
import Mathlib.Analysis.Calculus.Deriv.MeanValue

/-!
# The fibre-root kernel: zero sets of smooth functions with positive slope along a `C^n` tube (W-SUB, K2)

Kernel of the smooth replacement of a compact `C^k` hypersurface (blueprint LFR47, design risk R7,
external review of the finite soul §8, two-sided case). Data: a compact `C^n` manifold `S`
(`1 ≤ n`), a `C^n` tube `Φ : S × ℝ → M` (a `PartialDiffeomorph` whose source contains
`S × (-a, a)`) into a smooth boundaryless manifold `M` of dimension `d + 1`, and a function `f`,
smooth on the open tube piece `Φ (S × (-a, a))`, with positive derivative along every fibre
`τ ↦ f (Φ (s, τ))` and opposite signs at the heights `∓b`, `0 < b < a`.

`exists_fibreRoot_hypersurface`: the zero set `fibreZeroSet Φ a f` of `f` in the tube piece is a
compact embedded slice (`IsEmbeddedSlice I d`) contained in `Φ (S × (-b, b))`; it is the graph
`s ↦ Φ (s, h s)` of a `C^n` root function `h`, and the normal projection
`x ↦ (Φ.symm x).1` is a `C^n` diffeomorphism from it (with `embeddedSliceChartedSpace`) onto `S`.
The root is `C^n` by the implicit function theorem in charts of `S` (Mathlib's
`ContDiffAt.implicitFunction`); the slice charts come from the regular zero set (K1b), and the
inverse is `C^n` into the slice by the corestriction lemma K1a.
-/

set_option autoImplicit false

noncomputable section

open Set Filter Function Manifold
open scoped ContDiff Manifold Topology

namespace DifferentialGeometry.Topology.Manifold.SmoothHypersurface

open DifferentialGeometry.Geometry DifferentialGeometry.Geometry.Topology

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  {ES : Type*} [NormedAddCommGroup ES] [NormedSpace ℝ ES]
  {HS : Type*} [TopologicalSpace HS] {IS : ModelWithCorners ℝ ES HS}
  {S : Type*} [TopologicalSpace S] [ChartedSpace HS S]

/-- The zero set of `f` in the tube piece `Φ (S × (-a, a))`. -/
def fibreZeroSet {n : WithTop ℕ∞} (Φ : PartialDiffeomorph (IS.prod 𝓘(ℝ, ℝ)) I (S × ℝ) M n)
    (a : ℝ) (f : M → ℝ) : Set M :=
  {x | x ∈ Φ '' (univ ×ˢ Ioo (-a) a) ∧ f x = 0}

/-- A real function with positive derivative on `(-a, a)` that is negative at `-b` and positive at
`b` (`0 < b < a`) has exactly one zero in `(-a, a)`, and it lies in `(-b, b)`. -/
theorem existsUnique_root_of_deriv_pos {F : ℝ → ℝ} {a b : ℝ} (hb : 0 < b) (hba : b < a)
    (hderiv : ∀ t ∈ Ioo (-a) a, 0 < deriv F t) (hneg : F (-b) < 0) (hpos : 0 < F b) :
    ∃ t ∈ Ioo (-b) b, F t = 0 ∧ ∀ t' ∈ Ioo (-a) a, F t' = 0 → t' = t := by
  have hcont : ContinuousOn F (Ioo (-a) a) := fun t ht =>
    (differentiableAt_of_deriv_ne_zero (hderiv t ht).ne').continuousAt.continuousWithinAt
  have hmono : StrictMonoOn F (Ioo (-a) a) :=
    strictMonoOn_of_deriv_pos (convex_Ioo _ _) hcont (by rwa [interior_Ioo])
  have hsub : Icc (-b) b ⊆ Ioo (-a) a := Icc_subset_Ioo (by linarith) hba
  obtain ⟨t, ht, hFt⟩ := intermediate_value_Ioo (by linarith) (hcont.mono hsub) ⟨hneg, hpos⟩
  have hta : t ∈ Ioo (-a) a := hsub (Ioo_subset_Icc_self ht)
  exact ⟨t, ht, hFt, fun t' ht' hF' => hmono.injOn ht' hta (hF'.trans hFt.symm)⟩

/-- Regularity along a positive-slope fibre: if `τ ↦ f (Φ (s, τ))` has nonzero derivative at `t`,
`Φ` is differentiable at `(s, t)` and `f` at `Φ (s, t)`, then `mfderiv f (Φ (s, t)) ≠ 0`. -/
theorem mfderiv_ne_zero_of_deriv_fibre_ne_zero {Ψ : S × ℝ → M} {f : M → ℝ}
    {s : S} {t : ℝ} (hΨ : MDifferentiableAt (IS.prod 𝓘(ℝ, ℝ)) I Ψ (s, t))
    (hf : MDifferentiableAt I 𝓘(ℝ, ℝ) f (Ψ (s, t)))
    (hderiv : deriv (fun τ => f (Ψ (s, τ))) t ≠ 0) :
    mfderiv I 𝓘(ℝ, ℝ) f (Ψ (s, t)) ≠ 0 := by
  intro h0
  have hf0 : HasMFDerivAt I 𝓘(ℝ, ℝ) f (Ψ (s, t)) 0 := by
    have := hf.hasMFDerivAt
    rwa [h0] at this
  have hι : MDifferentiableAt 𝓘(ℝ, ℝ) (IS.prod 𝓘(ℝ, ℝ)) (fun τ : ℝ => (s, τ)) t :=
    mdifferentiableAt_const.prodMk mdifferentiableAt_id
  have hcomp := hf0.comp t (hΨ.hasMFDerivAt.comp t hι.hasMFDerivAt)
  rw [ContinuousLinearMap.zero_comp] at hcomp
  have hF : HasFDerivAt (fun τ => f (Ψ (s, τ))) (0 : ℝ →L[ℝ] ℝ) t :=
    hasMFDerivAt_iff_hasFDerivAt.mp hcomp
  exact hderiv hF.hasDerivAt.deriv

/-- **Implicit function theorem along the fibres.** Let `G : S × ℝ → ℝ` be `C^n` (`1 ≤ n`) on
`S × (-a, a)` with positive derivative along every fibre, and let `h` pick, for every `s`, the unique
zero of `G (s, ·)` in `(-a, a)`. Then `h` is `C^n`. -/
theorem contMDiff_root_of_deriv_pos [CompleteSpace ES] [IS.Boundaryless] {n : ℕ} (hn : 1 ≤ n)
    {G : S × ℝ → ℝ} {a : ℝ}
    (hG : ContMDiffOn (IS.prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, ℝ) n G (univ ×ˢ Ioo (-a) a))
    (hderiv : ∀ s, ∀ t ∈ Ioo (-a) a, 0 < deriv (fun τ => G (s, τ)) t)
    {h : S → ℝ} (hmem : ∀ s, h s ∈ Ioo (-a) a) (hroot : ∀ s, G (s, h s) = 0)
    (huniq : ∀ s, ∀ t ∈ Ioo (-a) a, G (s, t) = 0 → t = h s) :
    ContMDiff IS 𝓘(ℝ, ℝ) n h := by
  intro s₀
  set φ := extChartAt IS s₀ with hφ
  set u₀ := φ s₀ with hu₀
  set t₀ := h s₀ with ht₀
  let F : ES × ℝ → ℝ := fun p => G (φ.symm p.1, p.2)
  have hGat : ContMDiffAt (IS.prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, ℝ) n G (s₀, t₀) :=
    hG.contMDiffAt ((isOpen_univ.prod isOpen_Ioo).mem_nhds ⟨mem_univ _, hmem s₀⟩)
  have hF : ContDiffAt ℝ n F (u₀, t₀) := by
    have h2 := (contMDiffAt_iff.mp hGat).2
    simp only [extChartAt_prod, extChartAt_model_space_eq_id, PartialEquiv.prod_symm,
      PartialEquiv.refl_symm, ModelWithCorners.range_eq_univ, contDiffWithinAt_univ] at h2
    exact h2
  have hn0 : ((n : ℕ∞) : WithTop ℕ∞) ≠ 0 := by
    have : n ≠ 0 := by omega
    exact_mod_cast this
  have hsymm : φ.symm u₀ = s₀ := extChartAt_to_inv s₀
  have hFfib : (fun τ => F (u₀, τ)) = fun τ => G (s₀, τ) := by
    funext τ
    simp only [F, hsymm]
  have hDF : HasFDerivAt F (fderiv ℝ F (u₀, t₀)) (u₀, t₀) :=
    (hF.differentiableAt (by exact_mod_cast hn0)).hasFDerivAt
  have hγ : HasDerivAt (fun τ : ℝ => (u₀, τ)) ((0 : ES), (1 : ℝ)) t₀ :=
    (hasDerivAt_const t₀ u₀).prodMk (hasDerivAt_id t₀)
  have hfib : HasDerivAt (fun τ => G (s₀, τ)) (fderiv ℝ F (u₀, t₀) ((0 : ES), (1 : ℝ))) t₀ := by
    rw [← hFfib]
    exact hDF.comp_hasDerivAt t₀ hγ
  set c := fderiv ℝ F (u₀, t₀) ((0 : ES), (1 : ℝ)) with hc
  have hcpos : 0 < c := by
    have := hderiv s₀ t₀ (hmem s₀)
    rwa [hfib.deriv] at this
  have hinv : (fderiv ℝ F (u₀, t₀) ∘L ContinuousLinearMap.inr ℝ ES ℝ).IsInvertible := by
    refine ⟨ContinuousLinearEquiv.unitsEquivAut ℝ (Units.mk0 c hcpos.ne'), ?_⟩
    ext
    simp [hc]
  set ψ := hF.implicitFunction hn0 hinv with hψ
  have hψ0 : ψ u₀ = t₀ := hF.implicitFunction_apply_self hn0 hinv
  have hψeq := hF.eventually_apply_implicitFunction hn0 hinv
  have hψC : ContDiffAt ℝ n ψ u₀ := hF.contDiffAt_implicitFunction hn0 hinv
  have hF0 : F (u₀, t₀) = 0 := by
    simp only [F, hsymm]
    exact hroot s₀
  have hψmem : ∀ᶠ u in 𝓝 u₀, ψ u ∈ Ioo (-a) a :=
    hψC.continuousAt.preimage_mem_nhds (isOpen_Ioo.mem_nhds (by rw [hψ0]; exact hmem s₀))
  have hφc : Tendsto φ (𝓝 s₀) (𝓝 u₀) := continuousAt_extChartAt s₀
  have heq : h =ᶠ[𝓝 s₀] ψ ∘ φ := by
    filter_upwards [extChartAt_source_mem_nhds (I := IS) s₀, hφc.eventually hψeq,
      hφc.eventually hψmem] with s hs h1 h2
    have hss : φ.symm (φ s) = s := φ.left_inv hs
    have hzero : G (s, ψ (φ s)) = 0 := by
      have h1' : F (φ s, ψ (φ s)) = 0 := by rw [h1]; exact hF0
      simpa only [F, hss] using h1'
    exact (huniq s _ h2 hzero).symm
  have hcomp : ContMDiffAt IS 𝓘(ℝ, ℝ) n (ψ ∘ φ) s₀ :=
    hψC.contMDiffAt.comp s₀ contMDiffAt_extChartAt
  exact hcomp.congr_of_eventuallyEq heq

/-- **K2: the fibre-root kernel.** A smooth function on the tube piece `Φ (S × (-a, a))` with positive
derivative along the fibres and opposite signs at the heights `∓b` has a compact zero set which is a
smooth embedded slice, a `C^n` graph over `S`, with `C^n` normal projection in both directions. -/
theorem exists_fibreRoot_hypersurface [FiniteDimensional ℝ E] [I.Boundaryless] [IsManifold I ∞ M]
    [CompleteSpace ES] [IS.Boundaryless] [CompactSpace S] {d : ℕ}
    (hdim : Module.finrank ℝ E = d + 1) {n : ℕ} (hn : 1 ≤ n)
    (Φ : PartialDiffeomorph (IS.prod 𝓘(ℝ, ℝ)) I (S × ℝ) M n) {a b : ℝ} (hb : 0 < b)
    (hba : b < a) (hsrc : univ ×ˢ Ioo (-a) a ⊆ Φ.source) {f : M → ℝ}
    (hf : ContMDiffOn I 𝓘(ℝ, ℝ) ∞ f (Φ '' (univ ×ˢ Ioo (-a) a)))
    (hneg : ∀ s, f (Φ (s, -b)) < 0) (hpos : ∀ s, 0 < f (Φ (s, b)))
    (hderiv : ∀ s, ∀ t ∈ Ioo (-a) a, 0 < deriv (fun τ => f (Φ (s, τ))) t) :
    ∃ hŜ : IsEmbeddedSlice I d (fibreZeroSet Φ a f), IsCompact (fibreZeroSet Φ a f) ∧
      fibreZeroSet Φ a f ⊆ Φ '' (univ ×ˢ Ioo (-b) b) ∧
      let _ := embeddedSliceChartedSpace hŜ
      ∃ β : Diffeomorph 𝓘(ℝ, Fin d → ℝ) IS (fibreZeroSet Φ a f) S n,
        (∀ x, β x = (Φ.symm x).1) ∧
        ∃ h : S → ℝ, ContMDiff IS 𝓘(ℝ, ℝ) n h ∧ (∀ s, h s ∈ Ioo (-b) b) ∧
          ∀ s, (β.symm s : M) = Φ (s, h s) := by
  classical
  set T := Φ '' (univ ×ˢ Ioo (-a) a) with hT
  have hTopen : IsOpen T :=
    Φ.toOpenPartialHomeomorph.isOpen_image_of_subset_source (isOpen_univ.prod isOpen_Ioo) hsrc
  have hn0 : (n : WithTop ℕ∞) ≠ 0 := by
    have : n ≠ 0 := by omega
    exact_mod_cast this
  have hnle : (n : WithTop ℕ∞) ≤ ∞ := by exact_mod_cast le_top
  have hTtarget : T ⊆ Φ.target := by
    rintro _ ⟨p, hp, rfl⟩
    exact Φ.map_source (hsrc hp)
  -- the root function
  choose h hhb hhroot hhuniq using fun s =>
    existsUnique_root_of_deriv_pos hb hba (hderiv s) (hneg s) (hpos s)
  have hba' : Ioo (-b) b ⊆ Ioo (-a) a := Ioo_subset_Ioo (by linarith) hba.le
  have hha : ∀ s, h s ∈ Ioo (-a) a := fun s => hba' (hhb s)
  have hmemsrc : ∀ s, ∀ t ∈ Ioo (-a) a, (s, t) ∈ Φ.source := fun s t ht =>
    hsrc ⟨mem_univ _, ht⟩
  have hG : ContMDiffOn (IS.prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, ℝ) n (fun p => f (Φ p)) (univ ×ˢ Ioo (-a) a) :=
    (hf.of_le hnle).comp (Φ.contMDiffOn_toFun.mono hsrc) (fun p hp => mem_image_of_mem _ hp)
  have hh : ContMDiff IS 𝓘(ℝ, ℝ) n h :=
    contMDiff_root_of_deriv_pos hn hG hderiv hha hhroot hhuniq
  -- the zero set is the graph
  have hZ : ∀ x, x ∈ fibreZeroSet Φ a f ↔ ∃ s, Φ (s, h s) = x := by
    intro x
    constructor
    · rintro ⟨⟨⟨s, t⟩, ⟨-, ht⟩, rfl⟩, hfx⟩
      exact ⟨s, by rw [hhuniq s t ht hfx]⟩
    · rintro ⟨s, rfl⟩
      exact ⟨mem_image_of_mem _ ⟨mem_univ _, hha s⟩, hhroot s⟩
  have hgraph : ContMDiff IS I n (fun s => Φ (s, h s)) :=
    Φ.contMDiffOn_toFun.comp_contMDiff (contMDiff_id.prodMk hh) (fun s => hmemsrc s _ (hha s))
  have hrange : fibreZeroSet Φ a f = range (fun s => Φ (s, h s)) := by
    ext x
    rw [hZ]
    rfl
  -- regularity and the slice structure
  have hreg : ∀ s, mfderiv I 𝓘(ℝ, ℝ) f (Φ (s, h s)) ≠ 0 := by
    intro s
    have hsrc' := hmemsrc s _ (hha s)
    have hΦd : MDifferentiableAt (IS.prod 𝓘(ℝ, ℝ)) I Φ (s, h s) :=
      (Φ.contMDiffOn_toFun.contMDiffAt (Φ.open_source.mem_nhds hsrc')).mdifferentiableAt hn0
    have hfd : MDifferentiableAt I 𝓘(ℝ, ℝ) f (Φ (s, h s)) :=
      (hf.contMDiffAt (hTopen.mem_nhds (mem_image_of_mem _ ⟨mem_univ _, hha s⟩))).mdifferentiableAt
        (by simp)
    exact mfderiv_ne_zero_of_deriv_fibre_ne_zero hΦd hfd (hderiv s _ (hha s)).ne'
  have hŜ : IsEmbeddedSlice I d (fibreZeroSet Φ a f) := by
    refine isEmbeddedSlice_of_forall_regular_zero hdim (fun x hx => ?_)
    obtain ⟨s, rfl⟩ := (hZ x).mp hx
    exact ⟨T, hTopen, hx.1, f, hf, fun y hy => ⟨fun hy' => hy'.2, fun hy' => ⟨hy, hy'⟩⟩, hreg s⟩
  refine ⟨hŜ, ?_, ?_, ?_⟩
  · rw [hrange]
    exact isCompact_range hgraph.continuous
  · intro x hx
    obtain ⟨s, rfl⟩ := (hZ x).mp hx
    exact mem_image_of_mem _ ⟨mem_univ _, hhb s⟩
  intro _
  have hmem : ∀ s, Φ (s, h s) ∈ fibreZeroSet Φ a f := fun s => (hZ _).mpr ⟨s, rfl⟩
  have hval : ContMDiff 𝓘(ℝ, Fin d → ℝ) I ∞ (Subtype.val : fibreZeroSet Φ a f → M) :=
    embeddedSlice_inclusion_contMDiff hŜ
  have hfwd : ContMDiff 𝓘(ℝ, Fin d → ℝ) (IS.prod 𝓘(ℝ, ℝ)) n
      (fun x : fibreZeroSet Φ a f => Φ.symm x) :=
    Φ.contMDiffOn_invFun.comp_contMDiff (hval.of_le hnle) (fun x => hTtarget x.2.1)
  have hinv : ContMDiff IS 𝓘(ℝ, Fin d → ℝ) n
      (fun s => (⟨Φ (s, h s), hmem s⟩ : fibreZeroSet Φ a f)) :=
    embeddedSlice_contMDiff_corestrict hŜ (n := (n : ℕ∞)) _ hgraph hmem
  have hleft : ∀ x : fibreZeroSet Φ a f,
      (⟨Φ (((Φ.symm x).1), h ((Φ.symm x).1)), hmem _⟩ : fibreZeroSet Φ a f) = x := by
    rintro ⟨x, ⟨⟨s, t⟩, ⟨-, ht⟩, rfl⟩, hfx⟩
    apply Subtype.ext
    have hl : Φ.symm.toPartialEquiv (Φ.toPartialEquiv (s, t)) = (s, t) :=
      Φ.left_inv (hmemsrc s t ht)
    have ht' := hhuniq s t ht hfx
    change Φ ((Φ.symm (Φ (s, t))).1, h (Φ.symm (Φ (s, t))).1) = Φ (s, t)
    simp only [hl, ← ht']
  have hright : ∀ s, (Φ.symm (Φ (s, h s))).1 = s := fun s => by
    have hl : Φ.symm.toPartialEquiv (Φ.toPartialEquiv (s, h s)) = (s, h s) :=
      Φ.left_inv (hmemsrc s _ (hha s))
    change (Φ.symm.toPartialEquiv (Φ.toPartialEquiv (s, h s))).1 = s
    rw [hl]
  let β : Diffeomorph 𝓘(ℝ, Fin d → ℝ) IS (fibreZeroSet Φ a f) S n :=
    { toFun := fun x => (Φ.symm x).1
      invFun := fun s => ⟨Φ (s, h s), hmem s⟩
      left_inv := hleft
      right_inv := hright
      contMDiff_toFun := contMDiff_fst.comp hfwd
      contMDiff_invFun := hinv }
  exact ⟨β, fun x => rfl, h, hh, hhb, fun s => rfl⟩

end DifferentialGeometry.Topology.Manifold.SmoothHypersurface
