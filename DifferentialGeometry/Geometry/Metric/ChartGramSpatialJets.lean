import DifferentialGeometry.Geometry.Metric.ChartGramJointSmoothness
import DifferentialGeometry.Geometry.Operator.HessianTrace
import DifferentialGeometry.Geometry.Connection.LeviCivita.LeviCivitaChartLocal

/-! # Joint `(t, x)`-continuity of the spatial Fréchet jets of the chart-Gram entry

For a metric family `g_DT : ℝ → SmoothRiemannianMetric I M` whose bundle inner-product
`Hom`-section `(t, x) ↦ (g_DT t).inner x` is jointly `C∞` on `Icc 0 T ×ˢ univ`
(`hsmooth`), every spatial Fréchet jet of order `k` of the chart-pulled-back Gram entry
`y ↦ chartGramOnE (g_DT t) α i j y` is jointly `(t, x)`-continuous, up to and including the
initial time `t = 0`, on `Icc 0 T ×ˢ chartLeviCivitaGoodSet α`.

This dissolves the "spatial-jet wall": the earlier readout only delivered the `k = 0` jet
(the value itself).  The genuinely new ingredient is the closed-time **jet bridge**
`continuousOn_joint_spatial_iteratedFDeriv`: for a scalar `F : ℝ × E → ℝ` that is jointly
`C∞` on `J ×ˢ U` (`J` uniquely differentiable, e.g. `Icc 0 T`; `U` open), the partial
spatial iterated Fréchet derivative `(t, y) ↦ iteratedFDeriv ℝ k (fun y' => F (t, y')) y`
is jointly continuous on `J ×ˢ U`.  Its proof reduces the spatial jet of the time-frozen
slice to the joint *within*-iterated derivative of `F` post-composed with the (`t`-shifted)
spatial inclusion, via a translation `F (· + (t, 0))` so that the spatial inclusion becomes
the genuinely *linear* `ContinuousLinearMap.inr ℝ ℝ E` and
`ContinuousLinearMap.iteratedFDerivWithin_comp_right` applies on the (open) slice base set.

The chart-Gram entry is fed through this bridge after transporting its joint smoothness
from the manifold form to the chart-target-interior Euclidean form
(`chartGramOnE_joint_contDiffOn_of_manifold_closed`), and the result is pulled back to the
manifold good set along the chart map `q ↦ (q.1, extChartAt I α q.2)`. -/

open Set Function

namespace DifferentialGeometry
namespace Integral
namespace Measure

open Bundle
open scoped Manifold ContDiff Pointwise
open DifferentialGeometry.Integral.DivergenceTheorem
open DifferentialGeometry.Integral.Connection

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [NeZero (Module.finrank ℝ E)]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M] [T2Space M]
  [SigmaCompactSpace M]

section JetBridge

/-- A translate of a uniquely-differentiable subset of `ℝ` is again uniquely
differentiable: if `UniqueDiffOn ℝ sI` then `UniqueDiffOn ℝ ((· + t) ⁻¹' sI)`. -/
private lemma uniqueDiffOn_preimage_add_right {sI : Set ℝ} (hsI : UniqueDiffOn ℝ sI) (t : ℝ) :
    UniqueDiffOn ℝ ((fun u : ℝ => u + t) ⁻¹' sI) := by
  have hset : (fun u : ℝ => u + t) ⁻¹' sI = (fun u : ℝ => u - t) '' sI := by
    ext u
    simp only [Set.mem_preimage, Set.mem_image]
    constructor
    · intro h; exact ⟨u + t, h, by ring⟩
    · rintro ⟨v, hv, rfl⟩; simpa using hv
  rw [hset]
  refine hsI.image (fun x _ => ((hasFDerivAt_id x).sub_const t).hasFDerivWithinAt)
    (fun _ _ => ?_)
  exact (ContinuousLinearEquiv.refl ℝ ℝ).surjective.denseRange

/-- **Slice ↔ joint within-iterated-derivative identity (the closed-time jet bridge core).**

On the open spatial slice through `(t, y₀) ∈ J ×ˢ U` (with `U` open and `J` uniquely
differentiable), the spatial iterated Fréchet derivative of the time-frozen slice
`y ↦ F (t, y)` equals the joint *within*-iterated derivative `iteratedFDerivWithin ℝ k F
(J ×ˢ U)` post-composed with the `k`-fold spatial inclusion
`fun _ => ContinuousLinearMap.inr ℝ ℝ E`.

The spatial inclusion `y ↦ (t, y)` is affine, not linear, so the linear comp-right lemma is
not directly applicable.  We pass to the translated function `Fshift := F (· + (t, 0))`,
whose iterated within-derivative on the translated set `s'` recovers that of `F` at `(t, y₀)`
by `iteratedFDerivWithin_comp_add_right`, and for which the spatial inclusion is the genuinely
linear `ContinuousLinearMap.inr ℝ ℝ E` with `inr ⁻¹' s' = U` (since `t ∈ J`). -/
private lemma iteratedFDeriv_slice_eq_within_comp_inr {J : Set ℝ} {U : Set E}
    (hJ : UniqueDiffOn ℝ J) (hU : IsOpen U) {F : ℝ × E → ℝ}
    (hF : ContDiffOn ℝ ∞ F (J ×ˢ U)) (k : ℕ) {t : ℝ} {y₀ : E}
    (ht : t ∈ J) (hy₀ : y₀ ∈ U) :
    iteratedFDeriv ℝ k (fun y : E => F (t, y)) y₀
      = (iteratedFDerivWithin ℝ k F (J ×ˢ U) (t, y₀)).compContinuousLinearMap
          (fun _ => ContinuousLinearMap.inr ℝ ℝ E) := by
  classical
  set c : ℝ × E := (t, (0 : E)) with hc_def
  set Fshift : ℝ × E → ℝ := fun q => F (q + c) with hFshift_def
  set s' : Set (ℝ × E) := (fun q : ℝ × E => q + c) ⁻¹' (J ×ˢ U) with hs'_def
  set g : E →L[ℝ] ℝ × E := ContinuousLinearMap.inr ℝ ℝ E with hg_def
  -- The slice equals `Fshift ∘ g`.
  have hslice_eq : (fun y : E => F (t, y)) = Fshift ∘ g := by
    funext y
    simp only [Fshift, Function.comp_apply, hg_def, ContinuousLinearMap.inr_apply, hc_def]
    congr 1
    ext <;> simp
  -- `s'` is the product of a translate of `J` with `U`.
  have hs'_prod : s' = ((fun u : ℝ => u + t) ⁻¹' J) ×ˢ U := by
    ext q
    simp only [hs'_def, hc_def, Set.mem_preimage, Set.mem_prod, Prod.fst_add, Prod.snd_add,
      add_zero]
  -- `s'` is uniquely differentiable and open in its spatial factor.
  have hs'_du : UniqueDiffOn ℝ s' := by
    rw [hs'_prod]
    exact (uniqueDiffOn_preimage_add_right hJ t).prod hU.uniqueDiffOn
  -- `Fshift` is jointly `C∞` on `s'`.
  have hFshift : ContDiffOn ℝ ∞ Fshift s' := by
    have hadd : ContDiff ℝ ∞ (fun q : ℝ × E => q + c) := contDiff_id.add contDiff_const
    have hmaps : Set.MapsTo (fun q : ℝ × E => q + c) s' (J ×ˢ U) := fun q hq => hq
    exact hF.comp hadd.contDiffOn hmaps
  -- The preimage of `s'` under `g = inr` is `U` (uses `t ∈ J`).
  have hgpre : g ⁻¹' s' = U := by
    have hcoe : (⇑g : E → ℝ × E) = fun y : E => (0, y) := by
      funext y; simp [hg_def, ContinuousLinearMap.inr_apply]
    rw [hs'_prod, hcoe]
    ext y
    simp only [Set.mem_preimage, Set.mem_prod]
    constructor
    · rintro ⟨_, hy⟩; exact hy
    · intro hy; refine ⟨?_, hy⟩; simpa using ht
  -- Linear comp-right on the slice through `g`.
  have hg_mem : g y₀ ∈ s' := by
    rw [← Set.mem_preimage, hgpre]; exact hy₀
  have hcomp := ContinuousLinearMap.iteratedFDerivWithin_comp_right (𝕜 := ℝ)
    (f := Fshift) g hFshift hs'_du (by rw [hgpre]; exact hU.uniqueDiffOn)
    (x := y₀) hg_mem (i := k) (by exact_mod_cast le_top)
  -- Translate the within-iterated derivative of `Fshift` at `(0, y₀)` to `F` at `(t, y₀)`.
  have hg_y₀ : g y₀ = (0, y₀) := by simp [hg_def, ContinuousLinearMap.inr_apply]
  have htrans : iteratedFDerivWithin ℝ k Fshift s' (0, y₀)
      = iteratedFDerivWithin ℝ k F (J ×ˢ U) (t, y₀) := by
    have hshift := iteratedFDerivWithin_comp_add_right (𝕜 := ℝ) (f := F) (s := s') k c (0, y₀)
    rw [show Fshift = fun q : ℝ × E => F (q + c) from hFshift_def, hshift]
    have hset : c +ᵥ s' = J ×ˢ U := by
      rw [hs'_def]
      ext q
      simp only [Set.mem_vadd_set, Set.mem_preimage]
      constructor
      · rintro ⟨w, hw, rfl⟩; simpa [vadd_eq_add, add_comm, add_assoc] using hw
      · intro hq; exact ⟨-c +ᵥ q, by simpa [vadd_eq_add] using hq, by simp⟩
    rw [hset]
    congr 1
    simp [hc_def]
  -- Assemble.
  rw [hslice_eq]
  have hslice_open : iteratedFDerivWithin ℝ k (Fshift ∘ g) (g ⁻¹' s') y₀
      = iteratedFDeriv ℝ k (Fshift ∘ g) y₀ := by
    rw [hgpre]
    exact iteratedFDerivWithin_of_isOpen (𝕜 := ℝ) (f := Fshift ∘ g) k hU hy₀
  rw [← hslice_open, hcomp, hg_y₀, htrans]

/-- **The closed-time spatial jet bridge.**

For a scalar `F : ℝ × E → ℝ` jointly `C∞` on `J ×ˢ U` (with `J` uniquely differentiable —
e.g. `Set.Icc 0 T` anchored at the initial time `0` — and `U` open), the partial spatial
iterated Fréchet derivative `(t, y) ↦ iteratedFDeriv ℝ k (fun y' => F (t, y')) y` is jointly
`(t, y)`-continuous on `J ×ˢ U`, for every jet order `k`.

This is the general engine that dissolves the spatial-jet wall: the joint within-iterated
derivative `iteratedFDerivWithin ℝ k F (J ×ˢ U)` is `ContinuousOn` by
`ContinuousOn.continuousOn_iteratedFDerivWithin`, and post-composition with the fixed spatial
inclusion `fun _ => inr` (a continuous linear map on `ContinuousMultilinearMap`) is
continuous; the slice identity `iteratedFDeriv_slice_eq_within_comp_inr` makes the spatial
jet of the time-frozen slice agree with this composite on `J ×ˢ U`. -/
theorem continuousOn_joint_spatial_iteratedFDeriv {J : Set ℝ} {U : Set E}
    (hJ : UniqueDiffOn ℝ J) (hU : IsOpen U) {F : ℝ × E → ℝ}
    (hF : ContDiffOn ℝ ∞ F (J ×ˢ U)) (k : ℕ) :
    ContinuousOn
      (fun q : ℝ × E => iteratedFDeriv ℝ k (fun y : E => F (q.1, y)) q.2)
      (J ×ˢ U) := by
  classical
  have hprod_du : UniqueDiffOn ℝ (J ×ˢ U) := hJ.prod hU.uniqueDiffOn
  have hwithin : ContinuousOn (fun q : ℝ × E => iteratedFDerivWithin ℝ k F (J ×ˢ U) q)
      (J ×ˢ U) :=
    ContinuousOn.continuousOn_iteratedFDerivWithin hF hprod_du (by exact_mod_cast le_top)
  have hpost : Continuous
      (fun L : ContinuousMultilinearMap ℝ (fun _ : Fin k => ℝ × E) ℝ =>
        L.compContinuousLinearMap (fun _ : Fin k => ContinuousLinearMap.inr ℝ ℝ E)) :=
    (ContinuousMultilinearMap.compContinuousLinearMapL
      (fun _ : Fin k => ContinuousLinearMap.inr ℝ ℝ E)).continuous
  refine (hpost.comp_continuousOn hwithin).congr ?_
  intro q hq
  obtain ⟨ht, hy⟩ := hq
  simp only [Function.comp_apply]
  exact iteratedFDeriv_slice_eq_within_comp_inr (E := E) hJ hU hF k ht hy

end JetBridge

section ManifoldTransfer

/-- On `interior (extChartAt I α).target`, the chart inverse image lies in the
trivialization base set at `α`. -/
private lemma symm_mem_baseSet_of_mem_interior {α : M} {y : E}
    (hy : y ∈ interior (extChartAt I α).target) :
    (extChartAt I α).symm y ∈ (trivializationAt E (TangentSpace I) α).baseSet := by
  have hy_tgt : y ∈ (extChartAt I α).target := interior_subset hy
  have hsource : (extChartAt I α).symm y ∈ (extChartAt I α).source :=
    (extChartAt I α).map_target hy_tgt
  rw [extChartAt_source_eq_chartAt_source (I := I)] at hsource
  rw [trivializationAt_baseSet_eq_chartAt_source]
  exact hsource

/-- **Transfer of the chart-Gram joint smoothness from the manifold form to the
chart-target-interior Euclidean form.**

From the joint `(t, x)`-`C∞` smoothness of the chart-pulled-back Gram entry on
`Icc 0 T ×ˢ (chartAt H α).source` (the manifold form), the Euclidean chart-Gram entry
`(t, y) ↦ chartGramOnE (g_DT t) α i j y` is jointly `C∞` on
`Icc 0 T ×ˢ interior (extChartAt I α).target`.  The transfer composes with the chart
inverse `(t, y) ↦ (t, (extChartAt I α).symm y)`, which is smooth and maps the chart-target
interior into the chart source, and recovers the value through the chart round-trip
`(extChartAt I α).right_inv`. -/
private lemma chartGramOnE_joint_contDiffOn_of_manifold_closed
    (g_DT : ℝ → SmoothRiemannianMetric I M) (α : M) {T : ℝ}
    (h_gDT : ∀ (i j : Fin (Module.finrank ℝ E)),
      ContMDiffOn (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) ∞
        (fun q : ℝ × M =>
          chartGramOnE (I := I) (g_DT q.1) α i j (extChartAt I α q.2))
        (Set.Icc (0 : ℝ) T ×ˢ (chartAt H α).source))
    (i j : Fin (Module.finrank ℝ E)) :
    ContDiffOn ℝ ∞
      (fun p : ℝ × E => chartGramOnE (I := I) (g_DT p.1) α i j p.2)
      (Set.Icc (0 : ℝ) T ×ˢ interior (extChartAt I α).target) := by
  classical
  set Ψ : ℝ × E → ℝ × M := fun p => (p.1, (extChartAt I α).symm p.2) with hΨ
  have hΨ_smooth : ContMDiffOn ((𝓘(ℝ, ℝ)).prod 𝓘(ℝ, E)) ((𝓘(ℝ, ℝ)).prod I) ∞ Ψ
      (Set.Icc (0 : ℝ) T ×ˢ interior (extChartAt I α).target) := by
    refine ContMDiffOn.prodMk ?_ ?_
    · exact contMDiffOn_fst
    · have hsymm : ContMDiffOn 𝓘(ℝ, E) I ∞ (extChartAt I α).symm
          (extChartAt I α).target := contMDiffOn_extChartAt_symm (I := I) α
      refine hsymm.comp contMDiffOn_snd ?_
      intro p hp; exact Set.mem_preimage.mpr (interior_subset hp.2)
  have hmaps : Set.MapsTo Ψ
      (Set.Icc (0 : ℝ) T ×ˢ interior (extChartAt I α).target)
      (Set.Icc (0 : ℝ) T ×ˢ (chartAt H α).source) := by
    intro p hp
    refine ⟨hp.1, ?_⟩
    have hbase := symm_mem_baseSet_of_mem_interior (I := I) (α := α) hp.2
    rwa [trivializationAt_baseSet_eq_chartAt_source] at hbase
  have hcomp : ContMDiffOn ((𝓘(ℝ, ℝ)).prod 𝓘(ℝ, E)) 𝓘(ℝ, ℝ) ∞
      ((fun q : ℝ × M =>
          chartGramOnE (I := I) (g_DT q.1) α i j (extChartAt I α q.2)) ∘ Ψ)
      (Set.Icc (0 : ℝ) T ×ˢ interior (extChartAt I α).target) :=
    (h_gDT i j).comp hΨ_smooth hmaps
  have hcongr : Set.EqOn
      (fun p : ℝ × E => chartGramOnE (I := I) (g_DT p.1) α i j p.2)
      ((fun q : ℝ × M =>
          chartGramOnE (I := I) (g_DT q.1) α i j (extChartAt I α q.2)) ∘ Ψ)
      (Set.Icc (0 : ℝ) T ×ˢ interior (extChartAt I α).target) := by
    intro p hp
    have hy_tgt : p.2 ∈ (extChartAt I α).target := interior_subset hp.2
    simp only [Function.comp_apply, hΨ]
    rw [(extChartAt I α).right_inv hy_tgt]
  have hcomp' : ContMDiffOn ((𝓘(ℝ, ℝ)).prod 𝓘(ℝ, E)) 𝓘(ℝ, ℝ) ∞
      (fun p : ℝ × E => chartGramOnE (I := I) (g_DT p.1) α i j p.2)
      (Set.Icc (0 : ℝ) T ×ˢ interior (extChartAt I α).target) :=
    hcomp.congr hcongr
  rw [← contMDiffOn_iff_contDiffOn, modelWithCornersSelf_prod, ← chartedSpaceSelf_prod]
  exact hcomp'

end ManifoldTransfer

set_option linter.unusedVariables false in
/-- **Joint `(t, x)`-continuity of the spatial Fréchet jets of the chart-Gram entry, up to
and including the initial time `0`.**

For a metric family `g_DT` whose bundle inner-product `Hom`-section is jointly `C∞` on
`Icc 0 T ×ˢ univ` (`hsmooth`), every spatial jet `iteratedFDeriv ℝ k` of the chart-Gram
entry `chartGramOnE (g_DT t) α i j` (read at `extChartAt I α x`) is jointly `(t, x)`
continuous on `Icc 0 T ×ˢ chartLeviCivitaGoodSet α`, including the `t = 0` boundary.

This dissolves the spatial-jet wall (the earlier readout delivered only the `k = 0` jet).
The route is: transport `hsmooth` to the manifold chart-Gram joint smoothness on the chart
source (`chartGramOnE_jointContMDiffOn_of_innerSmooth`); transfer it to the
chart-target-interior Euclidean form (`chartGramOnE_joint_contDiffOn_of_manifold_closed`);
feed it through the closed-time spatial jet bridge
(`continuousOn_joint_spatial_iteratedFDeriv`); and pull back along the chart map
`q ↦ (q.1, extChartAt I α q.2)`, which is continuous on the good set and maps it into the
chart-target interior. -/
theorem chartGramOnE_jets_jointContinuousOn_of_innerSmooth
    (α : M) (i j : Fin (Module.finrank ℝ E)) (k : ℕ) (hk : k ≤ 2)
    (g_DT : ℝ → SmoothRiemannianMetric I M) (T : ℝ) (hT : 0 < T)
    (hsmooth : ContMDiffOn (𝓘(ℝ, ℝ).prod I) (I.prod 𝓘(ℝ, E →L[ℝ] E →L[ℝ] ℝ)) ∞
      (fun q : ℝ × M => TotalSpace.mk' (E →L[ℝ] E →L[ℝ] ℝ)
        (E := fun y : M => TangentSpace I y →L[ℝ] TangentSpace I y →L[ℝ] ℝ)
        q.2 ((g_DT q.1).inner q.2))
      (Set.Icc 0 T ×ˢ Set.univ)) :
    ContinuousOn
      (fun q : ℝ × M => iteratedFDeriv ℝ k
        (Integral.DivergenceTheorem.chartGramOnE (I := I) (g_DT q.1) α i j)
        (extChartAt I α q.2))
      (Set.Icc 0 T ×ˢ chartLeviCivitaGoodSet (I := I) α) := by
  classical
  -- Step 1: the manifold chart-Gram entries are jointly `C∞` on the chart source.
  have hsmooth' : ContMDiffOn (𝓘(ℝ, ℝ).prod I) (I.prod 𝓘(ℝ, E →L[ℝ] E →L[ℝ] ℝ)) ∞
      (fun q : ℝ × M => TotalSpace.mk' (E →L[ℝ] E →L[ℝ] ℝ)
        (E := fun y : M => TangentSpace I y →L[ℝ] TangentSpace I y →L[ℝ] ℝ)
        q.2 ((g_DT q.1).inner q.2))
      (Set.Icc 0 T ×ˢ (trivializationAt E (TangentSpace I) α).baseSet) :=
    hsmooth.mono (Set.prod_mono_right (Set.subset_univ _))
  have h_gDT : ∀ (i' j' : Fin (Module.finrank ℝ E)),
      ContMDiffOn (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) ∞
        (fun q : ℝ × M =>
          chartGramOnE (I := I) (g_DT q.1) α i' j' (extChartAt I α q.2))
        (Set.Icc (0 : ℝ) T ×ˢ (chartAt H α).source) := fun i' j' =>
    chartGramOnE_jointContMDiffOn_of_innerSmooth (I := I) α i' j' g_DT
      (J := Set.Icc 0 T) hsmooth'
  -- Step 2: transfer to the chart-target-interior Euclidean form.
  have hMaster : ContDiffOn ℝ ∞
      (fun p : ℝ × E => chartGramOnE (I := I) (g_DT p.1) α i j p.2)
      (Set.Icc (0 : ℝ) T ×ˢ interior (extChartAt I α).target) :=
    chartGramOnE_joint_contDiffOn_of_manifold_closed (I := I) g_DT α h_gDT i j
  -- Step 3: the spatial jet bridge gives joint continuity of the Euclidean jet.
  have hbridge : ContinuousOn
      (fun q : ℝ × E => iteratedFDeriv ℝ k
        (fun y : E => chartGramOnE (I := I) (g_DT q.1) α i j y) q.2)
      (Set.Icc (0 : ℝ) T ×ˢ interior (extChartAt I α).target) :=
    continuousOn_joint_spatial_iteratedFDeriv (E := E)
      (uniqueDiffOn_Icc hT) isOpen_interior hMaster k
  -- Step 4: pull back along the chart map `Θ q = (q.1, extChartAt I α q.2)`.
  set Θ : ℝ × M → ℝ × E := fun q => (q.1, extChartAt I α q.2) with hΘ
  have hΘ_cont : ContinuousOn Θ
      (Set.Icc (0 : ℝ) T ×ˢ chartLeviCivitaGoodSet (I := I) α) := by
    refine ContinuousOn.prodMk continuousOn_fst ?_
    have hcont : ContinuousOn (extChartAt I α) (extChartAt I α).source :=
      continuousOn_extChartAt α
    refine (hcont.comp continuousOn_snd ?_)
    intro q hq
    exact chartLeviCivitaGoodSet_mem_extChartAt_source (I := I) hq.2
  have hΘ_maps : Set.MapsTo Θ
      (Set.Icc (0 : ℝ) T ×ˢ chartLeviCivitaGoodSet (I := I) α)
      (Set.Icc (0 : ℝ) T ×ˢ interior (extChartAt I α).target) := by
    intro q hq
    refine ⟨hq.1, ?_⟩
    exact chartLeviCivitaGoodSet_extChartAt_mem_interior (I := I) hq.2
  have hfinal := hbridge.comp hΘ_cont hΘ_maps
  refine hfinal.congr ?_
  intro q hq
  simp only [Function.comp_apply, hΘ]

end Measure
end Integral
end DifferentialGeometry
