import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch12.OpenStep_S145
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.CuspP1.ExteriorWindowStage

set_option autoImplicit false

/-! # CH12-O82 G1: same-stage open image of a persistent model patch

`openImage_O82`: if `Θ : ℝ × M → D` is smooth on an open `U` and `x ↦ Θ (σ₁, x)` has injective
differential at `x₁`, then every point `Θ q` with `q` near `(σ₁, x₁)` is hit by `Θ (σ₁, ·)` from
any prescribed neighbourhood `V` of `x₁` (inverse function theorem on the slice).

`patch_rr_O82`: for a `PersistentModelPatch` at `(t, z₀)` with injective spatial differential of
`p.map (t, ·)` at `z₀`, for `(s, z)` near `(t, z₀)` with `t ≤ s` the point `mold s z` is
(`HEq`) a point `mold t z''` with `z'' ∈ V` (right constancy of the active stage + `p.agrees`).
-/

noncomputable section
open Set Filter Topology DifferentialGeometry DifferentialGeometry.Geometry.Hyperbolic
open DifferentialGeometry.PDE.RicciFlow.Surgery.Topology DifferentialGeometry.Geometry.Collapse
open DifferentialGeometry.Topology.Manifold
open Manifold GC.LongTime GC.LongTime.CuspP1
open TopologicalSpace
open scoped Manifold ContDiff ENNReal

namespace GC.LongTime.Ch12
universe u

/-- Slice inverse function theorem in neighbourhood form. -/
theorem openImage_O82 {M D : Type u} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] [IsManifold (𝓡 3) ∞ M] [T2Space M]
    [TopologicalSpace D] [ChartedSpace (EuclideanSpace ℝ (Fin 3)) D] [IsManifold (𝓡 3) ∞ D]
    (Θ : ℝ × M → D) (U : Opens (ℝ × M)) (hΘ : ContMDiffOn (𝓘(ℝ, ℝ).prod (𝓡 3)) (𝓡 3) ∞ Θ U)
    {σ1 : ℝ} {x1 : M} (hx : (σ1, x1) ∈ U)
    (hinj : Function.Injective (mfderiv (𝓡 3) (𝓡 3) (fun x => Θ (σ1, x)) x1))
    {V : Set M} (hV : V ∈ 𝓝 x1) :
    ∀ᶠ q in 𝓝 (σ1, x1), ∃ x ∈ V, (σ1, x) ∈ U ∧ Θ (σ1, x) = Θ q := by
  classical
  let N : Opens M := ⟨(fun x : M => ((σ1 : ℝ), x)) ⁻¹' (U : Set (ℝ × M)),
    U.isOpen.preimage (continuous_const.prodMk continuous_id)⟩
  have hx1 : x1 ∈ N := hx
  have hsl : ContMDiff (𝓡 3) (𝓘(ℝ, ℝ).prod (𝓡 3)) ∞ (fun x : M => ((σ1 : ℝ), x)) :=
    contMDiff_const.prodMk contMDiff_id
  have hΘ1 : ContMDiffOn (𝓡 3) (𝓡 3) ∞ (fun x => Θ (σ1, x)) N :=
    hΘ.comp hsl.contMDiffOn (fun _ hy => hy)
  have hsm := contMDiff_restrict_C4 (fun x => Θ (σ1, x)) N hΘ1
  let z0 : N := ⟨x1, hx1⟩
  have hinj' : Function.Injective
      (mfderiv (𝓡 3) (𝓡 3) (fun z : N => (fun x => Θ (σ1, x)) (z : M)) z0) := by
    intro a b hab
    have h := mfderiv_comp_val_C4 (fun x => Θ (σ1, x)) N hΘ1 z0
    rw [h a, h b] at hab
    exact hinj hab
  have hloc := isLocalDiffeomorphAt_of_isInteriorPoint_of_injective_mfderiv hsm (x := z0)
    (BoundarylessManifold.isInteriorPoint (I := 𝓡 3)) (by simp) hinj'
  have hmem := hloc.localInverse_mem_source
  have hLz : hloc.localInverse (Θ (σ1, x1)) = z0 :=
    hloc.localInverse_left_inv hloc.localInverse_mem_target
  have hO1 : hloc.localInverse.source ∈ 𝓝 (Θ (σ1, x1)) :=
    hloc.localInverse.open_source.mem_nhds hmem
  have hLc : ContinuousAt (fun y => ((hloc.localInverse y : N) : M)) (Θ (σ1, x1)) :=
    continuous_subtype_val.continuousAt.comp hloc.continuousAt_localInverse
  have hO2 : (fun y => ((hloc.localInverse y : N) : M)) ⁻¹' V ∈ 𝓝 (Θ (σ1, x1)) := by
    apply hLc.preimage_mem_nhds
    rw [hLz]
    exact hV
  have hΘc : ContinuousAt Θ (σ1, x1) :=
    (hΘ.contMDiffAt (U.isOpen.mem_nhds hx)).continuousAt
  filter_upwards [hΘc.preimage_mem_nhds hO1, hΘc.preimage_mem_nhds hO2] with q hqs hqV
  exact ⟨((hloc.localInverse (Θ q) : N) : M), hqV, (hloc.localInverse (Θ q)).2,
    hloc.localInverse_right_inv hqs⟩

/-- Backward survivor maps at equal stage indices agree (`HEq`). -/
theorem bsm_heq_O82 (K : ObservedHistory.{u}) (first last : Fin (K.eventCount + 1))
    (hle : first ≤ last) {k₁ k₂ : Fin (K.eventCount + 1)} (hk : k₁ = k₂)
    (hf₁ : first ≤ k₁) (hl₁ : k₁ ≤ last) (hf₂ : first ≤ k₂) (hl₂ : k₂ ≤ last)
    (y : K.backwardSurvivorDomain first last hle) :
    HEq (K.backwardSurvivorMap first last hle k₁ hf₁ hl₁ y)
      (K.backwardSurvivorMap first last hle k₂ hf₂ hl₂ y) := by
  subst hk
  rfl

section Patch

variable {P : OrientedThreeStage.{u}} {g : P.Metric} {F : GC.Interface.RawSurgery P g}
  {Hold : FiniteVolumeHyperbolicModel.{u}} {start : ℝ} {α : ℝ → ℝ}
  {Ω : TopologicalSpace.Opens (ℝ × Hold.Carrier)}
  {mold : ∀ t : ℝ, start ≤ t → Hold.Carrier → (postStage F.observation t).Carrier}

/-- Same-stage right regularisation near one patch point. -/
theorem patch_rr_O82 {t : ℝ} {z₀ : Hold.Carrier}
    (p : PersistentModelPatch F Hold start α (sourceSlice_CX5 Ω) mold t z₀) (hi : start ≤ t)
    (hinj : Function.Injective (mfderiv (𝓡 3) (𝓡 3) (fun x' => p.map (t, x')) z₀))
    {V : Set Hold.Carrier} (hV : V ∈ 𝓝 z₀) :
    ∀ᶠ q : ℝ × Hold.Carrier in 𝓝 (t, z₀), t ≤ q.1 → ∀ (hs : start ≤ q.1)
      (x : (postStage F.observation t).Carrier), HEq x (mold q.1 hs q.2) →
        x ∈ mold t hi '' V := by
  classical
  have ht0 : 0 ≤ t := p.a_nonneg.trans p.before.le
  have hth : t ≤ (F.tower.history p.n).horizon := p.after.le.trans p.horizon
  let τt : Icc (0 : ℝ) (F.tower.history p.n).horizon := ⟨t, ht0, hth⟩
  have hτt : (τt : ℝ) ∈ Ioo p.a p.b := ⟨p.before, p.after⟩
  let U : Opens (ℝ × Hold.Carrier) := ⟨Ioo p.a p.b ×ˢ (p.neighborhood : Set Hold.Carrier),
    isOpen_Ioo.prod p.neighborhood.isOpen⟩
  have hU : ((t, z₀) : ℝ × Hold.Carrier) ∈ U := ⟨hτt, p.mem_neighborhood⟩
  have hVN : V ∩ p.neighborhood ∈ 𝓝 z₀ :=
    Filter.inter_mem hV (p.neighborhood.isOpen.mem_nhds p.mem_neighborhood)
  obtain ⟨δr, hδr, hconst⟩ :=
    exists_right_const_activeStage_CPD7 (F.tower.history p.n).toHistory ht0 hth
  have himg := openImage_O82 p.map U p.smooth hU hinj hVN
  have hUn : (U : Set (ℝ × Hold.Carrier)) ∈ 𝓝 (t, z₀) := U.isOpen.mem_nhds hU
  have hδn : {q : ℝ × Hold.Carrier | q.1 < t + δr} ∈ 𝓝 (t, z₀) :=
    (isOpen_lt continuous_fst continuous_const).mem_nhds (show t < t + δr by linarith)
  filter_upwards [himg, hUn, hδn] with q hq hqU hqδ
  intro htq hs x hx
  obtain ⟨x'', ⟨hx''V, hx''N⟩, -, hmap⟩ := hq
  have hq0 : 0 ≤ q.1 := ht0.trans htq
  have hqh : q.1 ≤ (F.tower.history p.n).horizon := hqU.1.2.le.trans p.horizon
  let τs : Icc (0 : ℝ) (F.tower.history p.n).horizon := ⟨q.1, hq0, hqh⟩
  have hτs : (τs : ℝ) ∈ Ioo p.a p.b := hqU.1
  have hact : (F.tower.history p.n).toHistory.activeStage τs =
      (F.tower.history p.n).toHistory.activeStage τt :=
    hconst q.1 hq0 hqh htq hqδ
  have h1 := p.agrees τs hτs hs q.2 hqU.2
  have h2 := p.agrees τt hτt hi x'' hx''N
  have h3 := bsm_heq_O82 (F.tower.history p.n).toHistory p.first p.last p.ordered hact
    (p.stages τs hτs).1 (p.stages τs hτs).2 (p.stages τt hτt).1 (p.stages τt hτt).2 (p.map q)
  have hmap' : p.map ((τt : ℝ), x'') = p.map q := hmap
  rw [hmap'] at h2
  exact ⟨x'', hx''V, eq_of_heq (h2.symm.trans (h3.symm.trans (h1.trans hx.symm)))⟩

end Patch

end GC.LongTime.Ch12
