import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Seifert.BaseMorse
import DifferentialGeometry.Topology.Diffeomorph.Flow
import DifferentialGeometry.Topology.VectorField.Transport
import DifferentialGeometry.Topology.Manifold.OpenSubtypeDiffeomorph
import DifferentialGeometry.Topology.Manifold.RegularLevel.Collar.LevelAtlas
import DifferentialGeometry.Topology.Manifold.ModelWithCorners
import DifferentialGeometry.Topology.Manifold.OneManifold.CircleClassification
import DifferentialGeometry.Topology.Morse.CriticalPoint
import DifferentialGeometry.Topology.Manifold.IntegralCurve.ScalarRate
import Mathlib.Analysis.ODE.ExistUnique
import Mathlib.Analysis.Calculus.BumpFunction.Basic
import Mathlib.Analysis.Calculus.ContDiff.RCLike

/-!
# Level bicollars of Morse data on the base surface

Lane MD1 of the P1 Morse-decomposition plan, tier T4.

`exists_flow_of_tsupport_interior`: a smooth vector field with compact support in the interior of
a manifold with boundary has a smooth global flow; it is the flow of the boundaryless interior
(`Diffeomorph.compactSupportFlow`), extended by the identity.

`exists_circle_of_level`: a compact component of a regular level lying in the interior of a
surface is the image of a smooth injective `γ : Circle → M`, and every smooth map with values in
it factors smoothly through `γ`; the level atlas of the interior and lane CC's classification of
compact connected one-manifolds.

`BaseMorseData.exists_levelBicollar` (frozen): the flow of `κ ψ(f) • field`, with `ψ` a bump equal
to `1` within `3κ/2` of the level, applied to that circle; along it `f` is affine of slope `κ` by
ODE uniqueness for the height, and the inverse is `x ↦ (γ⁻¹ (Φ (-τ x) x), τ x)` with
`τ = (f - ℓ) / κ`. `mfderiv_ne_zero_of_near_level` and `isInteriorPoint_of_near_level`: within
`2κ` of every level, `f` is regular and the points are interior.
-/

set_option autoImplicit false

noncomputable section
open Set Metric Function Bundle
open DifferentialGeometry DifferentialGeometry.Topology GC.Endpoint GC.GraphManifold
open DifferentialGeometry.Topology.Morse
open scoped Manifold ContDiff Topology

universe u

namespace GC.Seifert

theorem exists_flow_of_tsupport_interior {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [T2Space M]
    (Y : (x : M) → TangentSpace I x)
    (hY : ContMDiff I I.tangent ∞ (fun x => (⟨x, Y x⟩ : TangentBundle I M)))
    (hYc : IsCompact (tsupport Y)) (hYint : ∀ x ∈ tsupport Y, I.IsInteriorPoint x) :
    ∃ Φ : ℝ → M → M,
      ContMDiff (𝓘(ℝ, ℝ).prod I) I ∞ (fun p : ℝ × M => Φ p.1 p.2) ∧
      (∀ x, Φ 0 x = x) ∧ (∀ s t x, Φ t (Φ s x) = Φ (s + t) x) ∧
      ∀ x, IsMIntegralCurve (fun t => Φ t x) Y := by
  classical
  let U := DifferentialGeometry.Manifold.intrinsicInterior I ∞ (by simp) (M := M)
  have hzero (x : M) (hx : x ∉ U) : x ∉ tsupport Y := fun h => hx (hYint x h)
  rcases isEmpty_or_nonempty U with hU | hU
  · refine ⟨fun _ x => x, contMDiff_snd, fun _ => rfl, fun _ _ _ => rfl, fun x => ?_⟩
    exact isMIntegralCurve_const
      (image_eq_zero_of_notMem_tsupport (hzero x fun h => hU.false ⟨x, h⟩))
  let _ : ChartedSpace E U := DifferentialGeometry.Manifold.interiorChartedSpace I ∞ (M := U)
  have _ : IsManifold 𝓘(ℝ, E) ∞ U := DifferentialGeometry.Manifold.interiorIsManifold I ∞
  let ι : PartialDiffeomorph 𝓘(ℝ, E) I U M ∞ :=
    ((DifferentialGeometry.Manifold.interiorAtlasDiffeomorph I ∞ (M := U)).symm
      ).toPartialDiffeomorph.trans
      (DifferentialGeometry.Manifold.openSubtypePartialDiffeomorph I U hU)
  have hιs (z : U) : z ∈ ι.source := ⟨mem_univ _, mem_univ _⟩
  have hιapply (z : U) : ι z = z.val := rfl
  let YU : (y : U) → TangentSpace 𝓘(ℝ, E) y := VectorField.mpullback 𝓘(ℝ, E) I ι Y
  have hYU : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, E).tangent ∞
      (fun y => (⟨y, YU y⟩ : TangentBundle 𝓘(ℝ, E) U)) := by
    have h := DifferentialGeometry.VectorField.contMDiffOn_mpullback_partialDiffeomorph ι
      (m := ∞) (by simp) (V := Y) hY.contMDiffOn
    intro y
    exact (h y (hιs y)).contMDiffAt (ι.open_source.mem_nhds (hιs y))
  have hrel (y : U) : mfderiv 𝓘(ℝ, E) I ι y (YU y) = Y y.val := by
    let e := (ι.isLocalDiffeomorphAt 𝓘(ℝ, E) I ∞ (hιs y)).mfderivToContinuousLinearEquiv
      (by simp)
    have he : (e : TangentSpace 𝓘(ℝ, E) y →L[ℝ] TangentSpace I (ι y)) =
        mfderiv 𝓘(ℝ, E) I ι y := rfl
    change mfderiv 𝓘(ℝ, E) I ι y ((mfderiv 𝓘(ℝ, E) I ι y).inverse (Y (ι y))) = Y y.val
    rw [← he, ContinuousLinearMap.inverse_equiv]
    exact e.apply_symm_apply _
  have hYU0 (y : U) (hy : y.val ∉ tsupport Y) : YU y = 0 := by
    change (mfderiv 𝓘(ℝ, E) I ι y).inverse (Y (ι y)) = 0
    rw [hιapply, image_eq_zero_of_notMem_tsupport hy]
    exact ContinuousLinearMap.map_zero _
  have hcompact : IsCompact ((Subtype.val : U → M) ⁻¹' tsupport Y) := by
    refine Subtype.isCompact_iff.mpr ?_
    rw [image_preimage_eq_of_subset fun x hx => ⟨⟨x, hYint x hx⟩, rfl⟩]
    exact hYc
  have hYUc : IsCompact (tsupport YU) := by
    refine hcompact.of_isClosed_subset (isClosed_tsupport _) ?_
    refine closure_minimal (fun y hy => ?_)
      ((isClosed_tsupport Y).preimage continuous_subtype_val)
    by_contra h
    exact hy (hYU0 y h)
  let Fl := Diffeomorph.compactSupportFlow YU hYU hYUc
  let Φ : ℝ → M → M := fun t x => if hx : x ∈ U then (Fl t ⟨x, hx⟩).val else x
  have hΦU (t : ℝ) (y : U) : Φ t y.val = (Fl t y).val := by
    simp only [Φ, y.2, ↓reduceDIte]
  have hΦn (t : ℝ) (x : M) (hx : x ∉ U) : Φ t x = x := by
    simp only [Φ, hx, ↓reduceDIte]
  refine ⟨Φ, ?_, fun x => ?_, fun s t x => ?_, fun x => ?_⟩
  · rintro ⟨t₀, x₀⟩
    by_cases hx₀ : x₀ ∈ U
    · let σ : M → U := fun x => if hx : x ∈ U then ⟨x, hx⟩ else ⟨x₀, hx₀⟩
      have hσ : ContMDiffAt I 𝓘(ℝ, E) ∞ σ x₀ := by
        have hid : ContMDiff I 𝓘(ℝ, E) ∞ (id : U → U) :=
          DifferentialGeometry.Manifold.contMDiff_id_interiorAtlas I ∞ (M := U)
        have heq : (fun y : U => σ y) = id := funext fun y => by simp [σ, y.2]
        have h : ContMDiffAt I 𝓘(ℝ, E) ∞ (fun y : U => σ y) ⟨x₀, hx₀⟩ := by
          rw [heq]
          exact hid _
        exact (contMDiffAt_subtype_iff (f := σ)).mp h
      have hval : ContMDiff 𝓘(ℝ, E) I ∞ (Subtype.val : U → M) :=
        DifferentialGeometry.Manifold.contMDiff_intrinsicInterior_val I ∞ (by simp)
      have hFl := Diffeomorph.contMDiff_compactSupportFlow YU hYU hYUc
      have h1 : ContMDiffAt (𝓘(ℝ, ℝ).prod I) (𝓘(ℝ, ℝ).prod 𝓘(ℝ, E)) ∞
          (fun p : ℝ × M => (p.1, σ p.2)) (t₀, x₀) :=
        contMDiffAt_fst.prodMk
          (ContMDiffAt.comp (x := (t₀, x₀)) (g := σ) (f := Prod.snd) hσ contMDiffAt_snd)
      have h2 : ContMDiffAt (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, E) ∞
          (fun p : ℝ × M => Fl p.1 (σ p.2)) (t₀, x₀) :=
        (hFl (t₀, σ x₀)).comp (t₀, x₀) h1
      have hcomp : ContMDiffAt (𝓘(ℝ, ℝ).prod I) I ∞
          (fun p : ℝ × M => (Fl p.1 (σ p.2)).val) (t₀, x₀) :=
        (hval (Fl t₀ (σ x₀))).comp (t₀, x₀) h2
      refine hcomp.congr_of_eventuallyEq ?_
      have hUo : (U : Set M) ∈ 𝓝 x₀ := U.isOpen.mem_nhds hx₀
      filter_upwards [continuous_snd.continuousAt.preimage_mem_nhds hUo] with p hp
      have hp' : p.2 ∈ U := hp
      have : σ p.2 = ⟨p.2, hp'⟩ := by simp only [σ, hp', ↓reduceDIte]
      rw [this, ← hΦU]
    · have hN : (tsupport Y)ᶜ ∈ 𝓝 x₀ := (isClosed_tsupport Y).isOpen_compl.mem_nhds (hzero x₀ hx₀)
      refine contMDiffAt_snd.congr_of_eventuallyEq ?_
      filter_upwards [continuous_snd.continuousAt.preimage_mem_nhds hN] with p hp
      by_cases hpU : p.2 ∈ U
      · rw [show p.2 = (⟨p.2, hpU⟩ : U).val from rfl, hΦU]
        exact congrArg Subtype.val (Diffeomorph.compactSupportFlow_apply_eq_self_of_eq_zero
          YU hYU hYUc (hYU0 ⟨p.2, hpU⟩ hp) p.1)
      · exact hΦn _ _ hpU
  · by_cases hx : x ∈ U
    · rw [show x = (⟨x, hx⟩ : U).val from rfl, hΦU,
        show Fl 0 = Diffeomorph.refl 𝓘(ℝ, E) U ∞ from
          Diffeomorph.compactSupportFlow_zero YU hYU hYUc]
      rfl
    · exact hΦn _ _ hx
  · by_cases hx : x ∈ U
    · rw [show x = (⟨x, hx⟩ : U).val from rfl, hΦU, hΦU, hΦU,
        show Fl (s + t) = (Fl s).trans (Fl t) from
          Diffeomorph.compactSupportFlow_add YU hYU hYUc s t]
      rfl
    · rw [hΦn _ _ hx, hΦn _ _ hx, hΦn _ _ hx]
  · by_cases hx : x ∈ U
    · have hcurve := Diffeomorph.isMIntegralCurve_compactSupportFlow YU hYU hYUc ⟨x, hx⟩
      intro t
      have hd := (hιs (Fl t ⟨x, hx⟩))
      have hι : HasMFDerivAt 𝓘(ℝ, E) I ι (Fl t ⟨x, hx⟩)
          (mfderiv 𝓘(ℝ, E) I ι (Fl t ⟨x, hx⟩)) :=
        (ι.mdifferentiableAt (by simp) hd).hasMFDerivAt
      have h := hι.comp t (hcurve t)
      have hfun : (fun t => Φ t x) = ι ∘ fun t => Fl t ⟨x, hx⟩ := by
        funext s
        exact hΦU s ⟨x, hx⟩
      have hder : (mfderiv 𝓘(ℝ, E) I ι (Fl t ⟨x, hx⟩)).comp
          ((1 : ℝ →L[ℝ] ℝ).smulRight (YU (Fl t ⟨x, hx⟩))) =
          (1 : ℝ →L[ℝ] ℝ).smulRight (Y (Fl t ⟨x, hx⟩).val) := by
        ext
        change mfderiv 𝓘(ℝ, E) I ι (Fl t ⟨x, hx⟩) ((1 : ℝ) • YU (Fl t ⟨x, hx⟩)) =
          (1 : ℝ) • Y (Fl t ⟨x, hx⟩).val
        rw [map_smul, hrel]
        rfl
      rw [hfun]
      exact h.congr_mfderiv hder
    · have hc : (fun t => Φ t x) = fun _ => x := funext fun t => hΦn t x hx
      rw [hc]
      exact isMIntegralCurve_const (image_eq_zero_of_notMem_tsupport (hzero x hx))

theorem exists_circle_of_level {H : Type*} [TopologicalSpace H]
    {I : ModelWithCorners ℝ (EuclideanSpace ℝ (Fin 2)) H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [T2Space M]
    {f : M → ℝ} (hf : ContMDiff I 𝓘(ℝ, ℝ) ∞ f) {ℓ : ℝ} (hcompact : IsCompact (f ⁻¹' {ℓ}))
    (hint : ∀ x, f x = ℓ → I.IsInteriorPoint x)
    (hreg : ∀ x, f x = ℓ → mfderiv I 𝓘(ℝ, ℝ) f x ≠ 0) {x₀ : M} (hx₀ : f x₀ = ℓ) :
    ∃ γ : Circle → M, ContMDiff (𝓡 1) I ∞ γ ∧ Injective γ ∧
      range γ = connectedComponentIn (f ⁻¹' {ℓ}) x₀ ∧
      (∃ W : Set M, IsOpen W ∧ W ∩ f ⁻¹' {ℓ} = range γ) ∧
      ∀ T : Set M, IsOpen T → ∀ F : M → M, ContMDiffOn I I ∞ F T → MapsTo F T (range γ) →
        ContMDiffOn I (𝓡 1) ∞ (fun x => invFun γ (F x)) T := by
  classical
  let E2 := EuclideanSpace ℝ (Fin 2)
  let U := DifferentialGeometry.Manifold.intrinsicInterior I ∞ (by simp) (M := M)
  let _ : ChartedSpace E2 U := DifferentialGeometry.Manifold.interiorChartedSpace I ∞ (M := U)
  have _ : IsManifold 𝓘(ℝ, E2) ∞ U := DifferentialGeometry.Manifold.interiorIsManifold I ∞
  have hU : Nonempty U := ⟨⟨x₀, hint x₀ hx₀⟩⟩
  have hval : ContMDiff 𝓘(ℝ, E2) I ∞ (Subtype.val : U → M) :=
    DifferentialGeometry.Manifold.contMDiff_intrinsicInterior_val I ∞ (by simp)
  let L : E2 ≃L[ℝ] (Fin (1 + 1) → ℝ) := ContinuousLinearEquiv.ofFinrankEq (by simp [E2])
  let J : ModelWithCorners ℝ (Fin (1 + 1) → ℝ) E2 := 𝓘(ℝ, E2).transContinuousLinearEquiv L
  let g : U → ℝ := fun y => f y
  have hgE : ContMDiff 𝓘(ℝ, E2) 𝓘(ℝ, ℝ) ∞ g := hf.comp hval
  have hgJ : ContMDiff J 𝓘(ℝ, ℝ) ∞ g :=
    (ContinuousLinearEquiv.contMDiff_transContinuousLinearEquiv_left L).mpr hgE
  have hgold : ContMDiff I 𝓘(ℝ, ℝ) ∞ g := hf.comp contMDiff_subtype_val
  have hrJ : ∀ y, g y = ℓ → mfderiv J 𝓘(ℝ, ℝ) g y ≠ 0 := by
    intro y hy hcrit
    have h1 : IsCriticalPointAt 𝓘(ℝ, E2) g y :=
      (DifferentialGeometry.Topology.Morse.isCriticalPointAt_transContinuousLinearEquiv_iff
        𝓘(ℝ, E2) L g y).mp hcrit
    have ho : (show E2 →L[ℝ] ℝ from mfderiv 𝓘(ℝ, E2) 𝓘(ℝ, ℝ) g y) =
        (show E2 →L[ℝ] ℝ from mfderiv I 𝓘(ℝ, ℝ) g y) :=
      DifferentialGeometry.Manifold.mfderiv_interiorAtlas I hgold y
    have hu := DifferentialGeometry.Manifold.mfderiv_openRestriction I hf y y.2
    exact hreg y hy (hu.symm.trans (ho.symm.trans h1))
  let Λ := {y : U // g y = ℓ}
  let _ : ChartedSpace (Fin 1 → ℝ) Λ :=
    DifferentialGeometry.Manifold.RegularLevel.levelChartedSpace J hgJ hrJ
  have _ : IsManifold 𝓘(ℝ, Fin 1 → ℝ) ∞ Λ :=
    DifferentialGeometry.Manifold.RegularLevel.levelIsManifold J hgJ hrJ
  have _ : LocallyConnectedSpace Λ := ChartedSpace.locallyConnectedSpace (Fin 1 → ℝ) Λ
  let ψ : Λ ≃ₜ (f ⁻¹' {ℓ} : Set M) :=
    { toFun := fun y => ⟨y.val.val, y.2⟩
      invFun := fun z => ⟨⟨z.val, hint z.val z.2⟩, z.2⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl
      continuous_toFun := (continuous_subtype_val.comp continuous_subtype_val).subtype_mk _
      continuous_invFun :=
        (continuous_subtype_val.subtype_mk _).subtype_mk _ }
  have _ : CompactSpace (f ⁻¹' {ℓ} : Set M) := isCompact_iff_compactSpace.mp hcompact
  have _ : CompactSpace Λ := Homeomorph.compactSpace ψ.symm
  let p₀ : Λ := ⟨⟨x₀, hint x₀ hx₀⟩, hx₀⟩
  let C : TopologicalSpace.Opens Λ := ⟨connectedComponent p₀, isOpen_connectedComponent⟩
  have _ : CompactSpace C := isCompact_iff_compactSpace.mp isClosed_connectedComponent.isCompact
  have _ : ConnectedSpace C := isConnected_iff_connectedSpace.mp isConnected_connectedComponent
  obtain ⟨e⟩ :=
    DifferentialGeometry.Topology.Manifold.OneManifold.nonempty_circle_diffeomorph_of_finrank_eq_one
      (Fin 1 → ℝ) (Fin 1 → ℝ) C 𝓘(ℝ, Fin 1 → ℝ) (Module.finrank_fin_fun ℝ)
  let γ : Circle → M := fun t => (e t).val.val.val
  have hγ : ContMDiff (𝓡 1) I ∞ γ := by
    have h1 : ContMDiff (𝓡 1) 𝓘(ℝ, Fin 1 → ℝ) ∞ (fun t => (e t).val) :=
      contMDiff_subtype_val.comp e.contMDiff
    have h2 : ContMDiff (𝓡 1) J ∞ (fun t => (e t).val.val) :=
      (DifferentialGeometry.Manifold.RegularLevel.contMDiff_level_inclusion J hgJ hrJ).comp h1
    have h3 : ContMDiff (𝓡 1) 𝓘(ℝ, E2) ∞ (fun t => (e t).val.val) :=
      (ContinuousLinearEquiv.contMDiff_transContinuousLinearEquiv_right L).mp h2
    exact hval.comp h3
  have hγinj : Injective γ := fun a b h =>
    e.injective (Subtype.ext (Subtype.ext (Subtype.ext h)))
  have h1 : range γ = Subtype.val '' (ψ '' connectedComponent p₀) := by
    ext x
    constructor
    · rintro ⟨t, rfl⟩
      exact ⟨ψ (e t).val, ⟨(e t).val, (e t).2, rfl⟩, rfl⟩
    · rintro ⟨_, ⟨y, hy, rfl⟩, rfl⟩
      obtain ⟨t, ht⟩ := e.surjective ⟨y, hy⟩
      have ht' : e t = ⟨y, hy⟩ := ht
      refine ⟨t, ?_⟩
      change (e t).val.val.val = (ψ y).val
      rw [ht']
      rfl
  have hrange : range γ = connectedComponentIn (f ⁻¹' {ℓ}) x₀ := by
    have h2 : ψ '' connectedComponent p₀ = connectedComponent (ψ p₀) := by
      rw [← connectedComponentIn_univ, ψ.image_connectedComponentIn (mem_univ _),
        image_univ_of_surjective ψ.surjective, connectedComponentIn_univ]
    rw [h1, h2, connectedComponentIn_eq_image (show x₀ ∈ f ⁻¹' {ℓ} from hx₀)]
    rfl
  have hW : ∃ W : Set M, IsOpen W ∧ W ∩ f ⁻¹' {ℓ} = range γ := by
    obtain ⟨W, hWo, hWe⟩ := isOpen_induced_iff.mp (ψ.isOpenMap _ isOpen_connectedComponent)
    refine ⟨W, hWo, ?_⟩
    rw [h1, ← hWe]
    ext x
    constructor
    · rintro ⟨hxW, hx⟩
      exact ⟨⟨x, hx⟩, hxW, rfl⟩
    · rintro ⟨y, hy, rfl⟩
      exact ⟨hy, y.2⟩
  refine ⟨γ, hγ, hγinj, hrange, hW, fun T hT F hF hFT => ?_⟩
  let T' : TopologicalSpace.Opens M := ⟨T, hT⟩
  let ι : PartialDiffeomorph 𝓘(ℝ, E2) I U M ∞ :=
    ((DifferentialGeometry.Manifold.interiorAtlasDiffeomorph I ∞ (M := U)).symm
      ).toPartialDiffeomorph.trans
      (DifferentialGeometry.Manifold.openSubtypePartialDiffeomorph I U hU)
  have hιs (z : U) : z ∈ ι.source := ⟨mem_univ _, mem_univ _⟩
  have hpre (z : T') : ∃ t, F z = γ t := by
    obtain ⟨t, ht⟩ := hFT z.2
    exact ⟨t, ht.symm⟩
  have hFU (z : T') : F z ∈ U := by
    obtain ⟨t, ht⟩ := hpre z
    rw [ht]
    exact (e t).val.val.2
  let F1 : T' → U := fun z => ⟨F z, hFU z⟩
  have hFval : ContMDiff I I ∞ (fun z : T' => F z) :=
    hF.comp_contMDiff contMDiff_subtype_val fun z => z.2
  have hF1 : ContMDiff I 𝓘(ℝ, E2) ∞ F1 := by
    have hmem (z : T') : F z ∈ ι.symm.source := by
      have h := ι.map_source (hιs ⟨F z, hFU z⟩)
      exact h
    refine (ι.symm.contMDiffOn.comp_contMDiff hFval hmem).congr fun z => ?_
    exact (ι.left_inv (hιs ⟨F z, hFU z⟩)).symm
  have hF1J : ContMDiff I J ∞ F1 :=
    (ContinuousLinearEquiv.contMDiff_transContinuousLinearEquiv_right L).mpr hF1
  have hF1a (z : T') : g (F1 z) = ℓ := by
    have h : F z ∈ f ⁻¹' {ℓ} := connectedComponentIn_subset _ _ (hrange ▸ hFT z.2)
    exact h
  have hF2 := DifferentialGeometry.Manifold.RegularLevel.contMDiff_level_factor J hgJ hrJ
    hF1J hF1a
  have hC (z : T') : (⟨F1 z, hF1a z⟩ : Λ) ∈ C := by
    obtain ⟨t, ht⟩ := hpre z
    have heq : (⟨F1 z, hF1a z⟩ : Λ) = (e t).val := Subtype.ext (Subtype.ext ht)
    rw [heq]
    exact (e t).2
  have hCne : Nonempty C := ⟨⟨p₀, mem_connectedComponent⟩⟩
  let ιC := DifferentialGeometry.Manifold.openSubtypePartialDiffeomorph 𝓘(ℝ, Fin 1 → ℝ) C hCne
  let F3 : T' → C := fun z => ⟨⟨F1 z, hF1a z⟩, hC z⟩
  have hF3 : ContMDiff I 𝓘(ℝ, Fin 1 → ℝ) ∞ F3 := by
    have hmem (z : T') : (⟨F1 z, hF1a z⟩ : Λ) ∈ ιC.symm.source := by
      have h := ιC.map_source (x := F3 z) (by simp [ιC])
      exact h
    refine (ιC.symm.contMDiffOn.comp_contMDiff hF2 hmem).congr fun z => ?_
    exact (ιC.left_inv (by simp [ιC])).symm
  let G : T' → Circle := fun z => e.symm (F3 z)
  have hG : ContMDiff I (𝓡 1) ∞ G := e.symm.contMDiff.comp hF3
  have hGeq (z : T') : invFun γ (F z) = G z := by
    have h : γ (G z) = F z := by
      change (e (e.symm (F3 z))).val.val.val = F z
      rw [e.apply_symm_apply]
    rw [← h]
    exact leftInverse_invFun hγinj (G z)
  intro x hx
  have h : ContMDiffAt I (𝓡 1) ∞ (fun z : T' => invFun γ (F z)) ⟨x, hx⟩ := by
    rw [show (fun z : T' => invFun γ (F z)) = G from funext hGeq]
    exact hG _
  exact ((contMDiffAt_subtype_iff (U := T') (f := fun x => invFun γ (F x))).mp h
    ).contMDiffWithinAt

private theorem eq_affine_of_hasDerivAt {φ : ℝ → ℝ} {K : NNReal} (hφ : LipschitzWith K φ)
    {ℓ r κ : ℝ} (hκ : 0 < κ) (hφ1 : ∀ y, |y - ℓ| < r → φ y = κ) {h : ℝ → ℝ}
    (hh : ∀ s, HasDerivAt h (φ (h s)) s) (h0 : |h 0 - ℓ| < r) {s : ℝ}
    (hs : |h 0 + κ * s - ℓ| < r) : h s = h 0 + κ * s := by
  set a := (ℓ - r - h 0) / κ
  set b := (ℓ + r - h 0) / κ
  have hab (t : ℝ) : t ∈ Ioo a b ↔ |h 0 + κ * t - ℓ| < r := by
    rw [mem_Ioo, div_lt_iff₀ hκ, lt_div_iff₀ hκ, abs_lt]
    constructor <;> rintro ⟨h1, h2⟩ <;> constructor <;> linarith
  have h0ab : (0 : ℝ) ∈ Ioo a b := (hab 0).mpr (by simpa using h0)
  have hEq := ODE_solution_unique_of_mem_Ioo (v := fun _ y => φ y) (s := fun _ => univ) (K := K)
    (f := h) (g := fun t => h 0 + κ * t) (fun _ _ => hφ.lipschitzOnWith) h0ab
    (fun t _ => ⟨hh t, mem_univ _⟩)
    (fun t ht => ⟨by
      rw [hφ1 _ ((hab t).mp ht)]
      simpa using ((hasDerivAt_id t).const_mul κ).const_add (h 0), mem_univ _⟩) (by simp)
  exact hEq ((hab s).mpr hs)

namespace BaseMorseData

variable {B : CompactSurface.{u}}

theorem mfderiv_ne_zero_of_near_level (D : BaseMorseData B) (i : Fin (D.m + 1)) {x : B.Carrier}
    (hx : |D.f x - D.level i| < 2 * D.κ) :
    mfderiv (SurfaceModel.model B.kind) 𝓘(ℝ, ℝ) D.f x ≠ 0 := by
  intro hz
  have hu := D.field_unit i x hx
  rw [hz] at hu
  have h01 : (0 : ℝ) = 1 := hu
  norm_num at h01

theorem isInteriorPoint_of_near_level (D : BaseMorseData B) (i : Fin (D.m + 1)) {x : B.Carrier}
    (hx : |D.f x - D.level i| < 2 * D.κ) : (SurfaceModel.model B.kind).IsInteriorPoint x := by
  have h0 : D.level 0 ≤ D.level i := D.level_strictMono.monotone (Fin.zero_le i)
  exact D.isInteriorPoint_of_pos (by linarith [(abs_lt.mp hx).1, D.two_κ_lt_level])

theorem exists_levelBicollar (D : BaseMorseData B) (i : Fin (D.m + 1)) {x₀ : B.Carrier}
    (hx₀ : D.f x₀ = D.level i) :
    ∃ c : PartialDiffeomorph ((𝓡 1).prod 𝓘(ℝ, ℝ)) (SurfaceModel.model B.kind) (Circle × ℝ)
        B.Carrier ∞,
      c.source = {p | -1 < p.2 ∧ p.2 < 1} ∧
      range (fun t => c (t, 0)) = connectedComponentIn (D.f ⁻¹' {D.level i}) x₀ ∧
      (∀ t s, -1 < s → s < 1 → D.f (c (t, s)) = D.level i + D.κ * s) ∧
      ∀ t, IsMIntegralCurveOn (fun s => c (t, s)) (fun x => D.κ • D.field x) (Ioo (-1) 1) := by
  classical
  set ℓ := D.level i
  set κ := D.κ
  have hκ : 0 < κ := D.κ_pos
  have hℓ : 2 * κ < ℓ :=
    D.two_κ_lt_level.trans_le (D.level_strictMono.monotone (Fin.zero_le i))
  let ψ : ContDiffBump ℓ := ⟨3 * κ / 2, 2 * κ, by positivity, by linarith⟩
  have hψ1 (y : ℝ) (hy : |y - ℓ| < 3 * κ / 2) : ψ y = 1 :=
    ψ.one_of_mem_closedBall (by rw [mem_closedBall, Real.dist_eq]; exact hy.le)
  have hψ0 (y : ℝ) (hy : ψ y ≠ 0) : |y - ℓ| < 2 * κ := by
    have h : y ∈ support ψ := hy
    rw [ψ.support_eq, mem_ball, Real.dist_eq] at h
    exact h
  let Y : (x : B.Carrier) → TangentSpace (SurfaceModel.model B.kind) x :=
    fun x => (κ * ψ (D.f x)) • D.field x
  have hψf : ContMDiff (SurfaceModel.model B.kind) 𝓘(ℝ, ℝ) ∞ (fun x => κ * ψ (D.f x)) :=
    contMDiff_const.mul ((ψ.contDiff (n := (⊤ : ℕ∞))).contMDiff.comp D.smooth)
  have hY : ContMDiff (SurfaceModel.model B.kind) (SurfaceModel.model B.kind).tangent ∞
      (fun x => (⟨x, Y x⟩ : TangentBundle (SurfaceModel.model B.kind) B.Carrier)) :=
    hψf.smul_section D.field_smooth
  have hYrate (x : B.Carrier) :
      mfderiv (SurfaceModel.model B.kind) 𝓘(ℝ, ℝ) D.f x (Y x) = κ * ψ (D.f x) := by
    change mfderiv (SurfaceModel.model B.kind) 𝓘(ℝ, ℝ) D.f x ((κ * ψ (D.f x)) • D.field x) =
      κ * ψ (D.f x)
    rw [map_smul]
    by_cases h : ψ (D.f x) = 0
    · rw [h, mul_zero, zero_smul]
      rfl
    · rw [D.field_unit i x (hψ0 _ h)]
      change (κ * ψ (D.f x)) * (1 : ℝ) = κ * ψ (D.f x)
      exact mul_one _
  have hYsupp : tsupport Y ⊆ D.f ⁻¹' Icc (ℓ - 2 * κ) (ℓ + 2 * κ) := by
    refine closure_minimal (fun x hx => ?_) (isClosed_Icc.preimage D.smooth.continuous)
    have hψx : ψ (D.f x) ≠ 0 := fun h => hx (by
      change (κ * ψ (D.f x)) • D.field x = 0
      rw [h, mul_zero, zero_smul])
    have h := hψ0 _ hψx
    exact ⟨by linarith [(abs_lt.mp h).1], by linarith [(abs_lt.mp h).2]⟩
  have hYc : IsCompact (tsupport Y) := (isClosed_tsupport Y).isCompact
  have hYint : ∀ x ∈ tsupport Y, (SurfaceModel.model B.kind).IsInteriorPoint x := fun x hx =>
    D.isInteriorPoint_of_pos (by linarith [(hYsupp hx).1])
  obtain ⟨Φ, hΦs, hΦ0, hΦadd, hΦcurve⟩ := exists_flow_of_tsupport_interior Y hY hYc hYint
  obtain ⟨K, hK⟩ := ContDiff.lipschitzWith_of_hasCompactSupport (𝕂 := ℝ) (n := 1)
    (f := fun y : ℝ => κ * ψ y) (ψ.hasCompactSupport.mul_left)
    (contDiff_const.mul ψ.contDiff) one_ne_zero
  have hheight (x : B.Carrier) (hx : |D.f x - ℓ| < 3 * κ / 2) (s : ℝ)
      (hs : |D.f x + κ * s - ℓ| < 3 * κ / 2) : D.f (Φ s x) = D.f x + κ * s := by
    have hd (t : ℝ) : HasDerivAt (fun t => D.f (Φ t x)) (κ * ψ (D.f (Φ t x))) t := by
      have h := DifferentialGeometry.Manifold.hasDerivWithinAt_scalar_comp_integralCurve
        ((hΦcurve x).isMIntegralCurveOn univ) (mem_univ t) (D.smooth.mdifferentiableAt (by simp))
      rw [hYrate] at h
      exact h.hasDerivAt Filter.univ_mem
    have h := eq_affine_of_hasDerivAt hK hκ (r := 3 * κ / 2) (ℓ := ℓ)
      (fun y hy => by simp only [hψ1 y hy, mul_one]) hd (by rw [hΦ0]; exact hx)
      (by rw [hΦ0]; exact hs)
    rw [hΦ0] at h
    exact h
  have hlc : IsCompact (D.f ⁻¹' {ℓ}) :=
    (isClosed_singleton.preimage D.smooth.continuous).isCompact
  have hli : ∀ x, D.f x = ℓ → (SurfaceModel.model B.kind).IsInteriorPoint x := fun x hx =>
    D.isInteriorPoint_of_pos (by rw [hx]; linarith)
  have hlr : ∀ x, D.f x = ℓ → mfderiv (SurfaceModel.model B.kind) 𝓘(ℝ, ℝ) D.f x ≠ 0 := by
    intro x hx hz
    have hu := D.field_unit i x (by rw [hx, sub_self, abs_zero]; linarith)
    rw [hz] at hu
    have h01 : (0 : ℝ) = 1 := hu
    norm_num at h01
  obtain ⟨γ, hγ, hγinj, hγrange, ⟨W, hWo, hWe⟩, hfactor⟩ :=
    exists_circle_of_level D.smooth hlc hli hlr hx₀
  have hγℓ (t : Circle) : D.f (γ t) = ℓ := by
    have h : γ t ∈ D.f ⁻¹' {ℓ} := connectedComponentIn_subset _ _ (hγrange ▸ mem_range_self t)
    exact h
  have hγW (t : Circle) : γ t ∈ W := by
    have h : γ t ∈ W ∩ D.f ⁻¹' {ℓ} := hWe ▸ mem_range_self t
    exact h.1
  let cf : Circle × ℝ → B.Carrier := fun p => Φ p.2 (γ p.1)
  have hcf : ContMDiff ((𝓡 1).prod 𝓘(ℝ, ℝ)) (SurfaceModel.model B.kind) ∞ cf :=
    hΦs.comp (contMDiff_snd.prodMk (hγ.comp contMDiff_fst))
  have hcfh (t : Circle) (s : ℝ) (hs : |s| < 3 / 2) : D.f (cf (t, s)) = ℓ + κ * s := by
    have hks : |κ * s| < 3 * κ / 2 := by
      rw [abs_mul, abs_of_pos hκ]
      nlinarith [abs_nonneg s]
    have h := hheight (γ t) (by rw [hγℓ, sub_self, abs_zero]; positivity) s
      (by rw [hγℓ, add_sub_cancel_left]; exact hks)
    rw [h, hγℓ]
  let τ : B.Carrier → ℝ := fun x => (D.f x - ℓ) / κ
  have hτ : ContMDiff (SurfaceModel.model B.kind) 𝓘(ℝ, ℝ) ∞ τ :=
    (D.smooth.sub contMDiff_const).div_const κ
  let F : B.Carrier → B.Carrier := fun x => Φ (-τ x) x
  have hF : ContMDiff (SurfaceModel.model B.kind) (SurfaceModel.model B.kind) ∞ F :=
    hΦs.comp (hτ.neg.prodMk contMDiff_id)
  have hFℓ (x : B.Carrier) (hx : |D.f x - ℓ| < κ) : D.f (F x) = ℓ := by
    have hsum : D.f x + κ * -τ x = ℓ := by
      simp only [τ]
      field_simp
      ring
    have h := hheight x (by linarith) (-τ x) (by rw [hsum, sub_self, abs_zero]; positivity)
    rw [h, hsum]
  let T : Set B.Carrier := {x | |D.f x - ℓ| < κ ∧ F x ∈ W}
  have hTo : IsOpen T :=
    (isOpen_lt (continuous_abs.comp (D.smooth.continuous.sub continuous_const))
      continuous_const).inter (hWo.preimage hF.continuous)
  have hFT : MapsTo F T (range γ) := fun x hx => hWe ▸ ⟨hx.2, hFℓ x hx.1⟩
  let inv : B.Carrier → Circle × ℝ := fun x => (invFun γ (F x), τ x)
  have hinv : ContMDiffOn (SurfaceModel.model B.kind) ((𝓡 1).prod 𝓘(ℝ, ℝ)) ∞ inv T :=
    (hfactor T hTo F hF.contMDiffOn hFT).prodMk hτ.contMDiffOn
  have hτcf (t : Circle) (s : ℝ) (hs : |s| < 3 / 2) : τ (cf (t, s)) = s := by
    simp only [τ]
    rw [hcfh t s hs]
    field_simp
    ring
  have hFcf (t : Circle) (s : ℝ) (hs : |s| < 3 / 2) : F (cf (t, s)) = γ t := by
    simp only [F]
    rw [hτcf t s hs]
    change Φ (-s) (Φ s (γ t)) = γ t
    rw [hΦadd, add_neg_cancel, hΦ0]
  have hcfF (x : B.Carrier) (hx : x ∈ T) : cf (inv x) = x := by
    have hγx : γ (invFun γ (F x)) = F x := invFun_eq (hFT hx)
    change Φ (τ x) (γ (invFun γ (F x))) = x
    rw [hγx]
    change Φ (τ x) (Φ (-τ x) x) = x
    rw [hΦadd, neg_add_cancel, hΦ0]
  have habs (p : Circle × ℝ) (hp : -1 < p.2 ∧ p.2 < 1) : |p.2| < 3 / 2 :=
    abs_lt.mpr ⟨by linarith [hp.1], by linarith [hp.2]⟩
  let c : PartialDiffeomorph ((𝓡 1).prod 𝓘(ℝ, ℝ)) (SurfaceModel.model B.kind) (Circle × ℝ)
      B.Carrier ∞ :=
    { toFun := cf
      invFun := inv
      source := {p | -1 < p.2 ∧ p.2 < 1}
      target := T
      map_source' := fun p hp => by
        refine ⟨?_, ?_⟩
        · change |D.f (cf (p.1, p.2)) - ℓ| < κ
          rw [hcfh p.1 p.2 (habs p hp), add_sub_cancel_left, abs_mul, abs_of_pos hκ]
          have h1 : |p.2| < 1 := abs_lt.mpr hp
          nlinarith [abs_nonneg p.2]
        · change F (cf (p.1, p.2)) ∈ W
          rw [hFcf p.1 p.2 (habs p hp)]
          exact hγW p.1
      map_target' := fun x hx => by
        have h := abs_lt.mp hx.1
        change -1 < τ x ∧ τ x < 1
        constructor
        · rw [lt_div_iff₀ hκ]
          linarith
        · rw [div_lt_iff₀ hκ]
          linarith
      left_inv' := fun p hp => by
        change (invFun γ (F (cf (p.1, p.2))), τ (cf (p.1, p.2))) = p
        rw [hFcf p.1 p.2 (habs p hp), hτcf p.1 p.2 (habs p hp), leftInverse_invFun hγinj p.1]
      right_inv' := fun x hx => hcfF x hx
      open_source := (isOpen_lt continuous_const continuous_snd).inter
        (isOpen_lt continuous_snd continuous_const)
      open_target := hTo
      contMDiffOn_toFun := hcf.contMDiffOn
      contMDiffOn_invFun := hinv }
  refine ⟨c, rfl, ?_, fun t s hs1 hs2 => hcfh t s (abs_lt.mpr ⟨by linarith, by linarith⟩), ?_⟩
  · rw [← hγrange]
    congr 1
    funext t
    exact hΦ0 (γ t)
  · intro t s hs
    have h := hΦcurve (γ t) s
    have hY1 : Y (Φ s (γ t)) = κ • D.field (Φ s (γ t)) := by
      change (κ * ψ (D.f (Φ s (γ t)))) • D.field (Φ s (γ t)) = κ • D.field (Φ s (γ t))
      have hsabs : |s| < 3 / 2 := abs_lt.mpr ⟨by linarith [hs.1], by linarith [hs.2]⟩
      have hval : D.f (Φ s (γ t)) = ℓ + κ * s := hcfh t s hsabs
      rw [hψ1 _ (by
        rw [hval, add_sub_cancel_left, abs_mul, abs_of_pos hκ]
        nlinarith [abs_nonneg s]), mul_one]
    rw [hY1] at h
    exact h.hasMFDerivWithinAt

end BaseMorseData

end GC.Seifert
