import DifferentialGeometry.Topology.VectorBundle.RankOneQuotient.Basic
import DifferentialGeometry.Topology.VectorBundle.NormPreservingDisc

/-!
# Smooth maps out of a rank-one bundle through `S(V) × ℝ`

Lane LFR54-QUOT. Let `ν : Σ → TotalSpace F V` be a smooth injective unit map onto the unit sphere
bundle of a smooth Riemannian line bundle, intertwining an involution `τ` with `v ↦ -v`, such that
`proj ∘ ν` is a local diffeomorphism. A smooth map `Θ : Σ × ℝ → M` with `Θ (τ p, -t) = Θ (p, t)`
descends along `Φ (p, t) = t • ν p` to a smooth map on the total space
(`exists_contMDiff_rankOneDescend`): near a point the local inverse `s` of `proj ∘ ν` and the fibre
inner product `t = ⟪z, ν (s (proj z))⟫` are smooth coordinates inverting `Φ`.

The closed `R`-disc bundle with its native boundary charts (`normClosedDiscBundleChartedSpace`):
the inclusion is smooth (`contMDiff_normClosedDisc_val`) and a map into it is smooth exactly when its
composite with the inclusion is smooth (`contMDiff_normClosedDisc_iff`).
-/

set_option autoImplicit false

noncomputable section

open Bundle Manifold Set Filter Module
open scoped ContDiff Topology Manifold
open DifferentialGeometry.Topology.Morse DifferentialGeometry.Manifold.RegularLevel

namespace DifferentialGeometry.Topology.VectorBundle.RankOneQuotient

variable {EB F : Type*} [NormedAddCommGroup EB] [NormedSpace ℝ EB]
  [NormedAddCommGroup F] [NormedSpace ℝ F] {HB : Type*} [TopologicalSpace HB]
  {IB : ModelWithCorners ℝ EB HB}
  {B : Type*} [TopologicalSpace B] [ChartedSpace HB B]
  {V : B → Type*} [TopologicalSpace (TotalSpace F V)]
  [∀ b, NormedAddCommGroup (V b)] [∀ b, InnerProductSpace ℝ (V b)]
  [FiberBundle F V] [VectorBundle ℝ F V]
  [IsContMDiffRiemannianBundle IB ∞ F V]
  {ES : Type*} [NormedAddCommGroup ES] [NormedSpace ℝ ES] {HS : Type*} [TopologicalSpace HS]
  {IS : ModelWithCorners ℝ ES HS} {S : Type*} [TopologicalSpace S] [ChartedSpace HS S]
  {EM : Type*} [NormedAddCommGroup EM] [NormedSpace ℝ EM] {HM : Type*} [TopologicalSpace HM]
  {J : ModelWithCorners ℝ EM HM} {M : Type*} [TopologicalSpace M] [ChartedSpace HM M]

/-- **Descent along `(p, t) ↦ t • ν p`.** -/
theorem exists_contMDiff_rankOneDescend (hF : finrank ℝ F = 1)
    (ν : S → TotalSpace F V) (hν : ContMDiff IS (IB.prod 𝓘(ℝ, F)) ∞ ν)
    (hνS : ∀ p, ‖(ν p).2‖ = 1) (hνinj : Function.Injective ν)
    (hνsurj : ∀ z : TotalSpace F V, ‖z.2‖ = 1 → ∃ p, ν p = z)
    (τ : S → S) (hνneg : ∀ p, ν (τ p) = ⟨(ν p).proj, -(ν p).2⟩)
    (hνloc : IsLocalDiffeomorph IS IB ∞ (fun p => (ν p).proj))
    (Θ : S × ℝ → M) (hΘ : ContMDiff (IS.prod 𝓘(ℝ, ℝ)) J ∞ Θ)
    (hΘτ : ∀ p t, Θ (τ p, -t) = Θ (p, t)) :
    ∃ Ψ : TotalSpace F V → M, (∀ q, Ψ (rankOneParam ν q) = Θ q) ∧
      ContMDiff (IB.prod 𝓘(ℝ, F)) J ∞ Ψ := by
  classical
  have hsurj := rankOneParam_surjective ν hF hνsurj
  let Ψ : TotalSpace F V → M := fun z => Θ (Classical.choose (hsurj z))
  have hΨ : ∀ q, Ψ (rankOneParam ν q) = Θ q := by
    intro q
    have hq := Classical.choose_spec (hsurj (rankOneParam ν q))
    change Θ (Classical.choose (hsurj (rankOneParam ν q))) = Θ q
    rcases rankOneParam_eq_iff ν τ hF hνS hνinj hνneg hq with h | h
    · rw [h]
    · rw [h, hΘτ]
  refine ⟨Ψ, hΨ, fun z₀ => ?_⟩
  obtain ⟨⟨p₀, t₀⟩, hq₀⟩ := hsurj z₀
  have hb₀ : (ν p₀).proj = z₀.proj :=
    (congrArg TotalSpace.proj hq₀ : (rankOneParam ν (p₀, t₀)).proj = z₀.proj)
  let hl := hνloc p₀
  let s : B → S := hl.localInverse
  let bz : TotalSpace F V → B := fun z => (ν (s z.proj)).proj
  let vz : ∀ z, V (bz z) := fun z => (ν (s z.proj)).2
  let wz : ∀ z, V (bz z) := fun z =>
    if h : z.proj = bz z then cast (congrArg V h) z.2 else 0
  let T : TotalSpace F V → ℝ := fun z => inner ℝ (wz z) (vz z)
  let κ : TotalSpace F V → S × ℝ := fun z => (s z.proj, T z)
  -- near `z₀` the local inverse is a right inverse of `proj ∘ ν`
  have hev : ∀ᶠ z in 𝓝 z₀, bz z = z.proj := by
    have h1 := hl.localInverse_eventuallyEq_right
    rw [hb₀] at h1
    exact (FiberBundle.continuous_proj F V).continuousAt.eventually h1
  have hmk : ∀ᶠ z in 𝓝 z₀, (⟨bz z, wz z⟩ : TotalSpace F V) = z := by
    filter_upwards [hev] with z hz
    have h' : z.proj = bz z := hz.symm
    change (⟨bz z, if h : z.proj = bz z then cast (congrArg V h) z.2 else 0⟩ :
      TotalSpace F V) = z
    rw [dite_eq_left h']
    exact TotalSpace.mk_cast h' z.2
  have hκ : ∀ᶠ z in 𝓝 z₀, rankOneParam ν (κ z) = z := by
    filter_upwards [hmk] with z hz
    have hrank : finrank ℝ (V (bz z)) = 1 := (finrank_fiber (F := F) (V := V) _).trans hF
    have hw := eq_inner_smul_of_finrank_eq_one hrank (wz z) (vz z) (hνS _)
    change (⟨bz z, T z • vz z⟩ : TotalSpace F V) = z
    change (⟨bz z, inner ℝ (wz z) (vz z) • vz z⟩ : TotalSpace F V) = z
    rw [← hw]
    exact hz
  have hΨκ : Ψ =ᶠ[𝓝 z₀] Θ ∘ κ := by
    filter_upwards [hκ] with z hz
    change Ψ z = Θ (κ z)
    conv_lhs => rw [← hz]
    exact hΨ (κ z)
  -- smoothness of the local coordinates
  have hs : ContMDiffAt (IB.prod 𝓘(ℝ, F)) IS ∞ (fun z : TotalSpace F V => s z.proj) z₀ := by
    have h1 := hl.contMDiffAt_localInverse
    change ContMDiffAt IB IS ∞ s (ν p₀).proj at h1
    rw [hb₀] at h1
    exact h1.comp z₀ (Bundle.contMDiff_proj (IB := IB) (n := ∞) (F := F) (E := V) z₀)
  have hvz : ContMDiffAt (IB.prod 𝓘(ℝ, F)) (IB.prod 𝓘(ℝ, F)) ∞
      (fun z => (⟨bz z, vz z⟩ : TotalSpace F V)) z₀ :=
    (hν (s z₀.proj)).comp z₀ hs
  have hwz : ContMDiffAt (IB.prod 𝓘(ℝ, F)) (IB.prod 𝓘(ℝ, F)) ∞
      (fun z => (⟨bz z, wz z⟩ : TotalSpace F V)) z₀ :=
    contMDiffAt_id.congr_of_eventuallyEq hmk
  have hT : ContMDiffAt (IB.prod 𝓘(ℝ, F)) 𝓘(ℝ, ℝ) ∞ T z₀ := hwz.inner_bundle hvz
  have hκs : ContMDiffAt (IB.prod 𝓘(ℝ, F)) (IS.prod 𝓘(ℝ, ℝ)) ∞ κ z₀ := hs.prodMk hT
  exact ((hΘ (κ z₀)).comp z₀ hκs).congr_of_eventuallyEq hΨκ

variable [FiniteDimensional ℝ EB] [FiniteDimensional ℝ F] [IB.Boundaryless] [IsManifold IB ∞ B]
  [ContMDiffVectorBundle ∞ F V IB]

/-- The inclusion of the closed `R`-disc bundle (native boundary charts) is smooth. -/
theorem contMDiff_normClosedDisc_val {m : ℕ} (hd : finrank ℝ (EB × F) = m + 1) (R : ℝ)
    (hR : 0 < R) :
    letI := normClosedDiscBundleChartedSpace (IB := IB) (V := V) hd R hR
    ContMDiff (morseModelWithCornersHalfSpace m) (IB.prod 𝓘(ℝ, F)) ∞
      (Subtype.val : {z : TotalSpace F V // ‖z.2‖ ≤ R} → TotalSpace F V) := by
  let := closedDiscBundleChartedSpace (IB := IB) (V := V) hd R hR
  let := closedDiscBundle_isManifold (IB := IB) (V := V) hd R hR
  let e₁ := normClosedDiscSublevelHomeomorph (F := F) (V := V) R hR
  let := DifferentialGeometry.Manifold.Homeomorph.pullbackChartedSpace
    (H := MorseHalfSpace m) e₁
  let D₁ := DifferentialGeometry.Manifold.Homeomorph.pullbackDiffeomorph
    (I := morseModelWithCornersHalfSpace m) (n := ∞) e₁
  have h := contMDiff_sublevel_inclusion (bundleRadiusBoundaryModel (IB := IB) hd)
    (contMDiff_fiberRadiusSquared_boundaryModel (V := V) hd)
    (fun z hz => mfderiv_fiberRadiusSquared_boundaryModel_ne_zero hd hR z hz)
  have h2 := (bundleRadiusBoundaryEquiv hd).contMDiff_transContinuousLinearEquiv_right.mp h
  exact h2.comp D₁.contMDiff

/-- A map into the closed `R`-disc bundle is smooth iff its composite with the inclusion is. -/
theorem contMDiff_normClosedDisc_iff {m : ℕ} (hd : finrank ℝ (EB × F) = m + 1) {R : ℝ}
    (hR : 0 < R) {EX : Type*} [NormedAddCommGroup EX] [NormedSpace ℝ EX] {HX : Type*}
    [TopologicalSpace HX] {JX : ModelWithCorners ℝ EX HX} {X : Type*} [TopologicalSpace X]
    [ChartedSpace HX X] {g : X → {z : TotalSpace F V // ‖z.2‖ ≤ R}} :
    letI := normClosedDiscBundleChartedSpace (IB := IB) (V := V) hd R hR
    ContMDiff JX (morseModelWithCornersHalfSpace m) ∞ g ↔
      ContMDiff JX (IB.prod 𝓘(ℝ, F)) ∞ (fun x => (g x).val) := by
  let := normClosedDiscBundleChartedSpace (IB := IB) (V := V) hd R hR
  refine ⟨fun hg => (contMDiff_normClosedDisc_val hd R hR).comp hg, fun hg => ?_⟩
  let := closedDiscBundleChartedSpace (IB := IB) (V := V) hd R hR
  let := closedDiscBundle_isManifold (IB := IB) (V := V) hd R hR
  let e₁ := normClosedDiscSublevelHomeomorph (F := F) (V := V) R hR
  let := DifferentialGeometry.Manifold.Homeomorph.pullbackChartedSpace
    (H := MorseHalfSpace m) e₁
  let D₁ := DifferentialGeometry.Manifold.Homeomorph.pullbackDiffeomorph
    (I := morseModelWithCornersHalfSpace m) (n := ∞) e₁
  have h1 : ContMDiff JX (morseModelWithCornersHalfSpace m) ∞ (fun x => D₁ (g x)) := by
    apply (contMDiff_sublevel_iff (bundleRadiusBoundaryModel (IB := IB) hd) JX
      (contMDiff_fiberRadiusSquared_boundaryModel (V := V) hd)
      (fun z hz => mfderiv_fiberRadiusSquared_boundaryModel_ne_zero hd hR z hz) le_rfl).mpr
    exact (bundleRadiusBoundaryEquiv hd).contMDiff_transContinuousLinearEquiv_right.mpr hg
  have h2 := D₁.symm.contMDiff.comp h1
  refine h2.congr fun x => ?_
  exact (D₁.symm_apply_apply (g x)).symm

end DifferentialGeometry.Topology.VectorBundle.RankOneQuotient
