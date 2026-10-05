import DifferentialGeometry.Topology.Manifold.DiskModelChartExtension
import DifferentialGeometry.Topology.Manifold.RegularLevel.Collar.LevelAtlas
import DifferentialGeometry.Topology.Manifold.SmoothModelTransport
import DifferentialGeometry.Topology.Manifold.SmoothModelTransportSource
import DifferentialGeometry.Topology.Manifold.ClosedBall

/-!
# FC39 GROUP G, RIMBOX route B (sheet §3 K2): the polar two-sided end collar on the slice `{g = 0}`

Lane FC39-G-RIMBOX, dispositions D62-3 (b), D62-6 ("POLAR-2 initial collar: ι = old handle slice at
`t = 0` into `N₀ = {g = 0}`, disk model id; the slice lemma `d(g, T)` onto ⟹ `d(T|ker dg) ≠ 0`").
On a boundaryless 3-manifold `Y` modelled on `MorseModel 3`, for a regular function `g` and a smooth
`T`, and a smooth injective immersion `ι₀` of the closed disk into the slice `{g = 0}` with `T = c` on
the rim, `T ≤ c` on the disk and `(g, T)` submersive at the rim:

* the slice `N₀ = {g = 0}` (`RegularLevel.levelChartedSpace`, model `MorseModel 2`) recharted on the
  Euclidean plane (`chartedSpaceTransHomeomorph`, `isManifold_transHomeomorph`);
* the slice lemma: `range d(val) = ker dg` (dimension count), so `d(T|N₀) ≠ 0` at the rim;
* POLAR-2 (`exists_diskModel_polar_twoSided_of_immersion`) on `N₀`;

give `exists_polarEndCollar_GRIM`: a disk re-parametrization `d` (identity on the rim and on
`‖w‖ ≤ 1 − η`) and a two-sided collar `C` of the rim in `{g = 0}` (smooth, injective, immersive on
`{|‖z‖ − 1| < δ}`) with `T ∘ C = c + κ (‖z‖ − 1)`, `C = ι₀` on the rim and the INNER MATCHING
`ι₀ (d w) = C w` for `1 − δ < ‖w‖` — the input of the short `RimProductAt` proof (D62-3 (b)).
-/

set_option autoImplicit false

noncomputable section

open Set Function
open DifferentialGeometry DifferentialGeometry.Topology DifferentialGeometry.Topology.Morse
open scoped Manifold ContDiff Topology

namespace GC.GraphManifold.Assembly.FC39P0

local instance diskChartsEC_GRIM : ChartedSpace (EuclideanHalfSpace 2) (ClosedCell 2) :=
  DifferentialGeometry.Topology.Handle.closedCellChartedSpaceSucc 1

local instance diskSmoothEC_GRIM : IsManifold (𝓡∂ 2) ∞ (ClosedCell 2) :=
  DifferentialGeometry.Topology.Handle.closedCellIsManifold 1

local instance diskChartsEC'_GRIM : ChartedSpace (EuclideanHalfSpace (1 + 1)) (ClosedCell 2) :=
  DifferentialGeometry.Topology.Handle.closedCellChartedSpaceSucc 1

local instance diskSmoothEC'_GRIM : IsManifold (𝓡∂ (1 + 1)) ∞ (ClosedCell 2) :=
  DifferentialGeometry.Topology.Handle.closedCellIsManifold 1

variable {H Y : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ (MorseModel 3) H}
  [I.Boundaryless] [TopologicalSpace Y] [ChartedSpace H Y] [IsManifold I ∞ Y] [T2Space Y]

/-- **The polar two-sided end collar (POLAR-2 on the regular slice `{g = 0}`).** The old end disk
`ι₀`, re-parametrized by a disk diffeomorphism `d`, agrees near the rim with a two-sided collar `C`
in the slice along which `T` is radial. -/
theorem exists_polarEndCollar_GRIM {g T : Y → ℝ} (hg : ContMDiff I 𝓘(ℝ, ℝ) ∞ g)
    (hT : ContMDiff I 𝓘(ℝ, ℝ) ∞ T) (hgr : ∀ y, g y = 0 → mfderiv I 𝓘(ℝ, ℝ) g y ≠ 0)
    (ι₀ : ClosedCell 2 → Y) (hι₀ : ContMDiff (𝓡∂ 2) I ∞ ι₀) (hι₀inj : Injective ι₀)
    (hι₀imm : ∀ w, Injective (mfderiv (𝓡∂ 2) I ι₀ w)) (hι₀g : ∀ w, g (ι₀ w) = 0) {c : ℝ}
    (hTc : ∀ w : ClosedCell 2, ‖(w : EuclideanSpace ℝ (Fin 2))‖ = 1 → T (ι₀ w) = c)
    (hTle : ∀ w, T (ι₀ w) ≤ c)
    (hpair : ∀ w : ClosedCell 2, ‖(w : EuclideanSpace ℝ (Fin 2))‖ = 1 →
      Surjective (mfderiv I 𝓘(ℝ, ℝ × ℝ) (fun y => (g y, T y)) (ι₀ w)))
    {κ : ℝ} (hκ : 0 < κ) {η : ℝ} (hη0 : 0 < η) (hη1 : η < 1) :
    ∃ δ : ℝ, 0 < δ ∧ δ < η ∧
      ∃ (d : ClosedCell 2 ≃ₘ⟮𝓡∂ 2, 𝓡∂ 2⟯ ClosedCell 2) (C : EuclideanSpace ℝ (Fin 2) → Y),
        ContMDiffOn (𝓡 2) I ∞ C {z | |‖z‖ - 1| < δ} ∧ InjOn C {z | |‖z‖ - 1| < δ} ∧
        (∀ z, |‖z‖ - 1| < δ → Injective (mfderiv (𝓡 2) I C z)) ∧
        (∀ z, |‖z‖ - 1| < δ → g (C z) = 0 ∧ T (C z) = c + κ * (‖z‖ - 1)) ∧
        (∀ w : ClosedCell 2, ‖(w : EuclideanSpace ℝ (Fin 2))‖ = 1 → C w = ι₀ w) ∧
        (∀ w : ClosedCell 2, 1 - δ < ‖(w : EuclideanSpace ℝ (Fin 2))‖ → ι₀ (d w) = C w) ∧
        (∀ w : ClosedCell 2, ‖(w : EuclideanSpace ℝ (Fin 2))‖ = 1 → d w = w) ∧
        (∀ w : ClosedCell 2, ‖(w : EuclideanSpace ℝ (Fin 2))‖ ≤ 1 - η → d w = w) := by
  -- the slice manifold, recharted on the Euclidean plane
  let N₀ := {y : Y // g y = 0}
  let A : ChartedSpace (MorseModel 2) N₀ :=
    DifferentialGeometry.Manifold.RegularLevel.levelChartedSpace I hg hgr
  have hA : IsManifold 𝓘(ℝ, MorseModel 2) ∞ N₀ :=
    DifferentialGeometry.Manifold.RegularLevel.levelIsManifold I hg hgr
  have hdim : Module.finrank ℝ (MorseModel 2) = Module.finrank ℝ (EuclideanSpace ℝ (Fin 2)) := by
    simp [MorseModel]
  let L : MorseModel 2 ≃L[ℝ] EuclideanSpace ℝ (Fin 2) := ContinuousLinearEquiv.ofFinrankEq hdim
  have hcompat : ∀ y, (𝓡 2) (L.toHomeomorph y) = L (𝓘(ℝ, MorseModel 2) y) := fun _ => rfl
  let B : ChartedSpace (EuclideanSpace ℝ (Fin 2)) N₀ :=
    DifferentialGeometry.Manifold.chartedSpaceTransHomeomorph (M := N₀) L.toHomeomorph
  have hB : IsManifold (𝓡 2) ∞ N₀ :=
    DifferentialGeometry.Manifold.isManifold_transHomeomorph 𝓘(ℝ, MorseModel 2) (𝓡 2)
      L.toHomeomorph L hcompat
  have hn : (∞ : WithTop ℕ∞) ≠ 0 := by simp
  have hval : ContMDiff (𝓡 2) I ∞ (Subtype.val : N₀ → Y) :=
    (DifferentialGeometry.Manifold.contMDiff_chartedSpaceTransHomeomorph_source_iff
      𝓘(ℝ, MorseModel 2) (𝓡 2) L.toHomeomorph L hcompat I).mpr
      (DifferentialGeometry.Manifold.RegularLevel.contMDiff_level_inclusion I hg hgr)
  have hemb : Manifold.IsSmoothEmbedding (𝓡 2) I ∞ (Subtype.val : N₀ → Y) :=
    (DifferentialGeometry.Manifold.isSmoothEmbedding_chartedSpaceTransHomeomorph_source_iff
      𝓘(ℝ, MorseModel 2) (𝓡 2) L.toHomeomorph L hcompat I).mpr
      (DifferentialGeometry.Manifold.RegularLevel.isSmoothEmbedding_level_inclusion I hg hgr)
  have hvalimm : ∀ y : N₀, Injective (mfderiv (𝓡 2) I (Subtype.val : N₀ → Y) y) :=
    fun y => hemb.isImmersion.mfderiv_injective hn y
  let ι : ClosedCell 2 → N₀ := fun w => ⟨ι₀ w, hι₀g w⟩
  have hι : ContMDiff (𝓡∂ 2) (𝓡 2) ∞ ι :=
    (DifferentialGeometry.Manifold.contMDiff_chartedSpaceTransHomeomorph_iff
      𝓘(ℝ, MorseModel 2) (𝓡 2) L.toHomeomorph L hcompat (𝓡∂ 2)).mpr
      (DifferentialGeometry.Manifold.RegularLevel.contMDiff_level_factor I hg hgr hι₀ hι₀g)
  have hιinj : Injective ι := fun w w' h => hι₀inj (congrArg Subtype.val h)
  have hιc : ∀ w, mfderiv (𝓡∂ 2) I ι₀ w =
      (mfderiv (𝓡 2) I (Subtype.val : N₀ → Y) (ι w)).comp (mfderiv (𝓡∂ 2) (𝓡 2) ι w) := fun w =>
    mfderiv_comp (g := (Subtype.val : N₀ → Y)) (f := ι) w ((hval _).mdifferentiableAt hn)
      ((hι w).mdifferentiableAt hn)
  have hιimm : ∀ w, Injective (mfderiv (𝓡∂ 2) (𝓡 2) ι w) := by
    intro w v v' h
    apply hι₀imm w
    rw [hιc w]
    exact congrArg (mfderiv (𝓡 2) I (Subtype.val : N₀ → Y) (ι w)) h
  let T₀ : N₀ → ℝ := fun y => T y.val
  have hT₀ : ContMDiff (𝓡 2) 𝓘(ℝ, ℝ) ∞ T₀ := hT.comp hval
  -- regularity of `T` on the slice at the rim
  have hreg : ∀ w : ClosedCell 2, ‖(w : EuclideanSpace ℝ (Fin 2))‖ = 1 →
      mfderiv (𝓡 2) 𝓘(ℝ, ℝ) T₀ (ι w) ≠ 0 := by
    intro w hw
    let Dv : EuclideanSpace ℝ (Fin 2) →L[ℝ] MorseModel 3 :=
      mfderiv (𝓡 2) I (Subtype.val : N₀ → Y) (ι w)
    let dg : MorseModel 3 →L[ℝ] ℝ := mfderiv I 𝓘(ℝ, ℝ) g (ι₀ w)
    let dT : MorseModel 3 →L[ℝ] ℝ := mfderiv I 𝓘(ℝ, ℝ) T (ι₀ w)
    let dP : MorseModel 3 →L[ℝ] ℝ × ℝ := mfderiv I 𝓘(ℝ, ℝ × ℝ) (fun y => (g y, T y)) (ι₀ w)
    have hgd : MDifferentiableAt I 𝓘(ℝ, ℝ) g (ι₀ w) := (hg _).mdifferentiableAt hn
    have hTd : MDifferentiableAt I 𝓘(ℝ, ℝ) T (ι₀ w) := (hT _).mdifferentiableAt hn
    have hvd : MDifferentiableAt (𝓡 2) I (Subtype.val : N₀ → Y) (ι w) :=
      (hval _).mdifferentiableAt hn
    have hpd : MDifferentiableAt I 𝓘(ℝ, ℝ × ℝ) (fun y => (g y, T y)) (ι₀ w) :=
      ((hg.prodMk_space hT) _).mdifferentiableAt hn
    have hfst : ∀ u, (dP u).1 = dg u := by
      intro u
      have hfd : MDifferentiableAt 𝓘(ℝ, ℝ × ℝ) 𝓘(ℝ, ℝ) (Prod.fst : ℝ × ℝ → ℝ)
          (g (ι₀ w), T (ι₀ w)) := ((contDiff_fst.contMDiff) _).mdifferentiableAt hn
      have := mfderiv_comp (ι₀ w) hfd hpd
      have hc : (Prod.fst ∘ fun y => (g y, T y)) = g := rfl
      rw [hc, mfderiv_eq_fderiv, fderiv_fst] at this
      change (dP u).1 = mfderiv I 𝓘(ℝ, ℝ) g (ι₀ w) u
      rw [this]
      rfl
    have hsnd : ∀ u, (dP u).2 = dT u := by
      intro u
      have hsd : MDifferentiableAt 𝓘(ℝ, ℝ × ℝ) 𝓘(ℝ, ℝ) (Prod.snd : ℝ × ℝ → ℝ)
          (g (ι₀ w), T (ι₀ w)) := ((contDiff_snd.contMDiff) _).mdifferentiableAt hn
      have := mfderiv_comp (ι₀ w) hsd hpd
      have hc : (Prod.snd ∘ fun y => (g y, T y)) = T := rfl
      rw [hc, mfderiv_eq_fderiv, fderiv_snd] at this
      change (dP u).2 = mfderiv I 𝓘(ℝ, ℝ) T (ι₀ w) u
      rw [this]
      rfl
    have hPs : Surjective dP := hpair w hw
    obtain ⟨u, hu⟩ := hPs (0, 1)
    have hu1 : dg u = 0 := by rw [← hfst, hu]
    have hu2 : dT u = 1 := by rw [← hsnd, hu]
    have hgv : ∀ v, dg (Dv v) = 0 := by
      intro v
      have hconst : (g ∘ (Subtype.val : N₀ → Y)) = fun _ => 0 := funext fun y => y.2
      have h1 := mfderiv_comp (ι w) hgd hvd
      rw [hconst, mfderiv_const] at h1
      have h2 := congrArg (fun F => F v) h1
      exact h2.symm
    have hgsurj : Surjective dg := by
      intro r
      obtain ⟨u', hu'⟩ := hPs (r, 0)
      exact ⟨u', by rw [← hfst, hu']⟩
    have hle : LinearMap.range (Dv : EuclideanSpace ℝ (Fin 2) →ₗ[ℝ] MorseModel 3) ≤
        LinearMap.ker (dg : MorseModel 3 →ₗ[ℝ] ℝ) := by
      rintro _ ⟨v, rfl⟩
      exact hgv v
    have hrk1 : Module.finrank ℝ
        (LinearMap.range (Dv : EuclideanSpace ℝ (Fin 2) →ₗ[ℝ] MorseModel 3)) = 2 := by
      have hinjDv : Injective (Dv : EuclideanSpace ℝ (Fin 2) →ₗ[ℝ] MorseModel 3) := hvalimm (ι w)
      rw [LinearMap.finrank_range_of_inj hinjDv]
      simp
    have hrk2 : Module.finrank ℝ (LinearMap.ker (dg : MorseModel 3 →ₗ[ℝ] ℝ)) = 2 := by
      have h := LinearMap.finrank_range_add_finrank_ker (dg : MorseModel 3 →ₗ[ℝ] ℝ)
      rw [LinearMap.range_eq_top.mpr hgsurj, finrank_top, Module.finrank_self] at h
      have h3 : Module.finrank ℝ (MorseModel 3) = 3 := Module.finrank_fin_fun ℝ
      omega
    have heq := Submodule.eq_of_le_of_finrank_eq hle (hrk1.trans hrk2.symm)
    have humem : u ∈ LinearMap.range (Dv : EuclideanSpace ℝ (Fin 2) →ₗ[ℝ] MorseModel 3) := by
      rw [heq]
      exact hu1
    obtain ⟨v, hv⟩ := humem
    intro h0
    let dT₀ : EuclideanSpace ℝ (Fin 2) →L[ℝ] ℝ := mfderiv (𝓡 2) 𝓘(ℝ, ℝ) T₀ (ι w)
    have hdT₀ : dT₀ = 0 := h0
    have hT₀v : dT₀ v = 1 := by
      have h1 := mfderiv_comp (ι w) hTd hvd
      have hc : T ∘ (Subtype.val : N₀ → Y) = T₀ := rfl
      rw [hc] at h1
      change mfderiv (𝓡 2) 𝓘(ℝ, ℝ) T₀ (ι w) v = (1 : ℝ)
      rw [h1]
      change dT (Dv v) = 1
      have hv' : Dv v = u := hv
      rw [hv', hu2]
    rw [hdT₀] at hT₀v
    exact absurd hT₀v (by norm_num)
  -- POLAR-2 on the slice
  have hbd : ∀ z : ClosedCell 2,
      (𝓡∂ 2).IsBoundaryPoint z ↔ ‖(z : EuclideanSpace ℝ (Fin 2))‖ = 1 :=
    fun z => Set.ext_iff.mp (DifferentialGeometry.Topology.Manifold.closedCell_boundary_eq_sphere 1) z
  have hT2 : T2Space N₀ := inferInstance
  let _ : ChartedSpace (EuclideanSpace ℝ (Fin (1 + 1))) N₀ := B
  have _ : IsManifold (𝓡 (1 + 1)) ∞ N₀ := hB
  obtain ⟨δ, hδ0, hδη, d, C, hCs, hCT, hCS, hCD, hDS, hDη⟩ :=
    DifferentialGeometry.Topology.Manifold.exists_diskModel_polar_twoSided_of_immersion
      (m := 1) (N := N₀) (S := ClosedCell 2) (Diffeomorph.refl (𝓡∂ 2) (ClosedCell 2) ∞) ι hι hιinj
      hιimm (V := univ) isOpen_univ (fun _ _ => mem_univ _) hT₀.contMDiffOn (c := c)
      (fun y hy => hTc y ((hbd y).mp hy)) (fun y _ => hTle y)
      (fun y hy => hreg y ((hbd y).mp hy)) hκ hη0 hη1
  have hzs : ∀ z : EuclideanSpace ℝ (Fin 2), |‖z‖ - 1| < δ → z ∈ C.source := fun z hz => by
    rw [hCs]
    exact hz
  refine ⟨δ, hδ0, hδη, d, fun z => (C z : Y), ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · have hCsm : ContMDiffOn (𝓡 2) (𝓡 2) ∞ C {z | |‖z‖ - 1| < δ} := by
      rw [← hCs]
      exact C.contMDiffOn
    exact hval.comp_contMDiffOn hCsm
  · intro z hz z' hz' h
    exact C.toPartialEquiv.injOn (hzs z hz) (hzs z' hz') (Subtype.ext h)
  · intro z hz
    have hzC := hzs z hz
    have hCd : MDifferentiableAt (𝓡 2) (𝓡 2) C z := C.mdifferentiableAt hn hzC
    have hCsd : MDifferentiableAt (𝓡 2) (𝓡 2) C.symm (C z) :=
      C.symm.mdifferentiableAt hn (C.map_source hzC)
    have hev : (C.symm ∘ C) =ᶠ[𝓝 z] id := by
      filter_upwards [C.open_source.mem_nhds hzC] with y hy
      exact C.toPartialEquiv.left_inv hy
    have hid : mfderiv (𝓡 2) (𝓡 2) (C.symm ∘ C) z = ContinuousLinearMap.id ℝ _ := by
      rw [hev.mfderiv_eq, mfderiv_id]
      ext v
      rfl
    rw [mfderiv_comp z hCsd hCd] at hid
    have hCinj : Injective (mfderiv (𝓡 2) (𝓡 2) C z) := by
      intro v v' h
      have h1 := congrArg (mfderiv (𝓡 2) (𝓡 2) C.symm (C z)) h
      have h2 : ∀ x, mfderiv (𝓡 2) (𝓡 2) C.symm (C z) (mfderiv (𝓡 2) (𝓡 2) C z x) = x :=
        fun x => congrArg (fun F => F x) hid
      rw [h2, h2] at h1
      exact h1
    have hvd : MDifferentiableAt (𝓡 2) I (Subtype.val : N₀ → Y) (C z) :=
      (hval _).mdifferentiableAt hn
    have hcomp : mfderiv (𝓡 2) I (fun z => (C z : Y)) z =
        (mfderiv (𝓡 2) I (Subtype.val : N₀ → Y) (C z)).comp (mfderiv (𝓡 2) (𝓡 2) C z) :=
      mfderiv_comp (g := (Subtype.val : N₀ → Y)) (f := C) z hvd hCd
    rw [hcomp]
    exact (hvalimm (C z)).comp hCinj
  · intro z hz
    exact ⟨(C z).2, (hCT z (hzs z hz)).2⟩
  · intro w hw
    exact congrArg Subtype.val (hCS w hw)
  · intro w hw
    exact congrArg Subtype.val (hCD w hw)
  · intro w hw
    exact hDS w hw
  · intro w hw
    exact hDη w hw

end GC.GraphManifold.Assembly.FC39P0
