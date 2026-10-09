import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Closure.FC39GRimEdgeSlab
import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Closure.FC39GRimEndCollar
import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Closure.AssemblySeamCollar
import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Closure.AssemblyDiskSmale

/-!
# FC39 GROUP G, RIMBOX route B (sheet §4, binding G5c part 1): the polar end disk in the edge slab

Lane FC39-G-RIMBOX, dispositions D62-6. For an interval component `i` of the edge export with its
two-sided axial coordinate `φ` (`FC39GRimAxialCoordinate.lean`), on the boundaryless edge-slab
interior `Y` (`edgeSlab_GRIM`, interior charts): POLAR-2 on the slice `{φ ∘ proj = 0}` applied to the
OLD end disk `ι₀ = intervalTriv i (·, 0)` (K2, `exists_polarEndCollar_GRIM` with the model
`interiorSeamModel`), transported back to `𝓘(ℝ, ℝ³)` (`ContinuousLinearEquiv.toTransContinuousLinearEquiv`),
gives the NEW end disk `D` with the same image (the whole end disk), polar near the rim, whose height
is the level exactly on the rim, and the two-sided collar `C` with the inner matching `D = C`
(`edgeSlab_polarEndDisk_GRIM`). Derivatives move carrier → interior (`mfderiv_interiorAtlas`) →
seam (`mfderiv_transContinuousLinearEquiv`); `rank_two` gives the slice regularity at the rim.
-/

set_option autoImplicit false

noncomputable section

open Set Function
open DifferentialGeometry DifferentialGeometry.Topology GC.Endpoint GC.Seifert GC.GraphManifold
open Manifold
open scoped Manifold ContDiff Topology

universe u

namespace GC.GraphManifold.Assembly.FC39P0

local instance diskChartsSED_GRIM : ChartedSpace (EuclideanHalfSpace 2) (ClosedCell 2) :=
  DifferentialGeometry.Topology.Handle.closedCellChartedSpaceSucc 1

local instance diskSmoothSED_GRIM : IsManifold (𝓡∂ 2) ∞ (ClosedCell 2) :=
  DifferentialGeometry.Topology.Handle.closedCellIsManifold 1

variable {W : CompactCarrier.{u}}

/-- The carrier-model derivative of the axial coordinate on the slab. -/
theorem edgeSlab_mfderiv_axial_GRIM (P : EdgeBundle W) {V : Set P.Base} (hV : IsOpen V)
    {φ : P.Base → ℝ} (hφ : ContMDiffOn (𝓡 1) 𝓘(ℝ, ℝ) ∞ φ V)
    (y : W.pieceInterior (edgeSlab_GRIM P V hV)) :
    mfderiv W.model 𝓘(ℝ, ℝ) (fun y => φ (P.proj (edgeSlabIncl_GRIM P V hV y))) y =
      (mfderiv (𝓡 1) 𝓘(ℝ, ℝ) φ (P.proj (edgeSlabIncl_GRIM P V hV y))).comp
        (mfderiv W.model (𝓡 1) P.proj (edgeSlabIncl_GRIM P V hV y)) := by
  have hn : (∞ : WithTop ℕ∞) ≠ 0 := by simp
  have hι : ContMDiff W.model W.model ∞ (edgeSlabIncl_GRIM P V hV) := contMDiff_inclusion _
  have hpV : P.proj (edgeSlabIncl_GRIM P V hV y) ∈ V := y.2.1.snd
  have hφd : MDifferentiableAt (𝓡 1) 𝓘(ℝ, ℝ) φ (P.proj (edgeSlabIncl_GRIM P V hV y)) :=
    (hφ.contMDiffAt (hV.mem_nhds hpV)).mdifferentiableAt hn
  have hpd : MDifferentiableAt W.model (𝓡 1) P.proj (edgeSlabIncl_GRIM P V hV y) :=
    (P.proj_smooth _).mdifferentiableAt hn
  have hιd : MDifferentiableAt W.model W.model (edgeSlabIncl_GRIM P V hV) y :=
    (hι y).mdifferentiableAt hn
  change mfderiv W.model 𝓘(ℝ, ℝ) (φ ∘ P.proj ∘ edgeSlabIncl_GRIM P V hV) y = _
  rw [mfderiv_comp y hφd (hpd.comp y hιd), mfderiv_comp y hpd hιd,
    DifferentialGeometry.mfderiv_opens_incl]
  rfl

/-- The carrier-model derivative of the height on the slab. -/
theorem edgeSlab_mfderiv_height_GRIM (P : EdgeBundle W) {V : Set P.Base} (hV : IsOpen V)
    (y : W.pieceInterior (edgeSlab_GRIM P V hV)) :
    mfderiv W.model 𝓘(ℝ, ℝ) (fun y => P.height (edgeSlabIncl_GRIM P V hV y)) y =
      mfderiv W.model 𝓘(ℝ, ℝ) P.height (edgeSlabIncl_GRIM P V hV y) := by
  have hn : (∞ : WithTop ℕ∞) ≠ 0 := by simp
  have hhd : MDifferentiableAt W.model 𝓘(ℝ, ℝ) P.height (edgeSlabIncl_GRIM P V hV y) :=
    (P.height_smooth _).mdifferentiableAt hn
  have hιd : MDifferentiableAt W.model W.model (edgeSlabIncl_GRIM P V hV) y :=
    ((contMDiff_inclusion (pieceInterior_edgeSlab_le_GRIM P V hV)) y).mdifferentiableAt hn
  change mfderiv W.model 𝓘(ℝ, ℝ) (P.height ∘ edgeSlabIncl_GRIM P V hV) y = _
  rw [mfderiv_comp y hhd hιd, DifferentialGeometry.mfderiv_opens_incl]
  rfl

/-- **The polar end disk of an interval component in its edge slab** (binding of K2): same image as
the old end disk, polar near the rim, height = level exactly on the rim, two-sided collar with the
inner matching. -/
theorem edgeSlab_polarEndDisk_GRIM {P : EdgeBundle W} (M : EdgeComponentModels P)
    (i : Fin M.intervalCount) {V : Set P.Base} (hV : IsOpen V) {φ : P.Base → ℝ}
    (hφ : ContMDiffOn (𝓡 1) 𝓘(ℝ, ℝ) ∞ φ V)
    (hφs : ∀ c ∈ V, Surjective (mfderiv (𝓡 1) 𝓘(ℝ, ℝ) φ c)) (hφinj : InjOn φ V)
    (hφβ : ∀ t, φ (M.intervalBase i t) = t) (hβV : range (M.intervalBase i) ⊆ V)
    {κ η : ℝ} (hκ : 0 < κ) (hη0 : 0 < η) (hη1 : η < 1) :
    let _ := DifferentialGeometry.Manifold.interiorChartedSpace W.model ∞
      (M := W.pieceInterior (edgeSlab_GRIM P V hV))
    ∃ δ : ℝ, 0 < δ ∧ δ < η ∧
      ∃ D : ClosedCell 2 → W.pieceInterior (edgeSlab_GRIM P V hV),
        ContMDiff (𝓡∂ 2) 𝓘(ℝ, EuclideanSpace ℝ (Fin 3)) ∞ D ∧ Injective D ∧
        (∀ w, Injective (mfderiv (𝓡∂ 2) 𝓘(ℝ, EuclideanSpace ℝ (Fin 3)) D w)) ∧
        (∀ w, φ (P.proj (edgeSlabIncl_GRIM P V hV (D w))) = 0 ∧
          P.height (edgeSlabIncl_GRIM P V hV (D w)) ≤ P.level) ∧
        (∀ y, φ (P.proj (edgeSlabIncl_GRIM P V hV y)) = 0 →
          P.height (edgeSlabIncl_GRIM P V hV y) ≤ P.level → ∃ w, D w = y) ∧
        (∀ w : ClosedCell 2, 1 - δ < ‖(w : EuclideanSpace ℝ (Fin 2))‖ →
          P.height (edgeSlabIncl_GRIM P V hV (D w)) =
            P.level + κ * (‖(w : EuclideanSpace ℝ (Fin 2))‖ - 1)) ∧
        (∀ w : ClosedCell 2, P.height (edgeSlabIncl_GRIM P V hV (D w)) = P.level →
          ‖(w : EuclideanSpace ℝ (Fin 2))‖ = 1) ∧
        ∃ C : EuclideanSpace ℝ (Fin 2) → W.pieceInterior (edgeSlab_GRIM P V hV),
          ContMDiffOn (𝓡 2) 𝓘(ℝ, EuclideanSpace ℝ (Fin 3)) ∞ C {z | |‖z‖ - 1| < δ} ∧
          InjOn C {z | |‖z‖ - 1| < δ} ∧
          (∀ z, |‖z‖ - 1| < δ →
            Injective (mfderiv (𝓡 2) 𝓘(ℝ, EuclideanSpace ℝ (Fin 3)) C z)) ∧
          (∀ z, |‖z‖ - 1| < δ → φ (P.proj (edgeSlabIncl_GRIM P V hV (C z))) = 0 ∧
            P.height (edgeSlabIncl_GRIM P V hV (C z)) = P.level + κ * (‖z‖ - 1)) ∧
          ∀ w : ClosedCell 2, 1 - δ < ‖(w : EuclideanSpace ℝ (Fin 2))‖ → D w = C w := by
  intro _
  have hn : (∞ : WithTop ℕ∞) ≠ 0 := by simp
  have _ : IsManifold 𝓘(ℝ, EuclideanSpace ℝ (Fin 3)) ∞ (W.pieceInterior (edgeSlab_GRIM P V hV)) :=
    DifferentialGeometry.Manifold.interiorIsManifold W.model ∞
  have hιs : ContMDiff W.model W.model ∞ (edgeSlabIncl_GRIM P V hV) := contMDiff_inclusion _
  have hpV : ∀ y : W.pieceInterior (edgeSlab_GRIM P V hV),
      P.proj (edgeSlabIncl_GRIM P V hV y) ∈ V := fun y => y.2.1.snd
  have hgW : ContMDiff W.model 𝓘(ℝ, ℝ) ∞
      (fun y : W.pieceInterior (edgeSlab_GRIM P V hV) => φ (P.proj (edgeSlabIncl_GRIM P V hV y))) :=
    fun y => (hφ.contMDiffAt (hV.mem_nhds (hpV y))).comp y ((P.proj_smooth.comp hιs) y)
  have hTW : ContMDiff W.model 𝓘(ℝ, ℝ) ∞
      (fun y : W.pieceInterior (edgeSlab_GRIM P V hV) => P.height (edgeSlabIncl_GRIM P V hV y)) :=
    P.height_smooth.comp hιs
  have hid := DifferentialGeometry.Manifold.contMDiff_interiorAtlas_id W.model ∞
    (M := W.pieceInterior (edgeSlab_GRIM P V hV))
  have hgE := hgW.comp hid
  have hTE := hTW.comp hid
  have hgS : ContMDiff interiorSeamModel 𝓘(ℝ, ℝ) ∞
      (fun y : W.pieceInterior (edgeSlab_GRIM P V hV) => φ (P.proj (edgeSlabIncl_GRIM P V hV y))) :=
    interiorSeamRechart.contMDiff_transContinuousLinearEquiv_left.mpr hgE
  have hTS : ContMDiff interiorSeamModel 𝓘(ℝ, ℝ) ∞
      (fun y : W.pieceInterior (edgeSlab_GRIM P V hV) => P.height (edgeSlabIncl_GRIM P V hV y)) :=
    interiorSeamRechart.contMDiff_transContinuousLinearEquiv_left.mpr hTE
  -- derivative transfer: seam ← interior ← carrier
  have hSW : ∀ {F : Type} [NormedAddCommGroup F] [NormedSpace ℝ F]
      (f : W.pieceInterior (edgeSlab_GRIM P V hV) → F)
      (hf : ContMDiff W.model 𝓘(ℝ, F) ∞ f) (y : W.pieceInterior (edgeSlab_GRIM P V hV))
      (v : DifferentialGeometry.Topology.Morse.MorseModel 3),
      mfderiv interiorSeamModel 𝓘(ℝ, F) f y v =
        mfderiv W.model 𝓘(ℝ, F) f y (interiorSeamRechart.symm v) := by
    intro F _ _ f hf y v
    have hE : MDifferentiableAt 𝓘(ℝ, EuclideanSpace ℝ (Fin 3)) 𝓘(ℝ, F) f y :=
      ((hf.comp hid) y).mdifferentiableAt hn
    rw [DifferentialGeometry.Manifold.mfderiv_transContinuousLinearEquiv
      𝓘(ℝ, EuclideanSpace ℝ (Fin 3)) interiorSeamRechart hE]
    have h := DifferentialGeometry.Manifold.mfderiv_interiorAtlas W.model hf y
    exact congrArg (fun L : EuclideanSpace ℝ (Fin 3) →L[ℝ] F => L (interiorSeamRechart.symm v)) h
  -- regularity of the axial coordinate (seam model)
  have hgsurjW : ∀ y : W.pieceInterior (edgeSlab_GRIM P V hV),
      Surjective (mfderiv W.model 𝓘(ℝ, ℝ)
        (fun y => φ (P.proj (edgeSlabIncl_GRIM P V hV y))) y) := by
    intro y
    rw [edgeSlab_mfderiv_axial_GRIM P hV hφ y]
    exact (hφs _ (hpV y)).comp (P.proj_submersion _)
  have hgr : ∀ y : W.pieceInterior (edgeSlab_GRIM P V hV),
      (fun y => φ (P.proj (edgeSlabIncl_GRIM P V hV y))) y = 0 →
      mfderiv interiorSeamModel 𝓘(ℝ, ℝ)
        (fun y => φ (P.proj (edgeSlabIncl_GRIM P V hV y))) y ≠ 0 := by
    intro y _ h0
    obtain ⟨u, hu⟩ := hgsurjW y 1
    have h1 := hSW _ hgW y (interiorSeamRechart u)
    rw [h0] at h1
    have e : interiorSeamRechart.symm (interiorSeamRechart u) = u :=
      interiorSeamRechart.symm_apply_apply u
    rw [e, hu] at h1
    have h2 : (0 : ℝ) = 1 := h1
    exact absurd h2 (by norm_num)
  -- the old end disk in the slab
  set H₀ := M.intervalTriv i with hH₀
  have hs₀ : ContMDiff (𝓡∂ 2) W.model ∞ (fun w : ClosedCell 2 => H₀.map (w, iccEnd false)) :=
    H₀.smooth.comp (contMDiff_id.prodMk contMDiff_const)
  have hs₀Y : ∀ w : ClosedCell 2, H₀.map (w, iccEnd false) ∈ W.pieceInterior (edgeSlab_GRIM P V hV) := by
    intro w
    obtain ⟨hx, hpx⟩ := M.intervalTriv_proj i w (iccEnd false)
    refine ⟨⟨hx, ?_⟩, H₀.interior ⟨(w, iccEnd false), rfl⟩⟩
    rw [hpx]
    exact hβV ⟨_, rfl⟩
  let ι₀ : ClosedCell 2 → W.pieceInterior (edgeSlab_GRIM P V hV) := fun w => ⟨_, hs₀Y w⟩
  have hι₀ : ContMDiff (𝓡∂ 2) interiorSeamModel ∞ ι₀ :=
    contMDiff_codRestrict_interiorSeamModel W (edgeSlab_GRIM P V hV) hs₀ hs₀Y
  have hι₀inj : Injective ι₀ := by
    intro w w' h
    have := H₀.injective (congrArg Subtype.val h)
    exact (Prod.mk.inj this).1
  have hval : ContMDiff interiorSeamModel W.model ∞
      (Subtype.val : W.pieceInterior (edgeSlab_GRIM P V hV) → W.Carrier) :=
    contMDiff_val_interiorSeamModel W (edgeSlab_GRIM P V hV)
  have hs₀imm : ∀ w, Injective (mfderiv (𝓡∂ 2) W.model
      (fun w : ClosedCell 2 => H₀.map (w, iccEnd false)) w) := by
    intro w
    have hD : HasMFDerivAt (𝓡∂ 2) ((𝓡∂ 2).prod (𝓡∂ 1))
        (fun w : ClosedCell 2 => (w, iccEnd false)) w
        ((ContinuousLinearMap.id ℝ (TangentSpace (𝓡∂ 2) w)).prod 0) :=
      (hasMFDerivAt_id w).prodMk (hasMFDerivAt_const (iccEnd false) w)
    have hHd : MDifferentiableAt ((𝓡∂ 2).prod (𝓡∂ 1)) W.model H₀.map (w, iccEnd false) :=
      (H₀.smooth _).mdifferentiableAt hn
    change Injective (mfderiv (𝓡∂ 2) W.model (H₀.map ∘ fun w : ClosedCell 2 => (w, iccEnd false)) w)
    rw [mfderiv_comp w hHd hD.mdifferentiableAt, hD.mfderiv]
    intro a b hab
    have h1 := (H₀.mfderiv_bijective (w, iccEnd false)).1 hab
    exact (Prod.mk.inj h1).1
  have hι₀imm : ∀ w, Injective (mfderiv (𝓡∂ 2) interiorSeamModel ι₀ w) := by
    intro w a b hab
    apply hs₀imm w
    have hc : mfderiv (𝓡∂ 2) W.model (fun w : ClosedCell 2 => H₀.map (w, iccEnd false)) w =
        (mfderiv interiorSeamModel W.model
          (Subtype.val : W.pieceInterior (edgeSlab_GRIM P V hV) → W.Carrier) (ι₀ w)).comp
          (mfderiv (𝓡∂ 2) interiorSeamModel ι₀ w) :=
      mfderiv_comp (g := (Subtype.val : W.pieceInterior (edgeSlab_GRIM P V hV) → W.Carrier))
        (f := ι₀) w ((hval _).mdifferentiableAt hn) ((hι₀ w).mdifferentiableAt hn)
    rw [hc]
    exact congrArg (mfderiv interiorSeamModel W.model
      (Subtype.val : W.pieceInterior (edgeSlab_GRIM P V hV) → W.Carrier) (ι₀ w)) hab
  have hβ0 : φ (M.intervalBase i (iccEnd false)) = 0 := by
    rw [hφβ]
    simp [iccEnd]
  have hι₀P : ∀ w, P.proj (edgeSlabIncl_GRIM P V hV (ι₀ w)) = M.intervalBase i (iccEnd false) := by
    intro w
    obtain ⟨hx, hpx⟩ := M.intervalTriv_proj i w (iccEnd false)
    exact hpx
  have hι₀g : ∀ w, (fun y => φ (P.proj (edgeSlabIncl_GRIM P V hV y))) (ι₀ w) = 0 := by
    intro w
    change φ (P.proj (edgeSlabIncl_GRIM P V hV (ι₀ w))) = 0
    rw [hι₀P, hβ0]
  have hTc : ∀ w : ClosedCell 2, ‖(w : EuclideanSpace ℝ (Fin 2))‖ = 1 →
      (fun y => P.height (edgeSlabIncl_GRIM P V hV y)) (ι₀ w) = P.level := by
    intro w hw
    have hmem : H₀.map (w, iccEnd false) ∈ P.rim (M.intervalBase i (iccEnd false)) := by
      rw [← M.intervalTriv_rim i (iccEnd false)]
      exact ⟨w, mem_diskRim_iff.mpr hw, rfl⟩
    obtain ⟨x, ⟨-, hxl⟩, hxv⟩ := hmem
    have hxe : x = edgeSlabIncl_GRIM P V hV (ι₀ w) := Subtype.ext hxv
    change P.height (edgeSlabIncl_GRIM P V hV (ι₀ w)) = P.level
    rw [← hxe]
    exact hxl
  have hTle : ∀ w, (fun y => P.height (edgeSlabIncl_GRIM P V hV y)) (ι₀ w) ≤ P.level := by
    intro w
    have hmem : H₀.map (w, iccEnd false) ∈ P.disk (M.intervalBase i (iccEnd false)) := by
      rw [← M.intervalTriv_disk i (iccEnd false)]
      exact ⟨w, rfl⟩
    obtain ⟨x, ⟨-, hxl⟩, hxv⟩ := hmem
    have hxe : x = edgeSlabIncl_GRIM P V hV (ι₀ w) := Subtype.ext hxv
    change P.height (edgeSlabIncl_GRIM P V hV (ι₀ w)) ≤ P.level
    rw [← hxe]
    exact hxl
  -- the pair (g, T) is submersive at the rim (rank_two)
  have hpairW : ContMDiff W.model 𝓘(ℝ, ℝ × ℝ) ∞
      (fun y : W.pieceInterior (edgeSlab_GRIM P V hV) =>
        (φ (P.proj (edgeSlabIncl_GRIM P V hV y)), P.height (edgeSlabIncl_GRIM P V hV y))) :=
    hgW.prodMk_space hTW
  have hpair : ∀ w : ClosedCell 2, ‖(w : EuclideanSpace ℝ (Fin 2))‖ = 1 →
      Surjective (mfderiv interiorSeamModel 𝓘(ℝ, ℝ × ℝ)
        (fun y => ((fun y => φ (P.proj (edgeSlabIncl_GRIM P V hV y))) y,
          (fun y => P.height (edgeSlabIncl_GRIM P V hV y)) y)) (ι₀ w)) := by
    intro w hw
    set y := ι₀ w with hy
    have hpd : MDifferentiableAt W.model 𝓘(ℝ, ℝ × ℝ)
        (fun y : W.pieceInterior (edgeSlab_GRIM P V hV) =>
          (φ (P.proj (edgeSlabIncl_GRIM P V hV y)), P.height (edgeSlabIncl_GRIM P V hV y))) y :=
      (hpairW y).mdifferentiableAt hn
    have hfst : ∀ u, (mfderiv W.model 𝓘(ℝ, ℝ × ℝ)
        (fun y : W.pieceInterior (edgeSlab_GRIM P V hV) =>
          (φ (P.proj (edgeSlabIncl_GRIM P V hV y)), P.height (edgeSlabIncl_GRIM P V hV y))) y u).1 =
        mfderiv W.model 𝓘(ℝ, ℝ) (fun y => φ (P.proj (edgeSlabIncl_GRIM P V hV y))) y u := by
      intro u
      have hfd : MDifferentiableAt 𝓘(ℝ, ℝ × ℝ) 𝓘(ℝ, ℝ) (Prod.fst : ℝ × ℝ → ℝ)
          (φ (P.proj (edgeSlabIncl_GRIM P V hV y)), P.height (edgeSlabIncl_GRIM P V hV y)) :=
        ((contDiff_fst.contMDiff) _).mdifferentiableAt hn
      have := mfderiv_comp y hfd hpd
      have hc : (Prod.fst ∘ fun y : W.pieceInterior (edgeSlab_GRIM P V hV) =>
          (φ (P.proj (edgeSlabIncl_GRIM P V hV y)), P.height (edgeSlabIncl_GRIM P V hV y))) =
          fun y => φ (P.proj (edgeSlabIncl_GRIM P V hV y)) := rfl
      rw [hc, mfderiv_eq_fderiv, fderiv_fst] at this
      rw [this]
      rfl
    have hsnd : ∀ u, (mfderiv W.model 𝓘(ℝ, ℝ × ℝ)
        (fun y : W.pieceInterior (edgeSlab_GRIM P V hV) =>
          (φ (P.proj (edgeSlabIncl_GRIM P V hV y)), P.height (edgeSlabIncl_GRIM P V hV y))) y u).2 =
        mfderiv W.model 𝓘(ℝ, ℝ) (fun y => P.height (edgeSlabIncl_GRIM P V hV y)) y u := by
      intro u
      have hsd : MDifferentiableAt 𝓘(ℝ, ℝ × ℝ) 𝓘(ℝ, ℝ) (Prod.snd : ℝ × ℝ → ℝ)
          (φ (P.proj (edgeSlabIncl_GRIM P V hV y)), P.height (edgeSlabIncl_GRIM P V hV y)) :=
        ((contDiff_snd.contMDiff) _).mdifferentiableAt hn
      have := mfderiv_comp y hsd hpd
      have hc : (Prod.snd ∘ fun y : W.pieceInterior (edgeSlab_GRIM P V hV) =>
          (φ (P.proj (edgeSlabIncl_GRIM P V hV y)), P.height (edgeSlabIncl_GRIM P V hV y))) =
          fun y => P.height (edgeSlabIncl_GRIM P V hV y) := rfl
      rw [hc, mfderiv_eq_fderiv, fderiv_snd] at this
      rw [this]
      rfl
    rintro ⟨r, u⟩
    obtain ⟨w', hw'⟩ := hφs _ (hpV y) r
    obtain ⟨v₀, hv₀⟩ := P.rank_two (edgeSlabIncl_GRIM P V hV y) (hTc w hw) (w', u)
    obtain ⟨hv1, hv2⟩ := Prod.mk.inj hv₀
    refine ⟨interiorSeamRechart v₀, ?_⟩
    have e : interiorSeamRechart.symm (interiorSeamRechart v₀) = v₀ :=
      interiorSeamRechart.symm_apply_apply v₀
    rw [hSW _ hpairW y, e]
    refine Prod.ext ((hfst v₀).trans ?_) ((hsnd v₀).trans ?_)
    · rw [edgeSlab_mfderiv_axial_GRIM P hV hφ y]
      change mfderiv (𝓡 1) 𝓘(ℝ, ℝ) φ _ (mfderiv W.model (𝓡 1) P.proj _ v₀) = r
      rw [hv1, hw']
    · rw [edgeSlab_mfderiv_height_GRIM P hV y]
      exact hv2
  -- POLAR-2 on the slice (K2)
  obtain ⟨δ, hδ0, hδη, d, C, hC, hCinj, hCimm, hCT, -, hCD, hdS, -⟩ :=
    exists_polarEndCollar_GRIM (I := interiorSeamModel) hgS hTS hgr ι₀ hι₀ hι₀inj hι₀imm hι₀g
      hTc hTle hpair hκ hη0 hη1
  -- back to the model 𝓘(ℝ, ℝ³)
  let Ψ := ContinuousLinearEquiv.toTransContinuousLinearEquiv (n := ∞)
    𝓘(ℝ, EuclideanSpace ℝ (Fin 3)) (W.pieceInterior (edgeSlab_GRIM P V hV)) interiorSeamRechart
  have hΨinj : ∀ y, Injective (mfderiv interiorSeamModel 𝓘(ℝ, EuclideanSpace ℝ (Fin 3)) Ψ.symm y) :=
    fun y => ((Ψ.symm.isLocalDiffeomorph y).mfderivToContinuousLinearEquiv hn).injective
  have hΨd : ∀ y, MDifferentiableAt interiorSeamModel 𝓘(ℝ, EuclideanSpace ℝ (Fin 3)) Ψ.symm y :=
    fun y => (Ψ.symm.contMDiff y).mdifferentiableAt hn
  have hannOpen : IsOpen {z : EuclideanSpace ℝ (Fin 2) | |‖z‖ - 1| < δ} :=
    isOpen_lt (continuous_abs.comp (continuous_norm.sub continuous_const)) continuous_const
  have hinner : ∀ w : ClosedCell 2, 1 - δ < ‖(w : EuclideanSpace ℝ (Fin 2))‖ →
      |‖(w : EuclideanSpace ℝ (Fin 2))‖ - 1| < δ := by
    intro w hw
    rw [abs_lt]
    exact ⟨by linarith, by linarith [w.2]⟩
  refine ⟨δ, hδ0, hδη, ι₀ ∘ d, ?_, hι₀inj.comp d.injective, ?_, ?_, ?_, ?_, ?_, C, ?_, hCinj, ?_,
    ?_, fun w hw => hCD w hw⟩
  · exact Ψ.symm.contMDiff.comp (hι₀.comp d.contMDiff)
  · intro w
    change Injective (mfderiv (𝓡∂ 2) 𝓘(ℝ, EuclideanSpace ℝ (Fin 3)) (Ψ.symm ∘ (ι₀ ∘ d)) w)
    have hdd : MDifferentiableAt (𝓡∂ 2) (𝓡∂ 2) d w := (d.contMDiff w).mdifferentiableAt hn
    have hιd : MDifferentiableAt (𝓡∂ 2) interiorSeamModel ι₀ (d w) := (hι₀ _).mdifferentiableAt hn
    rw [mfderiv_comp w (hΨd _) (hιd.comp w hdd), mfderiv_comp w hιd hdd]
    exact (hΨinj _).comp ((hι₀imm _).comp ((d.isLocalDiffeomorph w).mfderivToContinuousLinearEquiv hn).injective)
  · intro w
    exact ⟨hι₀g (d w), hTle (d w)⟩
  · intro y hy0 hyle
    have hpy : P.proj (edgeSlabIncl_GRIM P V hV y) = M.intervalBase i (iccEnd false) :=
      hφinj (hpV y) (hβV ⟨_, rfl⟩) (hy0.trans hβ0.symm)
    have hmem : (y : W.Carrier) ∈ P.disk (M.intervalBase i (iccEnd false)) :=
      ⟨edgeSlabIncl_GRIM P V hV y, ⟨hpy, hyle⟩, rfl⟩
    rw [← M.intervalTriv_disk i (iccEnd false)] at hmem
    obtain ⟨w', hw'⟩ := hmem
    refine ⟨d.symm w', ?_⟩
    change ι₀ (d (d.symm w')) = y
    rw [d.apply_symm_apply]
    exact Subtype.ext hw'
  · intro w hw
    change P.height (edgeSlabIncl_GRIM P V hV (ι₀ (d w))) = _
    rw [hCD w hw]
    exact (hCT _ (hinner w hw)).2
  · intro w hw
    change P.height (edgeSlabIncl_GRIM P V hV (ι₀ (d w))) = P.level at hw
    have hmem : H₀.map (d w, iccEnd false) ∈ P.rim (M.intervalBase i (iccEnd false)) :=
      ⟨edgeSlabIncl_GRIM P V hV (ι₀ (d w)), ⟨hι₀P (d w), hw⟩, rfl⟩
    rw [← M.intervalTriv_rim i (iccEnd false)] at hmem
    obtain ⟨w'', hw''r, hw''⟩ := hmem
    have he : w'' = d w := (Prod.mk.inj (H₀.injective hw'')).1
    have hn1 : ‖((d w : ClosedCell 2) : EuclideanSpace ℝ (Fin 2))‖ = 1 := by
      rw [← he]
      exact mem_diskRim_iff.mp hw''r
    have hfix : d (d w) = d w := hdS (d w) hn1
    have hdw : d w = w := d.injective hfix
    rw [← hdw]
    exact hn1
  · exact Ψ.symm.contMDiff.comp_contMDiffOn hC
  · intro z hz
    have hCdz : MDifferentiableAt (𝓡 2) interiorSeamModel C z :=
      (hC.contMDiffAt (hannOpen.mem_nhds hz)).mdifferentiableAt hn
    change Injective (mfderiv (𝓡 2) 𝓘(ℝ, EuclideanSpace ℝ (Fin 3)) (Ψ.symm ∘ C) z)
    rw [mfderiv_comp z (hΨd _) hCdz]
    exact (hΨinj _).comp (hCimm z hz)
  · intro z hz
    exact hCT z hz

end GC.GraphManifold.Assembly.FC39P0
