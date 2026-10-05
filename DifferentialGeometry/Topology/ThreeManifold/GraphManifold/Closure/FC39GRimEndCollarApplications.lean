import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Closure.FC39GRimEndCollar

/-!
# FC39 GROUP G, RIMBOX route B: consumer of the polar end collar

Lane FC39-G-RIMBOX. `exists_polarEndDisk_GRIM`: the re-parametrized end disk `D = ι₀ ∘ d` is a
smooth injective immersion with the SAME image as `ι₀` (the actual end disk), polar near the rim
(`T (D w) = c + κ (‖w‖ − 1)`), and equal to the two-sided collar on the inner side — exactly the end
disk input of the flow handle (`exists_flowHandle_polar_GRIM`, with `B = c − T`).
-/

set_option autoImplicit false

noncomputable section

open Set Function
open DifferentialGeometry DifferentialGeometry.Topology DifferentialGeometry.Topology.Morse
open scoped Manifold ContDiff Topology

namespace GC.GraphManifold.Assembly.FC39P0

local instance diskChartsECA_GRIM : ChartedSpace (EuclideanHalfSpace 2) (ClosedCell 2) :=
  DifferentialGeometry.Topology.Handle.closedCellChartedSpaceSucc 1

local instance diskSmoothECA_GRIM : IsManifold (𝓡∂ 2) ∞ (ClosedCell 2) :=
  DifferentialGeometry.Topology.Handle.closedCellIsManifold 1

variable {H Y : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ (MorseModel 3) H}
  [I.Boundaryless] [TopologicalSpace Y] [ChartedSpace H Y] [IsManifold I ∞ Y] [T2Space Y]

/-- **The polar end disk**: same image as the old end disk, polar near the rim, equal to the
two-sided collar on the inner side. -/
theorem exists_polarEndDisk_GRIM {g T : Y → ℝ} (hg : ContMDiff I 𝓘(ℝ, ℝ) ∞ g)
    (hT : ContMDiff I 𝓘(ℝ, ℝ) ∞ T) (hgr : ∀ y, g y = 0 → mfderiv I 𝓘(ℝ, ℝ) g y ≠ 0)
    (ι₀ : ClosedCell 2 → Y) (hι₀ : ContMDiff (𝓡∂ 2) I ∞ ι₀) (hι₀inj : Injective ι₀)
    (hι₀imm : ∀ w, Injective (mfderiv (𝓡∂ 2) I ι₀ w)) (hι₀g : ∀ w, g (ι₀ w) = 0) {c : ℝ}
    (hTc : ∀ w : ClosedCell 2, ‖(w : EuclideanSpace ℝ (Fin 2))‖ = 1 → T (ι₀ w) = c)
    (hTle : ∀ w, T (ι₀ w) ≤ c)
    (hpair : ∀ w : ClosedCell 2, ‖(w : EuclideanSpace ℝ (Fin 2))‖ = 1 →
      Surjective (mfderiv I 𝓘(ℝ, ℝ × ℝ) (fun y => (g y, T y)) (ι₀ w)))
    {κ : ℝ} (hκ : 0 < κ) {η : ℝ} (hη0 : 0 < η) (hη1 : η < 1) :
    ∃ δ : ℝ, 0 < δ ∧ δ < η ∧ ∃ D : ClosedCell 2 → Y,
      ContMDiff (𝓡∂ 2) I ∞ D ∧ Injective D ∧ (∀ w, Injective (mfderiv (𝓡∂ 2) I D w)) ∧
      range D = range ι₀ ∧
      (∀ w : ClosedCell 2, 1 - δ < ‖(w : EuclideanSpace ℝ (Fin 2))‖ →
        T (D w) = c + κ * (‖(w : EuclideanSpace ℝ (Fin 2))‖ - 1)) ∧
      ∃ C : EuclideanSpace ℝ (Fin 2) → Y, ContMDiffOn (𝓡 2) I ∞ C {z | |‖z‖ - 1| < δ} ∧
        InjOn C {z | |‖z‖ - 1| < δ} ∧
        (∀ z, |‖z‖ - 1| < δ → Injective (mfderiv (𝓡 2) I C z)) ∧
        (∀ z, |‖z‖ - 1| < δ → g (C z) = 0 ∧ T (C z) = c + κ * (‖z‖ - 1)) ∧
        ∀ w : ClosedCell 2, 1 - δ < ‖(w : EuclideanSpace ℝ (Fin 2))‖ → D w = C w := by
  obtain ⟨δ, hδ0, hδη, d, C, hCs, hCinj, hCimm, hCT, -, hCD, -, -⟩ :=
    exists_polarEndCollar_GRIM hg hT hgr ι₀ hι₀ hι₀inj hι₀imm hι₀g hTc hTle hpair hκ hη0 hη1
  have hn : (∞ : WithTop ℕ∞) ≠ 0 := by simp
  refine ⟨δ, hδ0, hδη, ι₀ ∘ d, hι₀.comp d.contMDiff, hι₀inj.comp d.injective, fun w => ?_, ?_,
    fun w hw => ?_, C, hCs, hCinj, hCimm, hCT, fun w hw => hCD w hw⟩
  · rw [mfderiv_comp w ((hι₀ _).mdifferentiableAt hn) ((d.contMDiff w).mdifferentiableAt hn)]
    exact (hι₀imm (d w)).comp ((d.isLocalDiffeomorph w).mfderivToContinuousLinearEquiv hn).injective
  · have hd : range d = univ := range_eq_univ.mpr fun x => ⟨d.symm x, d.apply_symm_apply x⟩
    rw [range_comp, hd, image_univ]
  · change T (ι₀ (d w)) = _
    rw [hCD w hw]
    have hz : |‖(w : EuclideanSpace ℝ (Fin 2))‖ - 1| < δ := by
      rw [abs_lt]
      exact ⟨by linarith, by linarith [w.2]⟩
    exact (hCT _ hz).2

end GC.GraphManifold.Assembly.FC39P0
