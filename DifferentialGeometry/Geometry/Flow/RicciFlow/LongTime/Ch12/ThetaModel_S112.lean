import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch12.ErrModel_O43
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch12.HadamardJets_S112
import Mathlib.Geometry.Manifold.PartitionOfUnity

/-!
# CH12-S112 G1b-prep: cutoff, the global smooth model map `Θ`, uniform jet bound

For a function `P` smooth on an open set `U ⊇ K` (`K` compact) there is `r > 0` and a globally smooth
`P'` equal to `P` on `cthickening r K ⊆ U`.  For such `P'` the map
`Θ (y, (v, N)) = β (pullbackForm (P' (y + v), 1 + N) − P' y)` is globally smooth with
`Θ (y, 0) = 0`, and has uniformly bounded derivatives on `K × closedBall 0 1`.
-/

set_option autoImplicit false

noncomputable section

open DifferentialGeometry DifferentialGeometry.Tensor0SBundle
open DifferentialGeometry.CheegerGromovCompactness
open Set Metric Filter
open scoped ContDiff Topology

namespace GC.LongTime.Ch12

local notation "E3" => EuclideanSpace ℝ (Fin 3)

/-- A globally smooth cutoff of `P` (smooth on `U`) which agrees with `P` near the compact `K ⊆ U`. -/
theorem exists_cutoff_S112 {W : Type} [NormedAddCommGroup W] [NormedSpace ℝ W]
    {K U : Set E3} (hK : IsCompact K) (hU : IsOpen U) (hKU : K ⊆ U) {P : E3 → W}
    (hP : ContDiffOn ℝ ∞ P U) :
    ∃ (r : ℝ) (P' : E3 → W), 0 < r ∧ cthickening r K ⊆ U ∧ ContDiff ℝ ∞ P' ∧
      ∀ y ∈ cthickening r K, P' y = P y := by
  obtain ⟨d, hd, hdU⟩ := hK.exists_cthickening_subset_open hU hKU
  have hr : 0 < d / 3 := by positivity
  have hts : cthickening (d / 3) K ⊆ thickening (2 * (d / 3)) K :=
    cthickening_subset_thickening' (by positivity) (by linarith) K
  obtain ⟨χ, hχ, -, hsupp, hχ1⟩ := exists_contDiff_support_eq_eq_one_iff (n := ⊤)
    (isOpen_thickening (δ := 2 * (d / 3)) (E := K)) isClosed_cthickening hts
  have htsupp : tsupport χ ⊆ U := by
    rw [tsupport, hsupp]
    exact (closure_thickening_subset_cthickening _ _).trans
      ((cthickening_mono (by linarith) K).trans hdU)
  refine ⟨d / 3, fun y => χ y • P y, hr, (cthickening_mono (by linarith) K).trans hdU, ?_, ?_⟩
  · rw [contDiff_iff_contDiffAt]
    intro y
    by_cases hy : y ∈ U
    · exact hχ.contDiffAt.smul ((hP.contDiffAt (hU.mem_nhds hy)))
    · have hyχ : y ∉ tsupport χ := fun h => hy (htsupp h)
      have heq : (fun y => χ y • P y) =ᶠ[𝓝 y] (fun _ => (0 : W)) := by
        filter_upwards [(isClosed_tsupport χ).isOpen_compl.mem_nhds hyχ] with z hz
        rw [image_eq_zero_of_notMem_tsupport hz, zero_smul]
      exact contDiffAt_const.congr_of_eventuallyEq heq
  · intro y hy
    change χ y • P y = P y
    rw [(hχ1 y).1 hy, one_smul]

/-- The global model map. -/
def thetaS112 (P' : E3 → (E3 →L[ℝ] E3 →L[ℝ] ℝ)) :
    E3 × (E3 × (E3 →L[ℝ] E3)) → Tensor0SModel 2 ℝ E3 := fun p =>
  bilinearTensor02_O43 (pullbackForm (P' (p.1 + p.2.1), ContinuousLinearMap.id ℝ E3 + p.2.2) -
    P' p.1)

theorem thetaS112_contDiff {P' : E3 → (E3 →L[ℝ] E3 →L[ℝ] ℝ)} (hP' : ContDiff ℝ ∞ P') :
    ContDiff ℝ ∞ (thetaS112 P') := by
  unfold thetaS112
  refine bilinearTensor02_contDiff_O43.comp (ContDiff.sub ?_ (hP'.comp contDiff_fst))
  refine pullbackForm.contDiff.comp (ContDiff.prodMk ?_ ?_)
  · exact hP'.comp (contDiff_fst.add (contDiff_fst.comp contDiff_snd))
  · exact contDiff_const.add (contDiff_snd.comp contDiff_snd)

theorem thetaS112_zero (P' : E3 → (E3 →L[ℝ] E3 →L[ℝ] ℝ)) (y : E3) :
    thetaS112 P' (y, 0) = 0 := by
  have h : pullbackForm (P' (y + 0), ContinuousLinearMap.id ℝ E3 + 0) = P' y := by
    ext v w
    simp [pullbackForm_apply]
  change bilinearTensor02_O43 (pullbackForm (P' (y + 0), ContinuousLinearMap.id ℝ E3 + 0) -
    P' y) = 0
  rw [h, sub_self]
  unfold bilinearTensor02_O43
  rw [ContinuousLinearMap.comp_zero]
  ext m
  simp [ContinuousLinearMap.uncurryLeft_apply]

/-- Uniform bound of the derivatives of a smooth map on `K × closedBall 0 1`. -/
theorem exists_jet_bound_S112 {Z W : Type} [NormedAddCommGroup Z] [NormedSpace ℝ Z] [ProperSpace Z]
    [NormedAddCommGroup W] [NormedSpace ℝ W] {Θ : E3 × Z → W} (hΘ : ContDiff ℝ ∞ Θ)
    {K : Set E3} (hK : IsCompact K) (k : ℕ) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ i ≤ k + 1, ∀ y ∈ K, ∀ z : Z, ‖z‖ ≤ 1 →
      ‖iteratedFDeriv ℝ i Θ (y, z)‖ ≤ M := by
  have hS : IsCompact (K ×ˢ closedBall (0 : Z) 1) := hK.prod (isCompact_closedBall _ _)
  have hb : ∀ i : ℕ, ∃ B : ℝ, ∀ p ∈ K ×ˢ closedBall (0 : Z) 1, ‖iteratedFDeriv ℝ i Θ p‖ ≤ B :=
    fun i => hS.exists_bound_of_continuousOn
      (hΘ.continuous_iteratedFDeriv (by exact_mod_cast le_top)).continuousOn
  choose B hB using hb
  refine ⟨∑ i ∈ Finset.range (k + 2), |B i|, Finset.sum_nonneg fun _ _ => abs_nonneg _,
    fun i hi y hy z hz => ?_⟩
  have h1 := hB i (y, z) ⟨hy, by simpa using hz⟩
  refine h1.trans ((le_abs_self _).trans ?_)
  exact Finset.single_le_sum (f := fun j => |B j|) (fun _ _ => abs_nonneg _)
    (Finset.mem_range.2 (by omega))

end GC.LongTime.Ch12
