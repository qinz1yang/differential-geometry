import DifferentialGeometry.Geometry.Collapse.CircleFiberKernel
import DifferentialGeometry.Topology.Ehresmann.LineBallTrivialization

/-!
# LFR20 item 2, kernel: a submersion to an interval with an enclosure is a trivial bundle

Blueprint LFR20 (master207A:26358), item 2 and step 4 ("properness traps the trajectories"). Abstract
form: `η` is a smooth real function on an open set `W` of a smooth manifold, with nonzero
differential wherever `|η| < r`, and the part of `W` where `|η| < r` lies in a compact `K ⊆ W`.

* `realSlabOpens`, `realSlabMap`: the slab `W ∩ η⁻¹(-r, r)` and `η` on it, as a map to the open interval
  `lineBallOpens r`;
* `contMDiff_realSlabMap`, `mfderiv_realSlabMap`, `surjective_mfderiv_realSlabMap`, `isProperMap_realSlabMap`;
* `exists_trivial_proper_slab_of_enclosure`: the restriction is a smooth proper submersion, trivial
  over every `(-R, R)`, `R < r`, with fibre the zero fibre.
-/

set_option autoImplicit false

noncomputable section

open Set Function Metric
open scoped ContDiff Manifold Topology

namespace DifferentialGeometry.Geometry.Collapse

open DifferentialGeometry.Topology.Ehresmann DifferentialGeometry.Topology.Manifold

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace H] [TopologicalSpace M] [ChartedSpace H M] {I : ModelWithCorners ℝ E H}

/-- The slab `W ∩ η⁻¹(-r, r)` as an open set. -/
def realSlabOpens (W : Set M) (hW : IsOpen W) (η : M → ℝ) (hη : ContinuousOn η W) (r : ℝ) :
    TopologicalSpace.Opens M :=
  ⟨W ∩ η ⁻¹' ball 0 r, hη.isOpen_inter_preimage hW isOpen_ball⟩

theorem mem_realSlabOpens_iff {W : Set M} {hW : IsOpen W} {η : M → ℝ} {hη : ContinuousOn η W}
    {r : ℝ} {x : M} : x ∈ realSlabOpens W hW η hη r ↔ x ∈ W ∧ |η x| < r := by
  change x ∈ W ∧ η x ∈ ball (0 : ℝ) r ↔ _
  rw [mem_ball, dist_zero_right, Real.norm_eq_abs]

/-- `η` restricted to the slab, as a map to the open interval `(-r, r)`. -/
def realSlabMap (W : Set M) (hW : IsOpen W) (η : M → ℝ) (hη : ContinuousOn η W) (r : ℝ) :
    realSlabOpens W hW η hη r → lineBallOpens r :=
  fun x => ⟨η x, mem_lineBallOpens_iff.mpr (mem_realSlabOpens_iff.mp x.2).2⟩

theorem realSlabMap_coe (W : Set M) (hW : IsOpen W) (η : M → ℝ) (hη : ContinuousOn η W) (r : ℝ)
    (x : realSlabOpens W hW η hη r) : (realSlabMap W hW η hη r x : ℝ) = η x :=
  rfl

theorem continuous_realSlabMap {W : Set M} (hW : IsOpen W) {η : M → ℝ} (hη : ContinuousOn η W)
    (r : ℝ) : Continuous (realSlabMap W hW η hη r) :=
  (hη.comp_continuous continuous_subtype_val (fun x => x.2.1)).subtype_mk _

theorem contMDiff_realSlabMap {W : Set M} (hW : IsOpen W) {η : M → ℝ}
    (hη : ContMDiffOn I 𝓘(ℝ, ℝ) ∞ η W) (r : ℝ) :
    ContMDiff I 𝓘(ℝ, ℝ) ∞ (realSlabMap W hW η hη.continuousOn r) := by
  apply (ContMDiff.subtypeVal_comp_iff (lineBallOpens r) _).mp
  exact hη.comp_contMDiff contMDiff_subtype_val (fun x => x.2.1)

theorem mfderiv_realSlabMap {W : Set M} (hW : IsOpen W) {η : M → ℝ}
    (hη : ContMDiffOn I 𝓘(ℝ, ℝ) ∞ η W) (r : ℝ) (x : realSlabOpens W hW η hη.continuousOn r) :
    mfderiv I 𝓘(ℝ, ℝ) (realSlabMap W hW η hη.continuousOn r) x = mfderiv I 𝓘(ℝ, ℝ) η x.1 := by
  set f := realSlabMap W hW η hη.continuousOn r
  have hfd : MDifferentiableAt I 𝓘(ℝ, ℝ) f x :=
    ((contMDiff_realSlabMap hW hη r) x).mdifferentiableAt (by simp)
  have hηd : MDifferentiableAt I 𝓘(ℝ, ℝ) η x.1 :=
    ((hη x.1 x.2.1).contMDiffAt (hW.mem_nhds x.2.1)).mdifferentiableAt (by simp)
  have h1 : HasMFDerivAt I 𝓘(ℝ, ℝ) (Subtype.val ∘ f) x
      ((ContinuousLinearMap.id ℝ ℝ).comp (mfderiv I 𝓘(ℝ, ℝ) f x)) :=
    (DifferentialGeometry.hasMFDerivAt_subtype_val (I := 𝓘(ℝ, ℝ)) (lineBallOpens r)
      (f x)).comp x hfd.hasMFDerivAt
  have h2 : HasMFDerivAt I 𝓘(ℝ, ℝ) (η ∘ Subtype.val) x
      ((mfderiv I 𝓘(ℝ, ℝ) η x.1).comp (ContinuousLinearMap.id ℝ E)) :=
    hηd.hasMFDerivAt.comp x (DifferentialGeometry.hasMFDerivAt_subtype_val (I := I) _ x)
  have h1' : HasMFDerivAt I 𝓘(ℝ, ℝ) (η ∘ Subtype.val) x
      ((ContinuousLinearMap.id ℝ ℝ).comp (mfderiv I 𝓘(ℝ, ℝ) f x)) := h1
  have := hasMFDerivAt_unique h1' h2
  ext v
  exact congrArg (fun L : E →L[ℝ] ℝ => L v) this

/-- A nonzero real linear functional is surjective. -/
theorem surjective_realLinear_of_apply_ne_zero {V : Type*} [AddCommGroup V] [Module ℝ V]
    [TopologicalSpace V] {L : V →L[ℝ] ℝ} {w : V} (hw : L w ≠ 0) : Surjective L :=
  fun s => ⟨(s / L w) • w, by rw [map_smul, smul_eq_mul, div_mul_cancel₀ s hw]⟩

theorem surjective_mfderiv_realSlabMap {W : Set M} (hW : IsOpen W)
    {η : M → ℝ} (hη : ContMDiffOn I 𝓘(ℝ, ℝ) ∞ η W) {r : ℝ}
    (hreg : ∀ x ∈ W, |η x| < r → ∃ w : E, mfderiv I 𝓘(ℝ, ℝ) η x w ≠ 0)
    (x : realSlabOpens W hW η hη.continuousOn r) :
    Surjective (mfderiv I 𝓘(ℝ, ℝ) (realSlabMap W hW η hη.continuousOn r) x) := by
  rw [mfderiv_realSlabMap hW hη r x]
  obtain ⟨w, hw⟩ := hreg x.1 x.2.1 (mem_realSlabOpens_iff.mp x.2).2
  exact surjective_realLinear_of_apply_ne_zero hw

theorem isProperMap_realSlabMap [T2Space M] {W : Set M} (hW : IsOpen W) {η : M → ℝ}
    (hη : ContinuousOn η W) {r : ℝ} {K : Set M} (hK : IsCompact K) (hKW : K ⊆ W)
    (hencl : ∀ x ∈ W, |η x| < r → x ∈ K) : IsProperMap (realSlabMap W hW η hη r) := by
  rw [isProperMap_iff_isCompact_preimage]
  refine ⟨continuous_realSlabMap hW hη r, fun C hC => ?_⟩
  set f := realSlabMap W hW η hη r
  have hC' : IsCompact (Subtype.val '' C : Set ℝ) := hC.image continuous_subtype_val
  have himage : Subtype.val '' (f ⁻¹' C) = K ∩ η ⁻¹' (Subtype.val '' C) := by
    ext x
    constructor
    · rintro ⟨u, hu, rfl⟩
      have hu' := mem_realSlabOpens_iff.mp u.2
      exact ⟨hencl u.1 hu'.1 hu'.2, f u, hu, rfl⟩
    · rintro ⟨hxK, c, hc, hcx⟩
      have hxS : x ∈ realSlabOpens W hW η hη r := by
        rw [mem_realSlabOpens_iff, ← hcx]
        exact ⟨hKW hxK, mem_lineBallOpens_iff.mp c.2⟩
      refine ⟨⟨x, hxS⟩, ?_, rfl⟩
      have : f ⟨x, hxS⟩ = c := Subtype.ext hcx.symm
      change f ⟨x, hxS⟩ ∈ C
      rw [this]
      exact hc
  rw [Subtype.isCompact_iff, himage]
  exact hK.of_isClosed_subset ((hη.mono hKW).preimage_isClosed_of_isClosed hK.isClosed
    hC'.isClosed) inter_subset_left

/-- **LFR20 item 2, kernel.** Let `η` be smooth on an open set `W` of a smooth manifold, with
nonzero differential wherever `|η| < r`, and suppose the part of `W` where `|η| < r` lies in a
compact `K ⊆ W`. Then `η : W ∩ η⁻¹(-r, r) → (-r, r)` is a smooth proper submersion, trivial over
every `(-R, R)`, `0 < R < r`, with fibre the zero fibre. -/
theorem exists_trivial_proper_slab_of_enclosure [FiniteDimensional ℝ E] [I.Boundaryless]
    [IsManifold I ∞ M] [T2Space M]
    {W : Set M} (hW : IsOpen W) {η : M → ℝ} (hη : ContMDiffOn I 𝓘(ℝ, ℝ) ∞ η W) {r : ℝ}
    (hreg : ∀ x ∈ W, |η x| < r → ∃ w : E, mfderiv I 𝓘(ℝ, ℝ) η x w ≠ 0)
    {K : Set M} (hK : IsCompact K) (hKW : K ⊆ W) (hencl : ∀ x ∈ W, |η x| < r → x ∈ K) :
    let f := realSlabMap W hW η hη.continuousOn r
    ContMDiff I 𝓘(ℝ, ℝ) ∞ f ∧ (∀ x, Surjective (mfderiv I 𝓘(ℝ, ℝ) f x)) ∧ IsProperMap f ∧
      ∀ R (hR : 0 < R) (hRr : R < r),
        let y₀ : lineBallOpens r := ⟨0, zero_mem_lineBallOpens (hR.trans hRr)⟩
        let _ := regularFiberChartedSpace f y₀ (contMDiff_realSlabMap hW hη r)
          (fun x _ ↦ surjective_mfderiv_realSlabMap hW hη hreg x)
        let U : TopologicalSpace.Opens (realSlabOpens W hW η hη.continuousOn r) :=
          ⟨f ⁻¹' lineBallInner r R,
            (lineBallInner r R).isOpen.preimage (continuous_realSlabMap hW _ r)⟩
        ∃ (hy : y₀ ∈ lineBallInner r R) (Θ : Diffeomorph
            (𝓘(ℝ, Fin (Module.finrank ℝ E - Module.finrank ℝ ℝ) → ℝ).prod 𝓘(ℝ, ℝ)) I
            ({x // f x = y₀} × lineBallInner r R) U ∞),
          (∀ q, f (Θ q).1 = q.2.1) ∧ (∀ x, (Θ (x, ⟨y₀, hy⟩)).1 = x.1) := by
  intro f
  have hf : ContMDiff I 𝓘(ℝ, ℝ) ∞ f := contMDiff_realSlabMap hW hη r
  have hsub : ∀ x, Surjective (mfderiv I 𝓘(ℝ, ℝ) f x) :=
    surjective_mfderiv_realSlabMap hW hη hreg
  have hprop : IsProperMap f := isProperMap_realSlabMap hW hη.continuousOn hK hKW hencl
  have : LocallyCompactSpace (lineBallOpens r) := (lineBallOpens r).isOpen.locallyCompactSpace
  have : SigmaCompactSpace (realSlabOpens W hW η hη.continuousOn r) :=
    sigmaCompactSpace_of_isProperMap hprop
  exact ⟨hf, hsub, hprop, fun R hR hRr =>
    exists_trivialization_over_lineBall_of_proper f hf hprop hsub hR hRr⟩

end DifferentialGeometry.Geometry.Collapse
