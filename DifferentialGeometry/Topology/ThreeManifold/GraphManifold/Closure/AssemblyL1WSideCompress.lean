import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Closure.AssemblyL1WSideCapChart
import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Closure.AssemblyL1NeckBox
import DifferentialGeometry.Topology.Manifold.CollarStretch
import DifferentialGeometry.Topology.Handle.BallTwoDiskExtensionApplications

/-!
# Chapter-14 assembly, item L1, group G3b: compressing the ball side of a neck

The two-disk normalization G2 realizes the cap germs only on SOME neighbourhood of the caps, while a
cycle normal form needs a ball to agree with its neck on the whole cap region (depth `2ε`). So the
ball side of the neck is compressed toward the end disk before the ball is normalized:

* `compress l a`: the increasing profile `τ ↦ -l (G⁻¹ (-τ / l))`, `G = collarStretch a` (the tree's
  collar stretch, `Manifold/CollarStretch.lean`): the identity for `τ ≥ 0`, above the identity, and
  the translation by `l a` for `τ ≤ -l (1/2 + a)`; its inverse `compressInv l a` is explicit.
* `neckCompress N l a`: the neck `N` precomposed with `(z, τ) ↦ (z, compress l a τ)`; the handle
  side is unchanged.
* `radialCompress l a`: a radial profile of `ℝ³` equal to `1 + compress l a (r - 1)` for `r ≥ 1/4`
  and to the identity near `0` and beyond `1`; `radialCompressDiffeo` is the corresponding
  diffeomorphism of `ℝ³` (it preserves the closed unit ball). On the cap regions it is the cap chart
  read compression: `capMap b (T x) = ((capMap b x).1, compress l a (capMap b x).2)`.
-/

set_option autoImplicit false

noncomputable section

open Set Function Metric Filter
open DifferentialGeometry DifferentialGeometry.Topology GC.Endpoint Manifold
open scoped Manifold ContDiff Topology InnerProductSpace

namespace GC.GraphManifold.Assembly

open DifferentialGeometry.Topology.Manifold (collarStretch collarStretchIso)

/-! ## The compression profile -/

/-- The compression profile `τ ↦ -l (G⁻¹ (-τ / l))`, `G = collarStretch a`. -/
def compress (l : ℝ) {a : ℝ} (ha : 0 ≤ a) (τ : ℝ) : ℝ :=
  -l * (collarStretchIso ha).symm (-τ / l)

/-- The inverse of the compression profile. -/
def compressInv (l a : ℝ) (t : ℝ) : ℝ :=
  -l * collarStretch a (-t / l)

variable {l a : ℝ}

theorem compressInv_compress (hl : 0 < l) (ha : 0 ≤ a) (τ : ℝ) :
    compressInv l a (compress l ha τ) = τ := by
  have h : -(-l * (collarStretchIso ha).symm (-τ / l)) / l = (collarStretchIso ha).symm (-τ / l) := by
    field_simp
  rw [compressInv, compress, h, ← DifferentialGeometry.Topology.Manifold.collarStretchIso_apply ha,
    OrderIso.apply_symm_apply]
  field_simp

theorem compress_compressInv (hl : 0 < l) (ha : 0 ≤ a) (t : ℝ) :
    compress l ha (compressInv l a t) = t := by
  have h : -(-l * collarStretch a (-t / l)) / l = collarStretch a (-t / l) := by
    field_simp
  rw [compress, compressInv, h, ← DifferentialGeometry.Topology.Manifold.collarStretchIso_apply ha,
    OrderIso.symm_apply_apply]
  field_simp

theorem contDiff_compress (ha : 0 ≤ a) : ContDiff ℝ ∞ (compress l ha) :=
  contDiff_const.mul ((DifferentialGeometry.Topology.Manifold.contDiff_collarStretchIso_symm ha).comp
    (contDiff_id.neg.div_const l))

theorem contDiff_compressInv : ContDiff ℝ ∞ (compressInv l a) :=
  contDiff_const.mul ((DifferentialGeometry.Topology.Manifold.contDiff_collarStretch a).comp
    (contDiff_id.neg.div_const l))

theorem collarStretch_ge (ha : 0 ≤ a) (s : ℝ) : s ≤ collarStretch a s := by
  have h := mul_nonneg ha (Real.smoothTransition.nonneg (2 * s))
  unfold collarStretch
  linarith

theorem collarStretchIso_symm_le (ha : 0 ≤ a) (u : ℝ) : (collarStretchIso ha).symm u ≤ u := by
  have h := collarStretch_ge ha ((collarStretchIso ha).symm u)
  rwa [← DifferentialGeometry.Topology.Manifold.collarStretchIso_apply ha,
    OrderIso.apply_symm_apply] at h

theorem compress_of_nonneg (hl : 0 < l) (ha : 0 ≤ a) {τ : ℝ} (hτ : 0 ≤ τ) :
    compress l ha τ = τ := by
  have hu : -τ / l ≤ 0 := div_nonpos_of_nonpos_of_nonneg (by linarith) hl.le
  have hG : (collarStretchIso ha) (-τ / l) = -τ / l :=
    DifferentialGeometry.Topology.Manifold.collarStretch_of_nonpos a hu
  have h : (collarStretchIso ha).symm (-τ / l) = -τ / l := by
    conv_lhs => rw [← hG]
    exact OrderIso.symm_apply_apply _ _
  rw [compress, h]
  field_simp

theorem le_compress (hl : 0 < l) (ha : 0 ≤ a) (τ : ℝ) : τ ≤ compress l ha τ := by
  have h := collarStretchIso_symm_le ha (-τ / l)
  have h' : -l * (-τ / l) ≤ -l * (collarStretchIso ha).symm (-τ / l) :=
    mul_le_mul_of_nonpos_left h (by linarith)
  have he : -l * (-τ / l) = τ := by field_simp
  rw [compress]
  linarith

theorem compress_nonpos (hl : 0 < l) (ha : 0 ≤ a) {τ : ℝ} (hτ : τ ≤ 0) :
    compress l ha τ ≤ 0 := by
  have hu : 0 ≤ -τ / l := div_nonneg (by linarith) hl.le
  have h := DifferentialGeometry.Topology.Manifold.collarStretchIso_symm_nonneg ha hu
  rw [compress]
  nlinarith

theorem compress_eq_add (hl : 0 < l) (ha : 0 ≤ a) {τ : ℝ} (hτ : τ ≤ -l * (1 / 2 + a)) :
    compress l ha τ = τ + l * a := by
  have hu : 1 / 2 + a ≤ -τ / l := by
    rw [le_div_iff₀ hl]
    linarith
  have hG : (collarStretchIso ha) (-τ / l - a) = -τ / l := by
    rw [DifferentialGeometry.Topology.Manifold.collarStretchIso_apply,
      DifferentialGeometry.Topology.Manifold.collarStretch_of_half_le a (by linarith)]
    ring
  have h : (collarStretchIso ha).symm (-τ / l) = -τ / l - a := by
    conv_lhs => rw [← hG]
    exact OrderIso.symm_apply_apply _ _
  rw [compress, h]
  field_simp
  ring

theorem hasDerivAt_compressInv (t : ℝ) :
    HasDerivAt (compressInv l a)
      (-l * ((1 + a * (deriv Real.smoothTransition (2 * (-t / l)) * 2)) * (-1 / l))) t := by
  have h1 : HasDerivAt (fun t : ℝ => -t / l) (-1 / l) t := by
    simpa using ((hasDerivAt_id t).neg).div_const l
  have h2 := (DifferentialGeometry.Topology.Manifold.hasDerivAt_collarStretch a (-t / l)).comp t h1
  exact h2.const_mul (-l)

theorem compressInv_deriv_pos (hl : 0 < l) (ha : 0 ≤ a) (t : ℝ) :
    0 < -l * ((1 + a * (deriv Real.smoothTransition (2 * (-t / l)) * 2)) * (-1 / l)) := by
  have h : 0 ≤ deriv Real.smoothTransition (2 * (-t / l)) :=
    Real.smoothTransition.monotone.deriv_nonneg
  have h' : 0 ≤ a * (deriv Real.smoothTransition (2 * (-t / l)) * 2) :=
    mul_nonneg ha (mul_nonneg h (by norm_num))
  have he : -l * ((1 + a * (deriv Real.smoothTransition (2 * (-t / l)) * 2)) * (-1 / l)) =
      1 + a * (deriv Real.smoothTransition (2 * (-t / l)) * 2) := by
    field_simp
  rw [he]
  linarith

/-- The derivative of the compression profile is positive. -/
theorem hasDerivAt_compress (hl : 0 < l) (ha : 0 ≤ a) (τ : ℝ) :
    ∃ d : ℝ, 0 < d ∧ HasDerivAt (compress l ha) d τ := by
  have hd := hasDerivAt_compressInv (l := l) (a := a) (compress l ha τ)
  have hpos := compressInv_deriv_pos hl ha (compress l ha τ)
  refine ⟨_, inv_pos.mpr hpos, ?_⟩
  apply HasDerivAt.of_local_left_inverse (contDiff_compress ha).continuous.continuousAt hd hpos.ne'
  exact Eventually.of_forall fun t => compressInv_compress hl ha t

/-! ## The compressed neck -/

/-- The diffeomorphism `(z, τ) ↦ (z, compress l a τ)` of the neck space. -/
def neckCompressDiffeo (hl : 0 < l) (ha : 0 ≤ a) :
    (EuclideanSpace ℝ (Fin 2) × ℝ) ≃ₘ⟮𝓘(ℝ, EuclideanSpace ℝ (Fin 2) × ℝ),
      𝓘(ℝ, EuclideanSpace ℝ (Fin 2) × ℝ)⟯ (EuclideanSpace ℝ (Fin 2) × ℝ) where
  toFun q := (q.1, compress l ha q.2)
  invFun q := (q.1, compressInv l a q.2)
  left_inv q := by simp [compressInv_compress hl ha]
  right_inv q := by simp [compress_compressInv hl ha]
  contMDiff_toFun := (contDiff_fst.prodMk ((contDiff_compress ha).comp contDiff_snd)).contMDiff
  contMDiff_invFun := (contDiff_fst.prodMk (contDiff_compressInv.comp contDiff_snd)).contMDiff

/-- The neck `N` with its ball side compressed: `q ↦ N (q.1, compress l a q.2)`. -/
def neckCompress {M H' : Type*} [TopologicalSpace H'] [TopologicalSpace M] [ChartedSpace H' M]
    {I : ModelWithCorners ℝ (EuclideanSpace ℝ (Fin 3)) H'}
    (N : PartialDiffeomorph 𝓘(ℝ, EuclideanSpace ℝ (Fin 2) × ℝ) I (EuclideanSpace ℝ (Fin 2) × ℝ) M ∞)
    (hl : 0 < l) (ha : 0 ≤ a) :
    PartialDiffeomorph 𝓘(ℝ, EuclideanSpace ℝ (Fin 2) × ℝ) I (EuclideanSpace ℝ (Fin 2) × ℝ) M ∞ :=
  (neckCompressDiffeo hl ha).toPartialDiffeomorph.trans N

section neckCompress

variable {M H' : Type*} [TopologicalSpace H'] [TopologicalSpace M] [ChartedSpace H' M]
  {I : ModelWithCorners ℝ (EuclideanSpace ℝ (Fin 3)) H'}
  (N : PartialDiffeomorph 𝓘(ℝ, EuclideanSpace ℝ (Fin 2) × ℝ) I (EuclideanSpace ℝ (Fin 2) × ℝ) M ∞)
  (hl : 0 < l) (ha : 0 ≤ a)

theorem neckCompress_apply (q : EuclideanSpace ℝ (Fin 2) × ℝ) :
    neckCompress N hl ha q = N (q.1, compress l ha q.2) :=
  rfl

omit N ha in
theorem mem_neckCompress_source {N : PartialDiffeomorph 𝓘(ℝ, EuclideanSpace ℝ (Fin 2) × ℝ) I
      (EuclideanSpace ℝ (Fin 2) × ℝ) M ∞} {ha : 0 ≤ a} {q : EuclideanSpace ℝ (Fin 2) × ℝ} :
    q ∈ (neckCompress N hl ha).source ↔ (q.1, compress l ha q.2) ∈ N.source := by
  change q ∈ univ ∩ _ ↔ _
  simp only [univ_inter, mem_preimage]
  rfl

theorem neckCompress_target_subset : (neckCompress N hl ha).target ⊆ N.target :=
  fun _ hp => hp.1

end neckCompress

theorem compress_mem_Icc (hl : 0 < l) (ha : 0 ≤ a) {τ B : ℝ} (hτ : |τ| ≤ B) :
    |compress l ha τ| ≤ B := by
  rcases le_total 0 τ with h | h
  · rwa [compress_of_nonneg hl ha h]
  · have h1 := le_compress hl ha τ
    have h2 := compress_nonpos hl ha h
    rw [abs_of_nonpos h2]
    rw [abs_of_nonpos h] at hτ
    linarith

theorem neckCompress_mem_closedNeckDomain (hl : 0 < l) (ha : 0 ≤ a) {ε : ℝ}
    {q : EuclideanSpace ℝ (Fin 2) × ℝ} (hq : q ∈ closedNeckDomain ε) :
    (q.1, compress l ha q.2) ∈ closedNeckDomain ε :=
  ⟨hq.1, compress_mem_Icc hl ha hq.2⟩

theorem neckCompress_mem_neckDomain (hl : 0 < l) (ha : 0 ≤ a) {ε : ℝ}
    {q : EuclideanSpace ℝ (Fin 2) × ℝ} (hq : q ∈ neckDomain ε) :
    (q.1, compress l ha q.2) ∈ neckDomain ε := by
  refine ⟨hq.1, ?_⟩
  rcases le_total 0 q.2 with h | h
  · change |compress l ha q.2| < 2 * ε
    rw [compress_of_nonneg hl ha h]
    exact hq.2
  · have h1 := le_compress hl ha q.2
    have h2 := compress_nonpos hl ha h
    have h3 := hq.2
    change |compress l ha q.2| < 2 * ε
    rw [abs_of_nonpos h2]
    rw [abs_of_nonpos h] at h3
    linarith

end GC.GraphManifold.Assembly
