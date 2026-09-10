import DifferentialGeometry.Geometry.Neck.FiniteAlignment
import DifferentialGeometry.Topology.Manifold.OrderedCollarPatch

noncomputable section
open Set Bundle Topology
open scoped Manifold ContDiff BigOperators
open DifferentialGeometry DifferentialGeometry.Geometry.Operator
open DifferentialGeometry.Geometry.Affine DifferentialGeometry.Topology.Manifold

namespace DifferentialGeometry.Geometry.Neck

theorem regular_patch_of_ordered_neck_collars
    {n : ℕ} {E H W F H' M : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H]
    {I : ModelWithCorners ℝ E H} [TopologicalSpace W] [ChartedSpace H W]
    [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
    [TopologicalSpace H'] {J : ModelWithCorners ℝ F H'}
    [TopologicalSpace M] [ChartedSpace H' M] [IsManifold J ∞ M] [T2Space M]
    [BoundarylessManifold J M]
    (ι : W → M) (hι : ContMDiff I J ∞ ι)
    (hιsurj : ∀ w, Function.Surjective (mfderiv I J ι w))
    (g : SmoothRiemannianMetric J M) (C : Fin (n + 1) → cylindricalChart J (M := M))
    (U : ∀ i, Set (C i).domain) (hU : ∀ i, IsOpen (U i))
    (ε δ : ℝ) (hε : ε < 1 / 200000) (hδ : 92354 * ε + δ < 1)
    (hmetric : ∀ i, (C i).metricCloseOn g ε (U i))
    (s c e : Fin n → ℝ) (hs : ∀ j, s j = 1 ∨ s j = -1) (he : ∀ j, 0 ≤ e j) :
    let a := finiteLineAffineAlignment s c
    let v : Fin (n + 1) → W → ℝ := fun i w ↦ (a i).1 * (C i).axial (ι w) + (a i).2
    let V : Fin (n + 1) → Set W := fun i ↦ ι ⁻¹' (C i).region (U i)
    ∀ (θ : Fin (n + 2) → C^∞⟮I, W; 𝓘(ℝ), ℝ⟯)
      (horder : ∀ w, Antitone (fun i ↦ θ i w))
      (hfirst : ∀ w, θ 0 w = 1) (hlast : ∀ w, θ (Fin.last (n + 1)) w = 0),
    let χ := orderedStepPartition θ horder hfirst hlast
    (∀ i, tsupport (χ i) ⊆ V i) →
    ∀ K : Fin n → Set W, Pairwise (fun i j ↦ Disjoint (K i) (K j)) →
    (∀ i j : Fin (n + 1), i.val + 1 < j.val → Disjoint (tsupport (χ i)) (tsupport (χ j))) →
    (∀ j, tsupport (χ j.castSucc) ∩ tsupport (χ j.succ) ⊆ K j) →
    (∀ j, ∀ w ∈ K j, ∀ i, χ i w ≠ 0 → i = j.castSucc ∨ i = j.succ) →
    (∀ j w, w ∉ K j → mvfderiv I (θ j.succ.castSucc) w = 0) →
    (∀ j, K j ⊆ V j.castSucc ∩ V j.succ) →
    (∀ j, ∀ w ∈ K j, |(C j.succ).axial (ι w) -
      (s j * (C j.castSucc).axial (ι w) + c j)| ≤ e j) →
    (∀ j, ∀ w ∈ K j,
      Real.sqrt (g.inner (ι w)
        (gradFun g (C j.succ).axial (ι w) - s j • gradFun g (C j.castSucc).axial (ι w))
        (gradFun g (C j.succ).axial (ι w) - s j • gradFun g (C j.castSucc).axial (ι w))) ≤ δ) →
    ∀ (k : Fin n → Fin (n + 1)), (∀ j, k j = j.castSucc ∨ k j = j.succ) →
    ∀ (D : Fin n → ℝ), (∀ j, 0 ≤ D j) →
    (∀ j, ∀ w ∈ K j, ∀ z : TangentSpace I w,
      |mvfderiv I (θ j.succ.castSucc) w z| ≤ D j * |mvfderiv I (v (k j)) w z|) →
    ∀ B : ℝ, 0 ≤ B → (∀ j, D j * (1 + 92354 * ε) * e j ≤ B) → B < 1 - 92354 * ε →
    let u := fun w ↦ ∑ i, χ i w * v i w
    ContMDiff I 𝓘(ℝ) ∞ u ∧ ∀ w, mvfderiv I u w ≠ 0 := by
  classical
  intro a v V θ horder hfirst hlast χ hsupp K hdisjoint hnonadjacent hintersection
    hactive hzero hKV hvalue hgradient k hk D hD hstep B hB hproduct hsmall
  let q : Fin (n + 1) → M → ℝ := fun i x ↦ (a i).1 * (C i).axial x + (a i).2
  obtain ⟨ν, Y, hp, heq⟩ := exists_finitely_aligned_least_ricci_fields_of_metric_close
    g C U hU ε hε hmetric s c hs
  have htarget (i) {w : W} (hw : w ∈ V i) : ι w ∈ (C i).target := by
    obtain ⟨y, _, hy⟩ := hw
    rw [← hy]
    exact y.property
  have hqat (i) {w : W} (hw : w ∈ V i) : ContMDiffAt J 𝓘(ℝ) ∞ (q i) (ι w) :=
    ((hp i).1 (ι w) (htarget i hw)).contMDiffAt ((C i).target.isOpen.mem_nhds (htarget i hw))
  have hvat (i) {w : W} (hw : w ∈ V i) : ContMDiffAt I 𝓘(ℝ) ∞ (v i) w :=
    (hqat i hw).comp w hι.contMDiffAt
  let L (w : W) (y : TangentSpace J (ι w)) : TangentSpace I w := (hιsurj w y).choose
  have hL (w : W) (y : TangentSpace J (ι w)) : mfderiv I J ι w (L w y) = y :=
    (hιsurj w y).choose_spec
  let X : Fin (n + 1) → ∀ w : W, TangentSpace I w := fun i w ↦ L w (Y i (ι w))
  have hd (i) {w : W} (hw : w ∈ V i) :
      mvfderiv I (v i) w (X i w) = mvfderiv J (q i) (ι w) (Y i (ι w)) := by
    have h := mvfderiv_comp_apply w ((hqat i hw).mdifferentiableAt (by decide))
      (hι.mdifferentiable (by decide) w) (X i w)
    change mvfderiv I (v i) w (X i w) =
      mvfderiv J (q i) (ι w) (mfderiv I J ι w (L w (Y i (ι w)))) at h
    rwa [hL] at h
  have hder (i) {w : W} (hw : w ∈ V i) :
      |mvfderiv I (v i) w (X i w) - 1| ≤ 92354 * ε := by
    rw [hd i hw]
    exact ((hp i).2.2.2 (ι w) hw).2.2.2.2.2.2
  have hagree (j : Fin n) (w : W) (hw : w ∈ K j) : X j.succ w = X j.castSucc w := by
    change L w (Y j.succ (ι w)) = L w (Y j.castSucc (ι w))
    rw [(heq j (ι w) (hKV j hw).1 (hKV j hw).2 δ hδ (hgradient j w hw)).2]
  apply contMDiff_and_mvfderiv_ne_zero_ordered_collar_partition
    θ horder hfirst hlast v (fun i w hw ↦ hvat i (hsupp i hw)) X K hdisjoint
    hnonadjacent hintersection hactive hzero hagree (fun _ ↦ B) (fun _ ↦ 1 - 92354 * ε)
    (fun _ ↦ hB)
  · intro j w hw
    have hkV : w ∈ V (k j) := by
      rcases hk j with h | h
      · exact h ▸ (hKV j hw).1
      · exact h ▸ (hKV j hw).2
    have hX : X (k j) w = X j.castSucc w := by
      rcases hk j with h | h
      · rw [h]
      · rw [h, hagree j w hw]
    have hcoord : |mvfderiv I (v (k j)) w (X j.castSucc w)| ≤ 1 + 92354 * ε := by
      rw [← hX]
      have hh := abs_le.mp (hder (k j) hkV)
      apply abs_le.mpr
      constructor <;> linarith only [hh.1, hh.2]
    have hcut : |mvfderiv I (θ j.succ.castSucc) w (X j.castSucc w)| ≤ D j * (1 + 92354 * ε) :=
      (hstep j w hw _).trans (mul_le_mul_of_nonneg_left hcoord (hD j))
    have hval : |v j.succ w - v j.castSucc w| ≤ e j := by
      change |(a j.succ).1 * (C j.succ).axial (ι w) + (a j.succ).2 -
        ((a j.castSucc).1 * (C j.castSucc).axial (ι w) + (a j.castSucc).2)| ≤ e j
      rw [abs_finiteLineAffineAlignment_transition_error s c hs]
      exact hvalue j w hw
    calc
      _ ≤ |mvfderiv I (θ j.succ.castSucc) w (X j.castSucc w)| * e j :=
        mul_le_mul_of_nonneg_left hval (abs_nonneg _)
      _ ≤ D j * (1 + 92354 * ε) * e j := mul_le_mul_of_nonneg_right hcut (he j)
      _ ≤ B := hproduct j
  · intro i w hw
    have hh := (abs_le.mp (hder i (hsupp i hw))).1
    linarith only [hh]
  · exact fun _ ↦ hsmall

end DifferentialGeometry.Geometry.Neck
