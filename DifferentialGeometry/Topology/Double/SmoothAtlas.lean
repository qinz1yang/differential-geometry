import DifferentialGeometry.Topology.Double.NegativeTransition
import DifferentialGeometry.Topology.Manifold.OpenCoverAtlas

set_option autoImplicit false
noncomputable section
open Set Function Manifold Topology TopologicalSpace
open scoped ContDiff Topology
namespace Poincare.Topology

theorem exists_smoothAtlas_double_of_collar
    {M E H F G : Type} [TopologicalSpace M] [CompactSpace M] [T2Space M]
    [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H] [ChartedSpace H M]
    (I : ModelWithCorners ℝ E H) [IsManifold I ∞ M]
    (B : Set M) [NormedAddCommGroup F] [NormedSpace ℝ F]
    [TopologicalSpace G] [ChartedSpace G B] (J : ModelWithCorners ℝ F G)
    [IsManifold J ∞ B] [BoundarylessManifold J B]
    (L : (F × ℝ) ≃L[ℝ] E)
    (r : C(M, ℝ)) (hr : ∀ b : B, r b.val = 0)
    (hz : ∀ x, r x = 0 → x ∈ B) (hn : ∀ x, 0 ≤ r x)
    (hI : ∀ x, 0 < r x → I.IsInteriorPoint x)
    {a : ℝ} (c : C(B × Icc (0 : ℝ) a, M))
    (hheight : ∀ q, r (c q) = q.2.val)
    (hsmall : ∀ x, r x ≤ a → x ∈ range c) (hc : IsEmbedding c) (ha : 0 < a)
    (d : Diffeomorph (J.prod 𝓘(ℝ, ℝ)) I (doublePositiveStrip B (a := a)) (doublePositiveBand r (a := a)) ∞)
    (hd : ∀ q, (d q).val = c (q.val.1, ⟨q.val.2, q.property.1.le, q.property.2.le⟩)) :
    ∃ A : ChartedSpace E (Double B), let _ := A
      IsManifold 𝓘(ℝ, E) ∞ (Double B) ∧
      ContMDiffOn I 𝓘(ℝ, E) ∞ (doublePositive B) {x | 0 < r x} ∧
      ContMDiffOn I 𝓘(ℝ, E) ∞ (doubleNegative B) {x | 0 < r x} ∧
      ∀ b : B, ContMDiffOn (J.prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, E) ∞
        (doubleSeamPatch B r hr hz hn c hheight hsmall hc ha b) {q | |q.2| < a} ∧
        ContMDiffOn 𝓘(ℝ, E) (J.prod 𝓘(ℝ, ℝ)) ∞
          (doubleSeamPatch B r hr hz hn c hheight hsmall hc ha b).symm
          {z | |doubleHeight B r hr z| < a} := by
  let K := Bool ⊕ B
  let V : K → Type := fun k => match k with | .inl _ => E | .inr _ => F × ℝ
  let W : K → Type := fun k => match k with | .inl _ => H | .inr _ => ModelProd G ℝ
  let N : K → Type := fun k => match k with | .inl _ => M | .inr _ => B × ℝ
  let _ : ∀ k, NormedAddCommGroup (V k) := by rintro (i | b) <;> exact inferInstance
  let _ : ∀ k, NormedSpace ℝ (V k) := by rintro (i | b) <;> exact inferInstance
  let _ : ∀ k, TopologicalSpace (W k) := by rintro (i | b) <;> exact inferInstance
  let _ : ∀ k, TopologicalSpace (N k) := by rintro (i | b) <;> exact inferInstance
  let _ : ∀ k, ChartedSpace (W k) (N k) := by rintro (i | b) <;> exact inferInstance
  let Q : ∀ k, ModelWithCorners ℝ (V k) (W k) := fun k =>
    match k with | .inl _ => I | .inr _ => J.prod 𝓘(ℝ, ℝ)
  let _ : ∀ k, IsManifold (Q k) ∞ (N k) := by rintro (i | b) <;> exact inferInstance
  let C : ∀ k, V k ≃L[ℝ] E := fun k =>
    match k with | .inl _ => ContinuousLinearEquiv.refl ℝ E | .inr _ => L
  let e : ∀ k, OpenPartialHomeomorph (N k) (Double B) := fun k => match k with
    | .inl false => doublePositivePatch B r hr hn
    | .inl true => doubleNegativePatch B r hr hn
    | .inr b => doubleSeamPatch B r hr hz hn c hheight hsmall hc ha b
  have hcover : ∀ z : Double B, ∃ k, z ∈ (e k).target := by
    intro z
    rcases lt_trichotomy 0 (doubleHeight B r hr z) with hp | he | hm
    · exact ⟨.inl false, hp⟩
    · have hb : doubleFold B z ∈ B := by
        apply hz
        rw [← abs_doubleHeight B r hr hn, ← he, abs_zero]
      refine ⟨.inr ⟨doubleFold B z, hb⟩, ?_⟩
      change z ∈ (doubleSeamPatch B r hr hz hn c hheight hsmall hc ha ⟨doubleFold B z, hb⟩).target
      rw [doubleSeamPatch_target]
      change |doubleHeight B r hr z| < a
      simpa [← he] using ha
    · exact ⟨.inl true, hm⟩
  have hinterior : ∀ k p, p ∈ (e k).source → (Q k).IsInteriorPoint p := by
    rintro (i | b) p hp
    · cases i <;> exact hI p hp
    · exact BoundarylessManifold.isInteriorPoint
  have htrans : ∀ i j, ContMDiffOn (Q i) (Q j) ∞
      ((e i).trans (e j).symm) ((e i).trans (e j).symm).source := by
    rintro (i | b) (j | b')
    · cases i <;> cases j <;> exact contMDiff_id.contMDiffOn
    · cases i
      · exact contMDiffOn_doublePositive_seam_transition I B J r hr hz hn c hheight hsmall hc ha b' d hd
      · exact contMDiffOn_doubleNegative_seam_transition I B J r hr hz hn c hheight hsmall hc ha b' d hd
    · cases j
      · exact contMDiffOn_doubleSeam_positive_transition I B J r hr hz hn c hheight hsmall hc ha b d hd
      · exact contMDiffOn_doubleSeam_negative_transition I B J r hr hz hn c hheight hsmall hc ha b d hd
    · apply contMDiff_id.contMDiffOn.congr
      intro q hq
      exact doubleSeamPatch_transition_apply B r hr hz hn c hheight hsmall hc ha b b' hq
  let A := Poincare.Manifold.openCoverChartedSpace V W N Q C e hcover hinterior
  refine ⟨A, Poincare.Manifold.isManifold_openCoverChartedSpace V W N Q C e hcover hinterior htrans,
    Poincare.Manifold.contMDiffOn_openCover_parametrization V W N Q C e hcover hinterior htrans (.inl false),
    Poincare.Manifold.contMDiffOn_openCover_parametrization V W N Q C e hcover hinterior htrans (.inl true), ?_⟩
  intro b
  have hf := Poincare.Manifold.contMDiffOn_openCover_parametrization V W N Q C e hcover hinterior htrans (.inr b)
  have hg := Poincare.Manifold.contMDiffOn_openCover_inverse V W N Q C e hcover hinterior htrans (.inr b)
  change ContMDiffOn (J.prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, E) ∞
    (doubleSeamPatch B r hr hz hn c hheight hsmall hc ha b)
    (doubleSeamPatch B r hr hz hn c hheight hsmall hc ha b).source at hf
  change ContMDiffOn 𝓘(ℝ, E) (J.prod 𝓘(ℝ, ℝ)) ∞
    (doubleSeamPatch B r hr hz hn c hheight hsmall hc ha b).symm
    (doubleSeamPatch B r hr hz hn c hheight hsmall hc ha b).target at hg
  rw [doubleSeamPatch_source] at hf
  rw [doubleSeamPatch_target] at hg
  exact ⟨hf, hg⟩

end Poincare.Topology
