import DifferentialGeometry.Topology.Double.Manifold
import DifferentialGeometry.Topology.VectorField.Pushforward
import DifferentialGeometry.Topology.VectorField.Transport

set_option autoImplicit false
noncomputable section
open Set Function Manifold Topology TopologicalSpace Bundle
open scoped ContDiff Topology Manifold

namespace DifferentialGeometry.Topology

private theorem exists_doubleAtlas_chartSmoothness
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
    (d : Diffeomorph (J.prod 𝓘(ℝ, ℝ)) I
      (doublePositiveStrip B (a := a)) (doublePositiveBand r (a := a)) ∞)
    (hd : ∀ q, (d q).val = c (q.val.1, ⟨q.val.2, q.property.1.le, q.property.2.le⟩)) :
    ∃ A : ChartedSpace E (Double B), let _ := A;
      IsManifold 𝓘(ℝ, E) ∞ (Double B) ∧
      T2Space (Double B) ∧
      ContMDiffOn I 𝓘(ℝ, E) ∞ (doublePositive B) {x | 0 < r x} ∧
      ContMDiffOn I 𝓘(ℝ, E) ∞ (doubleNegative B) {x | 0 < r x} ∧
      ContMDiffOn 𝓘(ℝ, E) I ∞ (doubleFold B) {z | 0 < doubleHeight B r hr z} ∧
      ContMDiffOn 𝓘(ℝ, E) I ∞ (doubleFold B) {z | doubleHeight B r hr z < 0} ∧
      (∀ b : B, ContMDiffOn (J.prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, E) ∞
        (doubleSeamPatch B r hr hz hn c hheight hsmall hc ha b) {q | |q.2| < a}) ∧
      (∀ b : B, ContMDiffOn 𝓘(ℝ, E) (J.prod 𝓘(ℝ, ℝ)) ∞
        (doubleSeamPatch B r hr hz hn c hheight hsmall hc ha b).symm
        {z | |doubleHeight B r hr z| < a}) := by
  let K := Bool ⊕ B
  let VK : K → Type := fun k => match k with | .inl _ => E | .inr _ => F × ℝ
  let WK : K → Type := fun k => match k with | .inl _ => H | .inr _ => ModelProd G ℝ
  let NK : K → Type := fun k => match k with | .inl _ => M | .inr _ => B × ℝ
  let _ : ∀ k, NormedAddCommGroup (VK k) := by rintro (i | b) <;> exact inferInstance
  let _ : ∀ k, NormedSpace ℝ (VK k) := by rintro (i | b) <;> exact inferInstance
  let _ : ∀ k, TopologicalSpace (WK k) := by rintro (i | b) <;> exact inferInstance
  let _ : ∀ k, TopologicalSpace (NK k) := by rintro (i | b) <;> exact inferInstance
  let _ : ∀ k, ChartedSpace (WK k) (NK k) := by rintro (i | b) <;> exact inferInstance
  let Q : ∀ k, ModelWithCorners ℝ (VK k) (WK k) := fun k =>
    match k with | .inl _ => I | .inr _ => J.prod 𝓘(ℝ, ℝ)
  let _ : ∀ k, IsManifold (Q k) ∞ (NK k) := by rintro (i | b) <;> exact inferInstance
  let C : ∀ k, VK k ≃L[ℝ] E := fun k =>
    match k with | .inl _ => ContinuousLinearEquiv.refl ℝ E | .inr _ => L
  let e : ∀ k, OpenPartialHomeomorph (NK k) (Double B) := fun k => match k with
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
      change z ∈ (doubleSeamPatch B r hr hz hn c hheight hsmall hc ha
          ⟨doubleFold B z, hb⟩).target
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
      · exact contMDiffOn_doublePositive_seam_transition I B J r hr hz hn c hheight hsmall hc
          ha b' d hd
      · exact contMDiffOn_doubleNegative_seam_transition I B J r hr hz hn c hheight hsmall hc
          ha b' d hd
    · cases j
      · exact contMDiffOn_doubleSeam_positive_transition I B J r hr hz hn c hheight hsmall hc
          ha b d hd
      · exact contMDiffOn_doubleSeam_negative_transition I B J r hr hz hn c hheight hsmall hc
          ha b d hd
    · apply contMDiff_id.contMDiffOn.congr
      intro q hq
      exact doubleSeamPatch_transition_apply B r hr hz hn c hheight hsmall hc ha b b' hq
  let A := DifferentialGeometry.Manifold.openCoverChartedSpace VK WK NK Q C e hcover hinterior
  refine ⟨A, DifferentialGeometry.Manifold.isManifold_openCoverChartedSpace VK WK NK Q C e hcover
    hinterior htrans, t2Space_double B r hr hz, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact DifferentialGeometry.Manifold.contMDiffOn_openCover_parametrization VK WK NK Q C e
      hcover hinterior htrans (.inl false)
  · exact DifferentialGeometry.Manifold.contMDiffOn_openCover_parametrization VK WK NK Q C e
      hcover hinterior htrans (.inl true)
  · exact DifferentialGeometry.Manifold.contMDiffOn_openCover_inverse VK WK NK Q C e
      hcover hinterior htrans (.inl false)
  · exact DifferentialGeometry.Manifold.contMDiffOn_openCover_inverse VK WK NK Q C e
      hcover hinterior htrans (.inl true)
  · intro b
    have h := DifferentialGeometry.Manifold.contMDiffOn_openCover_parametrization VK WK NK Q C e
      hcover hinterior htrans (.inr b)
    convert h using 2
    rw [doubleSeamPatch_source]
  · intro b
    have h := DifferentialGeometry.Manifold.contMDiffOn_openCover_inverse VK WK NK Q C e
      hcover hinterior htrans (.inr b)
    convert h using 2
    rw [doubleSeamPatch_target]

private def partialDiffeomorphOfOpenPartialHomeomorph
    {E₁ H₁ M₁ E₂ H₂ M₂ : Type*}
    [NormedAddCommGroup E₁] [NormedSpace ℝ E₁] [TopologicalSpace H₁]
    [TopologicalSpace M₁] [ChartedSpace H₁ M₁]
    [NormedAddCommGroup E₂] [NormedSpace ℝ E₂] [TopologicalSpace H₂]
    [TopologicalSpace M₂] [ChartedSpace H₂ M₂]
    (I₁ : ModelWithCorners ℝ E₁ H₁) (I₂ : ModelWithCorners ℝ E₂ H₂)
    (e : OpenPartialHomeomorph M₁ M₂) (h₁ : ContMDiffOn I₁ I₂ ∞ e e.source)
    (h₂ : ContMDiffOn I₂ I₁ ∞ e.symm e.target) :
    PartialDiffeomorph I₁ I₂ M₁ M₂ ∞ where
  toPartialEquiv := e.toPartialEquiv
  open_source := e.open_source
  open_target := e.open_target
  contMDiffOn_toFun := h₁
  contMDiffOn_invFun := h₂

private def pushforwardField
    {E₁ H₁ M₁ E₂ H₂ M₂ : Type*}
    [NormedAddCommGroup E₁] [NormedSpace ℝ E₁] [TopologicalSpace H₁]
    [TopologicalSpace M₁] [ChartedSpace H₁ M₁]
    [NormedAddCommGroup E₂] [NormedSpace ℝ E₂] [TopologicalSpace H₂]
    [TopologicalSpace M₂] [ChartedSpace H₂ M₂]
    (I₁ : ModelWithCorners ℝ E₁ H₁) (I₂ : ModelWithCorners ℝ E₂ H₂)
    (e : PartialDiffeomorph I₁ I₂ M₁ M₂ ∞) (v : ∀ x : M₁, TangentSpace I₁ x) :
    (z : M₂) → TangentSpace I₂ z := by
  classical
  exact fun z => if z ∈ e.target then _root_.VectorField.mpullback I₂ I₁ e.symm v z else 0

private theorem pushforwardField_of_mem
    {E₁ H₁ M₁ E₂ H₂ M₂ : Type*}
    [NormedAddCommGroup E₁] [NormedSpace ℝ E₁] [TopologicalSpace H₁]
    [TopologicalSpace M₁] [ChartedSpace H₁ M₁]
    [NormedAddCommGroup E₂] [NormedSpace ℝ E₂] [TopologicalSpace H₂]
    [TopologicalSpace M₂] [ChartedSpace H₂ M₂]
    (I₁ : ModelWithCorners ℝ E₁ H₁) (I₂ : ModelWithCorners ℝ E₂ H₂)
    (e : PartialDiffeomorph I₁ I₂ M₁ M₂ ∞) (v : ∀ x : M₁, TangentSpace I₁ x)
    {z : M₂} (hz : z ∈ e.target) :
    pushforwardField I₁ I₂ e v z = _root_.VectorField.mpullback I₂ I₁ e.symm v z := by
  classical
  simp only [pushforwardField, if_pos hz]

private theorem pushforwardField_of_not_mem
    {E₁ H₁ M₁ E₂ H₂ M₂ : Type*}
    [NormedAddCommGroup E₁] [NormedSpace ℝ E₁] [TopologicalSpace H₁]
    [TopologicalSpace M₁] [ChartedSpace H₁ M₁]
    [NormedAddCommGroup E₂] [NormedSpace ℝ E₂] [TopologicalSpace H₂]
    [TopologicalSpace M₂] [ChartedSpace H₂ M₂]
    (I₁ : ModelWithCorners ℝ E₁ H₁) (I₂ : ModelWithCorners ℝ E₂ H₂)
    (e : PartialDiffeomorph I₁ I₂ M₁ M₂ ∞) (v : ∀ x : M₁, TangentSpace I₁ x)
    {z : M₂} (hz : z ∉ e.target) :
    pushforwardField I₁ I₂ e v z = 0 := by
  classical
  simp only [pushforwardField, if_neg hz]

private theorem contMDiffOn_pushforwardField
    {E₁ H₁ M₁ E₂ H₂ M₂ : Type*}
    [NormedAddCommGroup E₁] [NormedSpace ℝ E₁] [TopologicalSpace H₁]
    [TopologicalSpace M₁] [ChartedSpace H₁ M₁]
    [NormedAddCommGroup E₂] [NormedSpace ℝ E₂] [TopologicalSpace H₂]
    [TopologicalSpace M₂] [ChartedSpace H₂ M₂]
    (I₁ : ModelWithCorners ℝ E₁ H₁) (I₂ : ModelWithCorners ℝ E₂ H₂)
    (e : PartialDiffeomorph I₁ I₂ M₁ M₂ ∞) (v : ∀ x : M₁, TangentSpace I₁ x)
    [IsManifold I₁ 1 M₁] [IsManifold I₂ 1 M₂]
    (hv : ContMDiff I₁ I₁.tangent ∞ (fun x => (⟨x, v x⟩ : TangentBundle I₁ M₁))) :
    ContMDiffOn I₂ I₂.tangent ∞
      (fun z => (⟨z, pushforwardField I₁ I₂ e v z⟩ : TangentBundle I₂ M₂))
          e.target := by
  refine (DifferentialGeometry.VectorField.contMDiffOn_mpullback_partialDiffeomorph
    (m := ∞) (n := ∞) e.symm (by simp) hv.contMDiffOn).congr (fun z hz => ?_)
  rw [pushforwardField_of_mem I₁ I₂ e v hz]

private theorem support_pushforwardField_subset
    {E₁ H₁ M₁ E₂ H₂ M₂ : Type*}
    [NormedAddCommGroup E₁] [NormedSpace ℝ E₁] [TopologicalSpace H₁]
    [TopologicalSpace M₁] [ChartedSpace H₁ M₁]
    [NormedAddCommGroup E₂] [NormedSpace ℝ E₂] [TopologicalSpace H₂]
    [TopologicalSpace M₂] [ChartedSpace H₂ M₂]
    (I₁ : ModelWithCorners ℝ E₁ H₁) (I₂ : ModelWithCorners ℝ E₂ H₂)
    (e : PartialDiffeomorph I₁ I₂ M₁ M₂ ∞) (v : ∀ x : M₁, TangentSpace I₁ x)
    [IsManifold I₁ 1 M₁] [IsManifold I₂ 1 M₂]
    {z : M₂} (hz : pushforwardField I₁ I₂ e v z ≠ 0) :
    z ∈ e '' (tsupport v) := by
  by_cases hzt : z ∈ e.target
  · rw [pushforwardField_of_mem I₁ I₂ e v hzt] at hz
    have hne : v (e.symm z) ≠ 0 := by
      intro h0
      refine hz ?_
      change (mfderiv I₂ I₁ e.symm z).inverse (v (e.symm z)) = 0
      rw [h0, map_zero]
    exact ⟨e.symm z, subset_tsupport _ hne, by
      simpa using e.right_inv hzt⟩
  · exact absurd (pushforwardField_of_not_mem I₁ I₂ e v hzt) hz

private theorem mfderiv_doubleSeamPatch_eq_comp_doubleFold
    {M E H F G : Type} [TopologicalSpace M] [CompactSpace M] [T2Space M]
    [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H] [ChartedSpace H M]
    (I : ModelWithCorners ℝ E H) [IsManifold I ∞ M]
    (B : Set M) [NormedAddCommGroup F] [NormedSpace ℝ F]
    [TopologicalSpace G] [ChartedSpace G B] (J : ModelWithCorners ℝ F G)
    [IsManifold J ∞ B] [ChartedSpace E (Double B)]
    [IsManifold 𝓘(ℝ, E) ∞ (Double B)] [T2Space (Double B)]
    (r : C(M, ℝ)) (hr : ∀ b : B, r b.val = 0)
    (hz : ∀ x, r x = 0 → x ∈ B) (hn : ∀ x, 0 ≤ r x)
    {a : ℝ} (c : C(B × Icc (0 : ℝ) a, M))
    (hheight : ∀ q, r (c q) = q.2.val)
    (hsmall : ∀ x, r x ≤ a → x ∈ range c) (hc : IsEmbedding c) (ha : 0 < a)
    (b : B)
    (hpos : ContMDiffOn I 𝓘(ℝ, E) ∞ (doublePositive B) {x | 0 < r x})
    (hfold : ContMDiffOn 𝓘(ℝ, E) I ∞ (doubleFold B)
      {z | 0 < doubleHeight B r hr z})
    (hseam : ContMDiffOn (J.prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, E) ∞
      (doubleSeamPatch B r hr hz hn c hheight hsmall hc ha b) {q | |q.2| < a})
    {q : B × ℝ} (hq : q ∈ doublePositiveStrip B (a := a)) :
    mfderiv (J.prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, E)
        (doubleSeamPatch B r hr hz hn c hheight hsmall hc ha b) q =
      (mfderiv I 𝓘(ℝ, E) (doublePositive B)
        (doubleFold B (doubleSeamPatch B r hr hz hn c hheight hsmall hc ha b q))).comp
        (mfderiv (J.prod 𝓘(ℝ, ℝ)) I
          (fun q' : B × ℝ => doubleFold B
            (doubleSeamPatch B r hr hz hn c hheight hsmall hc ha b q')) q) := by
  have hq' : 0 < q.2 ∧ q.2 < a := hq
  have hqa : |q.2| < a := by rw [abs_of_pos hq'.1]; exact hq'.2
  have hfoldEq : doubleFold B (doubleSeamPatch B r hr hz hn c hheight hsmall hc ha b q) =
      c (q.1, ⟨q.2, hq'.1.le, (le_abs_self q.2).trans hqa.le⟩) := by
    rw [doubleSeamPatch_of_nonneg B r hr hz hn c hheight hsmall hc ha b hqa hq'.1.le]
    rfl
  have hposn : 0 < doubleHeight B r hr
      (doubleSeamPatch B r hr hz hn c hheight hsmall hc ha b q) := by
    rw [doubleHeight_seamPatch B r hr hz hn c hheight hsmall hc ha b hqa]
    exact hq'.1
  have hfdC : ContMDiffAt (J.prod 𝓘(ℝ, ℝ)) I ∞
      (fun q' : B × ℝ => doubleFold B
        (doubleSeamPatch B r hr hz hn c hheight hsmall hc ha b q')) q :=
    (hfold.contMDiffAt ((isOpen_lt continuous_const (doubleHeight B r hr).continuous).mem_nhds
      hposn)).comp
      q (hseam.contMDiffAt ((isOpen_lt continuous_snd.abs continuous_const).mem_nhds hqa))
  have hfd : MDifferentiableAt (J.prod 𝓘(ℝ, ℝ)) I
      (fun q' : B × ℝ => doubleFold B
        (doubleSeamPatch B r hr hz hn c hheight hsmall hc ha b q')) q :=
    hfdC.mdifferentiableAt (by norm_num)
  have hpeq : (fun q' : B × ℝ => doublePositive B (doubleFold B
      (doubleSeamPatch B r hr hz hn c hheight hsmall hc ha b q'))) =ᶠ[𝓝 q]
      (doubleSeamPatch B r hr hz hn c hheight hsmall hc ha b) := by
    filter_upwards [(doublePositiveStrip B (a := a)).isOpen.mem_nhds hq] with q' hq''
    have hq''a : |q'.2| < a := by rw [abs_of_pos hq''.1]; exact hq''.2
    rw [doubleSeamPatch_of_nonneg B r hr hz hn c hheight hsmall hc ha b hq''a hq''.1.le]
    rfl
  have hrc : 0 < r (c (q.1, ⟨q.2, hq'.1.le, (le_abs_self q.2).trans hqa.le⟩)) := by
    rw [hheight]
    exact hq'.1
  have hposAt : MDifferentiableAt I 𝓘(ℝ, E) (doublePositive B)
      (doubleFold B (doubleSeamPatch B r hr hz hn c hheight hsmall hc ha b q)) := by
    refine (hpos.contMDiffAt ?_).mdifferentiableAt (by norm_num)
    refine (isOpen_lt continuous_const r.continuous).mem_nhds ?_
    rw [hfoldEq]
    exact hrc
  have hchain : mfderiv% (fun q' : B × ℝ => doublePositive B (doubleFold B
        (doubleSeamPatch B r hr hz hn c hheight hsmall hc ha b q'))) q =
      mfderiv% (doubleSeamPatch B r hr hz hn c hheight hsmall hc ha b) q :=
    Filter.EventuallyEq.mfderiv_eq hpeq
  have hcomp : mfderiv% (fun q' : B × ℝ => doublePositive B (doubleFold B
        (doubleSeamPatch B r hr hz hn c hheight hsmall hc ha b q'))) q =
      (mfderiv% (doublePositive B : M → Double B)
        (doubleFold B (doubleSeamPatch B r hr hz hn c hheight hsmall hc ha b q))).comp
        (mfderiv% (fun q' : B × ℝ => doubleFold B
          (doubleSeamPatch B r hr hz hn c hheight hsmall hc ha b q')) q) :=
    mfderiv_comp (I := J.prod 𝓘(ℝ, ℝ)) (I' := I) (I'' := 𝓘(ℝ, E))
      (M := B × ℝ) (M' := M) (M'' := Double B)
      (f := fun q' : B × ℝ => doubleFold B
        (doubleSeamPatch B r hr hz hn c hheight hsmall hc ha b q'))
      (g := (doublePositive B : M → Double B)) q hposAt hfd
  rw [← hchain]
  exact hcomp

private theorem comp_inverse_apply_eq
    {E₁ H₁ M₁ E₂ H₂ M₂ E₃ H₃ M₃ : Type*}
    [NormedAddCommGroup E₁] [NormedSpace ℝ E₁] [TopologicalSpace H₁]
    [TopologicalSpace M₁] [ChartedSpace H₁ M₁]
    [NormedAddCommGroup E₂] [NormedSpace ℝ E₂] [TopologicalSpace H₂]
    [TopologicalSpace M₂] [ChartedSpace H₂ M₂]
    [NormedAddCommGroup E₃] [NormedSpace ℝ E₃] [TopologicalSpace H₃]
    [TopologicalSpace M₃] [ChartedSpace H₃ M₃]
    {I₁ : ModelWithCorners ℝ E₁ H₁} {I₂ : ModelWithCorners ℝ E₂ H₂}
    {I₃ : ModelWithCorners ℝ E₃ H₃}
    {f : M₁ → M₂} {g : M₂ → M₃} {s : M₁ → M₃} {x : M₁}
    {u : (y : M₁) → TangentSpace I₁ y} {w : (z : M₂) → TangentSpace I₂ z}
    (hchain : mfderiv I₁ I₃ s x = (mfderiv I₂ I₃ g (f x)).comp (mfderiv I₁ I₂ f x))
    (hinv : (mfderiv I₁ I₂ f x).IsInvertible)
    (hu : u x = (mfderiv I₁ I₂ f x).inverse (w (f x))) :
    mfderiv I₁ I₃ s x (u x) = (mfderiv I₂ I₃ g (f x)) (w (f x)) := by
  rw [hchain]
  change (mfderiv I₂ I₃ g (f x)) ((mfderiv I₁ I₂ f x) (u x)) = _
  rw [hu, hinv.self_apply_inverse]

theorem exists_doubleSeam_transport
    {M E H F G : Type} [TopologicalSpace M] [CompactSpace M] [T2Space M]
    [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H] [ChartedSpace H M]
    (I : ModelWithCorners ℝ E H) [IsManifold I ∞ M]
    (B : Set M) [NormedAddCommGroup F] [NormedSpace ℝ F]
    [TopologicalSpace G] [ChartedSpace G B] (J : ModelWithCorners ℝ F G)
    [IsManifold J ∞ B] [BoundarylessManifold J B]
    (L : (F × ℝ) ≃L[ℝ] E)
    (r : C(M, ℝ)) (hr : ∀ b : B, r b.val = 0)
    (hrsmooth : ContMDiff I 𝓘(ℝ, ℝ) ∞ r)
    (hz : ∀ x, r x = 0 → x ∈ B) (hn : ∀ x, 0 ≤ r x)
    (hI : ∀ x, 0 < r x → I.IsInteriorPoint x)
    {a : ℝ} (c : C(B × Icc (0 : ℝ) a, M))
    (hheight : ∀ q, r (c q) = q.2.val)
    (hsmall : ∀ x, r x ≤ a → x ∈ range c) (hc : IsEmbedding c) (ha : 0 < a)
    (d : Diffeomorph (J.prod 𝓘(ℝ, ℝ)) I
      (doublePositiveStrip B (a := a)) (doublePositiveBand r (a := a)) ∞)
    (hd : ∀ q, (d q).val = c (q.val.1, ⟨q.val.2, q.property.1.le, q.property.2.le⟩))
    (b₀ : B)
    (V : ∀ x : M, TangentSpace I x)
    (hV : ContMDiff I I.tangent ∞ (fun x => (⟨x, V x⟩ : TangentBundle I M)))
    (hsupp : IsCompact (tsupport V))
    (W : ∀ q : B × ℝ, TangentSpace (J.prod 𝓘(ℝ, ℝ)) q)
    (hW : ContMDiff (J.prod 𝓘(ℝ, ℝ)) (J.prod 𝓘(ℝ, ℝ)).tangent ∞
      (fun q => (⟨q, W q⟩ : TangentBundle (J.prod 𝓘(ℝ, ℝ)) (B × ℝ))))
    (hWsupp : IsCompact (tsupport W))
    (hWtan : ∀ q : B × ℝ, q.2 = 0 → (W q).2 = 0)
    (hWdatum : ∀ q : B × ℝ, q ∈ doublePositiveStrip B (a := a) →
      W q = (mfderiv (J.prod 𝓘(ℝ, ℝ)) I
        (fun q' : B × ℝ => doubleFold B
          (doubleSeamPatch B r hr hz hn c hheight hsmall hc ha b₀ q')) q).inverse
        (V (doubleFold B (doubleSeamPatch B r hr hz hn c hheight hsmall hc ha b₀ q)))) :
    ∃ (A : ChartedSpace E (Double B)) (hA : IsManifold 𝓘(ℝ, E) ∞ (Double B))
      (hT : T2Space (Double B)),
      let _ := A
      let _ := hA
      let _ := hT
      ∃ X : (z : Double B) → TangentSpace 𝓘(ℝ, E) z,
        ContMDiff 𝓘(ℝ, E) (𝓘(ℝ, E)).tangent ∞
          (fun z => (⟨z, X z⟩ : TangentBundle 𝓘(ℝ, E) (Double B))) ∧
        IsCompact (tsupport X) ∧
        (∀ x : M, 0 < r x →
          X (doublePositive B x) = mfderiv I 𝓘(ℝ, E) (doublePositive B) x (V x)) ∧
        (∀ q : B × ℝ, q.2 = 0 →
          X (doubleSeamPatch B r hr hz hn c hheight hsmall hc ha b₀ q) =
            mfderiv (J.prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, E)
              (doubleSeamPatch B r hr hz hn c hheight hsmall hc ha b₀) q (W q)) ∧
        (∀ q : B × ℝ, q.2 = 0 →
          ((mfderiv (J.prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, E)
              (doubleSeamPatch B r hr hz hn c hheight hsmall hc ha b₀) q).inverse
            (X (doubleSeamPatch B r hr hz hn c hheight hsmall hc ha b₀ q))).2 = 0) := by
  obtain ⟨A, hA, hT2, hposσ, hnegσ, hfoldPos, hfoldNeg, hseamσ, hseamσ'⟩ :=
    exists_doubleAtlas_chartSmoothness I B J L r hr hz hn hI c hheight hsmall hc ha d hd
  let pdPos : PartialDiffeomorph I 𝓘(ℝ, E) M (Double B) ∞ :=
    partialDiffeomorphOfOpenPartialHomeomorph I 𝓘(ℝ, E) (doublePositivePatch B r hr hn)
      hposσ hfoldPos
  let pdNeg : PartialDiffeomorph I 𝓘(ℝ, E) M (Double B) ∞ :=
    partialDiffeomorphOfOpenPartialHomeomorph I 𝓘(ℝ, E) (doubleNegativePatch B r hr hn)
      hnegσ hfoldNeg
  let pdSeam : PartialDiffeomorph (J.prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, E) (B × ℝ) (Double B) ∞ :=
    partialDiffeomorphOfOpenPartialHomeomorph (J.prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, E)
      (doubleSeamPatch B r hr hz hn c hheight hsmall hc ha b₀)
      (by rw [doubleSeamPatch_source]; exact hseamσ b₀)
      (by rw [doubleSeamPatch_target]; exact hseamσ' b₀)
  let seam : B × ℝ → Double B := doubleSeamPatch B r hr hz hn c hheight hsmall hc ha b₀
  let foldSeam : B × ℝ → M := fun q => doubleFold B (seam q)
  let Pseam : (z : Double B) → TangentSpace 𝓘(ℝ, E) z :=
    pushforwardField (J.prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, E) pdSeam W
  let Ppos : (z : Double B) → TangentSpace 𝓘(ℝ, E) z :=
    pushforwardField I 𝓘(ℝ, E) pdPos V
  let Pneg : (z : Double B) → TangentSpace 𝓘(ℝ, E) z :=
    pushforwardField I 𝓘(ℝ, E) pdNeg V
  let bump : ContDiffBump (0 : ℝ) := ⟨a / 8, a / 4, by linarith, by linarith⟩
  let ρ : Double B → ℝ := fun z => bump (doubleHeight B r hr z)
  let Pout : (z : Double B) → TangentSpace 𝓘(ℝ, E) z :=
    fun z => if 0 < doubleHeight B r hr z then Ppos z else Pneg z
  let X : (z : Double B) → TangentSpace 𝓘(ℝ, E) z :=
    fun z => ρ z • Pseam z + (1 - ρ z) • Pout z
  have hXsec : ∀ w : Double B, X w = ρ w • Pseam w + (1 - ρ w) • Pout w := fun w => rfl
  have hseamMem : ∀ z : Double B, z ∈ pdSeam.target ↔ |doubleHeight B r hr z| < a := by
    intro z
    change z ∈ (doubleSeamPatch B r hr hz hn c hheight hsmall hc ha b₀).target ↔ _
    rw [doubleSeamPatch_target]
    rfl
  have hposMem : ∀ z : Double B, z ∈ pdPos.target ↔ 0 < doubleHeight B r hr z :=
      fun z => Iff.rfl
  have hnegMem : ∀ z : Double B, z ∈ pdNeg.target ↔ doubleHeight B r hr z < 0 :=
      fun z => Iff.rfl
  have hseamHeight : ∀ z ∈ pdSeam.target, doubleHeight B r hr z = (pdSeam.symm z).2 := by
    intro z hzt
    have hsrc : pdSeam.symm z ∈ pdSeam.source := pdSeam.map_target hzt
    have hsrca : |(pdSeam.symm z).2| < a := by
      have h := hsrc
      change pdSeam.symm z ∈
          (doubleSeamPatch B r hr hz hn c hheight hsmall hc ha b₀).source at h
      rwa [doubleSeamPatch_source] at h
    have hs : doubleSeamPatch B r hr hz hn c hheight hsmall hc ha b₀ (pdSeam.symm z) = z := by
      change pdSeam (pdSeam.symm z) = z
      exact pdSeam.right_inv hzt
    calc doubleHeight B r hr z
        = doubleHeight B r hr (doubleSeamPatch B r hr hz hn c hheight hsmall hc ha b₀
            (pdSeam.symm z)) := by rw [hs]
      _ = (pdSeam.symm z).2 := doubleHeight_seamPatch B r hr hz hn c hheight hsmall hc ha b₀ hsrca
  have hseamPatchSymm : ∀ z ∈ pdSeam.target,
      doubleSeamPatch B r hr hz hn c hheight hsmall hc ha b₀ (pdSeam.symm z) = z := by
    intro z hzt
    change pdSeam (pdSeam.symm z) = z
    exact pdSeam.right_inv hzt
  have hseamSymmAbs : ∀ z ∈ pdSeam.target, |(pdSeam.symm z).2| < a := by
    intro z hzt
    have hsrc : pdSeam.symm z ∈ pdSeam.source := pdSeam.map_target hzt
    have h := hsrc
    change pdSeam.symm z ∈
        (doubleSeamPatch B r hr hz hn c hheight hsmall hc ha b₀).source at h
    rwa [doubleSeamPatch_source] at h
  have hWdatum' : ∀ q ∈ doublePositiveStrip B (a := a),
      W q = (mfderiv (J.prod 𝓘(ℝ, ℝ)) I foldSeam q).inverse (V (foldSeam q)) :=
    fun q hq => hWdatum q hq
  refine ⟨A, hA, hT2, X, ?_, ?_, ?_, ?_, ?_⟩
  · have hPseamSmooth : ContMDiffOn 𝓘(ℝ, E) (𝓘(ℝ, E)).tangent ∞
        (fun z => (⟨z, Pseam z⟩ : TangentBundle 𝓘(ℝ, E) (Double B))) pdSeam.target :=
      contMDiffOn_pushforwardField _ _ _ _ hW
    have hPposSmooth : ContMDiffOn 𝓘(ℝ, E) (𝓘(ℝ, E)).tangent ∞
        (fun z => (⟨z, Ppos z⟩ : TangentBundle 𝓘(ℝ, E) (Double B))) pdPos.target :=
      contMDiffOn_pushforwardField _ _ _ _ hV
    have hPnegSmooth : ContMDiffOn 𝓘(ℝ, E) (𝓘(ℝ, E)).tangent ∞
        (fun z => (⟨z, Pneg z⟩ : TangentBundle 𝓘(ℝ, E) (Double B))) pdNeg.target :=
      contMDiffOn_pushforwardField _ _ _ _ hV
    have hfoldPosAt : ContMDiffOn 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ (doubleHeight B r hr)
        pdPos.target := by
      intro z hz
      have hdh : doubleHeight B r hr =ᶠ[𝓝 z] (fun w => r (doubleFold B w)) := by
        filter_upwards [pdPos.open_target.mem_nhds hz] with w hw
        have hw' : doublePositive B (doubleFold B w) = w := by
          simpa using (doublePositivePatch B r hr hn).right_inv hw
        rw [← hw']
        simp
      exact (((hrsmooth.contMDiffAt.comp z
        (hfoldPos.contMDiffAt (pdPos.open_target.mem_nhds hz)))).congr_of_eventuallyEq
          hdh).contMDiffWithinAt
    have hfoldNegAt : ContMDiffOn 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ (doubleHeight B r hr)
        pdNeg.target := by
      intro z hz
      have hdh : doubleHeight B r hr =ᶠ[𝓝 z] (fun w => -r (doubleFold B w)) := by
        filter_upwards [pdNeg.open_target.mem_nhds hz] with w hw
        have hw' : doubleNegative B (doubleFold B w) = w := by
          simpa using (doubleNegativePatch B r hr hn).right_inv hw
        rw [← hw']
        simp
      exact ((((hrsmooth.contMDiffAt.neg).comp z
        (hfoldNeg.contMDiffAt (pdNeg.open_target.mem_nhds hz)))).congr_of_eventuallyEq
          hdh).contMDiffWithinAt
    have hfoldSeamAt : ContMDiffOn 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ (doubleHeight B r hr)
        pdSeam.target := by
      intro z hzt
      have hdh : doubleHeight B r hr =ᶠ[𝓝 z] (fun w => (pdSeam.symm w).2) := by
        filter_upwards [pdSeam.open_target.mem_nhds hzt] with w hw
        have hsrc : pdSeam.symm w ∈ pdSeam.source := pdSeam.map_target hw
        have hs : doubleSeamPatch B r hr hz hn c hheight hsmall hc ha b₀ (pdSeam.symm w) = w := by
          change pdSeam (pdSeam.symm w) = w
          exact pdSeam.right_inv hw
        have hsrca : |(pdSeam.symm w).2| < a := by
          have h := hsrc
          change pdSeam.symm w ∈ (doubleSeamPatch B r hr hz hn c hheight hsmall hc ha
            b₀).source at h
          rwa [doubleSeamPatch_source] at h
        calc doubleHeight B r hr w
            = doubleHeight B r hr (doubleSeamPatch B r hr hz hn c hheight hsmall hc ha b₀
                (pdSeam.symm w)) := by rw [hs]
          _ = (pdSeam.symm w).2 :=
              doubleHeight_seamPatch B r hr hz hn c hheight hsmall hc ha b₀ hsrca
      have h1 : ContMDiffAt 𝓘(ℝ, E) (J.prod 𝓘(ℝ, ℝ)) ∞ (fun w => pdSeam.symm w) z :=
        pdSeam.symm.contMDiffOn.contMDiffAt (pdSeam.open_target.mem_nhds hzt)
      have h2 : ContMDiffAt (J.prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, ℝ) ∞
          (fun p : B × ℝ => p.2) (pdSeam.symm z) := contMDiff_snd.contMDiffAt
      exact ((h2.comp z h1).congr_of_eventuallyEq hdh).contMDiffWithinAt
    have hdh : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ (doubleHeight B r hr) := by
      refine contMDiff_of_contMDiffOn_iUnion_of_isOpen (ι := Fin 3)
        (s := ![pdPos.target, pdNeg.target, pdSeam.target]) ?_ ?_ ?_
      · intro i
        fin_cases i
        · simpa using hfoldPosAt
        · simpa using hfoldNegAt
        · simpa using hfoldSeamAt
      · intro i
        fin_cases i <;> simp [pdPos.open_target, pdNeg.open_target, pdSeam.open_target]
      · ext z
        simp only [mem_iUnion, mem_univ, iff_true]
        rcases lt_trichotomy 0 (doubleHeight B r hr z) with hp | h0 | hm
        · exact ⟨0, by simpa using ((hposMem z).mpr hp)⟩
        · refine ⟨2, ?_⟩
          change z ∈ pdSeam.target
          rw [hseamMem, ← h0, abs_zero]
          exact ha
        · exact ⟨1, by simpa using ((hnegMem z).mpr hm)⟩
    have hρsmooth : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ ρ :=
      bump.contDiff.contMDiff.comp hdh
    have hX : ContMDiff 𝓘(ℝ, E) (𝓘(ℝ, E)).tangent ∞
        (fun z => (⟨z, X z⟩ : TangentBundle 𝓘(ℝ, E) (Double B))) := by
      intro z
      have hρ1 : |doubleHeight B r hr z| < a / 8 → ρ =ᶠ[𝓝 z] 1 := by
        intro hz
        have hmem : doubleHeight B r hr z ∈ Metric.ball (0 : ℝ) bump.rIn := by
          rw [Metric.mem_ball, dist_zero_right, Real.norm_eq_abs]
          exact hz
        exact (doubleHeight B r hr).continuous.continuousAt.eventually
          (bump.eventuallyEq_one_of_mem_ball hmem)
      have hρ0 : a / 4 < |doubleHeight B r hr z| → ρ =ᶠ[𝓝 z] 0 := by
        intro hz
        have hnear : ∀ᶠ w in 𝓝 z, a / 4 < |doubleHeight B r hr w| :=
          (isOpen_lt continuous_const (doubleHeight B r hr).continuous.abs).mem_nhds hz
        filter_upwards [hnear] with w hw
        exact bump.zero_of_le_dist (by rw [dist_zero_right, Real.norm_eq_abs]; exact hw.le)
      have hsecCongr : ∀ (V₁ V₂ : (z : Double B) → TangentSpace 𝓘(ℝ, E) z),
          (∀ w, V₁ w = V₂ w) →
          (fun w => (⟨w, V₁ w⟩ : TangentBundle 𝓘(ℝ, E) (Double B))) =
            (fun w => (⟨w, V₂ w⟩ : TangentBundle 𝓘(ℝ, E) (Double B))) :=
        fun V₁ V₂ h => funext fun w => congrArg _ (h w)
      by_cases hz8 : |doubleHeight B r hr z| < a / 8
      · have hev : (fun w => (⟨w, X w⟩ : TangentBundle 𝓘(ℝ, E) (Double B)))
            =ᶠ[𝓝 z]
            (fun w => (⟨w, Pseam w⟩ : TangentBundle 𝓘(ℝ, E) (Double B))) := by
          filter_upwards [hρ1 hz8] with w hw
          refine congrArg (fun v : TangentSpace 𝓘(ℝ, E) w =>
            (⟨w, v⟩ : TangentBundle 𝓘(ℝ, E) (Double B))) ?_
          rw [hXsec w, hw]
          simp
        refine (hPseamSmooth.contMDiffAt (pdSeam.open_target.mem_nhds ?_)).congr_of_eventuallyEq hev
        rw [hseamMem]
        linarith
      · by_cases hzlt : |doubleHeight B r hr z| < a
        · have hznz : doubleHeight B r hr z ≠ 0 := by
            intro h0
            exact hz8 (by rw [h0, abs_zero]; linarith)
          rcases lt_or_gt_of_ne hznz with hlt | hgt
          · have hev : (fun w => (⟨w, X w⟩ : TangentBundle 𝓘(ℝ, E) (Double B)))
                =ᶠ[𝓝 z]
                (fun w => (⟨w, ρ w • Pseam w + (1 - ρ w) • Pneg w⟩ :
                  TangentBundle 𝓘(ℝ, E) (Double B))) := by
              have hnear : ∀ᶠ w in 𝓝 z, doubleHeight B r hr w < 0 :=
                (isOpen_lt (doubleHeight B r hr).continuous continuous_const).mem_nhds hlt
              filter_upwards [hnear] with w hw
              refine congrArg (fun v : TangentSpace 𝓘(ℝ, E) w =>
                (⟨w, v⟩ : TangentBundle 𝓘(ℝ, E) (Double B))) ?_
              rw [hXsec w]
              simp only [Pout]
              rw [if_neg (not_lt.mpr hw.le)]
            have hsum : ContMDiffAt 𝓘(ℝ, E) (𝓘(ℝ, E)).tangent ∞
                (fun w => (⟨w, ρ w • Pseam w + (1 - ρ w) • Pneg w⟩ :
                  TangentBundle 𝓘(ℝ, E) (Double B))) z :=
              ((hρsmooth.contMDiffAt).smul_section
                (hPseamSmooth.contMDiffAt (pdSeam.open_target.mem_nhds ((hseamMem z).mpr hzlt))))
                |>.add_section
                (((contMDiffAt_const.sub hρsmooth.contMDiffAt).smul_section
                  (hPnegSmooth.contMDiffAt (pdNeg.open_target.mem_nhds ((hnegMem z).mpr hlt)))))
            exact hsum.congr_of_eventuallyEq hev
          · have hev : (fun w => (⟨w, X w⟩ : TangentBundle 𝓘(ℝ, E) (Double B)))
                =ᶠ[𝓝 z]
                (fun w => (⟨w, ρ w • Pseam w + (1 - ρ w) • Ppos w⟩ :
                  TangentBundle 𝓘(ℝ, E) (Double B))) := by
              have hnear : ∀ᶠ w in 𝓝 z, 0 < doubleHeight B r hr w :=
                (isOpen_lt continuous_const (doubleHeight B r hr).continuous).mem_nhds hgt
              filter_upwards [hnear] with w hw
              refine congrArg (fun v : TangentSpace 𝓘(ℝ, E) w =>
                (⟨w, v⟩ : TangentBundle 𝓘(ℝ, E) (Double B))) ?_
              rw [hXsec w]
              simp only [Pout]
              rw [if_pos hw]
            have hsum : ContMDiffAt 𝓘(ℝ, E) (𝓘(ℝ, E)).tangent ∞
                (fun w => (⟨w, ρ w • Pseam w + (1 - ρ w) • Ppos w⟩ :
                  TangentBundle 𝓘(ℝ, E) (Double B))) z :=
              ((hρsmooth.contMDiffAt).smul_section
                (hPseamSmooth.contMDiffAt (pdSeam.open_target.mem_nhds ((hseamMem z).mpr hzlt))))
                |>.add_section
                (((contMDiffAt_const.sub hρsmooth.contMDiffAt).smul_section
                  (hPposSmooth.contMDiffAt (pdPos.open_target.mem_nhds ((hposMem z).mpr hgt)))))
            exact hsum.congr_of_eventuallyEq hev
        · have hza : a ≤ |doubleHeight B r hr z| := le_of_not_gt hzlt
          have hgt4 : a / 4 < |doubleHeight B r hr z| := by linarith
          have hznz : doubleHeight B r hr z ≠ 0 := by
            intro h0
            rw [h0, abs_zero] at hza
            linarith
          have hev : (fun w => (⟨w, X w⟩ : TangentBundle 𝓘(ℝ, E) (Double B))) =ᶠ[𝓝 z]
              (fun w => (⟨w, Pout w⟩ : TangentBundle 𝓘(ℝ, E) (Double B))) := by
            filter_upwards [hρ0 hgt4] with w hw
            refine congrArg (fun v : TangentSpace 𝓘(ℝ, E) w =>
              (⟨w, v⟩ : TangentBundle 𝓘(ℝ, E) (Double B))) ?_
            rw [hXsec w, hw]
            simp
          rcases lt_or_gt_of_ne hznz with hlt | hgt
          · have hev2 : (fun w =>
                (⟨w, Pout w⟩ : TangentBundle 𝓘(ℝ, E) (Double B))) =ᶠ[𝓝 z]
                (fun w => (⟨w, Pneg w⟩ : TangentBundle 𝓘(ℝ, E) (Double B))) := by
              have hnear : ∀ᶠ w in 𝓝 z, doubleHeight B r hr w < 0 :=
                (isOpen_lt (doubleHeight B r hr).continuous continuous_const).mem_nhds hlt
              filter_upwards [hnear] with w hw
              refine congrArg (fun v : TangentSpace 𝓘(ℝ, E) w =>
                (⟨w, v⟩ : TangentBundle 𝓘(ℝ, E) (Double B))) ?_
              simp only [Pout]
              rw [if_neg (not_lt.mpr hw.le)]
            exact ((hPnegSmooth.contMDiffAt
              (pdNeg.open_target.mem_nhds ((hnegMem z).mpr hlt)))).congr_of_eventuallyEq
              (hev.trans hev2)
          · have hev2 : (fun w =>
                (⟨w, Pout w⟩ : TangentBundle 𝓘(ℝ, E) (Double B))) =ᶠ[𝓝 z]
                (fun w => (⟨w, Ppos w⟩ : TangentBundle 𝓘(ℝ, E) (Double B))) := by
              have hnear : ∀ᶠ w in 𝓝 z, 0 < doubleHeight B r hr w :=
                (isOpen_lt continuous_const (doubleHeight B r hr).continuous).mem_nhds hgt
              filter_upwards [hnear] with w hw
              refine congrArg (fun v : TangentSpace 𝓘(ℝ, E) w =>
                (⟨w, v⟩ : TangentBundle 𝓘(ℝ, E) (Double B))) ?_
              simp only [Pout]
              rw [if_pos hw]
            exact ((hPposSmooth.contMDiffAt
              (pdPos.open_target.mem_nhds ((hposMem z).mpr hgt)))).congr_of_eventuallyEq
              (hev.trans hev2)
    exact hX
  · have hbin1 : IsClosed {q : B × ℝ | |q.2| ≤ a / 4} :=
      isClosed_le continuous_snd.abs continuous_const
    have hρball : ∀ z : Double B, ρ z ≠ 0 → |doubleHeight B r hr z| < a / 4 := by
      intro z hz
      have hz' : bump (doubleHeight B r hr z) ≠ 0 := hz
      have hball : doubleHeight B r hr z ∈ Metric.ball (0 : ℝ) bump.rOut := by
        rw [← bump.support_eq]
        exact Function.mem_support.mpr hz'
      have hlt := Metric.mem_ball.mp hball
      rwa [dist_zero_right, Real.norm_eq_abs] at hlt
    have hcptSeam : IsCompact (doubleSeamPatch B r hr hz hn c hheight hsmall hc ha b₀ ''
        (tsupport W ∩ {q : B × ℝ | |q.2| ≤ a / 4})) := by
      refine (hWsupp.inter_right hbin1).image_of_continuousOn ?_
      refine (hseamσ b₀).continuousOn.mono ?_
      intro q hq
      change |q.2| < a
      exact lt_of_le_of_lt hq.2 (by linarith)
    have hcptPos : IsCompact (doublePositive B '' tsupport V) :=
      hsupp.image (doublePositive B).continuous
    have hcptNeg : IsCompact (doubleNegative B '' tsupport V) :=
      hsupp.image (doubleNegative B).continuous
    have hclPos : IsClosed (doublePositive B '' tsupport V) := hcptPos.isClosed
    have hclNeg : IsClosed (doubleNegative B '' tsupport V) := hcptNeg.isClosed
    have hsuppPseam : tsupport (fun z => ρ z • Pseam z) ⊆
        doubleSeamPatch B r hr hz hn c hheight hsmall hc ha b₀ ''
          (tsupport W ∩ {q : B × ℝ | |q.2| ≤ a / 4}) := by
      refine (IsClosed.closure_subset_iff hcptSeam.isClosed).mpr ?_
      intro z hz
      have hz' : ρ z • Pseam z ≠ 0 := hz
      have hPne : Pseam z ≠ 0 := fun h0 => hz' (by
        rw [h0, smul_zero])
      have hρne : ρ z ≠ 0 := fun h0 => hz' (by
        rw [h0, zero_smul])
      have hzt : z ∈ pdSeam.target := by
        by_contra h
        exact hPne (pushforwardField_of_not_mem _ _ _ _ h)
      have hWne : W (pdSeam.symm z) ≠ 0 := by
        intro h0
        refine hPne ?_
        change pushforwardField (J.prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, E) pdSeam W z = 0
        rw [pushforwardField_of_mem _ _ _ _ hzt, _root_.VectorField.mpullback_apply, h0, map_zero]
      have hb : |(pdSeam.symm z).2| ≤ a / 4 := by
        have h := hρball z hρne
        rw [hseamHeight z hzt] at h
        exact h.le
      exact ⟨pdSeam.symm z, ⟨subset_tsupport _ hWne, hb⟩, hseamPatchSymm z hzt⟩
    have hsuppPos : tsupport (fun z => Ppos z) ⊆ doublePositive B '' tsupport V := by
      refine (IsClosed.closure_subset_iff hclPos).mpr ?_
      intro z hz
      exact support_pushforwardField_subset I 𝓘(ℝ, E) pdPos V hz
    have hsuppNeg : tsupport (fun z => Pneg z) ⊆ doubleNegative B '' tsupport V := by
      refine (IsClosed.closure_subset_iff hclNeg).mpr ?_
      intro z hz
      exact support_pushforwardField_subset I 𝓘(ℝ, E) pdNeg V hz
    have hsuppPout : Function.support Pout ⊆ doublePositive B '' tsupport V ∪
        doubleNegative B '' tsupport V := by
      intro z hz
      have hne : Pout z ≠ 0 := hz
      by_cases hpos : 0 < doubleHeight B r hr z
      · have hne' : Ppos z ≠ 0 := by simpa only [Pout, if_pos hpos] using hne
        exact Or.inl (hsuppPos (subset_tsupport _ (Function.mem_support.mpr hne')))
      · have hne' : Pneg z ≠ 0 := by simpa only [Pout, if_neg hpos] using hne
        exact Or.inr (hsuppNeg (subset_tsupport _ (Function.mem_support.mpr hne')))
    have hsuppRest : tsupport (fun z => (1 - ρ z) • Pout z) ⊆
        doublePositive B '' tsupport V ∪ doubleNegative B '' tsupport V := by
      refine (IsClosed.closure_subset_iff (hclPos.union hclNeg)).mpr ?_
      intro z hz
      have hz' : (1 - ρ z) • Pout z ≠ 0 := hz
      have hPne : Pout z ≠ 0 := fun h0 => hz' (by
        rw [h0, smul_zero])
      exact hsuppPout (Function.mem_support.mpr hPne)
    have hsuppSum : Function.support X ⊆ tsupport (fun z => ρ z • Pseam z) ∪
        tsupport (fun z => (1 - ρ z) • Pout z) := by
      intro z hz
      have hz' : X z ≠ 0 := hz
      by_cases h1 : ρ z • Pseam z = 0
      · by_cases h2 : (1 - ρ z) • Pout z = 0
        · exact absurd (by rw [hXsec z, h1, h2, add_zero]) hz'
        · exact Or.inr (subset_tsupport _ h2)
      · exact Or.inl (subset_tsupport _ h1)
    have hsuppX : tsupport X ⊆ doubleSeamPatch B r hr hz hn c hheight hsmall hc ha b₀ ''
        (tsupport W ∩ {q : B × ℝ | |q.2| ≤ a / 4}) ∪
          (doublePositive B '' tsupport V ∪ doubleNegative B '' tsupport V) := by
      exact (closure_mono hsuppSum).trans (closure_minimal
        (union_subset (Subset.trans hsuppPseam subset_union_left)
          (Subset.trans hsuppRest subset_union_right))
        (hcptSeam.isClosed.union (hclPos.union hclNeg)))
    exact (hcptSeam.union (hcptPos.union hcptNeg)).of_isClosed_subset
      (isClosed_tsupport X) hsuppX
  · intro x hx
    have hxsrc : x ∈ pdPos.source := by
      change x ∈ (doublePositivePatch B r hr hn).source
      exact hx
    have hPpos : Ppos (doublePositive B x) = mfderiv I 𝓘(ℝ, E) (doublePositive B) x (V x) := by
      have hzt : doublePositive B x ∈ pdPos.target := by
        rw [hposMem]
        simpa using hx
      change pushforwardField I 𝓘(ℝ, E) pdPos V (doublePositive B x) = _
      rw [pushforwardField_of_mem I 𝓘(ℝ, E) pdPos V hzt]
      rw [show _root_.VectorField.mpullback 𝓘(ℝ, E) I pdPos.symm V (doublePositive B x) =
          mfderiv I 𝓘(ℝ, E) pdPos x (V x) from
        DifferentialGeometry.VectorField.mpullback_symm_partialDiffeomorph_apply
          pdPos (by norm_num) V hxsrc]
      rfl
    have hPout : Pout (doublePositive B x) = mfderiv I 𝓘(ℝ, E) (doublePositive B) x (V x) := by
      have hpos : 0 < doubleHeight B r hr (doublePositive B x) := by simpa using hx
      simp only [Pout, if_pos hpos]
      exact hPpos
    by_cases hxa : r x < a
    · obtain ⟨q₀, hq₀⟩ := hsmall x hxa.le
      let q : B × ℝ := (q₀.1, q₀.2.val)
      have hq2 : q.2 = r x := by
        change q₀.2.val = r x
        rw [← hheight q₀, hq₀]
      have hqpos : 0 < q.2 := by rw [hq2]; exact hx
      have hqa : |q.2| < a := by rw [abs_of_pos hqpos, hq2]; exact hxa
      have hstrip : q ∈ doublePositiveStrip B (a := a) := ⟨hqpos, by rw [hq2]; exact hxa⟩
      have hzEq : seam q = doublePositive B x := by
        change doubleSeamPatch B r hr hz hn c hheight hsmall hc ha b₀ q = doublePositive B x
        rw [doubleSeamPatch_of_nonneg B r hr hz hn c hheight hsmall hc ha b₀ hqa hqpos.le, hq₀]
      have hzx : x = foldSeam q := by
        have hfold : foldSeam q = x := by
          rw [show foldSeam q = doubleFold B (doublePositive B x) from congrArg (doubleFold B) hzEq]
          rfl
        exact hfold.symm
      have hqsrc : q ∈ (pdSeam.trans pdPos.symm).source := by
        refine ⟨?_, ?_⟩
        · change q ∈ (doubleSeamPatch B r hr hz hn c hheight hsmall hc ha b₀).source
          rwa [doubleSeamPatch_source]
        · change seam q ∈ pdPos.target
          rw [hzEq, hposMem]
          exact hx
      have hcrux : mfderiv (J.prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, E) seam q (W q) =
          mfderiv I 𝓘(ℝ, E) (doublePositive B) x (V x) := by
        have hchain := mfderiv_doubleSeamPatch_eq_comp_doubleFold I B J r hr hz hn c hheight hsmall
          hc ha b₀ hposσ hfoldPos (hseamσ b₀) hstrip
        have hinv : (mfderiv (J.prod 𝓘(ℝ, ℝ)) I foldSeam q).IsInvertible :=
          DifferentialGeometry.VectorField.isInvertible_mfderiv_partialDiffeomorph
            (pdSeam.trans pdPos.symm) (by norm_num) hqsrc
        have hu : W q = (mfderiv (J.prod 𝓘(ℝ, ℝ)) I foldSeam q).inverse (V (foldSeam q)) :=
          hWdatum' q hstrip
        have hmain := comp_inverse_apply_eq (I₁ := J.prod 𝓘(ℝ, ℝ)) (I₂ := I)
            (I₃ := 𝓘(ℝ, E))
          (f := foldSeam) (g := doublePositive B) (s := seam) (x := q) (u := W) (w := V)
          hchain hinv hu
        rw [hmain, ← hzx]
      have hPseamEq : Pseam (doublePositive B x) = mfderiv (J.prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, E)
        seam q (W q) := by
        have h1 : Pseam (doublePositive B x) = Pseam (seam q) := by rw [← hzEq]
        rw [h1]
        have hseamq : seam q ∈ pdSeam.target := by
          have h2 : doubleHeight B r hr (seam q) = q.2 := by
            change doubleHeight B r hr
              (doubleSeamPatch B r hr hz hn c hheight hsmall hc ha b₀ q) = q.2
            exact doubleHeight_seamPatch B r hr hz hn c hheight hsmall hc ha b₀ hqa
          rw [hseamMem, h2]
          exact hqa
        change pushforwardField (J.prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, E) pdSeam W (seam q) = _
        rw [pushforwardField_of_mem (J.prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, E) pdSeam W hseamq]
        exact DifferentialGeometry.VectorField.mpullback_symm_partialDiffeomorph_apply
          pdSeam (by norm_num) W (by
            change q ∈ (doubleSeamPatch B r hr hz hn c hheight hsmall hc ha b₀).source
            rwa [doubleSeamPatch_source])
      rw [hXsec, hPseamEq, hPout, hcrux]
      rw [← add_smul, add_sub_cancel, one_smul]
    · have hρ0 : ρ (doublePositive B x) = 0 := by
        refine bump.zero_of_le_dist ?_
        rw [dist_zero_right, Real.norm_eq_abs, show doubleHeight B r hr (doublePositive B x)
          = r x from rfl]
        have hra : bump.rOut ≤ a := by
          rw [show bump.rOut = a / 4 from rfl]
          linarith
        exact hra.trans ((le_of_not_gt hxa).trans (le_abs_self _))
      rw [hXsec, hρ0, zero_smul, zero_add, sub_zero, one_smul]
      exact hPout
  · intro q hq0
    have hqabs : |q.2| < a := by rw [hq0, abs_zero]; exact ha
    have hdh : doubleHeight B r hr (seam q) = q.2 := by
      change doubleHeight B r hr (doubleSeamPatch B r hr hz hn c hheight hsmall hc ha b₀ q) = q.2
      exact doubleHeight_seamPatch B r hr hz hn c hheight hsmall hc ha b₀ hqabs
    have hqsrc : q ∈ pdSeam.source := by
      change q ∈ (doubleSeamPatch B r hr hz hn c hheight hsmall hc ha b₀).source
      rwa [doubleSeamPatch_source]
    have hzt : seam q ∈ pdSeam.target := by
      rw [hseamMem, hdh, hq0, abs_zero]
      exact ha
    have hPseamVal : Pseam (seam q) =
        mfderiv (J.prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, E) seam q (W q) := by
      change pushforwardField (J.prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, E) pdSeam W (seam q) = _
      rw [pushforwardField_of_mem (J.prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, E) pdSeam W hzt]
      exact DifferentialGeometry.VectorField.mpullback_symm_partialDiffeomorph_apply
        pdSeam (by norm_num) W hqsrc
    have hρ1 : ρ (seam q) = 1 := by
      refine bump.one_of_mem_closedBall ?_
      rw [Metric.mem_closedBall, dist_zero_right, Real.norm_eq_abs, hdh, hq0, abs_zero]
      exact bump.rIn_pos.le
    rw [hXsec, hρ1, hPseamVal]
    simp only [one_smul, sub_self, zero_smul, add_zero]
    rfl
  · intro q hq0
    have hqabs : |q.2| < a := by rw [hq0, abs_zero]; exact ha
    have hdh : doubleHeight B r hr (seam q) = q.2 := by
      change doubleHeight B r hr (doubleSeamPatch B r hr hz hn c hheight hsmall hc ha b₀ q) = q.2
      exact doubleHeight_seamPatch B r hr hz hn c hheight hsmall hc ha b₀ hqabs
    have hqsrc : q ∈ pdSeam.source := by
      change q ∈ (doubleSeamPatch B r hr hz hn c hheight hsmall hc ha b₀).source
      rwa [doubleSeamPatch_source]
    have hzt : seam q ∈ pdSeam.target := by
      rw [hseamMem, hdh, hq0, abs_zero]
      exact ha
    have hPseamVal : Pseam (seam q) =
        mfderiv (J.prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, E) seam q (W q) := by
      change pushforwardField (J.prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, E) pdSeam W (seam q) = _
      rw [pushforwardField_of_mem (J.prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, E) pdSeam W hzt]
      exact DifferentialGeometry.VectorField.mpullback_symm_partialDiffeomorph_apply
        pdSeam (by norm_num) W hqsrc
    have hρ1 : ρ (seam q) = 1 := by
      refine bump.one_of_mem_closedBall ?_
      rw [Metric.mem_closedBall, dist_zero_right, Real.norm_eq_abs, hdh, hq0, abs_zero]
      exact bump.rIn_pos.le
    have hXval : X (seam q) = mfderiv (J.prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, E) seam q (W q) := by
      rw [hXsec, hρ1, hPseamVal]
      simp only [one_smul, sub_self, zero_smul, add_zero]
    have hinv : (mfderiv (J.prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, E) seam q).IsInvertible :=
      DifferentialGeometry.VectorField.isInvertible_mfderiv_partialDiffeomorph
        pdSeam (by norm_num) hqsrc
    rw [show X (doubleSeamPatch B r hr hz hn c hheight hsmall hc ha b₀ q) =
      mfderiv (J.prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, E) seam q (W q) from hXval, hinv.inverse_apply_self]
    exact hWtan q hq0

theorem exists_doubleSeam_transport_of_eq_zero_on_collar
    {M E H F G : Type} [TopologicalSpace M] [CompactSpace M] [T2Space M]
    [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H] [ChartedSpace H M]
    (I : ModelWithCorners ℝ E H) [IsManifold I ∞ M]
    (B : Set M) [NormedAddCommGroup F] [NormedSpace ℝ F]
    [TopologicalSpace G] [ChartedSpace G B] (J : ModelWithCorners ℝ F G)
    [IsManifold J ∞ B] [BoundarylessManifold J B]
    (L : (F × ℝ) ≃L[ℝ] E)
    (r : C(M, ℝ)) (hr : ∀ b : B, r b.val = 0)
    (hrsmooth : ContMDiff I 𝓘(ℝ, ℝ) ∞ r)
    (hz : ∀ x, r x = 0 → x ∈ B) (hn : ∀ x, 0 ≤ r x)
    (hI : ∀ x, 0 < r x → I.IsInteriorPoint x)
    {a : ℝ} (c : C(B × Icc (0 : ℝ) a, M))
    (hheight : ∀ q, r (c q) = q.2.val)
    (hsmall : ∀ x, r x ≤ a → x ∈ range c) (hc : IsEmbedding c) (ha : 0 < a)
    (d : Diffeomorph (J.prod 𝓘(ℝ, ℝ)) I
      (doublePositiveStrip B (a := a)) (doublePositiveBand r (a := a)) ∞)
    (hd : ∀ q, (d q).val = c (q.val.1, ⟨q.val.2, q.property.1.le, q.property.2.le⟩))
    (b₀ : B)
    (V : ∀ x : M, TangentSpace I x)
    (hV : ContMDiff I I.tangent ∞ (fun x => (⟨x, V x⟩ : TangentBundle I M)))
    (hsupp : IsCompact (tsupport V))
    (hVzero : ∀ x : M, r x < a → V x = 0) :
    ∃ (A : ChartedSpace E (Double B)) (hA : IsManifold 𝓘(ℝ, E) ∞ (Double B))
      (hT : T2Space (Double B)),
      let _ := A
      let _ := hA
      let _ := hT
      ∃ X : (z : Double B) → TangentSpace 𝓘(ℝ, E) z,
        ContMDiff 𝓘(ℝ, E) (𝓘(ℝ, E)).tangent ∞
          (fun z => (⟨z, X z⟩ : TangentBundle 𝓘(ℝ, E) (Double B))) ∧
        IsCompact (tsupport X) ∧
        (∀ x : M, 0 < r x →
          X (doublePositive B x) = mfderiv I 𝓘(ℝ, E) (doublePositive B) x (V x)) ∧
        (∀ q : B × ℝ, q.2 = 0 →
          X (doubleSeamPatch B r hr hz hn c hheight hsmall hc ha b₀ q) =
            mfderiv (J.prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, E)
              (doubleSeamPatch B r hr hz hn c hheight hsmall hc ha b₀) q 0) ∧
        (∀ q : B × ℝ, q.2 = 0 →
          ((mfderiv (J.prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, E)
              (doubleSeamPatch B r hr hz hn c hheight hsmall hc ha b₀) q).inverse
            (X (doubleSeamPatch B r hr hz hn c hheight hsmall hc ha b₀ q))).2 = 0) := by
  refine exists_doubleSeam_transport I B J L r hr hrsmooth hz hn hI c hheight hsmall hc ha d hd
    b₀ V hV hsupp 0
    (Bundle.contMDiff_zeroSection (𝕜 := ℝ) (IB := J.prod 𝓘(ℝ, ℝ))
      (F := F × ℝ) (E := TangentSpace (J.prod 𝓘(ℝ, ℝ))))
    (by
      refine isCompact_empty.of_isClosed_subset (isClosed_tsupport _) ?_
      refine (IsClosed.closure_subset_iff isClosed_empty).mpr ?_
      intro z hz
      exact Function.mem_support.mp hz rfl)
    (fun q _ => rfl) ?_
  intro q hq
  have hqa : |q.2| < a := by rw [abs_of_pos hq.1]; exact hq.2
  have hdh : doubleHeight B r hr
      (doubleSeamPatch B r hr hz hn c hheight hsmall hc ha b₀ q) = q.2 :=
    doubleHeight_seamPatch B r hr hz hn c hheight hsmall hc ha b₀ hqa
  have hpos : 0 < doubleHeight B r hr
      (doubleSeamPatch B r hr hz hn c hheight hsmall hc ha b₀ q) := by
    rw [hdh]; exact hq.1
  have hzEq : doublePositive B
      (doubleFold B (doubleSeamPatch B r hr hz hn c hheight hsmall hc ha b₀ q)) =
      doubleSeamPatch B r hr hz hn c hheight hsmall hc ha b₀ q := by
    simpa using (doublePositivePatch B r hr hn).right_inv hpos
  have hrfold : r (doubleFold B
      (doubleSeamPatch B r hr hz hn c hheight hsmall hc ha b₀ q)) = q.2 := by
    rw [← hdh, ← hzEq]
    simp
  rw [hVzero _ (by rw [hrfold]; exact hq.2)]
  simp

end DifferentialGeometry.Topology
