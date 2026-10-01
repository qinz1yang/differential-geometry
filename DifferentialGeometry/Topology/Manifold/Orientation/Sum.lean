import DifferentialGeometry.Topology.Manifold.Orientation
import DifferentialGeometry.Topology.Manifold.OrientationDiffeomorphTransport

noncomputable section

open Bundle Filter Manifold Set Topology TopologicalSpace
open scoped Manifold ContDiff

namespace DifferentialGeometry

universe u

section SumCharts

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] [Nonempty H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  {M' : Type*} [TopologicalSpace M'] [ChartedSpace H M'] [IsManifold I ∞ M']

omit [FiniteDimensional ℝ E] [IsManifold I ∞ M] [IsManifold I ∞ M'] in
theorem extChartAt_sum_inl_eq (p z : M) :
    extChartAt I (Sum.inl p : M ⊕ M') (Sum.inl z) = extChartAt I p z := by
  simp only [extChartAt, OpenPartialHomeomorph.extend_coe, Function.comp_apply,
    ChartedSpace.sum_chartAt_inl,
    OpenPartialHomeomorph.lift_openEmbedding_apply (chartAt H p) IsOpenEmbedding.inl (x := z)]

omit [FiniteDimensional ℝ E] [IsManifold I ∞ M] [IsManifold I ∞ M'] in
theorem extChartAt_sum_inr_eq (p z : M') :
    extChartAt I (Sum.inr p : M ⊕ M') (Sum.inr z) = extChartAt I p z := by
  simp only [extChartAt, OpenPartialHomeomorph.extend_coe, Function.comp_apply,
    ChartedSpace.sum_chartAt_inr,
    OpenPartialHomeomorph.lift_openEmbedding_apply (chartAt H p) IsOpenEmbedding.inr (x := z)]

omit [FiniteDimensional ℝ E] in
set_option backward.isDefEq.respectTransparency false in
theorem mfderiv_extChartAt_sum_inl (p z : M)
    (hzc : Sum.inl z ∈ (chartAt H (Sum.inl p : M ⊕ M')).source) :
    (mfderiv I 𝓘(ℝ,E) (extChartAt I (Sum.inl p : M ⊕ M')) (Sum.inl z) : E →L[ℝ] E) =
      (mfderiv I 𝓘(ℝ,E) (extChartAt I p) z : E →L[ℝ] E) := by
  have hev : (↑(extChartAt I (Sum.inl p : M ⊕ M')) ∘ (@Sum.inl M M')) =ᶠ[𝓝 z]
      (↑(extChartAt I p) : M → E) :=
    Filter.Eventually.of_forall (fun w => extChartAt_sum_inl_eq p w)
  have h1 : (mfderiv I 𝓘(ℝ,E)
      (↑(extChartAt I (Sum.inl p : M ⊕ M')) ∘ (@Sum.inl M M')) z : E →L[ℝ] E) =
      (mfderiv I 𝓘(ℝ,E) (extChartAt I p) z : E →L[ℝ] E) :=
    Filter.EventuallyEq.mfderiv_eq hev
  have hcomp := mfderiv_comp (x := z) (f := (@Sum.inl M M'))
    (g := (extChartAt I (Sum.inl p : M ⊕ M')))
    (mdifferentiableAt_extChartAt hzc) (hasMFDerivAt_inl.mdifferentiableAt)
  rw [mfderiv_sumInl (p := (Sum.inl z : M ⊕ M'))] at hcomp
  have h2 : (mfderiv I 𝓘(ℝ,E) (extChartAt I (Sum.inl p : M ⊕ M')) (Sum.inl z) :
      E →L[ℝ] E) =
      (mfderiv I 𝓘(ℝ,E) (↑(extChartAt I (Sum.inl p : M ⊕ M')) ∘ (@Sum.inl M M')) z :
        E →L[ℝ] E) := by
    rw [hcomp]
    exact (ContinuousLinearMap.comp_id
      (mfderiv I 𝓘(ℝ,E) (extChartAt I (Sum.inl p : M ⊕ M')) (Sum.inl z))).symm
  exact h2.trans h1

omit [FiniteDimensional ℝ E] in
set_option backward.isDefEq.respectTransparency false in
theorem mfderiv_extChartAt_sum_inr (p z : M')
    (hzc : Sum.inr z ∈ (chartAt H (Sum.inr p : M ⊕ M')).source) :
    (mfderiv I 𝓘(ℝ,E) (extChartAt I (Sum.inr p : M ⊕ M')) (Sum.inr z) : E →L[ℝ] E) =
      (mfderiv I 𝓘(ℝ,E) (extChartAt I p) z : E →L[ℝ] E) := by
  have hev : (↑(extChartAt I (Sum.inr p : M ⊕ M')) ∘ (@Sum.inr M M')) =ᶠ[𝓝 z]
      (↑(extChartAt I p) : M' → E) :=
    Filter.Eventually.of_forall (fun w => extChartAt_sum_inr_eq p w)
  have h1 : (mfderiv I 𝓘(ℝ,E)
      (↑(extChartAt I (Sum.inr p : M ⊕ M')) ∘ (@Sum.inr M M')) z : E →L[ℝ] E) =
      (mfderiv I 𝓘(ℝ,E) (extChartAt I p) z : E →L[ℝ] E) :=
    Filter.EventuallyEq.mfderiv_eq hev
  have hcomp := mfderiv_comp (x := z) (f := (@Sum.inr M M'))
    (g := (extChartAt I (Sum.inr p : M ⊕ M')))
    (mdifferentiableAt_extChartAt hzc) (hasMFDerivAt_inr.mdifferentiableAt)
  rw [mfderiv_sumInr] at hcomp
  have h2 : (mfderiv I 𝓘(ℝ,E) (extChartAt I (Sum.inr p : M ⊕ M')) (Sum.inr z) :
      E →L[ℝ] E) =
      (mfderiv I 𝓘(ℝ,E) (↑(extChartAt I (Sum.inr p : M ⊕ M')) ∘ (@Sum.inr M M')) z :
        E →L[ℝ] E) := by
    rw [hcomp]
    exact (ContinuousLinearMap.comp_id
      (mfderiv I 𝓘(ℝ,E) (extChartAt I (Sum.inr p : M ⊕ M')) (Sum.inr z))).symm
  exact h2.trans h1

omit [FiniteDimensional ℝ E] in
set_option backward.isDefEq.respectTransparency false in
theorem tangentChartEquiv_sum_inl (p z : M)
    (h : Sum.inl z ∈ (trivializationAt E (TangentSpace I) (Sum.inl p : M ⊕ M')).baseSet)
    (hz : z ∈ (trivializationAt E (TangentSpace I) p).baseSet) :
    tangentChartEquiv I (M ⊕ M') (Sum.inl p) (Sum.inl z) h =
      tangentChartEquiv I M p z hz := by
  have hzc : Sum.inl z ∈ (chartAt H (Sum.inl p : M ⊕ M')).source := by
    simpa only [TangentBundle.trivializationAt_baseSet] using h
  have hz' : z ∈ (chartAt H p).source := by
    rw [TangentBundle.trivializationAt_baseSet] at hz
    exact hz
  refine LinearEquiv.ext fun v => ?_
  change (trivializationAt E (TangentSpace I) (Sum.inl p : M ⊕ M')).linearEquivAt ℝ
      (Sum.inl z) h v =
    (trivializationAt E (TangentSpace I) p).linearEquivAt ℝ z hz v
  rw [Trivialization.linearEquivAt_apply, Trivialization.linearEquivAt_apply]
  rw [← Trivialization.continuousLinearMapAt_apply_of_mem ℝ _ h,
    ← Trivialization.continuousLinearMapAt_apply_of_mem ℝ _ hz]
  rw [TangentBundle.continuousLinearMapAt_trivializationAt hzc,
    TangentBundle.continuousLinearMapAt_trivializationAt hz']
  exact congrArg (fun L : E →L[ℝ] E => L v) (mfderiv_extChartAt_sum_inl p z hzc)

omit [FiniteDimensional ℝ E] in
set_option backward.isDefEq.respectTransparency false in
theorem tangentChartEquiv_sum_inr (p z : M')
    (h : Sum.inr z ∈ (trivializationAt E (TangentSpace I) (Sum.inr p : M ⊕ M')).baseSet)
    (hz : z ∈ (trivializationAt E (TangentSpace I) p).baseSet) :
    tangentChartEquiv I (M ⊕ M') (Sum.inr p) (Sum.inr z) h =
      tangentChartEquiv I M' p z hz := by
  have hzc : Sum.inr z ∈ (chartAt H (Sum.inr p : M ⊕ M')).source := by
    simpa only [TangentBundle.trivializationAt_baseSet] using h
  have hz' : z ∈ (chartAt H p).source := by
    rw [TangentBundle.trivializationAt_baseSet] at hz
    exact hz
  refine LinearEquiv.ext fun v => ?_
  change (trivializationAt E (TangentSpace I) (Sum.inr p : M ⊕ M')).linearEquivAt ℝ
      (Sum.inr z) h v =
    (trivializationAt E (TangentSpace I) p).linearEquivAt ℝ z hz v
  rw [Trivialization.linearEquivAt_apply, Trivialization.linearEquivAt_apply]
  rw [← Trivialization.continuousLinearMapAt_apply_of_mem ℝ _ h,
    ← Trivialization.continuousLinearMapAt_apply_of_mem ℝ _ hz]
  rw [TangentBundle.continuousLinearMapAt_trivializationAt hzc,
    TangentBundle.continuousLinearMapAt_trivializationAt hz']
  exact congrArg (fun L : E →L[ℝ] E => L v) (mfderiv_extChartAt_sum_inr p z hzc)

end SumCharts

namespace ManifoldOrientation

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] [Nonempty H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  {M' : Type*} [TopologicalSpace M'] [ChartedSpace H M'] [IsManifold I ∞ M']
  {n : ℕ}

def sum (oM : ManifoldOrientation I M n) (oN : ManifoldOrientation I M' n) :
    ManifoldOrientation I (M ⊕ M') n where
  dimension_eq := oM.dimension_eq
  orientation p := match p with
    | Sum.inl x => oM.orientation x
    | Sum.inr y => oN.orientation y
  locally_constant := by
    intro p x hx
    rcases p with p₀ | p₀'
    · rcases x with x₀ | x₀'
      · have hx' : x₀ ∈ (trivializationAt E (TangentSpace I) p₀).baseSet := by
          rw [TangentBundle.trivializationAt_baseSet]
          rw [TangentBundle.trivializationAt_baseSet, ChartedSpace.sum_chartAt_inl,
            OpenPartialHomeomorph.lift_openEmbedding_source] at hx
          obtain ⟨w, hw, hwz⟩ := hx
          rwa [Sum.inl.inj hwz] at hw
        obtain ⟨U, hUopen, hxU, hUsub, hlc⟩ := oM.locally_constant p₀ x₀ hx'
        refine ⟨Sum.inl '' U, IsOpenEmbedding.inl.isOpenMap U hUopen, ⟨x₀, hxU, rfl⟩,
          ?_, ?_⟩
        · intro y hy
          obtain ⟨w, hw, rfl⟩ := hy
          rw [TangentBundle.trivializationAt_baseSet, ChartedSpace.sum_chartAt_inl,
            OpenPartialHomeomorph.lift_openEmbedding_source]
          exact ⟨w, hUsub hw, rfl⟩
        · intro y hy
          obtain ⟨w, hw, rfl⟩ := hy
          rw [tangentChartEquiv_sum_inl p₀ w _ (hUsub hw),
            tangentChartEquiv_sum_inl p₀ x₀ hx hx']
          exact hlc w hw
      · exfalso
        rw [TangentBundle.trivializationAt_baseSet, ChartedSpace.sum_chartAt_inl,
          OpenPartialHomeomorph.lift_openEmbedding_source] at hx
        obtain ⟨w, -, hw⟩ := hx
        exact Sum.inl_ne_inr hw
    · rcases x with x₀ | x₀'
      · exfalso
        rw [TangentBundle.trivializationAt_baseSet, ChartedSpace.sum_chartAt_inr,
          OpenPartialHomeomorph.lift_openEmbedding_source] at hx
        obtain ⟨w, -, hw⟩ := hx
        exact Sum.inr_ne_inl hw
      · have hx' : x₀' ∈ (trivializationAt E (TangentSpace I) p₀').baseSet := by
          rw [TangentBundle.trivializationAt_baseSet]
          rw [TangentBundle.trivializationAt_baseSet, ChartedSpace.sum_chartAt_inr,
            OpenPartialHomeomorph.lift_openEmbedding_source] at hx
          obtain ⟨w, hw, hwz⟩ := hx
          rwa [Sum.inr.inj hwz] at hw
        obtain ⟨U, hUopen, hxU, hUsub, hlc⟩ := oN.locally_constant p₀' x₀' hx'
        refine ⟨Sum.inr '' U, IsOpenEmbedding.inr.isOpenMap U hUopen, ⟨x₀', hxU, rfl⟩,
          ?_, ?_⟩
        · intro y hy
          obtain ⟨w, hw, rfl⟩ := hy
          rw [TangentBundle.trivializationAt_baseSet, ChartedSpace.sum_chartAt_inr,
            OpenPartialHomeomorph.lift_openEmbedding_source]
          exact ⟨w, hUsub hw, rfl⟩
        · intro y hy
          obtain ⟨w, hw, rfl⟩ := hy
          rw [tangentChartEquiv_sum_inr p₀' w _ (hUsub hw),
            tangentChartEquiv_sum_inr p₀' x₀' hx hx']
          exact hlc w hw

@[simp] theorem sum_orientation_inl (oM : ManifoldOrientation I M n)
    (oN : ManifoldOrientation I M' n) (x : M) :
    (sum oM oN).orientation (Sum.inl x) = oM.orientation x := rfl

@[simp] theorem sum_orientation_inr (oM : ManifoldOrientation I M n)
    (oN : ManifoldOrientation I M' n) (y : M') :
    (sum oM oN).orientation (Sum.inr y) = oN.orientation y := rfl

end ManifoldOrientation

end DifferentialGeometry
