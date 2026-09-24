import DifferentialGeometry.Topology.Manifold.Orientation
import DifferentialGeometry.Topology.Manifold.OrientationDiffeomorphTransport
import DifferentialGeometry.Topology.ThreeManifold.CutCapUncutComponentRealization

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

namespace Topology

namespace ClosedOrientedManifold

variable {n : ℕ}

def sum (X Y : ClosedOrientedManifold.{u} n) : ClosedOrientedManifold.{u} n where
  Carrier := X.Carrier ⊕ Y.Carrier
  orientation := ManifoldOrientation.sum X.orientation Y.orientation

@[simp] theorem sum_carrier (X Y : ClosedOrientedManifold.{u} n) :
    (sum X Y).Carrier = (X.Carrier ⊕ Y.Carrier : Type u) := rfl

@[simp] theorem sum_orientation (X Y : ClosedOrientedManifold.{u} n) :
    (sum X Y).orientation = ManifoldOrientation.sum X.orientation Y.orientation := rfl

variable {X Y : ClosedOrientedManifold.{u} n}

private noncomputable def sumInlRetract (x : X.Carrier) :
    X.Carrier ⊕ Y.Carrier → X.Carrier := Sum.elim id fun _ => x

private theorem continuous_sumInlRetract (x : X.Carrier) :
    Continuous (sumInlRetract (X := X) (Y := Y) x) :=
  continuous_sum_dom.2 ⟨continuous_id, continuous_const⟩

private theorem componentSet_sum_subset_range_inl (x : X.Carrier) :
    componentSet (sum X Y) (ConnectedComponents.mk (Sum.inl x)) ⊆
      Set.range (@Sum.inl X.Carrier Y.Carrier) := by
  intro z hz
  have hcomp : ConnectedComponents.mk z =
      ConnectedComponents.mk (Sum.inl x : X.Carrier ⊕ Y.Carrier) := by
    change z ∈ componentSet (sum X Y) (ConnectedComponents.mk (Sum.inl x))
    exact hz
  have hz1 : z ∈ connectedComponent (Sum.inl x : X.Carrier ⊕ Y.Carrier) :=
    ConnectedComponents.coe_eq_coe'.mp hcomp
  exact isPreconnected_connectedComponent.subset_isClopen
    (isClopen_range_inl (X := X.Carrier) (Y := Y.Carrier))
    ⟨Sum.inl x, mem_connectedComponent, ⟨x, rfl⟩⟩ hz1

private theorem sumInlRetract_inl (x : X.Carrier) (z : X.Carrier ⊕ Y.Carrier)
    (hz : z ∈ Set.range (@Sum.inl X.Carrier Y.Carrier)) :
    Sum.inl (sumInlRetract (X := X) (Y := Y) x z) = z := by
  obtain ⟨y, rfl⟩ := hz
  rfl

private theorem sumInlRetract_mem (x : X.Carrier)
    (p : ↥((sum X Y).componentOpen (ConnectedComponents.mk (Sum.inl x)))) :
    sumInlRetract (X := X) (Y := Y) x p.1 ∈ componentSet X (ConnectedComponents.mk x) := by
  have hp : ConnectedComponents.mk p.1 =
      ConnectedComponents.mk (Sum.inl x : X.Carrier ⊕ Y.Carrier) := by
    change p.1 ∈ componentSet (sum X Y) (ConnectedComponents.mk (Sum.inl x))
    exact p.2
  have h := congrArg (continuous_sumInlRetract (X := X) (Y := Y) x).connectedComponentsMap hp
  have h' : ConnectedComponents.mk (sumInlRetract (X := X) (Y := Y) x p.1) =
      ConnectedComponents.mk (sumInlRetract (X := X) (Y := Y) x (Sum.inl x)) := h
  have hx0 : sumInlRetract (X := X) (Y := Y) x (Sum.inl x) = x := rfl
  rwa [hx0] at h'

private theorem sumInlRetract_sum_inl_mem (x : X.Carrier)
    (q : ↥(X.componentOpen (ConnectedComponents.mk x))) :
    (Sum.inl (q : X.Carrier) : X.Carrier ⊕ Y.Carrier) ∈
      componentSet (sum X Y) (ConnectedComponents.mk (Sum.inl x)) := by
  have hq : ConnectedComponents.mk (q : X.Carrier) = ConnectedComponents.mk x := by
    change (q : X.Carrier) ∈ componentSet X (ConnectedComponents.mk x)
    exact q.2
  have h := congrArg (continuous_inl (X := X.Carrier) (Y := Y.Carrier)).connectedComponentsMap hq
  have h' : ConnectedComponents.mk (Sum.inl (q : X.Carrier) : X.Carrier ⊕ Y.Carrier) =
      ConnectedComponents.mk (Sum.inl x : X.Carrier ⊕ Y.Carrier) := h
  exact h'

private theorem contMDiff_sumInlRetract (x : X.Carrier) :
    ContMDiff 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ∞
      (fun p : ↥((sum X Y).componentOpen (ConnectedComponents.mk (Sum.inl x))) =>
        sumInlRetract (X := X) (Y := Y) x p.1) := by
  have hcomp : ContMDiff 𝓘(ℝ, EuclideanSpace ℝ (Fin n))
      𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ∞
      ((@Sum.inl X.Carrier Y.Carrier) ∘
        (fun p : ↥((sum X Y).componentOpen (ConnectedComponents.mk (Sum.inl x))) =>
          sumInlRetract (X := X) (Y := Y) x p.1)) := by
    have hfun : ((@Sum.inl X.Carrier Y.Carrier) ∘
        (fun p : ↥((sum X Y).componentOpen (ConnectedComponents.mk (Sum.inl x))) =>
          sumInlRetract (X := X) (Y := Y) x p.1)) =
        (Subtype.val : ↥((sum X Y).componentOpen (ConnectedComponents.mk (Sum.inl x))) →
          X.Carrier ⊕ Y.Carrier) :=
      funext fun p => sumInlRetract_inl x p.1 (componentSet_sum_subset_range_inl x p.2)
    rw [hfun]
    exact contMDiff_subtype_val
  exact contMDiff_of_contMDiff_inl hcomp

noncomputable def sumComponentInl (x : X.Carrier) :
    Diffeomorph 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) 𝓘(ℝ, EuclideanSpace ℝ (Fin n))
      ↥((sum X Y).componentOpen (ConnectedComponents.mk (Sum.inl x)))
      ↥(X.componentOpen (ConnectedComponents.mk x)) ∞ where
  toFun p := ⟨sumInlRetract (X := X) (Y := Y) x p.1, sumInlRetract_mem x p⟩
  invFun q := ⟨Sum.inl (q : X.Carrier), sumInlRetract_sum_inl_mem x q⟩
  left_inv p := Subtype.ext (sumInlRetract_inl x p.1 (componentSet_sum_subset_range_inl x p.2))
  right_inv q := Subtype.ext rfl
  contMDiff_toFun := by
    intro p
    refine codRestr_contMDiffAt (V := X.componentOpen (ConnectedComponents.mk x))
      (f := fun p : ↥((sum X Y).componentOpen (ConnectedComponents.mk (Sum.inl x))) =>
        sumInlRetract (X := X) (Y := Y) x p.1)
      (sumInlRetract_mem x) ((contMDiff_sumInlRetract x).contMDiffAt)
  contMDiff_invFun := by
    intro q
    refine codRestr_contMDiffAt
      (V := (sum X Y).componentOpen (ConnectedComponents.mk (Sum.inl x)))
      (f := fun q : ↥(X.componentOpen (ConnectedComponents.mk x)) =>
        (Sum.inl (q : X.Carrier) : X.Carrier ⊕ Y.Carrier))
      (sumInlRetract_sum_inl_mem x)
      (((ContMDiff.inl (I := 𝓘(ℝ, EuclideanSpace ℝ (Fin n)))
        (M := X.Carrier) (M' := Y.Carrier)).comp contMDiff_subtype_val).contMDiffAt)

set_option backward.isDefEq.respectTransparency false in
theorem sumComponentInl_mfderiv (x : X.Carrier)
    (p : ↥((sum X Y).componentOpen (ConnectedComponents.mk (Sum.inl x)))) :
    (mfderiv 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) 𝓘(ℝ, EuclideanSpace ℝ (Fin n))
      (sumComponentInl x) p : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n)) =
      ContinuousLinearMap.id ℝ (EuclideanSpace ℝ (Fin n)) := by
  let D : Diffeomorph 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) 𝓘(ℝ, EuclideanSpace ℝ (Fin n))
      ↥((sum X Y).componentOpen (ConnectedComponents.mk (Sum.inl x)))
      ↥(X.componentOpen (ConnectedComponents.mk x)) ∞ := sumComponentInl (Y := Y) x
  let F : ↥((sum X Y).componentOpen (ConnectedComponents.mk (Sum.inl x))) → X.Carrier :=
    (Subtype.val : ↥(X.componentOpen (ConnectedComponents.mk x)) → X.Carrier) ∘
      (D : ↥((sum X Y).componentOpen (ConnectedComponents.mk (Sum.inl x))) →
        ↥(X.componentOpen (ConnectedComponents.mk x)))
  have hD : MDifferentiableAt 𝓘(ℝ, EuclideanSpace ℝ (Fin n))
      𝓘(ℝ, EuclideanSpace ℝ (Fin n)) D p :=
    D.contMDiff.mdifferentiableAt (by simp)
  have hval : MDifferentiableAt 𝓘(ℝ, EuclideanSpace ℝ (Fin n))
      𝓘(ℝ, EuclideanSpace ℝ (Fin n))
      (Subtype.val : ↥(X.componentOpen (ConnectedComponents.mk x)) → X.Carrier) (D p) :=
    (hasMFDerivAt_subtype_val (X.componentOpen (ConnectedComponents.mk x)) (D p)).mdifferentiableAt
  have hF : MDifferentiableAt 𝓘(ℝ, EuclideanSpace ℝ (Fin n))
      𝓘(ℝ, EuclideanSpace ℝ (Fin n)) F p := by
    exact MDifferentiableAt.comp (x := p) (f := D)
      (g := (Subtype.val : ↥(X.componentOpen (ConnectedComponents.mk x)) → X.Carrier)) hval hD
  have hinl : MDifferentiableAt 𝓘(ℝ, EuclideanSpace ℝ (Fin n))
      𝓘(ℝ, EuclideanSpace ℝ (Fin n)) (@Sum.inl X.Carrier Y.Carrier) (F p) :=
    hasMFDerivAt_inl.mdifferentiableAt
  have hcomp1 := mfderiv_comp (x := p) (f := F) (g := (@Sum.inl X.Carrier Y.Carrier)) hinl hF
  have hcomp2 := mfderiv_comp (x := p) (f := D)
    (g := (Subtype.val : ↥(X.componentOpen (ConnectedComponents.mk x)) → X.Carrier)) hval hD
  have hfun : ((@Sum.inl X.Carrier Y.Carrier) ∘ F) =
      (Subtype.val : ↥((sum X Y).componentOpen (ConnectedComponents.mk (Sum.inl x))) →
        X.Carrier ⊕ Y.Carrier) :=
    funext fun q => sumInlRetract_inl x q.1 (componentSet_sum_subset_range_inl x q.2)
  rw [hfun, DifferentialGeometry.mfderiv_subtype_val] at hcomp1
  rw [DifferentialGeometry.mfderiv_subtype_val] at hcomp2
  have hcomp2' : (mfderiv 𝓘(ℝ, EuclideanSpace ℝ (Fin n))
      𝓘(ℝ, EuclideanSpace ℝ (Fin n)) F p :
      EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n)) =
      mfderiv 𝓘(ℝ, EuclideanSpace ℝ (Fin n))
        𝓘(ℝ, EuclideanSpace ℝ (Fin n)) D p := hcomp2
  rw [hcomp2'] at hcomp1
  rw [mfderiv_sumInl (p := (Sum.inl (F p) : X.Carrier ⊕ Y.Carrier))] at hcomp1
  exact hcomp1.symm


set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency false in
theorem sumComponentInl_preservesOrientation (x : X.Carrier) :
    (sumComponentInl (Y := Y) x).preservesOrientation
      ((sum X Y).component (ConnectedComponents.mk (Sum.inl x))).orientation
      (X.component (ConnectedComponents.mk x)).orientation := by
  intro p
  have he : (sumComponentInl (Y := Y) x).mfderivToContinuousLinearEquiv (by simp) p =
      ContinuousLinearEquiv.refl ℝ (EuclideanSpace ℝ (Fin n)) := by
    apply ContinuousLinearEquiv.ext
    funext v
    exact congrArg (fun A : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n) => A v)
      (sumComponentInl_mfderiv (X := X) (Y := Y) x p)
  rw [he]
  have hrefl : (ContinuousLinearEquiv.refl ℝ (EuclideanSpace ℝ (Fin n))).toLinearEquiv =
      LinearEquiv.refl ℝ (EuclideanSpace ℝ (Fin n)) := rfl
  rw [hrefl]
  have hmap := Orientation.map_refl (R := ℝ) (M := EuclideanSpace ℝ (Fin n)) (ι := Fin n)
  rw [hmap]
  change Equiv.refl (Orientation ℝ (EuclideanSpace ℝ (Fin n)) (Fin n))
      (ClosedOrientedManifold.componentTangentOrientation (sum X Y)
        (ConnectedComponents.mk (Sum.inl x)) p) =
    ClosedOrientedManifold.componentTangentOrientation X (ConnectedComponents.mk x)
      ((sumComponentInl (Y := Y) x) p)
  rw [ClosedOrientedManifold.componentTangentOrientation_apply,
    ClosedOrientedManifold.componentTangentOrientation_apply]
  rw [← sumInlRetract_inl x p.1 (componentSet_sum_subset_range_inl x p.2)]
  simp only [sum_orientation, ManifoldOrientation.sum_orientation_inl]
  rfl

noncomputable def sumComponentInl_orientedDiffeomorph (x : X.Carrier) :
    OrientedDiffeomorph
      ((sum X Y).component (ConnectedComponents.mk (Sum.inl x))).toClosedOrientedManifold
      (X.component (ConnectedComponents.mk x)).toClosedOrientedManifold :=
  ⟨sumComponentInl x, sumComponentInl_preservesOrientation x⟩

private noncomputable def sumInrRetract (y : Y.Carrier) :
    X.Carrier ⊕ Y.Carrier → Y.Carrier := Sum.elim (fun _ => y) id

private theorem continuous_sumInrRetract (y : Y.Carrier) :
    Continuous (sumInrRetract (X := X) (Y := Y) y) :=
  continuous_sum_dom.2 ⟨continuous_const, continuous_id⟩

private theorem componentSet_sum_subset_range_inr (y : Y.Carrier) :
    componentSet (sum X Y) (ConnectedComponents.mk (Sum.inr y)) ⊆
      Set.range (@Sum.inr X.Carrier Y.Carrier) := by
  intro z hz
  have hcomp : ConnectedComponents.mk z =
      ConnectedComponents.mk (Sum.inr y : X.Carrier ⊕ Y.Carrier) := by
    change z ∈ componentSet (sum X Y) (ConnectedComponents.mk (Sum.inr y))
    exact hz
  have hz1 : z ∈ connectedComponent (Sum.inr y : X.Carrier ⊕ Y.Carrier) :=
    ConnectedComponents.coe_eq_coe'.mp hcomp
  exact isPreconnected_connectedComponent.subset_isClopen
    (isClopen_range_inr (X := X.Carrier) (Y := Y.Carrier))
    ⟨Sum.inr y, mem_connectedComponent, ⟨y, rfl⟩⟩ hz1

private theorem sumInrRetract_inr (y : Y.Carrier) (z : X.Carrier ⊕ Y.Carrier)
    (hz : z ∈ Set.range (@Sum.inr X.Carrier Y.Carrier)) :
    Sum.inr (sumInrRetract (X := X) (Y := Y) y z) = z := by
  obtain ⟨w, rfl⟩ := hz
  rfl

private theorem sumInrRetract_mem (y : Y.Carrier)
    (p : ↥((sum X Y).componentOpen (ConnectedComponents.mk (Sum.inr y)))) :
    sumInrRetract (X := X) (Y := Y) y p.1 ∈ componentSet Y (ConnectedComponents.mk y) := by
  have hp : ConnectedComponents.mk p.1 =
      ConnectedComponents.mk (Sum.inr y : X.Carrier ⊕ Y.Carrier) := by
    change p.1 ∈ componentSet (sum X Y) (ConnectedComponents.mk (Sum.inr y))
    exact p.2
  have h := congrArg (continuous_sumInrRetract (X := X) (Y := Y) y).connectedComponentsMap hp
  have h' : ConnectedComponents.mk (sumInrRetract (X := X) (Y := Y) y p.1) =
      ConnectedComponents.mk (sumInrRetract (X := X) (Y := Y) y (Sum.inr y)) := h
  have hy0 : sumInrRetract (X := X) (Y := Y) y (Sum.inr y) = y := rfl
  rwa [hy0] at h'

private theorem sumInrRetract_sum_inr_mem (y : Y.Carrier)
    (q : ↥(Y.componentOpen (ConnectedComponents.mk y))) :
    (Sum.inr (q : Y.Carrier) : X.Carrier ⊕ Y.Carrier) ∈
      componentSet (sum X Y) (ConnectedComponents.mk (Sum.inr y)) := by
  have hq : ConnectedComponents.mk (q : Y.Carrier) = ConnectedComponents.mk y := by
    change (q : Y.Carrier) ∈ componentSet Y (ConnectedComponents.mk y)
    exact q.2
  have h := congrArg (continuous_inr (X := X.Carrier) (Y := Y.Carrier)).connectedComponentsMap hq
  have h' : ConnectedComponents.mk (Sum.inr (q : Y.Carrier) : X.Carrier ⊕ Y.Carrier) =
      ConnectedComponents.mk (Sum.inr y : X.Carrier ⊕ Y.Carrier) := h
  exact h'

private theorem contMDiff_sumInrRetract (y : Y.Carrier) :
    ContMDiff 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ∞
      (fun p : ↥((sum X Y).componentOpen (ConnectedComponents.mk (Sum.inr y))) =>
        sumInrRetract (X := X) (Y := Y) y p.1) := by
  have hcomp : ContMDiff 𝓘(ℝ, EuclideanSpace ℝ (Fin n))
      𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ∞
      ((@Sum.inr X.Carrier Y.Carrier) ∘
        (fun p : ↥((sum X Y).componentOpen (ConnectedComponents.mk (Sum.inr y))) =>
          sumInrRetract (X := X) (Y := Y) y p.1)) := by
    have hfun : ((@Sum.inr X.Carrier Y.Carrier) ∘
        (fun p : ↥((sum X Y).componentOpen (ConnectedComponents.mk (Sum.inr y))) =>
          sumInrRetract (X := X) (Y := Y) y p.1)) =
        (Subtype.val : ↥((sum X Y).componentOpen (ConnectedComponents.mk (Sum.inr y))) →
          X.Carrier ⊕ Y.Carrier) :=
      funext fun p => sumInrRetract_inr y p.1 (componentSet_sum_subset_range_inr y p.2)
    rw [hfun]
    exact contMDiff_subtype_val
  exact contMDiff_of_contMDiff_inr hcomp

noncomputable def sumComponentInr (y : Y.Carrier) :
    Diffeomorph 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) 𝓘(ℝ, EuclideanSpace ℝ (Fin n))
      ↥((sum X Y).componentOpen (ConnectedComponents.mk (Sum.inr y)))
      ↥(Y.componentOpen (ConnectedComponents.mk y)) ∞ where
  toFun p := ⟨sumInrRetract (X := X) (Y := Y) y p.1, sumInrRetract_mem y p⟩
  invFun q := ⟨Sum.inr (q : Y.Carrier), sumInrRetract_sum_inr_mem y q⟩
  left_inv p := Subtype.ext (sumInrRetract_inr y p.1 (componentSet_sum_subset_range_inr y p.2))
  right_inv q := Subtype.ext rfl
  contMDiff_toFun := by
    intro p
    refine codRestr_contMDiffAt (V := Y.componentOpen (ConnectedComponents.mk y))
      (f := fun p : ↥((sum X Y).componentOpen (ConnectedComponents.mk (Sum.inr y))) =>
        sumInrRetract (X := X) (Y := Y) y p.1)
      (sumInrRetract_mem y) ((contMDiff_sumInrRetract y).contMDiffAt)
  contMDiff_invFun := by
    intro q
    refine codRestr_contMDiffAt
      (V := (sum X Y).componentOpen (ConnectedComponents.mk (Sum.inr y)))
      (f := fun q : ↥(Y.componentOpen (ConnectedComponents.mk y)) =>
        (Sum.inr (q : Y.Carrier) : X.Carrier ⊕ Y.Carrier))
      (sumInrRetract_sum_inr_mem y)
      (((ContMDiff.inr (I := 𝓘(ℝ, EuclideanSpace ℝ (Fin n)))
        (M := X.Carrier) (M' := Y.Carrier)).comp contMDiff_subtype_val).contMDiffAt)

set_option backward.isDefEq.respectTransparency false in
theorem sumComponentInr_mfderiv (y : Y.Carrier)
    (p : ↥((sum X Y).componentOpen (ConnectedComponents.mk (Sum.inr y)))) :
    (mfderiv 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) 𝓘(ℝ, EuclideanSpace ℝ (Fin n))
      (sumComponentInr (X := X) (Y := Y) y) p :
        EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n)) =
      ContinuousLinearMap.id ℝ (EuclideanSpace ℝ (Fin n)) := by
  let D : Diffeomorph 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) 𝓘(ℝ, EuclideanSpace ℝ (Fin n))
      ↥((sum X Y).componentOpen (ConnectedComponents.mk (Sum.inr y)))
      ↥(Y.componentOpen (ConnectedComponents.mk y)) ∞ := sumComponentInr (X := X) y
  let F : ↥((sum X Y).componentOpen (ConnectedComponents.mk (Sum.inr y))) → Y.Carrier :=
    (Subtype.val : ↥(Y.componentOpen (ConnectedComponents.mk y)) → Y.Carrier) ∘
      (D : ↥((sum X Y).componentOpen (ConnectedComponents.mk (Sum.inr y))) →
        ↥(Y.componentOpen (ConnectedComponents.mk y)))
  have hD : MDifferentiableAt 𝓘(ℝ, EuclideanSpace ℝ (Fin n))
      𝓘(ℝ, EuclideanSpace ℝ (Fin n)) D p :=
    D.contMDiff.mdifferentiableAt (by simp)
  have hval : MDifferentiableAt 𝓘(ℝ, EuclideanSpace ℝ (Fin n))
      𝓘(ℝ, EuclideanSpace ℝ (Fin n))
      (Subtype.val : ↥(Y.componentOpen (ConnectedComponents.mk y)) → Y.Carrier) (D p) :=
    (hasMFDerivAt_subtype_val (Y.componentOpen (ConnectedComponents.mk y)) (D p)).mdifferentiableAt
  have hF : MDifferentiableAt 𝓘(ℝ, EuclideanSpace ℝ (Fin n))
      𝓘(ℝ, EuclideanSpace ℝ (Fin n)) F p :=
    MDifferentiableAt.comp (x := p) (f := D)
      (g := (Subtype.val : ↥(Y.componentOpen (ConnectedComponents.mk y)) → Y.Carrier)) hval hD
  have hinr : MDifferentiableAt 𝓘(ℝ, EuclideanSpace ℝ (Fin n))
      𝓘(ℝ, EuclideanSpace ℝ (Fin n)) (@Sum.inr X.Carrier Y.Carrier) (F p) :=
    hasMFDerivAt_inr.mdifferentiableAt
  have hcomp1 := mfderiv_comp (x := p) (f := F) (g := (@Sum.inr X.Carrier Y.Carrier)) hinr hF
  have hcomp2 := mfderiv_comp (x := p) (f := D)
    (g := (Subtype.val : ↥(Y.componentOpen (ConnectedComponents.mk y)) → Y.Carrier)) hval hD
  have hfun : ((@Sum.inr X.Carrier Y.Carrier) ∘ F) =
      (Subtype.val : ↥((sum X Y).componentOpen (ConnectedComponents.mk (Sum.inr y))) →
        X.Carrier ⊕ Y.Carrier) :=
    funext fun q => sumInrRetract_inr y q.1 (componentSet_sum_subset_range_inr y q.2)
  rw [hfun, DifferentialGeometry.mfderiv_subtype_val] at hcomp1
  rw [DifferentialGeometry.mfderiv_subtype_val] at hcomp2
  have hcomp2' : (mfderiv 𝓘(ℝ, EuclideanSpace ℝ (Fin n))
      𝓘(ℝ, EuclideanSpace ℝ (Fin n)) F p :
      EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n)) =
      mfderiv 𝓘(ℝ, EuclideanSpace ℝ (Fin n))
        𝓘(ℝ, EuclideanSpace ℝ (Fin n)) D p := hcomp2
  rw [hcomp2'] at hcomp1
  rw [mfderiv_sumInr] at hcomp1
  exact hcomp1.symm

set_option backward.isDefEq.respectTransparency false in
theorem sumComponentInr_preservesOrientation (y : Y.Carrier) :
    (sumComponentInr (X := X) (Y := Y) y).preservesOrientation
      ((sum X Y).component (ConnectedComponents.mk (Sum.inr y))).orientation
      (Y.component (ConnectedComponents.mk y)).orientation := by
  intro p
  have he : (sumComponentInr (X := X) (Y := Y) y).mfderivToContinuousLinearEquiv (by simp) p =
      ContinuousLinearEquiv.refl ℝ (EuclideanSpace ℝ (Fin n)) := by
    apply ContinuousLinearEquiv.ext
    funext v
    exact congrArg (fun A : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n) => A v)
      (sumComponentInr_mfderiv (X := X) (Y := Y) y p)
  rw [he]
  have hrefl : (ContinuousLinearEquiv.refl ℝ (EuclideanSpace ℝ (Fin n))).toLinearEquiv =
      LinearEquiv.refl ℝ (EuclideanSpace ℝ (Fin n)) := rfl
  rw [hrefl]
  have hmap := Orientation.map_refl (R := ℝ) (M := EuclideanSpace ℝ (Fin n)) (ι := Fin n)
  rw [hmap]
  change Equiv.refl (Orientation ℝ (EuclideanSpace ℝ (Fin n)) (Fin n))
      (ClosedOrientedManifold.componentTangentOrientation (sum X Y)
        (ConnectedComponents.mk (Sum.inr y)) p) =
    ClosedOrientedManifold.componentTangentOrientation Y (ConnectedComponents.mk y)
      ((sumComponentInr (X := X) (Y := Y) y) p)
  rw [ClosedOrientedManifold.componentTangentOrientation_apply,
    ClosedOrientedManifold.componentTangentOrientation_apply]
  rw [← sumInrRetract_inr y p.1 (componentSet_sum_subset_range_inr y p.2)]
  simp only [sum_orientation, ManifoldOrientation.sum_orientation_inr]
  rfl

noncomputable def sumComponentInr_orientedDiffeomorph (y : Y.Carrier) :
    OrientedDiffeomorph
      ((sum X Y).component (ConnectedComponents.mk (Sum.inr y))).toClosedOrientedManifold
      (Y.component (ConnectedComponents.mk y)).toClosedOrientedManifold :=
  ⟨sumComponentInr y, sumComponentInr_preservesOrientation y⟩

end ClosedOrientedManifold

namespace SphericalCutCapTransition

variable {M Q : ClosedOrientedManifold.{u} 3}

theorem presentation_preservesOrientation (E : SphericalCutCapTransition M Q) :
    E.presentation.preservesOrientation E.capped.orientation
      (ClosedOrientedManifold.sum Q E.discarded).orientation := by
  intro x
  rcases hx : E.presentation x with q | d
  · have h := E.presentation_positive x
    rw [hx] at h
    simpa only [ClosedOrientedManifold.sum_orientation,
      ManifoldOrientation.sum_orientation_inl] using h
  · have h := E.presentation_positive x
    rw [hx] at h
    simpa only [ClosedOrientedManifold.sum_orientation,
      ManifoldOrientation.sum_orientation_inr] using h

theorem cappedRetainedPresentationRealization (E : SphericalCutCapTransition M Q) :
    E.CappedRetainedPresentationRealization := by
  intro x q hx
  let e : ClosedOrientedManifold.OrientedDiffeomorph E.capped
      (ClosedOrientedManifold.sum Q E.discarded) :=
    ⟨E.presentation, presentation_preservesOrientation E⟩
  have hC : e.1.continuous.connectedComponentsMap
      (ConnectedComponents.mk (E.capping.coreInclusion x)) =
      ConnectedComponents.mk (Sum.inl q) := by
    change E.presentation.continuous.connectedComponentsMap
      (ConnectedComponents.mk (E.capping.coreInclusion x)) = ConnectedComponents.mk (Sum.inl q)
    rw [Continuous.connectedComponentsMap_mk, hx]
  refine ⟨(e.component (ConnectedComponents.mk (E.capping.coreInclusion x))).trans ?_⟩
  rw [hC]
  exact ClosedOrientedManifold.sumComponentInl_orientedDiffeomorph q

theorem cappedDiscardedPresentationRealization (E : SphericalCutCapTransition M Q) :
    E.CappedDiscardedPresentationRealization := by
  intro x d hx
  let e : ClosedOrientedManifold.OrientedDiffeomorph E.capped
      (ClosedOrientedManifold.sum Q E.discarded) :=
    ⟨E.presentation, presentation_preservesOrientation E⟩
  have hC : e.1.continuous.connectedComponentsMap
      (ConnectedComponents.mk (E.capping.coreInclusion x)) =
      ConnectedComponents.mk (Sum.inr d) := by
    change E.presentation.continuous.connectedComponentsMap
      (ConnectedComponents.mk (E.capping.coreInclusion x)) = ConnectedComponents.mk (Sum.inr d)
    rw [Continuous.connectedComponentsMap_mk, hx]
  refine ⟨(e.component (ConnectedComponents.mk (E.capping.coreInclusion x))).trans ?_⟩
  rw [hC]
  exact ClosedOrientedManifold.sumComponentInr_orientedDiffeomorph d

theorem cappedPresentationRealization (E : SphericalCutCapTransition M Q) :
    E.CappedPresentationRealization :=
  E.cappedPresentationRealization_of_retained_of_discarded
    (cappedRetainedPresentationRealization E) (cappedDiscardedPresentationRealization E)

theorem noTubeRealization_of_uncutCappingRealization (E : SphericalCutCapTransition M Q)
    (h : E.UncutCappingRealization) : E.NoTubeRealization :=
  E.noTubeRealization_of_uncutCappingRealization_of_cappedPresentationRealization h
    (cappedPresentationRealization E)

end SphericalCutCapTransition

end Topology

end DifferentialGeometry
