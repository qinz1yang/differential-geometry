import DifferentialGeometry.Tensor.RSTensor.Basis
import DifferentialGeometry.Tensor.RSTensor.NablaOnTensors.Connection.Smooth
import DifferentialGeometry.Bundle.TangentSpace
import Mathlib.Geometry.Manifold.VectorBundle.Hom

set_option autoImplicit false

noncomputable section

namespace DifferentialGeometry

attribute [local instance] Fintype.ofFinite Classical.propDecidable

open Bundle
open DifferentialGeometry.Tensor0SBundle
open scoped Manifold ContDiff Topology

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace Real E]
variable [FiniteDimensional Real E] [CompleteSpace E]
variable {H : Type*} [TopologicalSpace H]
variable {I : ModelWithCorners Real E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

theorem localFrame_coeff_apply_contMDiffAt
    {Idx : Type*} [Finite Idx] {u : Set M}
    {frame : Idx → (x : M) → TangentSpace I x}
    (hframe : IsLocalFrameOn I E ∞ frame u)
    {x : M} (hu : u ∈ nhds x)
    {σ : (x : M) → TangentSpace I x}
    (hσ : ContMDiffAt I (I.prod (modelWithCornersSelf ℝ E)) ∞ (T% σ) x)
    (i : Idx) :
    ContMDiffAt I (modelWithCornersSelf ℝ ℝ) ∞ (fun y ↦ hframe.coeff i y (σ y)) x := by
  classical
  let _ := Fintype.ofFinite Idx
  let e := trivializationAt E (TangentSpace I : M → Type _) x
  have he : x ∈ e.baseSet := mem_baseSet_trivializationAt E (TangentSpace I) x
  have hx : x ∈ u := mem_of_mem_nhds hu
  let b : Module.Basis Idx ℝ E :=
    (hframe.toBasisAt hx).map (e.linearEquivAt ℝ x he)
  let A : M → E →L[ℝ] E := fun y ↦
    b.constrL (fun j ↦ e.continuousLinearMapAt ℝ y (frame j y))
  have hframe_coord (j : Idx) :
      ContMDiffAt I (modelWithCornersSelf ℝ E) ∞
        (fun y ↦ e.continuousLinearMapAt ℝ y (frame j y)) x := by
    have hj : ContMDiffAt I (I.prod (modelWithCornersSelf ℝ E)) ∞
        (T% (frame j)) x := (hframe.contMDiffOn j).contMDiffAt hu
    refine ((e.contMDiffAt_section_iff he).mp hj).congr_of_eventuallyEq ?_
    filter_upwards [e.open_baseSet.mem_nhds he] with y hy
    exact Bundle.Trivialization.continuousLinearMapAt_apply_of_mem
      ℝ e hy (frame j y)
  have hA : ContMDiffAt I (modelWithCornersSelf ℝ (E →L[ℝ] E)) ∞ A x := by
    apply contMDiffAt_clm_of_pointwise (IB := I) (X := M)
    intro v
    have hv : v = ∑ j, b.repr v j • b j := (b.sum_repr v).symm
    have hsum : ContMDiffAt I (modelWithCornersSelf ℝ E) ∞
        (fun y ↦ ∑ j, b.repr v j •
          e.continuousLinearMapAt ℝ y (frame j y)) x := by
      apply ContMDiffAt.sum
      intro j _
      have hc : ContMDiffAt I (modelWithCornersSelf ℝ ℝ) ∞
          (fun _ : M ↦ b.repr v j) x := contMDiffAt_const
      exact hc.smul (hframe_coord j)
    refine hsum.congr_of_eventuallyEq (Filter.Eventually.of_forall fun y ↦ ?_)
    change A y v = _
    change b.constrL (fun j ↦ e.continuousLinearMapAt ℝ y (frame j y)) v = _
    rw [hv, map_sum]
    simp
  have hA_x : A x = ContinuousLinearMap.id ℝ E := by
    apply ContinuousLinearMap.ext
    intro v
    rw [← b.sum_repr v, map_sum]
    simp only [A, map_smul, Module.Basis.constrL_basis,
      ContinuousLinearMap.id_apply]
    apply Finset.sum_congr rfl
    intro j _
    congr 1
    rw [Bundle.Trivialization.continuousLinearMapAt_apply_of_mem ℝ e he]
    simp [b, IsLocalFrameOn.toBasisAt_coe]
  have hA_inv : (A x).IsInvertible := by
    rw [hA_x]
    simpa using
      (ContinuousLinearMap.isInvertible_equiv
        (f := ContinuousLinearEquiv.refl ℝ E))
  have hAinv : ContMDiffAt I (modelWithCornersSelf ℝ (E →L[ℝ] E)) ∞
      (ContinuousLinearMap.inverse ∘ A) x :=
    (hA_inv.contDiffAt_map_inverse (n := ∞)).contMDiffAt.comp x hA
  have hσcoord : ContMDiffAt I (modelWithCornersSelf ℝ E) ∞
      (fun y ↦ e.continuousLinearMapAt ℝ y (σ y)) x := by
    refine ((e.contMDiffAt_section_iff he).mp hσ).congr_of_eventuallyEq ?_
    filter_upwards [e.open_baseSet.mem_nhds he] with y hy
    exact Bundle.Trivialization.continuousLinearMapAt_apply_of_mem ℝ e hy (σ y)
  have hinv_apply : ContMDiffAt I (modelWithCornersSelf ℝ E) ∞
      (fun y ↦ ContinuousLinearMap.inverse (A y)
        (e.continuousLinearMapAt ℝ y (σ y))) x :=
    hAinv.clm_apply hσcoord
  have hcoord : ContMDiffAt I (modelWithCornersSelf ℝ ℝ) ∞
      (fun y ↦ b.coord i (ContinuousLinearMap.inverse (A y)
        (e.continuousLinearMapAt ℝ y (σ y)))) x :=
    b.coord i |>.toContinuousLinearMap.contDiff.contMDiff.contMDiffAt.comp x hinv_apply
  refine hcoord.congr_of_eventuallyEq ?_
  filter_upwards [hu, e.open_baseSet.mem_nhds he] with y hyu hye
  let by' : Module.Basis Idx ℝ E :=
    (hframe.toBasisAt hyu).map (e.linearEquivAt ℝ y hye)
  have hA_basis (j : Idx) : A y (b j) = by' j := by
    simp only [A, Module.Basis.constrL_basis]
    rw [Bundle.Trivialization.continuousLinearMapAt_apply_of_mem ℝ e hye]
    simp [by', IsLocalFrameOn.toBasisAt_coe]
  have hA_eq : A y = (b.equivFunL.trans by'.equivFunL.symm : E →L[ℝ] E) := by
    have htrans_basis (j : Idx) :
        (b.equivFunL.trans by'.equivFunL.symm) (b j) = by' j := by
      change by'.equivFunL.symm (b.equivFunL (b j)) = by' j
      apply by'.equivFunL.injective
      rw [by'.equivFunL.apply_symm_apply]
      ext k
      simp [Module.Basis.equivFunL_apply]
    apply ContinuousLinearMap.ext
    intro v
    rw [← b.sum_repr v, map_sum, map_sum]
    exact Finset.sum_congr rfl fun j _ ↦ by
      rw [map_smul, map_smul, hA_basis]
      change (b.repr v) j • by' j =
        (b.repr v) j • (b.equivFunL.trans by'.equivFunL.symm) (b j)
      rw [htrans_basis]
  have hAinv_eq : ContinuousLinearMap.inverse (A y) =
      (by'.equivFunL.trans b.equivFunL.symm : E →L[ℝ] E) := by
    rw [hA_eq]
    rw [ContinuousLinearMap.inverse_equiv]
    rfl
  rw [hAinv_eq]
  have hσcoord_eq : e.continuousLinearMapAt ℝ y (σ y) =
      (e.linearEquivAt ℝ y hye) (σ y) := by
    rw [Bundle.Trivialization.continuousLinearMapAt_apply_of_mem ℝ e hye]
    rfl
  rw [hσcoord_eq]
  have hcoord_transfer :
      b.coord i ((by'.equivFunL.trans b.equivFunL.symm)
        ((e.linearEquivAt ℝ y hye) (σ y))) =
        by'.coord i ((e.linearEquivAt ℝ y hye) (σ y)) := by
    simp only [ContinuousLinearEquiv.trans_apply]
    exact congrFun
      (b.equivFunL.apply_symm_apply
        (by'.repr ((e.linearEquivAt ℝ y hye) (σ y)))) i
  have hcoeff_eq : hframe.coeff i y (σ y) =
      by'.coord i ((e.linearEquivAt ℝ y hye) (σ y)) := by
    rw [hframe.coeff_apply_of_mem hyu]
    simp only [Module.Basis.coord_apply]
    change ((hframe.toBasisAt hyu).repr (σ y)) i =
      (((hframe.toBasisAt hyu).map (e.linearEquivAt ℝ y hye)).repr
        ((e.linearEquivAt ℝ y hye) (σ y))) i
    rw [Module.Basis.map_repr]
    change ((hframe.toBasisAt hyu).repr (σ y)) i =
      ((hframe.toBasisAt hyu).repr
        ((e.linearEquivAt ℝ y hye).symm
          ((e.linearEquivAt ℝ y hye) (σ y)))) i
    rw [(e.linearEquivAt ℝ y hye).symm_apply_apply]
  exact hcoeff_eq.trans hcoord_transfer.symm

theorem localFrame_coeff_apply_contMDiffOn
    {Idx : Type*} [Finite Idx] {u : Set M}
    {frame : Idx → (x : M) → TangentSpace I x}
    (hframe : IsLocalFrameOn I E ∞ frame u)
    (hu : IsOpen u)
    {σ : (x : M) → TangentSpace I x}
    (hσ : ContMDiffOn I (I.prod (modelWithCornersSelf ℝ E)) ∞ (T% σ) u)
    (i : Idx) :
    ContMDiffOn I (modelWithCornersSelf ℝ ℝ) ∞ (fun x ↦ hframe.coeff i x (σ x)) u := by
  intro x hx
  exact (localFrame_coeff_apply_contMDiffAt hframe (hu.mem_nhds hx)
    ((hσ x hx).contMDiffAt (hu.mem_nhds hx)) i).contMDiffWithinAt

omit [CompleteSpace E] in
theorem localFrame_dual_contMDiffOn
    {Idx : Type*} [Finite Idx] {u : Set M}
    {frame : Idx → (x : M) → TangentSpace I x}
    (hframe : IsLocalFrameOn I E ∞ frame u)
    (hu : IsOpen u) (i : Idx) :
    ContMDiffOn I (I.prod (modelWithCornersSelf ℝ (E →L[ℝ] ℝ))) ∞
      (fun x ↦ TotalSpace.mk' (E →L[ℝ] ℝ)
        (E := fun x : M ↦ TangentSpace I x →L[ℝ] ℝ)
        x (hframe.coeff i x).toContinuousLinearMap) u := by
  intro x hx
  apply ContMDiffAt.contMDiffWithinAt
  rw [contMDiffAt_hom_bundle]
  refine ⟨contMDiffAt_id, ?_⟩
  apply contMDiffAt_clm_of_pointwise (IB := I) (X := M)
  intro v
  let e₁ := trivializationAt E (TangentSpace I : M → Type _) x
  let e₂ := trivializationAt ℝ (Bundle.Trivial M ℝ) x
  have he₁ : x ∈ e₁.baseSet := mem_baseSet_trivializationAt E (TangentSpace I) x
  let Y : (y : M) → TangentSpace I y := fun y ↦ e₁.symmL ℝ y v
  have hY : ContMDiffAt I (I.prod (modelWithCornersSelf ℝ E)) ∞ (T% Y) x := by
    refine (e₁.contMDiffAt_section_iff he₁).mpr ?_
    have hconst : ContMDiffAt I (modelWithCornersSelf ℝ E) ∞ (fun _ : M ↦ v) x :=
      contMDiffAt_const
    refine hconst.congr_of_eventuallyEq ?_
    filter_upwards [e₁.open_baseSet.mem_nhds he₁] with y hy
    simp [Y, Bundle.Trivialization.symmL_apply, hy, e₁.apply_mk_symm]
  have hscalar := localFrame_coeff_apply_contMDiffAt hframe (hu.mem_nhds hx) hY i
  refine hscalar.congr_of_eventuallyEq ?_
  have he₂ : x ∈ e₂.baseSet := mem_baseSet_trivializationAt ℝ (Bundle.Trivial M ℝ) x
  filter_upwards [e₁.open_baseSet.mem_nhds he₁,
    e₂.open_baseSet.mem_nhds he₂] with y hy₁ hy₂
  change ContinuousLinearMap.inCoordinates E (TangentSpace I) ℝ
      (Bundle.Trivial M ℝ) x y x y
        (hframe.coeff i y).toContinuousLinearMap v = hframe.coeff i y (Y y)
  rw [show ContinuousLinearMap.inCoordinates E (TangentSpace I) ℝ
      (Bundle.Trivial M ℝ) x y x y
        (hframe.coeff i y).toContinuousLinearMap v =
      e₂.continuousLinearMapAt ℝ y
        (hframe.coeff i y (e₁.symmL ℝ y v)) from rfl]
  rw [Bundle.Trivialization.continuousLinearMapAt_apply_of_mem ℝ e₂ hy₂]
  rfl

omit [CompleteSpace E] in
theorem exists_smooth_localFrameOn (x : M) :
    ∃ (u : Set M)
      (frame : Fin (Module.finrank ℝ E) → (y : M) → TangentSpace I y),
      IsOpen u ∧ x ∈ u ∧ IsLocalFrameOn I E ∞ frame u := by
  let e := trivializationAt E (TangentSpace I : M → Type _) x
  let b := Module.finBasis ℝ E
  exact ⟨e.baseSet, e.localFrame b, e.open_baseSet,
    mem_baseSet_trivializationAt E (TangentSpace I) x,
    e.isLocalFrameOn_localFrame_baseSet I ∞ b⟩

omit [FiniteDimensional ℝ E] [CompleteSpace E] in
theorem localFrame_coeff_apply_frame
    {Idx : Type*} [DecidableEq Idx] {u : Set M} {n : WithTop ℕ∞}
    {frame : Idx → (x : M) → TangentSpace I x}
    (hframe : IsLocalFrameOn I E n frame u)
    {x : M} (hx : x ∈ u) (i j : Idx) :
    hframe.coeff i x (frame j x) = if j = i then 1 else 0 := by
  classical
  rw [hframe.coeff_apply_of_mem hx]
  rw [← hframe.toBasisAt_coe hx j]
  rw [(hframe.toBasisAt hx).repr_self]
  simp [Finsupp.single_apply]

omit [FiniteDimensional ℝ E] [CompleteSpace E] in
theorem covariantDerivative_finset_sum_tangent
    {ι : Type*} (cov : CovariantDerivative I E (TangentSpace I : M → Type _))
    (t : Finset ι) (σ : ι → (x : M) → TangentSpace I x)
    {x : M} (v : TangentSpace I x)
    (hσ : ∀ i, MDiffAt (T% (σ i)) x) :
    (cov (t.sum σ) x) v = t.sum (fun i => (cov (σ i) x) v) := by
  classical
  induction t using Finset.induction_on with
  | empty =>
      simp [cov.isCovariantDerivativeOnUniv.zero]
  | insert i t hit ih =>
      have hσi : MDiffAt (T% (σ i)) x := hσ i
      have hsum : MDiffAt (T% (t.sum σ)) x := by
        have hsum_raw := MDifferentiableAt.sum_section (s := t) (t := σ)
          (fun i _ => hσ i)
        simpa using hsum_raw
      calc
        (cov ((insert i t).sum σ) x) v
            = (cov (σ i + t.sum σ) x) v := by
              simp [Finset.sum_insert, hit]
        _ = ((cov (σ i) x + cov (t.sum σ) x) v) := by
              rw [cov.isCovariantDerivativeOnUniv.add hσi hsum]
        _ = (cov (σ i) x) v + (cov (t.sum σ) x) v := by
              simp
        _ = (insert i t).sum (fun j => (cov (σ j) x) v) := by
              rw [ih]
              simp [Finset.sum_insert, hit]

omit [CompleteSpace E] in
theorem covariantDerivative_localFrame_coeff_eq
    {ι : Type*} [Finite ι]
    (cov : CovariantDerivative I E (TangentSpace I : M → Type _))
    (e : Trivialization E (TotalSpace.proj : TotalSpace E (TangentSpace I : M → Type _) → M))
    [MemTrivializationAtlas e] (b : Module.Basis ι Real E)
    {σ : (x : M) → TangentSpace I x} {x : M}
    (hx : x ∈ e.baseSet) (hσ : MDiffAt (T% σ) x) (i k : ι) :
    e.localFrameCoeff I b k x
        ((cov σ x) (e.localFrame b i x)) =
      mvfderiv (I := I) ((LinearMap.piApply (e.localFrameCoeff I b k)) σ)
        x (e.localFrame b i x) +
        ∑ j : ι,
          e.localFrameCoeff I b j x (σ x) *
            e.localFrameCoeff I b k x
              ((cov (e.localFrame b j) x) (e.localFrame b i x)) := by
  classical
  let frame : ι → (x : M) → TangentSpace I x := fun j => e.localFrame b j
  let coeff : ι → M → Real := fun j y => e.localFrameCoeff I b j y (σ y)
  let term : ι → (x : M) → TangentSpace I x := fun j => coeff j • frame j
  have hframe_diff (j : ι) : MDiffAt (T% (fun y => frame j y)) x := by
    simpa [frame] using
      ((e.isLocalFrameOn_localFrame_baseSet I ∞ b).contMDiffAt
        e.open_baseSet hx j).mdifferentiableAt (by simp)
  have hcoeff_diff (j : ι) :
      MDifferentiableAt I 𝓘(Real, Real) (coeff j) x := by
    simpa [coeff] using
      mdifferentiableAt_localFrameCoeff
        (I := I) (e := e) (b := b) hx hσ j
  have hterm_diff (j : ι) : MDiffAt (T% (fun y => term j y)) x := by
    exact (hcoeff_diff j).smul_section (hframe_diff j)
  have hsum_diff :
      MDiffAt (T% ((Finset.univ : Finset ι).sum term)) x := by
    simpa using
      MDifferentiableAt.sum_section
        (s := (Finset.univ : Finset ι)) (t := term) (fun j _ => hterm_diff j)
  have hσ_ev :
      σ =ᶠ[𝓝 x] fun y : M => ∑ j : ι, term j y := by
    filter_upwards [e.open_baseSet.mem_nhds hx] with y hy
    change σ y = ∑ j : ι,
      e.localFrameCoeff I b j y (σ y) • e.localFrame b j y
    exact e.eq_sum_localFrameCoeff_smul (I := I) (b := b) (s := σ) hy
  have hcov_congr :
      cov σ x = cov ((Finset.univ : Finset ι).sum term) x :=
    cov.isCovariantDerivativeOnUniv.congr_of_eventuallyEq hσ hsum_diff
      (by simp) (by
        filter_upwards [hσ_ev] with y hy
        apply (tangentSpaceModelContinuousLinearEquiv (I := I) y).injective
        simpa only [Finset.sum_apply, map_sum,
          tangentSpaceModelContinuousLinearEquiv_apply] using hy)
  have hcov_sum :
      (cov σ x) (frame i x) =
        ∑ j : ι,
          (mvfderiv (I := I) (coeff j) x (frame i x) • frame j x +
            coeff j x • (cov (frame j) x) (frame i x)) := by
    calc
      (cov σ x) (frame i x)
          = (cov ((Finset.univ : Finset ι).sum term) x) (frame i x) := by
            rw [hcov_congr]
      _ = ∑ j : ι, (cov (term j) x) (frame i x) := by
            rw [covariantDerivative_finset_sum_tangent (I := I) cov
              (Finset.univ : Finset ι) term (frame i x) hterm_diff]
      _ = ∑ j : ι,
          (mvfderiv (I := I) (coeff j) x (frame i x) • frame j x +
            coeff j x • (cov (frame j) x) (frame i x)) := by
            refine Finset.sum_congr rfl fun j _ => ?_
            have hleib := congr($(cov.isCovariantDerivativeOnUniv.leibniz
              (σ := frame j) (g := coeff j) (x := x)
              (hframe_diff j) (hcoeff_diff j)) (frame i x))
            simpa [term, coeff, frame, add_comm] using hleib
  have hcoeff_frame (j l : ι) :
      e.localFrameCoeff I b l x (frame j x) = (if j = l then 1 else 0) := by
    rw [e.localFrameCoeff_apply_of_mem_baseSet b hx]
    change ((e.basisAt b hx).repr (e.localFrame b j x)) l = (if j = l then 1 else 0)
    rw [e.localFrame_apply_of_mem_baseSet (b := b) hx]
    rw [(e.basisAt b hx).repr_self]
    simp [Finsupp.single_apply]
  rw [hcov_sum]
  rw [map_sum]
  simp only [map_add]
  rw [Finset.sum_add_distrib]
  have hderiv_sum :
      (∑ j : ι,
          e.localFrameCoeff I b k x
            (mvfderiv (I := I) (coeff j) x (frame i x) • frame j x)) =
        mvfderiv (I := I) (coeff k) x (frame i x) := by
    calc
      (∑ j : ι,
          e.localFrameCoeff I b k x
            (mvfderiv (I := I) (coeff j) x (frame i x) • frame j x))
          = ∑ j : ι,
              mvfderiv (I := I) (coeff j) x (frame i x) *
                e.localFrameCoeff I b k x (frame j x) := by
              refine Finset.sum_congr rfl fun j _ => ?_
              simp
      _ = ∑ j : ι,
            mvfderiv (I := I) (coeff j) x (frame i x) *
              (if j = k then 1 else 0) := by
              refine Finset.sum_congr rfl fun j _ => ?_
              rw [hcoeff_frame j k]
      _ = mvfderiv (I := I) (coeff k) x (frame i x) := by
              simp
  have hchristoffel_sum :
      (∑ j : ι,
          e.localFrameCoeff I b k x
            (coeff j x • (cov (frame j) x) (frame i x))) =
        ∑ j : ι,
          coeff j x *
            e.localFrameCoeff I b k x ((cov (frame j) x) (frame i x)) := by
    refine Finset.sum_congr rfl fun j _ => ?_
    simp
  rw [hderiv_sum, hchristoffel_sum]
  rfl

omit [CompleteSpace E] in
theorem covariantDerivative_localFrame_coeff_eq_along
    {ι : Type*} [Finite ι]
    (cov : CovariantDerivative I E (TangentSpace I : M → Type _))
    (e : Trivialization E (TotalSpace.proj : TotalSpace E (TangentSpace I : M → Type _) → M))
    [MemTrivializationAtlas e] (b : Module.Basis ι Real E)
    {σ : (x : M) → TangentSpace I x} {x : M}
    (hx : x ∈ e.baseSet) (hσ : MDiffAt (T% σ) x)
    (v : TangentSpace I x) (k : ι) :
    e.localFrameCoeff I b k x ((cov σ x) v) =
      mvfderiv (I := I) ((LinearMap.piApply (e.localFrameCoeff I b k)) σ) x v +
        ∑ j : ι,
          e.localFrameCoeff I b j x (σ x) *
            e.localFrameCoeff I b k x
              ((cov (e.localFrame b j) x) v) := by
  classical
  let f : M → Real := (LinearMap.piApply (e.localFrameCoeff I b k)) σ
  let lhs : TangentSpace I x →ₗ[Real] Real :=
    (e.localFrameCoeff I b k x).comp (cov σ x).toLinearMap
  let rhs : TangentSpace I x →ₗ[Real] Real :=
    (mvfderiv (I := I) f x).toLinearMap +
      ∑ j : ι,
        e.localFrameCoeff I b j x (σ x) •
          ((e.localFrameCoeff I b k x).comp (cov (e.localFrame b j) x).toLinearMap)
  have hlin : lhs = rhs := by
    apply (e.basisAt b hx).ext
    intro i
    have hframe : e.basisAt b hx i = e.localFrame b i x := by
      exact (e.localFrame_apply_of_mem_baseSet (b := b) (i := i) hx).symm
    have hbase :=
      covariantDerivative_localFrame_coeff_eq (I := I) cov e b hx hσ i k
    simpa [lhs, rhs, f, hframe, Finset.sum_apply] using hbase
  have happly := congrArg (fun L : TangentSpace I x →ₗ[Real] Real => L v) hlin
  simpa [lhs, rhs, f, Finset.sum_apply] using happly

noncomputable def homModelCoeff
    {ι : Type*} (b : Module.Basis ι Real E) (i k : ι) :
    (E →L[Real] E) →ₗ[Real] Real where
  toFun A := b.coord k (A (b i))
  map_add' A B := by simp
  map_smul' c A := by simp

noncomputable def localHomCoeff
    {ι : Type*}
    (e : Trivialization E (TotalSpace.proj : TotalSpace E (TangentSpace I : M → Type _) → M))
    [MemTrivializationAtlas e] (b : Module.Basis ι Real E) (i k : ι) (x : M) :
    (TangentSpace I x →L[Real] TangentSpace I x) →ₗ[Real] Real :=
  (homModelCoeff (E := E) b i k).comp
    ((e.continuousLinearMap (RingHom.id Real) e).linearMapAt Real x)

omit [FiniteDimensional ℝ E] [CompleteSpace E] in
theorem localHomCoeff_apply
    {ι : Type*}
    (e : Trivialization E (TotalSpace.proj : TotalSpace E (TangentSpace I : M → Type _) → M))
    [MemTrivializationAtlas e] (b : Module.Basis ι Real E)
    {x : M} (hx : x ∈ e.baseSet)
    (A : TangentSpace I x →L[Real] TangentSpace I x) (i k : ι) :
    localHomCoeff (I := I) e b i k x A =
      e.localFrameCoeff I b k x (A (e.localFrame b i x)) := by
  rw [e.localFrame_apply_of_mem_baseSet (b := b) hx]
  have hbasis :
      e.basisAt b hx =
        (e.isLocalFrameOn_localFrame_baseSet I 1 b).toBasisAt hx := by
    ext j
    simp [IsLocalFrameOn.toBasisAt, Bundle.Trivialization.localFrame,
      Bundle.Trivialization.basisAt, hx]
  have hhom : x ∈ (e.continuousLinearMap (RingHom.id Real) e).baseSet := by
    simp [hx]
  simp only [localHomCoeff, homModelCoeff, LinearMap.coe_comp, Function.comp_apply]
  simp only [Bundle.Trivialization.localFrameCoeff, IsLocalFrameOn.coeff, hx, ↓reduceDIte]
  rw [← hbasis]
  rw [((e.continuousLinearMap (RingHom.id Real) e).coe_linearMapAt_of_mem hhom)]
  change
    b.coord k (((e.continuousLinearMap (RingHom.id Real) e) ⟨x, A⟩).2 (b i)) =
      (e.basisAt b hx).coord k (A ((e.basisAt b hx) i))
  rw [Bundle.Trivialization.continuousLinearMap_apply]
  change b.coord k
      (e.continuousLinearMapAt Real x (A (e.symmL Real x (b i)))) =
    (e.basisAt b hx).coord k (A ((e.basisAt b hx) i))
  rw [e.symmL_apply hx (b i)]
  simp [Bundle.Trivialization.basisAt, Bundle.Trivialization.continuousLinearMapAt_apply,
    e.coe_linearMapAt_of_mem hx]

omit [CompleteSpace E] in
theorem homLocalFrameCoeff_eq_localHomCoeff
    {ι : Type*} [Finite ι]
    (e : Trivialization E (TotalSpace.proj : TotalSpace E (TangentSpace I : M → Type _) → M))
    [MemTrivializationAtlas e] (b : Module.Basis ι Real E)
    {x : M} (hx : x ∈ e.baseSet)
    (A : TangentSpace I x →L[Real] TangentSpace I x) (i k : ι) :
    (e.continuousLinearMap (RingHom.id Real) e).localFrameCoeff I
        (continuousLinearMapHomBasis (𝕜 := Real) b b) (k, i) x A =
      localHomCoeff (I := I) e b i k x A := by
  let eHom := e.continuousLinearMap (RingHom.id Real) e
  let bHom := continuousLinearMapHomBasis (𝕜 := Real) b b
  have hhom : x ∈ eHom.baseSet := by
    simp [eHom, hx]
  classical
  let s : (y : M) → TangentSpace I y →L[Real] TangentSpace I y :=
    fun y => if h : x = y then h ▸ A else 0
  have hsx : s x = A := by
    simp [s]
  rw [← hsx]
  rw [eHom.localFrameCoeff_apply_of_mem_baseSet bHom hhom s (k, i)]
  simp only [eHom, bHom, hsx]
  simp [Bundle.Trivialization.basisAt, localHomCoeff, homModelCoeff,
    continuousLinearMap_homBasis_repr]
  simp only [((e.continuousLinearMap (RingHom.id Real) e).coe_linearMapAt_of_mem hhom)]

omit [CompleteSpace E] in
theorem covariantDerivative_localHomCoeff_eq
    {ι : Type*} [Finite ι]
    (cov : CovariantDerivative I E (TangentSpace I : M → Type _))
    (e : Trivialization E (TotalSpace.proj : TotalSpace E (TangentSpace I : M → Type _) → M))
    [MemTrivializationAtlas e] (b : Module.Basis ι Real E)
    {σ : (x : M) → TangentSpace I x} {x : M}
    (hx : x ∈ e.baseSet) (hσ : MDiffAt (T% σ) x) (i k : ι) :
    localHomCoeff (I := I) e b i k x (cov σ x) =
      mvfderiv (I := I) ((LinearMap.piApply (e.localFrameCoeff I b k)) σ)
        x (e.localFrame b i x) +
        ∑ j : ι,
          e.localFrameCoeff I b j x (σ x) *
            e.localFrameCoeff I b k x
              ((cov (e.localFrame b j) x) (e.localFrame b i x)) := by
  rw [localHomCoeff_apply (I := I) e b hx (cov σ x) i k]
  exact covariantDerivative_localFrame_coeff_eq (I := I) cov e b hx hσ i k

omit [CompleteSpace E] in
theorem covariantDerivative_localHomCoeff_eventuallyEq
    {ι : Type*} [Finite ι]
    (cov : CovariantDerivative I E (TangentSpace I : M → Type _))
    (e : Trivialization E (TotalSpace.proj : TotalSpace E (TangentSpace I : M → Type _) → M))
    [MemTrivializationAtlas e] (b : Module.Basis ι Real E)
    {σ : (x : M) → TangentSpace I x} {x : M}
    (hx : x ∈ e.baseSet) (hσ : ∀ᶠ y in 𝓝 x, MDiffAt (T% σ) y) (i k : ι) :
    (fun y : M => localHomCoeff (I := I) e b i k y (cov σ y)) =ᶠ[𝓝 x]
      fun y : M =>
        mvfderiv (I := I) ((LinearMap.piApply (e.localFrameCoeff I b k)) σ)
          y (e.localFrame b i y) +
          ∑ j : ι,
            e.localFrameCoeff I b j y (σ y) *
              e.localFrameCoeff I b k y
                ((cov (e.localFrame b j) y) (e.localFrame b i y)) := by
  filter_upwards [e.open_baseSet.mem_nhds hx, hσ] with y hy hσy
  exact covariantDerivative_localHomCoeff_eq (I := I) cov e b hy hσy i k

omit [CompleteSpace E] in
theorem covariantDerivative_localHomCoeff_contMDiffAt
    {ι : Type*} [Finite ι]
    (cov : CovariantDerivative I E (TangentSpace I : M → Type _))
    (e : Trivialization E (TotalSpace.proj : TotalSpace E (TangentSpace I : M → Type _) → M))
    [MemTrivializationAtlas e] (b : Module.Basis ι Real E)
    {σ : (x : M) → TangentSpace I x} {x : M}
    (hx : x ∈ e.baseSet) (hσ : ∀ᶠ y in 𝓝 x, MDiffAt (T% σ) y)
    (i k : ι)
    (hderiv : ContMDiffAt I 𝓘(Real, Real) ∞
      (fun y : M =>
        mvfderiv (I := I) ((LinearMap.piApply (e.localFrameCoeff I b k)) σ)
          y (e.localFrame b i y)) x)
    (hcoeff : ∀ j : ι, ContMDiffAt I 𝓘(Real, Real) ∞
      (fun y : M => e.localFrameCoeff I b j y (σ y)) x)
    (hchristoffel : ∀ j : ι, ContMDiffAt I 𝓘(Real, Real) ∞
      (fun y : M =>
        e.localFrameCoeff I b k y
          ((cov (e.localFrame b j) y) (e.localFrame b i y))) x) :
    ContMDiffAt I 𝓘(Real, Real) ∞
      (fun y : M => localHomCoeff (I := I) e b i k y (cov σ y)) x := by
  have hEq :=
    covariantDerivative_localHomCoeff_eventuallyEq (I := I) cov e b hx hσ i k
  have hRhs : ContMDiffAt I 𝓘(Real, Real) ∞
      (fun y : M =>
        mvfderiv (I := I) ((LinearMap.piApply (e.localFrameCoeff I b k)) σ)
          y (e.localFrame b i y) +
          ∑ j : ι,
            e.localFrameCoeff I b j y (σ y) *
              e.localFrameCoeff I b k y
                ((cov (e.localFrame b j) y) (e.localFrame b i y))) x := by
    refine hderiv.add ?_
    exact ContMDiffAt.sum fun j _ => (hcoeff j).mul (hchristoffel j)
  exact hRhs.congr_of_eventuallyEq hEq

omit [CompleteSpace E] in
theorem covariantDerivative_localHomCoeff_contMDiffAt_one
    {ι : Type*} [Finite ι]
    (cov : CovariantDerivative I E (TangentSpace I : M → Type _))
    (e : Trivialization E (TotalSpace.proj : TotalSpace E (TangentSpace I : M → Type _) → M))
    [MemTrivializationAtlas e] (b : Module.Basis ι Real E)
    {σ : (x : M) → TangentSpace I x} {x : M}
    (hx : x ∈ e.baseSet) (hσ : ∀ᶠ y in 𝓝 x, MDiffAt (T% σ) y)
    (i k : ι)
    (hderiv : ContMDiffAt I 𝓘(Real, Real) (1 : WithTop ℕ∞)
      (fun y : M =>
        mvfderiv (I := I) ((LinearMap.piApply (e.localFrameCoeff I b k)) σ)
          y (e.localFrame b i y)) x)
    (hcoeff : ∀ j : ι, ContMDiffAt I 𝓘(Real, Real) (1 : WithTop ℕ∞)
      (fun y : M => e.localFrameCoeff I b j y (σ y)) x)
    (hchristoffel : ∀ j : ι, ContMDiffAt I 𝓘(Real, Real) (1 : WithTop ℕ∞)
      (fun y : M =>
        e.localFrameCoeff I b k y
          ((cov (e.localFrame b j) y) (e.localFrame b i y))) x) :
    ContMDiffAt I 𝓘(Real, Real) (1 : WithTop ℕ∞)
      (fun y : M => localHomCoeff (I := I) e b i k y (cov σ y)) x := by
  have hEq :=
    covariantDerivative_localHomCoeff_eventuallyEq (I := I) cov e b hx hσ i k
  have hRhs : ContMDiffAt I 𝓘(Real, Real) (1 : WithTop ℕ∞)
      (fun y : M =>
        mvfderiv (I := I) ((LinearMap.piApply (e.localFrameCoeff I b k)) σ)
          y (e.localFrame b i y) +
          ∑ j : ι,
            e.localFrameCoeff I b j y (σ y) *
              e.localFrameCoeff I b k y
                ((cov (e.localFrame b j) y) (e.localFrame b i y))) x := by
    refine hderiv.add ?_
    exact ContMDiffAt.sum fun j _ => (hcoeff j).mul (hchristoffel j)
  exact hRhs.congr_of_eventuallyEq hEq

omit [FiniteDimensional ℝ E] [CompleteSpace E] in
theorem mvfderiv_apply_contMDiffAt_of_section
    {f : M -> Real} {X : (p : M) -> TangentSpace I p} {x₀ : M}
    (hf : ContMDiffAt I 𝓘(Real, Real) ∞ f x₀)
    (hX : ContMDiffAt I (I.prod 𝓘(Real, E)) ∞
      (fun p : M => (⟨p, X p⟩ :
        TotalSpace E (TangentSpace I : M -> Type _))) x₀) :
    ContMDiffAt I 𝓘(Real, Real) ∞
      (fun p : M => mvfderiv (I := I) f p (X p)) x₀ := by
  rw [contMDiffAt_infty]
  intro n
  let e := trivializationAt E (TangentSpace I : M -> Type _) x₀
  let Xcoord : M -> E := fun p => e.continuousLinearMapAt Real p (X p)
  have hXcoord :
      ContMDiffAt I 𝓘(Real, E) (n : WithTop ℕ∞) Xcoord x₀ := by
    have hXTop :
        ContMDiffAt I 𝓘(Real, E) ∞
          (fun p : M => (e ⟨p, X p⟩).2) x₀ := by
      simpa [e] using
        (e.contMDiffAt_section_iff
          (s := X)
          (x₀ := x₀)
          (by simp [e])).mp hX
    refine (hXTop.of_le
      (by exact_mod_cast le_top : (n : WithTop ℕ∞) ≤ ∞)).congr_of_eventuallyEq ?_
    filter_upwards [e.open_baseSet.mem_nhds (by simp [e])] with p hp
    have hcoe : ⇑(e.linearMapAt Real p) = fun z => (e ⟨p, z⟩).2 :=
      e.coe_linearMapAt_of_mem (R := Real) hp
    change e.continuousLinearMapAt Real p (X p) = (e ⟨p, X p⟩).2
    exact congrFun hcoe (X p)
  have hF :
      ContMDiffAt (I.prod I) 𝓘(Real, Real) ((n : WithTop ℕ∞) + 1)
        (fun q : M × M => f q.2) (x₀, x₀) := by
    exact (hf.comp (x₀, x₀) contMDiffAt_snd).of_le
      (by exact_mod_cast le_top : ((n : WithTop ℕ∞) + 1) ≤ ∞)
  have hApply :=
    ContMDiffAt.mfderiv_apply
      (I := I) (I' := 𝓘(Real, Real))
      (f := fun (_ : M) (p : M) => f p)
      (g := fun p : M => p)
      (g₁ := fun p : M => p)
      (g₂ := Xcoord)
      (x₀ := x₀)
      (m := (n : WithTop ℕ∞))
      hF contMDiffAt_id contMDiffAt_id hXcoord le_rfl
  refine hApply.congr_of_eventuallyEq ?_
  filter_upwards [e.open_baseSet.mem_nhds (by simp [e])] with p hp
  have hp_src : p ∈ (chartAt H x₀).source := by
    simpa [e, TangentBundle.trivializationAt_baseSet] using hp
  have hf_src : f p ∈ (chartAt Real (f x₀)).source := by
    rw [chartAt_self_eq]
    exact Set.mem_univ _
  rw [inTangentCoordinates_eq (I := I) (I' := 𝓘(Real, Real))
    (f := fun p : M => p) (g := f)
    (ϕ := fun p : M => mfderiv I 𝓘(Real, Real) f p)
    hp_src hf_src]
  have htarget :
      (tangentBundleCore 𝓘(Real, Real) Real).coordChange
        (achart Real (f p)) (achart Real (f x₀)) (f p) = (1 : Real →L[Real] Real) := by
    simp
  have hsource_raw :=
    (TangentBundle.symmL_trivializationAt_eq_core
      (𝕜 := Real) (I := I) (b₀ := x₀) (b := p) hp_src).symm
  have hcancel :
      e.symmL Real p (Xcoord p) = X p := by
    exact e.symmL_continuousLinearMapAt (R := Real) hp (X p)
  rw [htarget, hsource_raw]
  change (mfderiv I 𝓘(Real, Real) f p) (X p) =
    (mfderiv I 𝓘(Real, Real) f p) (e.symmL Real p (Xcoord p))
  rw [hcancel]

omit [FiniteDimensional ℝ E] [CompleteSpace E] in
theorem mvfderiv_apply_contMDiffAt_of_section_one
    {f : M -> Real} {X : (p : M) -> TangentSpace I p} {x₀ : M}
    (hf : ContMDiffAt I 𝓘(Real, Real) (2 : WithTop ℕ∞) f x₀)
    (hX : ContMDiffAt I (I.prod 𝓘(Real, E)) (1 : WithTop ℕ∞)
      (fun p : M => (⟨p, X p⟩ :
        TotalSpace E (TangentSpace I : M -> Type _))) x₀) :
    ContMDiffAt I 𝓘(Real, Real) (1 : WithTop ℕ∞)
      (fun p : M => mvfderiv (I := I) f p (X p)) x₀ := by
  let e := trivializationAt E (TangentSpace I : M -> Type _) x₀
  let Xcoord : M -> E := fun p => e.continuousLinearMapAt Real p (X p)
  have hXcoord :
      ContMDiffAt I 𝓘(Real, E) (1 : WithTop ℕ∞) Xcoord x₀ := by
    have hXtriv :
        ContMDiffAt I 𝓘(Real, E) (1 : WithTop ℕ∞)
          (fun p : M => (e ⟨p, X p⟩).2) x₀ := by
      simpa [e] using
        (e.contMDiffAt_section_iff
          (s := X)
          (x₀ := x₀)
          (by simp [e])).mp hX
    refine hXtriv.congr_of_eventuallyEq ?_
    filter_upwards [e.open_baseSet.mem_nhds (by simp [e])] with p hp
    have hcoe : ⇑(e.linearMapAt Real p) = fun z => (e ⟨p, z⟩).2 :=
      e.coe_linearMapAt_of_mem (R := Real) hp
    change e.continuousLinearMapAt Real p (X p) = (e ⟨p, X p⟩).2
    exact congrFun hcoe (X p)
  have hF :
      ContMDiffAt (I.prod I) 𝓘(Real, Real) (2 : WithTop ℕ∞)
        (fun q : M × M => f q.2) (x₀, x₀) := by
    exact (hf.comp (x₀, x₀) contMDiffAt_snd).congr_of_eventuallyEq
      (Filter.Eventually.of_forall fun _ => rfl)
  have hApply :=
    ContMDiffAt.mfderiv_apply
      (I := I) (I' := 𝓘(Real, Real))
      (f := fun (_ : M) (p : M) => f p)
      (g := fun p : M => p)
      (g₁ := fun p : M => p)
      (g₂ := Xcoord)
      (x₀ := x₀)
      (m := (1 : WithTop ℕ∞))
      hF contMDiffAt_id contMDiffAt_id hXcoord le_rfl
  refine hApply.congr_of_eventuallyEq ?_
  filter_upwards [e.open_baseSet.mem_nhds (by simp [e])] with p hp
  have hp_src : p ∈ (chartAt H x₀).source := by
    simpa [e, TangentBundle.trivializationAt_baseSet] using hp
  have hf_src : f p ∈ (chartAt Real (f x₀)).source := by
    rw [chartAt_self_eq]
    exact Set.mem_univ _
  rw [inTangentCoordinates_eq (I := I) (I' := 𝓘(Real, Real))
    (f := fun p : M => p) (g := f)
    (ϕ := fun p : M => mfderiv I 𝓘(Real, Real) f p)
    hp_src hf_src]
  have htarget :
      (tangentBundleCore 𝓘(Real, Real) Real).coordChange
        (achart Real (f p)) (achart Real (f x₀)) (f p) = (1 : Real →L[Real] Real) := by
    simp
  have hsource_raw :=
    (TangentBundle.symmL_trivializationAt_eq_core
      (𝕜 := Real) (I := I) (b₀ := x₀) (b := p) hp_src).symm
  have hcancel :
      e.symmL Real p (Xcoord p) = X p := by
    exact e.symmL_continuousLinearMapAt (R := Real) hp (X p)
  rw [htarget, hsource_raw]
  change (mfderiv I 𝓘(Real, Real) f p) (X p) =
    (mfderiv I 𝓘(Real, Real) f p) (e.symmL Real p (Xcoord p))
  rw [hcancel]

omit [CompleteSpace E] in
theorem localFrameCoeff_extDeriv_contMDiffAt
    {ι : Type*}
    (e : Trivialization E (TotalSpace.proj : TotalSpace E (TangentSpace I : M → Type _) → M))
    [MemTrivializationAtlas e] (b : Module.Basis ι Real E)
    {σ : (x : M) → TangentSpace I x} {x : M}
    (hx : x ∈ e.baseSet)
    (hσ : ContMDiffAt I (I.prod 𝓘(Real, E)) ∞ (T% σ) x)
    (i k : ι) :
    ContMDiffAt I 𝓘(Real, Real) ∞
      (fun y : M =>
        mvfderiv (I := I) ((LinearMap.piApply (e.localFrameCoeff I b k)) σ)
          y (e.localFrame b i y)) x := by
  have hcoeff :
      ContMDiffAt I 𝓘(Real, Real) ∞
        ((LinearMap.piApply (e.localFrameCoeff I b k)) σ) x :=
    contMDiffAt_localFrameCoeff
      (I := I) (V := TangentSpace I) (e := e) (b := b) (s := σ)
      (k := (∞ : WithTop ℕ∞)) hx hσ k
  have hframe :
      ContMDiffAt I (I.prod 𝓘(Real, E)) ∞
        (T% (e.localFrame b i)) x :=
    (e.isLocalFrameOn_localFrame_baseSet I ∞ b).contMDiffAt
      e.open_baseSet hx i
  exact mvfderiv_apply_contMDiffAt_of_section
    (I := I)
    (f := (LinearMap.piApply (e.localFrameCoeff I b k)) σ)
    (X := e.localFrame b i) hcoeff hframe

omit [CompleteSpace E] in
theorem localFrameCoeff_extDeriv_contMDiffAt_one
    {ι : Type*}
    (e : Trivialization E (TotalSpace.proj : TotalSpace E (TangentSpace I : M → Type _) → M))
    [MemTrivializationAtlas e] (b : Module.Basis ι Real E)
    {σ : (x : M) → TangentSpace I x} {x : M}
    (hx : x ∈ e.baseSet)
    (hσ : ContMDiffAt I (I.prod 𝓘(Real, E)) (2 : WithTop ℕ∞) (T% σ) x)
    (i k : ι) :
    ContMDiffAt I 𝓘(Real, Real) (1 : WithTop ℕ∞)
      (fun y : M =>
        mvfderiv (I := I) ((LinearMap.piApply (e.localFrameCoeff I b k)) σ)
          y (e.localFrame b i y)) x := by
  have hcoeff :
      ContMDiffAt I 𝓘(Real, Real) (2 : WithTop ℕ∞)
        ((LinearMap.piApply (e.localFrameCoeff I b k)) σ) x :=
    contMDiffAt_localFrameCoeff
      (I := I) (V := TangentSpace I) (e := e) (b := b) (s := σ)
      (k := (2 : WithTop ℕ∞)) hx hσ k
  have hframe :
      ContMDiffAt I (I.prod 𝓘(Real, E)) (1 : WithTop ℕ∞)
        (T% (e.localFrame b i)) x :=
    ((e.isLocalFrameOn_localFrame_baseSet I ∞ b).contMDiffAt
      e.open_baseSet hx i).of_le (by simp : (1 : WithTop ℕ∞) ≤ ∞)
  exact mvfderiv_apply_contMDiffAt_of_section_one
    (I := I)
    (f := (LinearMap.piApply (e.localFrameCoeff I b k)) σ)
    (X := e.localFrame b i) hcoeff hframe

omit [CompleteSpace E] in
theorem covariantDerivative_localHomCoeff_contMDiffAt_of_section
    {ι : Type*} [Finite ι]
    (cov : CovariantDerivative I E (TangentSpace I : M → Type _))
    (e : Trivialization E (TotalSpace.proj : TotalSpace E (TangentSpace I : M → Type _) → M))
    [MemTrivializationAtlas e] (b : Module.Basis ι Real E)
    {σ : (x : M) → TangentSpace I x} {x : M}
    (hx : x ∈ e.baseSet)
    (hσdiff : ∀ᶠ y in 𝓝 x, MDiffAt (T% σ) y)
    (hσ : ContMDiffAt I (I.prod 𝓘(Real, E)) ∞ (T% σ) x)
    (i k : ι)
    (hchristoffel : ∀ j : ι, ContMDiffAt I 𝓘(Real, Real) ∞
      (fun y : M =>
        e.localFrameCoeff I b k y
          ((cov (e.localFrame b j) y) (e.localFrame b i y))) x) :
    ContMDiffAt I 𝓘(Real, Real) ∞
      (fun y : M => localHomCoeff (I := I) e b i k y (cov σ y)) x := by
  refine covariantDerivative_localHomCoeff_contMDiffAt
    (I := I) cov e b hx hσdiff i k ?_ ?_ hchristoffel
  · exact localFrameCoeff_extDeriv_contMDiffAt (I := I) e b hx hσ i k
  · intro j
    exact contMDiffAt_localFrameCoeff
      (I := I) (V := TangentSpace I) (e := e) (b := b) (s := σ)
      (k := (∞ : WithTop ℕ∞)) hx hσ j

omit [CompleteSpace E] in
theorem covariantDerivative_localHomCoeff_contMDiffAt_of_section_one
    {ι : Type*} [Finite ι]
    (cov : CovariantDerivative I E (TangentSpace I : M → Type _))
    (e : Trivialization E (TotalSpace.proj : TotalSpace E (TangentSpace I : M → Type _) → M))
    [MemTrivializationAtlas e] (b : Module.Basis ι Real E)
    {σ : (x : M) → TangentSpace I x} {x : M}
    (hx : x ∈ e.baseSet)
    (hσdiff : ∀ᶠ y in 𝓝 x, MDiffAt (T% σ) y)
    (hσ : ContMDiffAt I (I.prod 𝓘(Real, E)) (2 : WithTop ℕ∞) (T% σ) x)
    (i k : ι)
    (hchristoffel : ∀ j : ι, ContMDiffAt I 𝓘(Real, Real) ∞
      (fun y : M =>
        e.localFrameCoeff I b k y
          ((cov (e.localFrame b j) y) (e.localFrame b i y))) x) :
    ContMDiffAt I 𝓘(Real, Real) (1 : WithTop ℕ∞)
      (fun y : M => localHomCoeff (I := I) e b i k y (cov σ y)) x := by
  refine covariantDerivative_localHomCoeff_contMDiffAt_one
    (I := I) cov e b hx hσdiff i k ?_ ?_ ?_
  · exact localFrameCoeff_extDeriv_contMDiffAt_one (I := I) e b hx hσ i k
  · intro j
    have hcoeff2 :
        ContMDiffAt I 𝓘(Real, Real) (2 : WithTop ℕ∞)
          (fun y : M => e.localFrameCoeff I b j y (σ y)) x :=
      contMDiffAt_localFrameCoeff
        (I := I) (V := TangentSpace I) (e := e) (b := b) (s := σ)
        (k := (2 : WithTop ℕ∞)) hx hσ j
    exact hcoeff2.of_le (by simp : (1 : WithTop ℕ∞) ≤ (2 : WithTop ℕ∞))
  · intro j
    exact (hchristoffel j).of_le (by simp : (1 : WithTop ℕ∞) ≤ ∞)

omit [CompleteSpace E] in
theorem covariantDerivative_homSection_contMDiffAt_of_coeff
    {ι : Type*} [Finite ι]
    (cov : CovariantDerivative I E (TangentSpace I : M → Type _))
    (e : Trivialization E (TotalSpace.proj : TotalSpace E (TangentSpace I : M → Type _) → M))
    [MemTrivializationAtlas e] (b : Module.Basis ι Real E)
    {σ : (x : M) → TangentSpace I x} {x : M}
    (hx : x ∈ e.baseSet)
    (hσdiff : ∀ᶠ y in 𝓝 x, MDiffAt (T% σ) y)
    (hσ : ContMDiffAt I (I.prod 𝓘(Real, E)) ∞ (T% σ) x)
    (hchristoffel : ∀ i k j : ι, ContMDiffAt I 𝓘(Real, Real) ∞
      (fun y : M =>
        e.localFrameCoeff I b k y
          ((cov (e.localFrame b j) y) (e.localFrame b i y))) x) :
    ContMDiffAt I (I.prod 𝓘(Real, E →L[Real] E)) ∞
      (fun y : M =>
        (⟨y, cov σ y⟩ :
          TotalSpace (E →L[Real] E)
            (fun y : M => TangentSpace I y →L[Real] TangentSpace I y))) x := by
  classical
  let eHom := e.continuousLinearMap (RingHom.id Real) e
  let bHom := continuousLinearMapHomBasis (𝕜 := Real) b b
  have hhom : x ∈ eHom.baseSet := by
    simp [eHom, hx]
  refine
    (contMDiffAt_iff_localFrameCoeff (I := I) (e := eHom) bHom
      (s := fun y : M => cov σ y) (k := (∞ : WithTop ℕ∞)) hhom).mpr ?_
  rintro ⟨k, i⟩
  have hlocal :
      ContMDiffAt I 𝓘(Real, Real) ∞
        (fun y : M => localHomCoeff (I := I) e b i k y (cov σ y)) x :=
    covariantDerivative_localHomCoeff_contMDiffAt_of_section
      (I := I) cov e b hx hσdiff hσ i k (fun j => hchristoffel i k j)
  have heq :
      (fun y : M =>
          (eHom.localFrameCoeff I bHom (k, i) y) (cov σ y)) =ᶠ[𝓝 x]
        fun y : M => localHomCoeff (I := I) e b i k y (cov σ y) := by
    filter_upwards [e.open_baseSet.mem_nhds hx] with y hy
    exact homLocalFrameCoeff_eq_localHomCoeff (I := I) e b hy (cov σ y) i k
  exact hlocal.congr_of_eventuallyEq heq

omit [CompleteSpace E] in
theorem covariantDerivative_homSection_contMDiffAt_of_coeff_one
    {ι : Type*} [Finite ι]
    (cov : CovariantDerivative I E (TangentSpace I : M → Type _))
    (e : Trivialization E (TotalSpace.proj : TotalSpace E (TangentSpace I : M → Type _) → M))
    [MemTrivializationAtlas e] (b : Module.Basis ι Real E)
    {σ : (x : M) → TangentSpace I x} {x : M}
    (hx : x ∈ e.baseSet)
    (hσdiff : ∀ᶠ y in 𝓝 x, MDiffAt (T% σ) y)
    (hσ : ContMDiffAt I (I.prod 𝓘(Real, E)) (2 : WithTop ℕ∞) (T% σ) x)
    (hchristoffel : ∀ i k j : ι, ContMDiffAt I 𝓘(Real, Real) ∞
      (fun y : M =>
        e.localFrameCoeff I b k y
          ((cov (e.localFrame b j) y) (e.localFrame b i y))) x) :
    ContMDiffAt I (I.prod 𝓘(Real, E →L[Real] E)) (1 : WithTop ℕ∞)
      (fun y : M =>
        (⟨y, cov σ y⟩ :
          TotalSpace (E →L[Real] E)
            (fun y : M => TangentSpace I y →L[Real] TangentSpace I y))) x := by
  classical
  let eHom := e.continuousLinearMap (RingHom.id Real) e
  let bHom := continuousLinearMapHomBasis (𝕜 := Real) b b
  have hhom : x ∈ eHom.baseSet := by
    simp [eHom, hx]
  refine
    (contMDiffAt_iff_localFrameCoeff (I := I) (e := eHom) bHom
      (s := fun y : M => cov σ y) (k := (1 : WithTop ℕ∞)) hhom).mpr ?_
  rintro ⟨k, i⟩
  have hlocal :
      ContMDiffAt I 𝓘(Real, Real) (1 : WithTop ℕ∞)
        (fun y : M => localHomCoeff (I := I) e b i k y (cov σ y)) x :=
    covariantDerivative_localHomCoeff_contMDiffAt_of_section_one
      (I := I) cov e b hx hσdiff hσ i k (fun j => hchristoffel i k j)
  have heq :
      (fun y : M =>
          (eHom.localFrameCoeff I bHom (k, i) y) (cov σ y)) =ᶠ[𝓝 x]
        fun y : M => localHomCoeff (I := I) e b i k y (cov σ y) := by
    filter_upwards [e.open_baseSet.mem_nhds hx] with y hy
    exact homLocalFrameCoeff_eq_localHomCoeff (I := I) e b hy (cov σ y) i k
  exact hlocal.congr_of_eventuallyEq heq


end DifferentialGeometry
