import Mathlib.LinearAlgebra.Orientation
import Mathlib.LinearAlgebra.Basis.Prod
import Mathlib.LinearAlgebra.Matrix.Block
import Mathlib.Topology.Algebra.Module.FiniteDimension
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Analysis.Normed.Operator.BoundedLinearMaps

/-!
# The orientation induced on a complement of an ordered frame

Let `L : F × V ≃ₗ E` be a linear equivalence and `bF` an ordered basis of `F` (the "ordered
Euclidean factor"). An orientation `oE` of `E` induces an orientation of `V`: the unique `oV` such
that, for every basis `b` of `V` with orientation `oV`, the frame `(L (bF a, 0))_a, (L (0, b i))_i`
(in this order, reindexed by `σ`) is positively oriented for `oE`
(`splitInducedOrientation`, characterised by `splitInducedOrientation_eq_iff`). This is the
general-rank version of `normalFirstOrientation` (which is hard-wired to `ℝ × F`, `Fin 3`, `Fin 2`).

Naturality in `E` (`splitInducedOrientation_map`) and in `V` (`splitInducedOrientation_change`),
and constancy along continuous families (`splitInducedOrientation_eventually_eq`) are the inputs of
the chart arguments in `AmbientSplitOrientation`.
-/

set_option autoImplicit false

noncomputable section

open Function Module Filter
open scoped Topology

namespace DifferentialGeometry.Topology.Manifold

section Linear

variable {F V E : Type*} [AddCommGroup F] [Module ℝ F] [AddCommGroup V] [Module ℝ V]
  [AddCommGroup E] [Module ℝ E]
  {ιF ιV ιE : Type*}

/-- The ordered frame `(L (bF a, 0))_a, (L (0, bV i))_i` of `E`, reindexed by `σ`. -/
def splitFrameBasis (bF : Basis ιF ℝ F) (bV : Basis ιV ℝ V) (σ : ιF ⊕ ιV ≃ ιE)
    (L : (F × V) ≃ₗ[ℝ] E) : Basis ιE ℝ E :=
  ((bF.prod bV).reindex σ).map L

theorem splitFrameBasis_apply_inl (bF : Basis ιF ℝ F) (bV : Basis ιV ℝ V) (σ : ιF ⊕ ιV ≃ ιE)
    (L : (F × V) ≃ₗ[ℝ] E) (a : ιF) :
    splitFrameBasis bF bV σ L (σ (Sum.inl a)) = L (bF a, 0) := by
  simp [splitFrameBasis, Basis.prod_apply]

theorem splitFrameBasis_apply_inr (bF : Basis ιF ℝ F) (bV : Basis ιV ℝ V) (σ : ιF ⊕ ιV ≃ ιE)
    (L : (F × V) ≃ₗ[ℝ] E) (i : ιV) :
    splitFrameBasis bF bV σ L (σ (Sum.inr i)) = L (0, bV i) := by
  simp [splitFrameBasis, Basis.prod_apply]

private theorem prod_toMatrix_eq_fromBlocks [DecidableEq ιF] (bF : Basis ιF ℝ F) (bV bV' : Basis ιV ℝ V) :
    (bF.prod bV).toMatrix (bF.prod bV') = Matrix.fromBlocks 1 0 0 (bV.toMatrix bV') := by
  ext i j
  rcases i with i | i <;> rcases j with j | j <;>
    simp [Basis.toMatrix_apply, Basis.prod_repr_inl, Basis.prod_repr_inr, Basis.prod_apply,
      Matrix.one_apply, Finsupp.single_apply, eq_comm]

variable [Fintype ιV] [DecidableEq ιV] [Fintype ιE] [DecidableEq ιE]

/-- The determinant of one ordered frame against another with the same `F`-part. -/
theorem splitFrameBasis_det (bF : Basis ιF ℝ F) (bV bV' : Basis ιV ℝ V) (σ : ιF ⊕ ιV ≃ ιE)
    (L : (F × V) ≃ₗ[ℝ] E) :
    (splitFrameBasis bF bV σ L).det (splitFrameBasis bF bV' σ L) = bV.det bV' := by
  classical
  let _ : Fintype ιF := by
    let _ : Fintype (ιF ⊕ ιV) := Fintype.ofEquiv ιE σ.symm
    exact Fintype.ofInjective (Sum.inl : ιF → ιF ⊕ ιV) Sum.inl_injective
  rw [splitFrameBasis, Basis.det_map]
  have h1 : (L.symm ∘ ⇑(splitFrameBasis bF bV' σ L)) = ⇑((bF.prod bV').reindex σ) := by
    funext i
    simp [splitFrameBasis]
  rw [h1, Basis.det_reindex]
  have h2 : (⇑((bF.prod bV').reindex σ) ∘ ⇑σ) = ⇑(bF.prod bV') := by
    funext i
    simp
  rw [h2, Basis.det_apply, Basis.det_apply, prod_toMatrix_eq_fromBlocks,
    Matrix.det_fromBlocks_zero₂₁, Matrix.det_one, one_mul]

open Classical in
/-- **The orientation induced on `V`** by an orientation `oE` of `E`, the ordered frame `bF` of
`F` and the identification `L : F × V ≃ E`; computed with the reference basis `bV` (the result does
not depend on it: `splitInducedOrientation_basis_independent`). -/
def splitInducedOrientation (bF : Basis ιF ℝ F) (bV : Basis ιV ℝ V) (σ : ιF ⊕ ιV ≃ ιE)
    (L : (F × V) ≃ₗ[ℝ] E) (oE : Orientation ℝ E ιE) : Orientation ℝ V ιV :=
  if (splitFrameBasis bF bV σ L).orientation = oE then bV.orientation else -bV.orientation

omit [Fintype ιE] [DecidableEq ιE] [Fintype ιV] [DecidableEq ιV] in
private theorem orientation_cases_of_neg {X : Type*} [AddCommGroup X] [Module ℝ X]
    {o p q : Orientation ℝ X ιE} (hq : q = -p) (hop : o = p ∨ o = -p) : (p = o ↔ ¬ q = o) := by
  rw [hq]
  rcases hop with h | h
  · subst h
    exact ⟨fun _ h' => Module.Ray.ne_neg_self o h'.symm, fun _ => rfl⟩
  · subst h
    refine ⟨fun h' => absurd h' (Module.Ray.ne_neg_self p), fun h' => absurd rfl h'⟩

theorem splitInducedOrientation_basis_independent (bF : Basis ιF ℝ F) (bV bV' : Basis ιV ℝ V)
    (σ : ιF ⊕ ιV ≃ ιE) (L : (F × V) ≃ₗ[ℝ] E) (oE : Orientation ℝ E ιE) :
    splitInducedOrientation bF bV σ L oE = splitInducedOrientation bF bV' σ L oE := by
  classical
  have hdet := splitFrameBasis_det bF bV bV' σ L
  have hne : bV.det bV' ≠ 0 := (bV.isUnit_det bV').ne_zero
  unfold splitInducedOrientation
  rcases lt_or_gt_of_ne hne with hneg | hpos
  · -- opposite orientations
    have hV : bV'.orientation = -bV.orientation := by
      rw [← Basis.orientation_ne_iff_eq_neg]
      intro h
      rw [eq_comm, Basis.orientation_eq_iff_det_pos] at h
      exact lt_asymm hneg h
    have hE : (splitFrameBasis bF bV' σ L).orientation =
        -(splitFrameBasis bF bV σ L).orientation := by
      rw [← Basis.orientation_ne_iff_eq_neg]
      intro h
      rw [eq_comm, Basis.orientation_eq_iff_det_pos, hdet] at h
      exact lt_asymm hneg h
    have hiff := orientation_cases_of_neg hE
      ((splitFrameBasis bF bV σ L).orientation_eq_or_eq_neg oE)
    by_cases h : (splitFrameBasis bF bV σ L).orientation = oE
    · rw [ite_eq_left h, ite_eq_right (hiff.mp h), hV]
      exact (neg_neg bV.orientation).symm
    · have h' : (splitFrameBasis bF bV' σ L).orientation = oE := by
        by_contra h''
        exact h (hiff.mpr h'')
      rw [ite_eq_right h, ite_eq_left h', hV]
  · have hV : bV.orientation = bV'.orientation := (Basis.orientation_eq_iff_det_pos _ _).mpr hpos
    have hE : (splitFrameBasis bF bV σ L).orientation = (splitFrameBasis bF bV' σ L).orientation :=
      (Basis.orientation_eq_iff_det_pos _ _).mpr (hdet ▸ hpos)
    rw [hE, hV]

/-- **Characterisation (compatibility with the product orientation).** A basis `b` of `V` is
positive for the induced orientation iff the ordered frame `(L (bF a, 0), L (0, b i))` is positive
for `oE`. -/
theorem splitInducedOrientation_eq_iff {bF : Basis ιF ℝ F} (bV : Basis ιV ℝ V) {b : Basis ιV ℝ V}
    {σ : ιF ⊕ ιV ≃ ιE} {L : (F × V) ≃ₗ[ℝ] E} {oE : Orientation ℝ E ιE} :
    b.orientation = splitInducedOrientation bF bV σ L oE ↔
      (splitFrameBasis bF b σ L).orientation = oE := by
  classical
  rw [splitInducedOrientation_basis_independent bF bV b σ L oE]
  unfold splitInducedOrientation
  by_cases h : (splitFrameBasis bF b σ L).orientation = oE
  · rw [ite_eq_left h]
    exact ⟨fun _ => h, fun _ => rfl⟩
  · rw [ite_eq_right h]
    exact ⟨fun h' => absurd h' (Module.Ray.ne_neg_self b.orientation), fun h' => absurd h' h⟩

theorem splitInducedOrientation_neg (bF : Basis ιF ℝ F) (bV : Basis ιV ℝ V)
    (σ : ιF ⊕ ιV ≃ ιE) (L : (F × V) ≃ₗ[ℝ] E) (oE : Orientation ℝ E ιE) :
    splitInducedOrientation bF bV σ L (-oE) = -splitInducedOrientation bF bV σ L oE := by
  classical
  unfold splitInducedOrientation
  rcases (splitFrameBasis bF bV σ L).orientation_eq_or_eq_neg oE with h | h
  · subst h
    rw [ite_eq_left rfl, ite_eq_right (Module.Ray.ne_neg_self _)]
  · subst h
    have h1 : (splitFrameBasis bF bV σ L).orientation =
        - -(splitFrameBasis bF bV σ L).orientation :=
      (neg_neg (splitFrameBasis bF bV σ L).orientation).symm
    rw [ite_eq_left h1, ite_eq_right (Module.Ray.ne_neg_self _)]
    exact (neg_neg bV.orientation).symm

variable {G : Type*} [AddCommGroup G] [Module ℝ G]

/-- **Naturality in `E`.** -/
theorem splitInducedOrientation_map (bF : Basis ιF ℝ F) (bV : Basis ιV ℝ V)
    (σ : ιF ⊕ ιV ≃ ιE) (L : (F × V) ≃ₗ[ℝ] E) (g : E ≃ₗ[ℝ] G) (oE : Orientation ℝ E ιE) :
    splitInducedOrientation bF bV σ (L.trans g) (Orientation.map ιE g oE) =
      splitInducedOrientation bF bV σ L oE := by
  classical
  have hb : splitFrameBasis bF bV σ (L.trans g) = (splitFrameBasis bF bV σ L).map g := by
    apply Basis.eq_of_apply_eq
    intro i
    simp [splitFrameBasis]
  unfold splitInducedOrientation
  rw [hb, Basis.orientation_map]
  have hinj : (Orientation.map ιE g (splitFrameBasis bF bV σ L).orientation =
      Orientation.map ιE g oE) ↔ (splitFrameBasis bF bV σ L).orientation = oE :=
    (Orientation.map ιE g).injective.eq_iff
  by_cases h : (splitFrameBasis bF bV σ L).orientation = oE
  · rw [ite_eq_left (hinj.mpr h), ite_eq_left h]
  · rw [ite_eq_right (fun h' => h (hinj.mp h')), ite_eq_right h]

/-- **Naturality in `V`.** Precomposing the identification with `id × A⁻¹` maps the induced
orientation by `A`. -/
theorem splitInducedOrientation_change (bF : Basis ιF ℝ F) (bV : Basis ιV ℝ V)
    (σ : ιF ⊕ ιV ≃ ιE) (L : (F × V) ≃ₗ[ℝ] E) (A : V ≃ₗ[ℝ] V) (oE : Orientation ℝ E ιE) :
    splitInducedOrientation bF bV σ (((LinearEquiv.refl ℝ F).prodCongr A.symm).trans L) oE =
      Orientation.map ιV A (splitInducedOrientation bF bV σ L oE) := by
  classical
  rw [splitInducedOrientation_basis_independent bF bV (bV.map A) σ _ oE]
  have hb : splitFrameBasis bF (bV.map A) σ (((LinearEquiv.refl ℝ F).prodCongr A.symm).trans L) =
      splitFrameBasis bF bV σ L := by
    apply Basis.eq_of_apply_eq
    intro i
    obtain ⟨k, rfl⟩ := σ.surjective i
    rcases k with a | k
    · rw [splitFrameBasis_apply_inl, splitFrameBasis_apply_inl]
      simp
    · rw [splitFrameBasis_apply_inr, splitFrameBasis_apply_inr]
      simp
  unfold splitInducedOrientation
  rw [hb, Basis.orientation_map]
  by_cases h : (splitFrameBasis bF bV σ L).orientation = oE
  · rw [ite_eq_left h, ite_eq_left h]
  · rw [ite_eq_right h, ite_eq_right h, Orientation.map_neg]

end Linear

section Continuity

variable {X F V E : Type*} [TopologicalSpace X]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [NormedAddCommGroup V] [NormedSpace ℝ V]
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  {ιF ιV ιE : Type*} [Fintype ιV] [DecidableEq ιV] [Fintype ιE] [DecidableEq ιE]

/-- **Constancy along continuous families.** -/
theorem splitInducedOrientation_eventually_eq (bF : Basis ιF ℝ F) (bV : Basis ιV ℝ V)
    (σ : ιF ⊕ ιV ≃ ιE) (L : X → (F × V) ≃L[ℝ] E) (x : X)
    (hL : ContinuousAt (fun y => (L y : (F × V) →L[ℝ] E)) x) (oE : Orientation ℝ E ιE) :
    ∀ᶠ y in 𝓝 x, splitInducedOrientation bF bV σ (L y).toLinearEquiv oE =
      splitInducedOrientation bF bV σ (L x).toLinearEquiv oE := by
  have : Finite (ιF ⊕ ιV) := Finite.of_equiv ιE σ.symm
  have : Finite ιF := Finite.of_injective (Sum.inl : ιF → ιF ⊕ ιV) Sum.inl_injective
  let : FiniteDimensional ℝ F := bF.finiteDimensional_of_finite
  let : FiniteDimensional ℝ V := bV.finiteDimensional_of_finite
  let : FiniteDimensional ℝ E :=
    FiniteDimensional.of_injective (L x).symm.toLinearMap (L x).symm.injective
  let c : X → E ≃L[ℝ] E := fun y => (L x).symm.trans (L y)
  have hc : ContinuousAt (fun y => (c y : E →L[ℝ] E)) x := by
    change ContinuousAt (fun y => (L y : (F × V) →L[ℝ] E).comp ((L x).symm : E →L[ℝ] (F × V))) x
    exact hL.clm_comp continuousAt_const
  have hcx : c x = ContinuousLinearEquiv.refl ℝ E := by
    apply ContinuousLinearEquiv.ext
    funext v
    exact (L x).apply_symm_apply v
  have hpos : 0 < (c x : E →L[ℝ] E).det := by
    rw [hcx]
    change 0 < LinearMap.det (LinearMap.id : E →ₗ[ℝ] E)
    rw [LinearMap.det_id]
    exact zero_lt_one
  have hd := ContinuousLinearMap.continuous_det.continuousAt.comp hc
  have hdim : Fintype.card ιE = Module.finrank ℝ E :=
    (Module.finrank_eq_card_basis (splitFrameBasis bF bV σ (L x).toLinearEquiv)).symm
  filter_upwards [hd.eventually (lt_mem_nhds hpos)] with y hy
  have ho : Orientation.map ιE (c y).toLinearEquiv oE = oE :=
    (Orientation.map_eq_iff_det_pos oE (c y).toLinearEquiv hdim).mpr hy
  have h := splitInducedOrientation_map bF bV σ (L x).toLinearEquiv (c y).toLinearEquiv oE
  rw [ho] at h
  have heq : (L x).toLinearEquiv.trans (c y).toLinearEquiv = (L y).toLinearEquiv := by
    apply LinearEquiv.ext
    intro v
    change L y ((L x).symm ((L x) v)) = L y v
    rw [(L x).symm_apply_apply]
  rw [heq] at h
  exact h

end Continuity

end DifferentialGeometry.Topology.Manifold
