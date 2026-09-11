import Mathlib.Analysis.InnerProductSpace.Projection.FiniteDimensional
import Mathlib.Analysis.Normed.Module.Connected
import Mathlib.Topology.Homotopy.Basic
import Mathlib.Analysis.InnerProductSpace.GramSchmidtOrtho
import Mathlib.LinearAlgebra.Matrix.Block
import Mathlib.LinearAlgebra.Determinant
import Mathlib.LinearAlgebra.Orientation
import Mathlib.Tactic.NormNum


noncomputable section
open Set Submodule InnerProductSpace
open scoped Topology
namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

section Pair
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E]

private def hyperplaneReflectionMap (u : E) : C(E, E) :=
  ⟨(ℝ ∙ u)ᗮ.reflection, (ℝ ∙ u)ᗮ.reflection.continuous⟩

omit [FiniteDimensional ℝ E] in
private theorem hyperplaneReflectionMap_apply (u z : E) :
    hyperplaneReflectionMap u z =
      -((2 : ℝ) • ((inner ℝ u z / ‖u‖ ^ 2) • u) - z) := by
  change (ℝ ∙ u)ᗮ.reflection z =
    -((2 : ℝ) • ((inner ℝ u z / ‖u‖ ^ 2) • u) - z)
  simpa only [two_smul, add_smul, RCLike.ofReal_real_eq_id, id_eq] using (Submodule.reflection_orthogonal_apply (ℝ ∙ u) z).trans
    (congrArg Neg.neg (Submodule.reflection_singleton_apply u z))

omit [FiniteDimensional ℝ E] in
private theorem hyperplaneReflectionMap_joint_continuous
    {A : Type*} [TopologicalSpace A] {v z : A → E}
    (hv : Continuous v) (hz : Continuous z) (hne : ∀ a, v a ≠ 0) :
    Continuous (fun a => hyperplaneReflectionMap (v a) (z a)) := by
  simp only [hyperplaneReflectionMap_apply]
  exact ((((hv.inner hz).div (hv.norm.pow 2)
    (fun a => pow_ne_zero 2 (norm_ne_zero_iff.mpr (hne a)))).smul hv).const_smul
      (2 : ℝ)).sub hz |>.neg

omit [FiniteDimensional ℝ E] in
private theorem reflection_pair_homotopy
    (hdim : 1 < Module.rank ℝ E) (u v : E) (hu : u ≠ 0) (hv : v ≠ 0) :
    ∃ H : ((hyperplaneReflectionMap u).comp (hyperplaneReflectionMap v)).Homotopy
        (ContinuousMap.id E),
      ∀ t z, ‖H (t, z)‖ = ‖z‖ := by
  have hpath := (isPathConnected_compl_singleton_of_one_lt_rank hdim (0 : E)).joinedIn
    v (by simpa using hv) u (by simpa using hu)
  let γ := hpath.somePath
  have hγ : ∀ t, γ t ≠ 0 := by
    intro t
    have hm : γ t ∈ ({0}ᶜ : Set E) := hpath.somePath_mem t
    exact hm
  let H : ((hyperplaneReflectionMap u).comp (hyperplaneReflectionMap v)).Homotopy
      (ContinuousMap.id E) := {
    toFun := fun p => hyperplaneReflectionMap u (hyperplaneReflectionMap (γ p.1) p.2)
    continuous_toFun := (hyperplaneReflectionMap u).continuous.comp
      (hyperplaneReflectionMap_joint_continuous (γ.continuous.comp continuous_fst)
        continuous_snd (fun p => hγ p.1))
    map_zero_left := fun z => by simp [γ]
    map_one_left := fun z => by
      change (ℝ ∙ u)ᗮ.reflection ((ℝ ∙ γ 1)ᗮ.reflection z) = z
      rw [show γ 1 = u from γ.target]
      exact (ℝ ∙ u)ᗮ.reflection_reflection z }
  refine ⟨H, ?_⟩
  intro t z
  change ‖(ℝ ∙ u)ᗮ.reflection ((ℝ ∙ γ t)ᗮ.reflection z)‖ = ‖z‖
  rw [LinearIsometryEquiv.norm_map, LinearIsometryEquiv.norm_map]


private theorem hyperplane_reflection_det (u : E) (hu : u ≠ 0) :
    LinearMap.det (ℝ ∙ u)ᗮ.reflection.toLinearMap = -1 := by
  rw [Submodule.det_reflection, Submodule.orthogonal_orthogonal,
    finrank_span_singleton hu, pow_one]

omit [FiniteDimensional ℝ E] in
private theorem zero_hyperplane_reflection :
    (ℝ ∙ (0 : E))ᗮ.reflection = 1 := by
  ext z
  change hyperplaneReflectionMap (0 : E) z = z
  simp [hyperplaneReflectionMap_apply]

attribute [local instance] Classical.propDecidable in
omit [FiniteDimensional ℝ E] in
private theorem reflection_product_remove_zero (l : List E) :
    ((l.filter (fun v => decide (v ≠ 0))).map (fun v => (ℝ ∙ v)ᗮ.reflection)).prod =
      (l.map (fun v => (ℝ ∙ v)ᗮ.reflection)).prod := by
  classical
  induction l with
  | nil => rfl
  | cons v l ih =>
    by_cases hv : v = 0
    · have hb : ¬(decide (v ≠ 0) = true) := by simp [hv]
      rw [List.filter_cons_of_neg (p := fun w : E => decide (w ≠ 0)) hb]
      simp only [List.map_cons, List.prod_cons,
        hv, zero_hyperplane_reflection, one_mul, ih]
    · have hb : decide (v ≠ 0) = true := by simp [hv]
      rw [List.filter_cons_of_pos (p := fun w : E => decide (w ≠ 0)) hb]
      simp only [List.map_cons, List.prod_cons, ih]

private theorem reflection_product_det (l : List E) (hne : ∀ v ∈ l, v ≠ 0) :
    LinearMap.det ((l.map (fun v => (ℝ ∙ v)ᗮ.reflection)).prod).toLinearMap =
      (-1 : ℝ) ^ l.length := by
  induction l with
  | nil =>
    change LinearMap.det (LinearMap.id : E →ₗ[ℝ] E) = 1
    exact LinearMap.det_id
  | cons v l ih =>
    have hv := hne v (by simp)
    have hl : ∀ w ∈ l, w ≠ 0 := fun w hw => hne w (by simp [hw])
    simp only [List.map_cons, List.prod_cons, List.length_cons]
    change LinearMap.det ((ℝ ∙ v)ᗮ.reflection.toLinearMap.comp
      ((l.map (fun w => (ℝ ∙ w)ᗮ.reflection)).prod).toLinearMap) = _
    rw [LinearMap.det_comp, hyperplane_reflection_det v hv, ih hl, pow_succ]
    ring

private theorem positive_isometry_reflection_pair
    (hdim : Module.finrank ℝ E ≤ 3) (φ : E ≃ₗᵢ[ℝ] E)
    (hpos : 0 < LinearMap.det φ.toLinearMap) :
    φ = 1 ∨ ∃ u v : E, u ≠ 0 ∧ v ≠ 0 ∧
      φ = (ℝ ∙ u)ᗮ.reflection * (ℝ ∙ v)ᗮ.reflection := by
  classical
  obtain ⟨l, hlen, hφ⟩ := φ.reflections_generate_dim
  let m := l.filter (fun v => decide (v ≠ 0))
  have hm : m.length ≤ 3 := (List.length_filter_le _ _).trans (hlen.trans hdim)
  have hn : ∀ v ∈ m, v ≠ 0 := by
    intro v hv
    exact of_decide_eq_true (List.mem_filter.mp hv).2
  have hprod : φ = (m.map (fun v => (ℝ ∙ v)ᗮ.reflection)).prod :=
    hφ.trans (reflection_product_remove_zero l).symm
  have hd : 0 < (-1 : ℝ) ^ m.length := by
    rw [hprod, reflection_product_det m hn] at hpos
    exact hpos
  have hlen_cases : m.length = 0 ∨ m.length = 2 := by
    have hc : m.length = 0 ∨ m.length = 1 ∨ m.length = 2 ∨ m.length = 3 := by omega
    rcases hc with h | h | h | h
    · exact Or.inl h
    · norm_num [h] at hd
    · exact Or.inr h
    · norm_num [h] at hd
  rcases hlen_cases with hzero | htwo
  · left
    rw [List.length_eq_zero_iff.mp hzero] at hprod
    simpa using hprod
  · right
    obtain ⟨u, v, huv⟩ := List.length_eq_two.mp htwo
    refine ⟨u, v, hn u (by simp [huv]), hn v (by simp [huv]), ?_⟩
    simpa only [huv, List.map_cons, List.map_nil, List.prod_cons, List.prod_nil,
      mul_one] using hprod

private theorem positive_isometry_homotopy
    (hdimLower : 1 < Module.rank ℝ E) (hdimUpper : Module.finrank ℝ E ≤ 3)
    (φ : E ≃ₗᵢ[ℝ] E) (hpos : 0 < LinearMap.det φ.toLinearMap) :
    ∃ H : (⟨φ, φ.continuous⟩ : C(E, E)).Homotopy (ContinuousMap.id E),
      ∀ t z, ‖H (t, z)‖ = ‖z‖ := by
  rcases positive_isometry_reflection_pair hdimUpper φ hpos with h | ⟨u, v, hu, hv, h⟩
  · subst φ
    exact ⟨ContinuousMap.Homotopy.refl (ContinuousMap.id E), fun _ _ => rfl⟩
  · subst φ
    exact reflection_pair_homotopy hdimLower u v hu hv

end Pair

section Triangular
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

private theorem gramSchmidt_inner_original (f : Fin 3 → E) (i : Fin 3) :
    inner ℝ (gramSchmidt ℝ f i) (f i) = ‖gramSchmidt ℝ f i‖ ^ 2 := by
  calc
    inner ℝ (gramSchmidt ℝ f i) (f i) =
        inner ℝ (gramSchmidt ℝ f i)
          (gramSchmidt ℝ f i + ∑ j ∈ Finset.Iio i,
            (inner ℝ (gramSchmidt ℝ f j) (f i) / ‖gramSchmidt ℝ f j‖ ^ 2) •
              gramSchmidt ℝ f j) :=
      congrArg (inner ℝ (gramSchmidt ℝ f i)) (gramSchmidt_def'' ℝ f i)
    _ = inner ℝ (gramSchmidt ℝ f i) (gramSchmidt ℝ f i) := by
      rw [inner_add_right, inner_sum]
      have hs : (∑ j ∈ Finset.Iio i,
          inner ℝ (gramSchmidt ℝ f i)
            ((inner ℝ (gramSchmidt ℝ f j) (f i) / ‖gramSchmidt ℝ f j‖ ^ 2) •
              gramSchmidt ℝ f j)) = 0 := by
        apply Finset.sum_eq_zero
        intro j hj
        rw [real_inner_smul_right, gramSchmidt_orthogonal ℝ f
          (ne_of_gt (Finset.mem_Iio.mp hj)), mul_zero]
      rw [hs, add_zero]
    _ = ‖gramSchmidt ℝ f i‖ ^ 2 := real_inner_self_eq_norm_sq _

private theorem gramSchmidtNormed_inner_pos (f : Fin 3 → E)
    (hli : LinearIndependent ℝ f) (i : Fin 3) :
    0 < inner ℝ (gramSchmidtNormed ℝ f i) (f i) := by
  rw [gramSchmidtNormed, real_inner_smul_left, gramSchmidt_inner_original]
  have hn : 0 < ‖gramSchmidt ℝ f i‖ := norm_pos_iff.mpr (gramSchmidt_ne_zero i hli)
  exact mul_pos (inv_pos.mpr hn) (sq_pos_of_pos hn)

variable [FiniteDimensional ℝ E]

private theorem gramSchmidt_basis_det_pos
    (hdim : Module.finrank ℝ E = Fintype.card (Fin 3))
    (f : Fin 3 → E) (hli : LinearIndependent ℝ f) :
    0 < (gramSchmidtOrthonormalBasis hdim f).toBasis.det f := by
  rw [gramSchmidtOrthonormalBasis_det]
  apply Finset.prod_pos
  intro i _
  have hn : gramSchmidtNormed ℝ f i ≠ 0 := by
    intro he
    have hunit := gramSchmidtNormed_unit_length i hli
    rw [he, norm_zero] at hunit
    norm_num at hunit
  rw [gramSchmidtOrthonormalBasis_apply hdim hn]
  exact gramSchmidtNormed_inner_pos f hli i

private theorem positive_triangular_interpolation_det
    (R : Matrix (Fin 3) (Fin 3) ℝ) (hR : R.IsUpperTriangular)
    (hdiag : ∀ i, 0 < R i i) (t : unitInterval) :
    0 < Matrix.det ((1 - (t : ℝ)) • R + (t : ℝ) • (1 : Matrix (Fin 3) (Fin 3) ℝ)) := by
  have htri : ((1 - (t : ℝ)) • R + (t : ℝ) •
      (1 : Matrix (Fin 3) (Fin 3) ℝ)).IsUpperTriangular := by
    intro i j hij
    have hne : i ≠ j := by
      intro he
      subst j
      exact (lt_irrefl i) hij
    simp only [Matrix.add_apply, Matrix.smul_apply, smul_eq_mul,
      hR hij, Matrix.one_apply_ne hne, mul_zero, add_zero]
  rw [Matrix.det_of_isUpperTriangular htri]
  apply Finset.prod_pos
  intro i _
  simp only [Matrix.add_apply, Matrix.smul_apply, Matrix.one_apply_eq, smul_eq_mul, mul_one]
  by_cases ht : (t : ℝ) = 1
  · simp [ht]
  · have ha : 0 < 1 - (t : ℝ) := sub_pos.mpr (lt_of_le_of_ne t.property.2 ht)
    exact add_pos_of_pos_of_nonneg (mul_pos ha (hdiag i)) t.property.1

private theorem positive_triangular_basis_homotopy
    (b g : OrthonormalBasis (Fin 3) ℝ E) (L : E ≃L[ℝ] E)
    (htri : (LinearMap.toMatrix b.toBasis g.toBasis L.toLinearMap).IsUpperTriangular)
    (hdiag : ∀ i, 0 < LinearMap.toMatrix b.toBasis g.toBasis L.toLinearMap i i) :
    ∃ H : (⟨L, L.continuous⟩ : C(E, E)).Homotopy
        (⟨b.equiv g (Equiv.refl (Fin 3)), (b.equiv g (Equiv.refl (Fin 3))).continuous⟩ : C(E, E)),
      ∀ t z, z ≠ 0 → H (t, z) ≠ 0 := by
  classical
  let Q := b.equiv g (Equiv.refl (Fin 3))
  let A (t : unitInterval) : E →L[ℝ] E :=
    (1 - (t : ℝ)) • L.toContinuousLinearMap +
      (t : ℝ) • Q.toContinuousLinearEquiv.toContinuousLinearMap
  have hrepr (y : E) : b.toBasis.repr (Q.symm y) = g.toBasis.repr y := by
    have he : b.toBasis.repr.toLinearMap.comp Q.symm.toLinearMap =
        g.toBasis.repr.toLinearMap := by
      apply g.toBasis.ext
      intro i
      have hQ : Q.symm (g i) = b i := by
        apply Q.injective
        simp [Q]
      change b.toBasis.repr (Q.symm (g i)) = g.toBasis.repr (g i)
      rw [hQ]
      exact (b.toBasis.repr_self i).trans (g.toBasis.repr_self i).symm
    exact DFunLike.congr_fun he y
  let B (t : unitInterval) : E →ₗ[ℝ] E := Q.symm.toLinearMap.comp (A t).toLinearMap
  have hmatrix (t : unitInterval) :
      LinearMap.toMatrix b.toBasis b.toBasis (B t) =
        (1 - (t : ℝ)) • LinearMap.toMatrix b.toBasis g.toBasis L.toLinearMap +
          (t : ℝ) • (1 : Matrix (Fin 3) (Fin 3) ℝ) := by
    ext i j
    rw [LinearMap.toMatrix_apply]
    change b.toBasis.repr (Q.symm (A t (b j))) i = _
    rw [hrepr]
    simp [A, Q, LinearMap.toMatrix_apply, Matrix.one_apply]
  have hBdet (t : unitInterval) : 0 < LinearMap.det (B t) := by
    rw [← LinearMap.det_toMatrix b.toBasis, hmatrix]
    exact positive_triangular_interpolation_det _ htri hdiag t
  have hB (t : unitInterval) : Function.Injective (B t) := by
    apply LinearMap.ker_eq_bot.mp
    by_contra hker
    exact (ne_of_gt (hBdet t)) (LinearMap.det_eq_zero_iff_ker_ne_bot.mpr hker)
  let H : (⟨L, L.continuous⟩ : C(E, E)).Homotopy
      (⟨Q, Q.continuous⟩ : C(E, E)) := {
    toFun := fun p => A p.1 p.2
    continuous_toFun := by
      change Continuous (fun p : unitInterval × E =>
        (1 - (p.1 : ℝ)) • L p.2 + (p.1 : ℝ) • Q p.2)
      fun_prop
    map_zero_left := fun z => by simp [A]
    map_one_left := fun z => by simp [A] }
  refine ⟨H, ?_⟩
  intro t z hz he
  have hzero : B t z = 0 := by
    change Q.symm (A t z) = 0
    change A t z = 0 at he
    rw [he, map_zero]
  exact hz (hB t (hzero.trans (map_zero (B t)).symm))

end Triangular

section PositiveLinear
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E]

theorem positive_linear_homotopy
    (b : OrthonormalBasis (Fin 3) ℝ E) (L : E ≃L[ℝ] E)
    (hpos : 0 < LinearMap.det L.toLinearMap) :
    ∃ H : (⟨L, L.continuous⟩ : C(E, E)).Homotopy (ContinuousMap.id E),
      ∀ t z, z ≠ 0 → H (t, z) ≠ 0 := by
  classical
  have hdim : Module.finrank ℝ E = Fintype.card (Fin 3) :=
    Module.finrank_eq_card_basis b.toBasis
  let f : Module.Basis (Fin 3) ℝ E := b.toBasis.map L.toLinearEquiv
  let g : OrthonormalBasis (Fin 3) ℝ E := gramSchmidtOrthonormalBasis hdim f
  let Q := b.equiv g (Equiv.refl (Fin 3))
  have hcoeff : LinearMap.toMatrix b.toBasis g.toBasis L.toLinearMap = g.toBasis.toMatrix f := by
    ext i j
    simp [LinearMap.toMatrix_apply, Module.Basis.toMatrix_apply, f]
  have htri : (LinearMap.toMatrix b.toBasis g.toBasis L.toLinearMap).IsUpperTriangular := by
    rw [hcoeff]
    exact gramSchmidtOrthonormalBasis_inv_isUpperTriangular hdim f
  have hdiag : ∀ i, 0 < LinearMap.toMatrix b.toBasis g.toBasis L.toLinearMap i i := by
    intro i
    rw [hcoeff]
    rw [Module.Basis.toMatrix_apply, g.coe_toBasis_repr_apply, g.repr_apply_apply]
    have hn : gramSchmidtNormed ℝ f i ≠ 0 := by
      intro he
      have hunit := gramSchmidtNormed_unit_length i f.linearIndependent
      rw [he, norm_zero] at hunit
      norm_num at hunit
    rw [show g i = gramSchmidtNormed ℝ f i from
      gramSchmidtOrthonormalBasis_apply hdim hn]
    exact gramSchmidtNormed_inner_pos f f.linearIndependent i
  have hfOrientation : f.orientation = b.toBasis.orientation :=
    (b.toBasis.orientation_comp_linearEquiv_eq_iff_det_pos L.toLinearEquiv).mpr hpos
  have hgOrientation : g.toBasis.orientation = f.orientation :=
    (g.toBasis.orientation_eq_iff_det_pos f).mpr
      (gramSchmidt_basis_det_pos hdim f f.linearIndependent)
  have hQBasis : b.toBasis.map Q.toLinearEquiv = g.toBasis := by
    ext i
    exact b.equiv_apply_basis g (Equiv.refl (Fin 3)) i
  have hQpos : 0 < LinearMap.det Q.toLinearMap := by
    apply (b.toBasis.orientation_comp_linearEquiv_eq_iff_det_pos Q.toLinearEquiv).mp
    rw [hQBasis]
    exact hgOrientation.trans hfOrientation
  obtain ⟨H, hH⟩ := positive_triangular_basis_homotopy b g L htri hdiag
  have hdimLower : 1 < Module.rank ℝ E :=
    Module.one_lt_rank_of_one_lt_finrank (by rw [hdim]; decide)
  have hdimUpper : Module.finrank ℝ E ≤ 3 := by rw [hdim]; decide
  obtain ⟨K, hK⟩ := positive_isometry_homotopy hdimLower hdimUpper Q hQpos
  refine ⟨H.trans K, ?_⟩
  intro t z hz
  rw [ContinuousMap.Homotopy.trans_apply]
  split_ifs
  · exact hH _ z hz
  · intro he
    have hnorm := congrArg norm he
    rw [hK, norm_zero] at hnorm
    exact hz (norm_eq_zero.mp hnorm)
end PositiveLinear

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
