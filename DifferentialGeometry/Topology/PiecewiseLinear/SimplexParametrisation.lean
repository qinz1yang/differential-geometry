import DifferentialGeometry.Topology.PiecewiseLinear.Orientation
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.Background
/-!
# Affine parametrisations of 3-simplices and flattened bipyramids

Steps A3 and A4 of route A' in
`docs/geometrization/handoffs/20261003-survey-r05-orientation-bridge.md`.

`simplexParam r hS : ThreeSpace →ᵃ[ℝ] E` sends `0, e₀, e₁, e₂` to the vertices of a 3-simplex `S`
listed in the order `r`. It is injective when `S` is a face of a complex and maps the open standard
simplex `openStdSimplex3` into `openSimplex S`.

`exists_bipyramid` handles two 3-simplices `S ≠ S'` on a common 2-face `T`. On a convex open box
`W` it builds an injective continuous map `Φ : ThreeSpace → E` into `K.space`, folding the plane
`y 2 = 0` onto `T`, equal to `simplexParam ∘ A` above that plane and to `simplexParam ∘ A'` below
it, for affine automorphisms `A`, `A'` whose determinant signs `detSign` cancel the boundary
coefficients of `S` and `S'` along `T`, as in `affineSimplexOrientationSign_pair_cancel`.
-/

set_option autoImplicit false

open Set Filter Topology

namespace DifferentialGeometry.Topology.PiecewiseLinear

open DifferentialGeometry.PDE.RicciFlow.Surgery.Topology (ThreeSpace)

variable {E : Type*}

section Param

variable [AddCommGroup E] [Module ℝ E]

private noncomputable def tetraLinear (q : Fin 4 → E) : ThreeSpace →ₗ[ℝ] E :=
  ∑ i : Fin 3, (EuclideanSpace.proj i : ThreeSpace →L[ℝ] ℝ).toLinearMap.smulRight
    (q i.succ - q 0)

noncomputable def tetraParam (q : Fin 4 → E) : ThreeSpace →ᵃ[ℝ] E :=
  (tetraLinear q).toAffineMap + AffineMap.const ℝ ThreeSpace (q 0)

theorem tetraParam_apply (q : Fin 4 → E) (y : ThreeSpace) :
    tetraParam q y =
      q 0 + y 0 • (q 1 - q 0) + y 1 • (q 2 - q 0) + y 2 • (q 3 - q 0) := by
  simp [tetraParam, tetraLinear, Fin.sum_univ_three]
  abel

noncomputable def stdWeights (y : ThreeSpace) : Fin 4 → ℝ :=
  ![1 - y 0 - y 1 - y 2, y 0, y 1, y 2]

omit [AddCommGroup E] [Module ℝ E] in
theorem sum_stdWeights (y : ThreeSpace) : ∑ i, stdWeights y i = 1 := by
  simp [stdWeights, Fin.sum_univ_four]
  ring

theorem tetraParam_eq_sum (q : Fin 4 → E) (y : ThreeSpace) :
    tetraParam q y = ∑ i, stdWeights y i • q i := by
  rw [tetraParam_apply]
  simp [stdWeights, Fin.sum_univ_four]
  module

theorem tetraParam_injective {q : Fin 4 → E} (hq : AffineIndependent ℝ q) :
    Function.Injective (tetraParam q) := by
  intro y z hyz
  rw [tetraParam_eq_sum, tetraParam_eq_sum] at hyz
  have key := (hq.affineCombination_eq_iff_eq (s := Finset.univ) (sum_stdWeights y)
    (sum_stdWeights z)).mp (by
      rw [Finset.affineCombination_eq_linear_combination _ _ _ (sum_stdWeights y),
        Finset.affineCombination_eq_linear_combination _ _ _ (sum_stdWeights z)]
      exact hyz)
  ext i
  fin_cases i
  · simpa [stdWeights] using key 1 (Finset.mem_univ _)
  · simpa [stdWeights] using key 2 (Finset.mem_univ _)
  · simpa [stdWeights] using key 3 (Finset.mem_univ _)

theorem tetraParam_mem_convexHull {S : Finset E} {q : Fin 4 → E} (hq : ∀ i, q i ∈ S)
    {y : ThreeSpace} (h0 : 0 ≤ y 0) (h1 : 0 ≤ y 1) (h2 : 0 ≤ y 2)
    (hs : y 0 + y 1 + y 2 ≤ 1) : tetraParam q y ∈ convexHull ℝ (S : Set E) := by
  rw [tetraParam_eq_sum]
  refine (convex_convexHull ℝ (S : Set E)).sum_mem (fun i _ => ?_) (sum_stdWeights y)
    (fun i _ => subset_convexHull ℝ (S : Set E) (Finset.mem_coe.mpr (hq i)))
  fin_cases i <;> simp [stdWeights] <;> linarith

noncomputable def simplexParam (r : LinearOrder E) {S : Finset E} (hS : S.card = 4) :
    ThreeSpace →ᵃ[ℝ] E :=
  tetraParam fun i => S.orderEmbOfFin hS i

theorem affineIndependent_orderEmbOfFin (r : LinearOrder E) {S : Finset E} (hS : S.card = 4)
    (hindep : AffineIndependent ℝ ((↑) : S → E)) :
    AffineIndependent ℝ fun i => S.orderEmbOfFin hS i := by
  have h := hindep.comp_embedding (S.orderIsoOfFin hS).toEquiv.toEmbedding
  convert h using 1
  funext i
  simp

theorem simplexParam_injective (r : LinearOrder E) {K : Geometry.SimplicialComplex ℝ E}
    {S : Finset E} (hSK : S ∈ K.faces) (hS : S.card = 4) :
    Function.Injective (simplexParam r hS) :=
  tetraParam_injective (affineIndependent_orderEmbOfFin r hS (K.indep hSK))

end Param

def openStdSimplex3 : Set ThreeSpace :=
  {y | 0 < y 0 ∧ 0 < y 1 ∧ 0 < y 2 ∧ y 0 + y 1 + y 2 < 1}

noncomputable def barycentre3 : ThreeSpace :=
  WithLp.toLp 2 ![1 / 4, 1 / 4, 1 / 4]

theorem barycentre3_mem_openStdSimplex3 : barycentre3 ∈ openStdSimplex3 := by
  norm_num [barycentre3, openStdSimplex3]

theorem isOpen_openStdSimplex3 : IsOpen openStdSimplex3 := by
  have h0 : Continuous fun y : ThreeSpace => y 0 := by fun_prop
  have h1 : Continuous fun y : ThreeSpace => y 1 := by fun_prop
  have h2 : Continuous fun y : ThreeSpace => y 2 := by fun_prop
  exact (isOpen_lt continuous_const h0).inter ((isOpen_lt continuous_const h1).inter
    ((isOpen_lt continuous_const h2).inter (isOpen_lt ((h0.add h1).add h2) continuous_const)))

theorem convex_openStdSimplex3 : Convex ℝ openStdSimplex3 := by
  intro y hy z hz a b ha hb hab
  obtain ⟨hy0, hy1, hy2, hys⟩ := hy
  obtain ⟨hz0, hz1, hz2, hzs⟩ := hz
  simp only [openStdSimplex3, Set.mem_ofPred_eq, PiLp.add_apply, PiLp.smul_apply, smul_eq_mul]
  rcases ha.eq_or_lt with rfl | ha'
  · simp only [zero_add] at hab
    subst hab
    simp only [zero_mul, zero_add, one_mul]
    exact ⟨hz0, hz1, hz2, hzs⟩
  · refine ⟨by positivity, by positivity, by positivity, ?_⟩
    nlinarith

theorem isPreconnected_openStdSimplex3 : IsPreconnected openStdSimplex3 :=
  convex_openStdSimplex3.isPreconnected

theorem simplexParam_mapsTo [AddCommGroup E] [Module ℝ E] (r : LinearOrder E) {S : Finset E}
    (hS : S.card = 4) : MapsTo (simplexParam r hS) openStdSimplex3 (openSimplex S) := by
  intro y hy
  obtain ⟨hy0, hy1, hy2, hys⟩ := hy
  have h : simplexParam r hS y ∈ openSimplex (Finset.univ.image (S.orderEmbOfFin hS)) := by
    refine (mem_openSimplex_image_iff (S.orderEmbOfFin hS).injective.injOn).mpr
      ⟨stdWeights y, ?_, sum_stdWeights y, (tetraParam_eq_sum _ y).symm⟩
    intro i _
    fin_cases i <;> simp [stdWeights] <;> linarith
  rwa [Finset.image_orderEmbOfFin_univ S hS] at h

theorem simplexParam_mapsTo_space [AddCommGroup E] [Module ℝ E] (r : LinearOrder E)
    {K : Geometry.SimplicialComplex ℝ E} {S : Finset E} (hSK : S ∈ K.faces) (hS : S.card = 4) :
    MapsTo (simplexParam r hS) openStdSimplex3 K.space := fun _ hy =>
  K.convexHull_subset_space hSK (openSimplex_subset_convexHull S (simplexParam_mapsTo r hS hy))

theorem continuous_simplexParam [NormedAddCommGroup E] [NormedSpace ℝ E] (r : LinearOrder E)
    {S : Finset E} (hS : S.card = 4) : Continuous (simplexParam r hS) :=
  (simplexParam r hS).continuous_of_finiteDimensional

noncomputable def detSign (A : ThreeSpace ≃ᵃ[ℝ] ThreeSpace) : ℤ :=
  if 0 < LinearMap.det (A.linear : ThreeSpace →ₗ[ℝ] ThreeSpace) then 1 else -1

section StandardMaps

private noncomputable def stdBasis3 : Module.Basis (Fin 3) ℝ ThreeSpace :=
  (EuclideanSpace.basisFun (Fin 3) ℝ).toBasis

private noncomputable def affineEquivOfMatrix (M : Matrix (Fin 3) (Fin 3) ℝ)
    (hM : IsUnit M.det) (c : ThreeSpace) : ThreeSpace ≃ᵃ[ℝ] ThreeSpace :=
  AffineEquiv.mk' (fun y => c + M.toLinearEquiv stdBasis3 hM y) (M.toLinearEquiv stdBasis3 hM) 0
    (by intro y; simp [add_comm])

private theorem affineEquivOfMatrix_apply (M : Matrix (Fin 3) (Fin 3) ℝ) (hM : IsUnit M.det)
    (c y : ThreeSpace) (i : Fin 3) :
    affineEquivOfMatrix M hM c y i = c i + ∑ j, M i j * y j := by
  change (c + M.toLinearEquiv stdBasis3 hM y) i = _
  simp [Pi.single_apply, mul_ite, Finset.sum_ite_eq, stdBasis3, Matrix.toLin_apply,
    Matrix.mulVec, dotProduct]

private theorem det_affineEquivOfMatrix (M : Matrix (Fin 3) (Fin 3) ℝ) (hM : IsUnit M.det)
    (c : ThreeSpace) :
    LinearMap.det ((affineEquivOfMatrix M hM c).linear : ThreeSpace →ₗ[ℝ] ThreeSpace) =
      M.det :=
  LinearMap.det_toLin stdBasis3 M

private theorem det_linear_trans (A B : ThreeSpace ≃ᵃ[ℝ] ThreeSpace) :
    LinearMap.det ((A.trans B).linear : ThreeSpace →ₗ[ℝ] ThreeSpace) =
      LinearMap.det (B.linear : ThreeSpace →ₗ[ℝ] ThreeSpace) *
        LinearMap.det (A.linear : ThreeSpace →ₗ[ℝ] ThreeSpace) := by
  change LinearMap.det ((A.linear.trans B.linear : ThreeSpace ≃ₗ[ℝ] ThreeSpace) :
    ThreeSpace →ₗ[ℝ] ThreeSpace) = _
  rw [LinearEquiv.coe_trans, LinearMap.det_comp]

private noncomputable def stdPermMatrix (p : Fin 4) : Matrix (Fin 3) (Fin 3) ℝ :=
  ![!![-1, -1, -1; 1, 0, 0; 0, 1, 0], !![0, 0, 1; 1, 0, 0; 0, 1, 0],
    !![1, 0, 0; 0, 0, 1; 0, 1, 0], 1] p

private theorem det_stdPermMatrix (p : Fin 4) : (stdPermMatrix p).det = -(-1) ^ (p : ℕ) := by
  fin_cases p <;> norm_num [stdPermMatrix, Matrix.det_fin_three]

private theorem isUnit_det_stdPermMatrix (p : Fin 4) : IsUnit (stdPermMatrix p).det := by
  rw [det_stdPermMatrix]
  exact isUnit_iff_ne_zero.mpr (by simp)

private noncomputable def stdPermOffset (p : Fin 4) : ThreeSpace :=
  ![WithLp.toLp 2 ![1, 0, 0], 0, 0, 0] p

private noncomputable def stdPerm (p : Fin 4) : ThreeSpace ≃ᵃ[ℝ] ThreeSpace :=
  affineEquivOfMatrix (stdPermMatrix p) (isUnit_det_stdPermMatrix p) (stdPermOffset p)

private theorem tetraParam_stdPerm [AddCommGroup E] [Module ℝ E] (q : Fin 4 → E) (p : Fin 4)
    (y : ThreeSpace) :
    tetraParam q (stdPerm p y) =
      q (p.succAbove 0) + y 0 • (q (p.succAbove 1) - q (p.succAbove 0)) +
        y 1 • (q (p.succAbove 2) - q (p.succAbove 0)) + y 2 • (q p - q (p.succAbove 0)) := by
  rw [tetraParam_apply]
  simp only [stdPerm, affineEquivOfMatrix_apply, Fin.sum_univ_three]
  fin_cases p <;>
    simp [stdPermMatrix, stdPermOffset, Fin.succAbove, Fin.lt_def] <;> module

private theorem detSign_stdPerm_mul (p : Fin 4) :
    detSign (stdPerm p) * (-1) ^ (p : ℕ) = -1 := by
  rw [detSign, stdPerm, det_affineEquivOfMatrix, det_stdPermMatrix]
  fin_cases p <;> norm_num

private theorem stdPerm_barycentre3 (p : Fin 4) : stdPerm p barycentre3 = barycentre3 := by
  ext i
  fin_cases p <;> fin_cases i <;>
    norm_num [stdPerm, affineEquivOfMatrix_apply, Fin.sum_univ_three, stdPermMatrix,
      stdPermOffset, barycentre3]

private noncomputable def stdRefl : ThreeSpace ≃ᵃ[ℝ] ThreeSpace :=
  affineEquivOfMatrix !![1, 0, 0; 0, 1, 0; 0, 0, -1]
    (isUnit_iff_ne_zero.mpr (by norm_num [Matrix.det_fin_three])) 0

private theorem stdRefl_apply (y : ThreeSpace) :
    stdRefl y = WithLp.toLp 2 ![y 0, y 1, -y 2] := by
  ext i
  fin_cases i <;> simp [stdRefl, affineEquivOfMatrix_apply, Fin.sum_univ_three]

private theorem detSign_stdRefl_trans_mul (p : Fin 4) :
    detSign (stdRefl.trans (stdPerm p)) * (-1) ^ (p : ℕ) = 1 := by
  rw [detSign, det_linear_trans, stdPerm, stdRefl, det_affineEquivOfMatrix,
    det_affineEquivOfMatrix, det_stdPermMatrix]
  fin_cases p <;> norm_num [Matrix.det_fin_three]

private theorem stdRefl_trans_stdPerm_apply (p : Fin 4) :
    stdRefl.trans (stdPerm p) (WithLp.toLp 2 ![1 / 4, 1 / 4, -(1 / 4)]) = barycentre3 := by
  rw [AffineEquiv.trans_apply, stdRefl_apply, ← stdPerm_barycentre3 p]
  norm_num [barycentre3]

end StandardMaps

section Position

theorem orderEmbOfFin_position (r : LinearOrder E) {S : Finset E} {N : ℕ} (hS : S.card = N)
    {a : E} (ha : a ∈ S) : S.orderEmbOfFin hS ((S.orderIsoOfFin hS).symm ⟨a, ha⟩) = a := by
  rw [← Finset.coe_orderIsoOfFin_apply, OrderIso.apply_symm_apply]

theorem orderEmbOfFin_succAbove_position (r : LinearOrder E) {S T : Finset E} {n : ℕ}
    (hS : S.card = n + 1) (hT : T.card = n) {a : E} (ha : a ∈ S) (herase : S.erase a = T)
    (i : Fin n) :
    S.orderEmbOfFin hS (((S.orderIsoOfFin hS).symm ⟨a, ha⟩).succAbove i) =
      T.orderEmbOfFin hT i := by
  set p := (S.orderIsoOfFin hS).symm ⟨a, ha⟩
  have hmem (j : Fin n) : S.orderEmbOfFin hS (p.succAbove j) ∈ T := by
    rw [← herase, Finset.mem_erase]
    refine ⟨?_, Finset.orderEmbOfFin_mem S hS _⟩
    intro heq
    rw [← orderEmbOfFin_position r hS ha] at heq
    exact Fin.succAbove_ne p j ((S.orderEmbOfFin hS).injective heq)
  have h := Finset.orderEmbOfFin_unique hT hmem
    ((S.orderEmbOfFin hS).strictMono.comp (Fin.strictMono_succAbove p))
  exact congrFun h i

theorem position_eq_incidenceIndex (r : LinearOrder E) {S : Finset E} {N : ℕ}
    (hS : S.card = N) {a : E} (ha : a ∈ S) :
    (((S.orderIsoOfFin hS).symm ⟨a, ha⟩ : Fin N) : ℕ) = incidenceIndex r S a := by
  subst hS
  exact orderIsoOfFin_symm_eq_incidenceIndex r S ha

theorem simplexBoundaryCoefficient_eq_neg_one_pow_position (r : LinearOrder E)
    {S T : Finset E} {N : ℕ} (hS : S.card = N) {a : E} (ha : a ∈ S)
    (herase : S.erase a = T) :
    simplexBoundaryCoefficient r S T =
      (-1) ^ (((S.orderIsoOfFin hS).symm ⟨a, ha⟩ : Fin N) : ℕ) := by
  rw [← herase, simplexBoundaryCoefficient_erase r ha, position_eq_incidenceIndex r hS ha,
    incidenceSign]

private theorem simplexParam_stdPerm_position [AddCommGroup E] [Module ℝ E] (r : LinearOrder E)
    {S T : Finset E} (hS : S.card = 4) (hT : T.card = 3) {a : E} (ha : a ∈ S)
    (herase : S.erase a = T) (y : ThreeSpace) :
    simplexParam r hS (stdPerm ((S.orderIsoOfFin hS).symm ⟨a, ha⟩) y) =
      T.orderEmbOfFin hT 0 + y 0 • (T.orderEmbOfFin hT 1 - T.orderEmbOfFin hT 0) +
        y 1 • (T.orderEmbOfFin hT 2 - T.orderEmbOfFin hT 0) +
          y 2 • (a - T.orderEmbOfFin hT 0) := by
  rw [simplexParam, tetraParam_stdPerm]
  simp only [orderEmbOfFin_succAbove_position r hS hT ha herase, orderEmbOfFin_position r hS ha]

end Position

theorem exists_bipyramid [NormedAddCommGroup E] [NormedSpace ℝ E] (r : LinearOrder E)
    {K : Geometry.SimplicialComplex ℝ E} [Finite K.faces] {T S S' : Finset E}
    (hT : T ∈ K.faces) (hTc : T.card = 3) (hS : S ∈ faceCofaces K T 4)
    (hS' : S' ∈ faceCofaces K T 4) (hne : S ≠ S') :
    ∃ (W : Set ThreeSpace) (Φ : ThreeSpace → E) (A A' : ThreeSpace ≃ᵃ[ℝ] ThreeSpace)
      (y y' : ThreeSpace), IsOpen W ∧ IsPreconnected W ∧ ContinuousOn Φ W ∧ InjOn Φ W ∧
      MapsTo Φ W K.space ∧ y ∈ W ∧ y' ∈ W ∧ A y ∈ openStdSimplex3 ∧
      A' y' ∈ openStdSimplex3 ∧
      Φ =ᶠ[𝓝 y] simplexParam r ((mem_faceCofaces K).mp hS).2.1 ∘ A ∧
      Φ =ᶠ[𝓝 y'] simplexParam r ((mem_faceCofaces K).mp hS').2.1 ∘ A' ∧
      detSign A * simplexBoundaryCoefficient r S T +
        detSign A' * simplexBoundaryCoefficient r S' T = 0 := by
  obtain ⟨hSK, hS4, hTS⟩ := (mem_faceCofaces K).mp hS
  obtain ⟨hS'K, hS'4, hTS'⟩ := (mem_faceCofaces K).mp hS'
  obtain ⟨a, haT, haS⟩ := Finset.exists_eq_insert_iff.mpr ⟨hTS, by omega⟩
  obtain ⟨b, hbT, hbS'⟩ := Finset.exists_eq_insert_iff.mpr ⟨hTS', by omega⟩
  have ha : a ∈ S := haS ▸ Finset.mem_insert_self a T
  have hb : b ∈ S' := hbS' ▸ Finset.mem_insert_self b T
  have hab : a ≠ b := fun h => hne (haS.symm.trans (h ▸ hbS'))
  have haErase : S.erase a = T := haS ▸ Finset.erase_insert haT
  have hbErase : S'.erase b = T := hbS' ▸ Finset.erase_insert hbT
  have hup := simplexParam_stdPerm_position r hS4 hTc ha haErase
  have hdown := simplexParam_stdPerm_position r hS'4 hTc hb hbErase
  have hcS := simplexBoundaryCoefficient_eq_neg_one_pow_position r hS4 ha haErase
  have hcS' := simplexBoundaryCoefficient_eq_neg_one_pow_position r hS'4 hb hbErase
  set t := T.orderEmbOfFin hTc with ht
  set p := (S.orderIsoOfFin hS4).symm ⟨a, ha⟩ with hp
  set p' := (S'.orderIsoOfFin hS'4).symm ⟨b, hb⟩ with hp'
  set Φ : ThreeSpace → E := fun y => t 0 + y 0 • (t 1 - t 0) + y 1 • (t 2 - t 0) +
    max (y 2) 0 • (a - t 0) + max (-y 2) 0 • (b - t 0) with hΦ
  have hΦup (y : ThreeSpace) (hy : 0 ≤ y 2) : Φ y = simplexParam r hS4 (stdPerm p y) := by
    rw [hup]
    simp only [hΦ, max_eq_left hy, max_eq_right (neg_nonpos.mpr hy), zero_smul, add_zero]
  have hΦdown (y : ThreeSpace) (hy : y 2 ≤ 0) :
      Φ y = simplexParam r hS'4 ((stdRefl.trans (stdPerm p')) y) := by
    rw [AffineEquiv.trans_apply, hdown, stdRefl_apply]
    simp only [hΦ, max_eq_right hy, max_eq_left (neg_nonneg.mpr hy), zero_smul, add_zero]
    simp
  have hcont : Continuous Φ := by
    simp only [hΦ]
    fun_prop
  let x := T.centroid ℝ id
  have hx : x ∈ openSimplex T := centroid_mem_openSimplex_of_mem_faces K T hT
  obtain ⟨ℓ, hℓT, hℓa, hℓb⟩ := exists_linearMap_separating_cofaces K hx haT hbT hab
    (by convert hSK; ext z; simp [← haS]) (by convert hS'K; ext z; simp [← hbS'])
  have hℓt (i : Fin 3) : ℓ (t i) = ℓ x := by
    have hy : t i ∈ affineSpan ℝ (T : Set E) :=
      mem_affineSpan ℝ (Finset.orderEmbOfFin_mem T hTc i)
    have hxspan : x ∈ affineSpan ℝ (T : Set E) :=
      convexHull_subset_affineSpan (T : Set E) (openSimplex_subset_convexHull T hx)
    have h0 : ℓ (t i - x) = 0 := by
      apply hℓT
      simpa only [direction_affineSpan, vsub_eq_sub] using
        AffineSubspace.vsub_mem_direction hy hxspan
    rw [map_sub] at h0
    linarith
  have hℓΦ (y : ThreeSpace) :
      ℓ (Φ y) = ℓ x + max (y 2) 0 + max (-y 2) 0 * ℓ (b - x) := by
    rw [map_sub] at hℓa ⊢
    simp only [hΦ, map_add, map_smul, map_sub, hℓt, smul_eq_mul]
    linear_combination max (y 2) 0 * hℓa
  have hinj : Function.Injective Φ := by
    intro y z hyz
    have h2 : y 2 = z 2 := by
      have h := congrArg ℓ hyz
      rw [hℓΦ, hℓΦ] at h
      rcases le_total 0 (y 2) with hy | hy <;> rcases le_total 0 (z 2) with hz | hz
      · rw [max_eq_left hy, max_eq_left hz, max_eq_right (neg_nonpos.mpr hy),
          max_eq_right (neg_nonpos.mpr hz)] at h
        linarith
      · rw [max_eq_left hy, max_eq_right hz, max_eq_right (neg_nonpos.mpr hy),
          max_eq_left (neg_nonneg.mpr hz)] at h
        have hzb := mul_nonneg_of_nonpos_of_nonpos hz hℓb.le
        have hy0 : y 2 = 0 := by linarith
        have hz0 : z 2 * ℓ (b - x) = 0 := by linarith
        rcases mul_eq_zero.mp hz0 with h' | h'
        · rw [hy0, h']
        · linarith
      · rw [max_eq_right hy, max_eq_left hz, max_eq_left (neg_nonneg.mpr hy),
          max_eq_right (neg_nonpos.mpr hz)] at h
        have hyb := mul_nonneg_of_nonpos_of_nonpos hy hℓb.le
        have hz0 : z 2 = 0 := by linarith
        have hy0 : y 2 * ℓ (b - x) = 0 := by linarith
        rcases mul_eq_zero.mp hy0 with h' | h'
        · rw [hz0, h']
        · linarith
      · rw [max_eq_right hy, max_eq_right hz, max_eq_left (neg_nonneg.mpr hy),
          max_eq_left (neg_nonneg.mpr hz)] at h
        have h' : (z 2 - y 2) * ℓ (b - x) = 0 := by linarith
        rcases mul_eq_zero.mp h' with h'' | h''
        · linarith
        · linarith
    rcases le_total 0 (y 2) with hy | hy
    · rw [hΦup y hy, hΦup z (h2 ▸ hy)] at hyz
      exact (stdPerm p).injective (simplexParam_injective r hSK hS4 hyz)
    · rw [hΦdown y hy, hΦdown z (h2 ▸ hy)] at hyz
      exact (stdRefl.trans (stdPerm p')).injective (simplexParam_injective r hS'K hS'4 hyz)
  let W : Set ThreeSpace :=
    (EuclideanSpace.proj (0 : Fin 3) : ThreeSpace →L[ℝ] ℝ) ⁻¹' Ioo 0 (1 / 3) ∩
      ((EuclideanSpace.proj (1 : Fin 3) : ThreeSpace →L[ℝ] ℝ) ⁻¹' Ioo 0 (1 / 3) ∩
        (EuclideanSpace.proj (2 : Fin 3) : ThreeSpace →L[ℝ] ℝ) ⁻¹' Ioo (-(1 / 3)) (1 / 3))
  have hWmem (y : ThreeSpace) : y ∈ W ↔
      (0 < y 0 ∧ y 0 < 1 / 3) ∧ (0 < y 1 ∧ y 1 < 1 / 3) ∧ (-(1 / 3) < y 2 ∧ y 2 < 1 / 3) := by
    simp [W]
  have hWopen : IsOpen W :=
    (isOpen_Ioo.preimage (EuclideanSpace.proj _).continuous).inter
      ((isOpen_Ioo.preimage (EuclideanSpace.proj _).continuous).inter
        (isOpen_Ioo.preimage (EuclideanSpace.proj _).continuous))
  have hWconvex : Convex ℝ W :=
    ((convex_Ioo _ _).linear_preimage
      (EuclideanSpace.proj _ : ThreeSpace →L[ℝ] ℝ).toLinearMap).inter
      (((convex_Ioo _ _).linear_preimage
        (EuclideanSpace.proj _ : ThreeSpace →L[ℝ] ℝ).toLinearMap).inter
        ((convex_Ioo _ _).linear_preimage
          (EuclideanSpace.proj _ : ThreeSpace →L[ℝ] ℝ).toLinearMap))
  have hmaps : MapsTo Φ W K.space := by
    intro y hy
    obtain ⟨⟨hy0, hy0'⟩, ⟨hy1, hy1'⟩, ⟨hy2, hy2'⟩⟩ := (hWmem y).mp hy
    have htS (i : Fin 3) : t i ∈ T := Finset.orderEmbOfFin_mem T hTc i
    rcases le_total 0 (y 2) with h | h
    · have heq : Φ y = tetraParam ![t 0, t 1, t 2, a] y := by
        rw [tetraParam_apply]
        simp [hΦ, max_eq_left h, max_eq_right (neg_nonpos.mpr h)]
      rw [heq]
      refine K.convexHull_subset_space hSK
        (tetraParam_mem_convexHull (fun i => ?_) hy0.le hy1.le h (by linarith))
      fin_cases i
      · exact hTS (htS 0)
      · exact hTS (htS 1)
      · exact hTS (htS 2)
      · exact ha
    · have heq : Φ y = tetraParam ![t 0, t 1, t 2, b] (stdRefl y) := by
        rw [tetraParam_apply, stdRefl_apply]
        simp [hΦ, max_eq_right h, max_eq_left (neg_nonneg.mpr h)]
      rw [heq]
      refine K.convexHull_subset_space hS'K
        (tetraParam_mem_convexHull (fun i => ?_) ?_ ?_ ?_ ?_)
      · fin_cases i
        · exact hTS' (htS 0)
        · exact hTS' (htS 1)
        · exact hTS' (htS 2)
        · exact hb
      all_goals simp [stdRefl_apply]
      all_goals linarith
  have hUp : IsOpen {z : ThreeSpace | 0 < z 2} := isOpen_lt continuous_const (by fun_prop)
  have hUdown : IsOpen {z : ThreeSpace | z 2 < 0} := isOpen_lt (by fun_prop) continuous_const
  refine ⟨W, Φ, stdPerm p, stdRefl.trans (stdPerm p'), barycentre3,
    WithLp.toLp 2 ![1 / 4, 1 / 4, -(1 / 4)], hWopen, hWconvex.isPreconnected,
    hcont.continuousOn, hinj.injOn, hmaps, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hWmem]
    norm_num [barycentre3]
  · rw [hWmem]
    norm_num
  · rw [stdPerm_barycentre3]
    exact barycentre3_mem_openStdSimplex3
  · rw [stdRefl_trans_stdPerm_apply]
    exact barycentre3_mem_openStdSimplex3
  · refine Filter.eventuallyEq_of_mem (hUp.mem_nhds ?_) fun z hz => hΦup z (le_of_lt hz)
    norm_num [barycentre3]
  · refine Filter.eventuallyEq_of_mem (hUdown.mem_nhds ?_) fun z hz => hΦdown z (le_of_lt hz)
    norm_num
  · rw [hcS, hcS']
    have h1 := detSign_stdPerm_mul p
    have h2 := detSign_stdRefl_trans_mul p'
    linarith

end DifferentialGeometry.Topology.PiecewiseLinear
