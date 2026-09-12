import DifferentialGeometry.Topology.PiecewiseLinear.SimplicialMap

open Set

namespace DifferentialGeometry.Topology.PiecewiseLinear

theorem sum_reindex_of_equiv {α M : Type*} [AddCommMonoid M] {s : Finset α} {n : ℕ}
    (e : Fin n ≃ s) (F : α → M) : ∑ v ∈ s, F v = ∑ i, F (e i) := by
  rw [← Finset.sum_coe_sort s F]
  exact (Fintype.sum_equiv e (fun i => F (e i)) (fun v => F v) fun _ => rfl).symm

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem isPLBall_convexHull_of_affineIndependent [FiniteDimensional ℝ E] {n : ℕ} (s : Finset E)
    (hs : AffineIndependent ℝ ((↑) : s → E)) (hcard : s.card = n + 1) :
    IsPLBall n (convexHull ℝ (s : Set E)) := by
  classical
  let e : Fin (n + 1) ≃ s := (Finset.equivFinOfCardEq hcard).symm
  let p : Fin (n + 1) → E := fun i => (e i : E)
  have hp : ∀ i, p i ∈ s := fun i => (e i).2
  have hpe : ∀ i, e.symm ⟨p i, hp i⟩ = i := fun i => by simp [p]
  let A : (Fin (n + 1) → ℝ) →ₗ[ℝ] E := Fintype.linearCombination ℝ p
  have hA : ∀ x, A x = ∑ i, x i • p i := fun x => by simp [A, Fintype.linearCombination_apply]
  let wx : (Fin (n + 1) → ℝ) → E → ℝ := fun x v => if h : v ∈ s then x (e.symm ⟨v, h⟩) else 0
  have hwx : ∀ x i, wx x (p i) = x i := fun x i => by simp only [wx, dif_pos (hp i), hpe]
  have hwx_sum : ∀ x, ∑ v ∈ s, wx x v = ∑ i, x i := fun x => by
    rw [sum_reindex_of_equiv e]
    exact Finset.sum_congr rfl fun i _ => hwx x i
  have hwx_smul : ∀ x, ∑ v ∈ s, wx x v • v = A x := fun x => by
    rw [sum_reindex_of_equiv e, hA]
    exact Finset.sum_congr rfl fun i _ => by rw [hwx x i]
  let g : E → Fin (n + 1) → ℝ := fun y i => weights s y (p i)
  have hg_mem : ∀ y ∈ convexHull ℝ (s : Set E), g y ∈ stdSimplex ℝ (Fin (n + 1)) := fun y hy =>
    ⟨fun i => weights_nonneg hy (hp i),
      (sum_reindex_of_equiv e (weights s y)).symm.trans (sum_weights hy)⟩
  have hAg : ∀ y ∈ convexHull ℝ (s : Set E), A (g y) = y := fun y hy => by
    rw [hA]
    exact (sum_reindex_of_equiv e fun v => weights s y v • v).symm.trans (sum_weights_smul hy)
  have hmaps : MapsTo A (stdSimplex ℝ (Fin (n + 1))) (convexHull ℝ (s : Set E)) := fun x hx => by
    rw [hA]
    exact (convex_convexHull ℝ _).sum_mem (fun i _ => hx.1 i) hx.2 fun i _ =>
      subset_convexHull ℝ _ (Finset.mem_coe.mpr (hp i))
  have hinj : InjOn A (stdSimplex ℝ (Fin (n + 1))) := fun x hx x' hx' hxx' => by
    have h := eq_on_of_sum_smul_eq hs ((hwx_sum x).trans hx.2) ((hwx_sum x').trans hx'.2)
      (by rw [hwx_smul x, hwx_smul x', hxx'])
    funext i
    rw [← hwx x i, ← hwx x' i]
    exact h (p i) (hp i)
  have hbij : BijOn A (stdSimplex ℝ (Fin (n + 1))) (convexHull ℝ (s : Set E)) :=
    ⟨hmaps, hinj, fun y hy => ⟨g y, hg_mem y hy, hAg y hy⟩⟩
  refine ⟨A, hbij, ?_, ?_⟩
  · exact (isPiecewiseAffineOn_of_affine_of_isHPolytope A.toAffineMap
      (isHPolytope_stdSimplex (Fin (n + 1)))).congr fun _ _ => rfl
  · let q : E → Fin (n + 1) → ℝ := fun v =>
      if h : v ∈ s then Pi.single (e.symm ⟨v, h⟩) (1 : ℝ) else 0
    have hq : ∀ i, q (e i) = Pi.single i 1 := fun i => by
      simp only [q, dif_pos (e i).2, Subtype.coe_eta, Equiv.symm_apply_apply]
    obtain ⟨B, hB⟩ := exists_affineMap_eqOn hs q
    have hgB : EqOn g B (convexHull ℝ (s : Set E)) := by
      intro y hy
      have hw := sum_weights hy
      have h1 : ∑ v ∈ s, weights s y v • v = s.affineCombination ℝ id (weights s y) :=
        (Finset.affineCombination_eq_linear_combination s id (weights s y) hw).symm
      have h2 : ∑ v ∈ s, weights s y v • B v = s.affineCombination ℝ (B ∘ id) (weights s y) :=
        (Finset.affineCombination_eq_linear_combination s (B ∘ id) (weights s y) hw).symm
      have hBy : B y = ∑ v ∈ s, weights s y v • B v := by
        conv_lhs => rw [← sum_weights_smul hy]
        rw [h1, h2, Finset.map_affineCombination s id (weights s y) hw B]
      rw [hBy, Finset.sum_congr rfl fun v hv => by rw [hB v hv],
        sum_reindex_of_equiv e fun v => weights s y v • q v]
      funext j
      simp only [g, p, Finset.sum_apply, Pi.smul_apply, hq, Pi.single_apply, smul_eq_mul, mul_ite,
        mul_one, mul_zero, Finset.sum_ite_eq, Finset.mem_univ, if_true]
    have hinvOn := hbij.invOn_invFunOn
    refine (isPiecewiseAffineOn_of_affine_of_isHPolytope B
      (isHPolytope_convexHull_of_affineIndependent s hs)).congr ?_
    intro y hy
    rw [← hgB hy]
    exact hinj (hbij.surjOn.mapsTo_invFunOn hy) (hg_mem y hy)
      ((hinvOn.2 hy).trans (hAg y hy).symm)

end DifferentialGeometry.Topology.PiecewiseLinear
