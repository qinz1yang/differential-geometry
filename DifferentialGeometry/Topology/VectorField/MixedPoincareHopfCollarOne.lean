import DifferentialGeometry.Topology.VectorField.RelativePoincareHopfOne

set_option autoImplicit false
noncomputable section
open Set Bundle Filter Manifold TopologicalSpace
open scoped ContDiff Topology
namespace Poincare.VectorField

theorem mixedPoincareHopf_one_of_collar
    {E H B M : Type}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [Subsingleton E]
    [TopologicalSpace H] [TopologicalSpace B] [ChartedSpace H B]
    [CompactSpace B]
    (J : ModelWithCorners ℝ E H)
    [IsManifold J 1 B]
    [TopologicalSpace M] [ChartedSpace (EuclideanHalfSpace 1) M]
    [IsManifold (𝓡∂ 1) ∞ M] [T2Space M] [CompactSpace M]
    {ε δ : ℝ} [Fact ((0 : ℝ) < ε)] (hδ : 0 < δ) (hδε : δ < ε) :
    let I := 𝓡∂ 1
    let S : Opens (B × Icc (0 : ℝ) ε) :=
      ⟨{q | q.2.val < δ}, isOpen_lt (continuous_subtype_val.comp continuous_snd) continuous_const⟩
    ∀ (Y : Opens M), I.boundary M ⊆ Y →
    ∀ e : Diffeomorph (J.prod (𝓡∂ 1)) I S Y ∞,
      (∀ q : S, 0 < q.val.2.val → I.IsInteriorPoint (e q).val) →
    ∀ V : ∀ x : M, TangentSpace I x,
      ContMDiff I I.tangent ∞ (fun x => (⟨x, V x⟩ : TangentBundle I M)) →
    ∀ (hVf : {x | V x = 0}.Finite)
      (hVi : ∀ x, V x = 0 → HasContinuousIsolatedZero I V x)
      (hVI : ∀ x, V x = 0 → I.IsInteriorPoint x),
    let W := _root_.VectorField.mpullback (J.prod (𝓡∂ 1)) I e (fun y : Y => V y.val)
    (∀ q : S, W q ≠ 0) →
    ∀ (A : Set B),
      (∀ q : S, q.val.2.val = 0 →
        (q.val.1 ∈ A → 0 < Poincare.Manifold.Interval.tangentCoordinateIcc q.val.2 (W q).2) ∧
        (q.val.1 ∉ A → Poincare.Manifold.Interval.tangentCoordinateIcc q.val.2 (W q).2 < 0)) →
    ∀ (K : Type) [Field K],
      interiorIndexSum I V hVf hVi hVI =
        Poincare.Homology.eulerChar K (TopCat.of M) - Poincare.Homology.eulerChar K (TopCat.of A) := by
  intro I S Y hY e hi V hV hVf hVi hVI W hn A hsign K _
  let _ : DiscreteTopology B := DifferentialGeometry.discrete_topology_of_subsingleton_model J
  let _ : Finite B := DifferentialGeometry.finite_of_compact_subsingleton_model J
  let z : B → S := fun p => ⟨(p, ⟨0, ⟨le_rfl, (Fact.out : (0 : ℝ) < ε).le⟩⟩), hδ⟩
  let T : ∀ p : B, TangentSpace J p := fun p => (W (z p)).1
  let b : B → ℝ := fun p =>
    -(Poincare.Manifold.Interval.tangentCoordinateIcc (z p).val.2 (W (z p)).2)
  have hr := relativePoincareHopf_one_of_collar J hδ hδε Y hY e hi V hV hVf hVi hVI hn K
  change interiorIndexSum I V hVf hVi hVI + (∑ᶠ _ : {p | T p = 0 ∧ b p < 0}, (1 : ℤ)) =
    Poincare.Homology.eulerChar K (TopCat.of M) at hr
  have hregion : {p | T p = 0 ∧ b p < 0} = A := by
    ext p
    have hT : T p = 0 := Subsingleton.elim (α := E) _ _
    simp only [mem_ofPred_eq, hT, true_and]
    change -(Poincare.Manifold.Interval.tangentCoordinateIcc (z p).val.2 (W (z p)).2) < 0 ↔ p ∈ A
    by_cases hp : p ∈ A
    · exact iff_of_true (neg_neg_of_pos ((hsign (z p) rfl).1 hp)) hp
    · exact iff_of_false (not_lt_of_ge (neg_nonneg.mpr ((hsign (z p) rfl).2 hp).le)) hp
  rw [hregion] at hr
  have hc : (∑ᶠ _ : A, (1 : ℤ)) = Poincare.Homology.eulerChar K (TopCat.of A) := by
    let _ : Fintype A := Fintype.ofFinite A
    rw [Poincare.Homology.eulerChar_of_finite_totallyDisconnected K]
    simp only [finsum_eq_sum_of_fintype, Finset.sum_const, Finset.card_univ, nsmul_eq_mul,
      mul_one, Nat.card_eq_fintype_card]
  rw [hc] at hr
  omega

end Poincare.VectorField
