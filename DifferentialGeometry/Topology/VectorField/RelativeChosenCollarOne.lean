import DifferentialGeometry.Topology.VectorField.CollarRestriction
import DifferentialGeometry.Topology.VectorField.RelativePoincareHopfOne

set_option autoImplicit false
noncomputable section
open Set Bundle Filter Manifold TopologicalSpace
open scoped ContDiff Topology
namespace DifferentialGeometry.VectorField

theorem relativePoincareHopf_one_of_chosen_collar
    {E H B : Type*} {M : Type}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [Subsingleton E]
    [TopologicalSpace H] [TopologicalSpace B] [ChartedSpace H B] [CompactSpace B]
    (J : ModelWithCorners ℝ E H) [IsManifold J 1 B]
    [TopologicalSpace M] [ChartedSpace (EuclideanHalfSpace 1) M]
    [IsManifold (𝓡∂ 1) ∞ M] [T2Space M] [CompactSpace M]
    {ε : ℝ} [Fact ((0 : ℝ) < ε)] :
    let I := 𝓡∂ 1
    ∀ (S : Opens (B × Icc (0 : ℝ) ε))
      (hS : ∀ p : B, (p, ⟨0, ⟨le_rfl, (Fact.out : (0 : ℝ) < ε).le⟩⟩) ∈ S),
    ∀ (Y : Opens M), I.boundary M ⊆ Y →
    ∀ e : Diffeomorph (J.prod (𝓡∂ 1)) I S Y ∞,
      (∀ q : S, 0 < q.val.2.val → I.IsInteriorPoint (e q).val) →
      (∀ q : S, q.val.2.val = 0 → I.IsBoundaryPoint (e q).val) →
    ∀ V : ∀ x : M, TangentSpace I x,
      ContMDiff I I.tangent ∞ (fun x => (⟨x, V x⟩ : TangentBundle I M)) →
    ∀ (hVf : {x | V x = 0}.Finite)
      (hVi : ∀ x, V x = 0 → HasContinuousIsolatedZero I V x)
      (hVI : ∀ x, V x = 0 → I.IsInteriorPoint x),
    let W := _root_.VectorField.mpullback (J.prod (𝓡∂ 1)) I e (fun y : Y => V y.val)
    let z : B → S := fun p => ⟨(p, ⟨0, ⟨le_rfl, (Fact.out : (0 : ℝ) < ε).le⟩⟩), hS p⟩
    let T : ∀ p : B, TangentSpace J p := fun p => (W (z p)).1
    let b : B → ℝ := fun p =>
      -(DifferentialGeometry.Manifold.Interval.tangentCoordinateIcc (z p).val.2 (W (z p)).2)
    ∀ (K : Type) [Field K],
      interiorIndexSum I V hVf hVi hVI + (∑ᶠ _ : {p | T p = 0 ∧ b p < 0}, (1 : ℤ)) =
        DifferentialGeometry.Homology.eulerChar K (TopCat.of M) := by
  intro I S hS Y hY e hi hz V hV hVf hVi hVI W z T b K _
  have hn (q : S) (hq : q.val.2.val = 0) : V (e q).val ≠ 0 := by
    intro hv
    exact (I.isBoundaryPoint_iff_not_isInteriorPoint (e q).val).mp (hz q hq) (hVI _ hv)
  obtain ⟨δ, hδ, hδε, hUS, Y', e', he', hp, hn'⟩ :=
    exists_nonvanishing_collar_restriction S Y e hS V hV hn
  let U : Opens (B × Icc (0 : ℝ) ε) :=
    ⟨{q | q.2.val < δ}, isOpen_lt (continuous_subtype_val.comp continuous_snd) continuous_const⟩
  have hi' (q : U) (hq : 0 < q.val.2.val) : I.IsInteriorPoint (e' q).val := by
    rw [he' q]
    exact hi _ hq
  have hY' : I.boundary M ⊆ Y' := by
    intro x hx
    let y : Y := ⟨x, hY hx⟩
    let q := e.symm y
    have heq : (e q).val = x := congrArg Subtype.val (e.apply_symm_apply y)
    have hqzero : q.val.2.val = 0 := by
      apply le_antisymm _ q.val.2.property.1
      by_contra h
      have hh := hi q (lt_of_not_ge h)
      rw [heq] at hh
      exact (I.isBoundaryPoint_iff_not_isInteriorPoint x).mp hx hh
    let q' : U := ⟨q.val, by change q.val.2.val < δ; rw [hqzero]; exact hδ⟩
    have heq' : (e' q').val = x := (he' q').trans heq
    exact heq' ▸ (e' q').property
  let W' := _root_.VectorField.mpullback (J.prod (𝓡∂ 1)) I e' (fun y : Y' => V y.val)
  let z' : B → U := fun p => ⟨(p, ⟨0, ⟨le_rfl, (Fact.out : (0 : ℝ) < ε).le⟩⟩), hδ⟩
  let T' : ∀ p : B, TangentSpace J p := fun p => (W' (z' p)).1
  let b' : B → ℝ := fun p =>
    -(DifferentialGeometry.Manifold.Interval.tangentCoordinateIcc (z' p).val.2 (W' (z' p)).2)
  have hT : T' = T := by
    funext p
    exact congrArg Prod.fst (hp (z' p))
  have hb : b' = b := by
    funext p
    exact congrArg (fun v : E × EuclideanSpace ℝ (Fin 1) =>
      -(DifferentialGeometry.Manifold.Interval.tangentCoordinateIcc (z' p).val.2 v.2)) (hp (z' p))
  have hr := relativePoincareHopf_one_of_collar J hδ hδε Y' hY' e' hi' V hV hVf hVi hVI hn' K
  change interiorIndexSum I V hVf hVi hVI + (∑ᶠ _ : {p | T' p = 0 ∧ b' p < 0}, (1 : ℤ)) =
    DifferentialGeometry.Homology.eulerChar K (TopCat.of M) at hr
  rw [hT, hb] at hr
  exact hr

end DifferentialGeometry.VectorField
