import DifferentialGeometry.Topology.VectorField.CollarPatch
import DifferentialGeometry.Topology.Manifold.BoundaryCollar.NormalSign

set_option autoImplicit false
noncomputable section
open Set Bundle Filter Manifold TopologicalSpace
open scoped ContDiff Topology
namespace Poincare.VectorField

theorem exists_outward_replacement_in_collar
    {E H B M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [TopologicalSpace H] [TopologicalSpace B] [ChartedSpace H B] [CompactSpace B]
    {J : ModelWithCorners ℝ E H} [IsManifold J 1 B]
    {n : ℕ} [TopologicalSpace M] [ChartedSpace (EuclideanHalfSpace (n + 1)) M]
    [IsManifold (𝓡∂ (n + 1)) 1 M] [T2Space M]
    {ε δ a : ℝ} [Fact ((0 : ℝ) < ε)] (hδ : 0 < δ) (hδε : δ < ε)
    (ha : 0 < a) (haδ : 4 * a < δ) :
    let I := 𝓡∂ (n + 1)
    let S : Opens (B × Icc (0 : ℝ) ε) :=
      ⟨{q | q.2.val < δ}, isOpen_lt (continuous_subtype_val.comp continuous_snd) continuous_const⟩
    ∀ (Y : Opens M), I.boundary M ⊆ Y →
    ∀ e : Diffeomorph (J.prod (𝓡∂ 1)) I S Y ∞,
      (∀ q : S, 0 < q.val.2.val → I.IsInteriorPoint (e q).val) →
    ∀ V : ∀ x : M, TangentSpace I x,
      ContMDiff I I.tangent ∞ (fun x => (⟨x, V x⟩ : TangentBundle I M)) →
    let W := _root_.VectorField.mpullback (J.prod (𝓡∂ 1)) I e (fun y : Y => V y.val)
    (∀ q : S, W q ≠ 0) →
    let z : B → S := fun p => ⟨(p, ⟨0, ⟨le_rfl, (Fact.out : (0 : ℝ) < ε).le⟩⟩), hδ⟩
    let T : ∀ p : B, TangentSpace J p := fun p => (W (z p)).1
    let b : B → ℝ := fun p =>
      -(Poincare.Manifold.Interval.tangentCoordinateIcc (z p).val.2 (W (z p)).2) / a
    ∃ L : ∀ q : S, TangentSpace (J.prod (𝓡∂ 1)) q,
      ContMDiff (J.prod (𝓡∂ 1)) (J.prod (𝓡∂ 1)).tangent ∞
        (fun q => (⟨q, L q⟩ : TangentBundle (J.prod (𝓡∂ 1)) S)) ∧
      (∀ q : S, q.val.2.val ≤ a → L q =
        (T q.val.1, (Poincare.Manifold.Interval.tangentCoordinateIcc q.val.2).symm
          (-a * (collarExtension T b collarTransition (q.val.1, 1 - q.val.2.val / a)).2))) ∧
      ∃ G : ∀ x : M, TangentSpace I x,
        G = patchThroughDiffeomorph Y e V L ∧
        ContMDiff I I.tangent ∞ (fun x => (⟨x, G x⟩ : TangentBundle I M)) ∧
        (∀ x, I.IsBoundaryPoint x → (EuclideanSpace.proj (𝕜 := ℝ) (0 : Fin (n + 1))) (G x) < 0) ∧
        (∀ x, V x = 0 → G =ᶠ[𝓝 x] V) ∧
        ({x | G x = 0} = (fun q : S => (e q).val) '' {q | L q = 0} ∪ {x | V x = 0}) ∧
        Disjoint ((fun q : S => (e q).val) '' {q | L q = 0}) {x | V x = 0} ∧
        BijOn (fun q : S => q.val.1) {q | L q = 0} {p | T p = 0 ∧ b p < 0} ∧
        (∀ q : S, L q = 0 → q.val.2.val ∈ Ioo (a / 3) (2 * a / 3)) ∧
        ({p | T p = 0}.Finite → {x | V x = 0}.Finite → {x | G x = 0}.Finite) := by
  intro I S Y hY e hi V hV W hn z T b
  have hW : ContMDiff (J.prod (𝓡∂ 1)) (J.prod (𝓡∂ 1)).tangent ∞
      (fun q => (⟨q, W q⟩ : TangentBundle (J.prod (𝓡∂ 1)) S)) := by
    have hVr := contMDiff_tangentSection_restrict_opens Y hV.contMDiffOn
    intro q
    exact contMDiffAt_mpullback_partialDiffeomorph e.toPartialDiffeomorph (by simp)
      (by trivial) (hVr (e q))
  obtain ⟨L, hL, hLinner, hLmatch, hLout, hLzero⟩ := exists_inwardCollar_outwardization hδ ha W hW hn
  let G := patchThroughDiffeomorph Y e V L
  have hboundary (p : B) (hTp : T p = 0) : b p ≠ 0 := by
    intro hbp
    have hv : Poincare.Manifold.Interval.tangentCoordinateIcc (z p).val.2 (W (z p)).2 = 0 :=
      neg_eq_zero.mp ((div_eq_zero_iff.mp hbp).resolve_right ha.ne')
    exact hn (z p) (Prod.ext hTp
      ((Poincare.Manifold.Interval.tangentCoordinateIcc (z p).val.2).map_eq_zero_iff.mp hv))
  have hzero := patchThroughCollar_zeroSet S Y e V L hn
  refine ⟨L, hL, hLinner, G, rfl,
    contMDiff_patchThroughCollar S rfl Y e V L haδ hLmatch hV hL, ?_, ?_,
    hzero.1, hzero.2,
    inwardCollar_zeroSet_proj_bijOn S rfl T b L hboundary hLzero ha (by linarith) (by linarith),
    (fun q hq => inwardCollar_zero_height S T b L hboundary hLzero ha hq), ?_⟩
  · intro x hx
    let y : Y := ⟨x, hY hx⟩
    let q := e.symm y
    have he : (e q).val = x := congrArg Subtype.val (e.apply_symm_apply y)
    have hqb : I.IsBoundaryPoint (e q).val := he.symm ▸ hx
    have hq0 : q.val.2.val = 0 := by
      apply le_antisymm _ q.val.2.property.1
      by_contra h
      exact (I.isBoundaryPoint_iff_not_isInteriorPoint (e q).val).mp hqb (hi q (lt_of_not_ge h))
    have hv := Poincare.Manifold.BoundaryCollar.proj_collar_pushforward_neg S Y e hq0 hqb (L q)
      (by rw [hLout q hq0]; exact neg_neg_of_pos ha)
    have hg := patchThroughDiffeomorph_apply Y e V L q
    change (G (e q).val : EuclideanSpace ℝ (Fin (n + 1))) = _ at hg
    rw [← hg] at hv
    erw [he] at hv
    exact hv
  · intro x hx
    have hh := patchThroughCollar_eventuallyEq_at_original_zero S rfl Y e V L haδ hLmatch hn hx
    filter_upwards [hh] with y hy
    exact TotalSpace.mk_injective y hy
  · intro hTfinite hVfinite
    rw [hzero.1]
    exact ((finite_inwardCollar_zeroSet S rfl T b L hboundary hLzero ha
      (by linarith) (by linarith) hTfinite).image _).union hVfinite

end Poincare.VectorField
