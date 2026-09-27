import DifferentialGeometry.Topology.VectorField.CollarPullback
import DifferentialGeometry.Topology.VectorField.PullbackRestriction
import DifferentialGeometry.Topology.Manifold.Diffeomorph.Restriction

set_option autoImplicit false
noncomputable section
open Set Bundle Manifold TopologicalSpace
open scoped ContDiff Topology
namespace DifferentialGeometry.VectorField

theorem exists_nonvanishing_collar_restriction
    {E H B F G M : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    [TopologicalSpace H] [TopologicalSpace B] [ChartedSpace H B] [CompactSpace B]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    [TopologicalSpace G] [TopologicalSpace M] [ChartedSpace G M]
    {J : ModelWithCorners ℝ E H} {I : ModelWithCorners ℝ F G}
    [IsManifold J 1 B] [IsManifold I 1 M]
    {ε : ℝ} [Fact ((0 : ℝ) < ε)]
    (S : Opens (B × Icc (0 : ℝ) ε)) (Y : Opens M)
    (e : Diffeomorph (J.prod (𝓡∂ 1)) I S Y ∞)
    (hS : ∀ p : B, (p, ⟨0, ⟨le_rfl, (Fact.out : (0 : ℝ) < ε).le⟩⟩) ∈ S)
    (V : ∀ x : M, TangentSpace I x)
    (hV : ContMDiff I I.tangent ∞ (fun x => (⟨x, V x⟩ : TangentBundle I M)))
    (hn : ∀ q : S, q.val.2.val = 0 → V (e q).val ≠ 0) :
    ∃ (δ : ℝ) (_ : 0 < δ), δ < ε ∧
      let U : Opens (B × Icc (0 : ℝ) ε) :=
        ⟨{q | q.2.val < δ}, isOpen_lt (continuous_subtype_val.comp continuous_snd) continuous_const⟩
      ∃ (hUS : U ≤ S) (W : Opens M) (d : Diffeomorph (J.prod (𝓡∂ 1)) I U W ∞),
        (∀ q : U, (d q).val = (e ⟨q.val, hUS q.property⟩).val) ∧
        (∀ q : U, _root_.VectorField.mpullback (J.prod (𝓡∂ 1)) I d (fun y : W => V y.val) q =
          _root_.VectorField.mpullback (J.prod (𝓡∂ 1)) I e (fun y : Y => V y.val) ⟨q.val, hUS q.property⟩) ∧
        ∀ q : U, _root_.VectorField.mpullback (J.prod (𝓡∂ 1)) I d (fun y : W => V y.val) q ≠ 0 := by
  let W0 := _root_.VectorField.mpullback (J.prod (𝓡∂ 1)) I e (fun y : Y => V y.val)
  have hW0 : ContMDiff (J.prod (𝓡∂ 1)) (J.prod (𝓡∂ 1)).tangent ∞
      (fun q => (⟨q, W0 q⟩ : TangentBundle (J.prod (𝓡∂ 1)) S)) := by
    have hVr := contMDiff_tangentSection_restrict_opens Y hV.contMDiffOn
    intro q
    exact contMDiffAt_mpullback_partialDiffeomorph e.toPartialDiffeomorph (by simp)
      (by trivial) (hVr (e q))
  have hopen : IsOpen {q : S | W0 q ≠ 0} :=
    (DifferentialGeometry.VectorBundle.isClosed_zeroSet ℝ hW0.continuous).isOpen_compl
  obtain ⟨δ, hδ, hδε, hstrip⟩ := DifferentialGeometry.Topology.exists_shorter_strip_image_subset
    (Fact.out : (0 : ℝ) < ε) continuous_id (S.isOpen.isOpenMap_subtype_val _ hopen)
    (fun p => ⟨⟨_, hS p⟩, fun h => hn ⟨_, hS p⟩ rfl
      ((mpullback_diffeomorph_eq_zero_iff e (by simp) (fun y : Y => V y.val) _).mp h), rfl⟩)
  let U : Opens (B × Icc (0 : ℝ) ε) :=
    ⟨{q | q.2.val < δ}, isOpen_lt (continuous_subtype_val.comp continuous_snd) continuous_const⟩
  have hUS : U ≤ S := by
    intro q hq
    obtain ⟨r, _, hr⟩ := hstrip ⟨q, hq, rfl⟩
    change r.val = q at hr
    exact hr ▸ r.property
  obtain ⟨W, _, _, d, hd, _⟩ := DifferentialGeometry.Manifold.Diffeomorph.exists_restrict_opens e U hUS
  have hp := mpullback_eq_of_restrict_opens e d hUS hd V
  refine ⟨δ, hδ, hδε, hUS, W, d, hd, hp, ?_⟩
  intro q hq
  rw [hp q] at hq
  obtain ⟨r, hr, heq⟩ := hstrip ⟨q.val, q.property, rfl⟩
  have hh : r = ⟨q.val, hUS q.property⟩ := Subtype.ext heq
  exact hr (hh ▸ hq)

end DifferentialGeometry.VectorField
