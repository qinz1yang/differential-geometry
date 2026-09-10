import DifferentialGeometry.Topology.VectorField.InwardCollarIndexGerm
import DifferentialGeometry.Topology.VectorField.DiffeomorphPatchGerm
import DifferentialGeometry.Topology.VectorField.CollarIndexTransport
import DifferentialGeometry.Topology.VectorField.ContinuousIsolatedZeroGerm

set_option autoImplicit false
noncomputable section
open Set Bundle Filter Manifold TopologicalSpace
open scoped ContDiff Topology
namespace Poincare.VectorField

theorem exists_inwardCollar_patch_index
    {d : ℕ} {H H' B M : Type*}
    [TopologicalSpace H] [TopologicalSpace H']
    [TopologicalSpace B] [ChartedSpace H B] [TopologicalSpace M] [ChartedSpace H' M]
    (J : ModelWithCorners ℝ (EuclideanSpace ℝ (Fin (d + 1))) H)
    (I : ModelWithCorners ℝ (EuclideanSpace ℝ (Fin (d + 2))) H')
    [IsManifold J 1 B] [IsManifold I 1 M]
    {ε a : ℝ} [Fact ((0 : ℝ) < ε)] (ha : a ≠ 0)
    (S : Opens (B × Icc (0 : ℝ) ε)) (Y : Opens M)
    (e : Diffeomorph (J.prod (𝓡∂ 1)) I S Y ∞)
    (V : ∀ x : M, TangentSpace I x)
    (T : ∀ p : B, TangentSpace J p) (b : B → ℝ)
    (L : ∀ q : S, TangentSpace (J.prod (𝓡∂ 1)) q)
    (hL : ∀ p : S, p.val.2.val ≤ a → L p =
      (T p.val.1, (Poincare.Manifold.Interval.tangentCoordinateIcc p.val.2).symm
        (-a * (collarExtension T b collarTransition (p.val.1, 1 - p.val.2.val / a)).2)))
    (q : S) (hq : 0 < q.val.2.val ∧ q.val.2.val < ε) (hqa : q.val.2.val < a)
    (hT : HasContinuousIsolatedZero J T q.val.1) (hbase : J.IsInteriorPoint q.val.1)
    (hb : ContMDiffAt J 𝓘(ℝ, ℝ) 1 b q.val.1) (hb0 : b q.val.1 ≠ 0) (hz : L q = 0) :
    ∃ (hG : HasContinuousIsolatedZero I (patchThroughDiffeomorph Y e V L) (e q).val)
      (hGI : I.IsInteriorPoint (e q).val),
      interiorIndex I (patchThroughDiffeomorph Y e V L) (e q).val hG hGI =
        interiorIndex J T q.val.1 hT hbase := by
  obtain ⟨f, hqf, hf, hLgerm⟩ := exists_inwardCollar_pullback_germ ha S T b L hL q hq hqa
  have hCzero := (mpullback_partialDiffeomorph_eq_zero_iff f (by simp)
    (collarExtension T b collarTransition) hqf).mp (hLgerm.self_of_nhds.symm.trans hz)
  obtain ⟨Φ, hΦs, hΦeq, hGgerm⟩ := exists_patchThroughDiffeomorph_model_germ Y e V L
    (collarExtension T b collarTransition) f hqf hLgerm
  have hfq := hf q hqf
  erw [hfq] at hCzero hΦs hΦeq
  let Φ₁ : PartialDiffeomorph (J.prod 𝓘(ℝ, ℝ)) I (B × ℝ) M 1 :=
    { Φ with
      contMDiffOn_toFun := Φ.contMDiffOn.of_le (by simp)
      contMDiffOn_invFun := Φ.symm.contMDiffOn.of_le (by simp) }
  let W := _root_.VectorField.mpullback I (J.prod 𝓘(ℝ, ℝ)) Φ₁.symm
    (collarExtension T b collarTransition)
  have hW : HasContinuousIsolatedZero I W (e q).val :=
    hΦeq ▸ hT.collarPushforward J I Φ₁ hΦs hb hb0 hCzero
  have hWI : I.IsInteriorPoint (e q).val :=
    hΦeq ▸ isInteriorPoint_collar_image J I Φ₁ hΦs hbase
  have hG : HasContinuousIsolatedZero I (patchThroughDiffeomorph Y e V L) (e q).val :=
    hW.congr hGgerm.symm
  refine ⟨hG, hWI, (interiorIndex_congr I hG hW hGgerm hWI).trans ?_⟩
  have hindex := interiorIndex_collarPushforward J I Φ₁ hΦs hT hbase hb hb0 hCzero
  have hΦ₁eq : Φ₁ (q.val.1, 1 - q.val.2.val / a) = (e q).val := hΦeq
  have hresult (x : M) (he : x = Φ₁ (q.val.1, 1 - q.val.2.val / a))
      (hx : HasContinuousIsolatedZero I W x) (hxi : I.IsInteriorPoint x) :
      interiorIndex I W x hx hxi = interiorIndex J T q.val.1 hT hbase := by
    subst x
    exact hindex
  exact hresult (e q).val hΦ₁eq.symm hW hWI

end Poincare.VectorField
