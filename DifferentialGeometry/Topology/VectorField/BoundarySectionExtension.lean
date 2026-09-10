import DifferentialGeometry.Topology.VectorField.CollarPatch
import Mathlib.Geometry.Manifold.VectorBundle.ContMDiffSection

set_option autoImplicit false
noncomputable section
open Set Bundle Filter Manifold TopologicalSpace
open scoped ContDiff Topology
namespace Poincare.VectorField

theorem exists_boundary_section_extension
    {E F H H' B M : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    [TopologicalSpace H] [TopologicalSpace H']
    [TopologicalSpace B] [ChartedSpace H B] [CompactSpace B]
    [TopologicalSpace M] [ChartedSpace H' M] [T2Space M]
    {J : ModelWithCorners ℝ E H} {I : ModelWithCorners ℝ F H'}
    [IsManifold J 1 B] [IsManifold I 1 M]
    {ε δ : ℝ} [Fact ((0 : ℝ) < ε)] (hδ : 0 < δ) :
    let S : Opens (B × Icc (0 : ℝ) ε) :=
      ⟨{q | q.2.val < δ}, isOpen_lt (continuous_subtype_val.comp continuous_snd) continuous_const⟩
    ∀ (Y : Opens M) (e : Diffeomorph (J.prod (𝓡∂ 1)) I S Y ∞)
      (V : ∀ x : M, TangentSpace I x),
      ContMDiff I I.tangent ∞ (fun x => (⟨x, V x⟩ : TangentBundle I M)) →
    ∀ (T : ∀ p : B, TangentSpace J p) (b : B → ℝ),
      ContMDiff J J.tangent ∞ (fun p => (⟨p, T p⟩ : TangentBundle J B)) →
      ContMDiff J 𝓘(ℝ, ℝ) ∞ b →
    ∃ G : ∀ x : M, TangentSpace I x,
      ContMDiff I I.tangent ∞ (fun x => (⟨x, G x⟩ : TangentBundle I M)) ∧
      ∀ q : S, q.val.2.val = 0 → G (e q).val =
        mfderiv (J.prod (𝓡∂ 1)) I e q
          (T q.val.1, (Poincare.Manifold.Interval.tangentCoordinateIcc q.val.2).symm (b q.val.1)) := by
  intro S Y e V hV T b hT hb
  let W := _root_.VectorField.mpullback (J.prod (𝓡∂ 1)) I e (fun y : Y => V y.val)
  have hW : ContMDiff (J.prod (𝓡∂ 1)) (J.prod (𝓡∂ 1)).tangent ∞
      (fun q => (⟨q, W q⟩ : TangentBundle (J.prod (𝓡∂ 1)) S)) := by
    have hVr := contMDiff_tangentSection_restrict_opens Y hV.contMDiffOn
    intro q
    exact contMDiffAt_mpullback_partialDiffeomorph e.toPartialDiffeomorph (by simp)
      (by trivial) (hVr (e q))
  let Q : ∀ q : S, TangentSpace (J.prod (𝓡∂ 1)) q := fun q =>
    (T q.val.1, (Poincare.Manifold.Interval.tangentCoordinateIcc q.val.2).symm (b q.val.1))
  have hQ : ContMDiff (J.prod (𝓡∂ 1)) (J.prod (𝓡∂ 1)).tangent ∞
      (fun q => (⟨q, Q q⟩ : TangentBundle (J.prod (𝓡∂ 1)) S)) := by
    apply (contMDiff_tangentSection_opens_iff S Q).mpr
    have hp := (contMDiff_fst (I := J) (J := 𝓡∂ 1) (n := ∞)).comp (contMDiff_subtype_val (U := S))
    have hr := Poincare.Manifold.Interval.contMDiff_tangentCoordinateIcc_symm.comp
      (((contMDiff_snd (I := J) (J := 𝓡∂ 1)).comp
        (contMDiff_subtype_val (U := S))).prodMk (hb.comp hp))
    exact contMDiff_equivTangentBundleProd_symm.comp ((hT.comp hp).prodMk hr)
  let β : S → ℝ := fun q => 1 - collarTransition (2 * q.val.2.val / δ)
  have hβ : ContMDiff (J.prod (𝓡∂ 1)) 𝓘(ℝ, ℝ) ∞ β := by
    have hl : ContDiff ℝ ∞ (fun r : ℝ => 1 - collarTransition (2 * r / δ)) := by
      exact contDiff_const.sub (contDiff_collarTransition.comp (by fun_prop))
    exact hl.contMDiff.comp (contMDiff_subtypeVal_Icc.comp
      ((contMDiff_snd (I := J) (J := 𝓡∂ 1)).comp (contMDiff_subtype_val (U := S))))
  let L : ∀ q : S, TangentSpace (J.prod (𝓡∂ 1)) q := fun q =>
    β q • Q q + (1 - β q) • W q
  have hL : ContMDiff (J.prod (𝓡∂ 1)) (J.prod (𝓡∂ 1)).tangent ∞
      (fun q => (⟨q, L q⟩ : TangentBundle (J.prod (𝓡∂ 1)) S)) :=
    (hβ.smul_section hQ).add_section ((contMDiff_const.sub hβ).smul_section hW)
  have hmatch (q : S) (hq : δ / 2 ≤ q.val.2.val) : L q = W q := by
    have ht : 2 / 3 ≤ 2 * q.val.2.val / δ := by
      apply (le_div_iff₀ hδ).mpr
      linarith
    have hβq : β q = 0 := by simp only [β, collarTransition_eq_one ht, sub_self]
    simp only [L, hβq, zero_smul, sub_zero, one_smul, zero_add]
  refine ⟨patchThroughDiffeomorph Y e V L,
    contMDiff_patchThroughCollar S rfl Y e V L (by linarith : δ / 2 < δ) hmatch hV hL, ?_⟩
  intro q hq
  rw [patchThroughDiffeomorph_apply]
  have hβq : β q = 1 := by
    simp only [β, hq, mul_zero, zero_div, collarTransition_eq_zero (by norm_num : (0 : ℝ) ≤ 1 / 3), sub_zero]
  simp only [L, hβq, one_smul, sub_self, zero_smul, add_zero]
  rfl

end Poincare.VectorField
