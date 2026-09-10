import DifferentialGeometry.Topology.VectorField.PrescribedBoundaryComponents
import DifferentialGeometry.Topology.VectorField.RelativePoincareHopf
import DifferentialGeometry.Topology.VectorField.ClopenPoincareHopf

set_option autoImplicit false
noncomputable section
open Set Bundle Filter Manifold TopologicalSpace
open scoped ContDiff Topology
namespace Poincare.VectorField

theorem mixedPoincareHopf_of_collar
    {d : ℕ} {H B M : Type}
    [TopologicalSpace H] [TopologicalSpace B] [ChartedSpace H B]
    [CompactSpace B] [T2Space B]
    (J : ModelWithCorners ℝ (EuclideanSpace ℝ (Fin (d + 1))) H)
    [IsManifold J ∞ B] [BoundarylessManifold J B]
    [TopologicalSpace M] [ChartedSpace (EuclideanHalfSpace (d + 2)) M]
    [IsManifold (𝓡∂ (d + 2)) ∞ M] [T2Space M] [CompactSpace M]
    {ε δ : ℝ} [Fact ((0 : ℝ) < ε)] (hδ : 0 < δ) (hδε : δ < ε) :
    let I := 𝓡∂ (d + 2)
    let S : Opens (B × Icc (0 : ℝ) ε) :=
      ⟨{q | q.2.val < δ}, isOpen_lt (continuous_subtype_val.comp continuous_snd) continuous_const⟩
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
    (∀ q : S, W q ≠ 0) →
    ∀ (A : Set B), IsClopen A →
      (∀ q : S, q.val.2.val = 0 →
        (q.val.1 ∈ A → 0 < Poincare.Manifold.Interval.tangentCoordinateIcc q.val.2 (W q).2) ∧
        (q.val.1 ∉ A → Poincare.Manifold.Interval.tangentCoordinateIcc q.val.2 (W q).2 < 0)) →
    ∀ (K : Type) [Field K],
      interiorIndexSum I V hVf hVi hVI =
        Poincare.Homology.eulerChar K (TopCat.of M) - Poincare.Homology.eulerChar K (TopCat.of A) := by
  intro I S Y hY e hi hz V hV hVf hVi hVI W hn A hA hsign K _
  classical
  obtain ⟨T, hT, hTf, hTi, hTI, _⟩ := exists_closed_vectorField_interiorIndexSum_eq_eulerChar J (M := B)
  let b : B → ℝ := fun p => if p ∈ A then 1 else -1
  have hb : ContMDiff J 𝓘(ℝ, ℝ) ∞ b := by
    intro p
    by_cases hp : p ∈ A
    · apply (contMDiffAt_const (c := (1 : ℝ))).congr_of_eventuallyEq
      filter_upwards [hA.isOpen.mem_nhds hp] with q hq
      simp only [b, if_pos hq]
    · apply (contMDiffAt_const (c := (-1 : ℝ))).congr_of_eventuallyEq
      filter_upwards [hA.isClosed.isOpen_compl.mem_nhds hp] with q hq
      simp only [b, if_neg hq]
  have hnormal (q : S) (hq : q.val.2.val = 0) :
      0 < Poincare.Manifold.Interval.tangentCoordinateIcc q.val.2 (W q).2 * b q.val.1 := by
    by_cases hp : q.val.1 ∈ A
    · simpa only [b, if_pos hp, mul_one] using (hsign q hq).1 hp
    · simpa only [b, if_neg hp, mul_neg_one] using neg_pos.mpr ((hsign q hq).2 hp)
  obtain ⟨G, hG, hzero, hgerm, hcomp⟩ :=
    exists_with_prescribed_boundary_components hδ Y hY e hi hz V hV T b hT hb hnormal
  have hGf : {x | G x = 0}.Finite := hzero.symm ▸ hVf
  have hGV (x : M) (hx : G x = 0) : V x = 0 :=
    (congrArg (fun s : Set M => x ∈ s) hzero).mp hx
  have hGi (x : M) (hx : G x = 0) : HasContinuousIsolatedZero I G x :=
    (hVi x (hGV x hx)).congr (hgerm x (hGV x hx)).symm
  have hGI (x : M) (hx : G x = 0) : I.IsInteriorPoint x := hVI x (hGV x hx)
  let WG := _root_.VectorField.mpullback (J.prod (𝓡∂ 1)) I e (fun y : Y => G y.val)
  have hGn (q : S) : WG q ≠ 0 := by
    intro hq
    have hv := hGV (e q).val
      ((mpullback_diffeomorph_eq_zero_iff e (by simp) (fun y : Y => G y.val) q).mp hq)
    exact hn q ((mpullback_diffeomorph_eq_zero_iff e (by simp) (fun y : Y => V y.val) q).mpr hv)
  let z : B → S := fun p => ⟨(p, ⟨0, ⟨le_rfl, (Fact.out : (0 : ℝ) < ε).le⟩⟩), hδ⟩
  let TG : ∀ p : B, TangentSpace J p := fun p => (WG (z p)).1
  let bG : B → ℝ := fun p =>
    -(Poincare.Manifold.Interval.tangentCoordinateIcc (z p).val.2 (WG (z p)).2)
  have hTG : TG = T := by
    funext p
    exact congrArg Prod.fst (hcomp (z p) rfl)
  have hregion : {p | bG p < 0} = A := by
    ext p
    change -(Poincare.Manifold.Interval.tangentCoordinateIcc (z p).val.2 (WG (z p)).2) < 0 ↔ p ∈ A
    have hc := congrArg (fun v : EuclideanSpace ℝ (Fin (d + 1)) × EuclideanSpace ℝ (Fin 1) =>
      Poincare.Manifold.Interval.tangentCoordinateIcc (z p).val.2 v.2) (hcomp (z p) rfl)
    change Poincare.Manifold.Interval.tangentCoordinateIcc (z p).val.2 (WG (z p)).2 =
      Poincare.Manifold.Interval.tangentCoordinateIcc (z p).val.2
        ((Poincare.Manifold.Interval.tangentCoordinateIcc (z p).val.2).symm (b p)) at hc
    rw [hc, ContinuousLinearEquiv.apply_symm_apply]
    by_cases hp : p ∈ A <;> simp [b, hp]
  have hr := relativePoincareHopf_of_collar J hδ hδε Y hY e hi G hG hGf hGi hGI hGn
  change ∀ (hf : {p | TG p = 0}.Finite)
    (his : ∀ p, TG p = 0 → HasContinuousIsolatedZero J TG p)
    (hint : ∀ p, TG p = 0 → J.IsInteriorPoint p) (K : Type) [Field K],
    interiorIndexSum I G hGf hGi hGI + interiorIndexSumOn J TG hf his hint {p | bG p < 0} =
      Poincare.Homology.eulerChar K (TopCat.of M) at hr
  rw [hTG] at hr
  have hlaw := hr hTf hTi hTI K
  rw [hregion, interiorIndexSumOn_eq_eulerChar_of_isClopen J T hT hTf hTi hTI A hA K] at hlaw
  have heq := interiorIndexSum_eq_of_zero_germ I G V hGf hGi hGI hVf hVi hVI hzero
    (fun x hx => hgerm x (hGV x hx))
  rw [heq] at hlaw
  omega

end Poincare.VectorField
