import DifferentialGeometry.Topology.VectorField.RelativePoincareHopfOne
import DifferentialGeometry.Topology.Manifold.ZeroDimensional

set_option autoImplicit false
noncomputable section
open Set Bundle Filter Manifold TopologicalSpace
open scoped ContDiff Topology
namespace Poincare.VectorField

theorem eulerChar_collar_base_of_outward_components_one
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
      (∀ x, I.IsBoundaryPoint x → (EuclideanSpace.proj (𝕜 := ℝ) (0 : Fin 1)) (V x) < 0) →
    ∀ (_hVf : {x | V x = 0}.Finite)
      (_hVi : ∀ x, V x = 0 → HasContinuousIsolatedZero I V x)
      (_hVI : ∀ x, V x = 0 → I.IsInteriorPoint x),
    let W := _root_.VectorField.mpullback (J.prod (𝓡∂ 1)) I e (fun y : Y => V y.val)
    (∀ q : S, W q ≠ 0) →
    ∀ T : ∀ p : B, TangentSpace J p,
      (∀ q : S, q.val.2.val = 0 → W q =
        (T q.val.1, (Poincare.Manifold.Interval.tangentCoordinateIcc q.val.2).symm (-1))) →
    ∀ (K : Type) [Field K],
      Poincare.Homology.eulerChar K (TopCat.of B) =
        (1 - (-1 : ℤ) ^ 1) * Poincare.Homology.eulerChar K (TopCat.of M) := by
  intro I S Y hY e hi V hV hout hVf hVi hVI W hn T hcomp K _
  let z : B → S := fun p => ⟨(p, ⟨0, ⟨le_rfl, (Fact.out : (0 : ℝ) < ε).le⟩⟩), hδ⟩
  let Wn := _root_.VectorField.mpullback (J.prod (𝓡∂ 1)) I e (fun y : Y => (-V) y.val)
  have hWn (q : S) : Wn q = -W q := _root_.VectorField.mpullback_neg_apply
  have hnf : {x | (-V) x = 0}.Finite := by simpa only [Pi.neg_apply, neg_eq_zero] using hVf
  have hni (x : M) (hx : (-V) x = 0) : HasContinuousIsolatedZero I (-V) x :=
    (hVi x (neg_eq_zero.mp hx)).neg I
  have hnI (x : M) (hx : (-V) x = 0) : I.IsInteriorPoint x := hVI x (neg_eq_zero.mp hx)
  have hnn (q : S) : Wn q ≠ 0 := by rw [hWn]; exact neg_ne_zero.mpr (hn q)
  have hr := relativePoincareHopf_one_of_collar J hδ hδε Y hY e hi (-V) hV.neg_section hnf hni hnI hnn K
  let Tn : ∀ p : B, TangentSpace J p := fun p => (Wn (z p)).1
  let bn : B → ℝ := fun p =>
    -(Poincare.Manifold.Interval.tangentCoordinateIcc (z p).val.2 (Wn (z p)).2)
  have hbn : bn = (fun _ : B => (-1 : ℝ)) := by
    funext p
    change -(Poincare.Manifold.Interval.tangentCoordinateIcc (z p).val.2 (Wn (z p)).2) = -1
    rw [hWn, hcomp (z p) rfl]
    change -(Poincare.Manifold.Interval.tangentCoordinateIcc (z p).val.2
      (-((Poincare.Manifold.Interval.tangentCoordinateIcc (z p).val.2).symm (-1)))) = -1
    rw [map_neg, ContinuousLinearEquiv.apply_symm_apply, neg_neg]
  change interiorIndexSum I (-V) hnf hni hnI +
    (∑ᶠ _ : {p | Tn p = 0 ∧ bn p < 0}, (1 : ℤ)) =
      Poincare.Homology.eulerChar K (TopCat.of M) at hr
  rw [hbn] at hr
  have hs : {p | Tn p = 0 ∧ (-1 : ℝ) < 0} = {p | Tn p = 0} := by
    ext p
    simp
  rw [hs] at hr
  rw [sum_one_zeroSet_eq_eulerChar_of_subsingleton_model K Tn] at hr
  have hneg := interiorIndexSum_neg I V hVf hVi hVI
  have hvχ := interiorIndexSum_eq_eulerChar_of_outward V hV hout hVf hVi hVI K
  rw [hvχ] at hneg
  have hsum : (-1 : ℤ) ^ 1 * Poincare.Homology.eulerChar K (TopCat.of M) +
      Poincare.Homology.eulerChar K (TopCat.of B) = Poincare.Homology.eulerChar K (TopCat.of M) :=
    hneg ▸ hr
  linarith

end Poincare.VectorField
