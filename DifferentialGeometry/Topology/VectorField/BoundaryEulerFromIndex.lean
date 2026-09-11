import DifferentialGeometry.Topology.VectorField.RelativePoincareHopf
import DifferentialGeometry.Topology.VectorField.ClosedPoincareHopf

set_option autoImplicit false
noncomputable section
open Set Bundle Filter Manifold TopologicalSpace
open scoped ContDiff Topology
namespace DifferentialGeometry.VectorField

theorem eulerChar_collar_base_of_outward_components
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
    ∀ V : ∀ x : M, TangentSpace I x,
      ContMDiff I I.tangent ∞ (fun x => (⟨x, V x⟩ : TangentBundle I M)) →
      (∀ x, I.IsBoundaryPoint x → (EuclideanSpace.proj (𝕜 := ℝ) (0 : Fin (d + 2))) (V x) < 0) →
    ∀ (_hVf : {x | V x = 0}.Finite)
      (_hVi : ∀ x, V x = 0 → HasContinuousIsolatedZero I V x)
      (_hVI : ∀ x, V x = 0 → I.IsInteriorPoint x),
    let W := _root_.VectorField.mpullback (J.prod (𝓡∂ 1)) I e (fun y : Y => V y.val)
    (∀ q : S, W q ≠ 0) →
    ∀ T : ∀ p : B, TangentSpace J p,
      ContMDiff J J.tangent ∞ (fun p => (⟨p, T p⟩ : TangentBundle J B)) →
      (∀ q : S, q.val.2.val = 0 → W q =
        (T q.val.1, (DifferentialGeometry.Manifold.Interval.tangentCoordinateIcc q.val.2).symm (-1))) →
    ∀ (_hTf : {p | T p = 0}.Finite)
      (_hTi : ∀ p, T p = 0 → HasContinuousIsolatedZero J T p)
      (K : Type) [Field K],
      DifferentialGeometry.Homology.eulerChar K (TopCat.of B) =
        (1 - (-1 : ℤ) ^ (d + 2)) * DifferentialGeometry.Homology.eulerChar K (TopCat.of M) := by
  intro I S Y hY e hi V hV hout hVf hVi hVI W hn T hT hcomp hTf hTi K _
  let z : B → S := fun p => ⟨(p, ⟨0, ⟨le_rfl, (Fact.out : (0 : ℝ) < ε).le⟩⟩), hδ⟩
  let Wn := _root_.VectorField.mpullback (J.prod (𝓡∂ 1)) I e (fun y : Y => (-V) y.val)
  have hWn (q : S) : Wn q = -W q := _root_.VectorField.mpullback_neg_apply
  have hnf : {x | (-V) x = 0}.Finite := by simpa only [Pi.neg_apply, neg_eq_zero] using hVf
  have hni (x : M) (hx : (-V) x = 0) : HasContinuousIsolatedZero I (-V) x :=
    (hVi x (neg_eq_zero.mp hx)).neg I
  have hnI (x : M) (hx : (-V) x = 0) : I.IsInteriorPoint x := hVI x (neg_eq_zero.mp hx)
  have hnn (q : S) : Wn q ≠ 0 := by rw [hWn]; exact neg_ne_zero.mpr (hn q)
  have hr := relativePoincareHopf_of_collar J hδ hδε Y hY e hi (-V) hV.neg_section hnf hni hnI hnn
  let Tn : ∀ p : B, TangentSpace J p := fun p => (Wn (z p)).1
  let bn : B → ℝ := fun p =>
    -(DifferentialGeometry.Manifold.Interval.tangentCoordinateIcc (z p).val.2 (Wn (z p)).2)
  have htn : Tn = -T := by
    funext p
    change (Wn (z p)).1 = -(T p)
    rw [hWn, hcomp (z p) rfl]
    rfl
  have hbn : bn = (fun _ : B => (-1 : ℝ)) := by
    funext p
    change -(DifferentialGeometry.Manifold.Interval.tangentCoordinateIcc (z p).val.2 (Wn (z p)).2) = -1
    rw [hWn, hcomp (z p) rfl]
    change -(DifferentialGeometry.Manifold.Interval.tangentCoordinateIcc (z p).val.2
      (-((DifferentialGeometry.Manifold.Interval.tangentCoordinateIcc (z p).val.2).symm (-1)))) = -1
    rw [map_neg, ContinuousLinearEquiv.apply_symm_apply, neg_neg]
  change ∀ (hTf : {p | Tn p = 0}.Finite)
    (hTi : ∀ p, Tn p = 0 → HasContinuousIsolatedZero J Tn p)
    (hTI : ∀ p, Tn p = 0 → J.IsInteriorPoint p) (K : Type) [Field K],
    interiorIndexSum I (-V) hnf hni hnI + interiorIndexSumOn J Tn hTf hTi hTI {p | bn p < 0} =
      DifferentialGeometry.Homology.eulerChar K (TopCat.of M) at hr
  rw [htn, hbn] at hr
  have hTnf : {p | (-T) p = 0}.Finite := by simpa only [Pi.neg_apply, neg_eq_zero] using hTf
  have hTni (p : B) (hp : (-T) p = 0) : HasContinuousIsolatedZero J (-T) p :=
    (hTi p (neg_eq_zero.mp hp)).neg J
  have hTnI (p : B) (_hp : (-T) p = 0) : J.IsInteriorPoint p := BoundarylessManifold.isInteriorPoint
  have hlaw := hr hTnf hTni hTnI K
  have hregion : {p : B | (-1 : ℝ) < 0} = univ := by ext; simp
  rw [hregion, interiorIndexSumOn_univ] at hlaw
  rw [interiorIndexSum_eq_eulerChar_of_boundaryless J (-T) hT.neg_section hTnf hTni hTnI K] at hlaw
  have hneg := interiorIndexSum_neg I V hVf hVi hVI
  have hvχ := interiorIndexSum_eq_eulerChar_of_outward V hV hout hVf hVi hVI K
  rw [hvχ] at hneg
  have hsum : (-1 : ℤ) ^ (d + 2) * DifferentialGeometry.Homology.eulerChar K (TopCat.of M) +
      DifferentialGeometry.Homology.eulerChar K (TopCat.of B) = DifferentialGeometry.Homology.eulerChar K (TopCat.of M) :=
    hneg ▸ hlaw
  linarith

end DifferentialGeometry.VectorField
