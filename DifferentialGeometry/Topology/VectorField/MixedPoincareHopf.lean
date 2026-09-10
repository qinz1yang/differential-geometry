import DifferentialGeometry.Topology.VectorField.MixedPoincareHopfCollar
import DifferentialGeometry.Topology.VectorField.MixedPoincareHopfCollarOne
import DifferentialGeometry.Topology.VectorField.BoundaryCollarPullback
import DifferentialGeometry.Topology.Homology.ManifoldBoundary

set_option autoImplicit false
noncomputable section
open Set Bundle Filter Manifold TopologicalSpace
open scoped ContDiff Topology
open DifferentialGeometry.Integral.DivergenceTheorem.WithBoundary
namespace Poincare.VectorField


theorem mixedPoincareHopf_one
    {M : Type} [TopologicalSpace M]
    [ChartedSpace (EuclideanHalfSpace 1) M]
    [IsManifold (𝓡∂ 1) ∞ M] [T2Space M] [CompactSpace M]
    (V : ∀ x : M, TangentSpace (𝓡∂ 1) x)
    (hV : ContMDiff (𝓡∂ 1) (𝓡∂ 1).tangent ∞
      (fun x => (⟨x, V x⟩ : TangentBundle (𝓡∂ 1) M)))
    (hVf : {x | V x = 0}.Finite)
    (hVi : ∀ x, V x = 0 → HasContinuousIsolatedZero (𝓡∂ 1) V x)
    (hVI : ∀ x, V x = 0 → (𝓡∂ 1).IsInteriorPoint x)
    (A : Set (BoundaryManifold (𝓡∂ 1) M))
    (hin : ∀ p ∈ A, 0 < (EuclideanSpace.proj (𝕜 := ℝ) (0 : Fin 1)) (V p.val))
    (hout : ∀ p ∉ A, (EuclideanSpace.proj (𝕜 := ℝ) (0 : Fin 1)) (V p.val) < 0)
    (K : Type) [Field K] :
    interiorIndexSum (𝓡∂ 1) V hVf hVi hVI =
      Poincare.Homology.eulerChar K (TopCat.of M) - Poincare.Homology.eulerChar K (TopCat.of A) := by
  let I := 𝓡∂ 1
  let B := BoundaryManifold I M
  let J := HasSmoothBoundary.boundaryModel I
  let _ : J.Boundaryless := HasSmoothBoundary.boundaryIBoundaryless
  let _ : IsManifold J ∞ B := BoundaryManifold.isManifold (I := I)
  have hK : IsCompact (I.boundary M) := (I.isClosed_boundary (n := ∞) (by simp)).isCompact
  let _ : CompactSpace B := isCompact_iff_compactSpace.mp hK
  have hn (p : B) : V p.val ≠ 0 := by
    intro hv
    by_cases hp : p ∈ A
    · have hh := hin p hp
      rw [hv] at hh
      exact (lt_irrefl 0) hh
    · have hh := hout p hp
      rw [hv] at hh
      exact (lt_irrefl 0) hh
  obtain ⟨ε, hε, c, _, _, hc0, hci, δ, hδ, hδε, Y, hY, _, e, he, _, hWn⟩ :=
    exists_nonvanishing_boundary_collar_pullback hK V hV hn
  let _ : Fact ((0 : ℝ) < ε) := ⟨hε⟩
  have hi (q : _) (hq : 0 < q.val.2.val) : I.IsInteriorPoint (e q).val := by
    rw [he q]
    exact hci q.val hq
  have hzval (q : _) (hq : q.val.2.val = 0) : (e q).val = q.val.1.val := by
    rw [he q]
    have hqeq : q.val.2 = ⟨0, ⟨le_rfl, hε.le⟩⟩ := Subtype.ext hq
    change c (q.val.1, q.val.2) = q.val.1.val
    rw [hqeq, hc0]
    rfl
  have hz (q : _) (hq : q.val.2.val = 0) : I.IsBoundaryPoint (e q).val :=
    (hzval q hq).symm ▸ q.val.1.property
  have hs (q : _) (hq : q.val.2.val = 0) :
      (q.val.1 ∈ A → 0 < Poincare.Manifold.Interval.tangentCoordinateIcc q.val.2
        (_root_.VectorField.mpullback (J.prod (𝓡∂ 1)) I e (fun y : Y => V y.val) q).2) ∧
      (q.val.1 ∉ A → Poincare.Manifold.Interval.tangentCoordinateIcc q.val.2
        (_root_.VectorField.mpullback (J.prod (𝓡∂ 1)) I e (fun y : Y => V y.val) q).2 < 0) := by
    let W := _root_.VectorField.mpullback (J.prod (𝓡∂ 1)) I e (fun y : Y => V y.val)
    obtain ⟨a, ha, hnormal⟩ := Poincare.Manifold.BoundaryCollar.collar_normal_eq_pos_mul_proj _ Y e hq (hz q hq)
    have hh := hnormal (W q)
    have hpush : mfderiv (J.prod (𝓡∂ 1)) I e q (W q) = V (e q).val :=
      (isInvertible_mfderiv_diffeomorph e (by simp) q).self_apply_inverse _
    rw [hpush] at hh
    erw [hzval q hq] at hh
    change (q.val.1 ∈ A → 0 < Poincare.Manifold.Interval.tangentCoordinateIcc q.val.2 (W q).2) ∧
      (q.val.1 ∉ A → Poincare.Manifold.Interval.tangentCoordinateIcc q.val.2 (W q).2 < 0)
    rw [hh]
    exact ⟨fun hp => mul_pos ha (hin q.val.1 hp), fun hp => mul_neg_of_pos_of_neg ha (hout q.val.1 hp)⟩
  let _ : Subsingleton (HasSmoothBoundary.boundaryE I) := by
    change Subsingleton (EuclideanSpace ℝ (Fin 0))
    infer_instance
  exact mixedPoincareHopf_one_of_collar J hδ hδε Y hY e hi V hV hVf hVi hVI hWn A hs K


theorem mixedPoincareHopf_of_dimension_ge_two
    {d : ℕ}
    {M : Type} [TopologicalSpace M]
    [ChartedSpace (EuclideanHalfSpace (d + 2)) M]
    [IsManifold (𝓡∂ (d + 2)) ∞ M] [T2Space M] [CompactSpace M]
    (V : ∀ x : M, TangentSpace (𝓡∂ (d + 2)) x)
    (hV : ContMDiff (𝓡∂ (d + 2)) (𝓡∂ (d + 2)).tangent ∞
      (fun x => (⟨x, V x⟩ : TangentBundle (𝓡∂ (d + 2)) M)))
    (hVf : {x | V x = 0}.Finite)
    (hVi : ∀ x, V x = 0 → HasContinuousIsolatedZero (𝓡∂ (d + 2)) V x)
    (hVI : ∀ x, V x = 0 → (𝓡∂ (d + 2)).IsInteriorPoint x)
    (A : Set (BoundaryManifold (𝓡∂ (d + 2)) M)) (hA : IsClopen A)
    (hin : ∀ p ∈ A, 0 < (EuclideanSpace.proj (𝕜 := ℝ) (0 : Fin (d + 2))) (V p.val))
    (hout : ∀ p ∉ A, (EuclideanSpace.proj (𝕜 := ℝ) (0 : Fin (d + 2))) (V p.val) < 0)
    (K : Type) [Field K] :
    interiorIndexSum (𝓡∂ (d + 2)) V hVf hVi hVI =
      Poincare.Homology.eulerChar K (TopCat.of M) - Poincare.Homology.eulerChar K (TopCat.of A) := by
  let I := 𝓡∂ (d + 2)
  let B := BoundaryManifold I M
  let J := HasSmoothBoundary.boundaryModel I
  let _ : J.Boundaryless := HasSmoothBoundary.boundaryIBoundaryless
  let _ : IsManifold J ∞ B := BoundaryManifold.isManifold (I := I)
  have hK : IsCompact (I.boundary M) := (I.isClosed_boundary (n := ∞) (by simp)).isCompact
  let _ : CompactSpace B := isCompact_iff_compactSpace.mp hK
  have hn (p : B) : V p.val ≠ 0 := by
    intro hv
    by_cases hp : p ∈ A
    · have hh := hin p hp
      rw [hv] at hh
      exact (lt_irrefl 0) hh
    · have hh := hout p hp
      rw [hv] at hh
      exact (lt_irrefl 0) hh
  obtain ⟨ε, hε, c, _, _, hc0, hci, δ, hδ, hδε, Y, hY, _, e, he, _, hWn⟩ :=
    exists_nonvanishing_boundary_collar_pullback hK V hV hn
  let _ : Fact ((0 : ℝ) < ε) := ⟨hε⟩
  have hi (q : _) (hq : 0 < q.val.2.val) : I.IsInteriorPoint (e q).val := by
    rw [he q]
    exact hci q.val hq
  have hzval (q : _) (hq : q.val.2.val = 0) : (e q).val = q.val.1.val := by
    rw [he q]
    have hqeq : q.val.2 = ⟨0, ⟨le_rfl, hε.le⟩⟩ := Subtype.ext hq
    change c (q.val.1, q.val.2) = q.val.1.val
    rw [hqeq, hc0]
    rfl
  have hz (q : _) (hq : q.val.2.val = 0) : I.IsBoundaryPoint (e q).val :=
    (hzval q hq).symm ▸ q.val.1.property
  have hs (q : _) (hq : q.val.2.val = 0) :
      (q.val.1 ∈ A → 0 < Poincare.Manifold.Interval.tangentCoordinateIcc q.val.2
        (_root_.VectorField.mpullback (J.prod (𝓡∂ 1)) I e (fun y : Y => V y.val) q).2) ∧
      (q.val.1 ∉ A → Poincare.Manifold.Interval.tangentCoordinateIcc q.val.2
        (_root_.VectorField.mpullback (J.prod (𝓡∂ 1)) I e (fun y : Y => V y.val) q).2 < 0) := by
    let W := _root_.VectorField.mpullback (J.prod (𝓡∂ 1)) I e (fun y : Y => V y.val)
    obtain ⟨a, ha, hnormal⟩ := Poincare.Manifold.BoundaryCollar.collar_normal_eq_pos_mul_proj _ Y e hq (hz q hq)
    have hh := hnormal (W q)
    have hpush : mfderiv (J.prod (𝓡∂ 1)) I e q (W q) = V (e q).val :=
      (isInvertible_mfderiv_diffeomorph e (by simp) q).self_apply_inverse _
    rw [hpush] at hh
    erw [hzval q hq] at hh
    change (q.val.1 ∈ A → 0 < Poincare.Manifold.Interval.tangentCoordinateIcc q.val.2 (W q).2) ∧
      (q.val.1 ∉ A → Poincare.Manifold.Interval.tangentCoordinateIcc q.val.2 (W q).2 < 0)
    rw [hh]
    exact ⟨fun hp => mul_pos ha (hin q.val.1 hp), fun hp => mul_neg_of_pos_of_neg ha (hout q.val.1 hp)⟩
  exact mixedPoincareHopf_of_collar J hδ hδε Y hY e hi hz V hV hVf hVi hVI hWn A hA hs K

theorem mixedPoincareHopf
    {n : ℕ}
    {M : Type} [TopologicalSpace M]
    [ChartedSpace (EuclideanHalfSpace (n + 1)) M]
    [IsManifold (𝓡∂ (n + 1)) ∞ M] [T2Space M] [CompactSpace M]
    (V : ∀ x : M, TangentSpace (𝓡∂ (n + 1)) x)
    (hV : ContMDiff (𝓡∂ (n + 1)) (𝓡∂ (n + 1)).tangent ∞
      (fun x => (⟨x, V x⟩ : TangentBundle (𝓡∂ (n + 1)) M)))
    (hVf : {x | V x = 0}.Finite)
    (hVi : ∀ x, V x = 0 → HasContinuousIsolatedZero (𝓡∂ (n + 1)) V x)
    (hVI : ∀ x, V x = 0 → (𝓡∂ (n + 1)).IsInteriorPoint x)
    (A : Set (BoundaryManifold (𝓡∂ (n + 1)) M)) (hA : IsClopen A)
    (hin : ∀ p ∈ A, 0 < (EuclideanSpace.proj (𝕜 := ℝ) (0 : Fin (n + 1))) (V p.val))
    (hout : ∀ p ∉ A, (EuclideanSpace.proj (𝕜 := ℝ) (0 : Fin (n + 1))) (V p.val) < 0)
    (K : Type) [Field K] :
    interiorIndexSum (𝓡∂ (n + 1)) V hVf hVi hVI =
      Poincare.Homology.eulerChar K (TopCat.of M) - Poincare.Homology.eulerChar K (TopCat.of A) := by
  cases n with
  | zero => exact mixedPoincareHopf_one V hV hVf hVi hVI A hin hout K
  | succ d => exact mixedPoincareHopf_of_dimension_ge_two V hV hVf hVi hVI A hA hin hout K

end Poincare.VectorField
