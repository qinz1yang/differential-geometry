import DifferentialGeometry.Geometry.Connection.Product
import DifferentialGeometry.Geometry.Curvature.CurvatureOperator.Ricci.Basic

noncomputable section
open Bundle
open scoped Manifold ContDiff
open DifferentialGeometry DifferentialGeometry.Geometry.Connection
open DifferentialGeometry.Geometry.Curvature
open Poincare.Geometry.Metric Poincare.Geometry.VectorField Poincare.Geometry.Connection

namespace Poincare.Geometry.Curvature

private def covariantField
    {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [T2Space M]
    [BoundarylessManifold I M]
    (g : SmoothRiemannianMetric I M)
    (X Y : ContMDiffSection I E ∞ (TangentSpace I : M → Type _)) :
    ContMDiffSection I E ∞ (TangentSpace I : M → Type _) where
  toFun := covApply (LeviCivita g) X Y
  contMDiff_toFun := contMDiffOn_univ.mp (covApply_contMDiffOn
    (cov := LeviCivita g) X.contMDiff (by simpa using Y.contMDiff))

variable {E H M F K N : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [T2Space M]
  [BoundarylessManifold I M]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
  [TopologicalSpace K] {J : ModelWithCorners ℝ F K}
  [TopologicalSpace N] [ChartedSpace K N] [IsManifold J ∞ N] [T2Space N]
  [BoundarylessManifold J N]

private theorem riemannSec_product
    (g : SmoothRiemannianMetric I M) (h : SmoothRiemannianMetric J N)
    (X Y Z : ContMDiffSection I E ∞ (TangentSpace I : M → Type _))
    (X' Y' Z' : ContMDiffSection J F ∞ (TangentSpace J : N → Type _)) (x : M × N) :
    riemannSec (LeviCivita (g.prod h)) (productVectorField X X')
      (productVectorField Y Y') (productVectorField Z Z') x =
        (riemannSec (LeviCivita g) X Y Z x.1, riemannSec (LeviCivita h) X' Y' Z' x.2) := by
  have hc (A B : ContMDiffSection I E ∞ (TangentSpace I : M → Type _))
      (A' B' : ContMDiffSection J F ∞ (TangentSpace J : N → Type _)) :
      covApply (LeviCivita (g.prod h)) (productVectorField A A')
          (productVectorField B B') =
        (productVectorField (covariantField g A B) (covariantField h A' B') :
          ∀ y, TangentSpace (I.prod J) y) := by
    funext y
    exact leviCivita_productVectorField g h A B A' B' y
  unfold riemannSec
  rw [hc Y Z Y' Z', hc X Z X' Z']
  change
    leviCivitaConnectionOfMetric (g.prod h)
        (productVectorField (covariantField g Y Z) (covariantField h Y' Z')) x
        (productVectorField X X' x) -
      leviCivitaConnectionOfMetric (g.prod h)
        (productVectorField (covariantField g X Z) (covariantField h X' Z')) x
        (productVectorField Y Y' x) -
      leviCivitaConnectionOfMetric (g.prod h) (productVectorField Z Z') x
        (_root_.VectorField.mlieBracket (I.prod J) (productVectorField X X')
          (productVectorField Y Y') x) = _
  rw [leviCivita_productVectorField, leviCivita_productVectorField,
    leviCivita_productVectorField_apply]
  rw [mlieBracket_productVectorField]
  rfl

theorem riemannOp_productMetric
    (g : SmoothRiemannianMetric I M) (h : SmoothRiemannianMetric J N)
    (x : M × N) (v w z : TangentSpace (I.prod J) x) :
    riemannOp (LeviCivita (g.prod h)) x v w z =
      (riemannOp (LeviCivita g) x.1 v.1 w.1 z.1,
        riemannOp (LeviCivita h) x.2 v.2 w.2 z.2) := by
  let : CompleteSpace E := FiniteDimensional.complete ℝ E
  let : CompleteSpace F := FiniteDimensional.complete ℝ F
  obtain ⟨X, hX⟩ := ContMDiffSection.exists_eq_at (I := I) (F := E)
    (V := (TangentSpace I : M → Type _)) (n := (⊤ : ℕ∞)) x.1 v.1
  obtain ⟨Y, hY⟩ := ContMDiffSection.exists_eq_at (I := I) (F := E)
    (V := (TangentSpace I : M → Type _)) (n := (⊤ : ℕ∞)) x.1 w.1
  obtain ⟨Z, hZ⟩ := ContMDiffSection.exists_eq_at (I := I) (F := E)
    (V := (TangentSpace I : M → Type _)) (n := (⊤ : ℕ∞)) x.1 z.1
  obtain ⟨X', hX'⟩ := ContMDiffSection.exists_eq_at (I := J) (F := F)
    (V := (TangentSpace J : N → Type _)) (n := (⊤ : ℕ∞)) x.2 v.2
  obtain ⟨Y', hY'⟩ := ContMDiffSection.exists_eq_at (I := J) (F := F)
    (V := (TangentSpace J : N → Type _)) (n := (⊤ : ℕ∞)) x.2 w.2
  obtain ⟨Z', hZ'⟩ := ContMDiffSection.exists_eq_at (I := J) (F := F)
    (V := (TangentSpace J : N → Type _)) (n := (⊤ : ℕ∞)) x.2 z.2
  have hv : productVectorField X X' x = v := Prod.ext hX hX'
  have hw : productVectorField Y Y' x = w := Prod.ext hY hY'
  have hz : productVectorField Z Z' x = z := Prod.ext hZ hZ'
  have hp := riemannOp_apply_smooth (LeviCivita (g.prod h))
    (x := x) (productVectorField X X').contMDiff
    (productVectorField Y Y').contMDiff (productVectorField Z Z').contMDiff
  rw [hv, hw, hz, riemannSec_product] at hp
  have hg := riemannOp_apply_smooth (LeviCivita g) (x := x.1)
    X.contMDiff Y.contMDiff Z.contMDiff
  have hh := riemannOp_apply_smooth (LeviCivita h) (x := x.2)
    X'.contMDiff Y'.contMDiff Z'.contMDiff
  rw [hX, hY, hZ] at hg
  rw [hX', hY', hZ'] at hh
  exact hp.trans (congrArg₂ Prod.mk hg.symm hh.symm)

theorem ricciTensor_productMetric
    (g : SmoothRiemannianMetric I M) (h : SmoothRiemannianMetric J N)
    (x : M × N) (v w : TangentSpace (I.prod J) x) :
    ricciTensor (g.prod h) x v w =
      ricciTensor g x.1 v.1 w.1 + ricciTensor h x.2 v.2 w.2 := by
  have he : (ricciEndo (g.prod h) x v w : (E × F) →ₗ[ℝ] (E × F)) =
      LinearMap.prodMap (ricciEndo g x.1 v.1 w.1) (ricciEndo h x.2 v.2 w.2) := by
    apply LinearMap.ext
    intro u
    exact riemannOp_productMetric g h x u v w
  have ht := congrArg (LinearMap.trace ℝ (E × F)) he
  exact ht.trans (LinearMap.trace_prodMap' (ricciEndo g x.1 v.1 w.1)
    (ricciEndo h x.2 v.2 w.2))

end Poincare.Geometry.Curvature
