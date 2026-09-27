import DifferentialGeometry.Geometry.Compactness.CheegerGromov.Pointed.Restriction
import DifferentialGeometry.Geometry.Compactness.CheegerGromov.Pointed.Compactness.MetricExtension
import DifferentialGeometry.Geometry.Metric.Convergence.CovariantDerivative.Norm.ReferenceChange
import DifferentialGeometry.Topology.Manifold.PartialDiffeomorph.Opens

set_option autoImplicit false
noncomputable section
open Set Filter
open scoped Manifold ContDiff Topology

namespace DifferentialGeometry.CheegerGromovCompactness
open DifferentialGeometry.Geometry.Curvature
universe u uE uH
variable {E : Type uE} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]
  {H : Type uH} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
attribute [local instance] PointedRiemannianManifold.topology
  PointedRiemannianManifold.charted PointedRiemannianManifold.smooth
  PointedRiemannianManifold.t2 PointedRiemannianManifold.sigmaCompact
  PointedRiemannianManifold.t2TangentBundle

theorem exists_pointed_metric_convergence_of_pullback_on_open
    (X : PointedRiemannianSeq.{u, uE, uH} I) (L : PointedRiemannianManifold.{u, uE, uH} I)
    (f : ℕ → ℕ) (F : ∀ i, PartialDiffeomorph I I L.M (X.obj (f i)).M ∞)
    (U : TopologicalSpace.Opens L.M) (hpU : L.basepoint ∈ U)
    (hsource : ∀ i, (U : Set L.M) ⊆ (F i).source)
    (hbase : ∀ i, F i L.basepoint = (X.obj (f i)).basepoint)
    (G : ℕ → SmoothRiemannianMetric I U) (g r : SmoothRiemannianMetric I U)
    (hmetric : ∀ i (x : U) (v w : TangentSpace I x),
      (G i).inner x v w = (X.obj (f i)).metric.inner (F i x)
        (mfderiv I I (F i) x v) (mfderiv I I (F i) x w))
    (hconv : MetricCInfConvergenceOnCompacts G g r) :
    let Q : PointedRiemannianManifold I := { L.restrictOpen U hpU with metric := g }
    ∃ Psi : PointedRiemannianConvergenceMaps X Q f,
      (∀ i (x : U), Psi.map i x = F i (x : L.M)) ∧
      ∃ C : MetricConvergenceData Psi,
        ∀ i, C.domain i = CanonicalMetricCompactness.canonicalSourceData Psi i := by
  let : CompleteSpace E := FiniteDimensional.complete ℝ E
  let Q : PointedRiemannianManifold I := { L.restrictOpen U hpU with metric := g }
  let V (i : ℕ) : TopologicalSpace.Opens (X.obj (f i)).M :=
    ⟨F i '' (U : Set L.M), image_opens_isOpen (F i) (hsource i)⟩
  let e (i : ℕ) : U ≃ₘ⟮I, I⟯ V i := PartialDiffeomorph.toOpensDiffeo (F i) (hsource i)
  let _ (i : ℕ) : Nonempty (V i) := ⟨e i ⟨L.basepoint, hpU⟩⟩
  let Psi : PointedRiemannianConvergenceMaps X Q f := {
    partialDiffeomorph := fun i =>
      @PartialDiffeomorph.liftTargetOpen E _ _ H _ I E _ _ H _ I
        U _ _ (X.obj (f i)).M _ _ (V i)
        ⟨e i ⟨L.basepoint, hpU⟩⟩ (e i).toPartialDiffeomorph rfl
    source_exhausts := ⟨fun _ => isOpen_univ, fun _ => subset_univ _,
      fun _ _ => ⟨0, fun _ _ => subset_univ _⟩⟩
    base_mem := fun _ => mem_univ _
    basepoint_map := hbase }
  have hderiv (i : ℕ) (x : U) (v : TangentSpace I x) :
      mfderiv I I (Psi.map i) x v = mfderiv I I (F i) (x : L.M) v := by
    have h := PartialDiffeomorph.mfderiv_liftTargetOpen
      (e i).toPartialDiffeomorph rfl (x := x) (mem_univ _) v
    exact h.trans (PartialDiffeomorph.mfderiv_toOpensDiffeo (F i) (hsource i) x v)
  obtain ⟨C, hcanonical, _href⟩ := exists_canonicalMetricConvergenceData_of_metric_extension
    Psi G (hconv.change_reference g) (by
      intro K _hK
      exact Eventually.of_forall fun i => ⟨univ, isOpen_univ, subset_univ _,
        subset_univ _, fun x _ v w => by
          have h := hmetric i x v w
          exact h.trans (congrArg₂ (fun a b =>
            (X.obj (f i)).metric.inner (F i ((show U from x) : L.M)) a b)
            (hderiv i x v).symm (hderiv i x w).symm)⟩)
  exact ⟨Psi, fun _ _ => rfl, C, hcanonical⟩

end DifferentialGeometry.CheegerGromovCompactness
