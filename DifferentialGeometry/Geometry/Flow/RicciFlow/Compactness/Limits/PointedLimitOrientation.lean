import DifferentialGeometry.Geometry.Compactness.CheegerGromov.Pointed.Convergence.Maps
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.Background
import DifferentialGeometry.Geometry.Metric.Distance.Ball
import DifferentialGeometry.Geometry.Metric.Distance.Finiteness
import DifferentialGeometry.Topology.Manifold.OrientationExhaustion
import DifferentialGeometry.Topology.Manifold.SmoothOrientationCompatible

set_option autoImplicit false

noncomputable section

open Set TopologicalSpace
open DifferentialGeometry.CheegerGromovCompactness
open DifferentialGeometry.Topology.Manifold (SmoothOrientation
  exists_subsequence_smoothOrientation_on_monotone_open_cover)
open scoped Manifold ContDiff

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

universe u

attribute [local instance] PointedRiemannianManifold.topology PointedRiemannianManifold.charted
  PointedRiemannianManifold.smooth

private theorem finrank_threeSpace : Module.finrank ℝ ThreeSpace = 3 := by simp

private theorem nonempty_smoothOrientation_of_tangentOrientationSection {M : Type*}
    [TopologicalSpace M] [ChartedSpace ThreeSpace M] [IsManifold ThreeModel ∞ M]
    (o : TangentOrientationSection M) :
    Nonempty (SmoothOrientation ThreeModel M) := by
  have h3 : Nonempty (DifferentialGeometry.ManifoldOrientation ThreeModel M 3) :=
    ⟨{ dimension_eq := finrank_threeSpace
       orientation := o.orientation
       locally_constant := o.locally_constant }⟩
  obtain ⟨O⟩ := (congrArg (fun n => Nonempty (DifferentialGeometry.ManifoldOrientation
    ThreeModel M n)) finrank_threeSpace).mpr h3
  exact ⟨DifferentialGeometry.Topology.Manifold.smoothOrientationOfManifoldOrientation
    ThreeModel O⟩

private theorem nonempty_tangentOrientationSection_of_smoothOrientation {M : Type*}
    [TopologicalSpace M] [ChartedSpace ThreeSpace M] [IsManifold ThreeModel ∞ M]
    (o : SmoothOrientation ThreeModel M) :
    Nonempty (TangentOrientationSection M) := by
  obtain ⟨O, -⟩ :=
    DifferentialGeometry.Topology.Manifold.exists_manifoldOrientation_eq_of_smoothOrientation
      ThreeModel o
  obtain ⟨O₃⟩ := (congrArg (fun n => Nonempty (DifferentialGeometry.ManifoldOrientation
    ThreeModel M n)) finrank_threeSpace).mp ⟨O⟩
  exact ⟨{ orientation := O₃.orientation
           locally_constant := O₃.locally_constant }⟩

theorem nonempty_tangentOrientationSection_of_pointedConvergence
    {X : PointedRiemannianSeq.{u, 0, 0} ThreeModel}
    {P : PointedRiemannianManifold.{u, 0, 0} ThreeModel}
    {f : ℕ → ℕ} (F : PointedRiemannianConvergenceMaps X P f)
    (o : ∀ n, TangentOrientationSection (X.obj n).M)
    [ConnectedSpace P.M] {V : ℕ → Opens P.M}
    (hV : ∀ k, (V k : Set P.M) = riemannianBallOf P.metric P.basepoint (((k + 1 : ℕ) : ℝ) / 2))
    {N : ℕ → ℕ} (hVF : ∀ k j, N k ≤ j → (V k : Set P.M) ⊆ F.source j) :
    Nonempty (TangentOrientationSection P.M) := by
  have hr : ∀ k : ℕ, (0 : ℝ) < ((k + 1 : ℕ) : ℝ) / 2 := fun k => by positivity
  have hmono : Monotone V := by
    refine monotone_nat_of_le_succ fun k => ?_
    change (V k : Set P.M) ⊆ V (k + 1)
    rw [hV k, hV (k + 1)]
    refine riemannianBallOf_mono _ _ ?_
    refine div_le_div_of_nonneg_right ?_ (by norm_num)
    push_cast
    linarith
  have hcover : ∀ x : P.M, ∃ k, x ∈ V k := by
    intro x
    have hne := riemannianEDistOf_ne_top P.metric P.basepoint x
    obtain ⟨k, hk⟩ := exists_nat_gt (2 * (riemannianEDistOf P.metric P.basepoint x).toReal)
    refine ⟨k, ?_⟩
    change x ∈ (V k : Set P.M)
    rw [hV k]
    change riemannianEDistOf P.metric P.basepoint x < _
    rw [← ENNReal.ofReal_toReal hne, ENNReal.ofReal_lt_ofReal_iff (hr k)]
    push_cast
    linarith
  have hconn : ∀ k, IsPreconnected (V k : Set P.M) := fun k => by
    rw [hV k]
    exact (isPathConnected_riemannianBallOf P.metric P.basepoint (hr k)).isConnected.isPreconnected
  have hbase : ∀ k, P.basepoint ∈ V k := fun k => by
    change P.basepoint ∈ (V k : Set P.M)
    rw [hV k]
    change riemannianEDistOf P.metric P.basepoint P.basepoint < _
    rw [riemannianEDistOf_self]
    exact ENNReal.ofReal_pos.mpr (hr k)
  have hS : ∀ n, Nonempty
      (SmoothOrientation ThreeModel (X.obj n).M) :=
    fun n => nonempty_smoothOrientation_of_tangentOrientationSection (o n)
  let S := fun n => Classical.choice (hS n)
  let oV := fun k => DifferentialGeometry.PartialDiffeomorph.pullbackSmoothOrientation
    (F.partialDiffeomorph (N k)) (hVF k (N k) le_rfl) (S (f (N k)))
  obtain ⟨-, -, O, -⟩ :=
    exists_subsequence_smoothOrientation_on_monotone_open_cover ThreeModel V hmono hcover hconn
      P.basepoint hbase oV
  exact nonempty_tangentOrientationSection_of_smoothOrientation O

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
