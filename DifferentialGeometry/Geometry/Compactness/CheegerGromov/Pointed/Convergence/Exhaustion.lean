import DifferentialGeometry.Geometry.Compactness.CheegerGromov.Pointed.Convergence.Maps
import DifferentialGeometry.Topology.ConnectedExhaustion
import DifferentialGeometry.Topology.Manifold.PartialDiffeomorph

set_option autoImplicit false
noncomputable section
open Filter Set
open scoped Manifold ContDiff Topology

namespace DifferentialGeometry.CheegerGromovCompactness

universe u uE uH

variable {E : Type uE} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]
  {H : Type uH} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]

attribute [local instance] PointedRiemannianManifold.topology
  PointedRiemannianManifold.charted PointedRiemannianManifold.smooth
  PointedRiemannianManifold.t2 PointedRiemannianManifold.sigmaCompact
  PointedRiemannianManifold.t2TangentBundle

theorem PointedRiemannianConvergenceMaps.exists_subsequence_of_eventually_contains_compacts
    {X : PointedRiemannianSeq.{u, uE, uH} I}
    {P : PointedRiemannianManifold.{u, uE, uH} I} [PreconnectedSpace P.M]
    {f : ℕ → ℕ}
    (Phi : ∀ i, PartialDiffeomorph I I P.M (X.obj (f i)).M ∞)
    (hbase : ∀ i, Phi i P.basepoint = (X.obj (f i)).basepoint)
    (hsource : ∀ K : Set P.M, IsCompact K → ∀ᶠ i in atTop, K ⊆ (Phi i).source) :
    ∃ sigma : ℕ → ℕ, StrictMono sigma ∧
      ∃ F : PointedRiemannianConvergenceMaps X P (f ∘ sigma),
        (∀ i, F.map i = Phi (sigma i)) ∧
        (∀ i, IsCompact (closure (F.source i))) ∧
        ∀ i, IsConnected (F.source i) := by
  classical
  let _ : LocallyCompactSpace H := I.locallyCompactSpace
  let _ : LocallyCompactSpace P.M := ChartedSpace.locallyCompactSpace H P.M
  let _ : LocallyConnectedSpace H := I.toHomeomorph.locallyConnectedSpace
  let _ : LocallyConnectedSpace P.M := ChartedSpace.locallyConnectedSpace H P.M
  obtain ⟨U, hU, hcompact, hconn, hp⟩ :=
    (default : CompactExhaustion P.M).exists_connected_open_exhaustion P.basepoint
  have hN : ∀ n, ∃ N, ∀ i ≥ N, U n ⊆ (Phi i).source := by
    intro n
    obtain ⟨N, hN⟩ := eventually_atTop.mp (hsource (closure (U n)) (hcompact n))
    exact ⟨N, fun i hi => subset_closure.trans (hN i hi)⟩
  choose N hN using hN
  let sigma : ℕ → ℕ := Nat.rec (N 0) (fun n j => max (j + 1) (N (n + 1)))
  have hsigma : StrictMono sigma := strictMono_nat_of_lt_succ fun n =>
    (Nat.lt_succ_self (sigma n)).trans_le (le_max_left _ _)
  have hge : ∀ n, N n ≤ sigma n := by
    intro n
    cases n with
    | zero => exact le_rfl
    | succ n => exact le_max_right _ _
  let Psi := fun i => DifferentialGeometry.Topology.PartialDiffeomorph.restrict
    (Phi (sigma i)) (U i) (hU.isOpen i)
  have hPsi : ∀ i, (Psi i).source = U i := by
    intro i
    change (Phi (sigma i)).source ∩ U i = U i
    exact inter_eq_right.mpr (hN i (sigma i) (hge i))
  let F : PointedRiemannianConvergenceMaps X P (f ∘ sigma) := {
    partialDiffeomorph := Psi
    source_exhausts := by simpa only [hPsi] using hU
    base_mem := fun i => by rw [hPsi]; exact hp i
    basepoint_map := fun i => hbase (sigma i) }
  refine ⟨sigma, hsigma, F, fun _ => rfl, ?_, ?_⟩
  · intro i
    change IsCompact (closure (Psi i).source)
    rw [hPsi]
    exact hcompact i
  · intro i
    change IsConnected (Psi i).source
    rw [hPsi]
    exact hconn i

end DifferentialGeometry.CheegerGromovCompactness
