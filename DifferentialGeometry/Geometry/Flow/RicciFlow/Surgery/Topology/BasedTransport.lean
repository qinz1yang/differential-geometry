import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.LoopClass

noncomputable section

open Set Bundle Manifold
open scoped Topology unitInterval Manifold ContDiff

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

universe u

variable {X : Type u} [TopologicalSpace X] {x y z : X} {k : ℕ} [NeZero k]

structure MovingCubeHomotopy (p : Path x y)
    (c : GenLoop (Fin k) X x) (d : GenLoop (Fin k) X y) where
  homotopy : ContinuousMap.Homotopy c.val d.val
  boundary : ∀ t : I, ∀ w ∈ Cube.boundary (Fin k), homotopy (t, w) = p t

theorem exists_unique_pathTransportClass (p : Path x y) (c : GenLoop (Fin k) X x) :
    ∃! d : HomotopyGroup (Fin k) X y,
      ∃ representative : GenLoop (Fin k) X y,
        Quotient.mk _ representative = d ∧ Nonempty (MovingCubeHomotopy p c representative) := by
  sorry

def pathTransportClass (p : Path x y) (c : GenLoop (Fin k) X x) : HomotopyGroup (Fin k) X y :=
  Classical.choose (exists_unique_pathTransportClass p c)

theorem pathTransportClass_homotopic (p : Path x y) {c d : GenLoop (Fin k) X x}
    (h : GenLoop.Homotopic c d) : pathTransportClass p c = pathTransportClass p d := by
  sorry

def pathTransport (p : Path x y) : HomotopyGroup (Fin k) X x → HomotopyGroup (Fin k) X y :=
  Quotient.lift (pathTransportClass p) (fun _ _ h => pathTransportClass_homotopic p h)

theorem pathTransport_one (p : Path x y) : pathTransport (k := k) p 1 = 1 := by
  sorry

theorem pathTransport_mul (p : Path x y) (a b : HomotopyGroup (Fin k) X x) :
    pathTransport p (a*b) = pathTransport p a * pathTransport p b := by
  sorry

def pathTransportHom (p : Path x y) : HomotopyGroup (Fin k) X x →* HomotopyGroup (Fin k) X y :=
  { toFun := pathTransport p
    map_one' := pathTransport_one p
    map_mul' := pathTransport_mul p }

theorem pathTransport_bijective (p : Path x y) : Function.Bijective (pathTransport (k := k) p) := by
  sorry

def pathTransportEquiv (p : Path x y) : HomotopyGroup (Fin k) X x ≃* HomotopyGroup (Fin k) X y :=
  MulEquiv.ofBijective (pathTransportHom p) (pathTransport_bijective p)

theorem pathTransport_refl (a : HomotopyGroup (Fin k) X x) :
    pathTransport (Path.refl x) a = a := by
  sorry

theorem pathTransport_trans (p : Path x y) (q : Path y z) (a : HomotopyGroup (Fin k) X x) :
    pathTransport (p.trans q) a = pathTransport q (pathTransport p a) := by
  sorry

theorem pathTransport_natural {Y : Type u} [TopologicalSpace Y] (f : C(X, Y))
    (p : Path x y) (a : HomotopyGroup (Fin k) X x) :
    pathTransport (p.map f.continuous) (basedHomotopyMap f x a) =
      basedHomotopyMap f y (pathTransport p a) := by
  sorry

theorem pathTransport_independent [SimplyConnectedSpace X] (p q : Path x y) :
    pathTransport (k := k) p = pathTransport q := by
  sorry

theorem hurewiczThree_pathTransport (p : Path x y) (a : HomotopyGroup (Fin 3) X x) :
    hurewiczThree y (pathTransport p a) = hurewiczThree x a := by
  sorry

variable {M : Type u} [TopologicalSpace M] [ChartedSpace ThreeSpace M]
    [IsManifold ThreeModel ∞ M] [T2Space M] [CompactSpace M]
    [ConnectedSpace M] [SimplyConnectedSpace M]

theorem positiveHomotopyClass_pathTransport (o : TangentOrientationSection M)
    {q q' : M} (p : Path q q') :
    pathTransport p (positiveHomotopyClass o q) = positiveHomotopyClass o q' := by
  apply (rfs_homotopy_groups o q').2.injective
  rw [hurewiczThree_pathTransport, positiveHomotopyClass_hurewicz,
    positiveHomotopyClass_hurewicz]

variable {N : Type u} [TopologicalSpace N] [ChartedSpace ThreeSpace N]
    [IsManifold ThreeModel ∞ N] [T2Space N] [CompactSpace N]
    [ConnectedSpace N] [SimplyConnectedSpace N]

theorem positiveHomotopyClass_degree_one_to_basepoint (oM : TangentOrientationSection M)
    (oN : TangentOrientationSection N) (f : C(M, N)) (hf : orientedDegree oM oN f = 1)
    (p : M) (q : N) (path : Path (f p) q) :
    pathTransport path (basedHomotopyMap f p (positiveHomotopyClass oM p)) =
      positiveHomotopyClass oN q := by
  rw [rfs_degree_class_transport, hf, zpow_one, positiveHomotopyClass_pathTransport]

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
