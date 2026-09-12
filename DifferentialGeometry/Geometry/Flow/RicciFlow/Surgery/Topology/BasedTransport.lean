import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.LoopClass
import DifferentialGeometry.Topology.Homotopy.BasepointGroup

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
  obtain ⟨n, rfl⟩ : ∃ n, k = n + 1 := ⟨k - 1, (Nat.sub_add_cancel (NeZero.pos k)).symm⟩
  refine ⟨Quotient.mk _ (Topology.genLoopTransport n p c),
    ⟨Topology.genLoopTransport n p c, rfl,
      ⟨⟨Topology.cubePathHomotopy n p c, Topology.cubePathHomotopy_boundary n p c⟩⟩⟩, ?_⟩
  rintro d ⟨representative, hd, ⟨M⟩⟩
  rw [← hd]
  obtain ⟨F⟩ := Topology.genLoopTransport_extension_unique n p c representative
    M.homotopy.toContinuousMap M.homotopy.apply_zero M.homotopy.apply_one M.boundary
  exact Quotient.sound ⟨F⟩

def pathTransportClass (p : Path x y) (c : GenLoop (Fin k) X x) : HomotopyGroup (Fin k) X y :=
  Classical.choose (exists_unique_pathTransportClass p c)

private theorem pathTransportClass_unique {n : ℕ} {p : Path x y} {c : GenLoop (Fin (n + 1)) X x}
    {d : HomotopyGroup (Fin (n + 1)) X y}
    (hd : ∃ representative : GenLoop (Fin (n + 1)) X y,
      Quotient.mk _ representative = d ∧ Nonempty (MovingCubeHomotopy p c representative)) :
    d = pathTransportClass p c :=
  (Classical.choose_spec (exists_unique_pathTransportClass p c)).2 d hd

private theorem pathTransportClass_transport (n : ℕ) (p : Path x y)
    (c : GenLoop (Fin (n + 1)) X x) :
    pathTransportClass p c = Quotient.mk _ (Topology.genLoopTransport n p c) :=
  (pathTransportClass_unique ⟨Topology.genLoopTransport n p c, rfl,
    ⟨⟨Topology.cubePathHomotopy n p c, Topology.cubePathHomotopy_boundary n p c⟩⟩⟩).symm

private theorem pathTransportClass_eq_homotopyGroupTransport (n : ℕ) (p : Path x y)
    (c : GenLoop (Fin (n + 1)) X x) :
    pathTransportClass p c = Topology.homotopyGroupTransport n p (Quotient.mk _ c) := by
  rw [pathTransportClass_transport, Topology.homotopyGroupTransport]
  rfl

theorem pathTransportClass_homotopic (p : Path x y) {c d : GenLoop (Fin k) X x}
    (h : GenLoop.Homotopic c d) : pathTransportClass p c = pathTransportClass p d := by
  obtain ⟨n, rfl⟩ : ∃ n, k = n + 1 := ⟨k - 1, (Nat.sub_add_cancel (NeZero.pos k)).symm⟩
  rw [pathTransportClass_eq_homotopyGroupTransport, pathTransportClass_eq_homotopyGroupTransport]
  exact Quotient.sound (Topology.genLoopTransport_homotopic n p h)

def pathTransport (p : Path x y) : HomotopyGroup (Fin k) X x → HomotopyGroup (Fin k) X y :=
  Quotient.lift (pathTransportClass p) (fun _ _ h => pathTransportClass_homotopic p h)

theorem pathTransport_pathTransportClass (p : Path x y) (c : GenLoop (Fin k) X x) :
    pathTransport p (Quotient.mk _ c) = pathTransportClass p c := rfl

private theorem pathTransport_class_eq (n : ℕ) (p : Path x y)
    (a : HomotopyGroup (Fin (n + 1)) X x) :
    pathTransport (k := n + 1) p a = Topology.homotopyGroupTransport n p a := by
  induction a using Quotient.inductionOn with
  | h c =>
    rw [pathTransport_pathTransportClass]
    exact pathTransportClass_eq_homotopyGroupTransport n p c

theorem pathTransport_one (p : Path x y) : pathTransport (k := k) p 1 = 1 := by
  sorry

theorem pathTransport_mul (p : Path x y) (a b : HomotopyGroup (Fin k) X x) :
    pathTransport p (a*b) = pathTransport p a * pathTransport p b := by
  obtain ⟨n, rfl⟩ : ∃ n, k = n + 1 := ⟨k - 1, (Nat.sub_add_cancel (NeZero.pos k)).symm⟩
  rw [pathTransport_class_eq n p, pathTransport_class_eq n p, pathTransport_class_eq n p]
  exact Topology.homotopyGroupTransport_mul n p a b

def pathTransportHom (p : Path x y) : HomotopyGroup (Fin k) X x →* HomotopyGroup (Fin k) X y :=
  { toFun := pathTransport p
    map_one' := pathTransport_one p
    map_mul' := pathTransport_mul p }

theorem pathTransport_bijective (p : Path x y) : Function.Bijective (pathTransport (k := k) p) := by
  obtain ⟨n, rfl⟩ : ∃ n, k = n + 1 := ⟨k - 1, (Nat.sub_add_cancel (NeZero.pos k)).symm⟩
  rw [funext_iff.mpr (fun a => pathTransport_class_eq n p a)]
  exact (Topology.homotopyGroupBasepointEquiv n p).bijective

def pathTransportEquiv (p : Path x y) : HomotopyGroup (Fin k) X x ≃* HomotopyGroup (Fin k) X y :=
  MulEquiv.ofBijective (pathTransportHom p) (pathTransport_bijective p)

theorem pathTransport_refl (a : HomotopyGroup (Fin k) X x) :
    pathTransport (Path.refl x) a = a := by
  obtain ⟨n, rfl⟩ : ∃ n, k = n + 1 := ⟨k - 1, (Nat.sub_add_cancel (NeZero.pos k)).symm⟩
  rw [pathTransport_class_eq n (Path.refl x)]
  exact Topology.homotopyGroupTransport_refl n a

theorem pathTransport_trans (p : Path x y) (q : Path y z) (a : HomotopyGroup (Fin k) X x) :
    pathTransport (p.trans q) a = pathTransport q (pathTransport p a) := by
  obtain ⟨n, rfl⟩ : ∃ n, k = n + 1 := ⟨k - 1, (Nat.sub_add_cancel (NeZero.pos k)).symm⟩
  rw [pathTransport_class_eq n (p.trans q), pathTransport_class_eq n p, pathTransport_class_eq n q]
  exact (Topology.homotopyGroupTransport_trans n p q a).symm

theorem pathTransport_natural {Y : Type u} [TopologicalSpace Y] (f : C(X, Y))
    (p : Path x y) (a : HomotopyGroup (Fin k) X x) :
    pathTransport (p.map f.continuous) (basedHomotopyMap f x a) =
      basedHomotopyMap f y (pathTransport p a) := by
  sorry

theorem pathTransport_independent [SimplyConnectedSpace X] (p q : Path x y) :
    pathTransport (k := k) p = pathTransport q := by
  obtain ⟨n, rfl⟩ : ∃ n, k = n + 1 := ⟨k - 1, (Nat.sub_add_cancel (NeZero.pos k)).symm⟩
  funext a
  rw [pathTransport_class_eq n p, pathTransport_class_eq n q]
  exact Topology.homotopyGroupTransport_path_independent n p q a

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
