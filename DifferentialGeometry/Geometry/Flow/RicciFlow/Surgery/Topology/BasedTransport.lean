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
  obtain ⟨n, rfl⟩ : ∃ n, k = n + 1 := ⟨k - 1, (Nat.sub_add_cancel (NeZero.pos k)).symm⟩
  rw [pathTransport_class_eq n p]
  exact (Topology.homotopyGroupBasepointMulEquiv n p).map_one

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
  obtain ⟨n, rfl⟩ : ∃ n, k = n + 1 := ⟨k - 1, (Nat.sub_add_cancel (NeZero.pos k)).symm⟩
  induction a using Quotient.inductionOn with
  | h c =>
    simp only [basedHomotopyMap_mk, pathTransport_pathTransportClass,
      pathTransportClass_transport n (p.map f.continuous) (genLoopPostcompose f c),
      pathTransportClass_transport n p c]
    exact congrArg (fun r : GenLoop (Fin (n + 1)) Y (f y) =>
      (⟦r⟧ : HomotopyGroup (Fin (n + 1)) Y (f y)))
      (Topology.genLoopTransport_natural n f p c)

theorem pathTransport_independent [SimplyConnectedSpace X] (p q : Path x y) :
    pathTransport (k := k) p = pathTransport q := by
  obtain ⟨n, rfl⟩ : ∃ n, k = n + 1 := ⟨k - 1, (Nat.sub_add_cancel (NeZero.pos k)).symm⟩
  funext a
  rw [pathTransport_class_eq n p, pathTransport_class_eq n q]
  exact Topology.homotopyGroupTransport_path_independent n p q a

section

open scoped CategoryTheory

private def collapsedCubeSetoid : Setoid (ULift.{u} (I^(Fin 3))) where
  r a b := a = b ∨ (a.down ∈ Cube.boundary (Fin 3) ∧ b.down ∈ Cube.boundary (Fin 3))
  iseqv := by
    constructor
    · intro a
      exact Or.inl rfl
    · intro a b h
      rcases h with h | h
      · exact Or.inl h.symm
      · exact Or.inr h.symm
    · intro a b c hab hbc
      rcases hab with rfl | hab
      · exact hbc
      rcases hbc with rfl | hbc
      · exact Or.inr hab
      · exact Or.inr ⟨hab.1, hbc.2⟩

private abbrev CollapsedCube := Quotient collapsedCubeSetoid.{u}

private def collapsedCubeBase : CollapsedCube.{u} :=
  Quotient.mk _ (ULift.up (fun _ : Fin 3 => 0))

private def collapsedCubeProjection : C(ULift.{u} (I^(Fin 3)), CollapsedCube.{u}) :=
  ⟨Quotient.mk _, continuous_quotient_mk'⟩

private def universalCollapsedLoop :
    GenLoop (Fin 3) CollapsedCube.{u} collapsedCubeBase.{u} :=
  ⟨collapsedCubeProjection.comp ⟨ULift.up, continuous_uliftUp⟩, by
    intro w hw
    exact Quotient.sound (Or.inr ⟨hw, ⟨(0 : Fin 3), Or.inl rfl⟩⟩)⟩

private def collapsedCubeFactor (c : GenLoop (Fin 3) X x) : C(CollapsedCube.{u}, X) where
  toFun := Quotient.lift (fun w => c.val w.down) (by
    intro a b hab
    rcases hab with rfl | ⟨ha, hb⟩
    · rfl
    · exact (c.property _ ha).trans (c.property _ hb).symm)
  continuous_toFun := (c.val.continuous.comp continuous_uliftDown).quotient_lift _

private theorem collapsedCubeFactor_class (c : GenLoop (Fin 3) X x) :
    hurewiczCubeClass (genLoopPostcompose (collapsedCubeFactor c) universalCollapsedLoop) =
      hurewiczCubeClass c := rfl

private theorem cubeClass_natural' {Y : Type u} [TopologicalSpace Y] (f : C(X, Y))
    (c : GenLoop (Fin 3) X x) :
    hurewiczCubeClass (genLoopPostcompose f c) =
      integralHomologyMap 3 f (hurewiczCubeClass c) := by
  let F : IntegralChains X ⟶ IntegralChains Y := integralChainsFunctor.map (TopCat.ofHom f)
  have he :
      (IntegralChains X).liftCycles (hurewiczCubeChain c) 2
        ((ComplexShape.down ℕ).next_eq' (by rfl)) (hurewiczCubeChain_boundary c) ≫
        (IntegralChains X).homologyπ 3 ≫ HomologicalComplex.homologyMap F 3 =
      (IntegralChains Y).liftCycles (hurewiczCubeChain (genLoopPostcompose f c)) 2
        ((ComplexShape.down ℕ).next_eq' (by rfl)) (hurewiczCubeChain_boundary _) ≫
        (IntegralChains Y).homologyπ 3 := by
    rw [HomologicalComplex.homologyπ_naturality, ← CategoryTheory.Category.assoc,
      HomologicalComplex.liftCycles_comp_cyclesMap]
    apply congrArg (fun k : integralCoefficients ⟶ (IntegralChains Y).cycles 3 =>
      k ≫ (IntegralChains Y).homologyπ 3)
    apply (CategoryTheory.cancel_mono ((IntegralChains Y).iCycles 3)).1
    simp only [HomologicalComplex.liftCycles_i]
    exact hurewiczCubeChain_natural f c
  exact (congrArg (fun k : integralCoefficients ⟶ IntegralHomology Y 3 =>
    k (ULift.up 1)) he).symm

private def collapsedCubeHomotopy {c : GenLoop (Fin 3) X x} {d : GenLoop (Fin 3) X y}
    (H : ContinuousMap.Homotopy c.val d.val) (p : Path x y)
    (hH : ∀ t w, w ∈ Cube.boundary (Fin 3) → H (t, w) = p t) :
    ContinuousMap.Homotopy (collapsedCubeFactor c) (collapsedCubeFactor d) where
  toContinuousMap :=
    ⟨fun z => Quotient.lift (fun w => H (z.1, w.down))
        (by
          intro a b hab
          rcases hab with rfl | ⟨ha, hb⟩
          · rfl
          · rw [hH z.1 a.down ha, hH z.1 b.down hb]) z.2,
      by
        apply (isQuotientMap_quotient_mk' (s := collapsedCubeSetoid.{u})).continuous_lift_prod_right
        exact H.continuous.comp
          (continuous_fst.prodMk (continuous_uliftDown.comp continuous_snd))⟩
  map_zero_left := by
    intro z
    induction z using Quotient.inductionOn with
    | h w => exact H.apply_zero w.down
  map_one_left := by
    intro z
    induction z using Quotient.inductionOn with
    | h w => exact H.apply_one w.down

private theorem integralHomologyMap_homotopic' {Y : Type u} [TopologicalSpace Y]
    (n : ℕ) {f g : C(X, Y)} (h : f.Homotopic g) :
    integralHomologyMap n f = integralHomologyMap n g := by
  obtain ⟨H⟩ := h
  exact @TopCat.Homotopy.congr_homologyMap_singularChainComplexFunctor (ModuleCat.{u} ℤ)
      _ _ _ (TopCat.of X) (TopCat.of Y) (TopCat.ofHom f) (TopCat.ofHom g) _ H
        integralCoefficients n

private theorem hurewiczCubeClass_transport (p : Path x y) (c : GenLoop (Fin 3) X x) :
    hurewiczCubeClass (Topology.genLoopTransport 2 p c) = hurewiczCubeClass c := by
  have hhom : (collapsedCubeFactor c).Homotopic
      (collapsedCubeFactor (Topology.genLoopTransport 2 p c)) :=
    ⟨collapsedCubeHomotopy (Topology.cubePathHomotopy 2 p c) p
      (Topology.cubePathHomotopy_boundary 2 p c)⟩
  have hm : integralHomologyMap 3 (collapsedCubeFactor c) =
      integralHomologyMap 3 (collapsedCubeFactor (Topology.genLoopTransport 2 p c)) :=
    integralHomologyMap_homotopic' 3 hhom
  calc hurewiczCubeClass (Topology.genLoopTransport 2 p c)
      = hurewiczCubeClass (genLoopPostcompose
          (collapsedCubeFactor (Topology.genLoopTransport 2 p c)) universalCollapsedLoop) :=
        (collapsedCubeFactor_class (Topology.genLoopTransport 2 p c)).symm
    _ = integralHomologyMap 3 (collapsedCubeFactor (Topology.genLoopTransport 2 p c))
          (hurewiczCubeClass universalCollapsedLoop) :=
        cubeClass_natural' _ _
    _ = integralHomologyMap 3 (collapsedCubeFactor c)
          (hurewiczCubeClass universalCollapsedLoop) :=
        congrArg (fun k => k (hurewiczCubeClass universalCollapsedLoop)) hm.symm
    _ = hurewiczCubeClass (genLoopPostcompose (collapsedCubeFactor c) universalCollapsedLoop) :=
        (cubeClass_natural' _ _).symm
    _ = hurewiczCubeClass c := collapsedCubeFactor_class c

end

theorem hurewiczThree_pathTransport (p : Path x y) (a : HomotopyGroup (Fin 3) X x) :
    hurewiczThree y (pathTransport p a) = hurewiczThree x a := by
  induction a using Quotient.inductionOn with
  | h c =>
    rw [pathTransport_pathTransportClass, pathTransportClass_transport 2 p c]
    exact hurewiczCubeClass_transport p c

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
