import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.LoopClass

noncomputable section

open Set Bundle Manifold
open scoped Topology unitInterval Manifold ContDiff

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

universe u

def sphereCubeVector (x : I^(Fin 2)) : ThreeSpace := by
  classical
  let u : ℝ := (2 * (x 0 : ℝ) - 1) / ((x 0 : ℝ) * (1 - (x 0 : ℝ)))
  let v : ℝ := (2 * (x 1 : ℝ) - 1) / ((x 1 : ℝ) * (1 - (x 1 : ℝ)))
  exact if x ∈ Cube.boundary (Fin 2) then EuclideanSpace.single 2 1 else
    WithLp.toLp 2 ![2*u / (1+u^2+v^2), -2*v / (1+u^2+v^2),
      (u^2+v^2-1) / (1+u^2+v^2)]

theorem sphereCubeVector_norm (x : I^(Fin 2)) : ‖sphereCubeVector x‖ = 1 := by
  classical
  by_cases hb : x ∈ Cube.boundary (Fin 2)
  · simp [sphereCubeVector, hb, PiLp.norm_single]
  let u : ℝ := (2 * (x 0 : ℝ) - 1) / ((x 0 : ℝ) * (1 - (x 0 : ℝ)))
  let v : ℝ := (2 * (x 1 : ℝ) - 1) / ((x 1 : ℝ) * (1 - (x 1 : ℝ)))
  have hd : 1 + u^2 + v^2 ≠ 0 := by nlinarith [sq_nonneg u, sq_nonneg v]
  have hsq : ‖sphereCubeVector x‖^2 = 1 := by
    simp only [sphereCubeVector, if_neg hb]
    change ‖(WithLp.toLp 2 ![2*u / (1+u^2+v^2), -2*v / (1+u^2+v^2),
      (u^2+v^2-1) / (1+u^2+v^2)] : ThreeSpace)‖^2 = 1
    rw [EuclideanSpace.real_norm_sq_eq]
    norm_num [Fin.sum_univ_succ]
    field_simp [hd]
    ring
  nlinarith [norm_nonneg (sphereCubeVector x)]

theorem sphereCubeVector_continuous : Continuous sphereCubeVector := by
  sorry


def sphereCubeParameter : C(I^(Fin 2), Sphere 2) :=
  ⟨fun x => ⟨sphereCubeVector x, by
    simpa only [Sphere, Metric.mem_sphere, dist_zero_right] using sphereCubeVector_norm x⟩,
    sphereCubeVector_continuous.subtype_mk (fun x => by
      simpa only [Sphere, Metric.mem_sphere, dist_zero_right] using sphereCubeVector_norm x)⟩

variable {X : Type u} [TopologicalSpace X] {x : X}

theorem exists_unique_sphereFactor (c : GenLoop (Fin 2) X x) :
    ∃! f : C(Sphere 2, X), f.comp sphereCubeParameter = c.val := by
  sorry

def sphereFactor (c : GenLoop (Fin 2) X x) : C(Sphere 2, X) :=
  Classical.choose (exists_unique_sphereFactor c)

theorem sphereFactor_eq (c : GenLoop (Fin 2) X x) :
    (sphereFactor c).comp sphereCubeParameter = c.val :=
  (Classical.choose_spec (exists_unique_sphereFactor c)).1

theorem sphereFactor_homotopic {c d : GenLoop (Fin 2) X x}
    (h : c.val.HomotopicRel d.val (Cube.boundary (Fin 2))) :
    ContinuousMap.Homotopic (sphereFactor c) (sphereFactor d) := by
  sorry


def forgetBasedSphere (x : X) : HomotopyGroup (Fin 2) X x → FreeHomotopyClass (Sphere 2) X :=
  Quotient.lift (fun c => FreeHomotopyClass.mk (sphereFactor c))
    (fun _ _ h => (FreeHomotopyClass.mk_eq_mk_iff _ _).2 (sphereFactor_homotopic h))

def contractibleLoopInclusion : C(ContractibleContinuousLoop X, ContinuousFreeLoop X) :=
  ⟨Subtype.val, continuous_subtype_val⟩

theorem forgetBasedSphere_one (x : X) : forgetBasedSphere x 1 =
    FreeHomotopyClass.mk (ContinuousMap.const (Sphere 2) x) := by
  rw [HomotopyGroup.one_def]
  change FreeHomotopyClass.mk (sphereFactor (GenLoop.const : GenLoop (Fin 2) X x)) = _
  apply congrArg FreeHomotopyClass.mk
  exact ((Classical.choose_spec (exists_unique_sphereFactor
    (GenLoop.const : GenLoop (Fin 2) X x))).2 (ContinuousMap.const (Sphere 2) x) rfl).symm

theorem sphereFamily_homotopic_const_of_pi2_subsingleton
    (h : ∀ q : X, Subsingleton (HomotopyGroup (Fin 2) X q))
    (f : C(Sphere 2, X)) :
    ∃ q : X, ContinuousMap.Homotopic f (ContinuousMap.const (Sphere 2) q) := by
  classical
  have hz : (0 : I^(Fin 2)) ∈ Cube.boundary (Fin 2) := ⟨0, Or.inl rfl⟩
  let q : X := f (sphereCubeParameter 0)
  let c : GenLoop (Fin 2) X q := ⟨f.comp sphereCubeParameter, by
    intro y hy
    change f (sphereCubeParameter y) = f (sphereCubeParameter 0)
    apply congrArg f
    apply Subtype.ext
    change sphereCubeVector y = sphereCubeVector 0
    simp [sphereCubeVector, hy, hz]⟩
  have hf : sphereFactor c = f :=
    ((Classical.choose_spec (exists_unique_sphereFactor c)).2 f rfl).symm
  have hc : (⟦c⟧ : HomotopyGroup (Fin 2) X q) =
      (1 : HomotopyGroup (Fin 2) X q) := (h q).elim _ _
  refine ⟨q, (FreeHomotopyClass.mk_eq_mk_iff _ _).mp ?_⟩
  have he : forgetBasedSphere q (⟦c⟧ : HomotopyGroup (Fin 2) X q) =
      forgetBasedSphere q (1 : HomotopyGroup (Fin 2) X q) :=
    congrArg (forgetBasedSphere q) hc
  rw [forgetBasedSphere_one] at he
  change FreeHomotopyClass.mk (sphereFactor c) = _ at he
  rwa [hf] at he

theorem exists_unique_cubeAdjunct (c : GenLoop (Fin 3) X x) :
    ∃! A : GenLoop (Fin 2) (BasedContinuousLoop x) (basedConstantLoop x),
      ∀ p : I^(Fin 2), ∀ t : I,
        (A p).1 ((t : ℝ) : Circle) = c ![p 0, p 1, t] := by
  sorry

def cubeAdjunct (c : GenLoop (Fin 3) X x) :
    GenLoop (Fin 2) (BasedContinuousLoop x) (basedConstantLoop x) :=
  Classical.choose (exists_unique_cubeAdjunct c)

theorem cubeAdjunct_apply (c : GenLoop (Fin 3) X x) (p : I^(Fin 2)) (t : I) :
    (cubeAdjunct c p).1 ((t : ℝ) : Circle) = c ![p 0, p 1, t] :=
  (Classical.choose_spec (exists_unique_cubeAdjunct c)).1 p t

theorem cubeAdjunct_homotopic {c d : GenLoop (Fin 3) X x}
    (h : c.val.HomotopicRel d.val (Cube.boundary (Fin 3))) :
    (cubeAdjunct c).val.HomotopicRel (cubeAdjunct d).val (Cube.boundary (Fin 2)) := by
  sorry


def basedLoopAdjunction (x : X) : HomotopyGroup (Fin 3) X x →
    HomotopyGroup (Fin 2) (BasedContinuousLoop x) (basedConstantLoop x) :=
  Quotient.map cubeAdjunct (fun _ _ h => cubeAdjunct_homotopic h)

theorem basedLoopAdjunction_bijective (x : X) : Function.Bijective (basedLoopAdjunction x) := by
  sorry

theorem basedLoopAdjunction_one (x : X) : basedLoopAdjunction x 1 = 1 := by
  sorry

theorem basedLoopAdjunction_mul (a b : HomotopyGroup (Fin 3) X x) :
    basedLoopAdjunction x (a * b) = basedLoopAdjunction x a * basedLoopAdjunction x b := by
  sorry

def basedLoopAdjunctionEquiv (x : X) : HomotopyGroup (Fin 3) X x ≃*
    HomotopyGroup (Fin 2) (BasedContinuousLoop x) (basedConstantLoop x) :=
  MulEquiv.ofBijective
    ({ toFun := basedLoopAdjunction x
       map_one' := basedLoopAdjunction_one x
       map_mul' := basedLoopAdjunction_mul } : HomotopyGroup (Fin 3) X x →*
      HomotopyGroup (Fin 2) (BasedContinuousLoop x) (basedConstantLoop x))
    (basedLoopAdjunction_bijective x)


def freeLoopAdjunction (x : X) : HomotopyGroup (Fin 3) X x →
    HomotopyGroup (Fin 2) (ContinuousFreeLoop X) (constantLoops x) :=
  basedHomotopyMap (basedLoopInclusion x) (basedConstantLoop x) ∘ basedLoopAdjunction x

def freeLoopAdjunctionHom (x : X) : HomotopyGroup (Fin 3) X x →*
    HomotopyGroup (Fin 2) (ContinuousFreeLoop X) (constantLoops x) :=
  (basedHomotopyHom (basedLoopInclusion x) (basedConstantLoop x)).comp
    (basedLoopAdjunctionEquiv x).toMonoidHom

@[simp] theorem freeLoopAdjunctionHom_apply (x : X) (a : HomotopyGroup (Fin 3) X x) :
    freeLoopAdjunctionHom x a = freeLoopAdjunction x a := rfl

theorem freeLoopAdjunction_natural {Y : Type u} [TopologicalSpace Y]
    (f : C(X, Y)) (a : HomotopyGroup (Fin 3) X x) :
    basedHomotopyMap (loopPostcompose f) (constantLoops x) (freeLoopAdjunction x a) =
      freeLoopAdjunction (f x) (basedHomotopyMap f x a) := by
  sorry

variable {M : Type u} [TopologicalSpace M] [ChartedSpace ThreeSpace M]
    [IsManifold ThreeModel ∞ M] [hT2 : T2Space M] [hCompact : CompactSpace M]
    [hConnected : ConnectedSpace M] [hSimplyConnected : SimplyConnectedSpace M]

include hT2 hCompact hConnected hSimplyConnected

theorem rfs_free_loop_class (o : TangentOrientationSection M) (q : M) :
    PathConnectedSpace (ContinuousFreeLoop M) ∧ SimplyConnectedSpace (ContinuousFreeLoop M) ∧
    Function.Bijective (freeLoopAdjunction q) ∧
    Function.Bijective (forgetBasedSphere (constantLoops q)) := by
  sorry

def freeLoopAdjunctionEquiv (o : TangentOrientationSection M) (q : M) :
    HomotopyGroup (Fin 3) M q ≃*
      HomotopyGroup (Fin 2) (ContinuousFreeLoop M) (constantLoops q) :=
  MulEquiv.ofBijective (freeLoopAdjunctionHom q) (rfs_free_loop_class o q).2.2.1

def positiveBasedLoopClass (o : TangentOrientationSection M) (q : M) :
    HomotopyGroup (Fin 2) (ContinuousFreeLoop M) (constantLoops q) :=
  freeLoopAdjunction q (positiveHomotopyClass o q)

def positiveFreeLoopClass (o : TangentOrientationSection M) : FreeSphereClass M :=
  let q : M := Classical.choice inferInstance
  forgetBasedSphere (constantLoops q) (positiveBasedLoopClass o q)

theorem positiveFreeLoopClass_eq (o : TangentOrientationSection M) (q : M) :
    positiveFreeLoopClass o = forgetBasedSphere (constantLoops q) (positiveBasedLoopClass o q) := by
  sorry

theorem positiveFreeLoopClass_nontrivial (o : TangentOrientationSection M) (q : M) :
    positiveFreeLoopClass o ≠ FreeHomotopyClass.mk
      (ContinuousMap.const (Sphere 2) (constantLoops q)) := by
  intro h
  rw [positiveFreeLoopClass_eq o q, ← forgetBasedSphere_one (constantLoops q)] at h
  have hb := (rfs_free_loop_class o q).2.2.2.injective h
  have ha : positiveHomotopyClass o q = 1 := by
    apply (rfs_free_loop_class o q).2.2.1.injective
    exact hb.trans (freeLoopAdjunctionHom q).map_one.symm
  have h10 : (1 : ℤ) = 0 := (positiveHomotopyClass_infiniteOrder o q)
    (by simpa only [zpow_one, zpow_zero] using ha)
  norm_num at h10

theorem every_continuousLoop_contractible (γ : ContinuousFreeLoop M) : IsContractibleLoop γ := by
  sorry

def toContractibleLoops : C(ContinuousFreeLoop M, ContractibleContinuousLoop M) :=
  ⟨fun γ => ⟨γ, every_continuousLoop_contractible γ⟩, continuous_id.subtype_mk _⟩

def positiveFreeContractibleClass (o : TangentOrientationSection M) : FreeContractibleSphereClass M :=
  FreeHomotopyClass.map toContractibleLoops (positiveFreeLoopClass o)

theorem positiveFreeContractibleClass_inclusion (o : TangentOrientationSection M) :
    FreeHomotopyClass.map contractibleLoopInclusion (positiveFreeContractibleClass o) =
      positiveFreeLoopClass o := by
  unfold positiveFreeContractibleClass
  rw [← FreeHomotopyClass.map_comp]
  exact FreeHomotopyClass.map_id _

theorem positiveFreeContractibleClass_nontrivial (o : TangentOrientationSection M) (q : M) :
    positiveFreeContractibleClass o ≠ FreeHomotopyClass.mk
      (ContinuousMap.const (Sphere 2) (⟨constantLoops q, isContractibleLoop_constant q⟩ :
        ContractibleContinuousLoop M)) := by
  intro h
  apply positiveFreeLoopClass_nontrivial o q
  have hh := congrArg (FreeHomotopyClass.map contractibleLoopInclusion) h
  rw [positiveFreeContractibleClass_inclusion, FreeHomotopyClass.map_mk] at hh
  exact hh

variable {N : Type u} [TopologicalSpace N] [ChartedSpace ThreeSpace N]
    [IsManifold ThreeModel ∞ N] [T2Space N] [CompactSpace N]
    [ConnectedSpace N] [SimplyConnectedSpace N]

theorem positiveFreeLoopClass_natural (oM : TangentOrientationSection M)
    (oN : TangentOrientationSection N) (f : C(M, N)) (hf : orientedDegree oM oN f = 1) :
    FreeHomotopyClass.map (loopPostcompose f) (positiveFreeLoopClass oM) =
      positiveFreeLoopClass oN := by
  sorry

theorem positiveFreeContractibleClass_natural (oM : TangentOrientationSection M)
    (oN : TangentOrientationSection N) (f : C(M, N)) (hf : orientedDegree oM oN f = 1) :
    FreeHomotopyClass.map (contractibleLoopPostcompose f) (positiveFreeContractibleClass oM) =
      positiveFreeContractibleClass oN := by
  unfold positiveFreeContractibleClass
  rw [← FreeHomotopyClass.map_comp]
  have hcomp : (contractibleLoopPostcompose f).comp (toContractibleLoops (M := M)) =
      (toContractibleLoops (M := N)).comp (loopPostcompose f) := rfl
  rw [hcomp, FreeHomotopyClass.map_comp, positiveFreeLoopClass_natural oM oN f hf]

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
