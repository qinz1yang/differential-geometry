import DifferentialGeometry.Topology.Homotopy.SphereNaturality
import DifferentialGeometry.Topology.Homotopy.CubePrecomposition

noncomputable section

open ContinuousMap

namespace DifferentialGeometry.Topology

variable {X : Type*} [TopologicalSpace X]

def freeSpherePrecompose (n : ℕ)
    (f : C(Metric.sphere (0 : EuclideanSpace ℝ (Fin (n + 2))) 1,
      Metric.sphere (0 : EuclideanSpace ℝ (Fin (n + 2))) 1)) :
    ZerothHomotopy C(Metric.sphere (0 : EuclideanSpace ℝ (Fin (n + 2))) 1, X) →
      ZerothHomotopy C(Metric.sphere (0 : EuclideanSpace ℝ (Fin (n + 2))) 1, X) :=
  ZerothHomotopy.lift (fun g => ZerothHomotopy.mk (g.comp f))
    (fun {_ _} p => ZerothHomotopy.sound (p.map (continuous_precomp f)))

@[simp] theorem freeSpherePrecompose_mk (n : ℕ)
    (f : C(Metric.sphere (0 : EuclideanSpace ℝ (Fin (n + 2))) 1,
      Metric.sphere (0 : EuclideanSpace ℝ (Fin (n + 2))) 1))
    (g : C(Metric.sphere (0 : EuclideanSpace ℝ (Fin (n + 2))) 1, X)) :
    freeSpherePrecompose n f (ZerothHomotopy.mk g) = ZerothHomotopy.mk (g.comp f) := rfl

theorem freeSpherePrecompose_eq_of_homotopic (n : ℕ)
    {f g : C(Metric.sphere (0 : EuclideanSpace ℝ (Fin (n + 2))) 1,
      Metric.sphere (0 : EuclideanSpace ℝ (Fin (n + 2))) 1)}
    (h : f.Homotopic g) : freeSpherePrecompose (X := X) n f = freeSpherePrecompose n g := by
  funext a
  induction a using ZerothHomotopy.rec with
  | mk a =>
    apply Quotient.sound
    apply (homotopic_iff_joined _ _).mp
    exact (ContinuousMap.Homotopic.refl a).comp h

def homotopyGroupSpherePrecompose [SimplyConnectedSpace X] (n : ℕ) (x : X)
    (f : C(Metric.sphere (0 : EuclideanSpace ℝ (Fin (n + 2))) 1,
      Metric.sphere (0 : EuclideanSpace ℝ (Fin (n + 2))) 1)) :
    HomotopyGroup (Fin (n + 1)) X x → HomotopyGroup (Fin (n + 1)) X x :=
  fun a => (homotopyGroupFreeSphereEquiv n x).symm
    (freeSpherePrecompose n f (homotopyGroupToFreeSphere n x a))

theorem homotopyGroupSpherePrecompose_eq_of_homotopic [SimplyConnectedSpace X] (n : ℕ) (x : X)
    {f g : C(Metric.sphere (0 : EuclideanSpace ℝ (Fin (n + 2))) 1,
      Metric.sphere (0 : EuclideanSpace ℝ (Fin (n + 2))) 1)} (h : f.Homotopic g) :
    homotopyGroupSpherePrecompose n x f = homotopyGroupSpherePrecompose n x g := by
  unfold homotopyGroupSpherePrecompose
  rw [freeSpherePrecompose_eq_of_homotopic n h]

theorem homotopyGroupSpherePrecompose_one [SimplyConnectedSpace X] (n : ℕ) (x : X)
    (f : C(Metric.sphere (0 : EuclideanSpace ℝ (Fin (n + 2))) 1,
      Metric.sphere (0 : EuclideanSpace ℝ (Fin (n + 2))) 1)) :
    homotopyGroupSpherePrecompose n x f 1 = 1 := by
  apply (homotopyGroupFreeSphereEquiv n x).injective
  change homotopyGroupFreeSphereEquiv n x ((homotopyGroupFreeSphereEquiv n x).symm _) = _
  rw [Equiv.apply_symm_apply]
  change freeSpherePrecompose n f (homotopyGroupToFreeSphere n x 1) =
    homotopyGroupToFreeSphere n x 1
  rw [homotopyGroupToFreeSphere_one, freeSpherePrecompose_mk]
  rfl

theorem homotopyGroupSpherePrecompose_id [SimplyConnectedSpace X] (n : ℕ) (x : X) :
    homotopyGroupSpherePrecompose n x (ContinuousMap.id _) = id := by
  funext a
  change (homotopyGroupFreeSphereEquiv n x).symm
    (freeSpherePrecompose n (ContinuousMap.id _) (homotopyGroupFreeSphereEquiv n x a)) = a
  have h : freeSpherePrecompose (X := X) n (ContinuousMap.id _) = id := by
    funext c
    induction c using ZerothHomotopy.rec with
    | mk c => rfl
  rw [h]
  exact (homotopyGroupFreeSphereEquiv n x).symm_apply_apply a

end DifferentialGeometry.Topology

open scoped Topology unitInterval

namespace DifferentialGeometry.Topology

variable {X : Type*} [TopologicalSpace X]

def cubeSphereMap (n : ℕ) (r : C(I^(Fin (n + 1)), I^(Fin (n + 1))))
    (hr : Set.MapsTo r (Cube.boundary (Fin (n + 1))) (Cube.boundary (Fin (n + 1)))) :
    C(Metric.sphere (0 : EuclideanSpace ℝ (Fin (n + 2))) 1,
      Metric.sphere (0 : EuclideanSpace ℝ (Fin (n + 2))) 1) :=
  (genLoopSphereHomeomorph n (cubeSphereBasepoint n)
    ⟨(cubeSphereProjection n).comp r,
      fun v hv => cubeSphereProjection_boundary n (r v) (hr hv)⟩).val

@[simp] theorem cubeSphereMap_projection (n : ℕ)
    (r : C(I^(Fin (n + 1)), I^(Fin (n + 1))))
    (hr : Set.MapsTo r (Cube.boundary (Fin (n + 1))) (Cube.boundary (Fin (n + 1))))
    (v : I^(Fin (n + 1))) :
    cubeSphereMap n r hr (cubeSphereProjection n v) = cubeSphereProjection n (r v) :=
  genLoopSphereHomeomorph_projection n (cubeSphereBasepoint n) _ v

@[simp] theorem cubeSphereMap_basepoint (n : ℕ)
    (r : C(I^(Fin (n + 1)), I^(Fin (n + 1))))
    (hr : Set.MapsTo r (Cube.boundary (Fin (n + 1))) (Cube.boundary (Fin (n + 1)))) :
    cubeSphereMap n r hr (cubeSphereBasepoint n) = cubeSphereBasepoint n :=
  (genLoopSphereHomeomorph n (cubeSphereBasepoint n) _).property

theorem genLoopSphereHomeomorph_precompose (n : ℕ)
    (r : C(I^(Fin (n + 1)), I^(Fin (n + 1))))
    (hr : Set.MapsTo r (Cube.boundary (Fin (n + 1))) (Cube.boundary (Fin (n + 1))))
    (x : X) (p : GenLoop (Fin (n + 1)) X x) :
    (genLoopSphereHomeomorph n x (genLoopPrecompose r hr p)).val =
      (genLoopSphereHomeomorph n x p).val.comp (cubeSphereMap n r hr) := by
  ext z
  obtain ⟨v, rfl⟩ := cubeSphereProjection_surjective n z
  rw [ContinuousMap.comp_apply, cubeSphereMap_projection,
    genLoopSphereHomeomorph_projection, genLoopSphereHomeomorph_projection]
  rfl

theorem homotopyGroupSpherePrecompose_eq_cube [SimplyConnectedSpace X] (n : ℕ)
    (r : C(I^(Fin (n + 1)), I^(Fin (n + 1))))
    (hr : Set.MapsTo r (Cube.boundary (Fin (n + 1))) (Cube.boundary (Fin (n + 1))))
    (x : X) :
    homotopyGroupSpherePrecompose n x (cubeSphereMap n r hr) =
      homotopyGroupPrecompose r hr x := by
  funext a
  induction a using Quotient.inductionOn with
  | h p =>
    apply (homotopyGroupFreeSphereEquiv n x).injective
    change (homotopyGroupFreeSphereEquiv n x) ((homotopyGroupFreeSphereEquiv n x).symm _) = _
    rw [Equiv.apply_symm_apply]
    change ZerothHomotopy.mk _ = ZerothHomotopy.mk _
    exact congrArg ZerothHomotopy.mk (genLoopSphereHomeomorph_precompose n r hr x p).symm

def homotopyGroupCubeSpherePrecomposeHom [SimplyConnectedSpace X] (n : ℕ)
    (i : Fin (n + 1)) (r : C(I^(Fin (n + 1)), I^(Fin (n + 1))))
    (hr : Set.MapsTo r (Cube.boundary (Fin (n + 1))) (Cube.boundary (Fin (n + 1))))
    (hu : ∀ v t, r (Function.update v i t) = Function.update (r v) i t)
    (x : X) : HomotopyGroup (Fin (n + 1)) X x →* HomotopyGroup (Fin (n + 1)) X x where
  toFun := homotopyGroupSpherePrecompose n x (cubeSphereMap n r hr)
  map_one' := homotopyGroupSpherePrecompose_one n x _
  map_mul' a b := by
    rw [homotopyGroupSpherePrecompose_eq_cube]
    exact (homotopyGroupPrecomposeHom i r hr hu x).map_mul a b

theorem homotopyGroupSpherePrecompose_mul_of_homotopic_cube
    [SimplyConnectedSpace X] (n : ℕ) (i : Fin (n + 1))
    (r : C(I^(Fin (n + 1)), I^(Fin (n + 1))))
    (hr : Set.MapsTo r (Cube.boundary (Fin (n + 1))) (Cube.boundary (Fin (n + 1))))
    (hu : ∀ v t, r (Function.update v i t) = Function.update (r v) i t)
    (x : X)
    {f : C(Metric.sphere (0 : EuclideanSpace ℝ (Fin (n + 2))) 1,
      Metric.sphere (0 : EuclideanSpace ℝ (Fin (n + 2))) 1)}
    (hf : f.Homotopic (cubeSphereMap n r hr))
    (a b : HomotopyGroup (Fin (n + 1)) X x) :
    homotopyGroupSpherePrecompose n x f (a * b) =
      homotopyGroupSpherePrecompose n x f a * homotopyGroupSpherePrecompose n x f b := by
  rw [homotopyGroupSpherePrecompose_eq_of_homotopic n x hf]
  exact (homotopyGroupCubeSpherePrecomposeHom n i r hr hu x).map_mul a b


theorem homotopyGroupSpherePrecompose_mul_of_homotopic_suspension
    [SimplyConnectedSpace X] (n : ℕ) (i : Fin (n + 1))
    (r : C(I^({j : Fin (n + 1) // j ≠ i}), I^({j : Fin (n + 1) // j ≠ i})))
    (hr : Set.MapsTo r (Cube.boundary {j : Fin (n + 1) // j ≠ i})
      (Cube.boundary {j : Fin (n + 1) // j ≠ i}))
    (x : X)
    {f : C(Metric.sphere (0 : EuclideanSpace ℝ (Fin (n + 2))) 1,
      Metric.sphere (0 : EuclideanSpace ℝ (Fin (n + 2))) 1)}
    (hf : f.Homotopic (cubeSphereMap n (Cube.suspensionAt i r)
      (Cube.suspensionAt_mapsTo_boundary i r hr)))
    (a b : HomotopyGroup (Fin (n + 1)) X x) :
    homotopyGroupSpherePrecompose n x f (a * b) =
      homotopyGroupSpherePrecompose n x f a * homotopyGroupSpherePrecompose n x f b :=
  homotopyGroupSpherePrecompose_mul_of_homotopic_cube n i (Cube.suspensionAt i r)
    (Cube.suspensionAt_mapsTo_boundary i r hr) (Cube.suspensionAt_update i r) x hf a b

end DifferentialGeometry.Topology

namespace DifferentialGeometry.Topology

variable {X : Type*} [TopologicalSpace X]

theorem freeSpherePrecompose_comp (n : ℕ)
    (f g : C(Metric.sphere (0 : EuclideanSpace ℝ (Fin (n + 2))) 1,
      Metric.sphere (0 : EuclideanSpace ℝ (Fin (n + 2))) 1)) :
    freeSpherePrecompose (X := X) n (g.comp f) =
      freeSpherePrecompose n f ∘ freeSpherePrecompose n g := by
  funext a
  induction a using ZerothHomotopy.rec with
  | mk a => rfl

theorem homotopyGroupSpherePrecompose_comp [SimplyConnectedSpace X] (n : ℕ) (x : X)
    (f g : C(Metric.sphere (0 : EuclideanSpace ℝ (Fin (n + 2))) 1,
      Metric.sphere (0 : EuclideanSpace ℝ (Fin (n + 2))) 1)) :
    homotopyGroupSpherePrecompose n x (g.comp f) =
      homotopyGroupSpherePrecompose n x f ∘ homotopyGroupSpherePrecompose n x g := by
  funext a
  unfold homotopyGroupSpherePrecompose
  change (homotopyGroupFreeSphereEquiv n x).symm _ =
    (homotopyGroupFreeSphereEquiv n x).symm
      (freeSpherePrecompose n f ((homotopyGroupFreeSphereEquiv n x)
        ((homotopyGroupFreeSphereEquiv n x).symm _)))
  rw [Equiv.apply_symm_apply, freeSpherePrecompose_comp]
  rfl

theorem homotopyGroupSpherePrecompose_homotopyEquiv [SimplyConnectedSpace X]
    (n : ℕ) (x : X)
    (e : ContinuousMap.HomotopyEquiv
      (Metric.sphere (0 : EuclideanSpace ℝ (Fin (n + 2))) 1)
      (Metric.sphere (0 : EuclideanSpace ℝ (Fin (n + 2))) 1)) :
    Function.Bijective (homotopyGroupSpherePrecompose n x e.toFun) := by
  let T := homotopyGroupSpherePrecompose n x e.toFun
  let S := homotopyGroupSpherePrecompose n x e.invFun
  have hleft : T ∘ S = id := by
    dsimp [T, S]
    rw [← homotopyGroupSpherePrecompose_comp,
      homotopyGroupSpherePrecompose_eq_of_homotopic n x e.left_inv,
      homotopyGroupSpherePrecompose_id]
  have hright : S ∘ T = id := by
    dsimp [T, S]
    rw [← homotopyGroupSpherePrecompose_comp,
      homotopyGroupSpherePrecompose_eq_of_homotopic n x e.right_inv,
      homotopyGroupSpherePrecompose_id]
  exact ⟨(show Function.LeftInverse S T from congrFun hright).injective,
    (show Function.RightInverse S T from congrFun hleft).surjective⟩

end DifferentialGeometry.Topology
