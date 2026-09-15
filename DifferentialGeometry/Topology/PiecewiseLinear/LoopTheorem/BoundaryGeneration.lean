import DifferentialGeometry.Topology.FundamentalGroup.Sphere
import DifferentialGeometry.Topology.Cell.Coordinates
import DifferentialGeometry.Topology.PiecewiseLinear.LoopTheorem.CellAttachmentKernel
import DifferentialGeometry.Topology.PiecewiseLinear.LoopTheorem.SingularCell
import DifferentialGeometry.Topology.PiecewiseLinear.SphereSchoenflies
import Mathlib.Algebra.Group.Subgroup.Ker
import Mathlib.Data.List.FinRange

open Set
open scoped ContinuousMap

namespace DifferentialGeometry.Topology

universe u

open Classical in
noncomputable def attachedTwoCellGeometricGeneratorLoopAtLeft
    {Y : Type u} [TopologicalSpace Y] {X D : Set Y}
    (e : ClosedCell 2 ≃ₜ D)
    (hboundary : ∀ d : ClosedCell 2, (e d : Y) ∈ X ↔
      ‖(d : EuclideanSpace ℝ (Fin 2))‖ = 1)
    (x₀ : AttachedCellUnion X D)
    (hx₀ : x₀ ∈ attachedCellOuter (X := X) e ∩ attachedCellInner X D) :
    basedCircleLoop
      (VanKampen.leftBasepoint (attachedCellOuter (X := X) e) x₀ hx₀.1) where
  val := (attachedTwoCellGeometricGeneratorLoop e hboundary x₀ hx₀).1
  property := (attachedTwoCellGeometricGeneratorLoop e hboundary x₀ hx₀).2.trans
    (VanKampen.interToLeft_overlapBasepoint
      (attachedCellOuter (X := X) e) (attachedCellInner X D) x₀ hx₀)

theorem attachedTwoCellGeometricGeneratorLoopAtLeft_mk
    {Y : Type u} [TopologicalSpace Y] {X D : Set Y}
    (e : ClosedCell 2 ≃ₜ D)
    (hboundary : ∀ d : ClosedCell 2, (e d : Y) ∈ X ↔
      ‖(d : EuclideanSpace ℝ (Fin 2))‖ = 1)
    (x₀ : AttachedCellUnion X D)
    (hx₀ : x₀ ∈ attachedCellOuter (X := X) e ∩ attachedCellInner X D) :
    Path.Homotopic.Quotient.mk
        (circleToPath (attachedTwoCellGeometricGeneratorLoopAtLeft e hboundary x₀ hx₀)) =
      (VanKampen.fundamentalGroupInterToLeft
        (attachedCellOuter (X := X) e) (attachedCellInner X D) x₀ hx₀).hom
        (attachedCellOverlapTwoFundamentalGroupGenerator e hboundary
          (VanKampen.overlapBasepoint
            (attachedCellOuter (X := X) e) (attachedCellInner X D) x₀ hx₀)) := by
  exact eq_of_heq
    (attachedTwoCellGeometricGeneratorLoop_mk_heq e hboundary x₀ hx₀)

theorem attachedTwoCellKernelGeneratorLoop_homotopic_boundaryLoop
    {Y : Type u} [TopologicalSpace Y] {X D : Set Y}
    (e : ClosedCell 2 ≃ₜ D) (hX : IsClosed X) (hD : IsClosed D)
    (hboundary : ∀ d : ClosedCell 2, (e d : Y) ∈ X ↔
      ‖(d : EuclideanSpace ℝ (Fin 2))‖ = 1)
    (x₀ : AttachedCellUnion X D)
    (hx₀ : x₀ ∈ attachedCellOuter (X := X) e ∩ attachedCellInner X D) :
    (attachedTwoCellKernelGeneratorLoop e hboundary x₀ hx₀).1.Homotopic
      (FreeLoop.postcompose (attachedCellBaseToOuter e hboundary)
        (attachedTwoCellBoundaryLoop e hX hD hboundary x₀ hx₀)) := by
  have hclasses : Path.Homotopic.Quotient.mk
        (circleToPath (attachedTwoCellKernelGeneratorLoop e hboundary x₀ hx₀)) =
      Path.Homotopic.Quotient.mk
        (circleToPath
          (attachedTwoCellGeometricGeneratorLoopAtLeft e hboundary x₀ hx₀)) :=
    (attachedTwoCellKernelGeneratorLoop_mk e hboundary x₀ hx₀).trans
      (attachedTwoCellGeometricGeneratorLoopAtLeft_mk e hboundary x₀ hx₀).symm
  have hpaths := Path.Homotopic.Quotient.eq.mp hclasses
  have hloops := pathToCircle_homotopic hpaths
  have hkernel := congrArg Subtype.val
    ((basedPathCircleHomeomorph _).right_inv
      (attachedTwoCellKernelGeneratorLoop e hboundary x₀ hx₀))
  have hgeometric := congrArg Subtype.val
    ((basedPathCircleHomeomorph _).right_inv
      (attachedTwoCellGeometricGeneratorLoopAtLeft e hboundary x₀ hx₀))
  change pathToCircle
      (circleToPath (attachedTwoCellKernelGeneratorLoop e hboundary x₀ hx₀)) =
    (attachedTwoCellKernelGeneratorLoop e hboundary x₀ hx₀).1 at hkernel
  change pathToCircle
      (circleToPath
        (attachedTwoCellGeometricGeneratorLoopAtLeft e hboundary x₀ hx₀)) =
    (attachedTwoCellGeometricGeneratorLoopAtLeft e hboundary x₀ hx₀).1 at hgeometric
  rw [hkernel, hgeometric] at hloops
  exact hloops.trans
    (attachedTwoCellGeometricGeneratorLoop_homotopic_boundaryLoop
      e hX hD hboundary x₀ hx₀)

open Classical in
theorem ker_fundamentalGroupMap_attachedCellOuter_eq_normalClosure
    {Y : Type u} [TopologicalSpace Y] [T1Space Y]
    {X D : Set Y} [PathConnectedSpace X]
    (e : ClosedCell 2 ≃ₜ D) (hX : IsClosed X) (hD : IsClosed D)
    (hboundary : ∀ d : ClosedCell 2, (e d : Y) ∈ X ↔
      ‖(d : EuclideanSpace ℝ (Fin 2))‖ = 1)
    (x₀ : AttachedCellUnion X D)
    (hx₀ : x₀ ∈ attachedCellOuter (X := X) e ∩ attachedCellInner X D) :
    MonoidHom.ker (FundamentalGroup.map
        (VanKampen.subsetToAmbient (attachedCellOuter (X := X) e))
        (VanKampen.leftBasepoint (attachedCellOuter (X := X) e) x₀ hx₀.1)) =
      Subgroup.normalClosure
        ({Path.Homotopic.Quotient.mk
            (circleToPath (attachedTwoCellKernelGeneratorLoop e hboundary x₀ hx₀))} :
          Set (FundamentalGroup (attachedCellOuter (X := X) e)
            (VanKampen.leftBasepoint
              (attachedCellOuter (X := X) e) x₀ hx₀.1))) := by
  have hmaps :
      (VanKampen.fundamentalGroupLeftToAmbient
        (attachedCellOuter (X := X) e) x₀ hx₀.1).hom =
      FundamentalGroup.map
        (VanKampen.subsetToAmbient (attachedCellOuter (X := X) e))
        (VanKampen.leftBasepoint (attachedCellOuter (X := X) e) x₀ hx₀.1) := by
    ext g
    exact eq_of_heq
      (VanKampen.fundamentalGroup_mapOfEq_heq_map
        (VanKampen.subsetToAmbient (attachedCellOuter (X := X) e))
        (VanKampen.leftBasepoint (attachedCellOuter (X := X) e) x₀ hx₀.1) x₀
        (VanKampen.leftBasepoint_toAmbient
          (attachedCellOuter (X := X) e) x₀ hx₀.1) g)
  calc
    MonoidHom.ker (FundamentalGroup.map
        (VanKampen.subsetToAmbient (attachedCellOuter (X := X) e))
        (VanKampen.leftBasepoint (attachedCellOuter (X := X) e) x₀ hx₀.1)) =
        MonoidHom.ker
          (VanKampen.fundamentalGroupLeftToAmbient
            (attachedCellOuter (X := X) e) x₀ hx₀.1).hom :=
      congrArg MonoidHom.ker hmaps.symm
    _ = Subgroup.normalClosure
        ({(VanKampen.fundamentalGroupInterToLeft
            (attachedCellOuter (X := X) e) (attachedCellInner X D) x₀ hx₀).hom
            (attachedCellOverlapTwoFundamentalGroupGenerator e hboundary
              (VanKampen.overlapBasepoint
                (attachedCellOuter (X := X) e) (attachedCellInner X D) x₀ hx₀))} :
          Set (FundamentalGroup (attachedCellOuter (X := X) e)
            (VanKampen.leftBasepoint
              (attachedCellOuter (X := X) e) x₀ hx₀.1))) :=
      ker_fundamentalGroup_attachedCellOuterToUnion_eq_normalClosure
        e hX hD hboundary x₀ hx₀
    _ = Subgroup.normalClosure
        ({Path.Homotopic.Quotient.mk
            (circleToPath (attachedTwoCellKernelGeneratorLoop e hboundary x₀ hx₀))} :
          Set (FundamentalGroup (attachedCellOuter (X := X) e)
            (VanKampen.leftBasepoint
              (attachedCellOuter (X := X) e) x₀ hx₀.1))) := by
      rw [attachedTwoCellKernelGeneratorLoop_mk]

open Classical in
theorem surjective_fundamentalGroupMap_attachedCellOuter
    {Y : Type u} [TopologicalSpace Y] [T1Space Y]
    {X D : Set Y} [PathConnectedSpace X]
    (e : ClosedCell 2 ≃ₜ D) (hX : IsClosed X) (hD : IsClosed D)
    (hboundary : ∀ d : ClosedCell 2, (e d : Y) ∈ X ↔
      ‖(d : EuclideanSpace ℝ (Fin 2))‖ = 1)
    (x₀ : AttachedCellUnion X D)
    (hx₀ : x₀ ∈ attachedCellOuter (X := X) e ∩ attachedCellInner X D) :
    Function.Surjective (FundamentalGroup.map
      (VanKampen.subsetToAmbient (attachedCellOuter (X := X) e))
      (VanKampen.leftBasepoint (attachedCellOuter (X := X) e) x₀ hx₀.1)) := by
  have hmaps :
      (VanKampen.fundamentalGroupLeftToAmbient
        (attachedCellOuter (X := X) e) x₀ hx₀.1).hom =
      FundamentalGroup.map
        (VanKampen.subsetToAmbient (attachedCellOuter (X := X) e))
        (VanKampen.leftBasepoint (attachedCellOuter (X := X) e) x₀ hx₀.1) := by
    ext g
    exact eq_of_heq
      (VanKampen.fundamentalGroup_mapOfEq_heq_map
        (VanKampen.subsetToAmbient (attachedCellOuter (X := X) e))
        (VanKampen.leftBasepoint (attachedCellOuter (X := X) e) x₀ hx₀.1) x₀
        (VanKampen.leftBasepoint_toAmbient
          (attachedCellOuter (X := X) e) x₀ hx₀.1) g)
  rw [← hmaps]
  exact surjective_fundamentalGroup_attachedCellOuterToUnion
    e hX hD hboundary x₀ hx₀

theorem pathHomotopicQuotient_map_trans
    {A C : Type u} [TopologicalSpace A] [TopologicalSpace C]
    {a₀ a₁ a₂ : A} (p : Path.Homotopic.Quotient a₀ a₁)
    (q : Path.Homotopic.Quotient a₁ a₂) (f : C(A, C)) :
    Path.Homotopic.Quotient.map (p.trans q) f =
      (Path.Homotopic.Quotient.map p f).trans
        (Path.Homotopic.Quotient.map q f) := by
  induction p, q using Path.Homotopic.Quotient.ind₂ with
  | mk p q => exact congrArg Path.Homotopic.Quotient.mk (Path.map_trans p q f.continuous)

theorem pathHomotopicQuotient_map_symm
    {A C : Type u} [TopologicalSpace A] [TopologicalSpace C]
    {a₀ a₁ : A} (p : Path.Homotopic.Quotient a₀ a₁) (f : C(A, C)) :
    Path.Homotopic.Quotient.map p.symm f =
      (Path.Homotopic.Quotient.map p f).symm := by
  induction p using Path.Homotopic.Quotient.ind with
  | mk p => rfl

theorem fundamentalGroupChangeBasepoint_map
    {A C : Type u} [TopologicalSpace A] [TopologicalSpace C]
    {a₀ a₁ : A} (f : C(A, C)) (q : Path a₀ a₁)
    (g : FundamentalGroup A a₁) :
    fundamentalGroupChangeBasepoint (q.map f.continuous)
        (FundamentalGroup.map f a₁ g) =
      FundamentalGroup.map f a₀ (fundamentalGroupChangeBasepoint q g) := by
  rw [fundamentalGroupChangeBasepoint_apply, fundamentalGroupChangeBasepoint_apply]
  change (Path.Homotopic.Quotient.trans
      (Path.Homotopic.Quotient.mk (q.map f.continuous))
      (FundamentalGroup.map f a₁ g)).trans
        (Path.Homotopic.Quotient.symm
          (Path.Homotopic.Quotient.mk (q.map f.continuous))) = _
  change ((Path.Homotopic.Quotient.mk (q.map f.continuous)).trans
      (Path.Homotopic.Quotient.map g f)).trans
        (Path.Homotopic.Quotient.mk (q.map f.continuous)).symm =
    Path.Homotopic.Quotient.map
      (((Path.Homotopic.Quotient.mk q).trans g).trans
        (Path.Homotopic.Quotient.mk q).symm) f
  rw [pathHomotopicQuotient_map_trans, pathHomotopicQuotient_map_trans,
    pathHomotopicQuotient_map_symm, Path.Homotopic.Quotient.mk_map]

open Classical in
theorem FreeLoop.conjugacyClass_postcompose
    {A C : Type u} [TopologicalSpace A] [TopologicalSpace C]
    [PathConnectedSpace A] [PathConnectedSpace C]
    (f : C(A, C)) (γ : freeLoop A) (a : A) :
    FreeLoop.conjugacyClass (FreeLoop.postcompose f γ) (f a) =
      ConjClasses.map (FundamentalGroup.map f a)
        (FreeLoop.conjugacyClass γ a) := by
  let δ := FreeLoop.basedRepresentative γ a
  let δf : basedCircleLoop (f a) := ⟨f.comp δ.1, by
    change f (δ.1 0) = f a
    rw [δ.2]⟩
  have hδf : δf.1.Homotopic (FreeLoop.postcompose f γ) :=
    (ContinuousMap.Homotopic.refl f).comp
      (FreeLoop.basedRepresentative_homotopic γ a)
  have hsource := FreeLoop.conjugacyClass_eq_mk_circleToPath γ a δ
    (FreeLoop.basedRepresentative_homotopic γ a)
  calc
    FreeLoop.conjugacyClass (FreeLoop.postcompose f γ) (f a) =
        ConjClasses.mk (basedCircleFundamentalGroupClass δf) :=
      FreeLoop.conjugacyClass_eq_mk_circleToPath _ _ δf hδf
    _ = ConjClasses.map (FundamentalGroup.map f a)
        (ConjClasses.mk (basedCircleFundamentalGroupClass δ)) := by
      change ConjClasses.mk (basedCircleFundamentalGroupClass δf) =
        ConjClasses.mk (FundamentalGroup.map f a (basedCircleFundamentalGroupClass δ))
      congr 1
    _ = ConjClasses.map (FundamentalGroup.map f a)
        (FreeLoop.conjugacyClass γ a) := congrArg _ hsource.symm

open Classical in
theorem loopClassMeets_postcompose_map
    {A C : Type u} [TopologicalSpace A] [TopologicalSpace C]
    [PathConnectedSpace A] [PathConnectedSpace C]
    (f : C(A, C)) (γ : freeLoop A) (a : A)
    (N : Subgroup (FundamentalGroup A a))
    (hγ : loopClassMeets γ a N) :
    loopClassMeets (FreeLoop.postcompose f γ) (f a)
      (N.map (FundamentalGroup.map f a)) := by
  obtain ⟨g, hgC, hgN⟩ := hγ
  refine ⟨FundamentalGroup.map f a g, ?_, ⟨g, hgN, rfl⟩⟩
  rw [FreeLoop.conjugacyClass_postcompose]
  apply ConjClasses.mem_carrier_iff_mk_eq.mpr
  change ConjClasses.map (FundamentalGroup.map f a) (ConjClasses.mk g) =
    ConjClasses.map (FundamentalGroup.map f a) (FreeLoop.conjugacyClass γ a)
  rw [ConjClasses.mem_carrier_iff_mk_eq.mp hgC]

open Classical in
noncomputable def attachedTwoCellOverlapPoint
    {Y : Type u} [TopologicalSpace Y] {X D : Set Y}
    (e : ClosedCell 2 ≃ₜ D)
    (hboundary : ∀ d : ClosedCell 2, (e d : Y) ∈ X ↔
      ‖(d : EuclideanSpace ℝ (Fin 2))‖ = 1) :
    ↑(attachedCellOuter (X := X) e ∩ attachedCellInner X D) := by
  let _ : PathConnectedSpace
      ↑(attachedCellOuter (X := X) e ∩ attachedCellInner X D) :=
    pathConnectedSpace_attachedCellOverlap_two e hboundary
  exact Classical.choice inferInstance

open Classical in
noncomputable def attachedTwoCellFundamentalGroupHom
    {Y : Type u} [TopologicalSpace Y] {X D : Set Y}
    (e : ClosedCell 2 ≃ₜ D)
    (hboundary : ∀ d : ClosedCell 2, (e d : Y) ∈ X ↔
      ‖(d : EuclideanSpace ℝ (Fin 2))‖ = 1) (p : X) :
    FundamentalGroup X p →*
      FundamentalGroup (AttachedCellUnion X D)
        ((VanKampen.subsetToAmbient (attachedCellOuter (X := X) e))
          (attachedCellBaseToOuter e hboundary p)) :=
  (FundamentalGroup.map
      (VanKampen.subsetToAmbient (attachedCellOuter (X := X) e))
      (attachedCellBaseToOuter e hboundary p)).comp
    (FundamentalGroup.map (attachedCellBaseToOuter e hboundary) p)

open Classical in
noncomputable def attachedCellBaseToOuterHomotopyEquiv
    {Y : Type u} [TopologicalSpace Y] {X D : Set Y}
    (e : ClosedCell 2 ≃ₜ D) (hX : IsClosed X) (hD : IsClosed D)
    (hboundary : ∀ d : ClosedCell 2, (e d : Y) ∈ X ↔
      ‖(d : EuclideanSpace ℝ (Fin 2))‖ = 1) :
    X ≃ₕ ↑(attachedCellOuter (X := X) e) := by
  let h := (attachedCellOuterHomotopyEquivBase e hX hD hboundary).symm
  have hfun : h.toFun = attachedCellBaseToOuter e hboundary := by
    ext x
    rfl
  exact {
    toFun := attachedCellBaseToOuter e hboundary
    invFun := h.invFun
    left_inv := by simpa [← hfun] using h.left_inv
    right_inv := by simpa [← hfun] using h.right_inv
  }

open Classical in
theorem bijective_fundamentalGroupMap_attachedCellBaseToOuter
    {Y : Type u} [TopologicalSpace Y] {X D : Set Y}
    (e : ClosedCell 2 ≃ₜ D) (hX : IsClosed X) (hD : IsClosed D)
    (hboundary : ∀ d : ClosedCell 2, (e d : Y) ∈ X ↔
      ‖(d : EuclideanSpace ℝ (Fin 2))‖ = 1) (p : X) :
    Function.Bijective (FundamentalGroup.map (attachedCellBaseToOuter e hboundary) p) := by
  let hbase : attachedCellBaseToOuter e hboundary p =
      attachedCellBaseToOuter e hboundary p := rfl
  have hbij := fundamentalGroup_mapOfEq_bijective_of_homotopyEquiv
    (attachedCellBaseToOuterHomotopyEquiv e hX hD hboundary) p
    (attachedCellBaseToOuter e hboundary p) hbase
  change Function.Bijective
    (FundamentalGroup.mapOfEq (attachedCellBaseToOuter e hboundary) hbase) at hbij
  have hmaps :
      FundamentalGroup.mapOfEq (attachedCellBaseToOuter e hboundary) hbase =
        FundamentalGroup.map (attachedCellBaseToOuter e hboundary) p := by
    ext g
    rw [FundamentalGroup.mapOfEq_apply]
    rw [show hbase = rfl from Subsingleton.elim _ _,
      Path.Homotopic.Quotient.cast_rfl_rfl]
    rfl
  rw [hmaps] at hbij
  exact hbij

open Classical in
theorem surjective_fundamentalGroupMap_attachedCellOuter_at
    {Y : Type u} [TopologicalSpace Y] [T1Space Y]
    {X D : Set Y} [PathConnectedSpace X]
    (e : ClosedCell 2 ≃ₜ D) (hX : IsClosed X) (hD : IsClosed D)
    (hboundary : ∀ d : ClosedCell 2, (e d : Y) ∈ X ↔
      ‖(d : EuclideanSpace ℝ (Fin 2))‖ = 1)
    (p : X) :
    Function.Surjective (FundamentalGroup.map
      (VanKampen.subsetToAmbient (attachedCellOuter (X := X) e))
      (attachedCellBaseToOuter e hboundary p)) := by
  let _ : PathConnectedSpace ↑(attachedCellOuter (X := X) e) :=
    pathConnectedSpace_attachedCellOuter e hX hD hboundary
  let x := attachedTwoCellOverlapPoint e hboundary
  let x₀ : AttachedCellUnion X D := x.1
  have hx₀ : x₀ ∈ attachedCellOuter (X := X) e ∩ attachedCellInner X D := x.2
  let pU := attachedCellBaseToOuter e hboundary p
  let xU := VanKampen.leftBasepoint (attachedCellOuter (X := X) e) x₀ hx₀.1
  let q : Path pU xU := PathConnectedSpace.somePath pU xU
  let j := VanKampen.subsetToAmbient (attachedCellOuter (X := X) e)
  let qA := q.map j.continuous
  have hsurj := surjective_fundamentalGroupMap_attachedCellOuter
    e hX hD hboundary x₀ hx₀
  intro y
  obtain ⟨g, hg⟩ := hsurj ((fundamentalGroupChangeBasepoint qA).symm y)
  refine ⟨fundamentalGroupChangeBasepoint q g, ?_⟩
  calc
    FundamentalGroup.map j pU (fundamentalGroupChangeBasepoint q g) =
        fundamentalGroupChangeBasepoint qA (FundamentalGroup.map j xU g) :=
      (fundamentalGroupChangeBasepoint_map j q g).symm
    _ = fundamentalGroupChangeBasepoint qA ((fundamentalGroupChangeBasepoint qA).symm y) :=
      congrArg (fundamentalGroupChangeBasepoint qA) hg
    _ = y := (fundamentalGroupChangeBasepoint qA).apply_symm_apply y

open Classical in
theorem surjective_attachedTwoCellFundamentalGroupHom
    {Y : Type u} [TopologicalSpace Y] [T1Space Y]
    {X D : Set Y} [PathConnectedSpace X]
    (e : ClosedCell 2 ≃ₜ D) (hX : IsClosed X) (hD : IsClosed D)
    (hboundary : ∀ d : ClosedCell 2, (e d : Y) ∈ X ↔
      ‖(d : EuclideanSpace ℝ (Fin 2))‖ = 1)
    (p : X) : Function.Surjective (attachedTwoCellFundamentalGroupHom e hboundary p) :=
  (surjective_fundamentalGroupMap_attachedCellOuter_at e hX hD hboundary p).comp
    (bijective_fundamentalGroupMap_attachedCellBaseToOuter e hX hD hboundary p).2

open Classical in
noncomputable def attachedTwoCellBoundaryFreeLoop
    {Y : Type u} [TopologicalSpace Y] {X D : Set Y}
    (e : ClosedCell 2 ≃ₜ D) (hX : IsClosed X) (hD : IsClosed D)
    (hboundary : ∀ d : ClosedCell 2, (e d : Y) ∈ X ↔
      ‖(d : EuclideanSpace ℝ (Fin 2))‖ = 1) :
    freeLoop X :=
  attachedTwoCellBoundaryLoop e hX hD hboundary
    (attachedTwoCellOverlapPoint e hboundary).1
    (attachedTwoCellOverlapPoint e hboundary).2

theorem attachedTwoCellBoundaryFreeLoop_mem_attached_cell
    {Y : Type u} [TopologicalSpace Y] {X D : Set Y}
    (e : ClosedCell 2 ≃ₜ D) (hX : IsClosed X) (hD : IsClosed D)
    (hboundary : ∀ d : ClosedCell 2, (e d : Y) ∈ X ↔
      ‖(d : EuclideanSpace ℝ (Fin 2))‖ = 1) (θ : loopCircle) :
    ((attachedTwoCellBoundaryFreeLoop e hX hD hboundary θ : X) : Y) ∈ D :=
  attachedTwoCellBoundaryLoop_mem_attached_cell e hX hD hboundary
    (attachedTwoCellOverlapPoint e hboundary).1
    (attachedTwoCellOverlapPoint e hboundary).2 θ

open Classical in
theorem ker_attachedTwoCellFundamentalGroupHom_le_of_loopClassMeets
    {Y : Type u} [TopologicalSpace Y] [T1Space Y]
    {X D : Set Y} [PathConnectedSpace X]
    (e : ClosedCell 2 ≃ₜ D) (hX : IsClosed X) (hD : IsClosed D)
    (hboundary : ∀ d : ClosedCell 2, (e d : Y) ∈ X ↔
      ‖(d : EuclideanSpace ℝ (Fin 2))‖ = 1)
    (p : X) (N : Subgroup (FundamentalGroup X p)) [N.Normal]
    (hN : loopClassMeets (attachedTwoCellBoundaryFreeLoop e hX hD hboundary) p N) :
    MonoidHom.ker (attachedTwoCellFundamentalGroupHom e hboundary p) ≤ N := by
  let U := attachedCellOuter (X := X) e
  let A := AttachedCellUnion X D
  let a := FundamentalGroup.map (attachedCellBaseToOuter e hboundary) p
  let pU := attachedCellBaseToOuter e hboundary p
  let j := VanKampen.subsetToAmbient U
  let i := FundamentalGroup.map j pU
  let x := attachedTwoCellOverlapPoint e hboundary
  let x₀ : A := x.1
  have hx₀ : x₀ ∈ U ∩ attachedCellInner X D := x.2
  let xU := VanKampen.leftBasepoint U x₀ hx₀.1
  let q : Path pU xU := by
    let _ : PathConnectedSpace U :=
      pathConnectedSpace_attachedCellOuter e hX hD hboundary
    exact PathConnectedSpace.somePath pU xU
  let qA := q.map j.continuous
  let γ := attachedTwoCellKernelGeneratorLoop e hboundary x₀ hx₀
  let Nouter := N.map a
  have ha := bijective_fundamentalGroupMap_attachedCellBaseToOuter
    e hX hD hboundary p
  let _ : PathConnectedSpace U :=
    pathConnectedSpace_attachedCellOuter e hX hD hboundary
  let _ : Nouter.Normal := Subgroup.Normal.map (inferInstance : N.Normal) a ha.2
  have hmeet : loopClassMeets
      (FreeLoop.postcompose (attachedCellBaseToOuter e hboundary)
        (attachedTwoCellBoundaryFreeLoop e hX hD hboundary)) pU Nouter :=
    loopClassMeets_postcompose_map (attachedCellBaseToOuter e hboundary)
      (attachedTwoCellBoundaryFreeLoop e hX hD hboundary) p N hN
  have hcarrier := (loopClassMeets_iff_carrier_subset
    (FreeLoop.postcompose (attachedCellBaseToOuter e hboundary)
      (attachedTwoCellBoundaryFreeLoop e hX hD hboundary)) pU Nouter).mp hmeet
  have hhom : γ.1.Homotopic
      (FreeLoop.postcompose (attachedCellBaseToOuter e hboundary)
        (attachedTwoCellBoundaryFreeLoop e hX hD hboundary)) :=
    attachedTwoCellKernelGeneratorLoop_homotopic_boundaryLoop
      e hX hD hboundary x₀ hx₀
  have hclass := FreeLoop.conjugacyClass_eq_of_homotopic hhom pU
  have halong := FreeLoop.conjugacyClass_eq_mk_loopRepresentativeAlong q γ
  have hrepresentative : loopRepresentativeAlong q γ ∈ Nouter := by
    apply hcarrier
    apply ConjClasses.mem_carrier_iff_mk_eq.mpr
    exact halong.symm.trans hclass
  let N₀ := Nouter.comap (fundamentalGroupChangeBasepoint q).toMonoidHom
  let _ : N₀.Normal := Subgroup.Normal.comap (inferInstance : Nouter.Normal)
    (fundamentalGroupChangeBasepoint q).toMonoidHom
  have hgenerator : Path.Homotopic.Quotient.mk (circleToPath γ) ∈ N₀ := by
    change fundamentalGroupChangeBasepoint q
      (Path.Homotopic.Quotient.mk (circleToPath γ)) ∈ Nouter
    exact hrepresentative
  have hclosure : Subgroup.normalClosure
      ({Path.Homotopic.Quotient.mk (circleToPath γ)} :
        Set (FundamentalGroup U xU)) ≤ N₀ := by
    apply Subgroup.normalClosure_le_normal
    intro z hz
    rw [Set.mem_singleton_iff.mp hz]
    exact hgenerator
  intro g hg
  have hfg := MonoidHom.mem_ker.mp hg
  change i (a g) = 1 at hfg
  let g₀ := (fundamentalGroupChangeBasepoint q).symm (a g)
  have hag : fundamentalGroupChangeBasepoint q g₀ = a g :=
    (fundamentalGroupChangeBasepoint q).apply_symm_apply (a g)
  have hi₀ : FundamentalGroup.map j xU g₀ = 1 := by
    apply (fundamentalGroupChangeBasepoint qA).injective
    rw [fundamentalGroupChangeBasepoint_map]
    rw [hag, hfg, map_one]
  have hg₀closure : g₀ ∈ Subgroup.normalClosure
      ({Path.Homotopic.Quotient.mk (circleToPath γ)} :
        Set (FundamentalGroup U xU)) := by
    rw [← ker_fundamentalGroupMap_attachedCellOuter_eq_normalClosure
      e hX hD hboundary x₀ hx₀]
    exact MonoidHom.mem_ker.mpr hi₀
  have hg₀N : g₀ ∈ N₀ := hclosure hg₀closure
  have hagN : a g ∈ Nouter := by
    rw [← hag]
    exact hg₀N
  obtain ⟨n, hn, hng⟩ := hagN
  rw [← ha.1 hng]
  exact hn

def attachedCellUnionInclusion
    {Y : Type u} [TopologicalSpace Y] {X D : Set Y} :
    C(X, AttachedCellUnion X D) :=
  ContinuousMap.inclusion subset_union_left

theorem attachedCellBaseToUnion
    {Y : Type u} [TopologicalSpace Y] {X D : Set Y}
    (e : ClosedCell 2 ≃ₜ D)
    (hboundary : ∀ d : ClosedCell 2, (e d : Y) ∈ X ↔
      ‖(d : EuclideanSpace ℝ (Fin 2))‖ = 1) :
    (VanKampen.subsetToAmbient (attachedCellOuter (X := X) e)).comp
        (attachedCellBaseToOuter e hboundary) =
      attachedCellUnionInclusion := by
  ext x
  rfl

open Classical in
theorem bijective_fundamentalGroupMap_homeomorph
    {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    (e : X ≃ₜ Y) (x : X) :
    Function.Bijective (FundamentalGroup.map (e : C(X, Y)) x) := by
  let h : e x = e x := rfl
  have hbij := fundamentalGroup_mapOfEq_bijective_of_homotopyEquiv
    e.toHomotopyEquiv x (e x) h
  change Function.Bijective (FundamentalGroup.mapOfEq (e : C(X, Y)) h) at hbij
  have hmaps : FundamentalGroup.mapOfEq (e : C(X, Y)) h =
      FundamentalGroup.map (e : C(X, Y)) x := by
    ext g
    rw [FundamentalGroup.mapOfEq_apply]
    rw [show h = rfl from Subsingleton.elim _ _, Path.Homotopic.Quotient.cast_rfl_rfl]
    rfl
  rw [hmaps] at hbij
  exact hbij

end DifferentialGeometry.Topology

namespace DifferentialGeometry.Topology.PiecewiseLinear

universe v

variable {E : Type v} [NormedAddCommGroup E] [NormedSpace ℝ E]

def sphereWithDiskInteriorsRemoved {k : ℕ} (B : Set E) (D : Fin k → Set E) : Set E :=
  B ∩ ⋂ i, closure (B \ D i)

def diskAttachmentStage {k : ℕ} (B : Set E) (D : Fin k → Set E) :
    List (Fin k) → Set E
  | [] => sphereWithDiskInteriorsRemoved B D
  | i :: l => diskAttachmentStage B D l ∪ D i

omit [NormedSpace ℝ E] in
theorem mem_diskAttachmentStage_iff {k : ℕ} (B : Set E) (D : Fin k → Set E)
    (l : List (Fin k)) (x : E) :
    x ∈ diskAttachmentStage B D l ↔
      x ∈ sphereWithDiskInteriorsRemoved B D ∨ ∃ i ∈ l, x ∈ D i := by
  induction l with
  | nil => simp [diskAttachmentStage]
  | cons i l ih =>
      simp only [diskAttachmentStage, mem_union, ih, List.mem_cons]
      constructor
      · rintro ((hx | ⟨j, hjl, hxj⟩) | hxi)
        · exact Or.inl hx
        · exact Or.inr ⟨j, Or.inr hjl, hxj⟩
        · exact Or.inr ⟨i, Or.inl rfl, hxi⟩
      · rintro (hx | ⟨j, hj | hjl, hxj⟩)
        · exact Or.inl (Or.inl hx)
        · subst j
          exact Or.inr hxj
        · exact Or.inl (Or.inr ⟨j, hjl, hxj⟩)

omit [NormedSpace ℝ E] in
theorem sphereWithDiskInteriorsRemoved_subset {k : ℕ} (B : Set E)
    (D : Fin k → Set E) : sphereWithDiskInteriorsRemoved B D ⊆ B :=
  inter_subset_left

omit [NormedSpace ℝ E] in
theorem diskAttachmentStage_subset {k : ℕ} {B : Set E} {D : Fin k → Set E}
    (hDB : ∀ i, D i ⊆ B) (l : List (Fin k)) : diskAttachmentStage B D l ⊆ B := by
  intro x hx
  rw [mem_diskAttachmentStage_iff] at hx
  rcases hx with hx | ⟨i, -, hxi⟩
  · exact sphereWithDiskInteriorsRemoved_subset B D hx
  · exact hDB i hxi

theorem isClosed_sphereWithDiskInteriorsRemoved [FiniteDimensional ℝ E]
    {k : ℕ} {B : Set E} (D : Fin k → Set E) (hB : IsPLSphere 2 B) :
    IsClosed (sphereWithDiskInteriorsRemoved B D) :=
  hB.isPolyhedron.isClosed.inter (isClosed_iInter fun _ => isClosed_closure)

theorem isClosed_diskAttachmentStage [FiniteDimensional ℝ E]
    {k : ℕ} {B : Set E} {D : Fin k → Set E}
    (hB : IsPLSphere 2 B)
    (q : Fin k → (Fin 3 → ℝ) → E)
    (hq : ∀ i, IsPLHomeomorphOn (q i) (stdSimplex ℝ (Fin 3)) (D i))
    (l : List (Fin k)) : IsClosed (diskAttachmentStage B D l) := by
  induction l with
  | nil => exact isClosed_sphereWithDiskInteriorsRemoved D hB
  | cons i l ih =>
      exact ih.union (show IsClosed (D i) from (show IsPLBall 2 (D i) from ⟨q i, hq i⟩).isPolyhedron.isClosed)

open Classical in
theorem disk_inter_sphereWithDiskInteriorsRemoved [FiniteDimensional ℝ E]
    {k : ℕ} {B : Set E} {D : Fin k → Set E}
    (q : Fin k → (Fin 3 → ℝ) → E)
    (hB : IsPLSphere 2 B)
    (hq : ∀ i, IsPLHomeomorphOn (q i) (stdSimplex ℝ (Fin 3)) (D i))
    (hDB : ∀ i, D i ⊆ B)
    (hdisj : Pairwise (Function.onFun Disjoint D)) (i : Fin k) :
    D i ∩ sphereWithDiskInteriorsRemoved B D = q i '' stdSimplexBoundary 2 := by
  have hcommon : D i ∩ closure (B \ D i) = q i '' stdSimplexBoundary 2 :=
    hB.inter_closure_sdiff_eq_image_stdSimplexBoundary (hq i) (hDB i)
  apply Subset.antisymm
  · intro x hx
    rw [← hcommon]
    exact ⟨hx.1, Set.mem_iInter.mp hx.2.2 i⟩
  · intro x hx
    have hxcommon : x ∈ D i ∩ closure (B \ D i) := by
      rw [hcommon]
      exact hx
    refine ⟨hxcommon.1, hDB i hxcommon.1, Set.mem_iInter.mpr ?_⟩
    intro j
    by_cases hij : i = j
    · simpa [hij] using hxcommon.2
    · apply subset_closure
      refine ⟨hDB i hxcommon.1, ?_⟩
      intro hxj
      exact Set.disjoint_left.mp (hdisj hij) hxcommon.1 hxj

open Classical in
theorem disk_inter_diskAttachmentStage [FiniteDimensional ℝ E]
    {k : ℕ} {B : Set E} {D : Fin k → Set E}
    (q : Fin k → (Fin 3 → ℝ) → E)
    (hB : IsPLSphere 2 B)
    (hq : ∀ i, IsPLHomeomorphOn (q i) (stdSimplex ℝ (Fin 3)) (D i))
    (hDB : ∀ i, D i ⊆ B)
    (hdisj : Pairwise (Function.onFun Disjoint D))
    {i : Fin k} {l : List (Fin k)} (hil : i ∉ l) :
    D i ∩ diskAttachmentStage B D l = q i '' stdSimplexBoundary 2 := by
  apply Subset.antisymm
  · intro x hx
    have hxstage := (mem_diskAttachmentStage_iff B D l x).mp hx.2
    rcases hxstage with hxcore | ⟨j, hjl, hxj⟩
    · rw [← disk_inter_sphereWithDiskInteriorsRemoved q hB hq hDB hdisj i]
      exact ⟨hx.1, hxcore⟩
    · have hij : i ≠ j := by
        intro h
        exact hil (h ▸ hjl)
      exact (Set.disjoint_left.mp (hdisj hij) hx.1 hxj).elim
  · intro x hx
    have hxcore : x ∈ D i ∩ sphereWithDiskInteriorsRemoved B D := by
      rw [disk_inter_sphereWithDiskInteriorsRemoved q hB hq hDB hdisj i]
      exact hx
    exact ⟨hxcore.1, (mem_diskAttachmentStage_iff B D l x).mpr (Or.inl hxcore.2)⟩

noncomputable def diskClosedCellHomeomorph [FiniteDimensional ℝ E]
    {k : ℕ} {D : Fin k → Set E}
    (q : Fin k → (Fin 3 → ℝ) → E)
    (hq : ∀ i, IsPLHomeomorphOn (q i) (stdSimplex ℝ (Fin 3)) (D i))
    (i : Fin k) : ClosedCell 2 ≃ₜ D i :=
  (DifferentialGeometry.Cell.stdSimplexClosedCellHomeomorph 2).symm.trans
    (hq i).homeomorph

theorem stdSimplexClosedCellHomeomorph_norm_eq_one_iff
    (s : stdSimplex ℝ (Fin 3)) :
    ‖((DifferentialGeometry.Cell.stdSimplexClosedCellHomeomorph 2 s : ClosedCell 2) :
      EuclideanSpace ℝ (Fin 2))‖ = 1 ↔
      s ∈ DifferentialGeometry.Simplex.boundary (Fin 3) := by
  change ‖(DifferentialGeometry.Simplex.stdSimplexNormedBallHomeomorph
    (EuclideanSpace.equiv (Fin 2) ℝ).symm s).1‖ = 1 ↔ _
  simpa only [mem_sphere_zero_iff_norm, Nat.reduceAdd] using
    (DifferentialGeometry.Simplex.stdSimplexNormedBallHomeomorph_mem_sphere_iff
      (EuclideanSpace.equiv (Fin 2) ℝ).symm s)

open Classical in
theorem diskClosedCellHomeomorph_mem_stage_iff [FiniteDimensional ℝ E]
    {k : ℕ} {B : Set E} {D : Fin k → Set E}
    (q : Fin k → (Fin 3 → ℝ) → E)
    (hB : IsPLSphere 2 B)
    (hq : ∀ i, IsPLHomeomorphOn (q i) (stdSimplex ℝ (Fin 3)) (D i))
    (hDB : ∀ i, D i ⊆ B)
    (hdisj : Pairwise (Function.onFun Disjoint D))
    {i : Fin k} {l : List (Fin k)} (hil : i ∉ l) (d : ClosedCell 2) :
    ((diskClosedCellHomeomorph q hq i d : D i) : E) ∈ diskAttachmentStage B D l ↔
      ‖(d : EuclideanSpace ℝ (Fin 2))‖ = 1 := by
  let s := (DifferentialGeometry.Cell.stdSimplexClosedCellHomeomorph 2).symm d
  have hinter := disk_inter_diskAttachmentStage q hB hq hDB hdisj hil
  change q i s ∈ diskAttachmentStage B D l ↔ _
  constructor
  · intro hs
    have himage : q i s ∈ q i '' stdSimplexBoundary 2 := by
      rw [← hinter]
      exact ⟨(hq i).bijOn.mapsTo s.2, hs⟩
    obtain ⟨t, ht, hts⟩ := himage
    have hst : s.1 = t := (hq i).bijOn.injOn s.2 ht.1 hts.symm
    have hsboundary : s ∈ DifferentialGeometry.Simplex.boundary (Fin 3) := by
      change ∃ j : Fin 3, s.1 j = 0
      rw [hst]
      exact ht.2
    have hnorm := (stdSimplexClosedCellHomeomorph_norm_eq_one_iff s).mpr hsboundary
    rw [show DifferentialGeometry.Cell.stdSimplexClosedCellHomeomorph 2 s = d from
      (DifferentialGeometry.Cell.stdSimplexClosedCellHomeomorph 2).apply_symm_apply d] at hnorm
    exact hnorm
  · intro hd
    have hnorm :
        ‖((DifferentialGeometry.Cell.stdSimplexClosedCellHomeomorph 2 s).1 :
          EuclideanSpace ℝ (Fin 2))‖ = 1 := by
      rw [show DifferentialGeometry.Cell.stdSimplexClosedCellHomeomorph 2 s = d from
        (DifferentialGeometry.Cell.stdSimplexClosedCellHomeomorph 2).apply_symm_apply d]
      exact hd
    have hsboundary : s ∈ DifferentialGeometry.Simplex.boundary (Fin 3) :=
      (stdSimplexClosedCellHomeomorph_norm_eq_one_iff s).mp hnorm
    have himage : q i s ∈ q i '' stdSimplexBoundary 2 :=
      ⟨s, ⟨s.2, hsboundary⟩, rfl⟩
    rw [← hinter] at himage
    exact himage.2

theorem stdSimplexBoundary_two_nonempty : (stdSimplexBoundary 2).Nonempty := by
  refine ⟨Pi.single (0 : Fin 3) 1, single_mem_stdSimplex ℝ 0, 1, ?_⟩
  simp

open Classical in
theorem pathConnectedSpace_diskAttachmentStage [FiniteDimensional ℝ E]
    {k : ℕ} {B : Set E} {D : Fin k → Set E}
    (q : Fin k → (Fin 3 → ℝ) → E)
    (hB : IsPLSphere 2 B)
    (hq : ∀ i, IsPLHomeomorphOn (q i) (stdSimplex ℝ (Fin 3)) (D i))
    (hDB : ∀ i, D i ⊆ B)
    (hdisj : Pairwise (Function.onFun Disjoint D))
    [PathConnectedSpace (sphereWithDiskInteriorsRemoved B D)]
    (l : List (Fin k)) : PathConnectedSpace (diskAttachmentStage B D l) := by
  induction l with
  | nil =>
      change PathConnectedSpace (sphereWithDiskInteriorsRemoved B D)
      exact inferInstance
  | cons i l ih =>
      let _ : PathConnectedSpace (diskAttachmentStage B D l) := ih
      let _ : PathConnectedSpace (stdSimplex ℝ (Fin 3)) := inferInstance
      let _ : PathConnectedSpace (D i) :=
        (hq i).homeomorph.surjective.pathConnectedSpace (hq i).homeomorph.continuous
      apply isPathConnected_iff_pathConnectedSpace.mp
      apply (isPathConnected_iff_pathConnectedSpace.mpr
        (inferInstance : PathConnectedSpace (diskAttachmentStage B D l))).union
        (isPathConnected_iff_pathConnectedSpace.mpr
          (inferInstance : PathConnectedSpace (D i)))
      obtain ⟨s, hs⟩ := stdSimplexBoundary_two_nonempty
      have himage : q i s ∈ q i '' stdSimplexBoundary 2 := ⟨s, hs, rfl⟩
      have hxcore : q i s ∈ sphereWithDiskInteriorsRemoved B D := by
        rw [← disk_inter_sphereWithDiskInteriorsRemoved q hB hq hDB hdisj i] at himage
        exact himage.2
      exact ⟨q i s, (mem_diskAttachmentStage_iff B D l (q i s)).mpr (Or.inl hxcore),
        (hq i).bijOn.mapsTo hs.1⟩

omit [NormedSpace ℝ E] in
open Classical in
theorem diskAttachmentStage_eq_sphere
    {k : ℕ} {B : Set E} {D : Fin k → Set E}
    (hDB : ∀ i, D i ⊆ B) {l : List (Fin k)} (hl : ∀ i, i ∈ l) :
    diskAttachmentStage B D l = B := by
  apply Subset.antisymm (diskAttachmentStage_subset hDB l)
  intro x hxB
  rw [mem_diskAttachmentStage_iff]
  by_cases hxD : ∃ i, x ∈ D i
  · obtain ⟨i, hxi⟩ := hxD
    exact Or.inr ⟨i, hl i, hxi⟩
  · left
    refine ⟨hxB, Set.mem_iInter.mpr ?_⟩
    intro i
    apply subset_closure
    exact ⟨hxB, fun hxi => hxD ⟨i, hxi⟩⟩

omit [NormedSpace ℝ E] in
open Classical in
theorem diskAttachmentStage_finRange_eq_sphere
    {k : ℕ} {B : Set E} {D : Fin k → Set E} (hDB : ∀ i, D i ⊆ B) :
    diskAttachmentStage B D (List.finRange k) = B :=
  diskAttachmentStage_eq_sphere hDB (fun i => List.mem_finRange i)

open Classical in
noncomputable def diskAttachmentStepMap [FiniteDimensional ℝ E]
    {k : ℕ} {B : Set E} {D : Fin k → Set E}
    (q : Fin k → (Fin 3 → ℝ) → E)
    (hB : IsPLSphere 2 B)
    (hq : ∀ i, IsPLHomeomorphOn (q i) (stdSimplex ℝ (Fin 3)) (D i))
    (hDB : ∀ i, D i ⊆ B)
    (hdisj : Pairwise (Function.onFun Disjoint D))
    {i : Fin k} {l : List (Fin k)} (hil : i ∉ l) :
    C(diskAttachmentStage B D l, diskAttachmentStage B D (i :: l)) := by
  let X := diskAttachmentStage B D l
  let e := diskClosedCellHomeomorph q hq i
  have hboundary : ∀ d : ClosedCell 2, (e d : E) ∈ X ↔
      ‖(d : EuclideanSpace ℝ (Fin 2))‖ = 1 :=
    diskClosedCellHomeomorph_mem_stage_iff q hB hq hDB hdisj hil
  change C(X, AttachedCellUnion X (D i))
  exact (VanKampen.subsetToAmbient (attachedCellOuter (X := X) e)).comp
    (attachedCellBaseToOuter e hboundary)

open Classical in
theorem diskAttachmentStepMap_coe [FiniteDimensional ℝ E]
    {k : ℕ} {B : Set E} {D : Fin k → Set E}
    (q : Fin k → (Fin 3 → ℝ) → E)
    (hB : IsPLSphere 2 B)
    (hq : ∀ i, IsPLHomeomorphOn (q i) (stdSimplex ℝ (Fin 3)) (D i))
    (hDB : ∀ i, D i ⊆ B)
    (hdisj : Pairwise (Function.onFun Disjoint D))
    {i : Fin k} {l : List (Fin k)} (hil : i ∉ l)
    (x : diskAttachmentStage B D l) :
    ((diskAttachmentStepMap q hB hq hDB hdisj hil x :
      diskAttachmentStage B D (i :: l)) : E) = x := by
  let X := diskAttachmentStage B D l
  let e := diskClosedCellHomeomorph q hq i
  have hboundary : ∀ d : ClosedCell 2, (e d : E) ∈ X ↔
      ‖(d : EuclideanSpace ℝ (Fin 2))‖ = 1 :=
    diskClosedCellHomeomorph_mem_stage_iff q hB hq hDB hdisj hil
  have hmaps := congrArg
    (fun f : C(X, AttachedCellUnion X (D i)) => ((f x : AttachedCellUnion X (D i)) : E))
    (attachedCellBaseToUnion e hboundary)
  exact hmaps

open Classical in
theorem fundamentalGroupMap_diskAttachmentStepMap [FiniteDimensional ℝ E]
    {k : ℕ} {B : Set E} {D : Fin k → Set E}
    (q : Fin k → (Fin 3 → ℝ) → E)
    (hB : IsPLSphere 2 B)
    (hq : ∀ i, IsPLHomeomorphOn (q i) (stdSimplex ℝ (Fin 3)) (D i))
    (hDB : ∀ i, D i ⊆ B)
    (hdisj : Pairwise (Function.onFun Disjoint D))
    {i : Fin k} {l : List (Fin k)} (hil : i ∉ l)
    (p : diskAttachmentStage B D l) :
    FundamentalGroup.map (diskAttachmentStepMap q hB hq hDB hdisj hil) p =
      attachedTwoCellFundamentalGroupHom
        (diskClosedCellHomeomorph q hq i)
        (diskClosedCellHomeomorph_mem_stage_iff q hB hq hDB hdisj hil) p := by
  ext g
  exact Path.Homotopic.Quotient.map_comp

open Classical in
noncomputable def diskAttachmentMapForList [FiniteDimensional ℝ E]
    {k : ℕ} {B : Set E} {D : Fin k → Set E}
    (q : Fin k → (Fin 3 → ℝ) → E)
    (hB : IsPLSphere 2 B)
    (hq : ∀ i, IsPLHomeomorphOn (q i) (stdSimplex ℝ (Fin 3)) (D i))
    (hDB : ∀ i, D i ⊆ B)
    (hdisj : Pairwise (Function.onFun Disjoint D)) :
    (l : List (Fin k)) → l.Nodup →
      C(sphereWithDiskInteriorsRemoved B D, diskAttachmentStage B D l)
  | [], _ => ContinuousMap.id _
  | _i :: l, hl =>
      (diskAttachmentStepMap q hB hq hDB hdisj (List.nodup_cons.mp hl).1).comp
        (diskAttachmentMapForList q hB hq hDB hdisj l (List.nodup_cons.mp hl).2)

open Classical in
theorem diskAttachmentMapForList_coe [FiniteDimensional ℝ E]
    {k : ℕ} {B : Set E} {D : Fin k → Set E}
    (q : Fin k → (Fin 3 → ℝ) → E)
    (hB : IsPLSphere 2 B)
    (hq : ∀ i, IsPLHomeomorphOn (q i) (stdSimplex ℝ (Fin 3)) (D i))
    (hDB : ∀ i, D i ⊆ B)
    (hdisj : Pairwise (Function.onFun Disjoint D))
    (l : List (Fin k)) (hl : l.Nodup)
    (x : sphereWithDiskInteriorsRemoved B D) :
    ((diskAttachmentMapForList q hB hq hDB hdisj l hl x :
      diskAttachmentStage B D l) : E) = x := by
  induction l with
  | nil => rfl
  | cons i l ih =>
      rw [diskAttachmentMapForList]
      exact (diskAttachmentStepMap_coe q hB hq hDB hdisj
        (List.nodup_cons.mp hl).1 _).trans (ih (List.nodup_cons.mp hl).2)

open Classical in
noncomputable def diskBoundaryLoopInRemovedSphere [FiniteDimensional ℝ E]
    {k : ℕ} {B : Set E} {D : Fin k → Set E}
    (q : Fin k → (Fin 3 → ℝ) → E)
    (hB : IsPLSphere 2 B)
    (hq : ∀ i, IsPLHomeomorphOn (q i) (stdSimplex ℝ (Fin 3)) (D i))
    (hDB : ∀ i, D i ⊆ B)
    (hdisj : Pairwise (Function.onFun Disjoint D))
    {i : Fin k} {l : List (Fin k)} (hil : i ∉ l) :
    freeLoop (sphereWithDiskInteriorsRemoved B D) := by
  let X := diskAttachmentStage B D l
  let e := diskClosedCellHomeomorph q hq i
  have hX : IsClosed X := isClosed_diskAttachmentStage hB q hq l
  have hD : IsClosed (D i) :=
    (show IsPLBall 2 (D i) from ⟨q i, hq i⟩).isPolyhedron.isClosed
  have hboundary : ∀ d : ClosedCell 2, (e d : E) ∈ X ↔
      ‖(d : EuclideanSpace ℝ (Fin 2))‖ = 1 :=
    diskClosedCellHomeomorph_mem_stage_iff q hB hq hDB hdisj hil
  let γ := attachedTwoCellBoundaryFreeLoop e hX hD hboundary
  have hmem (θ : loopCircle) : ((γ θ : X) : E) ∈
      sphereWithDiskInteriorsRemoved B D := by
    have hxD : ((γ θ : X) : E) ∈ D i :=
      attachedTwoCellBoundaryFreeLoop_mem_attached_cell e hX hD hboundary θ
    have hximage : ((γ θ : X) : E) ∈ q i '' stdSimplexBoundary 2 := by
      rw [← disk_inter_diskAttachmentStage q hB hq hDB hdisj hil]
      exact ⟨hxD, (γ θ).2⟩
    have hxcore : ((γ θ : X) : E) ∈
        D i ∩ sphereWithDiskInteriorsRemoved B D := by
      rw [disk_inter_sphereWithDiskInteriorsRemoved q hB hq hDB hdisj i]
      exact hximage
    exact hxcore.2
  exact {
    toFun := fun θ => ⟨(γ θ : X), hmem θ⟩
    continuous_toFun :=
      (continuous_subtype_val.comp γ.continuous).subtype_mk hmem
  }

open Classical in
theorem diskBoundaryLoopInRemovedSphere_postcompose [FiniteDimensional ℝ E]
    {k : ℕ} {B : Set E} {D : Fin k → Set E}
    (q : Fin k → (Fin 3 → ℝ) → E)
    (hB : IsPLSphere 2 B)
    (hq : ∀ i, IsPLHomeomorphOn (q i) (stdSimplex ℝ (Fin 3)) (D i))
    (hDB : ∀ i, D i ⊆ B)
    (hdisj : Pairwise (Function.onFun Disjoint D))
    {i : Fin k} {l : List (Fin k)} (hil : i ∉ l) (hl : l.Nodup) :
    FreeLoop.postcompose (diskAttachmentMapForList q hB hq hDB hdisj l hl)
        (diskBoundaryLoopInRemovedSphere q hB hq hDB hdisj hil) =
      attachedTwoCellBoundaryFreeLoop
        (diskClosedCellHomeomorph q hq i)
        (isClosed_diskAttachmentStage hB q hq l)
        ((show IsPLBall 2 (D i) from ⟨q i, hq i⟩).isPolyhedron.isClosed)
        (diskClosedCellHomeomorph_mem_stage_iff q hB hq hDB hdisj hil) := by
  ext θ
  exact diskAttachmentMapForList_coe q hB hq hDB hdisj l hl _

open Classical in
theorem surjective_fundamentalGroupMap_diskAttachmentStepMap [FiniteDimensional ℝ E]
    {k : ℕ} {B : Set E} {D : Fin k → Set E}
    (q : Fin k → (Fin 3 → ℝ) → E)
    (hB : IsPLSphere 2 B)
    (hq : ∀ i, IsPLHomeomorphOn (q i) (stdSimplex ℝ (Fin 3)) (D i))
    (hDB : ∀ i, D i ⊆ B)
    (hdisj : Pairwise (Function.onFun Disjoint D))
    {i : Fin k} {l : List (Fin k)} (hil : i ∉ l)
    [PathConnectedSpace (diskAttachmentStage B D l)]
    (p : diskAttachmentStage B D l) :
    Function.Surjective
      (FundamentalGroup.map (diskAttachmentStepMap q hB hq hDB hdisj hil) p) := by
  rw [fundamentalGroupMap_diskAttachmentStepMap q hB hq hDB hdisj hil p]
  exact surjective_attachedTwoCellFundamentalGroupHom
    (diskClosedCellHomeomorph q hq i)
    (isClosed_diskAttachmentStage hB q hq l)
    ((show IsPLBall 2 (D i) from ⟨q i, hq i⟩).isPolyhedron.isClosed)
    (diskClosedCellHomeomorph_mem_stage_iff q hB hq hDB hdisj hil) p

open Classical in
theorem ker_fundamentalGroupMap_diskAttachmentStepMap_le_of_loopClassMeets
    [FiniteDimensional ℝ E]
    {k : ℕ} {B : Set E} {D : Fin k → Set E}
    (q : Fin k → (Fin 3 → ℝ) → E)
    (hB : IsPLSphere 2 B)
    (hq : ∀ i, IsPLHomeomorphOn (q i) (stdSimplex ℝ (Fin 3)) (D i))
    (hDB : ∀ i, D i ⊆ B)
    (hdisj : Pairwise (Function.onFun Disjoint D))
    {i : Fin k} {l : List (Fin k)} (hil : i ∉ l)
    [PathConnectedSpace (diskAttachmentStage B D l)]
    (p : diskAttachmentStage B D l)
    (N : Subgroup (FundamentalGroup (diskAttachmentStage B D l) p)) [N.Normal]
    (hN : loopClassMeets
      (attachedTwoCellBoundaryFreeLoop
        (diskClosedCellHomeomorph q hq i)
        (isClosed_diskAttachmentStage hB q hq l)
        ((show IsPLBall 2 (D i) from ⟨q i, hq i⟩).isPolyhedron.isClosed)
        (diskClosedCellHomeomorph_mem_stage_iff q hB hq hDB hdisj hil)) p N) :
    MonoidHom.ker
        (FundamentalGroup.map (diskAttachmentStepMap q hB hq hDB hdisj hil) p) ≤ N := by
  rw [fundamentalGroupMap_diskAttachmentStepMap q hB hq hDB hdisj hil p]
  exact ker_attachedTwoCellFundamentalGroupHom_le_of_loopClassMeets
    (diskClosedCellHomeomorph q hq i)
    (isClosed_diskAttachmentStage hB q hq l)
    ((show IsPLBall 2 (D i) from ⟨q i, hq i⟩).isPolyhedron.isClosed)
    (diskClosedCellHomeomorph_mem_stage_iff q hB hq hDB hdisj hil) p N hN

theorem ker_comp_le_of_ker_le_of_ker_le_map
    {G H K : Type*} [Group G] [Group H] [Group K]
    (f : G →* H) (g : H →* K) (N : Subgroup G)
    (hf : MonoidHom.ker f ≤ N) (hg : MonoidHom.ker g ≤ N.map f) :
    MonoidHom.ker (g.comp f) ≤ N := by
  intro x hx
  have hfx : f x ∈ MonoidHom.ker g :=
    MonoidHom.mem_ker.mpr (MonoidHom.mem_ker.mp hx)
  have hxcomap : x ∈ (N.map f).comap f := hg hfx
  rw [Subgroup.comap_map_eq_self hf] at hxcomap
  exact hxcomap

open Classical in
noncomputable def diskBoundaryLoopForList [FiniteDimensional ℝ E]
    {k : ℕ} {B : Set E} {D : Fin k → Set E}
    (q : Fin k → (Fin 3 → ℝ) → E)
    (hB : IsPLSphere 2 B)
    (hq : ∀ i, IsPLHomeomorphOn (q i) (stdSimplex ℝ (Fin 3)) (D i))
    (hDB : ∀ i, D i ⊆ B)
    (hdisj : Pairwise (Function.onFun Disjoint D)) :
    (l : List (Fin k)) → l.Nodup → (i : Fin k) → i ∈ l →
      freeLoop (sphereWithDiskInteriorsRemoved B D)
  | [], _, _, hi => (List.not_mem_nil hi).elim
  | a :: l, hl, i, hi =>
      if hia : i = a then
        diskBoundaryLoopInRemovedSphere q hB hq hDB hdisj (List.nodup_cons.mp hl).1
      else
        diskBoundaryLoopForList q hB hq hDB hdisj l (List.nodup_cons.mp hl).2 i (by
          simpa [hia] using hi)

open Classical in
noncomputable def sphereBoundaryLoop [FiniteDimensional ℝ E]
    {k : ℕ} {B : Set E} {D : Fin k → Set E}
    (q : Fin k → (Fin 3 → ℝ) → E)
    (hB : IsPLSphere 2 B)
    (hq : ∀ i, IsPLHomeomorphOn (q i) (stdSimplex ℝ (Fin 3)) (D i))
    (hDB : ∀ i, D i ⊆ B)
    (hdisj : Pairwise (Function.onFun Disjoint D))
    (i : Fin k) : freeLoop (sphereWithDiskInteriorsRemoved B D) :=
  diskBoundaryLoopForList q hB hq hDB hdisj (List.finRange k)
    (List.nodup_finRange k) i (List.mem_finRange i)

open Classical in
theorem surjective_and_ker_le_fundamentalGroupMap_diskAttachmentMapForList
    [FiniteDimensional ℝ E]
    {k : ℕ} {B : Set E} {D : Fin k → Set E}
    (q : Fin k → (Fin 3 → ℝ) → E)
    (hB : IsPLSphere 2 B)
    (hq : ∀ i, IsPLHomeomorphOn (q i) (stdSimplex ℝ (Fin 3)) (D i))
    (hDB : ∀ i, D i ⊆ B)
    (hdisj : Pairwise (Function.onFun Disjoint D))
    [PathConnectedSpace (sphereWithDiskInteriorsRemoved B D)]
    (P₀ : sphereWithDiskInteriorsRemoved B D)
    (N : Subgroup (FundamentalGroup (sphereWithDiskInteriorsRemoved B D) P₀)) [N.Normal]
    (l : List (Fin k)) (hl : l.Nodup)
    (hN : ∀ i (hi : i ∈ l),
      loopClassMeets (diskBoundaryLoopForList q hB hq hDB hdisj l hl i hi) P₀ N) :
    Function.Surjective
        (FundamentalGroup.map (diskAttachmentMapForList q hB hq hDB hdisj l hl) P₀) ∧
      MonoidHom.ker
          (FundamentalGroup.map (diskAttachmentMapForList q hB hq hDB hdisj l hl) P₀) ≤ N := by
  induction l with
  | nil =>
      have hbij := bijective_fundamentalGroupMap_homeomorph
        (Homeomorph.refl (sphereWithDiskInteriorsRemoved B D)) P₀
      change Function.Bijective
        (FundamentalGroup.map
          (diskAttachmentMapForList q hB hq hDB hdisj [] hl) P₀) at hbij
      refine ⟨hbij.2, ?_⟩
      intro g hg
      have hg1 : g = 1 := hbij.1 (by
        calc
          FundamentalGroup.map
              (diskAttachmentMapForList q hB hq hDB hdisj [] hl) P₀ g = 1 :=
            MonoidHom.mem_ker.mp hg
          _ = FundamentalGroup.map
              (diskAttachmentMapForList q hB hq hDB hdisj [] hl) P₀ 1 :=
            (map_one _).symm)
      rw [hg1]
      exact N.one_mem
  | cons a l ih =>
      have hal : a ∉ l := (List.nodup_cons.mp hl).1
      have hl' : l.Nodup := (List.nodup_cons.mp hl).2
      have hNtail : ∀ i (hi : i ∈ l),
          loopClassMeets (diskBoundaryLoopForList q hB hq hDB hdisj l hl' i hi) P₀ N := by
        intro i hi
        have hia : i ≠ a := by
          intro h
          exact hal (h ▸ hi)
        have h := hN i (by simp [hi])
        simpa [diskBoundaryLoopForList, hia] using h
      obtain ⟨hprevSurj, hprevKer⟩ := ih hl' hNtail
      let prev := diskAttachmentMapForList q hB hq hDB hdisj l hl'
      let step := diskAttachmentStepMap q hB hq hDB hdisj hal
      let F := FundamentalGroup.map prev P₀
      let G := FundamentalGroup.map step (prev P₀)
      let Nstage := N.map F
      let _ : PathConnectedSpace (diskAttachmentStage B D l) :=
        pathConnectedSpace_diskAttachmentStage q hB hq hDB hdisj l
      let _ : Nstage.Normal := Subgroup.Normal.map (inferInstance : N.Normal) F hprevSurj
      have hNhead : loopClassMeets
          (diskBoundaryLoopInRemovedSphere q hB hq hDB hdisj hal) P₀ N := by
        have h := hN a (by simp)
        simpa [diskBoundaryLoopForList] using h
      have hNstage : loopClassMeets
          (attachedTwoCellBoundaryFreeLoop
            (diskClosedCellHomeomorph q hq a)
            (isClosed_diskAttachmentStage hB q hq l)
            ((show IsPLBall 2 (D a) from ⟨q a, hq a⟩).isPolyhedron.isClosed)
            (diskClosedCellHomeomorph_mem_stage_iff q hB hq hDB hdisj hal))
          (prev P₀) Nstage := by
        have h := loopClassMeets_postcompose_map prev
          (diskBoundaryLoopInRemovedSphere q hB hq hDB hdisj hal) P₀ N hNhead
        rw [diskBoundaryLoopInRemovedSphere_postcompose q hB hq hDB hdisj hal hl'] at h
        exact h
      have hstepSurj : Function.Surjective G :=
        surjective_fundamentalGroupMap_diskAttachmentStepMap
          q hB hq hDB hdisj hal (prev P₀)
      have hstepKer : MonoidHom.ker G ≤ Nstage :=
        ker_fundamentalGroupMap_diskAttachmentStepMap_le_of_loopClassMeets
          q hB hq hDB hdisj hal (prev P₀) Nstage hNstage
      have hmap :
          FundamentalGroup.map
              (diskAttachmentMapForList q hB hq hDB hdisj (a :: l) hl) P₀ =
            G.comp F := by
        ext g
        exact Path.Homotopic.Quotient.map_comp
      rw [hmap]
      exact ⟨hstepSurj.comp hprevSurj,
        ker_comp_le_of_ker_le_of_ker_le_map F G N hprevKer hstepKer⟩

def stdSimplexBoundaryHomeomorphSimplexBoundary (n : ℕ) :
    stdSimplexBoundary n ≃ₜ DifferentialGeometry.Simplex.boundary (Fin (n + 1)) where
  toFun x := ⟨⟨x.1, x.2.1⟩, x.2.2⟩
  invFun x := ⟨x.1.1, x.1.2, x.2⟩
  left_inv _x := rfl
  right_inv _x := rfl
  continuous_toFun :=
    (continuous_subtype_val.subtype_mk _).subtype_mk _
  continuous_invFun :=
    (continuous_subtype_val.comp continuous_subtype_val).subtype_mk _

open Classical in
theorem IsPLSphere.twoSimplyConnectedSpace [FiniteDimensional ℝ E]
    {B : Set E} (hB : IsPLSphere 2 B) : SimplyConnectedSpace B := by
  obtain ⟨f, hf⟩ := hB
  let e : stdSimplexBoundary 3 ≃ₜ SphereTwo :=
    (stdSimplexBoundaryHomeomorphSimplexBoundary 3).trans
      (DifferentialGeometry.Simplex.stdSimplexNormedBoundarySphereHomeomorph
        (EuclideanSpace.equiv (Fin 3) ℝ).symm)
  let _ : SimplyConnectedSpace (stdSimplexBoundary 3) :=
    e.toHomotopyEquiv.simplyConnectedSpace
  exact hf.homeomorph.symm.toHomotopyEquiv.simplyConnectedSpace

open Classical in
theorem eq_top_of_boundaryLoops_mem_normal [FiniteDimensional ℝ E]
    {B : Set E} (hB : IsPLSphere 2 B) {k : ℕ}
    (D : Fin k → Set E) (q : Fin k → (Fin 3 → ℝ) → E)
    (hq : ∀ i, IsPLHomeomorphOn (q i) (stdSimplex ℝ (Fin 3)) (D i))
    (hDB : ∀ i, D i ⊆ B)
    (hdisj : Pairwise (Function.onFun Disjoint D))
    [PathConnectedSpace (sphereWithDiskInteriorsRemoved B D)]
    (P₀ : sphereWithDiskInteriorsRemoved B D)
    (N : Subgroup (FundamentalGroup (sphereWithDiskInteriorsRemoved B D) P₀)) [N.Normal]
    (hN : ∀ i, loopClassMeets (sphereBoundaryLoop q hB hq hDB hdisj i) P₀ N) :
    N = ⊤ := by
  let l := List.finRange k
  have hl : l.Nodup := List.nodup_finRange k
  have hNl : ∀ i (hi : i ∈ l),
      loopClassMeets (diskBoundaryLoopForList q hB hq hDB hdisj l hl i hi) P₀ N := by
    intro i hi
    simpa [sphereBoundaryLoop, l] using hN i
  have hresult := surjective_and_ker_le_fundamentalGroupMap_diskAttachmentMapForList
    q hB hq hDB hdisj P₀ N l hl hNl
  let _ : SimplyConnectedSpace B := hB.twoSimplyConnectedSpace
  have hstage : diskAttachmentStage B D l = B := by
    simpa [l] using diskAttachmentStage_finRange_eq_sphere (D := D) hDB
  let _ : SimplyConnectedSpace (diskAttachmentStage B D l) :=
    (Homeomorph.setCongr hstage).toHomotopyEquiv.simplyConnectedSpace
  apply top_unique
  intro g _
  apply hresult.2
  apply MonoidHom.mem_ker.mpr
  exact Subsingleton.elim _ _

end DifferentialGeometry.Topology.PiecewiseLinear
