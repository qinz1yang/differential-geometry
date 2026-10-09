/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.Topology.PiecewiseLinear.LoopTheorem.LemmaThree
import DifferentialGeometry.Topology.PiecewiseLinear.LoopTheorem.EmbeddedDisk

open Set

namespace DifferentialGeometry.Topology.PiecewiseLinear

open CategoryTheory in
theorem fundamentalGroupChangeBasepoint_loopRepresentativeAlong
    {X : Type*} [TopologicalSpace X] {x y z : X}
    (β : Path x y) (q : Path y z) (γ : basedCircleLoop z) :
    fundamentalGroupChangeBasepoint β (loopRepresentativeAlong q γ) =
      loopRepresentativeAlong (β.trans q) γ := by
  let b : FundamentalGroupoid.mk x ⟶ FundamentalGroupoid.mk y := ⟦β⟧
  let c : FundamentalGroupoid.mk y ⟶ FundamentalGroupoid.mk z := ⟦q⟧
  let g : FundamentalGroup X z := basedCircleFundamentalGroupClass γ
  change (b ≫ ((c ≫ g) ≫ Groupoid.inv c)) ≫ Groupoid.inv b =
    ((b ≫ c) ≫ g) ≫ Groupoid.inv (b ≫ c)
  simp [Category.assoc]

open Classical in
theorem normalSystemLoopConjugacyClass_comap_changeBasepoint_iff
    {X : Type*} [TopologicalSpace X] {x y : X}
    (β : Path x y) (γ : freeLoop X) (q : Path y (γ 0))
    (N : Subgroup (FundamentalGroup X x)) [N.Normal] :
    conjugacyClassMeets (normalSystemLoopConjugacyClass y γ q)
        (N.comap (fundamentalGroupChangeBasepoint β).toMonoidHom) ↔
      conjugacyClassMeets (normalSystemLoopConjugacyClass x γ (β.trans q)) N := by
  constructor
  · intro h
    have hmem := (conjugacyClassMeets_iff_carrier_subset _
      (N.comap (fundamentalGroupChangeBasepoint β).toMonoidHom)).mp h
        (ConjClasses.mem_carrier_iff_mk_eq.mpr rfl)
    change fundamentalGroupChangeBasepoint β (loopRepresentativeAlong q ⟨γ, rfl⟩) ∈ N at hmem
    rw [fundamentalGroupChangeBasepoint_loopRepresentativeAlong] at hmem
    exact ⟨_, ConjClasses.mem_carrier_iff_mk_eq.mpr rfl, hmem⟩
  · intro h
    have hmem := (conjugacyClassMeets_iff_carrier_subset _ N).mp h
      (ConjClasses.mem_carrier_iff_mk_eq.mpr rfl)
    refine ⟨loopRepresentativeAlong q ⟨γ, rfl⟩,
      ConjClasses.mem_carrier_iff_mk_eq.mpr rfl, ?_⟩
    change fundamentalGroupChangeBasepoint β (loopRepresentativeAlong q ⟨γ, rfl⟩) ∈ N
    rw [fundamentalGroupChangeBasepoint_loopRepresentativeAlong]
    exact hmem

namespace NormalSystem

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

open Classical in
noncomputable def atBoundaryLoop (S : NormalSystem E) : NormalSystem E := by
  let _ : S.normalSubgroup.Normal := S.normal
  refine { S with
    basepoint := S.boundaryLoop 0
    connector := Path.refl _
    normalSubgroup := S.normalSubgroup.comap
      (fundamentalGroupChangeBasepoint S.connector).toMonoidHom
    normal := inferInstance
    loopClass_avoids_normal := ?_ }
  intro h
  have h' := (normalSystemLoopConjugacyClass_comap_changeBasepoint_iff
    S.connector S.boundaryLoop (Path.refl _) S.normalSubgroup).mp h
  rw [S.loopConjugacyClass_eq_of_connector] at h'
  exact S.loopClass_avoids_normal h'

@[simp]
theorem atBoundaryLoop_basepoint (S : NormalSystem E) :
    S.atBoundaryLoop.basepoint = S.atBoundaryLoop.boundaryLoop 0 :=
  rfl

@[simp]
theorem atBoundaryLoop_sourceComplex (S : NormalSystem E) :
    S.atBoundaryLoop.sourceComplex = S.sourceComplex :=
  rfl

@[simp]
theorem atBoundaryLoop_singularMap (S : NormalSystem E) :
    S.atBoundaryLoop.singularMap = S.singularMap :=
  rfl

@[simp]
theorem atBoundaryLoop_complexity (S : NormalSystem E) :
    S.atBoundaryLoop.complexity = S.complexity :=
  rfl

@[simp]
theorem atBoundaryLoop_boundaryComplex (S : NormalSystem E) :
    S.atBoundaryLoop.boundaryComplex = S.boundaryComplex :=
  rfl

@[simp]
theorem atBoundaryLoop_normalSubgroup (S : NormalSystem E) :
    S.atBoundaryLoop.normalSubgroup = S.normalSubgroup.comap
      (fundamentalGroupChangeBasepoint S.connector).toMonoidHom :=
  rfl

open Classical in
noncomputable def NonsingularCell.ofAtBoundaryLoop {S : NormalSystem E}
    (D : NonsingularCell S.atBoundaryLoop) : NonsingularCell S := by
  let _ : S.normalSubgroup.Normal := S.normal
  refine { D with
    connector := S.connector.trans D.connector
    loopClass_avoids_normal := ?_ }
  intro h
  apply D.loopClass_avoids_normal
  exact (normalSystemLoopConjugacyClass_comap_changeBasepoint_iff
    S.connector D.boundaryLoop D.connector S.normalSubgroup).mpr h

@[simp]
theorem NonsingularCell.ofAtBoundaryLoop_sourceComplex {S : NormalSystem E}
    (D : NonsingularCell S.atBoundaryLoop) : D.ofAtBoundaryLoop.sourceComplex = D.sourceComplex :=
  rfl

@[simp]
theorem NonsingularCell.ofAtBoundaryLoop_vertexMap {S : NormalSystem E}
    (D : NonsingularCell S.atBoundaryLoop) : D.ofAtBoundaryLoop.vertexMap = D.vertexMap :=
  rfl

@[simp]
theorem NonsingularCell.ofAtBoundaryLoop_boundaryLoop {S : NormalSystem E}
    (D : NonsingularCell S.atBoundaryLoop) : D.ofAtBoundaryLoop.boundaryLoop = D.boundaryLoop :=
  rfl

open Classical in
noncomputable def EmbeddedDisk.ofAtBoundaryLoop {S : NormalSystem E}
    (D : EmbeddedDisk S.atBoundaryLoop) : EmbeddedDisk S := by
  let _ : S.normalSubgroup.Normal := S.normal
  refine { D with
    connector := S.connector.trans D.connector
    loopClass_avoids_normal := ?_ }
  intro h
  apply D.loopClass_avoids_normal
  exact (normalSystemLoopConjugacyClass_comap_changeBasepoint_iff
    S.connector D.boundaryLoop D.connector S.normalSubgroup).mpr h

@[simp]
theorem EmbeddedDisk.ofAtBoundaryLoop_domain {S : NormalSystem E}
    (D : EmbeddedDisk S.atBoundaryLoop) : D.ofAtBoundaryLoop.domain = D.domain :=
  rfl

@[simp]
theorem EmbeddedDisk.ofAtBoundaryLoop_map {S : NormalSystem E}
    (D : EmbeddedDisk S.atBoundaryLoop) : D.ofAtBoundaryLoop.map = D.map :=
  rfl

@[simp]
theorem EmbeddedDisk.ofAtBoundaryLoop_boundaryLoop {S : NormalSystem E}
    (D : EmbeddedDisk S.atBoundaryLoop) :
    D.ofAtBoundaryLoop.boundaryLoop = D.boundaryLoop :=
  rfl

theorem nonempty_embeddedDisk_of_atBoundaryLoop {S : NormalSystem E}
    (h : Nonempty (EmbeddedDisk S.atBoundaryLoop)) : Nonempty (EmbeddedDisk S) :=
  h.map EmbeddedDisk.ofAtBoundaryLoop

theorem nonempty_nonsingularCell_of_atBoundaryLoop {S : NormalSystem E}
    (h : Nonempty (NonsingularCell S.atBoundaryLoop)) : Nonempty (NonsingularCell S) :=
  h.map NonsingularCell.ofAtBoundaryLoop

end NormalSystem

end DifferentialGeometry.Topology.PiecewiseLinear
