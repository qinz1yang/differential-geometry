/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.Topology.PiecewiseLinear.Section34CompactVocabulary

open Set

namespace DifferentialGeometry.Topology.PiecewiseLinear

universe u v

variable {Vx Tt Ed Fc Pa Ar Eg Mk Ov Oe : Type u} {X : Type v}

theorem iUnion_section34BoundedLabel
    (f : Section34BoundedLabel Vx Tt Ed Fc Pa Ar Eg Mk Ov Oe → Set X) :
    (⋃ l, f l) =
      (⋃ v, f (.vertexBall v)) ∪ (⋃ t, f (.tetraBall t)) ∪
      (⋃ e, f (.splitDisk e)) ∪ (⋃ s, f (.faceDisk s)) ∪
      (⋃ x, f (.patch x)) ∪ (⋃ a, f (.faceArc a)) ∪
      (⋃ i, f (.edgeArc i)) ∪ (⋃ p, f (.markedPoint p)) ∪
      (⋃ o, f (.outerFace o)) ∪ (⋃ q, f (.outerArc q)) := by
  ext x
  simp only [mem_iUnion, mem_union]
  constructor
  · rintro ⟨l, hl⟩
    cases l with
    | vertexBall a =>
      exact Or.inl (Or.inl (Or.inl (Or.inl (
        Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (⟨a, hl⟩)))))))))
    | tetraBall a =>
      exact Or.inl (Or.inl (Or.inl (Or.inl (
        Or.inl (Or.inl (Or.inl (Or.inl (Or.inr ⟨a, hl⟩))))))))
    | splitDisk a =>
      exact Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inr ⟨a, hl⟩)))))))
    | faceDisk a =>
      exact Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inr ⟨a, hl⟩))))))
    | patch a =>
      exact Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inr ⟨a, hl⟩)))))
    | faceArc a =>
      exact Or.inl (Or.inl (Or.inl (Or.inl (Or.inr ⟨a, hl⟩))))
    | edgeArc a =>
      exact Or.inl (Or.inl (Or.inl (Or.inr ⟨a, hl⟩)))
    | markedPoint a =>
      exact Or.inl (Or.inl (Or.inr ⟨a, hl⟩))
    | outerFace a =>
      exact Or.inl (Or.inr ⟨a, hl⟩)
    | outerArc a =>
      exact Or.inr ⟨a, hl⟩
  · rintro (((((((((h | h) | h) | h) | h) | h) | h) | h) | h) | h)
    all_goals obtain ⟨a, ha⟩ := h
    all_goals first
      | exact ⟨.vertexBall a, ha⟩
      | exact ⟨.tetraBall a, ha⟩
      | exact ⟨.splitDisk a, ha⟩
      | exact ⟨.faceDisk a, ha⟩
      | exact ⟨.patch a, ha⟩
      | exact ⟨.faceArc a, ha⟩
      | exact ⟨.edgeArc a, ha⟩
      | exact ⟨.markedPoint a, ha⟩
      | exact ⟨.outerFace a, ha⟩
      | exact ⟨.outerArc a, ha⟩

end DifferentialGeometry.Topology.PiecewiseLinear
