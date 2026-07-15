/-
Copyright (c) 2024 Yury Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury Kudryashov
Coauthors: Jack McCarthy
-/
import DifferentialGeometry.Tensor.Alternating.Bundle
import DifferentialGeometry.Tensor.Alternating.FDeriv
import DifferentialGeometry.Tensor.Alternating.Wedge
import Mathlib.Analysis.Calculus.FDeriv.Symmetric
import Mathlib.Geometry.Manifold.VectorBundle.SmoothSection
import Mathlib.Geometry.Manifold.VectorBundle.Tangent

/-! # Differential forms: the `DifferentialForm` structure and its module instances -/

noncomputable section

open Filter ContinuousAlternatingMap Set
open scoped Topology

variable {E F F' F'' G : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]
  [NormedAddCommGroup F'] [NormedSpace ℝ F']
  [NormedAddCommGroup F''] [NormedSpace ℝ F'']
  [NormedAddCommGroup G] [NormedSpace ℝ G]
  {n m k : ℕ}

/-- A smooth (C∞) differential n-form on `E` with values in `F`. -/
structure DifferentialForm (n : ℕ) (E : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E]
    (F : Type*) [NormedAddCommGroup F] [NormedSpace ℝ F] where

  toFun : E → E [⋀^Fin n]→L[ℝ] F

  smooth : ContDiff ℝ ⊤ toFun

/-- Notation for smooth differential n-forms from `E` to `F`. -/
notation "Ω^" n "⟮" E ", " F "⟯" => DifferentialForm n E F

instance : FunLike (DifferentialForm n E F) E (E [⋀^Fin n]→L[ℝ] F) where
  coe := DifferentialForm.toFun
  coe_injective' := fun ⟨_, _⟩ ⟨_, _⟩ h => by cases h; rfl

@[ext]
theorem ext {ω τ : DifferentialForm n E F} (h : ∀ x, ω x = τ x) : ω = τ :=
  DFunLike.ext _ _ h

instance instZero : Zero (DifferentialForm n E F) where
  zero := ⟨0, contDiff_const⟩

instance instAdd : Add (DifferentialForm n E F) where
  add ω τ := ⟨fun x => ω x + τ x, ω.smooth.add τ.smooth⟩

instance instNeg : Neg (DifferentialForm n E F) where
  neg ω := ⟨fun x => -ω x, ω.smooth.neg⟩

instance instSub : Sub (DifferentialForm n E F) where
  sub ω τ := ⟨fun x => ω x - τ x, ω.smooth.sub τ.smooth⟩

instance instSMul : SMul ℝ (DifferentialForm n E F) where
  smul c ω := ⟨fun x => c • ω x, ω.smooth.const_smul c⟩

namespace DifferentialForm

@[simp] theorem zero_apply (x : E) : (0 : DifferentialForm n E F) x = 0 := rfl
@[simp] theorem add_apply (ω τ : DifferentialForm n E F) (x : E) :
    (ω + τ) x = ω x + τ x := rfl
@[simp] theorem neg_apply (ω : DifferentialForm n E F) (x : E) : (-ω) x = -ω x := rfl
@[simp] theorem sub_apply (ω τ : DifferentialForm n E F) (x : E) :
    (ω - τ) x = ω x - τ x := rfl
@[simp] theorem smul_apply (c : ℝ) (ω : DifferentialForm n E F) (x : E) :
    (c • ω) x = c • ω x := rfl

end DifferentialForm
