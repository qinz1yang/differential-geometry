import Mathlib.Topology.ContinuousMap.Basic
import Mathlib.Topology.Homotopy.Basic
import Mathlib.Topology.Homotopy.Equiv

namespace DifferentialGeometry.Topology.Homotopy

universe u v w

open ContinuousMap

structure HomotopyEquivUnder {X : Type u} [TopologicalSpace X] {Y : Type v} [TopologicalSpace Y]
    {Z : Type w} [TopologicalSpace Z] (toBase : C(X, Y)) (fromBase : C(X, Z)) where
  toFun : C(Y, Z)
  invFun : C(Z, Y)
  map_toBase : toFun.comp toBase = fromBase
  map_fromBase : invFun.comp fromBase = toBase
  left_inv : ContinuousMap.HomotopyRel (invFun.comp toFun) (ContinuousMap.id Y) (Set.range toBase)
  right_inv : ContinuousMap.HomotopyRel (toFun.comp invFun) (ContinuousMap.id Z) (Set.range fromBase)

namespace HomotopyEquivUnder

variable {X : Type u} [TopologicalSpace X] {Y : Type v} [TopologicalSpace Y]
variable {Z : Type w} [TopologicalSpace Z] {toBase : C(X, Y)} {fromBase : C(X, Z)}

def precompHomotopyRel {X Y W : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    [TopologicalSpace W] {f₀ f₁ : C(X, Y)} {S : Set X} (F : ContinuousMap.HomotopyRel f₀ f₁ S)
    {T : Set W} (h : C(W, X)) (hmaps : Set.MapsTo h T S) :
    ContinuousMap.HomotopyRel (f₀.comp h) (f₁.comp h) T where
  toHomotopy := F.toHomotopy.comp (ContinuousMap.Homotopy.refl h)
  prop' := by
    intro t x hx
    change F (t, h x) = f₀ (h x)
    exact F.prop t (h x) (hmaps hx)

noncomputable def toHomotopyEquiv (e : HomotopyEquivUnder toBase fromBase) :
    ContinuousMap.HomotopyEquiv Y Z where
  toFun := e.toFun
  invFun := e.invFun
  left_inv := ⟨e.left_inv.toHomotopy⟩
  right_inv := ⟨e.right_inv.toHomotopy⟩

@[simp]
theorem toHomotopyEquiv_toFun (e : HomotopyEquivUnder toBase fromBase) :
    e.toHomotopyEquiv.toFun = e.toFun := rfl

@[simp]
theorem toHomotopyEquiv_invFun (e : HomotopyEquivUnder toBase fromBase) :
    e.toHomotopyEquiv.invFun = e.invFun := rfl

theorem map_toBase_apply (e : HomotopyEquivUnder toBase fromBase) (x : X) :
    e.toFun (toBase x) = fromBase x :=
  congrArg (fun f : C(X, Z) => f x) e.map_toBase

theorem map_fromBase_apply (e : HomotopyEquivUnder toBase fromBase) (x : X) :
    e.invFun (fromBase x) = toBase x :=
  congrArg (fun f : C(X, Y) => f x) e.map_fromBase

noncomputable def refl {toBase fromBase : C(X, Y)} (h : toBase = fromBase) :
    HomotopyEquivUnder toBase fromBase where
  toFun := ContinuousMap.id Y
  invFun := ContinuousMap.id Y
  map_toBase := by
    simp [h]
  map_fromBase := by
    simp [h]
  left_inv := by
    simpa using (ContinuousMap.HomotopyRel.refl (ContinuousMap.id Y) (Set.range toBase))
  right_inv := by
    simpa using (ContinuousMap.HomotopyRel.refl (ContinuousMap.id Y) (Set.range fromBase))

noncomputable def symm (e : HomotopyEquivUnder toBase fromBase) :
    HomotopyEquivUnder fromBase toBase where
  toFun := e.invFun
  invFun := e.toFun
  map_toBase := e.map_fromBase
  map_fromBase := e.map_toBase
  left_inv := e.right_inv
  right_inv := e.left_inv

@[simp]
theorem symm_toFun (e : HomotopyEquivUnder toBase fromBase) :
    e.symm.toFun = e.invFun := rfl

@[simp]
theorem symm_invFun (e : HomotopyEquivUnder toBase fromBase) :
    e.symm.invFun = e.toFun := rfl

@[simp]
theorem symm_symm (e : HomotopyEquivUnder toBase fromBase) : e.symm.symm = e := by
  cases e
  rfl

noncomputable def trans {X₁ Y₁ Z₁ W : Type*} [TopologicalSpace X₁] [TopologicalSpace Y₁]
    [TopologicalSpace Z₁] [TopologicalSpace W]
    {toBase₁ : C(X₁, Y₁)} {fromBase₁ : C(X₁, Z₁)}
    {toBase₂ : C(X₁, Z₁)} {fromBase₂ : C(X₁, W)}
    (e₁ : HomotopyEquivUnder toBase₁ fromBase₁) (e₂ : HomotopyEquivUnder toBase₂ fromBase₂)
    (h : fromBase₁ = toBase₂) : HomotopyEquivUnder toBase₁ fromBase₂ where
  toFun := e₂.toFun.comp e₁.toFun
  invFun := e₁.invFun.comp e₂.invFun
  map_toBase := by
    apply ContinuousMap.ext
    intro x
    calc
      e₂.toFun (e₁.toFun (toBase₁ x)) = e₂.toFun (fromBase₁ x) :=
        congrArg e₂.toFun (e₁.map_toBase_apply x)
      _ = e₂.toFun (toBase₂ x) := by rw [h]
      _ = fromBase₂ x := e₂.map_toBase_apply x
  map_fromBase := by
    apply ContinuousMap.ext
    intro x
    calc
      e₁.invFun (e₂.invFun (fromBase₂ x)) = e₁.invFun (toBase₂ x) :=
        congrArg e₁.invFun (e₂.map_fromBase_apply x)
      _ = e₁.invFun (fromBase₁ x) := by rw [← h]
      _ = toBase₁ x := e₁.map_fromBase_apply x
  left_inv := by
    have hmap₂ : Set.MapsTo e₁.toFun (Set.range toBase₁) (Set.range toBase₂) := by
      intro y hy
      rcases hy with ⟨x, rfl⟩
      refine Set.mem_range.mpr ⟨x, ?_⟩
      rw [e₁.map_toBase_apply, h]
    have R₂pre : ContinuousMap.HomotopyRel
        ((e₂.invFun.comp e₂.toFun).comp e₁.toFun) ((ContinuousMap.id Z₁).comp e₁.toFun)
        (Set.range toBase₁) :=
      precompHomotopyRel (S := Set.range toBase₂) (T := Set.range toBase₁) e₂.left_inv e₁.toFun hmap₂
    have R₂post : ContinuousMap.HomotopyRel
        (e₁.invFun.comp ((e₂.invFun.comp e₂.toFun).comp e₁.toFun))
        (e₁.invFun.comp ((ContinuousMap.id Z₁).comp e₁.toFun)) (Set.range toBase₁) :=
      R₂pre.compContinuousMap e₁.invFun
    have R₂post' : ContinuousMap.HomotopyRel
        ((e₁.invFun.comp (e₂.invFun.comp e₂.toFun)).comp e₁.toFun)
        (e₁.invFun.comp e₁.toFun) (Set.range toBase₁) := by
      exact R₂post.cast (by ext x; rfl) (by ext x; rfl)
    have R₂post'' : ContinuousMap.HomotopyRel
        ((e₁.invFun.comp e₂.invFun).comp (e₂.toFun.comp e₁.toFun))
        (e₁.invFun.comp e₁.toFun) (Set.range toBase₁) := by
      exact R₂post'.cast (by ext x; rfl) (by ext x; rfl)
    exact R₂post''.trans e₁.left_inv
  right_inv := by
    have hmap₁ : Set.MapsTo e₂.invFun (Set.range fromBase₂) (Set.range fromBase₁) := by
      intro y hy
      rcases hy with ⟨x, rfl⟩
      refine Set.mem_range.mpr ⟨x, ?_⟩
      rw [e₂.map_fromBase_apply, ← h]
    have R₁pre : ContinuousMap.HomotopyRel
        ((e₁.toFun.comp e₁.invFun).comp e₂.invFun) ((ContinuousMap.id Z₁).comp e₂.invFun)
        (Set.range fromBase₂) :=
      precompHomotopyRel (S := Set.range fromBase₁) (T := Set.range fromBase₂) e₁.right_inv e₂.invFun
        hmap₁
    have R₁post : ContinuousMap.HomotopyRel
        (e₂.toFun.comp ((e₁.toFun.comp e₁.invFun).comp e₂.invFun))
        (e₂.toFun.comp ((ContinuousMap.id Z₁).comp e₂.invFun)) (Set.range fromBase₂) :=
      R₁pre.compContinuousMap e₂.toFun
    have R₁post' : ContinuousMap.HomotopyRel
        ((e₂.toFun.comp (e₁.toFun.comp e₁.invFun)).comp e₂.invFun)
        (e₂.toFun.comp e₂.invFun) (Set.range fromBase₂) := by
      exact R₁post.cast (by ext x; rfl) (by ext x; rfl)
    have R₁post'' : ContinuousMap.HomotopyRel
        ((e₂.toFun.comp e₁.toFun).comp (e₁.invFun.comp e₂.invFun))
        (e₂.toFun.comp e₂.invFun) (Set.range fromBase₂) := by
      exact R₁post'.cast (by ext x; rfl) (by ext x; rfl)
    exact R₁post''.trans e₂.right_inv

@[simp]
theorem trans_toFun (e₁ : HomotopyEquivUnder toBase fromBase) {W : Type*} [TopologicalSpace W]
    {toBase₂ : C(X, Z)} {fromBase₂ : C(X, W)} (e₂ : HomotopyEquivUnder toBase₂ fromBase₂)
    (h : fromBase = toBase₂) :
    (e₁.trans e₂ h).toFun = e₂.toFun.comp e₁.toFun := rfl

@[simp]
theorem trans_invFun (e₁ : HomotopyEquivUnder toBase fromBase) {W : Type*} [TopologicalSpace W]
    {toBase₂ : C(X, Z)} {fromBase₂ : C(X, W)} (e₂ : HomotopyEquivUnder toBase₂ fromBase₂)
    (h : fromBase = toBase₂) :
    (e₁.trans e₂ h).invFun = e₁.invFun.comp e₂.invFun := rfl

@[simp]
theorem toHomotopyEquiv_symm (e : HomotopyEquivUnder toBase fromBase) :
    e.symm.toHomotopyEquiv = e.toHomotopyEquiv.symm := by
  cases e with
  | mk toFun invFun map_toBase map_fromBase left_inv right_inv =>
    rfl

@[simp]
theorem toHomotopyEquiv_refl {toBase fromBase : C(X, Y)} (h : toBase = fromBase) :
    (refl h).toHomotopyEquiv = ContinuousMap.HomotopyEquiv.refl Y := by
  rfl

@[simp]
theorem toHomotopyEquiv_trans {X₁ Y₁ Z₁ W : Type*} [TopologicalSpace X₁] [TopologicalSpace Y₁]
    [TopologicalSpace Z₁] [TopologicalSpace W]
    {toBase₁ : C(X₁, Y₁)} {fromBase₁ : C(X₁, Z₁)}
    {toBase₂ : C(X₁, Z₁)} {fromBase₂ : C(X₁, W)}
    (e₁ : HomotopyEquivUnder toBase₁ fromBase₁) (e₂ : HomotopyEquivUnder toBase₂ fromBase₂)
    (h : fromBase₁ = toBase₂) :
    (e₁.trans e₂ h).toHomotopyEquiv = e₁.toHomotopyEquiv.trans e₂.toHomotopyEquiv := by
  rfl

end HomotopyEquivUnder

end DifferentialGeometry.Topology.Homotopy
