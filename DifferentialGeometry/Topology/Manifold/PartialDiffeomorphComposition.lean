import Mathlib.Geometry.Manifold.LocalDiffeomorph
import Lean.Elab.Tactic.Omega

set_option autoImplicit false

noncomputable section

universe u uE uH

namespace DifferentialGeometry
namespace HCGCompactness

open scoped Manifold ContDiff

variable {E : Type uE} [NormedAddCommGroup E] [NormedSpace Real E]
variable [FiniteDimensional Real E]
variable [NeZero (Module.finrank Real E)] [CompleteSpace E]
variable {H : Type uH} [TopologicalSpace H]
variable {I : ModelWithCorners Real E H} [I.Boundaryless]
variable {M : Type u} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
variable {N : Type u} [TopologicalSpace N] [ChartedSpace H N] [IsManifold I ∞ N]

section PartialTrans

noncomputable def PartialDiffeomorph.trans {P : Type u} [TopologicalSpace P]
    [ChartedSpace H P] [hManifoldP : IsManifold I ∞ P]
    (Φ : PartialDiffeomorph I I M N (∞ : WithTop ℕ∞))
    (Φ' : PartialDiffeomorph I I N P (∞ : WithTop ℕ∞)) :
    PartialDiffeomorph I I M P (∞ : WithTop ℕ∞) where
  toPartialEquiv := Φ.toPartialEquiv.trans Φ'.toPartialEquiv
  open_source := by
    let _ := hManifoldP
    have hsrc : (Φ.toPartialEquiv.trans Φ'.toPartialEquiv).source
        = Φ.source ∩ (Φ : M → N) ⁻¹' Φ'.source := rfl
    rw [hsrc]
    exact Φ.contMDiffOn_toFun.continuousOn.isOpen_inter_preimage Φ.open_source
      Φ'.open_source
  open_target := by
    have htgt : (Φ.toPartialEquiv.trans Φ'.toPartialEquiv).target
        = Φ'.target ∩ (Φ'.symm : P → N) ⁻¹' Φ.target := by
      rw [PartialEquiv.trans_target]
      rfl
    rw [htgt]
    exact Φ'.symm.contMDiffOn_toFun.continuousOn.isOpen_inter_preimage Φ'.open_target
      Φ.open_target
  contMDiffOn_toFun := by
    have hsrc : (Φ.toPartialEquiv.trans Φ'.toPartialEquiv).source
        = Φ.source ∩ (Φ : M → N) ⁻¹' Φ'.source := rfl
    rw [hsrc]
    exact Φ'.contMDiffOn_toFun.comp
      (Φ.contMDiffOn_toFun.mono Set.inter_subset_left)
      (fun y hy => hy.2)
  contMDiffOn_invFun := by
    have htgt : (Φ.toPartialEquiv.trans Φ'.toPartialEquiv).target
        = Φ'.target ∩ (Φ'.symm : P → N) ⁻¹' Φ.target := by
      rw [PartialEquiv.trans_target]
      rfl
    rw [htgt]
    exact Φ.symm.contMDiffOn_toFun.comp
      (Φ'.symm.contMDiffOn_toFun.mono Set.inter_subset_left)
      (fun y hy => hy.2)

end PartialTrans


section Chain

noncomputable def PartialDiffeomorph.refl (M : Type u) [TopologicalSpace M]
    [ChartedSpace H M] [hManifold : IsManifold I ∞ M] :
    PartialDiffeomorph I I M M (∞ : WithTop ℕ∞) where
  toPartialEquiv := PartialEquiv.refl M
  open_source := let _ := hManifold; isOpen_univ
  open_target := isOpen_univ
  contMDiffOn_toFun := contMDiff_id.contMDiffOn
  contMDiffOn_invFun := contMDiff_id.contMDiffOn

noncomputable def chainComp {Mf : ℕ → Type u} [∀ j, TopologicalSpace (Mf j)]
    [∀ j, ChartedSpace H (Mf j)] [∀ j, IsManifold I ∞ (Mf j)]
    (Ψ : ∀ j, PartialDiffeomorph I I (Mf j) (Mf (j + 1)) (∞ : WithTop ℕ∞)) (j l : ℕ) :
    PartialDiffeomorph I I (Mf j) (Mf (j + l)) (∞ : WithTop ℕ∞) :=
  Nat.rec
    (motive := fun l => PartialDiffeomorph I I (Mf j) (Mf (j + l)) (∞ : WithTop ℕ∞))
    (PartialDiffeomorph.refl (I := I) (Mf j))
    (fun l prev =>
      PartialDiffeomorph.trans (E := E) (H := H) (I := I) (M := Mf j)
        (N := Mf (j + l)) (P := Mf (j + l + 1)) prev (Ψ (j + l)))
    l

noncomputable def chainComp' {Mf : ℕ → Type u} [∀ j, TopologicalSpace (Mf j)]
    [∀ j, ChartedSpace H (Mf j)] [∀ j, IsManifold I ∞ (Mf j)]
    (Ψ : ∀ j, PartialDiffeomorph I I (Mf j) (Mf (j + 1)) (∞ : WithTop ℕ∞)) :
    ∀ (l j m : ℕ), j + l = m → PartialDiffeomorph I I (Mf j) (Mf m) (∞ : WithTop ℕ∞) :=
  Nat.rec
    (motive := fun l => ∀ j m : ℕ, j + l = m →
      PartialDiffeomorph I I (Mf j) (Mf m) (∞ : WithTop ℕ∞))
    (fun j m h => (Nat.add_zero j ▸ h : j = m) ▸ PartialDiffeomorph.refl (I := I) (Mf j))
    (fun l ih j m h =>
      PartialDiffeomorph.trans (E := E) (H := H) (I := I) (M := Mf j)
        (N := Mf (j + 1)) (P := Mf m) (Ψ j) (ih (j + 1) m (by omega)))

omit [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)] [CompleteSpace E] [I.Boundaryless] in
theorem chainComp_apply_succ {Mf : ℕ → Type u} [∀ j, TopologicalSpace (Mf j)]
    [∀ j, ChartedSpace H (Mf j)] [∀ j, IsManifold I ∞ (Mf j)]
    (Ψ : ∀ j, PartialDiffeomorph I I (Mf j) (Mf (j + 1)) (∞ : WithTop ℕ∞))
    (j l : ℕ) (x : Mf j) :
    (chainComp (I := I) (Mf := Mf) Ψ j (l + 1) : Mf j → Mf (j + (l + 1))) x
      = (Ψ (j + l) : Mf (j + l) → Mf (j + l + 1))
          ((chainComp (I := I) (Mf := Mf) Ψ j l : Mf j → Mf (j + l)) x) :=
  rfl

omit [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)] [CompleteSpace E] [I.Boundaryless] in
theorem chainComp_base {Mf : ℕ → Type u} [∀ j, TopologicalSpace (Mf j)]
    [∀ j, ChartedSpace H (Mf j)] [∀ j, IsManifold I ∞ (Mf j)]
    (Ψ : ∀ j, PartialDiffeomorph I I (Mf j) (Mf (j + 1)) (∞ : WithTop ℕ∞))
    (b : ∀ j, Mf j)
    (hbase : ∀ j, (Ψ j : Mf j → Mf (j + 1)) (b j) = b (j + 1))
    (j l : ℕ) :
    (chainComp (I := I) (Mf := Mf) Ψ j l : Mf j → Mf (j + l)) (b j) = b (j + l) := by
  induction l with
  | zero =>
      rfl
  | succ l ih =>
      rw [chainComp_apply_succ, ih]
      change (Ψ (j + l) : Mf (j + l) → Mf ((j + l) + 1)) (b (j + l)) =
        b ((j + l) + 1)
      exact hbase (j + l)

omit [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)] [CompleteSpace E] [I.Boundaryless] in
theorem chainComp_add_apply {Mf : ℕ → Type u} [∀ j, TopologicalSpace (Mf j)]
    [∀ j, ChartedSpace H (Mf j)] [∀ j, IsManifold I ∞ (Mf j)]
    (Ψ : ∀ j, PartialDiffeomorph I I (Mf j) (Mf (j + 1)) (∞ : WithTop ℕ∞))
    (j a b : ℕ) (x : Mf j) :
    cast (congrArg Mf (Nat.add_assoc j a b).symm)
        ((chainComp (I := I) (Mf := Mf) Ψ j (a + b) : Mf j → Mf (j + (a + b))) x) =
      (chainComp (I := I) (Mf := Mf) Ψ (j + a) b : Mf (j + a) → Mf ((j + a) + b))
        ((chainComp (I := I) (Mf := Mf) Ψ j a : Mf j → Mf (j + a)) x) := by
  have cast_step : ∀ (m n : ℕ) (h : m = n) (y : Mf m),
      cast (congrArg Mf (congrArg Nat.succ h))
          ((Ψ m : Mf m → Mf (m + 1)) y) =
        (Ψ n : Mf n → Mf (n + 1)) (cast (congrArg Mf h) y) := by
    intro m n h y
    subst h
    rfl
  induction b with
  | zero =>
      rfl
  | succ b ih =>
      change
        cast (congrArg Mf (Nat.add_assoc j a (b + 1)).symm)
            ((Ψ (j + (a + b)) : Mf (j + (a + b)) → Mf (j + (a + b) + 1))
              ((chainComp (I := I) (Mf := Mf) Ψ j (a + b) :
                Mf j → Mf (j + (a + b))) x)) =
          (Ψ ((j + a) + b) : Mf ((j + a) + b) → Mf ((j + a) + b + 1))
            ((chainComp (I := I) (Mf := Mf) Ψ (j + a) b :
              Mf (j + a) → Mf ((j + a) + b))
              ((chainComp (I := I) (Mf := Mf) Ψ j a : Mf j → Mf (j + a)) x))
      calc
        cast (congrArg Mf (Nat.add_assoc j a (b + 1)).symm)
            ((Ψ (j + (a + b)) : Mf (j + (a + b)) → Mf (j + (a + b) + 1))
              ((chainComp (I := I) (Mf := Mf) Ψ j (a + b) :
                Mf j → Mf (j + (a + b))) x)) =
            (Ψ ((j + a) + b) : Mf ((j + a) + b) → Mf ((j + a) + b + 1))
              (cast (congrArg Mf (Nat.add_assoc j a b).symm)
                ((chainComp (I := I) (Mf := Mf) Ψ j (a + b) :
                  Mf j → Mf (j + (a + b))) x)) := by
              simpa only [Nat.add_succ] using
                cast_step (j + (a + b)) ((j + a) + b) (Nat.add_assoc j a b).symm
                  ((chainComp (I := I) (Mf := Mf) Ψ j (a + b) :
                    Mf j → Mf (j + (a + b))) x)
        _ = (Ψ ((j + a) + b) : Mf ((j + a) + b) → Mf ((j + a) + b + 1))
              ((chainComp (I := I) (Mf := Mf) Ψ (j + a) b :
                Mf (j + a) → Mf ((j + a) + b))
                ((chainComp (I := I) (Mf := Mf) Ψ j a : Mf j → Mf (j + a)) x)) := by
              rw [ih]

noncomputable def chainCompAssoc {Mf : ℕ → Type u} [∀ j, TopologicalSpace (Mf j)]
    [∀ j, ChartedSpace H (Mf j)] [∀ j, IsManifold I ∞ (Mf j)]
    (Ψ : ∀ j, PartialDiffeomorph I I (Mf j) (Mf (j + 1)) (∞ : WithTop ℕ∞))
    (j a b : ℕ) :
    PartialDiffeomorph I I (Mf j) (Mf ((j + a) + b)) (∞ : WithTop ℕ∞) :=
  (Nat.add_assoc j a b).symm ▸ chainComp (I := I) (Mf := Mf) Ψ j (a + b)

omit [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)] [CompleteSpace E] [I.Boundaryless] in
private theorem targetCast_source {Mf : ℕ → Type u} [∀ j, TopologicalSpace (Mf j)]
    [∀ j, ChartedSpace H (Mf j)]
    {j l m : ℕ} (h : l = m)
    (Φ : PartialDiffeomorph I I (Mf j) (Mf l) (∞ : WithTop ℕ∞)) :
    (h ▸ Φ).source = Φ.source := by
  subst h
  rfl

omit [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)] [CompleteSpace E] [I.Boundaryless] in
theorem chainAssoc_source {Mf : ℕ → Type u} [∀ j, TopologicalSpace (Mf j)]
    [∀ j, ChartedSpace H (Mf j)] [∀ j, IsManifold I ∞ (Mf j)]
    (Ψ : ∀ j, PartialDiffeomorph I I (Mf j) (Mf (j + 1)) (∞ : WithTop ℕ∞))
    (j a b : ℕ) :
    (chainCompAssoc (I := I) (Mf := Mf) Ψ j a b).source =
      (chainComp (I := I) (Mf := Mf) Ψ j (a + b)).source := by
  simpa only [chainCompAssoc] using
    targetCast_source (I := I) (Nat.add_assoc j a b).symm
      (chainComp (I := I) (Mf := Mf) Ψ j (a + b))

omit [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)] [CompleteSpace E] [I.Boundaryless] in
theorem chainCompAssoc_apply {Mf : ℕ → Type u} [∀ j, TopologicalSpace (Mf j)]
    [∀ j, ChartedSpace H (Mf j)] [∀ j, IsManifold I ∞ (Mf j)]
    (Ψ : ∀ j, PartialDiffeomorph I I (Mf j) (Mf (j + 1)) (∞ : WithTop ℕ∞))
    (j a b : ℕ) (x : Mf j) :
    (chainCompAssoc (I := I) (Mf := Mf) Ψ j a b : Mf j → Mf ((j + a) + b)) x =
      (chainComp (I := I) (Mf := Mf) Ψ (j + a) b : Mf (j + a) → Mf ((j + a) + b))
        ((chainComp (I := I) (Mf := Mf) Ψ j a : Mf j → Mf (j + a)) x) := by
  have cast_apply : ∀ {m n : ℕ} (h : m = n)
      (F : PartialDiffeomorph I I (Mf j) (Mf m) (∞ : WithTop ℕ∞)) (y : Mf j),
      ((h ▸ F : PartialDiffeomorph I I (Mf j) (Mf n) (∞ : WithTop ℕ∞)) : Mf j → Mf n) y =
        cast (congrArg Mf h) ((F : Mf j → Mf m) y) := by
    intro m n h F y
    subst h
    rfl
  unfold chainCompAssoc
  rw [cast_apply]
  exact chainComp_add_apply (I := I) (Mf := Mf) Ψ j a b x

omit [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)] [CompleteSpace E] [I.Boundaryless] in
theorem chainCompAssoc_eq {Mf : ℕ → Type u} [∀ j, TopologicalSpace (Mf j)]
    [∀ j, ChartedSpace H (Mf j)] [∀ j, IsManifold I ∞ (Mf j)]
    (Ψ : ∀ j, PartialDiffeomorph I I (Mf j) (Mf (j + 1)) (∞ : WithTop ℕ∞))
    (j a b : ℕ) :
    (chainCompAssoc (I := I) (Mf := Mf) Ψ j a b : Mf j → Mf ((j + a) + b)) =
      (_root_.PartialDiffeomorph.trans (I := I)
        (chainComp (I := I) (Mf := Mf) Ψ j a)
        (chainComp (I := I) (Mf := Mf) Ψ (j + a) b) : Mf j → Mf ((j + a) + b)) := by
  funext x
  exact chainCompAssoc_apply (I := I) (Mf := Mf) Ψ j a b x

omit [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)] [CompleteSpace E] [I.Boundaryless] in
theorem chainComp'_apply_succ {Mf : ℕ → Type u} [∀ j, TopologicalSpace (Mf j)]
    [∀ j, ChartedSpace H (Mf j)] [∀ j, IsManifold I ∞ (Mf j)]
    (Ψ : ∀ j, PartialDiffeomorph I I (Mf j) (Mf (j + 1)) (∞ : WithTop ℕ∞))
    (l j m : ℕ) (h : j + (l + 1) = m) (x : Mf j) :
    (chainComp' (I := I) (Mf := Mf) Ψ (l + 1) j m h : Mf j → Mf m) x
      = (chainComp' (I := I) (Mf := Mf) Ψ l (j + 1) m (by omega) : Mf (j + 1) → Mf m)
          ((Ψ j : Mf j → Mf (j + 1)) x) :=
  rfl

omit [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)] [CompleteSpace E] [I.Boundaryless] in
theorem chainComp'_apply_zero {Mf : ℕ → Type u} [∀ j, TopologicalSpace (Mf j)]
    [∀ j, ChartedSpace H (Mf j)] [∀ j, IsManifold I ∞ (Mf j)]
    (Ψ : ∀ j, PartialDiffeomorph I I (Mf j) (Mf (j + 1)) (∞ : WithTop ℕ∞))
    (j m : ℕ) (h : j + 0 = m) (x : Mf j) :
    (chainComp' (I := I) (Mf := Mf) Ψ 0 j m h : Mf j → Mf m) x
      = (Nat.add_zero j ▸ h : j = m) ▸ x := by
  have hj : j = m := Nat.add_zero j ▸ h
  subst hj
  rfl

omit [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)] [CompleteSpace E] [I.Boundaryless] in
theorem chainComp'_snoc {Mf : ℕ → Type u} [∀ j, TopologicalSpace (Mf j)]
    [∀ j, ChartedSpace H (Mf j)] [∀ j, IsManifold I ∞ (Mf j)]
    (Ψ : ∀ j, PartialDiffeomorph I I (Mf j) (Mf (j + 1)) (∞ : WithTop ℕ∞)) :
    ∀ (l j m : ℕ) (h : j + (l + 1) = m) (x : Mf j),
      (chainComp' (I := I) (Mf := Mf) Ψ (l + 1) j m h : Mf j → Mf m) x
        = (h ▸ ((Ψ (j + l) : Mf (j + l) → Mf (j + l + 1))
            ((chainComp' (I := I) (Mf := Mf) Ψ l j (j + l) rfl :
              Mf j → Mf (j + l)) x)) : Mf m) := by
  intro l
  induction l with
  | zero =>
      intro j m h x
      subst h
      rw [chainComp'_apply_succ, chainComp'_apply_zero, chainComp'_apply_zero]
      rfl
  | succ l ih =>
      intro j m h x
      subst h
      rw [chainComp'_apply_succ,
        ih (j + 1) (j + (l + 1 + 1)) (by omega) ((Ψ j : Mf j → Mf (j + 1)) x)]
      conv_rhs => rw [chainComp'_apply_succ]
      have hcast : ∀ (a : ℕ) (ha : (j + 1) + l = a),
          (Ψ a : Mf a → Mf (a + 1))
              ((chainComp' (I := I) (Mf := Mf) Ψ l (j + 1) a ha : Mf (j + 1) → Mf a)
                ((Ψ j : Mf j → Mf (j + 1)) x))
            = ha ▸ ((Ψ ((j + 1) + l) : Mf ((j + 1) + l) → Mf ((j + 1) + l + 1))
                ((chainComp' (I := I) (Mf := Mf) Ψ l (j + 1) ((j + 1) + l) rfl :
                    Mf (j + 1) → Mf ((j + 1) + l))
                  ((Ψ j : Mf j → Mf (j + 1)) x))) := by
        intro a ha; subst ha; rfl
      rw [hcast (j + (l + 1)) (by omega)]
      simp only [eqRec_eq_cast]

omit [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)] [CompleteSpace E] [I.Boundaryless] in
theorem chainComp_eq_right {Mf : ℕ → Type u} [∀ j, TopologicalSpace (Mf j)]
    [∀ j, ChartedSpace H (Mf j)] [∀ j, IsManifold I ∞ (Mf j)]
    (Ψ : ∀ j, PartialDiffeomorph I I (Mf j) (Mf (j + 1)) (∞ : WithTop ℕ∞))
    (l j : ℕ) :
    (chainComp (I := I) (Mf := Mf) Ψ j l : Mf j → Mf (j + l))
      = (chainComp' (I := I) (Mf := Mf) Ψ l j (j + l) rfl :
          Mf j → Mf (j + l)) := by
  funext x
  induction l generalizing j with
  | zero =>
      rw [chainComp'_apply_zero]
      rfl
  | succ l ih =>
      rw [chainComp_apply_succ, ih j, chainComp'_snoc]

omit [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)] [CompleteSpace E] [I.Boundaryless] in
theorem chainComp_coe_head {Mf : ℕ → Type u} [∀ j, TopologicalSpace (Mf j)]
    [∀ j, ChartedSpace H (Mf j)] [∀ j, IsManifold I ∞ (Mf j)]
    (Ψ : ∀ j, PartialDiffeomorph I I (Mf j) (Mf (j + 1)) (∞ : WithTop ℕ∞)) :
    ∀ (l j : ℕ) (x : Mf j),
      (chainComp (I := I) (Mf := Mf) Ψ j (l + 1) : Mf j → Mf (j + (l + 1))) x
        = (chainComp' (I := I) (Mf := Mf) Ψ l (j + 1) (j + (l + 1)) (by omega) :
            Mf (j + 1) → Mf (j + (l + 1)))
            ((Ψ j : Mf j → Mf (j + 1)) x) := by
  have lemmaA : ∀ (l j : ℕ) (x : Mf j),
      (chainComp (I := I) (Mf := Mf) Ψ j l : Mf j → Mf (j + l)) x
        = (chainComp' (I := I) (Mf := Mf) Ψ l j (j + l) rfl :
            Mf j → Mf (j + l)) x := by
    intro l
    induction l with
    | zero =>
        intro j x
        rw [chainComp'_apply_zero]
        rfl
    | succ l ih =>
        intro j x
        rw [chainComp_apply_succ, ih j x, chainComp'_snoc]
  intro l j x
  rw [lemmaA (l + 1) j x]
  rw [chainComp'_apply_succ]

end Chain

end HCGCompactness
end DifferentialGeometry
