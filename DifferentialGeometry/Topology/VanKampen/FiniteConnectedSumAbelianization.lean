import DifferentialGeometry.Topology.VanKampen.ConnectedSumAbelianization
import DifferentialGeometry.Topology.VanKampen.FiniteConnectedSumFreeProduct

set_option autoImplicit false

noncomputable section

universe u

namespace DifferentialGeometry.Algebra.Group

private def piFinSuccMulEquiv {n : ℕ} (β : Fin (n + 1) → Type u) [∀ i, Group (β i)] :
    β 0 × (∀ i : Fin n, β i.succ) ≃* (∀ i : Fin (n + 1), β i) where
  toFun p := Fin.cons p.1 p.2
  invFun f := (f 0, fun i => f i.succ)
  left_inv p := by
    refine Prod.ext ?_ ?_
    · simp
    · funext i
      simp
  right_inv f := by
    funext i
    refine Fin.cases ?_ ?_ i <;> simp
  map_mul' p q := by
    funext i
    refine Fin.cases ?_ ?_ i <;> simp

theorem abelianizationCoprodIFinEquivPi (n : ℕ) :
    ∀ (G : Fin n → Type u) [∀ i, Group (G i)],
      Nonempty (Abelianization (Monoid.CoprodI G) ≃* (∀ i, Abelianization (G i))) := by
  induction n with
  | zero =>
    intro G inst
    have hsub : Subsingleton (Monoid.CoprodI G) :=
      (coprodI_subsingleton_iff G).mpr fun i => Fin.elim0 i
    let : Unique (Monoid.CoprodI G) :=
      { default := 1, uniq := fun a => hsub.elim a 1 }
    let : Unique (∀ i : Fin 0, Abelianization (G i)) :=
      { default := fun i => Fin.elim0 i, uniq := fun f => funext fun i => Fin.elim0 i }
    exact ⟨MulEquiv.ofUnique⟩
  | succ n ih =>
    intro G inst
    obtain ⟨e⟩ := @ih (fun i : Fin n => G i.succ) (fun i : Fin n => inst i.succ)
    refine ⟨(MulEquiv.abelianizationCongr (coprodIFinConsEquivCoprod G)).trans
      ((abelianizationCoprodEquivProd (G 0) (Monoid.CoprodI fun i : Fin n => G i.succ)).trans
        (((MulEquiv.refl (Abelianization (G 0))).prodCongr e).trans
          (piFinSuccMulEquiv (fun i : Fin (n + 1) => Abelianization (G i)))))⟩

private def piFinAppendMulEquiv (m n : ℕ) (β : Fin (m + n) → Type u) [∀ i, Group (β i)] :
    (∀ i : Fin m, β (Fin.castAdd n i)) × (∀ i : Fin n, β (Fin.natAdd m i)) ≃*
      (∀ i : Fin (m + n), β i) where
  toFun p := fun i => Fin.addCases (fun j => p.1 j) (fun j => p.2 j) i
  invFun f := (fun i => f (Fin.castAdd n i), fun i => f (Fin.natAdd m i))
  left_inv p := by
    refine Prod.ext ?_ ?_ <;> funext i <;> simp
  right_inv f := by
    funext i
    refine Fin.addCases (fun j => ?_) (fun j => ?_) i <;> simp
  map_mul' p q := by
    funext i
    refine Fin.addCases (fun j => ?_) (fun j => ?_) i <;> simp

theorem abelianizationCoprodIFinEquivPi_append (m n : ℕ) :
    ∀ (G : Fin (m + n) → Type u) [∀ i, Group (G i)],
      Nonempty (Abelianization (Monoid.CoprodI G) ≃*
        ((∀ i : Fin m, Abelianization (G (Fin.castAdd n i))) ×
          (∀ i : Fin n, Abelianization (G (Fin.natAdd m i))))) :=
  fun G _ =>
    (abelianizationCoprodIFinEquivPi (m + n) G).map fun e =>
      e.trans (piFinAppendMulEquiv m n fun i => Abelianization (G i)).symm

end DifferentialGeometry.Algebra.Group

namespace DifferentialGeometry.Topology

theorem abelianization_fundamentalGroup_finiteConnectedSum_freeProduct
    (L : List (ConnectedClosedOrientedManifold.{u} 3))
    (x : (i : Fin L.length) → (L.get i).Carrier)
    (y : (finiteConnectedSum L).Carrier) :
    Nonempty (Abelianization (FundamentalGroup (finiteConnectedSum L).Carrier y) ≃*
      (∀ i : Fin L.length, Abelianization (FundamentalGroup (L.get i).Carrier (x i)))) := by
  obtain ⟨e⟩ := fundamentalGroup_finiteConnectedSum_freeProduct L x y
  exact ⟨e.abelianizationCongr.trans
    (DifferentialGeometry.Algebra.Group.abelianizationCoprodIFinEquivPi L.length
      (fun i : Fin L.length => FundamentalGroup (L.get i).Carrier (x i))).some⟩


end DifferentialGeometry.Topology
