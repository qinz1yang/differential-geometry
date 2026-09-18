import Mathlib.AlgebraicTopology.FundamentalGroupoid.FundamentalGroup

namespace DifferentialGeometry.Topology

open Path

variable {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y] {x : X}

noncomputable def loopPow (p : Path x x) : ℕ → Path x x
  | 0 => Path.refl x
  | k + 1 => p.trans (loopPow p k)

noncomputable def loopZPow (p : Path x x) : ℤ → Path x x
  | Int.ofNat k => loopPow p k
  | Int.negSucc k => loopPow p.symm (k + 1)

theorem loopPow_zero (p : Path x x) : loopPow p 0 = Path.refl x := rfl

theorem loopPow_succ (p : Path x x) (k : ℕ) :
    loopPow p (k + 1) = p.trans (loopPow p k) := rfl

theorem loopZPow_natCast (p : Path x x) (k : ℕ) : loopZPow p (k : ℤ) = loopPow p k := rfl

theorem loopZPow_negSucc (p : Path x x) (k : ℕ) :
    loopZPow p (Int.negSucc k) = loopPow p.symm (k + 1) := rfl

theorem refl_map {f : X → Y} (hf : Continuous f) (a : X) :
    (Path.refl a).map hf = Path.refl (f a) := rfl

theorem symm_map (p : Path x x) {f : X → Y} (hf : Continuous f) :
    p.symm.map hf = (p.map hf).symm := rfl

theorem loopPow_map (p : Path x x) {f : X → Y} (hf : Continuous f) (k : ℕ) :
    (loopPow p k).map hf = loopPow (p.map hf) k := by
  induction k with
  | zero => rfl
  | succ k ih => rw [loopPow_succ, Path.map_trans, ih, loopPow_succ]

theorem loopZPow_map (p : Path x x) {f : X → Y} (hf : Continuous f) (k : ℤ) :
    (loopZPow p k).map hf = loopZPow (p.map hf) k := by
  cases k with
  | ofNat k => exact loopPow_map p hf k
  | negSucc k => rw [loopZPow_negSucc, loopPow_map, symm_map, loopZPow_negSucc]

theorem loopPow_homotopic {p q : Path x x} (h : p.Homotopic q) (k : ℕ) :
    (loopPow p k).Homotopic (loopPow q k) := by
  induction k with
  | zero => exact Path.Homotopic.refl _
  | succ k ih => exact h.hcomp ih

theorem loopZPow_homotopic {p q : Path x x} (h : p.Homotopic q) (k : ℤ) :
    (loopZPow p k).Homotopic (loopZPow q k) := by
  cases k with
  | ofNat k => exact loopPow_homotopic h k
  | negSucc k => exact loopPow_homotopic h.symm₂ (k + 1)

theorem cast_rfl (p : Path x x) : p.cast rfl rfl = p := rfl

theorem loopPow_cast {y : X} (p : Path x x) (hx : y = x) (k : ℕ) :
    (loopPow p k).cast hx hx = loopPow (p.cast hx hx) k := by
  cases hx
  rfl

theorem loopZPow_cast {y : X} (p : Path x x) (hx : y = x) (k : ℤ) :
    (loopZPow p k).cast hx hx = loopZPow (p.cast hx hx) k := by
  cases hx
  rfl

theorem fromPath_loopPow (p : Path x x) (k : ℕ) :
    (FundamentalGroup.fromPath (Path.Homotopic.Quotient.mk (loopPow p k)) :
        FundamentalGroup X x) =
      FundamentalGroup.fromPath (Path.Homotopic.Quotient.mk p) ^ k := by
  induction k with
  | zero => exact (FundamentalGroup.one_def (x := x)).symm
  | succ k ih =>
      change (Path.Homotopic.Quotient.mk (p.trans (loopPow p k)) : FundamentalGroup X x) = _
      rw [Path.Homotopic.Quotient.mk_trans, pow_succ, ← ih, FundamentalGroup.mul_def]

theorem fromPath_symm (p : Path x x) :
    (FundamentalGroup.fromPath (Path.Homotopic.Quotient.mk p.symm) : FundamentalGroup X x) =
      (FundamentalGroup.fromPath (Path.Homotopic.Quotient.mk p))⁻¹ :=
  (FundamentalGroup.inv_def (p := FundamentalGroup.fromPath
    (Path.Homotopic.Quotient.mk p))).symm

theorem fromPath_loopZPow (p : Path x x) (k : ℤ) :
    (FundamentalGroup.fromPath (Path.Homotopic.Quotient.mk (loopZPow p k)) :
        FundamentalGroup X x) =
      FundamentalGroup.fromPath (Path.Homotopic.Quotient.mk p) ^ k := by
  cases k with
  | ofNat k =>
      have hk : (Int.ofNat k) = (k : ℤ) := rfl
      rw [hk, loopZPow_natCast, fromPath_loopPow, zpow_natCast]
  | negSucc k =>
      rw [loopZPow_negSucc, fromPath_loopPow, fromPath_symm, zpow_negSucc, inv_pow]

theorem exists_homotopic_loopZPow_of_forall_exists_zpow
    {p : Path x x}
    (h : ∀ a : FundamentalGroup X x,
      ∃ k : ℤ, a = FundamentalGroup.fromPath (Path.Homotopic.Quotient.mk p) ^ k)
    (m : Path x x) : ∃ k : ℤ, m.Homotopic (loopZPow p k) := by
  obtain ⟨k, hk⟩ := h (FundamentalGroup.fromPath (Path.Homotopic.Quotient.mk m))
  refine ⟨k, Path.Homotopic.Quotient.eq.mp ?_⟩
  rw [← fromPath_loopZPow] at hk
  exact hk

end DifferentialGeometry.Topology
