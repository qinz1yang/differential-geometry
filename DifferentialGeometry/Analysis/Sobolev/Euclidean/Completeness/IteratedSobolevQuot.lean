import DifferentialGeometry.Analysis.Sobolev.Euclidean.Completeness.IteratedSobolevBanach
import DifferentialGeometry.Analysis.Sobolev.Euclidean.IteratedSobolevSpace.IteratedSobolevQuant

/-!
# A separated Euclidean Sobolev Banach carrier

The existing Euclidean theory proves sequence-level completeness for
`MemWkp`, but the local heat parametrix needs an actual Banach carrier on
which continuous linear maps can be formed.  This file supplies the minimal
carrier: Sobolev functions on one fixed open set, modulo a.e. equality there.

All algebraic, normed, and complete structures are ordinary theorem values.
No global or scoped instance is registered.  A finite-chart consumer installs
them only inside its own `letI` scope.
-/

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option linter.style.setOption false

open MeasureTheory Set Filter Topology
open scoped ENNReal NNReal

namespace DifferentialGeometry
namespace Analysis
namespace Sobolev
namespace Euclidean

variable {d : ℕ}

/-- The linear subspace of functions belonging to `W^{k,p}(Ω)`. -/
def euclidWkpSubmodule
    (k : ℕ) (p : ℝ≥0∞) (hp : 1 ≤ p)
    (Ω : Set (EuclideanSpace ℝ (Fin d))) (hΩ : IsOpen Ω) :
    Submodule ℝ (EuclideanSpace ℝ (Fin d) → ℝ) where
  carrier := {u | MemWkp (d := d) k p u Ω}
  zero_mem' := MemWkp_zero_fun (d := d) hp hΩ
  add_mem' := fun hu hv => MemWkp.add (d := d) hp hΩ hu hv
  smul_mem' := fun c u hu => by
    change MemWkp (d := d) k p (fun x => c * u x) Ω
    exact MemWkp.const_smul (d := d) hp hΩ hu c

/-- The unseparated Euclidean Sobolev carrier.  It is reducible to the
submodule subtype, so its algebra comes only from Mathlib's generic subtype
instances. -/
abbrev EuclidWkp
    (k : ℕ) (p : ℝ≥0∞) (hp : 1 ≤ p)
    (Ω : Set (EuclideanSpace ℝ (Fin d))) [hΩ : Fact (IsOpen Ω)] : Type _ :=
  ↑(euclidWkpSubmodule (d := d) k p hp Ω hΩ.out)

/-- A.e. equality on the fixed Sobolev domain. -/
def EuclidAEEq
    {k : ℕ} {p : ℝ≥0∞} {hp : 1 ≤ p}
    {Ω : Set (EuclideanSpace ℝ (Fin d))} [Fact (IsOpen Ω)]
    (u v : EuclidWkp (d := d) k p hp Ω) : Prop :=
  u.1 =ᵐ[volume.restrict Ω] v.1

theorem EuclidAEEq.rfl
    {k : ℕ} {p : ℝ≥0∞} {hp : 1 ≤ p}
    {Ω : Set (EuclideanSpace ℝ (Fin d))} [Fact (IsOpen Ω)]
    (u : EuclidWkp (d := d) k p hp Ω) : EuclidAEEq u u :=
  Filter.EventuallyEq.rfl

theorem EuclidAEEq.symm
    {k : ℕ} {p : ℝ≥0∞} {hp : 1 ≤ p}
    {Ω : Set (EuclideanSpace ℝ (Fin d))} [Fact (IsOpen Ω)]
    {u v : EuclidWkp (d := d) k p hp Ω}
    (h : EuclidAEEq u v) : EuclidAEEq v u := h.symm

theorem EuclidAEEq.trans
    {k : ℕ} {p : ℝ≥0∞} {hp : 1 ≤ p}
    {Ω : Set (EuclideanSpace ℝ (Fin d))} [Fact (IsOpen Ω)]
    {u v w : EuclidWkp (d := d) k p hp Ω}
    (huv : EuclidAEEq u v) (hvw : EuclidAEEq v w) : EuclidAEEq u w :=
  huv.trans hvw

private theorem eadd_rel
    {k : ℕ} {p : ℝ≥0∞} {hp : 1 ≤ p}
    {Ω : Set (EuclideanSpace ℝ (Fin d))} [Fact (IsOpen Ω)]
    {u₁ u₂ v₁ v₂ : EuclidWkp (d := d) k p hp Ω}
    (hu : EuclidAEEq u₁ u₂) (hv : EuclidAEEq v₁ v₂) :
    EuclidAEEq (u₁ + v₁) (u₂ + v₂) := by
  filter_upwards [hu, hv] with x hux hvx
  simp only [Pi.add_apply, hux, hvx]

private theorem eneg_rel
    {k : ℕ} {p : ℝ≥0∞} {hp : 1 ≤ p}
    {Ω : Set (EuclideanSpace ℝ (Fin d))} [Fact (IsOpen Ω)]
    {u v : EuclidWkp (d := d) k p hp Ω}
    (h : EuclidAEEq u v) : EuclidAEEq (-u) (-v) := by
  filter_upwards [h] with x hx
  simp only [Pi.neg_apply, hx]

private theorem esmul_rel
    {k : ℕ} {p : ℝ≥0∞} {hp : 1 ≤ p}
    {Ω : Set (EuclideanSpace ℝ (Fin d))} [Fact (IsOpen Ω)]
    (c : ℝ) {u v : EuclidWkp (d := d) k p hp Ω}
    (h : EuclidAEEq u v) : EuclidAEEq (c • u) (c • v) := by
  filter_upwards [h] with x hx
  simp only [Pi.smul_apply, smul_eq_mul, hx]

/-- The a.e.-equality setoid on the Euclidean Sobolev carrier. -/
def euclidWkpSetoid
    (k : ℕ) (p : ℝ≥0∞) (hp : 1 ≤ p)
    (Ω : Set (EuclideanSpace ℝ (Fin d))) [Fact (IsOpen Ω)] :
    Setoid (EuclidWkp (d := d) k p hp Ω) where
  r := EuclidAEEq
  iseqv := {
    refl := EuclidAEEq.rfl
    symm := EuclidAEEq.symm
    trans := EuclidAEEq.trans }

/-- The separated Euclidean `W^{k,p}(Ω)` carrier. -/
def EuclidWkpQ
    (k : ℕ) (p : ℝ≥0∞) (hp : 1 ≤ p)
    (Ω : Set (EuclideanSpace ℝ (Fin d))) [Fact (IsOpen Ω)] : Type _ :=
  Quotient (euclidWkpSetoid (d := d) k p hp Ω)

/-! ## Explicit quotient algebra -/

def ezero
    (k : ℕ) (p : ℝ≥0∞) (hp : 1 ≤ p)
    (Ω : Set (EuclideanSpace ℝ (Fin d))) [Fact (IsOpen Ω)] :
    EuclidWkpQ (d := d) k p hp Ω :=
  Quotient.mk (euclidWkpSetoid (d := d) k p hp Ω)
    (0 : EuclidWkp (d := d) k p hp Ω)

def eadd
    (k : ℕ) (p : ℝ≥0∞) (hp : 1 ≤ p)
    (Ω : Set (EuclideanSpace ℝ (Fin d))) [Fact (IsOpen Ω)] :
    EuclidWkpQ (d := d) k p hp Ω →
      EuclidWkpQ (d := d) k p hp Ω →
        EuclidWkpQ (d := d) k p hp Ω :=
  Quotient.map₂ (fun u v => u + v) (by
    intro u₁ u₂ hu v₁ v₂ hv
    exact eadd_rel hu hv)

def eneg
    (k : ℕ) (p : ℝ≥0∞) (hp : 1 ≤ p)
    (Ω : Set (EuclideanSpace ℝ (Fin d))) [Fact (IsOpen Ω)] :
    EuclidWkpQ (d := d) k p hp Ω → EuclidWkpQ (d := d) k p hp Ω :=
  Quotient.map (fun u => -u) (fun _ _ h => eneg_rel h)

def esmul
    (k : ℕ) (p : ℝ≥0∞) (hp : 1 ≤ p)
    (Ω : Set (EuclideanSpace ℝ (Fin d))) [Fact (IsOpen Ω)]
    (c : ℝ) :
    EuclidWkpQ (d := d) k p hp Ω → EuclidWkpQ (d := d) k p hp Ω :=
  Quotient.map (fun u => c • u) (fun _ _ h => esmul_rel c h)

def esub
    (k : ℕ) (p : ℝ≥0∞) (hp : 1 ≤ p)
    (Ω : Set (EuclideanSpace ℝ (Fin d))) [Fact (IsOpen Ω)] :
    EuclidWkpQ (d := d) k p hp Ω →
      EuclidWkpQ (d := d) k p hp Ω →
        EuclidWkpQ (d := d) k p hp Ω :=
  Quotient.map₂ (fun u v => u - v) (by
    intro u₁ u₂ hu v₁ v₂ hv
    change EuclidAEEq (u₁ + -v₁) (u₂ + -v₂)
    exact eadd_rel hu (eneg_rel hv))

noncomputable def erep
    (k : ℕ) (p : ℝ≥0∞) (hp : 1 ≤ p)
    (Ω : Set (EuclideanSpace ℝ (Fin d))) [Fact (IsOpen Ω)]
    (a : EuclidWkpQ (d := d) k p hp Ω) :
    EuclidWkp (d := d) k p hp Ω :=
  Quotient.out a

theorem emk_erep
    (k : ℕ) (p : ℝ≥0∞) (hp : 1 ≤ p)
    (Ω : Set (EuclideanSpace ℝ (Fin d))) [Fact (IsOpen Ω)]
    (a : EuclidWkpQ (d := d) k p hp Ω) :
    Quotient.mk (euclidWkpSetoid (d := d) k p hp Ω)
        (erep (d := d) k p hp Ω a) = a :=
  Quotient.out_eq a

private theorem eadd_zero
    (k : ℕ) {p : ℝ≥0∞} (hp : 1 ≤ p)
    {Ω : Set (EuclideanSpace ℝ (Fin d))} [Fact (IsOpen Ω)]
    (a : EuclidWkpQ (d := d) k p hp Ω) :
    eadd k p hp Ω a (ezero k p hp Ω) = a := by
  refine Quotient.inductionOn a ?_
  intro u
  change Quotient.mk (euclidWkpSetoid (d := d) k p hp Ω) (u + 0) =
    Quotient.mk (euclidWkpSetoid (d := d) k p hp Ω) u
  rw [add_zero]

private theorem ezero_add
    (k : ℕ) {p : ℝ≥0∞} (hp : 1 ≤ p)
    {Ω : Set (EuclideanSpace ℝ (Fin d))} [Fact (IsOpen Ω)]
    (a : EuclidWkpQ (d := d) k p hp Ω) :
    eadd k p hp Ω (ezero k p hp Ω) a = a := by
  refine Quotient.inductionOn a ?_
  intro u
  change Quotient.mk (euclidWkpSetoid (d := d) k p hp Ω) (0 + u) =
    Quotient.mk (euclidWkpSetoid (d := d) k p hp Ω) u
  rw [zero_add]

private theorem eadd_assoc
    (k : ℕ) {p : ℝ≥0∞} (hp : 1 ≤ p)
    {Ω : Set (EuclideanSpace ℝ (Fin d))} [Fact (IsOpen Ω)]
    (a b c : EuclidWkpQ (d := d) k p hp Ω) :
    eadd k p hp Ω (eadd k p hp Ω a b) c =
      eadd k p hp Ω a (eadd k p hp Ω b c) := by
  refine Quotient.inductionOn₃ a b c ?_
  intro u v w
  change Quotient.mk (euclidWkpSetoid (d := d) k p hp Ω) ((u + v) + w) =
    Quotient.mk (euclidWkpSetoid (d := d) k p hp Ω) (u + (v + w))
  rw [add_assoc]

private theorem eadd_comm
    (k : ℕ) {p : ℝ≥0∞} (hp : 1 ≤ p)
    {Ω : Set (EuclideanSpace ℝ (Fin d))} [Fact (IsOpen Ω)]
    (a b : EuclidWkpQ (d := d) k p hp Ω) :
    eadd k p hp Ω a b = eadd k p hp Ω b a := by
  refine Quotient.inductionOn₂ a b ?_
  intro u v
  change Quotient.mk (euclidWkpSetoid (d := d) k p hp Ω) (u + v) =
    Quotient.mk (euclidWkpSetoid (d := d) k p hp Ω) (v + u)
  rw [add_comm]

private theorem eneg_add_self
    (k : ℕ) {p : ℝ≥0∞} (hp : 1 ≤ p)
    {Ω : Set (EuclideanSpace ℝ (Fin d))} [Fact (IsOpen Ω)]
    (a : EuclidWkpQ (d := d) k p hp Ω) :
    eadd k p hp Ω (eneg k p hp Ω a) a = ezero k p hp Ω := by
  refine Quotient.inductionOn a ?_
  intro u
  change Quotient.mk (euclidWkpSetoid (d := d) k p hp Ω) (-u + u) =
    Quotient.mk (euclidWkpSetoid (d := d) k p hp Ω) 0
  rw [neg_add_cancel]

private theorem esub_add_neg
    (k : ℕ) {p : ℝ≥0∞} (hp : 1 ≤ p)
    {Ω : Set (EuclideanSpace ℝ (Fin d))} [Fact (IsOpen Ω)]
    (a b : EuclidWkpQ (d := d) k p hp Ω) :
    esub k p hp Ω a b = eadd k p hp Ω a (eneg k p hp Ω b) := by
  refine Quotient.inductionOn₂ a b ?_
  intro u v
  change Quotient.mk (euclidWkpSetoid (d := d) k p hp Ω) (u - v) =
    Quotient.mk (euclidWkpSetoid (d := d) k p hp Ω) (u + -v)
  rw [sub_eq_add_neg]

private theorem eone_smul
    (k : ℕ) {p : ℝ≥0∞} (hp : 1 ≤ p)
    {Ω : Set (EuclideanSpace ℝ (Fin d))} [Fact (IsOpen Ω)]
    (u : EuclidWkpQ (d := d) k p hp Ω) : esmul k p hp Ω 1 u = u := by
  refine Quotient.inductionOn u ?_
  intro v
  change Quotient.mk (euclidWkpSetoid (d := d) k p hp Ω) (1 • v) =
    Quotient.mk (euclidWkpSetoid (d := d) k p hp Ω) v
  rw [one_smul]

private theorem emul_smul
    (k : ℕ) {p : ℝ≥0∞} (hp : 1 ≤ p)
    {Ω : Set (EuclideanSpace ℝ (Fin d))} [Fact (IsOpen Ω)]
    (a b : ℝ) (u : EuclidWkpQ (d := d) k p hp Ω) :
    esmul k p hp Ω (a * b) u = esmul k p hp Ω a (esmul k p hp Ω b u) := by
  refine Quotient.inductionOn u ?_
  intro v
  change Quotient.mk (euclidWkpSetoid (d := d) k p hp Ω) ((a * b) • v) =
    Quotient.mk (euclidWkpSetoid (d := d) k p hp Ω) (a • b • v)
  rw [mul_smul]

private theorem esmul_zero
    (k : ℕ) {p : ℝ≥0∞} (hp : 1 ≤ p)
    {Ω : Set (EuclideanSpace ℝ (Fin d))} [Fact (IsOpen Ω)] (c : ℝ) :
    esmul k p hp Ω c (ezero k p hp Ω) = ezero k p hp Ω := by
  change Quotient.mk (euclidWkpSetoid (d := d) k p hp Ω)
      (c • (0 : EuclidWkp (d := d) k p hp Ω)) =
    Quotient.mk (euclidWkpSetoid (d := d) k p hp Ω) 0
  rw [smul_zero]

private theorem esmul_add
    (k : ℕ) {p : ℝ≥0∞} (hp : 1 ≤ p)
    {Ω : Set (EuclideanSpace ℝ (Fin d))} [Fact (IsOpen Ω)] (c : ℝ)
    (u v : EuclidWkpQ (d := d) k p hp Ω) :
    esmul k p hp Ω c (eadd k p hp Ω u v) =
      eadd k p hp Ω (esmul k p hp Ω c u) (esmul k p hp Ω c v) := by
  refine Quotient.inductionOn₂ u v ?_
  intro f h
  change Quotient.mk (euclidWkpSetoid (d := d) k p hp Ω) (c • (f + h)) =
    Quotient.mk (euclidWkpSetoid (d := d) k p hp Ω) (c • f + c • h)
  rw [smul_add]

private theorem eadd_smul
    (k : ℕ) {p : ℝ≥0∞} (hp : 1 ≤ p)
    {Ω : Set (EuclideanSpace ℝ (Fin d))} [Fact (IsOpen Ω)] (a b : ℝ)
    (u : EuclidWkpQ (d := d) k p hp Ω) :
    esmul k p hp Ω (a + b) u =
      eadd k p hp Ω (esmul k p hp Ω a u) (esmul k p hp Ω b u) := by
  refine Quotient.inductionOn u ?_
  intro f
  change Quotient.mk (euclidWkpSetoid (d := d) k p hp Ω) ((a + b) • f) =
    Quotient.mk (euclidWkpSetoid (d := d) k p hp Ω) (a • f + b • f)
  rw [add_smul]

private theorem ezero_smul
    (k : ℕ) {p : ℝ≥0∞} (hp : 1 ≤ p)
    {Ω : Set (EuclideanSpace ℝ (Fin d))} [Fact (IsOpen Ω)]
    (u : EuclidWkpQ (d := d) k p hp Ω) :
    esmul k p hp Ω 0 u = ezero k p hp Ω := by
  refine Quotient.inductionOn u ?_
  intro f
  change Quotient.mk (euclidWkpSetoid (d := d) k p hp Ω) (0 • f) =
    Quotient.mk (euclidWkpSetoid (d := d) k p hp Ω) 0
  rw [zero_smul]

/-- The explicit quotient operations form an additive commutative group. -/
noncomputable def ewkpAddGroup
    (k : ℕ) (p : ℝ≥0∞) (hp : 1 ≤ p)
    (Ω : Set (EuclideanSpace ℝ (Fin d))) [Fact (IsOpen Ω)] :
    AddCommGroup (EuclidWkpQ (d := d) k p hp Ω) where
  zero := ezero k p hp Ω
  add := eadd k p hp Ω
  neg := eneg k p hp Ω
  sub := esub k p hp Ω
  add_assoc := eadd_assoc k hp
  zero_add := ezero_add k hp
  add_zero := eadd_zero k hp
  add_comm := eadd_comm k hp
  neg_add_cancel := eneg_add_self k hp
  sub_eq_add_neg := esub_add_neg k hp
  nsmul := nsmulRec
  zsmul := zsmulRec

private noncomputable def ewkpModule
    (k : ℕ) (p : ℝ≥0∞) (hp : 1 ≤ p)
    (Ω : Set (EuclideanSpace ℝ (Fin d))) [Fact (IsOpen Ω)] :
    @Module ℝ (EuclidWkpQ (d := d) k p hp Ω)
      _ (ewkpAddGroup (d := d) k p hp Ω).toAddCommMonoid where
  smul := fun c => esmul k p hp Ω c
  one_smul := eone_smul k hp
  mul_smul := emul_smul k hp
  smul_zero := esmul_zero k hp
  smul_add := esmul_add k hp
  add_smul := eadd_smul k hp
  zero_smul := ezero_smul k hp

/-! ## Quotient norm and theorem-valued Banach structures -/

noncomputable def ewkpNorm
    (k : ℕ) (p : ℝ≥0∞) (hp : 1 ≤ p)
    (Ω : Set (EuclideanSpace ℝ (Fin d))) [Fact (IsOpen Ω)] :
    EuclidWkpQ (d := d) k p hp Ω → ℝ≥0∞ :=
  Quotient.lift (fun u => wkpNorm (d := d) k p u.1 Ω) (by
    intro u v huv
    exact wkpNorm_congr_ae (d := d) hp (by exact Fact.out) huv)

private theorem enorm_zero
    (k : ℕ) {p : ℝ≥0∞} (hp : 1 ≤ p)
    {Ω : Set (EuclideanSpace ℝ (Fin d))} [Fact (IsOpen Ω)] :
    ewkpNorm (d := d) k p hp Ω (ezero k p hp Ω) = 0 :=
  wkpNorm_zero_fun_zero (d := d) hp Fact.out

private theorem enorm_add_le
    (k : ℕ) {p : ℝ≥0∞} (hp : 1 ≤ p)
    {Ω : Set (EuclideanSpace ℝ (Fin d))} [Fact (IsOpen Ω)]
    (a b : EuclidWkpQ (d := d) k p hp Ω) :
    ewkpNorm (d := d) k p hp Ω (eadd k p hp Ω a b) ≤
      ewkpNorm (d := d) k p hp Ω a + ewkpNorm (d := d) k p hp Ω b := by
  refine Quotient.inductionOn₂ a b ?_
  intro u v
  exact wkpNorm_add_le (d := d) hp Fact.out u.2 v.2

private theorem enorm_smul
    (k : ℕ) {p : ℝ≥0∞} (hp : 1 ≤ p)
    {Ω : Set (EuclideanSpace ℝ (Fin d))} [Fact (IsOpen Ω)] (c : ℝ)
    (a : EuclidWkpQ (d := d) k p hp Ω) :
    ewkpNorm (d := d) k p hp Ω (esmul k p hp Ω c a) =
      ‖c‖ₙ * ewkpNorm (d := d) k p hp Ω a := by
  refine Quotient.inductionOn a ?_
  intro u
  exact wkpNorm_const_smul (d := d) hp Fact.out u.2 c

private theorem enorm_lt_top
    (k : ℕ) {p : ℝ≥0∞} (hp : 1 ≤ p)
    {Ω : Set (EuclideanSpace ℝ (Fin d))} [Fact (IsOpen Ω)]
    (a : EuclidWkpQ (d := d) k p hp Ω) :
    ewkpNorm (d := d) k p hp Ω a < ∞ := by
  refine Quotient.inductionOn a ?_
  exact fun u => wkpNorm_lt_top_of_memWkp (d := d) u.2

private theorem enorm_eq_zero
    (k : ℕ) {p : ℝ≥0∞} (hp : 1 ≤ p)
    {Ω : Set (EuclideanSpace ℝ (Fin d))} [Fact (IsOpen Ω)]
    (a : EuclidWkpQ (d := d) k p hp Ω) :
    ewkpNorm (d := d) k p hp Ω a = 0 ↔ a = ezero k p hp Ω := by
  refine Quotient.inductionOn a ?_
  intro u
  constructor
  · intro hzero
    have heLp_le := eLpNorm_le_wkpNorm (d := d) k p Ω u.1
    rw [hzero] at heLp_le
    have heLp : eLpNorm u.1 p (volume.restrict Ω) = 0 :=
      le_antisymm heLp_le (zero_le _)
    have hp_zero : p ≠ 0 := ne_of_gt (lt_of_lt_of_le (by norm_num) hp)
    have hae : u.1 =ᵐ[volume.restrict Ω] 0 :=
      (eLpNorm_eq_zero_iff u.2.memLp.aestronglyMeasurable hp_zero).mp heLp
    exact Quotient.sound hae
  · intro h
    change Quotient.mk (euclidWkpSetoid (d := d) k p hp Ω) u =
        Quotient.mk (euclidWkpSetoid (d := d) k p hp Ω) 0 at h
    have hae : EuclidAEEq u 0 := Quotient.exact h
    exact (wkpNorm_congr_ae (d := d) hp Fact.out hae).trans
      (wkpNorm_zero_fun_zero (d := d) hp Fact.out)

private noncomputable def ewkpNormInst
    (k : ℕ) (p : ℝ≥0∞) (hp : 1 ≤ p)
    (Ω : Set (EuclideanSpace ℝ (Fin d))) [Fact (IsOpen Ω)] :
    Norm (EuclidWkpQ (d := d) k p hp Ω) where
  norm a := (ewkpNorm (d := d) k p hp Ω a).toReal

private noncomputable def ewkpCore
    (k : ℕ) (p : ℝ≥0∞) (hp : 1 ≤ p)
    (Ω : Set (EuclideanSpace ℝ (Fin d))) [Fact (IsOpen Ω)] :
    @NormedSpace.Core ℝ (EuclidWkpQ (d := d) k p hp Ω)
      _ (ewkpAddGroup (d := d) k p hp Ω)
      (ewkpModule (d := d) k p hp Ω)
      (ewkpNormInst (d := d) k p hp Ω) where
  norm_nonneg _ := ENNReal.toReal_nonneg
  norm_smul c a := by
    change (ewkpNorm (d := d) k p hp Ω (esmul k p hp Ω c a)).toReal =
      ‖c‖ * (ewkpNorm (d := d) k p hp Ω a).toReal
    rw [enorm_smul (d := d) k hp, ENNReal.toReal_mul, toReal_enorm]
  norm_triangle a b := by
    change (ewkpNorm (d := d) k p hp Ω (eadd k p hp Ω a b)).toReal ≤
      (ewkpNorm (d := d) k p hp Ω a).toReal +
        (ewkpNorm (d := d) k p hp Ω b).toReal
    have ha : ewkpNorm (d := d) k p hp Ω a ≠ ∞ :=
      (enorm_lt_top (d := d) k hp a).ne
    have hb : ewkpNorm (d := d) k p hp Ω b ≠ ∞ :=
      (enorm_lt_top (d := d) k hp b).ne
    have hreal := ENNReal.toReal_mono (ENNReal.add_ne_top.mpr ⟨ha, hb⟩)
      (enorm_add_le (d := d) k hp a b)
    rwa [ENNReal.toReal_add ha hb] at hreal
  norm_eq_zero_iff a := by
    change (ewkpNorm (d := d) k p hp Ω a).toReal = 0 ↔ a = ezero k p hp Ω
    constructor
    · intro h
      rcases (ENNReal.toReal_eq_zero_iff _).mp h with hzero | htop
      · exact (enorm_eq_zero (d := d) k hp a).mp hzero
      · exact ((enorm_lt_top (d := d) k hp a).ne htop).elim
    · intro h
      rw [h, enorm_zero (d := d) k hp]
      exact ENNReal.toReal_zero

/-- The theorem-valued normed additive group on Euclidean Sobolev classes. -/
noncomputable def ewkpNormedGroup
    (k : ℕ) (p : ℝ≥0∞) (hp : 1 ≤ p)
    (Ω : Set (EuclideanSpace ℝ (Fin d))) [Fact (IsOpen Ω)] :
    NormedAddCommGroup (EuclidWkpQ (d := d) k p hp Ω) :=
  @NormedAddCommGroup.ofCore ℝ (EuclidWkpQ (d := d) k p hp Ω)
    _ (ewkpAddGroup (d := d) k p hp Ω)
    (ewkpModule (d := d) k p hp Ω)
    (ewkpNormInst (d := d) k p hp Ω)
    (ewkpCore (d := d) k p hp Ω)

/-- The theorem-valued normed real vector space on Euclidean Sobolev
classes. -/
noncomputable def ewkpNormedSpace
    (k : ℕ) (p : ℝ≥0∞) (hp : 1 ≤ p)
    (Ω : Set (EuclideanSpace ℝ (Fin d))) [Fact (IsOpen Ω)] :
    @NormedSpace ℝ (EuclidWkpQ (d := d) k p hp Ω) _
      (@NormedAddCommGroup.toSeminormedAddCommGroup
        (EuclidWkpQ (d := d) k p hp Ω)
        (ewkpNormedGroup (d := d) k p hp Ω)) :=
  @NormedSpace.ofCore ℝ (EuclidWkpQ (d := d) k p hp Ω) _
    (@NormedAddCommGroup.toSeminormedAddCommGroup
      (EuclidWkpQ (d := d) k p hp Ω)
      (ewkpNormedGroup (d := d) k p hp Ω))
    (ewkpModule (d := d) k p hp Ω)
    (ewkpCore (d := d) k p hp Ω)

/-- The norm distance written without installing the theorem-valued
structures. -/
def ewkpDist
    (k : ℕ) (p : ℝ≥0∞) (hp : 1 ≤ p)
    (Ω : Set (EuclideanSpace ℝ (Fin d))) [Fact (IsOpen Ω)]
    (a b : EuclidWkpQ (d := d) k p hp Ω) : ℝ :=
  (ewkpNorm (d := d) k p hp Ω (esub k p hp Ω a b)).toReal

/-- Completeness of the generated normed structure, obtained directly from
`MemWkp.exists_limit_of_wkpNorm_cauchy`. -/
theorem ewkpComplete
    [NeZero d]
    (k : ℕ) {p : ℝ≥0∞} (hp : 1 ≤ p) (hp_top : p ≠ ∞)
    (Ω : Set (EuclideanSpace ℝ (Fin d))) [Fact (IsOpen Ω)] :
    @CompleteSpace (EuclidWkpQ (d := d) k p hp Ω)
      (ewkpNormedGroup (d := d) k p hp Ω).toUniformSpace := by
  letI : NormedAddCommGroup (EuclidWkpQ (d := d) k p hp Ω) :=
    ewkpNormedGroup (d := d) k p hp Ω
  letI : NormedSpace ℝ (EuclidWkpQ (d := d) k p hp Ω) :=
    ewkpNormedSpace (d := d) k p hp Ω
  let rep : ℕ → EuclidWkpQ (d := d) k p hp Ω →
      EuclidWkp (d := d) k p hp Ω := fun _ => erep (d := d) k p hp Ω
  apply Metric.complete_of_cauchySeq_tendsto
  intro u hu
  have hc := (Metric.cauchySeq_iff.mp hu)
  have hrep_cauchy : ∀ ε : ℝ, 0 < ε → ∃ N : ℕ, ∀ m n : ℕ,
      N ≤ m → N ≤ n →
      wkpNorm (d := d) k p
          (fun x => (rep m (u m)).1 x - (rep n (u n)).1 x) Ω ≤
        ENNReal.ofReal ε := by
    intro ε hε
    obtain ⟨N, hN⟩ := hc ε hε
    refine ⟨N, ?_⟩
    intro m n hm hn
    have hdist := hN m hm n hn
    rw [← emk_erep (d := d) k p hp Ω (u m),
      ← emk_erep (d := d) k p hp Ω (u n), dist_eq_norm] at hdist
    have hreal :
        (wkpNorm (d := d) k p
          (fun x => (rep m (u m)).1 x - (rep n (u n)).1 x) Ω).toReal < ε := by
      exact hdist
    have hfinite : wkpNorm (d := d) k p
        (fun x => (rep m (u m)).1 x - (rep n (u n)).1 x) Ω ≠ ∞ := by
      apply (wkpNorm_lt_top_of_memWkp (d := d) ?_).ne
      exact MemWkp.sub (d := d) hp Fact.out (rep m (u m)).2 (rep n (u n)).2
    exact (ENNReal.le_ofReal_iff_toReal_le hfinite hε.le).2 hreal.le
  obtain ⟨v, hv_mem, hv⟩ := MemWkp.exists_limit_of_wkpNorm_cauchy
    (d := d) Fact.out k p hp hp_top
    (u := fun n => (rep n (u n)).1)
    (fun n => (rep n (u n)).2) hrep_cauchy
  let vq : EuclidWkpQ (d := d) k p hp Ω :=
    Quotient.mk (euclidWkpSetoid (d := d) k p hp Ω) ⟨v, hv_mem⟩
  refine ⟨vq, ?_⟩
  apply tendsto_iff_dist_tendsto_zero.mpr
  have hreal := (ENNReal.tendsto_toReal ENNReal.zero_ne_top).comp hv
  have hdist_eq : (fun n => dist (u n) vq) =
      (fun n => (wkpNorm (d := d) k p
        (fun x => (rep n (u n)).1 x - v x) Ω).toReal) := by
    funext n
    rw [← emk_erep (d := d) k p hp Ω (u n), dist_eq_norm]
    rfl
  rw [hdist_eq]
  exact hreal

end Euclidean
end Sobolev
end Analysis
end DifferentialGeometry
