import DifferentialGeometry.Geometry.Metric.Path.Length
import Mathlib.Topology.Homotopy.Path

noncomputable section

open Set
open scoped ENNReal Manifold

namespace Path

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace Real E]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners Real E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
variable [∀ x : M, ENorm (TangentSpace I x)]

structure LengthBoundedHomotopy (L : ENNReal) {x y : M} (p q : Path x y) where
  hom : p.Homotopy q
  isContMDiffWithSittingInstants :
    ∀ t : unitInterval, IsContMDiffWithSittingInstants (I := I) 1 (hom.eval t)
  length_le : ∀ t : unitInterval, riemannianELength (I := I) (hom.eval t) ≤ L

def lengthBoundedHomotopic (L : ENNReal) {x y : M} (p q : Path x y) : Prop :=
  Nonempty (LengthBoundedHomotopy (I := I) L p q)

namespace LengthBoundedHomotopy

variable {L : ENNReal} {x y : M} {p q r : Path x y}

noncomputable def mono {L' : ENNReal}
    (F : LengthBoundedHomotopy (I := I) L p q) (hLL' : L ≤ L') :
    LengthBoundedHomotopy (I := I) L' p q where
  hom := F.hom
  isContMDiffWithSittingInstants := F.isContMDiffWithSittingInstants
  length_le t := (F.length_le t).trans hLL'

noncomputable def refl
    (hpC1 : IsContMDiffWithSittingInstants (I := I) 1 p)
    (hp : riemannianELength (I := I) p ≤ L) :
    LengthBoundedHomotopy (I := I) L p p where
  hom := Path.Homotopy.refl p
  isContMDiffWithSittingInstants t := by
    have hpath : (Path.Homotopy.refl p).eval t = p := by
      ext s
      rfl
    rw [hpath]
    exact hpC1
  length_le t := by
    have hpath : (Path.Homotopy.refl p).eval t = p := by
      ext s
      rfl
    rw [hpath]
    exact hp

noncomputable def symm (F : LengthBoundedHomotopy (I := I) L p q) :
    LengthBoundedHomotopy (I := I) L q p where
  hom := F.hom.symm
  isContMDiffWithSittingInstants t := by
    have hpath : F.hom.symm.eval t = F.hom.eval (unitInterval.symm t) := by
      ext s
      rfl
    rw [hpath]
    exact F.isContMDiffWithSittingInstants (unitInterval.symm t)
  length_le t := by
    have hpath : F.hom.symm.eval t = F.hom.eval (unitInterval.symm t) := by
      ext s
      rfl
    rw [hpath]
    exact F.length_le (unitInterval.symm t)

noncomputable def trans
    (F : LengthBoundedHomotopy (I := I) L p q)
    (G : LengthBoundedHomotopy (I := I) L q r) :
    LengthBoundedHomotopy (I := I) L p r where
  hom := F.hom.trans G.hom
  isContMDiffWithSittingInstants t := by
    by_cases ht : (t : Real) ≤ 1 / 2
    · let t' : unitInterval :=
        ⟨2 * t, (unitInterval.mul_pos_mem_iff zero_lt_two).2 ⟨t.2.1, ht⟩⟩
      have h := F.isContMDiffWithSittingInstants t'
      convert h using 1
      ext s
      change (F.hom.trans G.hom) (t, s) = F.hom (t', s)
      rw [Path.Homotopy.trans_apply]
      simp only [ht, ↓reduceDIte, t']
    · let t' : unitInterval :=
        ⟨2 * t - 1,
          unitInterval.two_mul_sub_one_mem_iff.2
            ⟨(not_le.1 ht).le, t.2.2⟩⟩
      have h := G.isContMDiffWithSittingInstants t'
      convert h using 1
      ext s
      change (F.hom.trans G.hom) (t, s) = G.hom (t', s)
      rw [Path.Homotopy.trans_apply]
      simp only [ht, ↓reduceDIte, t']
  length_le t := by
    by_cases ht : (t : Real) ≤ 1 / 2
    · let t' : unitInterval :=
        ⟨2 * t, (unitInterval.mul_pos_mem_iff zero_lt_two).2 ⟨t.2.1, ht⟩⟩
      have h := F.length_le t'
      convert h using 1
      apply congrArg (riemannianELength (I := I))
      ext s
      change (F.hom.trans G.hom) (t, s) = F.hom (t', s)
      rw [Path.Homotopy.trans_apply]
      simp only [ht, ↓reduceDIte, t']
    · let t' : unitInterval :=
        ⟨2 * t - 1,
          unitInterval.two_mul_sub_one_mem_iff.2
            ⟨(not_le.1 ht).le, t.2.2⟩⟩
      have h := G.length_le t'
      convert h using 1
      apply congrArg (riemannianELength (I := I))
      ext s
      change (F.hom.trans G.hom) (t, s) = G.hom (t', s)
      rw [Path.Homotopy.trans_apply]
      simp only [ht, ↓reduceDIte, t']

private theorem hcomp_refl_eval {z : M} {c : Path y z}
    (F : LengthBoundedHomotopy (I := I) L p q) (t : unitInterval) :
    (F.hom.hcomp (Path.Homotopy.refl c)).eval t =
      (F.hom.eval t).trans c := by
  ext s
  change
    (F.hom.hcomp (Path.Homotopy.refl c)) (t, s) =
      ((F.hom.eval t).trans c) s
  rw [Path.Homotopy.hcomp_apply]
  by_cases hs : (s : Real) ≤ 1 / 2
  · simp only [hs, ↓reduceDIte, Path.trans_apply]
  · simp only [hs, ↓reduceDIte, Path.trans_apply]
    change (Path.Homotopy.refl c) (t, _) = _
    rw [Path.Homotopy.refl_apply]

variable [∀ z : M, ENormSMulClass Real (TangentSpace I z)]

noncomputable def appendRight {z : M} {c : Path y z}
    (F : LengthBoundedHomotopy (I := I) L p q)
    (hc : IsContMDiffWithSittingInstants (I := I) 1 c) :
    LengthBoundedHomotopy (I := I) (L + riemannianELength (I := I) c)
      (p.trans c) (q.trans c) where
  hom := F.hom.hcomp (Path.Homotopy.refl c)
  isContMDiffWithSittingInstants t := by
    rw [hcomp_refl_eval F t]
    exact (F.isContMDiffWithSittingInstants t).trans hc
  length_le t := by
    rw [hcomp_refl_eval F t,
      riemannianELength_trans
        ((F.isContMDiffWithSittingInstants t).contMDiff.contMDiffOn.mdifferentiableOn one_ne_zero)
        (hc.contMDiff.contMDiffOn.mdifferentiableOn one_ne_zero)]
    exact add_le_add (F.length_le t) le_rfl

end LengthBoundedHomotopy

end Path
