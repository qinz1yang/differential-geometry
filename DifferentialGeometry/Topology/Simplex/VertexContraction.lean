import DifferentialGeometry.Topology.Simplex.Face
import Mathlib.Topology.Homotopy.Basic

noncomputable section

namespace DifferentialGeometry.Simplex

variable {I J : Type*} [Fintype I] [Fintype J]

def vertexContraction [DecidableEq I] (i : I) :
    C(unitInterval × stdSimplex ℝ I, stdSimplex ℝ I) := by
  exact ⟨fun z => ⟨(1 - (z.1 : ℝ)) • z.2.val + (z.1 : ℝ) • (stdSimplex.vertex (S := ℝ) i).val,
    convex_stdSimplex ℝ I z.2.property (stdSimplex.vertex (S := ℝ) i).property
      (sub_nonneg.mpr z.1.property.2) z.1.property.1 (sub_add_cancel _ _)⟩, by
    apply Continuous.subtype_mk
    exact ((continuous_const.sub (continuous_subtype_val.comp continuous_fst)).smul
      (continuous_subtype_val.comp continuous_snd)).add
      ((continuous_subtype_val.comp continuous_fst).smul continuous_const)⟩

theorem vertexContraction_apply [DecidableEq I] (i : I) (t : unitInterval) (q : stdSimplex ℝ I) (j : I) :
    (vertexContraction i (t, q)).val j =
      (1 - (t : ℝ)) * q.val j + (t : ℝ) * if i = j then 1 else 0 := by
  simp [vertexContraction, Pi.single_apply, eq_comm]

@[simp] theorem vertexContraction_zero [DecidableEq I] (i : I) (q : stdSimplex ℝ I) :
    vertexContraction i (0, q) = q := by
  apply Subtype.ext
  simp [vertexContraction]

@[simp] theorem vertexContraction_one [DecidableEq I] (i : I) (q : stdSimplex ℝ I) :
    vertexContraction i (1, q) = stdSimplex.vertex (S := ℝ) i := by
  apply Subtype.ext
  simp [vertexContraction]

@[simp] theorem vertexContraction_vertex [DecidableEq I] (i : I) (t : unitInterval) :
    vertexContraction i (t, stdSimplex.vertex (S := ℝ) i) = stdSimplex.vertex (S := ℝ) i := by
  apply Subtype.ext
  funext j
  by_cases h : i = j <;> simp [vertexContraction, h]

theorem vertexContraction_map [DecidableEq I] [DecidableEq J] (f : I → J) (i : I) (t : unitInterval)
    (q : stdSimplex ℝ I) :
    vertexContraction (f i) (t, stdSimplex.map f q) =
      stdSimplex.map f (vertexContraction i (t, q)) := by
  apply Subtype.ext
  change (1 - (t : ℝ)) • FunOnFinite.linearMap ℝ ℝ f q.val +
      (t : ℝ) • (stdSimplex.vertex (S := ℝ) (f i)).val =
      FunOnFinite.linearMap ℝ ℝ f
        ((1 - (t : ℝ)) • q.val + (t : ℝ) • (stdSimplex.vertex (S := ℝ) i).val)
  rw [map_add, map_smul, map_smul]
  have h := congrArg Subtype.val (stdSimplex.map_vertex (S := ℝ) f i)
  exact congrArg (fun v => (1 - (t : ℝ)) • FunOnFinite.linearMap ℝ ℝ f q.val +
    (t : ℝ) • v) h.symm

end DifferentialGeometry.Simplex
