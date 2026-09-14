import DifferentialGeometry.Topology.GraphBand
import Mathlib.Geometry.Manifold.Algebra.Structures
import Mathlib.Geometry.Manifold.Diffeomorph

noncomputable section

open scoped Manifold ContDiff

namespace DifferentialGeometry.Topology

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {N : Type*} [TopologicalSpace N] [ChartedSpace H N]
variable {n : WithTop ℕ∞}

def graphBandDiffeomorph (a b : N → ℝ)
    (ha : ContMDiff I 𝓘(ℝ) n a) (hb : ContMDiff I 𝓘(ℝ) n b)
    (hab : ∀ p, a p < b p) :
    Diffeomorph (I.prod 𝓘(ℝ)) (I.prod 𝓘(ℝ)) (N × ℝ) (N × ℝ) n where
  toEquiv := (graphBandHomeomorph a b ha.continuous hb.continuous hab).toEquiv
  contMDiff_toFun := contMDiff_fst.prodMk
    ((((hb.sub ha).comp contMDiff_fst).mul contMDiff_snd).add
      (ha.comp contMDiff_fst))
  contMDiff_invFun := contMDiff_fst.prodMk
    ((contMDiff_snd.sub (ha.comp contMDiff_fst)).div₀
      ((hb.sub ha).comp contMDiff_fst)
      (fun p ↦ ne_of_gt (sub_pos.mpr (hab p.1))))

@[simp] theorem graphBandDiffeomorph_apply (a b : N → ℝ)
    (ha : ContMDiff I 𝓘(ℝ) n a) (hb : ContMDiff I 𝓘(ℝ) n b)
    (hab : ∀ p, a p < b p) (p : N × ℝ) :
    graphBandDiffeomorph a b ha hb hab p =
      (p.1, a p.1 + (b p.1 - a p.1) * p.2) :=
  graphBandHomeomorph_apply a b ha.continuous hb.continuous hab p

@[simp] theorem graphBandDiffeomorph_symm_apply (a b : N → ℝ)
    (ha : ContMDiff I 𝓘(ℝ) n a) (hb : ContMDiff I 𝓘(ℝ) n b)
    (hab : ∀ p, a p < b p) (p : N × ℝ) :
    (graphBandDiffeomorph a b ha hb hab).symm p =
      (p.1, (p.2 - a p.1) / (b p.1 - a p.1)) := rfl

end DifferentialGeometry.Topology
