import Mathlib.Algebra.AddConstMap.Basic
import Mathlib.Topology.Instances.AddCircle.Real

noncomputable section

open Set

namespace AddConstMap

theorem exists_continuous_extension_Icc {f : ℝ → ℝ} (a : ℝ)
    (hf : ContinuousOn f (Icc a (a + 1))) (hp : f (a + 1) = f a + 1) :
    ∃ g : AddConstMap ℝ ℝ 1 1, Continuous g ∧ EqOn g f (Icc a (a + 1)) := by
  let D := AddCircle.liftIco (1 : ℝ) a (fun x => f x - x)
  have hD : Continuous D := AddCircle.liftIco_continuous
    (by rw [hp]; ring) (hf.sub continuousOn_id)
  let g : AddConstMap ℝ ℝ 1 1 :=
    ⟨fun x => x + D (x : AddCircle (1 : ℝ)), fun x => by
      rw [AddCircle.coe_add_period]
      ring⟩
  have hgc : Continuous g := continuous_id.add (hD.comp (AddCircle.continuous_mk' (1 : ℝ)))
  have hco : EqOn g f (Ico a (a + 1)) := by
    intro x hx
    change x + AddCircle.liftIco (1 : ℝ) a (fun x => f x - x) (x : AddCircle (1 : ℝ)) = f x
    rw [AddCircle.liftIco_coe_apply hx]
    ring
  refine ⟨g, hgc, ?_⟩
  intro x hx
  rcases lt_or_eq_of_le hx.2 with hxlt | rfl
  · exact hco ⟨hx.1, hxlt⟩
  · have hg : g (a + 1) = g a + 1 := g.map_add_const' a
    rw [hg, hco (show a ∈ Ico a (a + 1) from ⟨le_rfl, by linarith⟩), hp]

end AddConstMap

end
