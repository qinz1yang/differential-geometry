import DifferentialGeometry.Topology.FundamentalGroup.MarkedFundamentalGroup
import DifferentialGeometry.Topology.FundamentalGroup.Circle
import Mathlib.Tactic.Continuity
namespace GC.Topology
open DifferentialGeometry.Topology
open scoped ContinuousMap
noncomputable section

abbrev Torus := Circle × Circle
abbrev TorusCylinder := Torus × ℝ

def torusAt (r : ℝ) : C(Torus, TorusCylinder) :=
  ⟨fun x => (x, r), continuous_id.prodMk continuous_const⟩

theorem torusAt_piOne_injective (r : ℝ) (p : Torus) :
    Function.Injective (FundamentalGroup.map (torusAt r) p) :=
  injective_fundamentalGroup_map_of_leftInverse (torusAt r) ContinuousMap.fst
    (fun _ => rfl) p

def torusSlide (r s : ℝ) : (torusAt r).Homotopy (torusAt s) where
  toFun tx := (tx.2, (1 - (tx.1 : ℝ)) * r + (tx.1 : ℝ) * s)
  continuous_toFun := by fun_prop
  map_zero_left x := by simp [torusAt]
  map_one_left x := by simp [torusAt]

theorem torusSlide_tracks (r s : ℝ) (p : Torus) :
    markedMap (torusAt s) p ((torusSlide r s).evalAt p) =
      FundamentalGroup.map (torusAt r) p :=
  homotopy_track _ _ (torusSlide r s) p

theorem torus_two_sides_disjoint (r s : ℝ) (h : r ≠ s) :
    Disjoint (Set.range (torusAt r)) (Set.range (torusAt s)) := by
  rw [Set.disjoint_left]
  rintro _ ⟨a, rfl⟩ ⟨b, hab⟩
  exact h (congrArg Prod.snd hab).symm

theorem torus_common_core_kernel (r s : ℝ) (p : Torus) :
    (FundamentalGroup.map ((torusAt r).comp (ContinuousMap.id Torus)) p).ker =
      (FundamentalGroup.map ((torusAt s).comp (ContinuousMap.id Torus)) p).ker :=
  common_core_kernel _ _ _ p (torusAt_piOne_injective r p) (torusAt_piOne_injective s p)

def torusFundamentalGroup : FundamentalGroup Torus (1, 1) ≃* Multiplicative ℤ × Multiplicative ℤ :=
  (fundamentalGroupProdEquiv (1 : Circle) (1 : Circle)).trans
    (fundamentalGroupCircleEquivInt.prodCongr fundamentalGroupCircleEquivInt)

theorem torus_has_nontrivial_loop : ∃ p : FundamentalGroup Torus (1, 1), p ≠ 1 := by
  refine ⟨torusFundamentalGroup.symm (Multiplicative.ofAdd (1 : ℤ), 1), ?_⟩
  intro h
  have he := congrArg torusFundamentalGroup h
  rw [MulEquiv.apply_symm_apply, map_one torusFundamentalGroup] at he
  have hc : (1 : ℤ) = 0 := congrArg (fun q => Multiplicative.toAdd q.1) he
  exact one_ne_zero hc

end
end GC.Topology
