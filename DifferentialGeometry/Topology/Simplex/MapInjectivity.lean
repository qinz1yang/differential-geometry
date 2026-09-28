import DifferentialGeometry.Topology.Simplex.Coordinates
import Mathlib.Analysis.Convex.StdSimplex
import Mathlib.Order.WellFounded
open Convexity.StdSimplex

namespace stdSimplex

variable {S : Type*} [Semiring S] [PartialOrder S] [IsOrderedRing S]

lemma map_apply_of_injective {X Y : Type*} [Fintype X] [Fintype Y]
    {f : X → Y} (hf : Function.Injective f)
    (p : coordinateSet S X) (x : X) :
    (coordinateMap f p) (f x) = p x := by
  classical
  change FunOnFinite.linearMap S S f p (f x) = p x
  rw [FunOnFinite.linearMap_apply_apply]
  rw [Finset.sum_eq_single x]
  · intro b hb hbx
    exact (hbx (hf (Finset.mem_filter.mp hb).2)).elim
  · simp

lemma map_apply_eq_zero_of_not_mem_range {X Y : Type*} [Fintype X] [Fintype Y]
    (f : X → Y) (p : coordinateSet S X) {y : Y} (hy : y ∉ Set.range f) :
    (coordinateMap f p) y = 0 := by
  classical
  change FunOnFinite.linearMap S S f p y = 0
  rw [FunOnFinite.linearMap_apply_apply]
  have h : ∀ x, f x ≠ y := fun x hxy => hy ⟨x, hxy⟩
  simp [h]

lemma range_subset_of_map_eq_of_nonzero {X Y : Type*} [Fintype X] [Fintype Y]
    {f g : X → Y} (hf : Function.Injective f)
    {p q : coordinateSet S X} (hp : ∀ x, p x ≠ 0)
    (h : coordinateMap f p = coordinateMap g q) : Set.range f ⊆ Set.range g := by
  rintro y ⟨x, rfl⟩
  by_contra hx
  apply hp x
  rw [← map_apply_of_injective hf p x, h]
  exact map_apply_eq_zero_of_not_mem_range g q hx

lemma map_injective {X Y : Type*} [Fintype X] [Fintype Y]
    {f : X → Y} (hf : Function.Injective f) :
    Function.Injective (coordinateMap (S := S) f) := by
  intro p q h
  ext x
  have hx := DFunLike.congr_fun h (f x)
  exact (map_apply_of_injective hf p x).symm.trans
    (hx.trans (map_apply_of_injective hf q x))

lemma eq_and_eq_of_map_eq_of_strictMono
    {X Y : Type*} [Fintype X] [Fintype Y] [LinearOrder X] [Preorder Y]
    {f g : X → Y}
    (hf : StrictMono f) (hg : StrictMono g)
    {p q : coordinateSet S X} (hp : ∀ x, p x ≠ 0)
    (h : coordinateMap f p = coordinateMap g q) : f = g ∧ p = q := by
  classical
  have hsub := range_subset_of_map_eq_of_nonzero hf.injective hp h
  have hcardf := Fintype.card_congr (Equiv.ofInjective f hf.injective)
  have hcardg := Fintype.card_congr (Equiv.ofInjective g hg.injective)
  have heq : Set.range f = Set.range g :=
    Set.eq_of_subset_of_card_le hsub (by omega)
  have hfg := hf.range_inj_of_wellFoundedLT hg |>.mp heq
  refine ⟨hfg, ?_⟩
  subst g
  exact map_injective hf.injective h

end stdSimplex
