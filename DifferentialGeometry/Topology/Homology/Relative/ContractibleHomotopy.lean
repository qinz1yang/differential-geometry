import DifferentialGeometry.Topology.Homology.Relative.ReducedMap

set_option autoImplicit false
noncomputable section
open CategoryTheory Set
open scoped unitInterval
namespace Poincare.Homology
universe u
variable {X Y : TopCat.{u}} {s : Set X} {t : Set Y}
  {f g : X ⟶ Y} (hf : MapsTo f s t) (hg : MapsTo g s t)


def relativeSubspaceHomotopy (H : TopCat.Homotopy f g)
    (hH : ∀ a : I, MapsTo (fun x => H (a,x)) s t) :
    TopCat.Homotopy (relativeSubspaceMap f hf) (relativeSubspaceMap g hg) where
  toFun q := ⟨H (q.1,q.2.val), hH q.1 q.2.property⟩
  continuous_toFun := (H.continuous.comp
    (continuous_fst.prodMk (continuous_subtype_val.comp continuous_snd))).subtype_mk _
  map_zero_left x := Subtype.ext (H.map_zero_left x.val)
  map_one_left x := Subtype.ext (H.map_one_left x.val)


@[simp]
theorem relativeSubspaceHomotopy_apply (H : TopCat.Homotopy f g)
    (hH : ∀ a : I, MapsTo (fun x => H (a,x)) s t) (a : I) (x : s) :
    (relativeSubspaceHomotopy hf hg H hH (a,x) : Y) = H (a,x.val) := rfl

variable {k : Type u} [Ring k] (A : ModuleCat.{u} k)
  [ContractibleSpace X] [ContractibleSpace Y]


theorem relativeHomologyMap_eq_of_subspace_homotopy
    (H : TopCat.Homotopy (relativeSubspaceMap f hf) (relativeSubspaceMap g hg)) (n : ℕ) :
    relativeHomologyMap A f hf (n + 1) = relativeHomologyMap A g hg (n + 1) := by
  apply (cancel_mono (relativeReducedConnectingIso Y t A n).hom).mp
  rw [← relativeReducedConnectingIso_naturality A f hf n,
    ← relativeReducedConnectingIso_naturality A g hg n,
    reducedSingularHomologyMap_eq_of_homotopy A H n]


theorem relativeHomologyMap_eq_of_homotopy_of_contractible
    (H : TopCat.Homotopy f g) (hH : ∀ a : I, MapsTo (fun x => H (a,x)) s t) (n : ℕ) :
    relativeHomologyMap A f hf (n + 1) = relativeHomologyMap A g hg (n + 1) :=
  relativeHomologyMap_eq_of_subspace_homotopy hf hg A (relativeSubspaceHomotopy hf hg H hH) n
end Poincare.Homology
