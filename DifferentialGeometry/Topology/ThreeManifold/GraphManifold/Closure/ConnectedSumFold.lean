import DifferentialGeometry.Topology.ThreeManifold.ConnectedSum.Construction
import DifferentialGeometry.Topology.Manifold.LocalDiffeomorph.OpenCodRestrict

/-!
Actual punctured-factor maps and their local collar geometry identify the whole connected sum.
-/

set_option autoImplicit false

noncomputable section

open Set Function
open DifferentialGeometry DifferentialGeometry.Topology
open scoped Manifold ContDiff Topology

universe u

namespace GC.GraphManifold

variable (M N Q : ConnectedClosedOrientedManifold.{u} 3)
  (c : OrientedBallChart M.toClosedOrientedManifold)
  (d : OrientedBallChart N.toClosedOrientedManifold) (a : BoundaryAttachment)
  (fL : c.toBallChart.Punctured → Q.Carrier) (fR : d.toBallChart.Punctured → Q.Carrier)
  (hcross : ∀ x y, fL x = fR y ↔ ∃ z,
    c.toBallChart.boundaryMap z = x ∧ d.toBallChart.boundaryMap (a.1 z) = y)

include hcross in
private theorem connectedSumFold_relation :
    ∀ x y, adjunctionRel c.toBallChart.boundaryMap
      (d.toBallChart.boundaryMap ∘ a.1) x y → Sum.elim fL fR x = Sum.elim fL fR y := by
  rintro x y ⟨z, h | h⟩
  · rcases h with ⟨rfl, rfl⟩
    exact (hcross _ _).mpr ⟨z, rfl, rfl⟩
  · rcases h with ⟨rfl, rfl⟩
    exact ((hcross _ _).mpr ⟨z, rfl, rfl⟩).symm

def connectedSumFold :
    ConnectedSumQuotient c.toBallChart d.toBallChart a.1.toHomeomorph → Q.Carrier :=
  Quot.lift (Sum.elim fL fR) (connectedSumFold_relation M N Q c d a fL fR hcross)

theorem connectedSumFold_left (x : c.toBallChart.Punctured) :
    connectedSumFold M N Q c d a fL fR hcross
      (ConnectedSumQuotient.inl c.toBallChart d.toBallChart a.1.toHomeomorph x) = fL x := rfl

theorem connectedSumFold_right (x : d.toBallChart.Punctured) :
    connectedSumFold M N Q c d a fL fR hcross
      (ConnectedSumQuotient.inr c.toBallChart d.toBallChart a.1.toHomeomorph x) = fR x := rfl

omit hcross in
def connectedSumFoldCollar (p : ConnectedSumQuotient.CollarDomain) : Q.Carrier :=
  if ht : 0 ≤ (p.2 : ℝ) then
    fL (c.toBallChart.radialMap p.1 (1 + (p.2 : ℝ)) (by
      have hr := ConnectedSumQuotient.collar_left_radius p.2 ht
      exact ⟨hr.1, le_trans hr.2.le (by norm_num)⟩))
  else
    fR (d.toBallChart.radialMap (a.1 p.1) (1 - (p.2 : ℝ)) (by
      have hr := ConnectedSumQuotient.collar_right_radius p.2 (lt_of_not_ge ht).le
      exact ⟨hr.1, le_trans hr.2.le (by norm_num)⟩))

theorem connectedSumFold_collar :
    connectedSumFold M N Q c d a fL fR hcross ∘
      ConnectedSumQuotient.collarMap c.toBallChart d.toBallChart a.1 =
        connectedSumFoldCollar M N Q c d a fL fR := by
  funext p
  by_cases ht : 0 ≤ (p.2 : ℝ)
  · rw [Function.comp_apply, ConnectedSumQuotient.collarMap_of_nonneg _ _ _ _ ht]
    simp only [connectedSumFoldCollar, dite_eq_left ht, connectedSumFold_left]
  · rw [Function.comp_apply,
      ConnectedSumQuotient.collarMap_of_neg _ _ _ _ (lt_of_not_ge ht)]
    simp only [connectedSumFoldCollar, dite_eq_right ht, connectedSumFold_right]

variable (hL : Continuous fL) (hR : Continuous fR)
  (hiL : Injective fL) (hiR : Injective fR)
  (hcover : ∀ y : Q.Carrier, (∃ x, fL x = y) ∨ ∃ x, fR x = y)

include hL hR in
theorem connectedSumFold_continuous :
    Continuous (connectedSumFold M N Q c d a fL fR hcross) :=
  continuous_adjunction_lift _ _
    (connectedSumFold_relation M N Q c d a fL fR hcross) (hL.sumElim hR)

include hiL hiR hcover in
theorem connectedSumFold_bijective :
    Bijective (connectedSumFold M N Q c d a fL fR hcross) := by
  constructor
  · intro x y he
    induction x using Quot.inductionOn with | h x =>
      induction y using Quot.inductionOn with | h y =>
        cases x with
        | inl x =>
          cases y with
          | inl y => exact congrArg (ConnectedSumQuotient.inl _ _ _) (hiL he)
          | inr y =>
            obtain ⟨z, rfl, rfl⟩ := (hcross x y).mp he
            exact ConnectedSumQuotient.boundary_eq _ _ _ z
        | inr x =>
          cases y with
          | inl y =>
            obtain ⟨z, rfl, rfl⟩ := (hcross y x).mp he.symm
            exact (ConnectedSumQuotient.boundary_eq _ _ _ z).symm
          | inr y => exact congrArg (ConnectedSumQuotient.inr _ _ _) (hiR he)
  · intro y
    rcases hcover y with ⟨x, hx⟩ | ⟨x, hx⟩
    · exact ⟨ConnectedSumQuotient.inl _ _ _ x, hx⟩
    · exact ⟨ConnectedSumQuotient.inr _ _ _ x, hx⟩

variable
  (hsL : IsLocalDiffeomorph (𝓡 3) (𝓡 3) ∞ (fL ∘ c.toBallChart.interiorToPunctured))
  (hsR : IsLocalDiffeomorph (𝓡 3) (𝓡 3) ∞ (fR ∘ d.toBallChart.interiorToPunctured))
  (hsC : IsLocalDiffeomorph ((𝓡 2).prod 𝓘(ℝ, ℝ)) (𝓡 3) ∞
    (connectedSumFoldCollar M N Q c d a fL fR))

def connectedSumFoldDiffeomorph :
    (smoothConnectedSum M N c d a).toConnectedClosedOrientedManifold.Carrier
      ≃ₘ⟮𝓡 3, 𝓡 3⟯ Q.Carrier := by
  let S := smoothConnectedSum M N c d a
  letI := S.charts
  have hf : IsLocalDiffeomorph (𝓡 3) (𝓡 3) ∞
      (connectedSumFold M N Q c d a fL fR hcross) := by
    intro y
    rcases ConnectedSumQuotient.interior_collar_cover c.toBallChart d.toBallChart a.1 y with
      ⟨x, rfl⟩ | ⟨x, rfl⟩ | ⟨p, rfl⟩
    · exact isLocalDiffeomorphAt_of_comp (hsL x) (S.interiorLeft_localDiffeomorph x)
    · exact isLocalDiffeomorphAt_of_comp (hsR x) (S.interiorRight_localDiffeomorph x)
    · apply isLocalDiffeomorphAt_of_comp (f := ConnectedSumQuotient.collarMap _ _ _)
        (g := connectedSumFold M N Q c d a fL fR hcross)
        (hf := S.collar_localDiffeomorph p)
      rw [connectedSumFold_collar]
      exact hsC p
  exact hf.diffeomorphOfBijective
    (connectedSumFold_bijective M N Q c d a fL fR hcross hiL hiR hcover)

theorem connectedSumFoldDiffeomorph_left (x : c.toBallChart.Punctured) :
    connectedSumFoldDiffeomorph M N Q c d a fL fR hcross hiL hiR hcover hsL hsR hsC
      (ConnectedSumQuotient.inl c.toBallChart d.toBallChart a.1.toHomeomorph x) = fL x := rfl

theorem connectedSumFoldDiffeomorph_right (x : d.toBallChart.Punctured) :
    connectedSumFoldDiffeomorph M N Q c d a fL fR hcross hiL hiR hcover hsL hsR hsC
      (ConnectedSumQuotient.inr c.toBallChart d.toBallChart a.1.toHomeomorph x) = fR x := rfl

end GC.GraphManifold
