import DifferentialGeometry.Geometry.Hyperbolic.LorentzModel.Horosphere.SmoothCylinder
import DifferentialGeometry.Geometry.Hyperbolic.LorentzModel.Horosphere.SmoothCoordinates
import DifferentialGeometry.Topology.Manifold.OpenEmbedding
import DifferentialGeometry.Topology.Manifold.ParametrizationDerivative

noncomputable section

open scoped Manifold ContDiff

namespace DifferentialGeometry.HorosphereProjection

open ProjectiveOrthogonalGroup (PO)
open Hyperbolic (HUpper)
open HyperbolicAction (poMulAction)
open HyperbolicBoundary (BoundaryH poBoundaryMulAction)
open MobiusBoundary (ptInfty)
open Busemann (busemann horosphere)
open BusemannCocycle (poConfFactor po_busemann_smul)
open Horospherical (Horizontal ofCoords horizontal height height_pos)

variable {m : ℕ}

private local instance : MulAction (PO (m + 1) 1) (HUpper (m + 1)) :=
  poMulAction (Nat.le_add_left 1 m)

local notation "I" => 𝓘(ℝ, EuclideanSpace ℝ (Fin (m + 1)))
local notation "J" => 𝓘(ℝ, Horizontal m)
local notation "K" => 𝓘(ℝ, Fin m → ℝ)

private def horosphereCoordinateLift (ξ : BoundaryH (m + 1)) (c : ℝ)
    (a : PO (m + 1) 1) (x : Horizontal m) : HUpper (m + 1) :=
  a⁻¹ • ofCoords x (Real.exp (Real.log (poConfFactor (Nat.le_add_left 1 m) a ξ) - c))
    (Real.exp_pos _)

private theorem contMDiff_horosphereCoordinateLift (ξ : BoundaryH (m + 1)) (c : ℝ)
    (a : PO (m + 1) 1) : ContMDiff J I ∞ (horosphereCoordinateLift ξ c a) := by
  let h : (TopologicalSpace.Opens.mk (Set.Ioi (0 : ℝ)) isOpen_Ioi) :=
    ⟨Real.exp (Real.log (poConfFactor (Nat.le_add_left 1 m) a ξ) - c), Real.exp_pos _⟩
  exact (HyperbolicAction.contMDiff_po_smul m ∞ a⁻¹).comp
    ((Horospherical.coordsDiffeomorph m).symm.contMDiff.comp
      (contMDiff_id.prodMk (contMDiff_const (c := h))))

private theorem horosphereCoordinateLift_mem (ξ : BoundaryH (m + 1)) (c : ℝ)
    (a : PO (m + 1) 1)
    (ha : (poBoundaryMulAction (Nat.le_add_left 1 m)).smul a ξ = ptInfty)
    (x : Horizontal m) : horosphereCoordinateLift ξ c a x ∈ horosphere ξ c := by
  have h := po_busemann_smul (Nat.le_add_left 1 m) a ξ
    (horosphereCoordinateLift ξ c a x)
  change busemann ((poBoundaryMulAction (Nat.le_add_left 1 m)).smul a ξ)
    (a • (a⁻¹ • ofCoords x (Real.exp (Real.log (poConfFactor (Nat.le_add_left 1 m) a ξ) - c))
      (Real.exp_pos _))) = _ at h
  rw [ha, smul_inv_smul, Horospherical.busemann_ofCoords, Real.log_exp] at h
  change busemann ξ (horosphereCoordinateLift ξ c a x) = c
  linarith

private theorem injective_mfderiv_horosphereCoordinateLift (ξ : BoundaryH (m + 1))
    (c : ℝ) (a : PO (m + 1) 1) (x : Horizontal m) :
    Function.Injective (mfderiv J I (horosphereCoordinateLift ξ c a) x) := by
  have hb : ContMDiff I J ∞ (fun p : HUpper (m + 1) => horizontal (a • p)) :=
    (Horospherical.coordsDiffeomorph m).contMDiff.fst.comp
      (HyperbolicAction.contMDiff_po_smul m ∞ a)
  apply Topology.Manifold.injective_mfderiv_of_leftInverseOn
    (contMDiff_horosphereCoordinateLift ξ c a) hb.contMDiffOn
    (fun _ => Set.mem_univ _) (p := x)
  intro y
  change horizontal (a • (a⁻¹ • ofCoords y _ _)) = y
  rw [smul_inv_smul, Horospherical.horizontal_ofCoords]

variable (P : Subgroup (PO (m + 1) 1))

private local instance : MulAction P (HUpper (m + 1)) :=
  EquivariantMap.subAction (Nat.le_add_left 1 m) P

local notation "Q" => MulAction.orbitRel.Quotient P (HUpper (m + 1))
local notation "π" => Quotient.mk (MulAction.orbitRel P (HUpper (m + 1)))

def quotientHorosphereCoordinates (ξ : BoundaryH (m + 1)) (c : ℝ)
    (a : PO (m + 1) 1)
    (ha : (poBoundaryMulAction (Nat.le_add_left 1 m)).smul a ξ = ptInfty) :
    C(Horizontal m, π '' horosphere ξ c) where
  toFun x := ⟨π (horosphereCoordinateLift ξ c a x),
    ⟨horosphereCoordinateLift ξ c a x, horosphereCoordinateLift_mem ξ c a ha x, rfl⟩⟩
  continuous_toFun := (continuous_quotient_mk'.comp
    (contMDiff_horosphereCoordinateLift ξ c a).continuous).subtype_mk _

@[simp] theorem quotientHorosphereCoordinates_apply (ξ : BoundaryH (m + 1)) (c : ℝ)
    (a : PO (m + 1) 1)
    (ha : (poBoundaryMulAction (Nat.le_add_left 1 m)).smul a ξ = ptInfty)
    (x : Horizontal m) :
    (quotientHorosphereCoordinates P ξ c a ha x).val =
      π (a⁻¹ • ofCoords x
        (Real.exp (Real.log (poConfFactor (Nat.le_add_left 1 m) a ξ) - c))
        (Real.exp_pos _)) := rfl

theorem quotientHorosphereCoordinates_surjective (ξ : BoundaryH (m + 1)) (c : ℝ)
    (a : PO (m + 1) 1)
    (ha : (poBoundaryMulAction (Nat.le_add_left 1 m)).smul a ξ = ptInfty) :
    Function.Surjective (quotientHorosphereCoordinates P ξ c a ha) := by
  intro z
  obtain ⟨p, hp, hpz⟩ := z.property
  have hb := po_busemann_smul (Nat.le_add_left 1 m) a ξ p
  rw [ha, Horospherical.busemann_eq_neg_log_height] at hb
  change -Real.log (height (a • p)) =
    busemann ξ p - Real.log (poConfFactor (Nat.le_add_left 1 m) a ξ) at hb
  change busemann ξ p = c at hp
  have hlog : Real.log (height (a • p)) =
      Real.log (poConfFactor (Nat.le_add_left 1 m) a ξ) - c := by linarith
  have hh : height (a • p) =
      Real.exp (Real.log (poConfFactor (Nat.le_add_left 1 m) a ξ) - c) := by
    rw [← hlog, Real.exp_log (height_pos _)]
  refine ⟨horizontal (a • p), Subtype.ext ?_⟩
  change π (horosphereCoordinateLift ξ c a (horizontal (a • p))) = z.val
  have hl : horosphereCoordinateLift ξ c a (horizontal (a • p)) = p := by
    have he : (⟨Real.exp (Real.log (poConfFactor (Nat.le_add_left 1 m) a ξ) - c),
        Real.exp_pos _⟩ : {h : ℝ // 0 < h}) = ⟨height (a • p), height_pos _⟩ :=
      Subtype.ext hh.symm
    have hc := congrArg (fun h : {h : ℝ // 0 < h} =>
      ofCoords (horizontal (a • p)) h.val h.property) he
    rw [Horospherical.ofCoords_horizontal_height] at hc
    exact (congrArg (fun q : HUpper (m + 1) => a⁻¹ • q) hc).trans (inv_smul_smul a p)
  rw [hl]
  exact hpz

private local instance : ContinuousConstSMul P (HUpper (m + 1)) :=
  ⟨fun γ => (HyperbolicAction.contMDiff_po_smul m ω (γ : PO (m + 1) 1)).continuous⟩

private local instance : ContMDiffConstSMul I ∞ P (HUpper (m + 1)) :=
  ⟨fun γ => HyperbolicAction.contMDiff_po_smul m ∞ (γ : PO (m + 1) 1)⟩

variable [ProperlyDiscontinuousSMul P (HUpper (m + 1))]
  [IsCancelSMul P (HUpper (m + 1))]
  (ξ : BoundaryH (m + 1))
  (hhor : ∀ γ : P, (poBoundaryMulAction (Nat.le_add_left 1 m)).smul
    (γ : PO (m + 1) 1) ξ = ξ ∧ poConfFactor (Nat.le_add_left 1 m) (γ : PO (m + 1) 1) ξ = 1)
  (c : ℝ) (a : PO (m + 1) 1)
  (ha : (poBoundaryMulAction (Nat.le_add_left 1 m)).smul a ξ = ptInfty)

theorem contMDiff_quotientHorosphereCoordinates :
    let _ := quotientHorosphereChartedSpace P ξ hhor c
    ContMDiff J K ∞ (quotientHorosphereCoordinates P ξ c a ha) := by
  let _ := quotientHorosphereChartedSpace P ξ hhor c
  have hπ := MulAction.isLocalDiffeomorph_quotientMk_of_properlyDiscontinuousSMul
    (G := P) (M := HUpper (m + 1)) (n := ∞) I
  exact contMDiff_quotient_horosphere_factor P ξ hhor c
    (hπ.contMDiff.comp (contMDiff_horosphereCoordinateLift ξ c a))
    (fun x => ⟨horosphereCoordinateLift ξ c a x, horosphereCoordinateLift_mem ξ c a ha x, rfl⟩)

theorem isLocalDiffeomorph_quotientHorosphereCoordinates :
    let _ := quotientHorosphereChartedSpace P ξ hhor c
    IsLocalDiffeomorph J K ∞ (quotientHorosphereCoordinates P ξ c a ha) := by
  let _ := quotientHorosphereChartedSpace P ξ hhor c
  let _ := isManifold_quotient_horosphere P ξ hhor c
  let q := quotientHorosphereCoordinates P ξ c a ha
  have hq : ContMDiff J K ∞ q := contMDiff_quotientHorosphereCoordinates P ξ hhor c a ha
  have hπ := MulAction.isLocalDiffeomorph_quotientMk_of_properlyDiscontinuousSMul
    (G := P) (M := HUpper (m + 1)) (n := ∞) I
  have hf := contMDiff_horosphereCoordinateLift ξ c a
  have hi := contMDiff_quotient_horosphere_inclusion P ξ hhor c
  apply Topology.Manifold.isLocalDiffeomorph_of_injective_mfderiv q hq
  · intro x
    have hπinj : Function.Injective (mfderiv I I π (horosphereCoordinateLift ξ c a x)) :=
      (hπ.isInvertible_mfderiv (by simp) _).injective
    have hall : Function.Injective (mfderiv J I (π ∘ horosphereCoordinateLift ξ c a) x) := by
      rw [mfderiv_comp x (hπ.contMDiff.mdifferentiable (by simp) _) (hf.mdifferentiable (by simp) _)]
      exact hπinj.comp (injective_mfderiv_horosphereCoordinateLift ξ c a x)
    have heq : (Subtype.val : (π '' horosphere ξ c) → Q) ∘ q =
        π ∘ horosphereCoordinateLift ξ c a := rfl
    rw [← heq, mfderiv_comp x (hi.mdifferentiable (by simp) _) (hq.mdifferentiable (by simp) _)] at hall
    intro v w hvw
    exact hall (congrArg (mfderiv K I (Subtype.val : (π '' horosphere ξ c) → Q) (q x)) hvw)
  · simp [Horizontal]

end DifferentialGeometry.HorosphereProjection
