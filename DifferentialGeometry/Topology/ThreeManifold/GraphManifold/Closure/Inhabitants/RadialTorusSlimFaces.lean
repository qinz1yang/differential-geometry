import
  DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Closure.Inhabitants.RadialTorusSlim

set_option autoImplicit false

noncomputable section

open Set Function
open DifferentialGeometry DifferentialGeometry.Topology GC.Endpoint GC.GraphManifold
open GC.GraphManifold.Assembly.FC39P0
open scoped Manifold ContDiff Topology

namespace GC.GraphManifold.Assembly.FC39P0.X135Radial

def cuspToSlim : cuspSet ≃ₘ⟮𝓡∂ 3, 𝓡∂ 3⟯ slimSet :=
  cuspProduct.symm.trans slimProduct

theorem cuspToSlim_boundary :
    cuspToSlim '' ((𝓡∂ 3).boundary cuspSet) = (𝓡∂ 3).boundary slimSet := by
  ext p
  constructor
  · rintro ⟨q, hq, rfl⟩
    exact ((cuspToSlim.isLocalDiffeomorph q).isBoundaryPoint_iff (by simp)).mp hq
  · intro hp
    refine ⟨cuspToSlim.symm p, ?_, cuspToSlim.apply_symm_apply p⟩
    exact ((cuspToSlim.symm.isLocalDiffeomorph p).isBoundaryPoint_iff (by simp)).mp hp

def slimEnd (b : Bool) (t : Torus) : slimSet := slimProduct (t, Assembly.iccEnd b)

theorem cuspToSlim_end (b : Bool) (t : Torus) :
    cuspToSlim (cuspEnd b t) = slimEnd b t := by
  change slimProduct (cuspProduct.symm (cuspProduct (t, Assembly.iccEnd b))) = _
  rw [cuspProduct.symm_apply_apply]
  rfl

theorem cuspToSlim_end_range (b : Bool) :
    cuspToSlim '' range (cuspEnd b) = range (slimEnd b) := by
  rw [← range_comp]
  congr 1
  funext t
  exact cuspToSlim_end b t

def slimEndPoint (b : Bool) : slimSet := slimEnd b (1, 1)

theorem slimEnd_component (b : Bool) :
    connectedComponentIn ((𝓡∂ 3).boundary slimSet) (slimEndPoint b) =
      range (slimEnd b) := by
  have h := cuspToSlim.toHomeomorph.image_connectedComponentIn
    (cuspEnd_in_boundary b (mem_range_self (1, 1)))
  change cuspToSlim '' connectedComponentIn ((𝓡∂ 3).boundary cuspSet)
    (cuspEndPoint b) = connectedComponentIn
    (cuspToSlim '' ((𝓡∂ 3).boundary cuspSet)) (cuspToSlim (cuspEndPoint b)) at h
  rw [cuspEnd_component, cuspToSlim_end_range, cuspToSlim_boundary] at h
  change range (slimEnd b) = connectedComponentIn ((𝓡∂ 3).boundary slimSet)
    (cuspToSlim (cuspEnd b (1, 1))) at h
  rw [cuspToSlim_end] at h
  exact h.symm

theorem slimEnd_in_boundary (b : Bool) : range (slimEnd b) ⊆ (𝓡∂ 3).boundary slimSet := by
  rw [← cuspToSlim_end_range, ← cuspToSlim_boundary]
  exact image_mono (cuspEnd_in_boundary b)

def slimModelFace (b : Bool) : ModelBoundaryFace slimPiece :=
  ⟨range (slimEnd b), slimEndPoint b, slimEnd_in_boundary b (mem_range_self (1, 1)),
    (slimEnd_component b).symm⟩

theorem slimEnd_height (b : Bool) (t : Torus) :
    cliffordHeight (slimEnd b t).val = if b then -(1 / 2 : ℝ) else -(1 / 4 : ℝ) := by
  change cliffordHeight (cliffordSeam.{0} (slimParameter (t, Assembly.iccEnd b))) = _
  rw [slimParameter_height]
  cases b <;> norm_num [Assembly.iccEnd]

theorem slimEnd_range (b : Bool) :
    range (slimEnd b) =
      {p | cliffordHeight p.val = if b then -(1 / 2 : ℝ) else -(1 / 4 : ℝ)} := by
  ext p
  constructor
  · rintro ⟨t, rfl⟩
    exact slimEnd_height b t
  · intro hp
    have htime : (slimProductInverse p).2 = Assembly.iccEnd b := by
      apply Subtype.ext
      change -1 - 4 * cliffordHeight p.val = (Assembly.iccEnd b).val
      rw [hp]
      cases b <;> norm_num [Assembly.iccEnd]
    refine ⟨(slimProductInverse p).1, ?_⟩
    change slimProductMap ((slimProductInverse p).1, Assembly.iccEnd b) = p
    rw [← htime]
    exact slimProduct_right p

theorem slim_boundary_iff {p : slimSet} :
    (𝓡∂ 3).IsBoundaryPoint p ↔
      cliffordHeight p.val = -(1 / 2 : ℝ) ∨ cliffordHeight p.val = -(1 / 4 : ℝ) := by
  erw [SmoothBoundaryAtlas.regularSublevel_isBoundaryPoint_iff (𝓡 3) (n := 2)
    finrank_euclideanSpace_fin
    (bandDefiner_smooth (-(1 / 2 : ℝ)) (-(1 / 4 : ℝ))) 0
    (bandDefiner_regular (-(1 / 2 : ℝ)) (-(1 / 4 : ℝ))
      (by norm_num) (by norm_num) (by norm_num))]
  exact bandDefiner_zero_iff

theorem slimModelFace_cases (F : ModelBoundaryFace slimPiece) :
    F = slimModelFace false ∨ F = slimModelFace true := by
  obtain ⟨p, hp, hF⟩ := F.property
  have hpoint : ∃ b : Bool, p ∈ range (slimEnd b) := by
    rcases (slim_boundary_iff (p := p)).mp hp with hlow | hhigh
    · exact ⟨true, (slimEnd_range true).symm ▸ hlow⟩
    · exact ⟨false, (slimEnd_range false).symm ▸ hhigh⟩
  obtain ⟨b, hb⟩ := hpoint
  have hsame : F = slimModelFace b := by
    apply Subtype.ext
    rw [hF]
    change connectedComponentIn ((𝓡∂ 3).boundary slimSet) p = range (slimEnd b)
    rw [← slimEnd_component b]
    exact (connectedComponentIn_eq (slimEnd_component b ▸ hb)).symm
  cases b
  · exact Or.inl hsame
  · exact Or.inr hsame

end GC.GraphManifold.Assembly.FC39P0.X135Radial
